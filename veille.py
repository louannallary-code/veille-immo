"""
Veille immo : surveille les pages d'annonces des agences et envoie
une notification (ntfy) dès qu'une nouvelle annonce correspond aux critères.

Lancement :
    python veille.py          -> passage normal
    python veille.py --test   -> passage + notification de test avec le bilan
"""

import json
import os
import re
import sys
import time
from datetime import datetime
from pathlib import Path
from urllib.parse import urljoin, urlparse, urlunparse

import requests
import yaml
from playwright.sync_api import sync_playwright

ICI = Path(__file__).parent
FICHIER_CONFIG = ICI / "agences.yaml"
DOSSIER_ETAT = ICI / "etat"
FICHIER_VUES = DOSSIER_ETAT / "annonces_vues.json"
FICHIER_SANTE = DOSSIER_ETAT / "sante.json"
FICHIER_RAPPORT = ICI / "RAPPORT.md"

NTFY_TOPIC = os.environ.get("NTFY_TOPIC", "").strip()
ECHECS_AVANT_ALERTE = 6  # ~30 min d'échecs d'affilée avant de prévenir

# Morceaux d'adresse qui ne sont jamais des annonces
EXCLUSIONS = re.compile(
    r"(agence|agences|estim|conseil|blog|actualit|contact|recrut|mentions|"
    r"cookie|connexion|login|compte|favori|alerte|vendre|faire-gerer|gestion|"
    r"syndic|honoraires|bareme|barème|avis|faq|newsletter|print|\.pdf$|"
    r"facebook|instagram|linkedin|twitter|youtube|tiktok)",
    re.I,
)
# Un identifiant d'annonce : nombre d'au moins 4 chiffres ou un UUID
IDENTIFIANT = re.compile(r"(\d{4,}|[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12})", re.I)


# ----------------------------------------------------------------------
# Lecture des infos d'une annonce à partir de son texte
# ----------------------------------------------------------------------

def _nombre(txt):
    txt = txt.replace(" ", "").replace("\xa0", "").replace(" ", "")
    # "1.205,96" -> 1205.96 ; "1,205" (rare) ignoré ; "1205.96" ok
    if re.fullmatch(r"\d{1,3}(\.\d{3})+(,\d+)?", txt):
        txt = txt.replace(".", "")
    txt = txt.replace(",", ".")
    try:
        return float(txt)
    except ValueError:
        return None


def extraire_infos(texte, url=""):
    """Devine loyer, surface, pièces, meublé et code postal. None = inconnu."""
    t = " ".join(texte.split())
    infos = {"loyer": None, "surface": None, "pieces": None, "meuble": None, "cp": None}

    # Loyer : premier montant en € plausible pour un loyer
    montant = r"(?<![\w.,])(\d{1,3}(?:[  \xa0.]\d{3})+|\d+)((?:[.,]\d{1,2})?)\s*(?:€|eur\b|euros?)"
    for m in re.finditer(montant, t, re.I):
        v = _nombre(m.group(1).replace(".", "").replace(" ", "") + m.group(2).replace(",", "."))
        if v and 150 <= v <= 30000:
            infos["loyer"] = v
            break

    # Surface
    m = re.search(r"(\d{1,4}(?:[.,]\d{1,2})?)\s*m(?:²|2\b|ètres? carrés)", t, re.I)
    if not m:
        m = re.search(r"(\d{1,4}(?:[.,]\d{1,2})?)m(?:²|2\b)", url, re.I)
    if m:
        infos["surface"] = _nombre(m.group(1))

    # Pièces
    source = t + " " + url.replace("-", " ").replace("/", " ")
    m = re.search(r"(\d{1,2})\s*(?:pi[eè]ces?|pp\b)", source, re.I)
    if m:
        infos["pieces"] = int(m.group(1))
    else:
        m = re.search(r"\b[TF](\d{1,2})\b", source)
        if m:
            infos["pieces"] = int(m.group(1))
        elif re.search(r"\bstudio|\bstudette", source, re.I):
            infos["pieces"] = 1

    # Meublé ?
    low = (t + " " + url).lower()
    if re.search(r"non[\s-]meubl|location vide|\bvide\b", low):
        infos["meuble"] = False
    elif "meubl" in low:
        infos["meuble"] = True

    # Code postal / arrondissement
    m = re.search(r"\b(75\d{3}|751\d{2})\b", t + " " + url)
    if m:
        cp = m.group(1)
        if cp.startswith("751"):  # codes INSEE type 75111 -> 75011
            cp = "750" + cp[3:]
        infos["cp"] = cp
    else:
        m = re.search(r"paris[\s-]*(\d{1,2})\s*(?:e|ème|eme|er)?\b", low)
        if m and 1 <= int(m.group(1)) <= 20:
            infos["cp"] = f"750{int(m.group(1)):02d}"
    return infos


def correspond(infos, crit):
    """Renvoie (True/False, raison). Une info inconnue ne bloque jamais."""
    if infos["loyer"] is not None and infos["loyer"] > crit["loyer_max"]:
        return False, f"loyer {infos['loyer']:.0f} €"
    if infos["surface"] is not None and infos["surface"] < crit["surface_min"]:
        return False, f"surface {infos['surface']} m²"
    if infos["pieces"] is not None and infos["pieces"] < crit["pieces_min"]:
        return False, f"{infos['pieces']} pièce(s)"
    if str(crit.get("meuble", "")).lower() in ("non", "false") and infos["meuble"] is True:
        return False, "meublé"
    cps = [str(c) for c in crit.get("codes_postaux", [])]
    if cps and infos["cp"] is not None and infos["cp"] not in cps:
        return False, f"code postal {infos['cp']}"
    return True, ""


# ----------------------------------------------------------------------
# Repérage des liens d'annonces sur une page
# ----------------------------------------------------------------------

JS_LIENS = """
() => {
  const out = [];
  const idDe = h => (h.match(/\\d{4,}|[0-9a-f]{8}-[0-9a-f-]{27}/i) || [null])[0];
  for (const a of document.querySelectorAll('a[href]')) {
    const monId = idDe(a.href);
    let el = a, texte = (a.innerText || '');
    // On remonte vers la "carte" de l'annonce, sans englober d'autres annonces
    for (let i = 0; i < 7 && el.parentElement; i++) {
      if (/€|eur/i.test(texte) && texte.length > 15) break;
      const parent = el.parentElement;
      const autres = [...parent.querySelectorAll('a[href]')]
        .map(x => idDe(x.href)).filter(x => x && x !== monId);
      const t = parent.innerText || '';
      if (autres.length > 0 || t.length > 1500) break;
      el = parent;
      texte = t;
    }
    out.push({href: a.href, texte: texte.slice(0, 600), titre: (a.title || a.innerText || '').slice(0, 150)});
  }
  return out;
}
"""


def normaliser(url):
    p = urlparse(url)
    return urlunparse((p.scheme, p.netloc.lower(), p.path.rstrip("/"), "", p.query, ""))


def meme_site(url, base):
    a = urlparse(url).netloc.lower().split(".")
    b = urlparse(base).netloc.lower().split(".")
    return a[-2:] == b[-2:]


def est_annonce(href, texte, base, motif):
    if not href.startswith("http") or not meme_site(href, base):
        return False
    chemin = urlparse(href).path
    if motif:
        return motif in href and bool(IDENTIFIANT.search(chemin))
    if EXCLUSIONS.search(chemin):
        return False
    if not IDENTIFIANT.search(chemin):
        return False
    return bool(re.search(r"€|eur", texte, re.I))


def lire_page(page, agence):
    page.goto(agence["url"], wait_until="domcontentloaded", timeout=45000)
    try:
        page.wait_for_load_state("networkidle", timeout=15000)
    except Exception:
        pass
    # Accepter les cookies si un bouton évident est présent
    for libelle in ("Tout accepter", "Accepter", "J'accepte", "Accepter et fermer", "OK"):
        try:
            bouton = page.get_by_role("button", name=libelle, exact=False).first
            if bouton.is_visible(timeout=500):
                bouton.click(timeout=1500)
                page.wait_for_timeout(1000)
                break
        except Exception:
            continue
    # Faire défiler pour charger les annonces "paresseuses"
    for _ in range(4):
        page.mouse.wheel(0, 2500)
        page.wait_for_timeout(700)

    annonces = {}
    for lien in page.evaluate(JS_LIENS):
        href = normaliser(urljoin(page.url, lien["href"]))
        if est_annonce(href, lien["texte"], agence["url"], agence.get("motif")):
            # on garde le texte le plus riche trouvé pour ce lien
            ancien = annonces.get(href)
            if ancien is None:
                annonces[href] = lien
            else:
                if len(lien["texte"]) > len(ancien["texte"]):
                    ancien["texte"] = lien["texte"]
                if len(lien["titre"].strip()) > len(ancien["titre"].strip()):
                    ancien["titre"] = lien["titre"]
    titre_page = page.title()
    return annonces, titre_page


# ----------------------------------------------------------------------
# Notifications
# ----------------------------------------------------------------------

def notifier(titre, message, lien=None, priorite=4, tags=None):
    print(f"[NOTIF] {titre} | {message} | {lien or ''}")
    if not NTFY_TOPIC:
        print("  (NTFY_TOPIC non défini : notification non envoyée)")
        return
    corps = {"topic": NTFY_TOPIC, "title": titre[:250], "message": message[:3500],
             "priority": priorite, "tags": tags or []}
    if lien:
        corps["click"] = lien
        corps["actions"] = [{"action": "view", "label": "Voir l'annonce", "url": lien}]
    try:
        requests.post("https://ntfy.sh/", json=corps, timeout=20)
    except Exception as e:
        print(f"  Échec de l'envoi : {e}")


def resume_infos(i):
    morceaux = []
    if i["loyer"]:
        morceaux.append(f"{i['loyer']:.0f} €")
    if i["surface"]:
        morceaux.append(f"{i['surface']:g} m²")
    if i["pieces"]:
        morceaux.append(f"{i['pieces']} p.")
    if i["cp"]:
        morceaux.append(i["cp"])
    return " · ".join(morceaux) if morceaux else "infos à vérifier"


# ----------------------------------------------------------------------
# Programme principal
# ----------------------------------------------------------------------

def charger(fichier, defaut):
    try:
        return json.loads(fichier.read_text(encoding="utf-8"))
    except Exception:
        return defaut


def main():
    mode_test = "--test" in sys.argv
    config = yaml.safe_load(FICHIER_CONFIG.read_text(encoding="utf-8"))
    crit = config["criteres"]
    agences = [a for a in config["agences"] if str(a.get("actif", "oui")).lower() not in ("non", "false")]

    DOSSIER_ETAT.mkdir(exist_ok=True)
    vues = charger(FICHIER_VUES, {})
    sante = charger(FICHIER_SANTE, {})
    lignes_rapport = []
    nb_nouvelles = 0

    with sync_playwright() as p:
        navigateur = p.chromium.launch(headless=True)
        contexte = navigateur.new_context(
            locale="fr-FR",
            user_agent=("Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
                        "(KHTML, like Gecko) Chrome/131.0.0.0 Safari/537.36"),
            viewport={"width": 1366, "height": 900},
        )
        for agence in agences:
            nom = agence["nom"]
            page = contexte.new_page()
            debut = time.time()
            erreur = None
            annonces, titre_page = {}, ""
            try:
                annonces, titre_page = lire_page(page, agence)
            except Exception as e:
                erreur = str(e).splitlines()[0][:150]
            finally:
                page.close()
            duree = time.time() - debut

            etat = sante.setdefault(nom, {"echecs": 0, "alerte_envoyee": False})
            premiere_fois = nom not in vues
            deja_vues = set(vues.get(nom, []))

            if erreur or not annonces:
                etat["echecs"] += 1
                statut = f"❌ {erreur}" if erreur else "⚠️ aucune annonce repérée"
                if etat["echecs"] >= ECHECS_AVANT_ALERTE and not etat["alerte_envoyee"] and not premiere_fois:
                    notifier(f"⚠️ {nom} ne répond plus",
                             "La veille n'arrive plus à lire ce site depuis ~30 min. "
                             "Regarde RAPPORT.md sur GitHub.", agence["url"], priorite=2, tags=["warning"])
                    etat["alerte_envoyee"] = True
            else:
                if etat["alerte_envoyee"]:
                    notifier(f"✅ {nom} fonctionne à nouveau", "La veille lit de nouveau ce site.",
                             priorite=2, tags=["white_check_mark"])
                etat.update({"echecs": 0, "alerte_envoyee": False})
                statut = f"✅ {len(annonces)} annonce(s) repérée(s)"

                gardees = 0
                for url, lien in annonces.items():
                    infos = extraire_infos(lien["texte"] + " " + lien["titre"], url)
                    ok, _ = correspond(infos, crit)
                    if ok:
                        gardees += 1
                    if url in deja_vues:
                        continue
                    deja_vues.add(url)
                    if premiere_fois or not ok:
                        continue  # 1er passage : on mémorise sans notifier
                    nb_nouvelles += 1
                    titre = (lien["titre"] or "Nouvelle annonce").strip().split("\n")[0][:80]
                    notifier(f"🏠 {nom} : {resume_infos(infos)}", titre, url, priorite=5,
                             tags=["house"])
                statut += f", dont {gardees} dans tes critères"
                vues[nom] = sorted(deja_vues)[-1500:]

            exemples = list(annonces)[:3]
            lignes_rapport.append((nom, agence["url"], statut, duree, titre_page, exemples))
            print(f"{nom}: {statut} ({duree:.0f}s)")
        navigateur.close()

    FICHIER_VUES.write_text(json.dumps(vues, ensure_ascii=False, indent=1), encoding="utf-8")
    FICHIER_SANTE.write_text(json.dumps(sante, ensure_ascii=False, indent=1), encoding="utf-8")
    ecrire_rapport(lignes_rapport, crit)

    if mode_test:
        ok = sum(1 for l in lignes_rapport if l[2].startswith("✅"))
        detail = "\n".join(f"{l[2][:2]} {l[0]}" for l in lignes_rapport)
        notifier(f"🧪 Test : {ok}/{len(lignes_rapport)} sites lus correctement", detail,
                 priorite=3, tags=["test_tube"])
    print(f"Terminé : {nb_nouvelles} nouvelle(s) annonce(s) notifiée(s).")


def ecrire_rapport(lignes, crit):
    heure = datetime.now().strftime("%d/%m/%Y")
    txt = [
        "# Rapport de la veille immo",
        "",
        f"Critères : {crit['loyer_max']} € max · {crit['surface_min']} m² min · "
        f"{crit['pieces_min']} pièces min · meublé : {crit.get('meuble')} · {', '.join(map(str, crit.get('codes_postaux', [])))}",
        f"Mis à jour le {heure}.",
        "",
        "| Agence | État | Titre de la page lue |",
        "|---|---|---|",
    ]
    for nom, url, statut, duree, titre_page, _ in lignes:
        txt.append(f"| [{nom}]({url}) | {statut} | {titre_page[:60].replace('|', '/')} |")
    txt += ["", "## Exemples de liens repérés (pour vérifier que ce sont bien des annonces)", ""]
    for nom, _, _, _, _, exemples in lignes:
        txt.append(f"**{nom}**")
        txt += [f"- {e}" for e in exemples] or ["- (aucun)"]
        txt.append("")
    FICHIER_RAPPORT.write_text("\n".join(txt), encoding="utf-8")


if __name__ == "__main__":
    main()
