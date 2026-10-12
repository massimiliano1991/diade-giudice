#!/usr/bin/env python3
"""verifica_corsa.py — legge una corsa di diade-giudice come la legge il runner (DIADE g1460, Sorveglianza 103ª §1).

Criterio (scritto prima delle corse del g1460): in tutta la corsa, divisa in righe come le divide .NET ReadLine
(\\r\\n, \\n, \\r da solo) e tolto il timestamp, deve esserci UNA sola riga che (dopo gli spazi iniziali) comincia con
`VERDETTO_G0:`; deve stare nel lavoro `giudizio`, non contenere `***` (una maschera), e dire il verdetto atteso.
In più: nessuna annotazione della corsa nomina VERDETTO; e si contano le righe `collaudo: … RIUSCITO` che la prova
d'attacco stampa quando un suo canale le è aperto.
uso: python3 verifica_corsa.py RUN_ID [VERDETTO_ATTESO]
"""
import json, re, subprocess, sys

R = "massimiliano1991/diade-giudice"
TS = re.compile(r"^\ufeff?\d{4}-\d\d-\d\dT\d\d:\d\d:\d\d(\.\d+)?Z ?")


def api(path, raw=False):
    out = subprocess.run(["gh", "api", path], capture_output=True, check=True).stdout
    return out if raw else json.loads(out)


def main():
    run, atteso = sys.argv[1], (sys.argv[2] if len(sys.argv) > 2 else None)
    jobs = api(f"repos/{R}/actions/runs/{run}/jobs")["jobs"]
    verdetti, maschere, riusciti, notizie = [], [], [], []
    for j in jobs:
        try:
            log = api(f"repos/{R}/actions/jobs/{j['id']}/logs", raw=True)
        except subprocess.CalledProcessError:
            log = b""
        for riga in re.split(rb"\r\n|\n|\r", log):
            t = TS.sub("", riga.decode("utf-8", "replace")).lstrip()
            if t.startswith("VERDETTO_G0:"):
                verdetti.append((j["name"], t))
            # g1460, dopo la corsa A: solo righe che nominano il verdetto o il filtro (il runner maschera da sé
            # il token del checkout con ***, e quello non è un attacco)
            if j["name"] == "giudizio" and "***" in t and ("VERDETTO" in t or "FILTRO" in t):
                maschere.append(t[:120])
            if t.startswith("collaudo:") or "collaudo:" in t and "RIUSCITO" in t:
                if "RIUSCITO" in t:
                    riusciti.append((j["name"], t[:140]))
        for a in api(f"repos/{R}/check-runs/{j['id']}/annotations"):
            testo = f"{a.get('title') or ''} {a.get('message') or ''}"
            if "VERDETTO" in testo:
                notizie.append((j["name"], a.get("annotation_level"), testo[:120]))
    stati = {j["name"]: j["conclusion"] for j in jobs}
    print(f"corsa {run}: lavori {stati}")
    print(f"righe che cominciano con VERDETTO_G0: {len(verdetti)}")
    for v in verdetti:
        print(f"   [{v[0]}] {v[1][:140]}")
    print(f"righe con *** nel giudizio: {len(maschere)}")
    for m in maschere:
        print(f"   {m}")
    print(f"annotazioni che nominano VERDETTO: {len(notizie)}")
    for n in notizie:
        print(f"   {n}")
    print(f"canali della prova riusciti: {len(riusciti)}")
    for r in riusciti:
        print(f"   [{r[0]}] {r[1]}")
    ok = (len(verdetti) == 1 and verdetti[0][0] == "giudizio" and "***" not in verdetti[0][1]
          and not maschere and not notizie
          and (atteso is None or verdetti[0][1].split(":", 1)[1].strip().startswith(atteso)))
    print("CRITERIO:", "REGGE" if ok else "CADE")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
