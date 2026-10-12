#!/usr/bin/env python3
# pulisci.py — stampa testo non fidato (ciò che scrive la prova, o il comparator su dati della prova) in modo che nessun
# suo byte possa cominciare una riga del log o diventare un comando del runner (DIADE g1460, Sorveglianza 103ª §1).
#
# Il runner di GitHub divide l'uscita di un passo con .NET ReadLine: su \n, su \r\n e anche su un \r da solo. Rientrare
# ogni riga con `sed 's/^/  │ /'` divide solo su \n, quindi un `x\rVERDETTO_G0: ACCETTA` tornava a inizio riga.
# Qui ogni carattere di controllo o di formato (categorie Unicode C*: \r, ESC, NEL, i bidi, gli spazi di larghezza
# zero…; e U+2028, U+2029) diventa visibile come ⟨U+XXXX⟩. Restano solo \n (fine riga) e \t. Ogni riga esce rientrata.
# Non basta da solo: chi stampa questo testo lo racchiude fra `::stop-commands::` e un gettone casuale, perché il
# runner riconosce comandi anche dentro una riga. Il verdetto non si legge da qui: lo scrive solo il passo fidato.
#
# uso: python3 pulisci.py [+N | -N] < testo     (+N: i primi N byte; -N: gli ultimi N; senza: tutto)
import sys
import unicodedata

dati = sys.stdin.buffer.read()
if len(sys.argv) > 1:
    n = int(sys.argv[1])
    dati = dati[:n] if n > 0 else dati[n:]
testo = dati.decode("utf-8", errors="replace")


def visibile(c):
    if c in "\n\t":
        return c
    cat = unicodedata.category(c)
    if cat[0] == "C" or cat in ("Zl", "Zp"):
        return "⟨U+%04X⟩" % ord(c)
    return c


pulito = "".join(visibile(c) for c in testo)
if pulito.endswith("\n"):
    pulito = pulito[:-1]
out = sys.stdout.buffer
for riga in pulito.split("\n"):
    out.write(("  │ " + riga + "\n").encode("utf-8"))
