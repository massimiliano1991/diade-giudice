#!/usr/bin/env bash
# ingresso.sh — gli input del workflow si stampano nel log e nel riassunto: solo percorsi e nomi semplici (DIADE g1460).
rf='^[A-Za-z0-9_./-]+\.lean$'; rb='^[A-Za-z0-9_.]+$'
if [[ $E =~ $rf && $P =~ $rf && $B =~ $rb && $E$P != *..* ]]; then exit 0; fi
echo "ingresso non valido: enunciato e prova sono percorsi .lean nel repo, bersaglio un nome Lean semplice"; exit 1
