#!/usr/bin/env bash
# prepara.sh — la parte comune dei lavori «enunciato» e «prova» di giudice.yml (g1458).
# elan + la toolchain del repo (v4.33.1), gli olean di Mathlib dalla cache (nessuna compilazione),
# e lean4export allo stesso commit di casa, costruito sulla v4.33.1 (un esportatore legge solo gli olean della sua versione).
# Si esegue dalla radice del repo, PRIMA che un qualunque byte della prova entri nel progetto.
set -euo pipefail
curl -sSfL https://github.com/leanprover/elan/releases/latest/download/elan-x86_64-unknown-linux-gnu.tar.gz | tar xz
./elan-init -y --default-toolchain none >/dev/null
rm -f elan-init
export PATH="$HOME/.elan/bin:$PATH"
echo "$HOME/.elan/bin" >> "$GITHUB_PATH"
lake exe cache get
git clone -q https://github.com/leanprover/lean4export "$RUNNER_TEMP/lean4export"
( cd "$RUNNER_TEMP/lean4export"
  git checkout -q 05d43a2bc773b40ecfdebb32294192a5ef756951
  echo "leanprover/lean4:v4.33.1" > lean-toolchain
  lake build lean4export
  cp .lake/build/bin/lean4export "$RUNNER_TEMP/lean4export-bin" )
echo "pronto: $(lean --version) · lean4export 05d43a2b su v4.33.1"
