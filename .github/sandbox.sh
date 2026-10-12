#!/usr/bin/env bash
# sandbox.sh — esegue un comando sul codice della prova dentro bubblewrap (DIADE g1460, Sorveglianza 103ª §1).
# Lean esegue codice mentre elabora (`#eval`, `initialize`, le macro): fuori dalla sandbox la prova aveva sudo, i file di
# comando del runner (il riassunto del lavoro, gli output, l'env) e la rete.
# Dentro vede: /usr e /etc in sola lettura, la toolchain del repo in sola lettura (chiamata diretta, senza il proxy di
# elan), la cartella del repo in scrittura (tranne .git, in sola lettura), lean4export in sola lettura, /tmp vuoto.
# Non vede: il resto della home del runner, $RUNNER_TEMP (i file di comando e la cartella fidata), la rete, le
# variabili d'ambiente. sudo non funziona: bubblewrap mette sempre no_new_privs.
# Dopo la sandbox nessun passo fidato esegue niente dalla cartella del repo: gli attrezzi fidati stanno in
# $RUNNER_TEMP/fidato, copiati prima che un byte della prova giri.
set -euo pipefail
W="$GITHUB_WORKSPACE"
TC="$HOME/.elan/toolchains/$(sed 's|/|--|; s|:|---|' "$W/lean-toolchain")"
test -x "$TC/bin/lake" || { echo "sandbox: manca $TC/bin/lake" >&2; exit 2; }
exec bwrap --die-with-parent --new-session --unshare-all --clearenv \
  --ro-bind /usr /usr --symlink usr/bin /bin --symlink usr/sbin /sbin --symlink usr/lib /lib --symlink usr/lib64 /lib64 \
  --ro-bind /etc /etc --proc /proc --dev /dev --tmpfs /tmp \
  --tmpfs /home --ro-bind "$HOME/.elan" "$HOME/.elan" \
  --bind "$W" "$W" --ro-bind "$W/.git" "$W/.git" \
  --ro-bind "$RUNNER_TEMP/fidato/lean4export" /opt/lean4export \
  --chdir "$W" --setenv HOME "$HOME" --setenv PATH "$TC/bin:/usr/bin:/bin" --setenv LANG C.UTF-8 \
  -- "$@"
