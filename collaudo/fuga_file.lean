-- collaudo/fuga_file.lean
-- Tentativo di fuga dalla sandbox via scrittura di file fuori dalla cartella di lavoro.
-- Il throw finale forza un errore lean (:N:M: error …) → RIFIUTA (errore).
-- In sandbox (bwrap): /tmp è un tmpfs isolato; scrivere /tmp/fuga_diade riesce DENTRO
-- la sandbox ma il file NON esiste sul filesystem reale del runner dopo l'uscita.
-- $HOME/fuga_diade: /home è tmpfs in sandbox → stesso isolamento.
-- ESITO ATTESO dal giudice: RIFIUTA (errore), e nel log una riga «FUGA_FILE: /tmp=… | HOME=…».
-- (g1473: `#eval do …` senza tipo non veniva eseguito — ora `show IO Unit from`.)

theorem banale_file : 1 + 1 = 2 := by rfl

#eval show IO Unit from do
  -- Tentativo 1: /tmp/fuga_diade
  let esito1 : String ←
    try
      IO.FS.writeFile "/tmp/fuga_diade" "fuga_diade_DIADE"
      pure "SCRITTO (sandbox tmpfs — NON persiste fuori)"
    catch e =>
      pure s!"FALLITO ({e})"
  -- Tentativo 2: $HOME/fuga_diade
  let home := (← IO.getEnv "HOME").getD "/non-disponibile"
  let esito2 : String ←
    try
      IO.FS.writeFile (home ++ "/fuga_diade") "fuga_diade_DIADE"
      pure s!"SCRITTO in {home}/fuga_diade (sandbox tmpfs /home — NON persiste fuori)"
    catch e =>
      pure s!"FALLITO in {home}/fuga_diade ({e})"
  -- Lancia sempre un errore con il resoconto (il filtro lo conta come RIFIUTA errore).
  throw (IO.userError s!"FUGA_FILE: /tmp={esito1} | HOME={esito2}")
