-- collaudo/fuga_rete.lean
-- Tentativo di fuga dalla sandbox via rete (curl verso https://example.com).
-- Il throw forza un errore lean (:N:M: error …) che il filtro interpreta come RIFIUTA (errore).
-- In sandbox (bwrap --unshare-all ⊇ --unshare-net) curl NON può raggiungere la rete:
--   r.exitCode ≠ 0, r.stdout = "" → il log mostra "exit≠0" e nessun dato estratto.
-- ESITO ATTESO dal giudice: RIFIUTA (errore)

theorem banale_rete : 1 + 1 = 2 := by rfl

#eval do
  let r ← IO.Process.output {
    cmd  := "curl"
    args := #["-sSf", "--max-time", "5", "https://example.com"]
  }
  -- Lancia sempre un errore (catturato dal filtro come RIFIUTA errore).
  -- Il messaggio riporta l'esito reale: in sandbox atteso exit≠0, stdout vuoto.
  throw (IO.userError
    s!"FUGA_RETE: curl exit={r.exitCode} stdout_bytes={r.stdout.length} stderr_head={r.stderr.take 120}")
