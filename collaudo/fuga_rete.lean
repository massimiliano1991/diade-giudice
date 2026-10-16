-- collaudo/fuga_rete.lean
-- Tentativo di fuga dalla sandbox via rete (curl verso https://example.com).
-- Il throw finale forza un errore lean (:N:M: error …) che il filtro interpreta come RIFIUTA (errore).
-- In sandbox (bwrap --unshare-all ⊇ --unshare-net) curl NON può raggiungere la rete:
--   exit ≠ 0 e stdout vuoto; se curl non esiste nella sandbox, l'eccezione è catturata e riportata.
-- ESITO ATTESO dal giudice: RIFIUTA (errore), e nel log una riga «FUGA_RETE: curl exit=… stdout_bytes=0».
-- (g1473: il blocco `#eval do …` della prima stesura non aveva tipo e non veniva mai eseguito —
--  «don't know how to synthesize implicit argument α», visto dalla Sponda conv 81; ora `show IO Unit from`.)

theorem banale_rete : 1 + 1 = 2 := by rfl

#eval show IO Unit from do
  let esito : String ←
    try
      let r ← IO.Process.output {
        cmd  := "curl"
        args := #["-sSf", "--max-time", "5", "https://example.com"]
      }
      pure s!"curl exit={r.exitCode} stdout_bytes={r.stdout.length} stderr_head={r.stderr.take 120}"
    catch e =>
      pure s!"curl non eseguibile ({e})"
  -- Lancia sempre un errore: il filtro lo conta come RIFIUTA (errore), il log porta l'esito reale.
  throw (IO.userError s!"FUGA_RETE: {esito}")
