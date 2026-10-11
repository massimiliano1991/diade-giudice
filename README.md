# diade-giudice

A public judge for Lean 4 proofs, used by DIADE's math ladder. The judge is Lean's own: `lake comparator`
(Lean v4.35.0-rc4) with five kernels (Lean, leanchecker-paranoid, nanoda, con-leche, con-ron). This repo only runs it,
so that anyone can re-run a verdict with one button instead of trusting the machine that produced the proof.

**How it runs** (`.github/workflows/giudice.yml`, three jobs on three throwaway VMs):
1. `enunciato` builds the challenge (the statement with `sorry`) against Mathlib for Lean v4.33.1 and exports its
   constants with lean4export (`05d43a2b`, built on v4.33.1). No byte of the proof reaches this VM. The sha256 of the
   export becomes a job output.
2. `prova` runs the proof: a plain elaboration plus `#print axioms` (time and peak memory measured), then builds and
   exports it. This is untrusted code, run with no credentials and read-only permissions. Only a data file leaves it.
3. `giudizio` runs nothing from the proof. It checks the challenge export against the sha from job 1, then runs
   `lake comparator --challenge-from-export --solution-from-export` (bubblewrap sandbox when the VM allows it).

**The verdict** is the line `VERDETTO_G0:` (ACCETTA = accepted, RIFIUTA = rejected) in the log of job `giudizio`, and
nothing else. To re-run one: Actions → giudice → Run workflow, or
`gh workflow run giudice.yml -R massimiliano1991/diade-giudice -f enunciato=enunciati/L1-v01.lean -f prova=prove/r1/L1-v01__a1.lean -f bersaglio=mathd_numbertheory_229`.

**Test cases** (`prove/collaudo/`): a real proof must be accepted, the statement itself (with `sorry`) rejected, and
`L1-v01__attacco.lean` (same theorem name, statement replaced by `True`) rejected. The last one passes the plain
elaboration check; only the comparator catches it.

**Limits, stated:** the time and memory figures come from the untrusted VM; they are honest for a cooperative prover,
not against an adversary. Times are from this runner's CPU, not from the machine where the ladder's rules were set.
lean4lean is left out: on v4.33.1 exports it fails even on valid proofs. Statements may import only Mathlib for now.
The comparator says the proof proves *that* statement; whether the statement says what was meant is a separate
question.

Material of DIADE (Vera). Proof files are outputs of DIADE's prover, kept here so verdicts can be re-run.
