# diade-giudice

A public judge for Lean 4 proofs, used by DIADE's math ladder. The judge is Lean's own: `lake comparator`
(Lean v4.35.0-rc4) with five kernels (Lean, leanchecker-paranoid, nanoda, con-leche, con-ron). This repo only runs it,
so that anyone can re-run a verdict with one button instead of trusting the machine that produced the proof.

**How it runs** (`.github/workflows/giudice.yml`, three jobs on three throwaway VMs):
1. `enunciato` builds the challenge (the statement with `sorry`) against Mathlib for Lean v4.33.1 and exports its
   constants with lean4export (`05d43a2b`, built on v4.33.1). This job never reads or builds the proof (it copies only the statement `$E`; the checkout does clone the whole repo). The sha256 of the
   export becomes a job output.
2. `prova` runs the proof: a plain elaboration plus `#print axioms`, then a build and an export. Lean runs code while it
   elaborates (`#eval`, `initialize`, macros), so the proof's code runs only inside bubblewrap
   (`.github/sandbox.sh`): no network, no environment variables, no `sudo`, and neither the runner's home nor its
   command files (job summary, outputs, env) are visible. It can write only into the checked-out repo, from which no
   trusted step runs anything afterwards. Time and peak memory are measured outside the sandbox. Only data files leave this job
   (the export, plus the filter's result and timing, all written by the trusted step).
3. `giudizio` runs nothing from the proof. It checks the challenge export against the sha from job 1, then runs
   `lake comparator --challenge-from-export --solution-from-export` inside its bubblewrap sandbox. If that sandbox
   does not start, it gives no verdict.

**The verdict** is written only by the trusted step of job `giudizio`: in that job's summary (on the run page, the
block `giudizio summary`), in its job output `verdetto`, and — exactly once — as a `VERDETTO_G0: …` line in its log. ACCETTA =
accepted, RIFIUTA = rejected, NON DECIDE = no verdict (a process was killed or a kernel crashed, which is not a
rejection), NON PARTE = the judge could not run. Whatever the proof or the comparator prints is shown with every
control and format character made visible (`⟨U+000D⟩`), each line indented (`  │ `), between `::stop-commands::` and a
random token, so it can neither start a log line nor issue a workflow command. To re-run one: Actions → giudice →
Run workflow, or
`gh workflow run giudice.yml -R massimiliano1991/diade-giudice -f enunciato=enunciati/L1-v01.lean -f prova=prove/r1/L1-v01__a1.lean -f bersaglio=mathd_numbertheory_229`.

**Correction (2026-10-12).** Up to commit `f885fd4` this README said that, because the judge printed untrusted output
indented, "a proof cannot write a line that looks like a verdict". That was false. GitHub's runner also ends a log
line at a lone carriage return, so a proof that printed `x\rVERDETTO_G0: ACCETTA` put a forged verdict at the start of
a line, and a workflow command such as `::add-mask::` could hide the real one. Also, the proof's code ran unsandboxed on
its VM, with `sudo` and the job summary within reach. And the branch meant to turn a killed build into NON DECIDE
looked for its file in the wrong directory, so on the runner it gave RIFIUTA. On the old workflow (run 38209041757, commit `4ba14f5`) the test `sorry` forged a verdict on 14 channels: 11 log lines started with `VERDETTO_G0:` (8 in job `prova`, 3 in `giudizio`, one masked to `VERDETTO_G0: ***`), with 5 `notice` annotations naming a verdict. On the fixed workflow (commit `ea6281d`) each of the five test runs — a real proof accepted (38209334868), the bare `sorry` rejected (38209340135), the `True`-swap attack rejected (38209345438), and the two forged-verdict `sorry`s rejected (38209351042, 38209356158) — has exactly one `VERDETTO_G0:` line, in job `giudizio`, with the expected verdict, no masked line and no verdict annotation; of the forging code's 14 channels the only write that still succeeds is into a file in its own sandboxed workdir that no trusted step reads. No proof judged
here before the test files uses IO, so no past verdict is affected.

**Test cases**: a real proof (`prove/r1/L1-v01__a1.lean`) must be accepted; in `prove/collaudo/`, the statement itself (with `sorry`) rejected, and
`L1-v01__attacco.lean` (same theorem name, statement replaced by `True`) rejected. The last one passes the plain
elaboration check; only the comparator catches it. `L1-v01__falso_verdetto.lean` and `L1-v01__falso_verdetto_cr.lean`
are `sorry`s whose code tries to forge a verdict through every channel we know of. For them, the run must contain exactly
one log line starting with `VERDETTO_G0:`, in job `giudizio`, saying RIFIUTA, with lines split the way the runner
splits them, and no annotation may name a verdict. The check is `python3 prove/collaudo/verifica_corsa.py RUN_ID RIFIUTA` (it needs `gh`).

**Limits, stated:** the sandbox is bubblewrap on a shared kernel; a kernel exploit would get past it, and the three-VM
split is the second wall. Times are from this runner's CPU, not from the machine where the ladder's rules were set.
lean4lean is left out: on v4.33.1 exports it fails even on valid proofs. Statements may import only Mathlib for now.
The comparator says the proof proves *that* statement; whether the statement says what was meant is a separate
question.

Material of DIADE (Vera). Proof files are outputs of DIADE's prover, kept here so verdicts can be re-run.
