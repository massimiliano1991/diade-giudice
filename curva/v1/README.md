# The v1 curve — the visible half, with the rows it follows from

This folder publishes the result of the first three runs (`r1`, `r2`, `r3`) of DIADE's math ladder (`v1`),
so that the figure can be checked from outside. **It goes out because the figure of G1 can be checked from
outside; the how stays at home.** What stays at home: the prover (the model, its prompt and its wrapper), the
runner that drives it, and the blind half of the ladder, of which only the counts appear here.

## What the ladder is

Five levels of `Lean 4` statements, chosen by the category of their source, not by anyone's judgement of
difficulty (whether the levels really get harder is a hypothesis the curve tests):

| level | what | from where |
|---|---|---|
| L1 | calibration: computation and easy contest | miniF2F test, `mathd_*` names |
| L2 | contest | miniF2F test `amc12*`, `aime*`, `imo*` + PutnamBench statements without `_solution` |
| L3 | known proof | google-deepmind/formal-conjectures: `@[category textbook]`, or `research solved` with a Lean formal proof |
| L4 | solved, no Lean proof | formal-conjectures: `@[category research solved]` without a Lean `formal_proof` |
| L5 | open | formal-conjectures: `@[category research open]` |

Each level has twenty statements, split in two halves by a salted hash: the **visible** half, which is what
this folder shows, and the **blind** half, which nobody at home reads (its list is committed, and the runner
prints only its counts). The prover gets up to `k` attempts per statement; a judged attempt is a SÌ only if the
home judge (`lake comparator` with the same kernels as `.github/workflows/giudice.yml` here) accepts it.

## What is here

- `curva_vera.jsonl` — one row per run, level and half: `n`, `pass1_*`, `passk_*`, `k`, how many extractions
  were removed (`tolte`), unknown (`ignote`) or re-judged by hand (`a_mano`). Rows with `"meta": "cieca"` are the
  blind half: counts only, no names. This is the file the home figure is read from.
- `corse/r1.jsonl`, `corse/r2.jsonl`, `corse/r3.jsonl` — every attempt of the visible half, in time order:
  statement id, level, attempt number, sha256 prefix of the proof file, Lean time, phase (`filtro` or `giudice`),
  `passa`, the judge's diagnostic. Four fields of the home ledger are omitted (tokens in, tokens out, cost, model time):
  they describe the prover. Home paths in diagnostics are shortened to `~`.
- `corse/a_mano.jsonl` — the verdicts given by hand after a home failure (memory guard, judge not starting,
  attempt in flight at a stop), each with the sha of the file it judged and, where one was run, the link to the
  public run of this repo's judge.
- `sequenza/r1.md`, `sequenza/r2.md`, `sequenza/r3.md` — the table of the true sequence (rule D7 below) for each
  run, as the home program prints it: closing count vs true count per level and half, and every statement
  where the two differ, named for the visible half, counted only for the blind one.
- `prove/rN/<id>__a<attempt>.lean` — the proof file of every accepted attempt of the visible half. The sha256 of
  each file starts with the `sha256` field of its row.
- `lancio.tsv` — one line per accepted attempt: run, id, attempt, level, proof path, statement path, target
  theorem name, sha prefix. Everything the judge workflow needs.
- `../../enunciati/<id>.lean` — the statement (with `sorry`) of every id that has an accepted attempt.

## The counting rule (D7, as written at home before the verdicts)

For each statement, all of the prover's extractions count, in time order and across restarts. A home failure
(memory guard, judge not starting, extraction in flight at a stop) with its file still present is judged by hand;
without the file it is removed and the next extraction takes its place; if the hand verdict fails too, the
extraction is unknown and the curve gives both bounds (`pass1_min`/`pass1_max`). A memory cap hit or a time-out is
the prover's NO, not a home failure. `pass@1` is the first remaining extraction; `pass@k` is a SÌ among the
first `k` remaining. The rule can only lower the figure, except for a hand SÌ on an extraction killed by the
home machine, and every such case is named in `sequenza/`.

## How to check a SÌ from outside

Pick a line of `lancio.tsv` and run the judge of this repo on it, on GitHub's machines, with one button:

```
gh workflow run giudice.yml -R massimiliano1991/diade-giudice \
  -f enunciato=enunciati/L1-v07.lean -f prova=curva/v1/prove/r1/L1-v07__a1.lean -f bersaglio=mathd_numbertheory_551
```

The verdict is the `verdetto` output of job `giudizio` (also in its summary and as the last `VERDETTO_G0:` line
of its log). Times in the home rows were measured on the home machine and are not the workflow's; the home time
cap does not apply here. To check that the proof files are the ones the rows name:

```
cut -f5,8 curva/v1/lancio.tsv | tail -n +2 | while read f s; do sha256sum "$f" | grep -q "^$s" || echo "DIFF $f"; done
```

To recount the accepted attempts from the rows (one line per SÌ in `corse/`, one file per line in `lancio.tsv`):

```
grep -h '"passa": true' curva/v1/corse/r[123].jsonl | wc -l ; tail -n +2 curva/v1/lancio.tsv | wc -l
```

## What this does not show

Not the prover, not its prompt, not the runner, not the blind half's names or files. Not a claim that the
levels are ordered by difficulty. Not the figures of later versions of the ladder: this is v1, runs r1 to r3,
and later runs will be added in their own folder with their own commit and timestamp.

## Timestamp

The commit that adds this folder is timestamped with OpenTimestamps; the `.ots` file (for a text file containing
the commit's sha) is added in the next commit, under `marca/`. `ots verify` on it proves the folder existed at
that time, not that its content is right: that, only the judge can say, one file at a time.
