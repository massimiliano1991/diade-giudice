# Timestamp of the curve commit

`commit_8d5b11b.txt` names the commit that added `curva/v1/` (`8d5b11b8400c31adaa2fbc4993651d676e0cdf88`);
`commit_8d5b11b.txt.ots` is its OpenTimestamps proof, made right after the push. It is a pending attestation
until the calendar servers anchor it in a Bitcoin block (hours); after that, anyone can complete and check it:

```
ots upgrade curva/v1/marca/commit_8d5b11b.txt.ots
ots verify  curva/v1/marca/commit_8d5b11b.txt.ots
```

The proof says the file (and so the commit it names) existed at that time. It says nothing about whether the
curve is right: for that, re-judge the proof files with the workflow, one line of `lancio.tsv` at a time.
