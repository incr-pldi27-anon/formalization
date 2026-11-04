# Incr formalization

## Build

Install [elan](https://github.com/leanprover/elan) and run:

```sh
lake exe cache get
lake build
```

## Soundness theorems

| Paper result | Lean declaration | Source |
| --- | --- | --- |
| Theorem D.9: Terminating soundness | `Incr.Incr.thm_sound` | [`Incr/Incr/Soundness/Proof.lean`](Incr/Incr/Soundness/Proof.lean) |
| Theorem E.12: Terminating live-mode soundness | `Incr.IncrPP.thm_sound` | [`Incr/IncrPP/Soundness/Proof.lean`](Incr/IncrPP/Soundness/Proof.lean) |

## Comparator

Both theorems are checked with the `lake comparator` command that ships with
Lean. Run it from the repository root:

```sh
lake comparator --config comparator/comparator.json
```

The challenge in `comparator/Challenge.lean` states both theorems without
proofs. The solution is the proof in this repository. Expected output ends with:

```
Lean default kernel accepts the solution
Your solution is okay!
```

Add `--paranoid` flag to run every checker that ships with Lean. This requires
`bwrap` (bubblewrap) to be installed.
