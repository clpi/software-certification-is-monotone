# software-certification-is-monotone

Lean 4.19.0 statements and proofs for the monotonic certification
pipeline: a general construction that certifies a qualified subject
as monotone over a fixed set of semantic dimensions, by a single
checkable artifact between two named states, from incremental
evidence that provably covers the full check. The full
specification is [spec.md](spec.md). The pipeline is a general
construction over any qualified subject, not a frontier-search
result and not a component of its first subject; idol-eyes is its
first subject, not its home.

The pipeline composes with the standing release-monotonicity
living spec (revision 12, section 1.23.10; 8,454 data points, 54
certified-monotonic transitions): it reuses that spec's
certificate form (its 1.9 and 1.10), projection rule (1.5),
baseline read (1.2), and cone-carried verdicts (1.16.3), and flags
its own additions as extensions in spec.md section 1. It cites the
candidate-space search results of clpi/software-frontier-is-solvable
by theorem name (Search.optimal, Search.join.frontier,
Search.glb.join, Search.tighten, Search.weighted, Search.reweight,
Search.full) where the dimension definitions use them; it
re-proves none of them.

## What is proved

A subject is modeled by a state type, an increment relation, and a
value function per dimension (seven harness dimensions:
coverage, fidelity, solvability, reconversibility,
reweightability, speed, setup). Evidence for a transition is a
chain of recorded increments, each step carrying its incremental
check outcome.

- `Cert.Chain.sound`: chain evidence proves the endpoint
  comparison — the incremental-covers-full property at transition
  grain. Depends on no axioms.
- `Cert.Chain.join`: coverage of consecutive increments composes
  to coverage of their join — the property at chain grain.
  Depends on no axioms.
- `Cert.check.sound`: an accepted certificate's certified
  dimension is monotone between its two states.
- `Cert.check.honest`: a regressed dimension cannot appear with
  any verdict but regressed in an accepted certificate — by
  construction of the artifact's own checker, which recomputes
  endpoint values and requires chain evidence behind every
  certified verdict. `Cert.check.notcertified` is the corollary
  that a regressed dimension never reads certified.
- `Cert.check.chain` and `Cert.certified.sound`: endpoints of a
  chain of accepted certificates are certified, and a certificate
  under the overall certified reading is sound on every dimension.
- `Control.control`: the standing refuted control — endpoint-only
  comparison accepts a three-state transition (values 10, 0, 10)
  whose interior regresses; no chain evidence for it exists, and
  the pipeline's checker rejects the matching claim.

The checker theorems and the control depend on exactly the axioms
propext and Quot.sound, as printed by Axioms.lean. The premises
the model assumes about the world (the measure is a function of
state; the increment relation is the recorded history; a step's
record is an executed check; orientation) are stated in spec.md
section 7, each with its falsification route.

## The first certificate

[certificates/idol-eyes-d29300b-to-d7e7b00.json](certificates/idol-eyes-d29300b-to-d7e7b00.json)
is the pipeline's first issuance, for clpi/idol-eyes between the
2026-11-06 beat-record baseline pin
d29300b68502af4c303e3a226477f5f6532d445f and the head
d7e7b009e735334bb2cbcff25db41320450ab051 read firsthand by the
issuing lane. Its overall reading is **not certified**: no
dimension regressed; coverage (18 to 23 partly rows of the 72-row
matrix), fidelity (21 to 126 executed contract tests), and
reconversibility (0 to 1 restore producers) improve with coverage
discharges stated on the artifact; setup is flat (2 pinned inputs
at both pins); solvability, reweightability, and speed are
unmeasured, each with its gap and closing route named on the
artifact. `certificates/check.py` recomputes the reading and
refuses inconsistency; its run output is
`certificates/check-output.txt`.

## Reproduce

```sh
./check.sh
```

`./check.sh` rejects proof escapes, builds under warnings as
errors (the build prints the axiom audit), and runs the
certificate checker over the first certificate.
