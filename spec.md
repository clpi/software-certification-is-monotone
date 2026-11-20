# The monotonic certification pipeline — specification

This document specifies the pipeline end to end at agent-proof
resolution: any agent can issue, check, or extend a certificate from
this text alone. Every claim carries one of four states, never
blurred: settled intent (directed, cited), proposed semantics
(stated exactly, not yet built), implemented (present in a tree at a
named pin), verified (executed or proved at a named pin, record on
disk).

Directive: Chris, direct, 2026-11-19 — lane C of the
candidate-space / idol-eyes program: build the monotonic
certification pipeline as its own general construction, with
idol-eyes as its first subject. The standing Q7 ruling (Chris,
2026-11-17) governs the certificate's shape: a release certificate
is a single checkable artifact between two pins.

## 1. Foundation and composition

Foundation (settled intent, canonical): the hypergraph is singular
— the total equivalence graph of equivalent terms, symbol-bound at
minimum resolution; resolved information grows append-only;
qualifications and colorings are constructed from it. The pipeline
is a construction over that foundation: a subject's states are
configurations read from the hypergraph, a dimension's value at a
state is a derived reading over the state's recorded facts, and a
certificate is a derived artifact between two states. List
constructions in any formalization in this repository are finite
models of the construction, never the hypergraph itself.

Composition with the standing release-monotonicity living spec
(~/workspace/research/living-spec-release-monotonicity-2026-11-14.md,
revision 12, section 1.23.10; its data layer holds 8,454 points and
54 certified-monotonic transitions). This pipeline reuses, and does
not redefine:

- the certificate as a single checkable artifact between two named
  states (living spec 1.9, with the monotonicity statement of 1.10);
- projection certification: a certificate names its projection
  exactly and certifies over exactly that (living spec 1.5);
- the baseline read: the earlier state of a certificate is the
  predecessor state on the subject's line, never chosen or frozen
  (living spec 1.2);
- carried verdicts over a change cone: facts outside a transition's
  cone carry their verdicts, facts inside are re-derived (living
  spec 1.16.3, rule of 5.2), at commit and merge grain (1.16);
- the coverage statement: what a certificate did not cover is
  printed on it (living spec 6.5).

Composition with the candidate-space search results in
clpi/software-frontier-is-solvable, cited by theorem name where
used: the returned set of a qualified search is exactly the
nondominated qualified set (Search.optimal); frontiers compound
under joins of spaces (Search.join.frontier); per-axis bounds
compound and tighten under joins (Search.glb.join, Search.tighten);
a weighting never bounds the search and reweighting is exact
(Search.weighted, Search.reweight, Search.full). Section 3 uses the
weighting results to define the reweightability dimension; no
frontier result is re-proved here.

Extensions. Everything in this spec that the living spec lacks is
an extension, flagged here once and never presented as living-spec
text:

- E1, the per-dimension verdict vocabulary of section 5
  (improving, flat, regressed, unmeasured with the gap named). The
  living spec scores three axes with holds, fails, or uncovered
  (its 1.10); the mapping is: improving and flat are holds with the
  direction printed, regressed is fails, unmeasured is uncovered
  with the gap named. The pipeline's finer vocabulary is required
  because its dimension set (section 2) is wider than three axes
  and its issuance is per increment (section 6).
- E2, the dimension-set derivation rule of section 2: the living
  spec contracts three axes for releases; a general subject's
  dimension set is derived from its own qualification contract.
- E3, the coverage obligation of section 4 stated as a chain of
  increment evidences: the living spec states cone-scoped carrying
  (1.16.3) and the anti-unification reason for it (1.17.1); the
  chain form here is that rule read at certificate grain, and its
  Lean form is proved in this repository (section 7).

## 2. The dimension set

Rule (settled intent, extension E2). A subject is certified over a
fixed set of dimensions. The set is derived from the subject's
qualification contract: one dimension for each respect in which the
contract requires the subject to be measurable and in which a
regression would refuse a transition. The set is stated in the
subject's first certificate and thereafter changes only by append:
a dimension enters the set when the contract gains a measurable
respect (the entering certificate names the contract change as its
evidence), and a dimension leaves the set only when the contract
retires the respect, recorded the same way. No certificate may
score a dimension outside the set, and no certificate may omit a
dimension in the set: an unscored dimension prints unmeasured with
its gap named (section 5). Appending a dimension never rewrites a
past certificate; the chain simply carries the wider set from the
appending certificate on.

The harness dimension set. For a harness subject — a subject whose
contract is to perceive, act, and be measured against a standing
comparator, idol-eyes being the first — the standing dimensions
are, with their derivation from the contract:

- coverage: the share of the comparator's verified capability
  surface the subject has built, in the contract's own row or case
  units. Derived from the contract's capability clause.
- fidelity: the faithfulness of the subject's behavior to its own
  stated contracts, measured by its executed contract batteries.
  Derived from the contract's correctness clause.
- solvability: the subject's success on live tasks under the
  contract's acceptance discipline. Derived from the contract's
  task clause.
- reconversibility: the subject's ability to return a fixture or
  environment to a recorded prior state. Derived from the
  contract's campaign discipline, which requires a known pre-state
  before any measurement is trusted.
- reweightability: the subject's search or observation weighting
  can be replaced on the fly without changing the qualified result
  set and without recomputation of what the set is. Derived from
  the candidate-space bet's weighting clause, as proved for the
  search layer in clpi/software-frontier-is-solvable
  (Search.weighted, Search.reweight, Search.full): a weighting
  orders, never bounds.
- speed: the subject's latency on the contract's measured axes
  under matched conditions. Derived from the contract's
  performance clause and its floor records (living spec 1.7).
- setup: the weight of standing the subject up — its pinned
  external inputs and prerequisites — oriented so lighter is
  better. Derived from the contract's distribution clause.

Each dimension's value is a natural-number reading oriented so a
larger value is better; a raw measure that grows when the subject
gets worse (a cost, a count of dependencies) enters through its
stated orientation in the dimension's measure rule (section 3),
never by a silent sign change on a certificate.

## 3. The measurement rule per dimension

Rule (settled intent). Measurement is continuous and empirical:
each measurement is an appended record on the subject's evidence,
carrying the state it was taken at, the contract it was taken
under, the venue, and its outcome. A measurement never rewrites a
prior record; a correction is a new record that names the record it
corrects. A dimension's value at a state is a stated function of
the state's measurement records — the same function at every state,
so two certificates over one transition read the same values.

Measure rules for the harness set (each is the full rule for its
dimension; a subject whose contract names a different unit for a
dimension states its unit in its first certificate and is then
bound by it):

- coverage: the count of built rows, plus the count of partly
  built rows stated separately, in the subject's capability matrix
  against its comparator, each row audited at the state (built:
  present at the row's contract; partly: a real subset present, the
  gap named; absent: not present). The certificate carries both
  counts; the dimension's value is the pair read in contract order,
  and the scalar carried in this repository's first certificate is
  the partly count where built is zero at both states (the general
  comparison is lexicographic: built first, then partly).
- fidelity: the count of executed contract-battery tests passing
  at the state, the battery being the subject's own full check
  target, executed whole in a named venue. The projection is named
  on the certificate: the first subject's projection is offline
  contract fidelity; live fidelity stands under solvability.
- solvability: the count of live tasks solved under the
  acceptance discipline (matched hardware, builds, state,
  permissions, and workload semantics; an effect counts only when
  independently confirmed). No executed campaign, no value: the
  dimension prints unmeasured.
- reconversibility: the count of state-restore producers with an
  executed battery in the subject, a producer being a program that
  records a pre-state, drives to a named baseline, verifies by
  re-observation, and restores the pre-state when restorable. The
  projection (the fixture shapes covered) is named on the
  certificate.
- reweightability: the dimension has a value exactly when the
  subject carries a weighting surface (a weight function over its
  search or observation space, replaceable at any point) and an
  executed check that replacing the weighting leaves the qualified
  result set unchanged, in the shape of Search.reweight. No
  weighting surface, no value: the dimension prints unmeasured.
- speed: the contract's latency readings (p50 and p95 per command
  or workload) under matched conditions against the baseline's
  readings and the floor record. Readings enter the certificate as
  the count of measured axes on which the subject is at or better
  than the earlier state within the axis's stated band, with the
  per-axis readings referenced as evidence. No matched measurement
  at both states, no value: unmeasured.
- setup: the count of pinned external inputs in the subject's own
  manifest, read whole. The certificate carries the raw count; the
  dimension's oriented value (the form the Lean model compares,
  larger is better under P4) is a stated fixed bound minus the
  count, so fewer inputs is a larger oriented value, flat is an
  equal count, and an improving claim on this dimension must show
  a strictly smaller count. The first certificate exercises only
  the flat case. Supporting counts (prerequisites of the check
  target) are evidence, not the value.

## 4. The incremental proof rule

Rule (settled intent). A dimension's monotonic verdict between two
states is certified only when the incremental evidence provably
covers the full from-scratch check of that dimension between those
states. Otherwise the dimension prints unmeasured, with the gap
named. Nothing is certified from a sample, an endpoint comparison,
or a carried verdict whose cone does not cover it.

The coverage obligation, stated precisely. Let the earlier state
be a, the later state be b, and the subject's recorded increments
between them be the steps of its history. Incremental evidence for
a dimension covers the full check when it is a chain: a sequence
of steps from a to b, consecutive, with no step of the history
between a and b missing, and for each step the recorded outcome of
that step's own check on the dimension (the step's value at its
start is at most its value at its end, under the step's measurement
contract). The full from-scratch check of the dimension between a
and b is the endpoint comparison of the dimension's values at a
and b. The chain discharges the obligation because the endpoint
comparison follows from the step outcomes by transitivity — and
for no other reason: an increment whose step outcome is missing,
or a history step not in the chain, leaves the obligation
undischarged, and endpoint equality over a regressed interior is
exactly the failure the standing control of section 7 refutes.

What discharges the obligation, per dimension, in practice — the
three discharge shapes, each of which is a chain in the sense
above:

- D1, full execution at both ends: the dimension's full check is
  itself executed at both states under one contract in one venue
  (a battery run whole, a manifest read whole). The chain is the
  single executed comparison; its step outcome is the recorded run.
- D2, delta audit with carrying: the dimension's full audit exists
  at the earlier state; at the later state, every unit whose
  premises meet the two-state diff is re-audited from later-state
  evidence, and every unit outside the diff's change cone carries
  its earlier state, with the diff itself as evidence that the
  carried set is exactly the untouched set (the cone rule of the
  living spec, 1.16.3). A diff containing a deletion that could
  remove a carried unit discharges nothing for that unit: it is
  re-audited or the dimension prints unmeasured.
- D3, chain of certificates: where certificates already cover
  consecutive increments between a and b, their composition
  discharges the endpoints, by coverage composition (section 7,
  Cert.Chain.join and Cert.check.chain). This is the
  incremental-covers-full property at chain grain: the chain of
  per-increment certificates is the evidence, and no from-scratch
  recomputation of the whole span is performed or needed.

Never blindly recompute (settled intent): a discharge that
recomputes what a carried chain already certifies is a defect of
the issuance, not thoroughness; recomputation is scoped to what
the carried foundation does not certify.

## 5. The certificate

Form (settled intent, with extension E1). A certificate is a
single checkable artifact between two named states (pins). It
carries exactly:

- the subject, the earlier pin, the later pin, the issuer, and the
  issuance date;
- the dimension set scored (section 2), in contract order;
- per dimension: the verdict — one of improving, flat, regressed,
  or unmeasured; for a measured verdict, the value at the earlier
  state, the value at the later state, the evidence references,
  and the coverage discharge (which of D1, D2, D3, and over what
  projection); for unmeasured, the gap named and its closing route
  with an owner;
- the list of regressed dimensions, printed as its own field;
- the overall reading, computed by the reading rule, never
  asserted independently of it.

Reading rule. The certificate reads certified exactly when every
dimension's verdict is improving or flat with its coverage
discharged. A regressed dimension blocks the certified reading:
the artifact states the regression in its per-dimension verdict
and in the regressed list; it does not hide it, average it away, or
offset it against an improving dimension. An unmeasured dimension
likewise blocks the certified reading and prints with its gap. In
every other case the reading is the words not certified, with the
blocking dimensions printed.

Checker. The artifact's checker (certificates/check.py for the
data form; Cert.check in the Lean form) re-reads the artifact,
refuses by name any measured verdict whose values contradict it,
any unmeasured verdict without a named gap and closing route, any
dimension-set mismatch, and recomputes the overall reading from
the per-dimension verdicts, refusing the artifact when the printed
reading differs. In the Lean form the checker additionally
requires chain evidence behind every certified verdict and the
regressed verdict behind every regressed value, and both
requirements are proved, not asserted (section 7).

Relation to the living spec's certificate (1.9): the fields above
are the monotonicity statement of 1.10 in this pipeline's
vocabulary (E1's mapping), over the projection the certificate
names (1.5). Threshold signing, series position, and the leakage
budget of 1.9 are living-spec fields for release certificates in
its own program; a pipeline certificate adopted into that program
carries them in addition, and their absence here is a stated
scope fact, not a redefinition: this pipeline's certificates are
single-producer certificates at the independence grade of living
spec 1.11, printed as such in the lane record.

## 6. Issuance per increment

Rule (settled intent). Every state change of the subject issues a
new certificate against its predecessor, forming the chain that
the living spec's transition record extends: certificate n + 1's
earlier pin is certificate n's later pin, and the chain is
append-only — a certificate is never edited after issuance; a
correction is a new certificate against the same predecessor,
naming the certificate it corrects. The first certificate of a
subject is issued against the earliest state the lane can read
firsthand, and states that fact. Composition over the chain is by
D3: the endpoints of any span are certified by the span's chain
when every link certifies the dimension, and a span containing a
regressed or unmeasured link certifies nothing over that link's
dimension — the span's own certificate, when issued, prints that
dimension from the span's evidence or as unmeasured, never as
carried through the broken link.

## 7. The Lean formalization

Implemented and verified in this repository at its landing pin,
Lean 4.19.0, family gate cold pass (check.sh: no proof escapes,
warnings as errors), zero sorries. The formalization models a
subject by a state type, an increment relation between states, and
a value function per dimension; a certificate is the structure of
section 5 with an evidence flag per dimension backed by chain
evidence. Theorem inventory, with states and axiom sets as printed
by Axioms.lean at the landing pin:

- Cert.Chain.sound — certificate soundness at chain grain: chain
  evidence between two states proves the later value is at least
  the earlier value on its dimension. Verified; depends on no
  axioms.
- Cert.Chain.join — coverage composition: chain evidence over
  consecutive increments composes to chain evidence over their
  join. Verified; depends on no axioms.
- Cert.check.sound — certificate soundness: an accepted
  certificate's certified dimension is monotone between its two
  states. Verified; axioms: propext, Quot.sound.
- Cert.check.honest — regression honesty: in an accepted
  certificate, a dimension whose value regressed carries the
  regressed verdict. Verified; axioms: propext, Quot.sound.
- Cert.check.notcertified — corollary: a regressed dimension's
  verdict does not certify in an accepted certificate. Verified;
  axioms: propext, Quot.sound.
- Cert.check.chain — chain certification of endpoints from two
  consecutive accepted certificates. Verified; axioms: propext,
  Quot.sound.
- Cert.certified.sound — a certificate under the overall certified
  reading is sound on every dimension. Verified; axioms: propext,
  Quot.sound.
- Control.control — the refuted control: on the named three-state
  instance (values 10, 0, 10 under the successor increment
  relation), the endpoint-only checker accepts, the interior
  regresses, no chain evidence exists, and the pipeline's checker
  rejects the matching claim. Verified; axioms: propext,
  Quot.sound. A control that starts passing is a defect in the
  pipeline, not in the control.

Premises, each with its falsification route. The theorems are
proved from the model's construction; what the model assumes
about the world is exactly:

- P1, the measure is a function of state: a dimension's value is a
  function from states to readings (in Lean, the value is a
  function by type). Falsification: two measurement records at one
  state, under one contract, giving different values with no state
  change between them — such a pair refuses the dimension's
  evidence until the measure rule is repaired.
- P2, the increment relation is the subject's recorded history:
  the relation holds exactly for the subject's recorded state
  changes, so a chain in the model is a chain in the history.
  Falsification: a recorded state change with no corresponding
  step — the audit of history against the relation finds it, and
  until the step is recorded no chain may cross it (the failure is
  closed-world: missing steps make coverage unprovable, never
  silently true).
- P3, a step's recorded outcome is an executed check: in Lean a
  chain step carries a proof of its inequality, so a false step
  cannot be constructed inside the model; the premise binds the
  producer outside it — a step record is admitted only from an
  executed incremental measurement. Falsification: re-measure the
  step under its contract; a mismatch refuses the step's evidence
  and every certificate whose chain uses it.
- P4, orientation: every dimension's value is oriented larger is
  better, by its measure rule (section 3). Falsification: a
  dimension whose larger reading is worse under its contract —
  the measure rule is repaired and the dimension's certificates
  re-issued; past certificates stand as issued, with the repair
  recorded.

## 8. The first subject

The pipeline's first subject is clpi/idol-eyes. Its first
certificate (certificates/idol-eyes-d29300b-to-d7e7b00.json,
checked by certificates/check.py, output in
certificates/check-output.txt) is issued between the 2026-11-06
beat-record baseline pin and the head read firsthand by the
issuing lane, and its overall reading is exactly what its evidence
supports: not certified — no dimension regressed; coverage,
fidelity, and reconversibility improving with discharges stated;
setup flat; solvability, reweightability, and speed unmeasured
with gaps and closing routes named on the artifact. The full
issuance record, including the executed make check verdicts at
both pins, is the lane record of the issuing lane.

## 9. Open gaps of this specification

- The general (non-harness) dimension-set derivation is stated as
  a rule (section 2) and instantiated only for the harness set;
  a second subject family is the closing route for its general
  form. Owner: the next subject lane.
- The lexicographic coverage comparison (built before partly) is
  stated in section 3 and exercised only in its degenerate case
  (built zero at both states); a subject state with built rows is
  the closing route. Owner: the idol-eyes lane, when a row first
  closes built.
- Speed's per-axis band discipline is inherited from the living
  spec's floor records (1.7); no floor record exists yet for the
  first subject, so the dimension's first measured certificate
  must land its floor records first. Owner: the idol-eyes campaign
  lane.
- The data-form checker verifies internal consistency and the
  reading rule; it does not re-read the subject's repositories.
  Binding the data form to the Lean checker (the artifact as a
  Lean certificate term) is proposed, with the closing route of
  generating the term from the artifact and checking it under the
  family gate. Owner: lane C follow-up.
