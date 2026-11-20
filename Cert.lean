/- The monotonic certification pipeline: core formalization.

A subject is certified over a fixed set of dimensions. Each dimension
carries a value per state, oriented so that a larger value is better.
Evidence for a transition is a chain of recorded increments; a step of
the chain carries the increment relation of the subject together with
the recorded outcome of the incremental check on that step. A
certificate is a single artifact between two states. Its checker
requires, for every dimension it certifies, chain evidence, and it
requires every dimension whose value regressed to be marked
regressed. The spec that this file formalizes is spec.md in this
repository. -/

namespace Cert

/-- The fixed dimension set of a harness subject, as derived in
spec.md section 2. A dimension enters or leaves the set only by
append to the subject's qualification contract; this type is the set
for the first subject. -/
inductive Dim where
  | coverage
  | fidelity
  | solvability
  | reconversibility
  | reweightability
  | speed
  | setup
deriving DecidableEq, Repr

/-- Every dimension of the set, in contract order. -/
def dims : List Dim :=
  [.coverage, .fidelity, .solvability, .reconversibility,
   .reweightability, .speed, .setup]

theorem dims.mem (d : Dim) : d ∈ dims := by
  cases d <;> decide

/-- A per-dimension verdict on a certificate. -/
inductive Verdict where
  | improving
  | flat
  | regressed
  | unmeasured
deriving DecidableEq, Repr

/-- The verdicts under which a dimension reads certified. -/
def certifies : Verdict → Bool
  | .improving => true
  | .flat => true
  | _ => false

section Core

variable {S : Type}
variable (adj : S → S → Prop)
variable (val : Dim → S → Nat)

/-- Chain evidence between two states on one dimension: a recorded
sequence of increments from the earlier state to the later state,
each step carrying the recorded outcome of its incremental check.
The empty chain covers a state against itself. -/
inductive Chain : Dim → S → S → Prop where
  | refl : Chain d a a
  | step : Chain d a b → adj b c → val d b ≤ val d c → Chain d a c

/-- Soundness of chain evidence: a chain between two states proves
the later value is at least the earlier value on its dimension.
This is the incremental-covers-full property at single-transition
grain: the full from-scratch check of the transition is the endpoint
comparison, and the chain discharges it. -/
theorem Chain.sound {d : Dim} {a b : S} (h : Chain adj val d a b) :
    val d a ≤ val d b := by
  induction h with
  | refl => exact Nat.le.refl
  | step _ _ hle ih => exact Nat.le_trans ih hle

/-- Coverage composition: chain evidence over consecutive increments
composes to chain evidence over their join, so a chain of certified
increments certifies the endpoints. This is the
incremental-covers-full property at chain grain. -/
theorem Chain.join {d : Dim} {a b c : S}
    (h₁ : Chain adj val d a b) (h₂ : Chain adj val d b c) :
    Chain adj val d a c := by
  induction h₂ with
  | refl => exact h₁
  | step h hadj hle ih => exact Chain.step ih hadj hle

/-- A certificate: one checkable artifact between two named states,
carrying a verdict per dimension and, where present, the chain
evidence for that dimension between the two states. -/
structure Certificate where
  lo : S
  hi : S
  verdict : Dim → Verdict
  /-- The evidence reference per dimension, as the checker reads it:
  present exactly when the artifact carries chain evidence for that
  dimension. In the data form of the artifact this is the reference
  itself; here it is the reference's presence bit. -/
  flag : Dim → Bool
  /-- The backing the verifier checks: a present reference resolves
  to chain evidence between the certificate's two states. An
  artifact whose reference does not resolve does not typecheck as
  a certificate at all. -/
  backed : ∀ d, flag d = true → Chain adj val d lo hi

/-- The per-dimension clause of the artifact's own checker: a
certified verdict requires chain evidence, and a regressed value
requires the regressed verdict. The checker recomputes the endpoint
values from the states; it trusts no verdict it cannot recompute or
back with evidence. -/
def ok (c : Certificate adj val) (d : Dim) : Bool :=
  ((!certifies (c.verdict d)) || c.flag d) &&
  (!(val d c.lo > val d c.hi) || decide (c.verdict d = .regressed))

/-- The artifact's checker: every dimension's clause holds. -/
def check (c : Certificate adj val) : Bool :=
  dims.all (ok adj val c)

/-- The certificate's overall reading: it reads certified exactly
when its checker passes and every dimension's verdict certifies.
Any regressed or unmeasured dimension blocks the certified
reading. -/
def certified (c : Certificate adj val) : Bool :=
  check adj val c && dims.all (fun d => certifies (c.verdict d))

theorem check.ok {c : Certificate adj val} {d : Dim}
    (h : check adj val c = true) : ok adj val c d = true := by
  have hmem : d ∈ dims := dims.mem d
  simp [check, List.all_eq_true] at h
  exact h d hmem

/-- Certificate soundness: if the checker accepts a certificate and
a dimension's verdict certifies, the dimension's value at the later
state is at least its value at the earlier state. The proof goes
through the chain evidence the checker required, by Chain.sound. -/
theorem check.sound {c : Certificate adj val} {d : Dim}
    (h : check adj val c = true) (hv : certifies (c.verdict d) = true) :
    val d c.lo ≤ val d c.hi := by
  have hok : ((!certifies (c.verdict d) || c.flag d) &&
      (!(val d c.lo > val d c.hi) ||
        decide (c.verdict d = .regressed))) = true :=
    check.ok adj val h (d := d)
  simp only [Bool.and_eq_true] at hok
  have hflag : c.flag d = true := by
    have h1 := hok.1
    simp [hv] at h1
    exact h1
  exact Chain.sound adj val (c.backed d hflag)

/-- Regression honesty: in a certificate the checker accepts, a
dimension whose value regressed cannot carry any verdict but
regressed; in particular it cannot appear certified. This holds by
construction of the checker's second clause, which recomputes the
endpoint values. -/
theorem check.honest {c : Certificate adj val} {d : Dim}
    (h : check adj val c = true)
    (hreg : val d c.hi < val d c.lo) :
    c.verdict d = .regressed := by
  have hok : ((!certifies (c.verdict d) || c.flag d) &&
      (!(val d c.lo > val d c.hi) ||
        decide (c.verdict d = .regressed))) = true :=
    check.ok adj val h (d := d)
  simp only [Bool.and_eq_true] at hok
  have h2 := hok.2
  have hgt : decide (val d c.lo > val d c.hi) = true := by
    rw [decide_eq_true_eq]; exact hreg
  simp only [hgt, Bool.not_true, Bool.false_or] at h2
  exact of_decide_eq_true h2

/-- Corollary of regression honesty: a regressed dimension's
verdict does not certify. -/
theorem check.notcertified {c : Certificate adj val} {d : Dim}
    (h : check adj val c = true)
    (hreg : val d c.hi < val d c.lo) :
    certifies (c.verdict d) = false := by
  rw [check.honest adj val h hreg]
  rfl

/-- Chain certification of endpoints: two accepted certificates
over consecutive increments, each certifying a dimension, certify
that dimension between the outer endpoints. The value comparison
is the composition of the two soundness results; the evidence
composition behind it is Chain.join. -/
theorem check.chain {a b c : S}
    {c₁ : Certificate adj val} {c₂ : Certificate adj val}
    (hlo₁ : c₁.lo = a) (hhi₁ : c₁.hi = b)
    (hlo₂ : c₂.lo = b) (hhi₂ : c₂.hi = c)
    (h₁ : check adj val c₁ = true) (h₂ : check adj val c₂ = true)
    {d : Dim} (hv₁ : certifies (c₁.verdict d) = true)
    (hv₂ : certifies (c₂.verdict d) = true) :
    val d a ≤ val d c := by
  have s₁ := check.sound adj val h₁ hv₁
  have s₂ := check.sound adj val h₂ hv₂
  rw [hlo₁, hhi₁] at s₁
  rw [hlo₂, hhi₂] at s₂
  exact Nat.le_trans s₁ s₂

/-- A certificate that reads certified under the overall reading
is sound on every dimension. -/
theorem certified.sound {c : Certificate adj val} {d : Dim}
    (h : certified adj val c = true) :
    val d c.lo ≤ val d c.hi := by
  have hpair : check adj val c = true ∧
      dims.all (fun d => certifies (c.verdict d)) = true := by
    have h' := h
    simp only [certified, Bool.and_eq_true] at h'
    exact h'
  have hv : certifies (c.verdict d) = true := by
    have hall := hpair.2
    rw [List.all_eq_true] at hall
    exact hall d (dims.mem d)
  exact check.sound adj val hpair.1 hv

end Core

end Cert
