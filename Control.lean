/- The standing refuted control: endpoint-only comparison.

A naive checker that compares only the endpoints of a transition
accepts the transition below, whose middle state regresses. The
pipeline's checker rejects the matching certificate, and no chain
evidence for the transition exists, because the step into the
middle state fails its incremental check. This control refutes
endpoint-only comparison as a certification method; if it ever
starts passing, the pipeline is defective, not the control. -/

import Cert

namespace Control

open Cert

/-- The increment relation of the control subject: each recorded
increment advances the state by exactly one. -/
def step : Nat → Nat → Prop :=
  fun a b => b = a + 1

/-- The control readings: the value falls at the middle state and
recovers at the end state. -/
def bad : Dim → Nat → Nat :=
  fun _ s => if s = 1 then 0 else 10

theorem bad.zero (d : Dim) : bad d 0 = 10 := rfl

theorem bad.one (d : Dim) : bad d 1 = 0 := rfl

theorem bad.two (d : Dim) : bad d 2 = 10 := rfl

/-- The interior regression: the middle state is worse than the
start state. -/
theorem interior (d : Dim) : bad d 1 < bad d 0 := by
  rw [bad.one, bad.zero]
  decide

/-- The endpoint comparison passes: the end value is at least the
start value. -/
theorem endpoint (d : Dim) : bad d 0 ≤ bad d 2 := by
  rw [bad.zero, bad.two]
  decide

/-- Cutting a chain at an intermediate state: with the successor
increment relation, a chain from a to b contains a chain from a to
every state between them. -/
theorem cut {val : Dim → Nat → Nat} {d : Dim} {a b : Nat}
    (h : Chain step val d a b) :
    ∀ {k : Nat}, a ≤ k → k ≤ b → Chain step val d a k := by
  induction h with
  | refl =>
      intro k hak hkb
      have hkk : k = a := by omega
      subst hkk
      exact Chain.refl
  | step h hadj hle ih =>
      rename_i pred last
      intro k hak hkb
      have hc : last = pred + 1 := hadj
      by_cases hk : k ≤ pred
      · exact ih hak hk
      · have hkk : k = last := by omega
        subst hkk
        exact Chain.step h hadj hle

/-- No chain evidence covers the control transition: any chain
from the start state to the end state cuts at the middle state,
and soundness of the cut chain would contradict the interior
regression. -/
theorem nochain (d : Dim) : ¬ Chain step bad d 0 2 := by
  intro h
  have hcut := cut h (k := 1) (by omega) (by omega)
  have hsound := Chain.sound step bad hcut
  rw [bad.zero, bad.one] at hsound
  exact Nat.not_succ_le_zero 9 hsound

/-- The endpoint-only checker: it compares the two endpoint values
and nothing else. -/
def naive (val : Dim → Nat → Nat) (lo hi : Nat) (d : Dim) : Bool :=
  decide (val d lo ≤ val d hi)

/-- The matching certificate under the pipeline: it claims the
flat verdict on every dimension and carries no evidence. -/
def claim : Certificate step bad where
  lo := 0
  hi := 2
  verdict := fun _ => .flat
  flag := fun _ => false
  backed := fun _ h => by simp at h

/-- The endpoint-only checker accepts the claim's transition. -/
theorem naiveaccepts (d : Dim) : naive bad 0 2 d = true := by
  simp [naive, endpoint d]

/-- The pipeline's checker rejects the claim: its flat verdict
certifies, so the checker requires chain evidence, and the claim
carries none. -/
theorem rejected : check step bad claim = false := by
  cases hc : check step bad claim with
  | false => rfl
  | true =>
      exfalso
      have hok : ((!certifies (claim.verdict .coverage) ||
          claim.flag .coverage) &&
          (!(bad .coverage claim.lo > bad .coverage claim.hi) ||
            decide (claim.verdict .coverage = .regressed))) = true :=
        check.ok step bad hc (d := .coverage)
      simp only [Bool.and_eq_true] at hok
      have h1 := hok.1
      simp [claim] at h1
      exact (by decide : ¬ certifies Verdict.flat = false) h1

/-- The assembled control: the endpoint-only checker accepts, the
interior regresses, no chain evidence exists, and the pipeline's
checker rejects. Endpoint-only comparison is thereby refuted as a
certification method. -/
theorem control (d : Dim) :
    naive bad 0 2 d = true ∧ bad d 1 < bad d 0 ∧
    ¬ Chain step bad d 0 2 ∧ check step bad claim = false :=
  ⟨naiveaccepts d, interior d, nochain d, rejected⟩

end Control
