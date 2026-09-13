import Substrate.Basic
import Mathlib.Computability.Halting

/-!
# Substrate.Noncomputable

Existence of a non-computable `ℕ → ℕ` function.  Constructed directly from the
diagonal halting predicate (`ComputablePred.halting_problem`) rather than a bare
cardinality argument, since the explicit witness is reused by `Prefix.lean` (Theorem 1).

Status: A_Lean (`EPIC_001_SUD_PART_I`).
-/

namespace Substrate

open Nat.Partrec (Code)
open Nat.Partrec.Code (eval)

/-- The diagonal halting predicate on codes: whether code `c` halts on input `0`. -/
def HaltsOnZero (c : Code) : Prop := (eval c 0).Dom

open scoped Classical in
/-- A classical indicator of `HaltsOnZero`, valued in `ℕ` (`1` if it halts, `0` otherwise). -/
noncomputable def haltingIndicatorCode (c : Code) : ℕ :=
  if HaltsOnZero c then 1 else 0

open scoped Classical in
theorem haltingIndicatorCode_eq_one_iff (c : Code) :
    haltingIndicatorCode c = 1 ↔ HaltsOnZero c := by
  unfold haltingIndicatorCode
  by_cases h : HaltsOnZero c <;> simp [h]

/-- The `ℕ → ℕ` witness: pull `haltingIndicatorCode` back along the canonical
`ℕ ≃ Code` denumeration. Marked `noncomputable` because it is defined via classical
(non-effective) case analysis on `(eval c 0).Dom` — that non-effectiveness is exactly
what the theorem below certifies. -/
noncomputable def haltingIndicator (n : ℕ) : ℕ :=
  haltingIndicatorCode (Denumerable.ofNat Code n)

/-- **`haltingIndicator` is not computable.**  If it were, `haltingIndicatorCode` would be
computable too (compose with the computable encoding `Code → ℕ`), hence `HaltsOnZero` would
be `ComputablePred`, contradicting `ComputablePred.halting_problem`. -/
theorem not_computable_haltingIndicator : ¬ Computable haltingIndicator := by
  intro hf
  have hcode : Computable haltingIndicatorCode := by
    have henc : Computable (Encodable.encode : Code → ℕ) := Computable.encode
    have hcomp : Computable (fun c => haltingIndicator (Encodable.encode c)) := hf.comp henc
    refine hcomp.of_eq (fun c => ?_)
    simp [haltingIndicator, Denumerable.ofNat_encode]
  have heq : Primrec₂ (fun (a b : ℕ) => decide (a = b)) := Primrec.eq.decide
  have heqc : Computable₂ (fun (a b : ℕ) => decide (a = b)) := heq.to_comp
  have hdec : Computable (fun c => decide (haltingIndicatorCode c = 1)) :=
    heqc.comp hcode (Computable.const 1)
  have hpred : ComputablePred (fun c => haltingIndicatorCode c = 1) :=
    Computable.computablePred hdec
  have hpred' : ComputablePred HaltsOnZero :=
    hpred.of_eq haltingIndicatorCode_eq_one_iff
  exact ComputablePred.halting_problem 0 hpred'

/-- Existence of a non-computable `ℕ → ℕ` function. -/
theorem exists_noncomputable_nat_fn : ∃ f : ℕ → ℕ, ¬ Computable f :=
  ⟨haltingIndicator, not_computable_haltingIndicator⟩

end Substrate
