import Substrate.Basic
import Substrate.NotFinDet
import Substrate.Certifier
import Substrate.LawBarrier

/-!
# Substrate.Outsourced

Lean-checkable half of **Theorem 5:** substrate is not internally decidable.

An internal observer decides a transcript property only via a finite-resource prefix test.
Such properties are at most finitely determined; Theorem 2 then forbids separating `D` from
`Cstrict`. Theorem 4 forbids computably deciding law-match for computable transcripts.

The MDL-uniqueness half of Theorem 5 cites P34/P84 (argument, not re-proved here).

Status: A_Lean (`EPIC_002_SUD_PART_II`).
-/

namespace Substrate

/-- A transcript property is *internally decidable* when some finite-resource internal test
decides it: positive verdict iff the property holds. -/
def InternallyDecidable (P : (ℕ → ℕ) → Prop) : Prop :=
  ∃ T : InternalTest, ∀ f, T.run f = true ↔ P f

/-- Every internally decidable property is finitely determined: the test only inspects
`Prefix f T.budget`. -/
theorem internally_decidable_implies_finitely_determined {P : (ℕ → ℕ) → Prop}
    (h : InternallyDecidable P) : FinitelyDetermined P := by
  obtain ⟨T, hT⟩ := h
  refine ⟨T.budget, fun f g heq => ⟨?_, ?_⟩⟩
  · intro hPf
    have htrue : T.verdict (Prefix f T.budget) = true := by
      simpa [InternalTest.run] using (hT f).2 hPf
    have hrun : T.verdict (Prefix g T.budget) = true := by rw [heq.symm]; exact htrue
    exact (hT g).1 (by simpa [InternalTest.run] using hrun)
  · intro hPg
    have htrue : T.verdict (Prefix g T.budget) = true := by
      simpa [InternalTest.run] using (hT g).2 hPg
    have hrun : T.verdict (Prefix f T.budget) = true := by rw [heq]; exact htrue
    exact (hT f).1 (by simpa [InternalTest.run] using hrun)

/-- Complement of a finitely determined property is finitely determined. -/
theorem finitely_determined_compl {P : (ℕ → ℕ) → Prop} (h : FinitelyDetermined P) :
    FinitelyDetermined (fun f => ¬ P f) := by
  obtain ⟨n, hFD⟩ := h
  exact ⟨n, fun f g heq => (hFD f g heq).not⟩

/-- **Theorem 5 (Lean half — outsourcing).**  No internally decidable transcript property
separates discrete (`D`) from strict-continuum (`Cstrict`) witnesses. Substrate class is
therefore not internally decidable. -/
theorem substrate_not_internally_decidable :
    ¬ ∃ P : (ℕ → ℕ) → Prop,
        InternallyDecidable P ∧ (∀ f ∈ D, P f) ∧ (∀ f ∈ Cstrict, ¬ P f) := by
  intro ⟨P, hID, hD, hC⟩
  exact substrate_not_finitely_determined ⟨P, internally_decidable_implies_finitely_determined hID, hD, hC⟩

/-- Symmetric separation: no internal test decides strict-continuum over discrete. -/
theorem substrate_not_internally_decidable' :
    ¬ ∃ P : (ℕ → ℕ) → Prop,
        InternallyDecidable P ∧ (∀ f ∈ D, ¬ P f) ∧ (∀ f ∈ Cstrict, P f) := by
  intro ⟨P, hID, hD, hC⟩
  exact substrate_not_finitely_determined
    ⟨fun f => ¬ P f,
     finitely_determined_compl (internally_decidable_implies_finitely_determined hID),
     hD, fun f hf => not_not.mpr (hC f hf)⟩

/-- Discrete membership is not internally decidable. -/
theorem discrete_not_internally_decidable : ¬ InternallyDecidable (fun f => f ∈ D) := by
  intro h
  exact substrate_not_internally_decidable
    ⟨fun f => f ∈ D, h, fun f hf => hf, fun f hf => Set.disjoint_right.mp D_disjoint_Cstrict hf⟩

/-- Strict-continuum membership is not internally decidable. -/
theorem strict_continuum_not_internally_decidable : ¬ InternallyDecidable (fun f => f ∈ Cstrict) := by
  intro h
  exact substrate_not_internally_decidable'
    ⟨fun f => f ∈ Cstrict, h, fun f hf => Set.disjoint_left.mp D_disjoint_Cstrict hf, fun f hf => hf⟩

end Substrate
