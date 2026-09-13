import Substrate.Basic
import Substrate.Prefix

/-!
# Substrate.NotFinDet

**Theorem 2:** no finitely determined property separates dense, disjoint transcript classes.

The abstract dense-pair lemma is pure prefix topology; the halting witness enters only at the
`D` / `Cstrict` instantiation via `prefix_indistinguishable`.

Status: A_Lean (`EPIC_001_SUD_PART_I`, extended `EPIC_005_SUD_PAPER_REVISION_2`).
-/

namespace Substrate

/-- **Abstract Theorem 2.**  If `A` and `B` are disjoint and each extends every finite prefix,
no finitely determined property holds on all of `A` and fails on all of `B`. -/
theorem not_finitely_determined_of_dense_pair
    {A B : Set (ℕ → ℕ)} (hA : ∀ p : List ℕ, ∃ a ∈ A, Prefix a p.length = p)
    (hB : ∀ p : List ℕ, ∃ b ∈ B, Prefix b p.length = p) (_hAB : Disjoint A B) :
    ¬ ∃ P : (ℕ → ℕ) → Prop,
        FinitelyDetermined P ∧ (∀ f ∈ A, P f) ∧ (∀ f ∈ B, ¬ P f) := by
  rintro ⟨P, ⟨n, hFD⟩, hPA, hPB⟩
  obtain ⟨a, haA, hpa⟩ := hA (List.replicate n 0)
  obtain ⟨b, hbB, hpb⟩ := hB (List.replicate n 0)
  have hlen : (List.replicate n 0).length = n := List.length_replicate
  have hpa' : Prefix a n = List.replicate n 0 := by rw [hlen] at hpa; exact hpa
  have hpb' : Prefix b n = List.replicate n 0 := by rw [hlen] at hpb; exact hpb
  have hagree : Prefix a n = Prefix b n := hpa'.trans hpb'.symm
  have hPa : P a := hPA a haA
  have hPb : ¬ P b := hPB b hbB
  exact hPb ((hFD a b hagree).mp hPa)

/-- **Theorem 2 (Substrate is not finitely determined).**  No finitely determined
property of transcripts holds on all of `D` and fails on all of `Cstrict`. -/
theorem substrate_not_finitely_determined :
    ¬ ∃ P : (ℕ → ℕ) → Prop,
        FinitelyDetermined P ∧ (∀ f ∈ D, P f) ∧ (∀ f ∈ Cstrict, ¬ P f) := by
  refine not_finitely_determined_of_dense_pair ?_ ?_ D_disjoint_Cstrict
  · intro p
    obtain ⟨d, hdD, hpd, _, _, _⟩ := prefix_indistinguishable p
    exact ⟨d, hdD, hpd⟩
  · intro p
    obtain ⟨_, _, _, c, hcC, hpc⟩ := prefix_indistinguishable p
    exact ⟨c, hcC, hpc⟩

end Substrate
