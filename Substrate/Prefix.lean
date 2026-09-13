import Substrate.Basic
import Substrate.Discrete
import Substrate.Noncomputable
import Mathlib.Analysis.Real.Cardinality
import Mathlib.SetTheory.Cardinal.Continuum

/-!
# Substrate.Prefix

**Theorem 1:** prefix indistinguishability — for every finite prefix `p`, extensions
exist in both `D` and `Cstrict`.

**Corollary:** `D` and `Cstrict` are disjoint (both dense in Baire space; the elementary
prefix-extension statement above is the operative, stronger content — full formalisation
of density in the product topology on `ℕ → ℕ` is the optional `Topology.lean` per spec §8).

Status: A_Lean (`EPIC_001_SUD_PART_I`).
-/

namespace Substrate

/-! ### Every transcript is continuum-realizable: `C = univ` -/

/-- `ℕ → ℕ` has continuum cardinality, hence is equivalent to `Fin 1 → ℝ`. -/
theorem nonempty_equiv_finOne_real : Nonempty ((ℕ → ℕ) ≃ (Fin 1 → ℝ)) := by
  have hcard : Cardinal.mk (ℕ → ℕ) = Cardinal.mk ℝ := by
    rw [← Cardinal.power_def, Cardinal.mk_nat, Cardinal.aleph0_power_aleph0, ← Cardinal.mk_real]
  obtain ⟨e1⟩ := Cardinal.eq.mp hcard
  exact ⟨e1.trans (Equiv.piUnique (fun _ : Fin 1 => ℝ)).symm⟩

/-- Every `f : ℕ → ℕ` is realizable by a continuum world: state space `ℕ → ℕ` itself
(cardinality `𝔠`), `init := f`, `step` left-shifts the sequence, `read` reads the head. -/
theorem mem_C (f : ℕ → ℕ) : f ∈ C := by
  obtain ⟨e⟩ := nonempty_equiv_finOne_real
  refine ⟨⟨ℕ → ℕ, f, fun g i => g (i + 1), fun g => g 0⟩, ⟨1, ⟨e⟩⟩, ?_⟩
  have hshift : ∀ t : ℕ, (fun (g : ℕ → ℕ) (i : ℕ) => g (i + 1))^[t] f = fun i => f (i + t) := by
    intro t
    induction t with
    | zero => rfl
    | succ n ih =>
      rw [Function.iterate_succ_apply', ih]
      funext i
      show f (i + 1 + n) = f (i + (n + 1))
      congr 1
      omega
  funext t
  show (fun (g : ℕ → ℕ) (i : ℕ) => g (i + 1))^[t] f 0 = f t
  rw [hshift]
  show f (0 + t) = f t
  congr 1
  omega

/-! ### Prefix reconstruction helper -/

theorem prefix_getD_eq (p : List ℕ) :
    (List.range p.length).map (fun i => p.getD i 0) = p := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_range, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem h2, Option.getD_some]

/-! ### Theorem 1 -/

/-- **Theorem 1 (Prefix Indistinguishability).**  Every finite prefix extends to a
transcript in `D` (zeros beyond the prefix) and to a transcript in `Cstrict`
(the halting-problem witness beyond the prefix). -/
theorem prefix_indistinguishable (p : List ℕ) :
    ∃ d ∈ D, Prefix d p.length = p ∧ ∃ c ∈ Cstrict, Prefix c p.length = p := by
  set n := p.length with hn
  -- the discrete witness: zero-extension of `p`
  have hcompD : Computable (fun i => p.getD i (0 : ℕ)) :=
    ((Primrec.list_getD (0 : ℕ)).comp (Primrec.const p) Primrec.id).to_comp
  refine ⟨fun i => p.getD i 0, (transcript_characterisation _).mpr hcompD, ?_, ?_⟩
  · show (List.range n).map (fun i => p.getD i 0) = p
    exact prefix_getD_eq p
  · -- the strict-continuum witness: halting-indicator beyond `p`
    set c : ℕ → ℕ := fun i => if i < n then p.getD i 0 else haltingIndicator (i - n) with hc
    have hnc : ¬ Computable c := by
      intro hf
      apply not_computable_haltingIndicator
      have hadd : Computable (fun k : ℕ => k + n) :=
        (Primrec.nat_add.comp Primrec.id (Primrec.const n)).to_comp
      have : Computable (fun k => c (k + n)) := hf.comp hadd
      refine this.of_eq (fun k => ?_)
      have hge : ¬ k + n < n := by omega
      simp only [hc, hge, if_false]
      congr 1
      omega
    refine ⟨c, ⟨mem_C c, hnc⟩, ?_⟩
    show (List.range n).map c = p
    have hcongr : (List.range n).map c = (List.range n).map (fun i => p.getD i 0) := by
      apply List.map_congr_left
      intro i hi
      have hlt : i < n := List.mem_range.mp hi
      simp [hc, hlt]
    rw [hcongr]
    exact prefix_getD_eq p

/-! ### Disjointness corollary -/

/-- `D` and `Cstrict` are disjoint: every discrete transcript is computable
(Lemma 2.1), so it cannot lie in the non-computable strict-continuum class. -/
theorem D_disjoint_Cstrict : Disjoint D Cstrict := by
  rw [Set.disjoint_left]
  intro f hfD hfCstrict
  have hcomp : Computable f := (transcript_characterisation f).mp hfD
  exact hfCstrict.2 hcomp

end Substrate
