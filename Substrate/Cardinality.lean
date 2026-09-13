import Substrate.Basic
import Substrate.Discrete
import Substrate.Prefix
import Substrate.Certifier
import Substrate.Outsourced
import Mathlib.Computability.PartrecCode
import Mathlib.Analysis.Real.Cardinality
import Mathlib.SetTheory.Cardinal.Continuum

/-!
# Substrate.Cardinality

Cardinality facts and the **uncountable-observer strengthening** of Theorem 5.

`D` is countable (computable transcripts); `Cstrict` is not countable (Baire space minus
a countable set).  No family of internal tests — indexed by *any* type, including an
uncountable one — can jointly decide discrete membership from strict-continuum rejection.
The obstruction is prefix indistinguishability (Theorem 1), exactly as for a single test.

Status: `EPIC_004_SUD_EXTENSIONS` (SPEC_000_SUD §7 bullet 5).
-/

namespace Substrate

open Nat.Partrec.Code

/-! ### Cardinality of Baire space -/

private theorem mk_nat_arrow_nat : Cardinal.mk (ℕ → ℕ) = Cardinal.continuum := by
  have hcard : Cardinal.mk (ℕ → ℕ) = Cardinal.mk ℝ := by
    rw [← Cardinal.power_def, Cardinal.mk_nat, Cardinal.aleph0_power_aleph0, ← Cardinal.mk_real]
  rw [hcard, Cardinal.mk_real]

/-! ### Countability of `D` -/

/-- The set of computable `ℕ → ℕ` functions is countable (Mathlib: encodable codes). -/
theorem computable_set_countable : Set.Countable {f : ℕ → ℕ | Computable f} := by
  haveI : Countable {f : ℕ → ℕ // Computable f} := inferInstance
  simpa using (inferInstance : Countable {f : ℕ → ℕ // Computable f})

/-- **`D` is countable** — discrete transcripts are exactly the computable ones (Lemma 2.1). -/
theorem D_countable : Set.Countable D := by
  rw [show D = {f | Computable f} from Set.ext (fun f => transcript_characterisation f)]
  exact computable_set_countable

/-! ### Non-countability of `Cstrict` -/

/-- Baire space is not countable (same cardinality as `ℝ`). -/
theorem baire_space_not_countable : ¬ (Set.univ : Set (ℕ → ℕ)).Countable := by
  intro h
  have hcount : Countable (ℕ → ℕ) := (Set.countable_univ_iff).1 h
  have hle : Cardinal.mk (ℕ → ℕ) ≤ Cardinal.aleph0 := (Cardinal.mk_le_aleph0_iff).2 hcount
  have hgt : Cardinal.aleph0 < Cardinal.mk (ℕ → ℕ) := by
    rw [mk_nat_arrow_nat]
    exact Cardinal.aleph0_lt_continuum
  exact lt_irrefl _ (hgt.trans_le hle)

/-- **`Cstrict` is not countable** — strict-continuum transcripts occupy almost all of Baire space. -/
theorem Cstrict_not_countable : ¬ Cstrict.Countable := by
  intro hCstrict
  have hD : Set.Countable D := D_countable
  have hunion : D ∪ Cstrict = (Set.univ : Set (ℕ → ℕ)) := by
    ext f
    constructor
    · intro hf; exact Set.mem_univ f
    · intro _
      by_cases hcomp : Computable f
      · exact Or.inl ((transcript_characterisation f).2 hcomp)
      · exact Or.inr ⟨mem_C f, hcomp⟩
  have hcount_univ : (Set.univ : Set (ℕ → ℕ)).Countable := by
    rw [← hunion]
    exact hD.union hCstrict
  exact baire_space_not_countable hcount_univ

/-! ### Joint decision over arbitrary index types -/

/-- A family of internal tests *jointly decides discrete membership* if every discrete transcript
is accepted by some test and no strict-continuum transcript is accepted by any test. -/
def JointlyDecidesDiscrete {I : Type*} (tests : I → InternalTest) : Prop :=
  (∀ f ∈ D, ∃ i, (tests i).run f) ∧ (∀ f ∈ Cstrict, ∀ i, ¬ (tests i).run f)

/-- A family of internally decidable predicates *jointly separates* `D` from `Cstrict` if every
discrete transcript satisfies some predicate and no strict-continuum transcript satisfies any. -/
def JointlySeparatesDiscrete {I : Type*} (P : I → (ℕ → ℕ) → Prop) : Prop :=
  (∀ i, InternallyDecidable (P i)) ∧
    ((∀ f ∈ D, ∃ i, P i f) ∧ (∀ f ∈ Cstrict, ∀ i, ¬ P i f))

theorem run_eq_of_prefix_eq {T : InternalTest} {f g : ℕ → ℕ}
    (h : Prefix f T.budget = Prefix g T.budget) : T.run f = T.run g := by
  simp [InternalTest.run, h]

/-- **Theorem 5 (cardinality / uncountable-observer strengthening).**
    No family of internal tests, indexed by an arbitrary (possibly uncountable) type, jointly
    decides discrete membership.  The obstruction is prefix indistinguishability (Theorem 1); an
    uncountable index type adds no power beyond a single test (see also `D_countable` /
    `Cstrict_not_countable`). -/
theorem no_joint_substrate_decision {I : Type*} (tests : I → InternalTest) :
    ¬ JointlyDecidesDiscrete tests := by
  intro ⟨hD, hC⟩
  set f0 : ℕ → ℕ := fun _ => 0 with hf0
  have hf0D : f0 ∈ D := (transcript_characterisation f0).2 (Computable.const 0)
  obtain ⟨i, hi⟩ := hD f0 hf0D
  set n := (tests i).budget with hn
  obtain ⟨d, _hdD, _hpd, c, hcC, hpc⟩ := prefix_indistinguishable (Prefix f0 n)
  have hlen : (Prefix f0 n).length = n := Prefix_length f0 n
  have hpc' : Prefix c n = Prefix f0 n := by simpa [hlen] using hpc
  have hf0_pref : Prefix f0 (tests i).budget = Prefix c (tests i).budget := by rw [← hn, hpc'.symm]
  have hrun_c : (tests i).run c = true :=
    run_eq_of_prefix_eq (T := tests i) (f := f0) (g := c) hf0_pref ▸ hi
  exact hC c hcC i hrun_c

/-- **Joint internal decidability strengthening.**  No family of internally decidable predicates,
    over any index type, separates `D` from `Cstrict`. -/
theorem no_joint_internally_decidable {I : Type*} (P : I → (ℕ → ℕ) → Prop) :
    ¬ JointlySeparatesDiscrete P := by
  intro ⟨hID, hD, hC⟩
  set f0 : ℕ → ℕ := fun _ => 0 with hf0
  have hf0D : f0 ∈ D := (transcript_characterisation f0).2 (Computable.const 0)
  obtain ⟨i, hi⟩ := hD f0 hf0D
  obtain ⟨T, hT⟩ := hID i
  set n := T.budget with hn
  obtain ⟨d, _hdD, _hpd, c, hcC, hpc⟩ := prefix_indistinguishable (Prefix f0 n)
  have hlen : (Prefix f0 n).length = n := Prefix_length f0 n
  have hpc' : Prefix c n = Prefix f0 n := by simpa [hlen] using hpc
  have hf0_pref : Prefix f0 T.budget = Prefix c T.budget := by rw [← hn, hpc'.symm]
  have hrun_d : T.run f0 = true := (hT f0).2 hi
  have hrun_c : T.run c = true :=
    run_eq_of_prefix_eq (T := T) (f := f0) (g := c) hf0_pref ▸ hrun_d
  exact hC c hcC i ((hT c).1 hrun_c)

/-- Corollary: an uncountable index set offers no extra power — joint decision is impossible
    regardless of indexing cardinality. -/
theorem uncountable_index_offers_no_power {I : Type*} [Uncountable I] (tests : I → InternalTest) :
    ¬ JointlyDecidesDiscrete tests :=
  no_joint_substrate_decision tests

end Substrate
