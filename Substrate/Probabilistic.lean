import Substrate.Basic
import Substrate.Discrete
import Substrate.Prefix
import Substrate.Certifier
import Substrate.Cardinality
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Distributions.Geometric
import Mathlib.MeasureTheory.Measure.Typeclasses.NoAtoms
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Substrate.Probabilistic

**Closed in Lean (deterministic):** no internal test has positive acceptance on `D` alone or on
`Cstrict` alone (`acceptance_on_D_iff_Cstrict`).

**Closed in Lean (measure infrastructure):** acceptance region measurability, infinite product
measure on full Baire space `ℕ → ℕ` via `Measure.infinitePi`, and the substrate-class mass
classification (`D_null_geometric`, `Cstrict_full_mass_geometric`).

**NOT closed (ε-tolerant / measure-theoretic generalization):** the `ProbabilisticTest` /
`HasProbAcceptAbove` block below is a *prefix-determined witness restatement* of the deterministic
result — not a genuine randomized observer or class-conditional rate bound. See module comments
on `HasProbAcceptAbove` and the open-problem note at the end.

Status: `EPIC_004_SUD_EXTENSIONS` (SPEC_000_SUD §7 bullet 4 — **partial**: deterministic closed;
ε-tolerant generalization still open).
-/

namespace Substrate

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology

/-! ### Deterministic acceptance (prefix-lifting of Theorem 2) -/

/-- An internal test has *positive acceptance* on class `S` if it returns `true` on some
transcript in `S`. -/
def HasPositiveAcceptance (T : InternalTest) (S : Set (ℕ → ℕ)) : Prop :=
  ∃ f ∈ S, T.run f

/-- **No exclusive class advantage.**  An internal test accepts some discrete transcript if and
only if it accepts some strict-continuum transcript.  This is the prefix-lifting of Theorem 2 to
tests — the substantive closed result for §7 bullet 4. -/
theorem acceptance_on_D_iff_Cstrict (T : InternalTest) :
    HasPositiveAcceptance T D ↔ HasPositiveAcceptance T Cstrict := by
  constructor
  · rintro ⟨d, hdD, hrun⟩
    obtain ⟨_d', _hdD', _hpd, c, hcC, hpc⟩ := prefix_indistinguishable (Prefix d T.budget)
    have hpc' : Prefix c T.budget = Prefix d T.budget := by
      rw [Prefix_length d T.budget] at hpc
      exact hpc
    refine ⟨c, hcC, ?_⟩
    simpa [InternalTest.run, hpc'] using hrun
  · rintro ⟨c, hcC, hrun⟩
    obtain ⟨d, hdD, hpd, _c', _hcC', _hpc⟩ := prefix_indistinguishable (Prefix c T.budget)
    have hpd' : Prefix d T.budget = Prefix c T.budget := by
      rw [Prefix_length c T.budget] at hpd
      exact hpd
    refine ⟨d, hdD, ?_⟩
    simpa [InternalTest.run, hpd'] using hrun

/-- Corollary: no internal test has positive acceptance on one substrate class only. -/
theorem not_exclusive_acceptance (T : InternalTest) :
    ¬ (HasPositiveAcceptance T D ∧ ¬ HasPositiveAcceptance T Cstrict) ∧
    ¬ (HasPositiveAcceptance T Cstrict ∧ ¬ HasPositiveAcceptance T D) := by
  constructor <;>
    intro h
  · exact h.2 ((acceptance_on_D_iff_Cstrict T).mp h.1)
  · exact h.2 ((acceptance_on_D_iff_Cstrict T).symm.mp h.1)

/-! ### Substrate classes in this model -/

/-- Every transcript is continuum-realizable (`ContinuumWorld` is classical on `ℝ`). -/
theorem C_eq_univ : (C : Set (ℕ → ℕ)) = Set.univ := by
  ext f
  exact ⟨fun _ => Set.mem_univ f, fun _ => mem_C f⟩

/-- Strict continuum = all transcripts except computable ones; since `D` = computable, this is
`univ \\ D`. -/
theorem Cstrict_eq_univ_diff_D : Cstrict = (Set.univ : Set (ℕ → ℕ)) \ D := by
  ext f
  simp [Cstrict, C_eq_univ, transcript_characterisation, Set.mem_diff, Set.mem_setOf_eq]

/-! ### Baire-space cylinders and acceptance sets -/

/-- Transcripts agreeing with a finite prefix `p` on its length — a clopen cylinder in Baire space. -/
def prefixCylinder (p : List ℕ) : Set (ℕ → ℕ) :=
  {f | Prefix f p.length = p}

/-- Prefix list for a finite coordinate assignment. -/
def prefixList (b : ℕ) (x : Fin b → ℕ) : List ℕ :=
  (List.finRange b).map x

lemma prefixList_length (b : ℕ) (x : Fin b → ℕ) : (prefixList b x).length = b := by
  simp [prefixList]

lemma prefix_eq_prefixList (b : ℕ) (f : ℕ → ℕ) :
    Prefix f b = prefixList b (fun i : Fin b => f i) := by
  apply List.ext_getElem <;> simp [Prefix, prefixList, List.getElem_map, List.getElem_finRange]

lemma prefixList_prefix (b : ℕ) (x : Fin b → ℕ) (f : ℕ → ℕ)
    (h : ∀ i : Fin b, f i = x i) : Prefix f b = prefixList b x := by
  apply List.ext_getElem
  · simp [Prefix, prefixList]
  · intro i hi hi'
    have hi'fin : i < b := by simpa [Prefix, prefixList] using hi'
    simp [Prefix, prefixList, List.getElem_map, List.getElem_finRange, h ⟨i, hi'fin⟩]

lemma prefixCylinder_eq_range_pi (p : List ℕ) :
    prefixCylinder p = Set.pi (Finset.range p.length) (fun i : ℕ => {p.getD i 0}) := by
  ext f
  constructor
  · intro h i hi
    have := congrArg (fun l => l.getD i 0) h
    simp [Prefix, List.getElem_range, Finset.mem_range.mp hi] at this ⊢
    exact this
  · intro h
    apply List.ext_getElem
    · simp [Prefix]
    · intro i hi hi'
      have hi'len : i < p.length := by simpa [Prefix] using hi'
      have hmem := h i (Finset.mem_range.mpr hi'len)
      simp [Prefix, List.getElem_map, List.getElem_range, Set.mem_singleton_iff,
        List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi'len] at hmem ⊢
      exact hmem

lemma prefixCylinder_measurable (p : List ℕ) : MeasurableSet (prefixCylinder p) := by
  rw [prefixCylinder_eq_range_pi]
  refine .pi (Finset.range p.length).countable_toSet fun i _ => .singleton _

/-- The deterministic acceptance region `{f | T.run f}`. -/
def acceptanceSet (T : InternalTest) : Set (ℕ → ℕ) :=
  {f | T.run f}

lemma acceptanceSet_eq_iUnion (T : InternalTest) :
    acceptanceSet T =
      ⋃ x : Fin T.budget → ℕ,
        if T.verdict (prefixList T.budget x) then prefixCylinder (prefixList T.budget x) else ∅ := by
  ext f
  simp only [acceptanceSet, InternalTest.run, Set.mem_iUnion, Set.mem_setOf_eq, prefixCylinder]
  constructor
  · intro hrun
    refine ⟨fun i : Fin T.budget => f i, ?_⟩
    have hprefix : Prefix f T.budget = prefixList T.budget (fun i : Fin T.budget => f i) :=
      prefix_eq_prefixList T.budget f
    by_cases hver : T.verdict (prefixList T.budget (fun i : Fin T.budget => f i))
    · simp [hver, prefixList_length, hprefix]
    · exfalso
      exact hver (hprefix ▸ hrun)
  · rintro ⟨x, hx⟩
    by_cases hver : T.verdict (prefixList T.budget x)
    · simp [hver] at hx
      have hcoord : ∀ i : Fin T.budget, f i = x i := by
        intro i
        have := congrArg (fun l => l.getD i.1 0) hx
        simp [Prefix, prefixList, List.getElem_map, List.getElem_finRange,
          List.getD_eq_getElem?_getD] at this ⊢
        exact this
      have hprefix := prefixList_prefix T.budget x f hcoord
      simpa [InternalTest.run, hprefix] using hver
    · simp [hver] at hx

theorem acceptanceSet_measurable (T : InternalTest) : MeasurableSet (acceptanceSet T) := by
  rw [acceptanceSet_eq_iUnion T]
  refine .iUnion fun x => ?_
  by_cases h : T.verdict (prefixList T.budget x)
  · simpa [h] using prefixCylinder_measurable (prefixList T.budget x)
  · simp [h]

/-! ### Canonical infinite product measure on Baire space -/

/-- Infinite i.i.d. product probability measure on `ℕ → ℕ` from a per-coordinate measure on `ℕ`. -/
noncomputable def baireProductMeasure (ν : Measure ℕ) [IsProbabilityMeasure ν] : Measure (ℕ → ℕ) :=
  Measure.infinitePi (fun _ : ℕ => ν)

instance baireProductMeasure_isProbability (ν : Measure ℕ) [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (baireProductMeasure ν) := by
  unfold baireProductMeasure
  infer_instance

/-- Per-coordinate geometric measure, packaged for `infinitePi` instance inference. -/
noncomputable def geomCoordMeasure (p : ℝ) (hp_pos : 0 < p) (hp_le : p ≤ 1) : ℕ → Measure ℕ :=
  fun _ => geometricMeasure hp_pos hp_le

instance geomCoordMeasure_isProbability (p : ℝ) (hp_pos : 0 < p) (hp_le : p ≤ 1) (i : ℕ) :
    IsProbabilityMeasure (geomCoordMeasure p hp_pos hp_le i) :=
  isProbabilityMeasure_geometricMeasure hp_pos hp_le

/-- The canonical geometric i.i.d. product on Baire space (full alphabet `ℕ`, every cylinder charged). -/
noncomputable def baireGeometricProduct (p : ℝ) (hp_pos : 0 < p) (hp_le : p ≤ 1) : Measure (ℕ → ℕ) :=
  Measure.infinitePi (geomCoordMeasure p hp_pos hp_le)

instance baireGeometricProduct_isProbability (p : ℝ) (hp_pos : 0 < p) (hp_le : p ≤ 1) :
    IsProbabilityMeasure (baireGeometricProduct p hp_pos hp_le) := by
  unfold baireGeometricProduct
  haveI : ∀ _ : ℕ, IsProbabilityMeasure (geometricMeasure hp_pos hp_le) := fun _ =>
    isProbabilityMeasure_geometricMeasure hp_pos hp_le
  infer_instance

theorem prefixCylinder_mass_pos {ν : Measure ℕ} [IsProbabilityMeasure ν]
    (_hpos : ∀ n : ℕ, ν {n} > 0) (p : List ℕ) :
    (baireProductMeasure ν) (prefixCylinder p) =
      ∏ i ∈ Finset.range p.length, ν {p.getD i 0} := by
  rw [prefixCylinder_eq_range_pi, baireProductMeasure, Measure.infinitePi_pi]
  all_goals intro i hi; exact .singleton _

theorem prefixCylinder_mass_pos_of_pos {ν : Measure ℕ} [IsProbabilityMeasure ν]
    (hpos : ∀ n : ℕ, ν {n} > 0) (p : List ℕ) :
    (baireProductMeasure ν) (prefixCylinder p) > 0 := by
  rw [prefixCylinder_mass_pos hpos]
  have hpos' : ∀ i ∈ Finset.range p.length, 0 < ν {p.getD i 0} := fun i _ => hpos (p.getD i 0)
  have hprod : ∏ i ∈ Finset.range p.length, ν {p.getD i 0} ≠ 0 := by
    intro h0
    obtain ⟨i, hi, hn⟩ := Finset.prod_eq_zero_iff.mp h0
    exact (hpos' i hi).ne' hn
  exact lt_of_le_of_ne (by simp) hprod.symm

theorem geometric_singleton_pos {p : ℝ} (hp_pos : 0 < p) (hp_lt : p < 1) (n : ℕ) :
    geometricMeasure hp_pos (hp_lt.le) {n} > 0 := by
  have hmeas : MeasurableSet ({n} : Set ℕ) := .singleton n
  rw [geometricMeasure, PMF.toMeasure_apply_singleton (geometricPMF hp_pos hp_lt.le) n hmeas,
    geometricPMF]
  exact ENNReal.ofReal_pos.mpr (geometricPMFReal_pos (n := n) hp_pos hp_lt)

private lemma one_sub_pow_le_one {p : ℝ} (hp_pos : 0 < p) (hp_le : p ≤ 1) (n : ℕ) :
    (1 - p) ^ n ≤ 1 := by
  induction n with
  | zero => simp
  | succ k ih =>
    calc
      (1 - p) ^ (k + 1) = (1 - p) ^ k * (1 - p) := pow_succ _ _
      _ ≤ 1 * (1 - p) := mul_le_mul_of_nonneg_right ih (sub_nonneg.mpr hp_le)
      _ = 1 - p := one_mul _
      _ ≤ 1 := sub_le_self 1 hp_pos.le

private theorem geometricMeasure_singleton_le_ofReal {p : ℝ} (hp_pos : 0 < p) (hp_le : p ≤ 1)
    (n : ℕ) : geometricMeasure hp_pos hp_le {n} ≤ ENNReal.ofReal p := by
  have hmeas : MeasurableSet ({n} : Set ℕ) := .singleton n
  rw [geometricMeasure, PMF.toMeasure_apply_singleton (geometricPMF hp_pos hp_le) n hmeas]
  show ENNReal.ofReal (geometricPMFReal p n) ≤ ENNReal.ofReal p
  rw [ENNReal.ofReal_le_ofReal_iff hp_pos.le]
  simp only [geometricPMFReal]
  rw [mul_comm]
  exact mul_le_of_le_one_right hp_pos.le (one_sub_pow_le_one hp_pos hp_le n)

private theorem geometricMeasure_singleton_le_one {p : ℝ} (hp_pos : 0 < p) (hp_le : p ≤ 1)
    (n : ℕ) : geometricMeasure hp_pos hp_le {n} ≤ 1 := by
  haveI := isProbabilityMeasure_geometricMeasure hp_pos hp_le
  exact measure_mono (Set.subset_univ _) |>.trans_eq measure_univ

/-- Under the geometric Baire product, every single transcript has measure zero. -/
theorem baireGeometricProduct_singleton_null {p : ℝ} (hp_pos : 0 < p) (hp_lt : p < 1)
    (f : ℕ → ℕ) : baireGeometricProduct p hp_pos hp_lt.le {f} = 0 := by
  haveI : ∀ _ : ℕ, MeasurableSingletonClass ℕ := fun _ => inferInstance
  let ν := geometricMeasure hp_pos hp_lt.le
  rw [baireGeometricProduct, Measure.infinitePi_singleton]
  have hle : ∀ i, (geomCoordMeasure p hp_pos hp_lt.le i) {f i} ≤ 1 :=
    fun i => geometricMeasure_singleton_le_one hp_pos hp_lt.le (f i)
  rw [ENNReal.tprod_eq_iInf_prod hle]
  have hbound : ∀ n, ∏ i ∈ Finset.range n, (geomCoordMeasure p hp_pos hp_lt.le i) {f i} ≤
      ENNReal.ofReal p ^ n := by
    intro n
    have hcoord : ∀ i ∈ Finset.range n, ν {f i} ≤ ENNReal.ofReal p :=
      fun i _ => geometricMeasure_singleton_le_ofReal hp_pos hp_lt.le (f i)
    calc
      ∏ i ∈ Finset.range n, (geomCoordMeasure p hp_pos hp_lt.le i) {f i}
          = ∏ i ∈ Finset.range n, ν {f i} := by simp [geomCoordMeasure, ν]
      _ ≤ ∏ _i ∈ Finset.range n, ENNReal.ofReal p :=
        Finset.prod_le_prod' fun i hi => hcoord i hi
      _ = ENNReal.ofReal p ^ n := by simp
  have hp_one : ENNReal.ofReal p < 1 := by
    rw [← ENNReal.ofReal_one]
    exact (ENNReal.ofReal_lt_ofReal_iff' (p := p) (q := 1)).2 ⟨hp_lt, zero_lt_one⟩
  have htend : Tendsto (fun n => ∏ i ∈ Finset.range n, (geomCoordMeasure p hp_pos hp_lt.le i) {f i})
      atTop (𝓝 0) :=
    tendsto_nhds_bot_mono' (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hp_one) hbound
  have hHasProd := ENNReal.hasProd_iInf_prod hle
  have h0 : HasProd (fun i => (geomCoordMeasure p hp_pos hp_lt.le i) {f i}) 0 :=
    (Multipliable.hasProd_iff_tendsto_nat (ENNReal.multipliable_of_le_one hle)).2 htend
  exact hHasProd.unique h0

instance baireGeometricProduct.noAtoms {p : ℝ} (hp_pos : 0 < p) (hp_lt : p < 1) :
    NoAtoms (baireGeometricProduct p hp_pos hp_lt.le) :=
  ⟨baireGeometricProduct_singleton_null hp_pos hp_lt⟩

theorem baireGeometric_prefixCylinder_mass_pos {p : ℝ} (hp_pos : 0 < p) (hp_lt : p < 1)
    (pref : List ℕ) :
    (baireGeometricProduct p hp_pos hp_lt.le) (prefixCylinder pref) > 0 := by
  unfold baireGeometricProduct
  haveI : ∀ _ : ℕ, IsProbabilityMeasure (geometricMeasure hp_pos hp_lt.le) := fun _ =>
    isProbabilityMeasure_geometricMeasure hp_pos hp_lt.le
  haveI : IsProbabilityMeasure (geometricMeasure hp_pos hp_lt.le) :=
    isProbabilityMeasure_geometricMeasure hp_pos hp_lt.le
  exact prefixCylinder_mass_pos_of_pos (ν := geometricMeasure hp_pos hp_lt.le)
    (hpos := geometric_singleton_pos hp_pos hp_lt) pref

/-! ### Substrate-class mass under the geometric Baire product -/

theorem D_measurable : MeasurableSet D :=
  D_countable.measurableSet

theorem Cstrict_measurable : MeasurableSet Cstrict := by
  rw [Cstrict_eq_univ_diff_D]
  exact MeasurableSet.diff .univ D_measurable

/-- **`D` has measure zero** under the geometric i.i.d. product (countable + no atoms). -/
theorem D_null_geometric {p : ℝ} (hp_pos : 0 < p) (hp_lt : p < 1) :
    baireGeometricProduct p hp_pos hp_lt.le D = 0 := by
  haveI := baireGeometricProduct.noAtoms hp_pos hp_lt
  exact D_countable.measure_zero _

/-- **`Cstrict` has full measure** (not measure zero): it is `univ \\ D` and `D` is null. -/
theorem Cstrict_full_mass_geometric {p : ℝ} (hp_pos : 0 < p) (hp_lt : p < 1) :
    baireGeometricProduct p hp_pos hp_lt.le Cstrict = 1 := by
  rw [Cstrict_eq_univ_diff_D, measure_diff_null (D_null_geometric hp_pos hp_lt), measure_univ]

/-! ### Global acceptance mass (not class-conditional) -/

/-- Total acceptance mass `μ(acceptanceSet T)` on all of Baire space — **not** a class-conditional
rate `μ(accept | D)` or `μ(accept | Cstrict)`. -/
noncomputable def acceptanceMass (T : InternalTest) (μ : Measure (ℕ → ℕ)) : ENNReal :=
  μ (acceptanceSet T)

theorem has_positive_acceptance_of_mass_pos {T : InternalTest} {μ : Measure (ℕ → ℕ)}
    (hμ : μ (acceptanceSet T) > 0) :
    ∃ f, T.run f := by
  obtain ⟨f, hf⟩ := nonempty_of_measure_ne_zero hμ.ne'
  exact ⟨f, by simpa [acceptanceSet] using hf⟩

theorem has_positive_acceptance_D_of_mass_pos {T : InternalTest} {μ : Measure (ℕ → ℕ)}
    (hμ : μ (acceptanceSet T) > 0) :
    HasPositiveAcceptance T D := by
  obtain ⟨f, hrun⟩ := has_positive_acceptance_of_mass_pos hμ
  obtain ⟨d, hdD, hpd, _, _, _⟩ := prefix_indistinguishable (Prefix f T.budget)
  have hpd' : Prefix d T.budget = Prefix f T.budget := by
    rw [Prefix_length f T.budget] at hpd
    exact hpd
  refine ⟨d, hdD, ?_⟩
  simpa [InternalTest.run, hpd'] using hrun

theorem has_positive_acceptance_Cstrict_of_mass_pos {T : InternalTest} {μ : Measure (ℕ → ℕ)}
    (hμ : μ (acceptanceSet T) > 0) :
    HasPositiveAcceptance T Cstrict := by
  obtain ⟨f, hrun⟩ := has_positive_acceptance_of_mass_pos hμ
  obtain ⟨_d, _hdD, _, c, hcC, hpc⟩ := prefix_indistinguishable (Prefix f T.budget)
  have hpc' : Prefix c T.budget = Prefix f T.budget := by
    rw [Prefix_length f T.budget] at hpc
    exact hpc
  refine ⟨c, hcC, ?_⟩
  simpa [InternalTest.run, hpc'] using hrun

theorem acceptanceMass_pos_of_verdict {T : InternalTest} {ν : Measure ℕ} [IsProbabilityMeasure ν]
    (hpos : ∀ n : ℕ, ν {n} > 0) {p : List ℕ} (hp : p.length = T.budget) (hver : T.verdict p) :
    acceptanceMass T (baireProductMeasure ν) > 0 := by
  unfold acceptanceMass acceptanceSet
  have hsubset : prefixCylinder p ⊆ acceptanceSet T := by
    intro f hf
    simp only [acceptanceSet, prefixCylinder, Set.mem_setOf_eq] at hf ⊢
    rw [InternalTest.run, ← hp, hf, hver]
  have hμpos : (baireProductMeasure ν) (prefixCylinder p) > 0 :=
    prefixCylinder_mass_pos_of_pos hpos p
  exact lt_of_lt_of_le hμpos (measure_mono hsubset)

/-- Positive global acceptance mass implies positive deterministic acceptance on both classes
(via prefix indistinguishability — same mechanism as `acceptance_on_D_iff_Cstrict`). -/
theorem acceptance_mass_meets_both_classes {T : InternalTest} {μ : Measure (ℕ → ℕ)}
    {ε : ENNReal} (hε : 0 < ε) (hμ : acceptanceMass T μ > ε) :
    HasPositiveAcceptance T D ∧ HasPositiveAcceptance T Cstrict := by
  have hμ' : μ (acceptanceSet T) > 0 := lt_trans hε hμ
  exact ⟨has_positive_acceptance_D_of_mass_pos hμ', has_positive_acceptance_Cstrict_of_mass_pos hμ'⟩

/-! ### Prefix-determined “probabilistic” tests (NOT a genuine ε-tolerant strengthening) -/

/-- A prefix-determined confidence function — **not** a randomized test. There is no coin flip
or internal randomness; `acceptProb` is a deterministic `ENNReal`-valued function of the budget
prefix, exactly parallel to `InternalTest.verdict : List ℕ → Bool`. -/
structure ProbabilisticTest where
  budget : ℕ
  acceptProb : List ℕ → ENNReal
  prob_le_one : ∀ p, acceptProb p ≤ 1

namespace ProbabilisticTest

def probAt (T : ProbabilisticTest) (f : ℕ → ℕ) : ENNReal :=
  T.acceptProb (Prefix f T.budget)

end ProbabilisticTest

/-- Witness-existence predicate: some transcript in `S` has prefix-confidence above `1 - ε`.
Because `probAt` depends only on the prefix, Theorem 1 transports witnesses with **identical**
(not merely ε-close) confidence values; the parameter `ε` is therefore **decorative** in the
equivalence below (the proof never uses `ε < 1` or `ε > 0`). This is *not* the spec's intended
class-conditional accept-rate bound under a sampling measure. -/
def HasProbAcceptAbove (T : ProbabilisticTest) (S : Set (ℕ → ℕ)) (ε : ENNReal) : Prop :=
  ∃ f ∈ S, (1 : ENNReal) - ε < T.probAt f

/-- **Notational restatement of `acceptance_on_D_iff_Cstrict`.**  The proof transports the *same*
prefix and hence the *same* `probAt` value; `ε` does no work. Kept for API stability only. -/
theorem prob_accept_above_on_D_iff_Cstrict (T : ProbabilisticTest) (ε : ENNReal) :
    HasProbAcceptAbove T D ε ↔ HasProbAcceptAbove T Cstrict ε := by
  constructor
  · rintro ⟨d, hdD, hprob⟩
    obtain ⟨_d', _hdD', _hpd, c, hcC, hpc⟩ := prefix_indistinguishable (Prefix d T.budget)
    have hpc' : Prefix c T.budget = Prefix d T.budget := by
      rw [Prefix_length d T.budget] at hpc
      exact hpc
    refine ⟨c, hcC, ?_⟩
    simpa [ProbabilisticTest.probAt, hpc'] using hprob
  · rintro ⟨c, hcC, hprob⟩
    obtain ⟨d, hdD, hpd, _c', _hcC', _hpc⟩ := prefix_indistinguishable (Prefix c T.budget)
    have hpd' : Prefix d T.budget = Prefix c T.budget := by
      rw [Prefix_length c T.budget] at hpd
      exact hpd
    refine ⟨d, hdD, ?_⟩
    simpa [ProbabilisticTest.probAt, hpd'] using hprob

theorem not_exclusive_prob_advantage (T : ProbabilisticTest) (ε : ENNReal) :
    ¬ (HasProbAcceptAbove T D ε ∧ ¬ HasProbAcceptAbove T Cstrict ε) ∧
    ¬ (HasProbAcceptAbove T Cstrict ε ∧ ¬ HasProbAcceptAbove T D ε) := by
  constructor <;>
    intro h
  · exact h.2 ((prob_accept_above_on_D_iff_Cstrict T ε).mp h.1)
  · exact h.2 ((prob_accept_above_on_D_iff_Cstrict T ε).symm.mp h.1)

def InternalTest.toProbabilistic (T : InternalTest) : ProbabilisticTest where
  budget := T.budget
  acceptProb := fun p => if T.verdict p then (1 : ENNReal) else 0
  prob_le_one := fun p => by split_ifs <;> simp

/-! ### Open problem (§7 bullet 4 — ε-tolerant, not yet formalized)

A **genuine** probabilistic / measure-theoretic generalization would require at least:

1. **Randomized tests** — acceptance is a Bernoulli (or other) draw with internal randomness, not
   a deterministic function of the prefix alone; and/or
2. **Class-charged sampling measures** — e.g. a mixture `ν = (1/2)•μ_D + (1/2)•μ_C` with `μ_D`
   a discrete probability on countable `D` and `μ_C` full mass on `Cstrict` (see `Cstrict_full_mass_geometric`);
   then define class-conditional accept rates `P(accept | f ∼ μ_D)` vs `P(accept | f ∼ μ_C)` and
   prove a non-trivial `|rate_D - rate_C| ≤ ε` obstruction.

Prefix indistinguishability does **not** imply such a rate bound: prefix-determined confidence
can differ in aggregate across classes because the *distribution of prefixes* under `μ_D` vs `μ_C`
can differ arbitrarily. This is why the witness-based `HasProbAcceptAbove` formulation above is
insufficient and was mis-billed as “closed.” -/

end Substrate
