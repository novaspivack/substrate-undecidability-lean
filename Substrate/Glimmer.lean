import Substrate.Basic
import Substrate.Discrete
import Substrate.Prefix
import Substrate.NotFinDet
import Substrate.Noncomputable
import Mathlib.Computability.PartrecCode
import Mathlib.Algebra.Order.Archimedean.Basic

/-!
# Substrate.Glimmer

The **Glimmer** class: limit-computable transcripts that are computably random relative to a
computable Born measure. This is the finite-description adjudicative case (Δ⁰₂, not free bits).

Non-emptiness of `Glimmer μ f` for the uniform measure (Chaitin's Ω) is **cited**, not
constructed here — see Downey–Hirschfeldt on computable randomness.

Status: A_Lean (`EPIC_005_SUD_PAPER_REVISION_2`).
-/

set_option maxHeartbeats 800000

namespace Substrate

/-! ### Limit computability -/

/-- Limit computable: `f = lim_s g t s` for some computable approximant `g`. -/
def LimitComputable (f : ℕ → ℕ) : Prop :=
  ∃ g : ℕ → ℕ → ℕ, Computable (fun p : ℕ × ℕ => g p.1 p.2) ∧
    ∀ t, ∃ s₀, ∀ s ≥ s₀, g t s = f t

theorem computable_limitComputable {f : ℕ → ℕ} (hf : Computable f) : LimitComputable f := by
  refine ⟨fun t _ => f t, ?_, ?_⟩
  · exact hf.comp Computable.fst
  · intro t; refine ⟨0, fun s _ => rfl⟩

theorem limitComputable_prefix_extension {f : ℕ → ℕ} (hf : LimitComputable f) (p : List ℕ) :
    ∃ g, LimitComputable g ∧ Prefix g p.length = p := by
  obtain ⟨approx, happ, hlim⟩ := hf
  refine ⟨fun t => if h : t < p.length then p.getD t 0 else f t, ?_, ?_⟩
  · refine ⟨fun t s => if h : t < p.length then p.getD t 0 else approx t s, ?_, ?_⟩
    · have hlt : PrimrecPred fun q : ℕ × ℕ => q.1 < p.length :=
        Primrec.nat_lt.comp Primrec.fst (Primrec.const p.length)
      refine Computable.cond (hlt.decide.to_comp)
        ((Primrec.list_getD (0 : ℕ)).comp (Primrec.const p) Primrec.fst).to_comp
        (happ.comp (Computable.fst.pair Computable.snd)) |>.of_eq fun q => by
        simp [Bool.cond_decide]
    · intro t
      by_cases ht : t < p.length
      · refine ⟨0, fun s _ => by simp [ht]⟩
      · obtain ⟨s₀, hs₀⟩ := hlim t
        refine ⟨s₀, fun s hs => by simp [ht, hs₀ s hs]⟩
  · rw [Prefix]
    refine (List.map_congr_left fun i hi => ?_).trans (prefix_getD_eq p)
    simp [List.mem_range.mp hi]

/-! ### Diagonal against limit-computable approximants -/

open Nat.Partrec (Code)
open Nat.Partrec.Code (eval evaln curry eval_curry eval_eq_rfindOpt)

/-- The `e`-th computable approximant at input `t` and stage `s`.
Uses `curry` so the `evaln` input is `s` rather than `Nat.pair t s`. -/
noncomputable def limitApprox (e t s : ℕ) : ℕ :=
  haveI : Decidable
      ((Nat.rfindOpt fun k => evaln k (curry (Denumerable.ofNat Code e) t) s).Dom) :=
    Classical.propDecidable _
  Option.getD
    (Part.toOption (Nat.rfindOpt fun k => evaln k (curry (Denumerable.ofNat Code e) t) s)) 0

private theorem limitApprox_eq_g {g : ℕ → ℕ → ℕ} {c : Code}
    (_hc : eval c = fun p => Part.some (g (Nat.unpair p).1 (Nat.unpair p).2)) (t s : ℕ)
    (hx : g t s ∈ eval c (Nat.pair t s)) :
    limitApprox (Encodable.encode c) t s = g t s := by
  classical
  simp only [limitApprox, Denumerable.ofNat_encode]
  have hx' : g t s ∈ eval (curry c t) s := (eval_curry c t s).symm ▸ hx
  have hmem : g t s ∈ Nat.rfindOpt (fun k => evaln k (curry c t) s) := by
    rwa [eval_eq_rfindOpt] at hx'
  have hto : Part.toOption (Nat.rfindOpt fun k => evaln k (curry c t) s) = Option.some (g t s) :=
    Part.toOption_eq_some_iff.mpr hmem
  simp [hto]

private def stabilizesToZero (e t : ℕ) : Prop :=
  ∃ s₀, ∀ s ≥ s₀, limitApprox e t s = 0

noncomputable def notLimitExtension (p : List ℕ) : ℕ → ℕ :=
  fun t =>
    if _h : t < p.length then
      p.getD t 0
    else
      let e := t - p.length
      haveI : Decidable (stabilizesToZero e t) := Classical.dec _
      if stabilizesToZero e t then 1 else 0

theorem notLimitExtension_prefix (p : List ℕ) :
    Prefix (notLimitExtension p) p.length = p := by
  rw [Prefix]
  refine (List.map_congr_left fun i hi => ?_).trans (prefix_getD_eq p)
  simp [notLimitExtension, List.mem_range.mp hi]

theorem notLimitExtension_not_limitComputable (p : List ℕ) :
    ¬ LimitComputable (notLimitExtension p) := by
  classical
  intro h
  obtain ⟨g, hg, hlim⟩ := h
  have hgUnpair : Computable fun p : ℕ => g p.unpair.1 p.unpair.2 :=
    hg.comp (Computable.unpair.comp Computable.id)
  have hpartrec : Nat.Partrec (fun q => Part.some (g q.unpair.1 q.unpair.2)) :=
    Partrec.nat_iff.1 (Partrec.some.comp hgUnpair)
  obtain ⟨cMaster, hcMaster⟩ := Nat.Partrec.Code.exists_code.mp hpartrec
  set e := Encodable.encode cMaster with he
  set t := p.length + e with ht
  have ht' : t - p.length = e := by unfold t; omega
  obtain ⟨sLim, hsLim⟩ := hlim t
  by_cases hst : stabilizesToZero e t
  · obtain ⟨s₀, hs₀⟩ := hst
    set s' := max (max sLim s₀) 1 with hs'def
    have hsge' : s₀ ≤ s' := by unfold s'; omega
    have hsLim'' : sLim ≤ s' := by unfold s'; omega
    have hx' : g t s' ∈ eval cMaster (Nat.pair t s') := by
      rw [hcMaster]; simp only [Nat.unpair_pair]; exact Part.mem_some _
    have hlz : limitApprox e t s' = 0 := hs₀ s' hsge'
    have hg : g t s' = notLimitExtension p t := hsLim s' hsLim''
    have hla' : limitApprox e t s' = g t s' :=
      limitApprox_eq_g (g := g) (c := cMaster) hcMaster t s' hx'
    have hf0 : notLimitExtension p t = 0 := by rw [← hg, ← hla', hlz]
    have htge : ¬ t < p.length := by unfold t; omega
    have hf1 : notLimitExtension p t = 1 := by
      have hstab : stabilizesToZero e t := ⟨s₀, hs₀⟩
      simp [notLimitExtension, ht', htge, if_pos hstab]
    exact Nat.zero_ne_one (hf0.symm.trans hf1)
  · have hnot : ∀ s₀, ∃ s ≥ s₀, limitApprox e t s ≠ 0 := by
      intro s₀
      by_contra hall
      push Not at hall
      exact hst ⟨s₀, hall⟩
    obtain ⟨s'', hs''ge, hne⟩ := hnot sLim
    have hx'' : g t s'' ∈ eval cMaster (Nat.pair t s'') := by
      rw [hcMaster]; simp only [Nat.unpair_pair]; exact Part.mem_some _
    have hg0 : g t s'' = notLimitExtension p t := hsLim s'' hs''ge
    have htge : ¬ t < p.length := by unfold t; omega
    have hf0 : notLimitExtension p t = 0 := by
      simp [notLimitExtension, ht', htge, if_neg hst]
    have hla0 : limitApprox e t s'' = 0 := by
      rw [limitApprox_eq_g (g := g) (c := cMaster) hcMaster t s'' hx'', hg0, hf0]
    exact hne hla0

theorem limitComputable_dense : ∀ p : List ℕ, ∃ f, LimitComputable f ∧ Prefix f p.length = p := by
  intro p
  obtain ⟨f, hf, hpre⟩ :=
    limitComputable_prefix_extension (computable_limitComputable (Computable.const 0)) p
  exact ⟨f, hf, hpre⟩

theorem notLimitComputable_dense : ∀ p : List ℕ, ∃ f, ¬ LimitComputable f ∧ Prefix f p.length = p := by
  intro p
  refine ⟨notLimitExtension p, notLimitExtension_not_limitComputable p, notLimitExtension_prefix p⟩

/-! ### Born measure (fraction representation) -/

def finPrefix (k : ℕ) (f : ℕ → Fin k) (t : ℕ) : List ℕ :=
  Prefix (fun i => (f i).val) t

/-- Prefix list alias (same as `finPrefix`; used in computability recursion). -/
abbrev finPrefixList (k : ℕ) (f : ℕ → Fin k) (t : ℕ) : List ℕ := finPrefix k f t

/-- A computable Born measure via numerator/denominator pairs per prefix and symbol.
Indices are `ℕ` (not `Fin k`) so computability is plain nat arithmetic. -/
structure BornMeasure (k : ℕ) where
  condNum : List ℕ → ℕ → ℕ
  condDen : List ℕ → ℕ → ℕ
  compNum : Computable (fun p : List ℕ × ℕ => condNum p.1 p.2)
  compDen : Computable (fun p : List ℕ × ℕ => condDen p.1 p.2)
  posDen : ∀ p a, a < k → 0 < condDen p a
  posNum : ∀ p a, a < k → 0 < condNum p a
  num_le_den : ∀ p a, a < k → condNum p a ≤ condDen p a
  sums_to_one : ∀ p,
    (Finset.univ : Finset (Fin k)).sum (fun a => (condNum p a.val : ℚ) / condDen p a.val) = 1

namespace BornMeasure

variable {k : ℕ} (μ : BornMeasure k)

def bornCond (p : List ℕ) (a : Fin k) : ℚ :=
  μ.condNum p a.val / μ.condDen p a.val

theorem bornCond_nonneg (p : List ℕ) (a : Fin k) : 0 ≤ bornCond μ p a := by
  unfold bornCond
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_pos.mpr (μ.posDen p a.val a.isLt)).le

theorem bornCond_le_one (p : List ℕ) (a : Fin k) : bornCond μ p a ≤ 1 := by
  unfold bornCond
  have hden : 0 < (μ.condDen p a.val : ℚ) := Nat.cast_pos.mpr (μ.posDen p a.val a.isLt)
  rw [div_le_one hden]
  exact Nat.cast_le.mpr (μ.num_le_den p a.val a.isLt)

/-- Non-degeneracy along `f`: the realized next symbol has probability at most `1 - ε`
infinitely often. -/
def NonDegenerateAlong (f : ℕ → Fin k) (ε : ℚ) : Prop :=
  ∀ n, ∃ t ≥ n, bornCond μ (finPrefix k f t) (f t) ≤ 1 - ε

/-- A computable `μ`-martingale via nat capital numerator/denominator. -/
structure CMartingale (μ : BornMeasure k) where
  dNum : List ℕ → ℕ
  dDen : List ℕ → ℕ
  compNum : Computable dNum
  compDen : Computable dDen
  posDen : ∀ p, 0 < dDen p
  fair : ∀ p, (dNum p : ℚ) / dDen p = (Finset.univ : Finset (Fin k)).sum fun a =>
      bornCond μ p a * ((dNum (p ++ [a.val]) : ℚ) / dDen (p ++ [a.val]))

end BornMeasure

noncomputable def martingaleValue {k : ℕ} {μ : BornMeasure k} (m : BornMeasure.CMartingale μ)
    (p : List ℕ) : ℚ :=
  (m.dNum p : ℚ) / m.dDen p

theorem martingaleValue_nonneg {k : ℕ} {μ : BornMeasure k} (m : BornMeasure.CMartingale μ)
    (p : List ℕ) : 0 ≤ martingaleValue m p := by
  unfold martingaleValue
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_pos.mpr (m.posDen p)).le

def Succeeds {k : ℕ} {μ : BornMeasure k} (m : BornMeasure.CMartingale μ) (f : ℕ → Fin k) : Prop :=
  ∀ B : ℚ, ∃ t, B < martingaleValue m (finPrefix k f t)

def ComputablyRandom {k : ℕ} (μ : BornMeasure k) (f : ℕ → Fin k) : Prop :=
  ∀ m : BornMeasure.CMartingale μ, ¬ Succeeds m f

def Glimmer {k : ℕ} (μ : BornMeasure k) (f : ℕ → Fin k) : Prop :=
  ComputablyRandom μ f ∧ LimitComputable (fun i => (f i).val)

open BornMeasure

/-! ### The bet-everything martingale -/

namespace BetMartingale

variable {k : ℕ}

def capitalNum (μ : BornMeasure k) (f : ℕ → Fin k) : ℕ → ℕ
  | 0 => 1
  | t + 1 => capitalNum μ f t * μ.condDen (finPrefix k f t) (f t).val

def capitalDen (μ : BornMeasure k) (f : ℕ → Fin k) : ℕ → ℕ
  | 0 => 1
  | t + 1 => capitalDen μ f t * μ.condNum (finPrefix k f t) (f t).val

noncomputable def capital (μ : BornMeasure k) (f : ℕ → Fin k) (t : ℕ) : ℚ :=
  (capitalNum μ f t : ℚ) / capitalDen μ f t

theorem capital_zero (μ : BornMeasure k) (f : ℕ → Fin k) :
    capital μ f 0 = 1 := by simp [capital, capitalNum, capitalDen]

theorem capital_succ (μ : BornMeasure k) (f : ℕ → Fin k) (t : ℕ) :
    capital μ f (t + 1) =
      capital μ f t / BornMeasure.bornCond μ (finPrefix k f t) (f t) := by
  unfold capital capitalNum capitalDen BornMeasure.bornCond
  cases t with
  | zero =>
    simp [capitalNum, capitalDen, finPrefix, Prefix, List.range_zero]
  | succ t =>
    set p := finPrefix k f t
    set a := (f t).val
    have hden : (0 : ℚ) < (μ.condDen p a : ℚ) := Nat.cast_pos.mpr (μ.posDen p a (f t).isLt)
    have hnum : (0 : ℚ) < (μ.condNum p a : ℚ) := Nat.cast_pos.mpr (μ.posNum p a (f t).isLt)
    simp [capitalNum, capitalDen, finPrefix, Prefix]
    field_simp [hden.ne', hnum.ne']

theorem capital_nonneg (μ : BornMeasure k) (f : ℕ → Fin k) (t : ℕ) :
    0 ≤ capital μ f t := by
  unfold capital
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_pos.mpr (by
    induction t with
    | zero => simp [capitalDen]
    | succ t ih =>
      rw [capitalDen]
      exact Nat.mul_pos ih (μ.posNum _ _ (f t).isLt))).le

private theorem capitalNum_pos (μ : BornMeasure k) (f : ℕ → Fin k) (t : ℕ) :
    0 < capitalNum μ f t := by
  induction t with
  | zero => simp [capitalNum]
  | succ t ih =>
    rw [capitalNum]
    exact Nat.mul_pos ih (μ.posDen _ _ (f t).isLt)

private theorem capitalDen_pos (μ : BornMeasure k) (f : ℕ → Fin k) (t : ℕ) :
    0 < capitalDen μ f t := by
  induction t with
  | zero => simp [capitalDen]
  | succ t ih =>
    rw [capitalDen]
    exact Nat.mul_pos ih (μ.posNum _ _ (f t).isLt)

theorem capital_pos (μ : BornMeasure k) (f : ℕ → Fin k) (t : ℕ) :
    0 < capital μ f t := by
  unfold capital
  exact div_pos (Nat.cast_pos.mpr (capitalNum_pos μ f t)) (Nat.cast_pos.mpr (capitalDen_pos μ f t))

theorem capital_mono (μ : BornMeasure k) (f : ℕ → Fin k) {t₁ t₂ : ℕ} (h : t₁ ≤ t₂) :
    capital μ f t₁ ≤ capital μ f t₂ := by
  have step : ∀ t, capital μ f t ≤ capital μ f (t + 1) := fun t => by
    rw [capital_succ]
    set p := finPrefix k f t with hpdef
    set a := f t with hadef
    have hcondpos : 0 < BornMeasure.bornCond μ p a := by
      unfold BornMeasure.bornCond
      exact div_pos (Nat.cast_pos.mpr (μ.posNum p a.val a.isLt))
        (Nat.cast_pos.mpr (μ.posDen p a.val a.isLt))
    refine (le_div_iff₀ hcondpos).mpr ?_
    nlinarith [BornMeasure.bornCond_le_one μ p a, capital_nonneg μ f t,
      BornMeasure.bornCond_nonneg μ p a]
  exact (monotone_nat_of_le_succ step) h

private theorem one_sub_eps_pos (μ : BornMeasure k) (f : ℕ → Fin k) {ε : ℚ}
    (hμ : NonDegenerateAlong μ f ε) : (0 : ℚ) < 1 - ε := by
  obtain ⟨t, _, hcond⟩ := hμ 0
  have hpos : 0 < BornMeasure.bornCond μ (finPrefix k f t) (f t) := by
    unfold BornMeasure.bornCond
    exact div_pos (Nat.cast_pos.mpr (μ.posNum _ _ (f t).isLt))
      (Nat.cast_pos.mpr (μ.posDen _ _ (f t).isLt))
  linarith [BornMeasure.bornCond_le_one μ (finPrefix k f t) (f t), hcond, hpos]

theorem capital_ge_of_nondeg (μ : BornMeasure k) (f : ℕ → Fin k) {ε : ℚ} (_hε : 0 < ε) (t : ℕ)
    (ht : BornMeasure.bornCond μ (finPrefix k f t) (f t) ≤ 1 - ε) :
    capital μ f t * (1 / (1 - ε)) ≤ capital μ f (t + 1) := by
  set p := finPrefix k f t with hpdef
  set a := f t with hadef
  have hcondpos : 0 < BornMeasure.bornCond μ p a := by
    unfold BornMeasure.bornCond
    exact div_pos (Nat.cast_pos.mpr (μ.posNum p a.val a.isLt))
      (Nat.cast_pos.mpr (μ.posDen p a.val a.isLt))
  have hden : 0 < 1 - ε := by linarith [ht, hcondpos]
  have hcap := capital_pos μ f t
  rw [capital_succ, le_div_iff₀ hcondpos]
  field_simp [hden.ne', hcondpos.ne', hcap.ne']
  nlinarith [ht, hcap, hcondpos]

def onPath (_μ : BornMeasure k) (f : ℕ → Fin k) (p : List ℕ) : Prop :=
  p = finPrefix k f p.length

/-- One-step wrong child off the realized path: parent prefix matches but full list does not. -/
def wrongChild (_μ : BornMeasure k) (f : ℕ → Fin k) (p : List ℕ) : Prop :=
  0 < p.length ∧
    p.take (p.length - 1) = finPrefix k f (p.length - 1) ∧
      p ≠ finPrefix k f p.length

instance wrongChildDecidable (μ : BornMeasure k) (f : ℕ → Fin k) (p : List ℕ) :
    Decidable (wrongChild μ f p) := by
  unfold wrongChild
  infer_instance

def wrongChildBool (μ : BornMeasure k) (f : ℕ → Fin k) (p : List ℕ) : Bool :=
  decide (wrongChild μ f p)

theorem wrongChild_iff (μ : BornMeasure k) (f : ℕ → Fin k) (p : List ℕ) :
    wrongChild μ f p ↔ wrongChildBool μ f p = true := by
  simp [wrongChildBool]

/-- Some initial segment of `p` is a one-step wrong child (dead branch). -/
def hasWrongStepBool (μ : BornMeasure k) (f : ℕ → Fin k) (p : List ℕ) : Bool :=
  (List.range p.length).any fun i => wrongChildBool μ f (p.take (i + 1))

def hasWrongStep (μ : BornMeasure k) (f : ℕ → Fin k) (p : List ℕ) : Prop :=
  hasWrongStepBool μ f p = true

instance hasWrongStepDecidable (μ : BornMeasure k) (f : ℕ → Fin k) (p : List ℕ) :
    Decidable (hasWrongStep μ f p) := by
  simp [hasWrongStep]
  infer_instance

theorem hasWrongStep_iff (μ : BornMeasure k) (f : ℕ → Fin k) (p : List ℕ) :
    hasWrongStep μ f p ↔ hasWrongStepBool μ f p = true := Iff.rfl

private theorem list_range_any_append_singleton (f : ℕ → Bool) (l : List ℕ) (n : ℕ) :
    (l ++ [n]).any (fun i => f i) = (l.any (fun i => f i) || f n) := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    rw [show (x :: xs) ++ [n] = x :: (xs ++ [n]) from rfl, List.any_cons, ih, List.any_cons, Bool.or_assoc]

private theorem list_range_any_eq_nat_rec (f : ℕ → Bool) : ∀ n,
    (List.range n).any (fun i => f i) =
      Nat.rec false (fun i acc => acc || f i) n := by
  intro n
  induction n with
  | zero => simp [List.range_zero, Nat.rec_zero, List.any_nil]
  | succ n ih =>
    rw [List.range_succ, list_range_any_append_singleton, ih]

private theorem hasWrongStepBool_eq_nat_rec (μ : BornMeasure k) (f : ℕ → Fin k) (p : List ℕ) :
    hasWrongStepBool μ f p =
      Nat.rec false (fun i acc => acc || wrongChildBool μ f (p.take (i + 1))) p.length :=
  list_range_any_eq_nat_rec (fun i => wrongChildBool μ f (p.take (i + 1))) p.length

theorem wrongChild_hasWrongStep (μ : BornMeasure k) (f : ℕ → Fin k) (p : List ℕ)
    (hw : wrongChild μ f p) : hasWrongStep μ f p := by
  rw [hasWrongStep_iff, hasWrongStepBool, List.any_eq_true]
  refine ⟨p.length - 1, List.mem_range.mpr (Nat.sub_lt hw.1 Nat.one_pos), ?_⟩
  rw [show p.take (p.length - 1 + 1) = p from by
    rw [Nat.sub_add_cancel (Nat.succ_le_of_lt hw.1), List.take_length]]
  exact (wrongChild_iff μ f p).1 hw

theorem hasWrongStep_of_take (μ : BornMeasure k) (f : ℕ → Fin k) {p : List ℕ} {i : ℕ}
    (hi : i < p.length) (hw : wrongChild μ f (p.take (i + 1))) : hasWrongStep μ f p := by
  rw [hasWrongStep_iff, hasWrongStepBool, List.any_eq_true]
  refine ⟨i, List.mem_range.mpr hi, (wrongChild_iff μ f _).1 hw⟩

theorem hasWrongStep_append (μ : BornMeasure k) (f : ℕ → Fin k) (p q : List ℕ)
    (hws : hasWrongStep μ f p) : hasWrongStep μ f (p ++ q) := by
  rw [hasWrongStep_iff, hasWrongStepBool, List.any_eq_true] at hws ⊢
  obtain ⟨i, hi, hwb⟩ := hws
  refine ⟨i, List.mem_range.mpr (Nat.lt_of_lt_of_le (List.mem_range.mp hi)
    (by simp [List.length_append])), ?_⟩
  have hile : i + 1 ≤ p.length := Nat.succ_le_of_lt (List.mem_range.mp hi)
  have htake : (p ++ q).take (i + 1) = p.take (i + 1) := by
    rw [List.take_eq_left_iff]
    exact Or.inr hile
  rw [show (p ++ q).take (i + 1) = p.take (i + 1) from htake]
  exact hwb

def dNum (μ : BornMeasure k) (f : ℕ → Fin k) (p : List ℕ) : ℕ :=
  if p = finPrefix k f p.length then capitalNum μ f p.length
  else if hasWrongStepBool μ f p then 0
  else 1

def dDen (μ : BornMeasure k) (f : ℕ → Fin k) (p : List ℕ) : ℕ :=
  if p = finPrefix k f p.length then capitalDen μ f p.length else 1

noncomputable def dFun (μ : BornMeasure k) (f : ℕ → Fin k) (p : List ℕ) : ℚ :=
  (dNum μ f p : ℚ) / dDen μ f p

theorem finPrefix_length (k : ℕ) (f : ℕ → Fin k) (t : ℕ) :
    (finPrefix k f t).length = t := by
  simp [finPrefix, Prefix, List.length_map, List.length_range]

theorem finPrefix_succ_eq_append (k : ℕ) (f : ℕ → Fin k) (p : List ℕ)
    (h : p = finPrefix k f p.length) :
    finPrefix k f (p.length + 1) = p ++ [(f p.length).val] := by
  rw [h]
  simp [finPrefix, Prefix, List.range_succ, List.map_append]

theorem finPrefix_take_eq (k : ℕ) (f : ℕ → Fin k) {t n : ℕ} (hn : n ≤ t) :
    (finPrefix k f t).take n = finPrefix k f n := by
  apply List.ext_getElem
  · simp [finPrefix_length, List.length_take, Nat.min_eq_left hn]
  · intro i hi hi'
    simp [finPrefix, Prefix, List.getElem_take, List.getElem_map, List.getElem_range]

private theorem take_append_singleton_prefix {p : List ℕ} {a : ℕ} :
    (p ++ [a]).take p.length = p := by
  rw [List.take_append, Nat.sub_self, List.take_zero, List.append_nil,
    (List.take_eq_self_iff p).2 (Nat.le_refl p.length)]

private theorem wrongChild_append_of_onPath (μ : BornMeasure k) (f : ℕ → Fin k) {p : List ℕ} {a : Fin k}
    (hp : p = finPrefix k f p.length) (ha : a ≠ f p.length) : wrongChild μ f (p ++ [a.val]) := by
  refine ⟨by simp, ?_, ?_⟩
  · have hlen : (p ++ [a.val]).length - 1 = p.length := by simp
    rw [hlen, take_append_singleton_prefix, hp, finPrefix_length]
  · intro heq
    have hpre := finPrefix_succ_eq_append k f p hp
    have heq' : p ++ [a.val] = p ++ [(f p.length).val] := by
      rw [show (p ++ [a.val]).length = p.length + 1 from by simp] at heq
      exact heq.trans hpre
    have hsingle : [a.val] = [(f p.length).val] := (List.append_right_injective p).eq_iff.mp heq'
    exact ha (Fin.ext (List.singleton_injective hsingle))

private theorem onPath_of_child_eq_finPrefix (μ : BornMeasure k) (f : ℕ → Fin k) {p : List ℕ} {a : Fin k}
    (heq : p ++ [a.val] = finPrefix k f (p.length + 1)) : onPath μ f p := by
  rw [onPath]
  have htake := congrArg (List.take p.length) heq
  rw [take_append_singleton_prefix] at htake
  rw [show (finPrefix k f (p.length + 1)).take p.length = finPrefix k f p.length from
    finPrefix_take_eq (k := k) (f := f) (Nat.le_succ p.length)] at htake
  exact htake

theorem not_wrongChild_finPrefix (μ : BornMeasure k) (f : ℕ → Fin k) (t : ℕ) :
    ¬ wrongChild μ f (finPrefix k f t) := by
  intro hw
  have hlen : (finPrefix k f t).length = t := finPrefix_length k f t
  exact hw.2.2 (by rw [hlen])

theorem finPrefix_not_hasWrongStep (μ : BornMeasure k) (f : ℕ → Fin k) (t : ℕ) :
    ¬ hasWrongStep μ f (finPrefix k f t) := by
  intro hws
  rw [hasWrongStep_iff, hasWrongStepBool, List.any_eq_true] at hws
  obtain ⟨i, hi, hwb⟩ := hws
  have hi' : i < t := by
    rw [← finPrefix_length k f t]
    exact List.mem_range.mp hi
  have hle : i + 1 ≤ t := Nat.succ_le_of_lt hi'
  have hpre := finPrefix_take_eq (k := k) (f := f) hle
  exact not_wrongChild_finPrefix μ f (i + 1)
    ((wrongChild_iff μ f (finPrefix k f (i + 1))).mpr (by simpa [hpre] using hwb))

theorem dFun_onPath (μ : BornMeasure k) (f : ℕ → Fin k) (t : ℕ) :
    dFun μ f (finPrefix k f t) = capital μ f t := by
  have hnws : ¬ hasWrongStep μ f (finPrefix k f t) := finPrefix_not_hasWrongStep μ f t
  have hb : ¬ hasWrongStepBool μ f (finPrefix k f t) := fun ht =>
    hnws ((hasWrongStep_iff μ f _).mpr ht)
  simp [dFun, dNum, dDen, finPrefix_length, capital]

theorem dFun_hasWrongStep (μ : BornMeasure k) (f : ℕ → Fin k) (p : List ℕ)
    (hws : hasWrongStep μ f p) : dFun μ f p = 0 := by
  have hb : hasWrongStepBool μ f p = true := (hasWrongStep_iff μ f p).mp hws
  by_cases hpath : p = finPrefix k f p.length
  · exfalso
    exact finPrefix_not_hasWrongStep μ f p.length (hpath ▸ hws)
  · unfold dFun dNum dDen
    simp [hpath, hb]

theorem dFun_offPath (μ : BornMeasure k) (f : ℕ → Fin k) (p : List ℕ)
    (h : ¬ onPath μ f p) (hws : ¬ hasWrongStep μ f p) : dFun μ f p = 1 := by
  have hp : p ≠ finPrefix k f p.length := by
    intro heq
    exact h (by simpa [onPath] using heq)
  have hb : ¬ hasWrongStepBool μ f p := fun ht => hws ((hasWrongStep_iff μ f p).mpr ht)
  simp [dFun, dNum, dDen, hp, hb]

noncomputable def dExt (μ : BornMeasure k) (f : ℕ → Fin k) (p : List ℕ) (a : Fin k) : ℚ :=
  if _hws : hasWrongStep μ f (p ++ [a.val]) then 0
  else if _h : p = finPrefix k f p.length then
    if _ha : a = f p.length then capital μ f (p.length + 1) else 0
  else
    1

theorem dExt_eq_dFun_append (μ : BornMeasure k) (f : ℕ → Fin k) (p : List ℕ) (a : Fin k) :
    dExt μ f p a = dFun μ f (p ++ [a.val]) := by
  classical
  by_cases hws : hasWrongStep μ f (p ++ [a.val])
  · rw [dFun_hasWrongStep μ f (p ++ [a.val]) hws]
    simp [dExt, hws]
  · by_cases h : p = finPrefix k f p.length
    · by_cases ha : a = f p.length
      · have hL : dExt μ f p a = capital μ f (p.length + 1) := by
          simp [dExt, if_neg hws, if_pos h, if_pos ha]
        have hR : dFun μ f (p ++ [a.val]) = capital μ f (p.length + 1) := by
          have hchild : p ++ [a.val] = finPrefix k f (p.length + 1) := by
            rw [ha, finPrefix_succ_eq_append k f p h]
          rw [hchild, dFun_onPath]
        rw [hL, hR]
      · exact absurd (wrongChild_hasWrongStep μ f (p ++ [a.val])
          (wrongChild_append_of_onPath μ f h ha)) hws
    · have hchild : p ++ [a.val] ≠ finPrefix k f (p.length + 1) := by
        intro heq
        exact h (onPath_of_child_eq_finPrefix μ f heq)
      rw [dFun_offPath μ f (p ++ [a.val]) (by
          intro hpath
          apply hchild
          simpa [onPath] using hpath) hws, dExt]
      simp [h, hws]

private theorem wrongChild_append_of_not_onPath (μ : BornMeasure k) (f : ℕ → Fin k) {p : List ℕ} {a : Fin k}
    (h : ¬ onPath μ f p) (hw : wrongChild μ f (p ++ [a.val])) : wrongChild μ f p := by
  exfalso
  apply h
  simpa [onPath] using hw.2.1

theorem dFun_fair (μ : BornMeasure k) (f : ℕ → Fin k) (p : List ℕ) :
    dFun μ f p = (Finset.univ : Finset (Fin k)).sum fun a =>
      BornMeasure.bornCond μ p a * dFun μ f (p ++ [a.val]) := by
  classical
  by_cases hws : hasWrongStep μ f p
  · rw [dFun_hasWrongStep μ f p hws]
    have hchild : ∀ (a : Fin k), hasWrongStep μ f (p ++ [a.val]) := fun a =>
      hasWrongStep_append μ f p [a.val] hws
    simp_rw [fun a => dFun_hasWrongStep μ f (p ++ [a.val]) (hchild a), mul_zero, Finset.sum_const_zero]
  · by_cases h : onPath μ f p
    · have hp : p = finPrefix k f p.length := h
      let hda := f p.length
      have hpre : dFun μ f p = capital μ f p.length := by
        rw [hp, dFun_onPath, finPrefix_length]
      rw [hpre, Finset.sum_eq_single hda]
      · have hcondpos : 0 < BornMeasure.bornCond μ p hda := by
          unfold BornMeasure.bornCond
          exact div_pos (Nat.cast_pos.mpr (μ.posNum p hda.val hda.isLt))
            (Nat.cast_pos.mpr (μ.posDen p hda.val hda.isLt))
        have hnext : dFun μ f (finPrefix k f (p.length + 1)) = capital μ f (p.length + 1) :=
          dFun_onPath μ f (p.length + 1)
        have hchildEq : p ++ [hda.val] = finPrefix k f (p.length + 1) := by
          rw [← finPrefix_succ_eq_append k f p hp]
        have hdf : dFun μ f (p ++ [hda.val]) = capital μ f (p.length + 1) := by rw [hchildEq, hnext]
        have hmain : capital μ f p.length =
            BornMeasure.bornCond μ p hda * capital μ f (p.length + 1) := by
          calc capital μ f p.length
              = capital μ f p.length / BornMeasure.bornCond μ p hda * BornMeasure.bornCond μ p hda := by
                  field_simp [hcondpos.ne']
            _ = capital μ f (p.length + 1) * BornMeasure.bornCond μ p hda := by
                rw [capital_succ, show finPrefix k f p.length = p from hp.symm, div_mul_cancel₀ _ hcondpos.ne']
            _ = BornMeasure.bornCond μ p hda * capital μ f (p.length + 1) := by ring
        rw [hmain, hdf]
      · intro a ha hne
        rw [dFun_hasWrongStep μ f (p ++ [a.val])
          (wrongChild_hasWrongStep μ f (p ++ [a.val])
            (wrongChild_append_of_onPath μ f hp (by
              intro heq; exact hne (Fin.ext (congrArg Fin.val heq))))), mul_zero]
      · simp
    · have h1 : dFun μ f p = 1 := dFun_offPath μ f p h hws
      rw [h1]
      have hoff : ∀ (a : Fin k), dFun μ f (p ++ [a.val]) = 1 := fun a => by
        have hnws : ¬ hasWrongStep μ f (p ++ [a.val]) := by
          intro hws'
          rw [hasWrongStep_iff, hasWrongStepBool, List.any_eq_true] at hws'
          obtain ⟨i, hi, hw⟩ := hws'
          have hwb : wrongChildBool μ f _ = true := hw
          by_cases hlt : i < p.length
          · have htake : (p ++ [a.val]).take (i + 1) = p.take (i + 1) := by
              rw [List.take_eq_left_iff]
              exact Or.inr (Nat.succ_le_of_lt hlt)
            have hw' : wrongChild μ f (p.take (i + 1)) := (wrongChild_iff μ f _).mpr (by simpa [htake] using hwb)
            exact hws (hasWrongStep_of_take μ f hlt hw')
          · have hi' : i = p.length := by
              have hbound : i < p.length + 1 := by
                simpa [List.length_append] using List.mem_range.mp hi
              exact Nat.eq_of_le_of_lt_succ (Nat.le_of_not_lt hlt) hbound
            subst hi'
            have htake_full : (p ++ [a.val]).take (p.length + 1) = p ++ [a.val] := by
              rw [List.take_eq_self_iff]
              simp [List.length_append]
            have hwfull : wrongChild μ f (p ++ [a.val]) :=
              (wrongChild_iff μ f (p ++ [a.val])).mpr (by rwa [htake_full] at hwb)
            have hwtake : (p ++ [a.val]).take p.length = finPrefix k f p.length := by
              simpa [Nat.sub_one, List.length_append] using hwfull.2.1
            exact h (by
              rw [onPath]
              exact (take_append_singleton_prefix (p := p) (a := a.val)).symm.trans hwtake)
        exact dFun_offPath μ f (p ++ [a.val]) (fun hpath =>
          h (onPath_of_child_eq_finPrefix μ f (by
            simpa [onPath, finPrefix_length] using hpath))) hnws
      simp_rw [hoff, mul_one]
      exact (μ.sums_to_one p).symm

private theorem finPrefix_computable (_μ : BornMeasure k) (f : ℕ → Fin k)
    (hf : Computable (fun i => (f i).val)) :
    Computable (fun t => finPrefix k f t) := by
  have hstep : Computable₂ fun (_ : ℕ) (pr : ℕ × List ℕ) => pr.2 ++ [(f pr.1).val] :=
    Computable.list_append.comp (Computable.snd.comp (Computable.snd.comp Computable.id))
      (Computable.list_cons.comp
        (hf.comp (Computable.fst.comp (Computable.snd.comp Computable.id)))
        (Computable.const []))
  refine (Computable.nat_rec (f := id) (g := fun _ => ([] : List ℕ))
      (h := fun (_ : ℕ) (pr : ℕ × List ℕ) => pr.2 ++ [(f pr.1).val])
      Computable.id (Computable.const []) hstep).of_eq fun t => by
    simp [finPrefix, Prefix]
    induction t with
    | zero => rfl
    | succ n ih =>
      simp only [List.range_succ, List.map_append, List.map_singleton]
      rw [show Nat.rec [] (fun y IH => IH ++ [(f y).val]) n =
          List.map (fun i => (f i).val) (List.range n) from by simpa [id_eq] using ih]

private theorem condDenAt_computable (μ : BornMeasure k) (f : ℕ → Fin k)
    (hf : Computable (fun i => (f i).val)) :
    Computable (fun t => μ.condDen (finPrefix k f t) (f t).val) :=
  μ.compDen.comp (Computable.pair (finPrefix_computable μ f hf) hf)

private theorem condNumAt_computable (μ : BornMeasure k) (f : ℕ → Fin k)
    (hf : Computable (fun i => (f i).val)) :
    Computable (fun t => μ.condNum (finPrefix k f t) (f t).val) :=
  μ.compNum.comp (Computable.pair (finPrefix_computable μ f hf) hf)

private theorem capitalNum_computable (μ : BornMeasure k) (f : ℕ → Fin k)
    (hf : Computable (fun i => (f i).val)) :
    Computable (capitalNum μ f) := by
  have hcond := condDenAt_computable μ f hf
  have hstep : Computable₂ fun (_ : ℕ) (pr : ℕ × ℕ) =>
      pr.2 * μ.condDen (finPrefix k f pr.1) (f pr.1).val :=
    Primrec.nat_mul.to_comp.comp (Computable.snd.comp (Computable.snd.comp Computable.id))
      (hcond.comp (Computable.fst.comp (Computable.snd.comp Computable.id)))
  refine (Computable.nat_rec (f := id) (g := fun _ => 1)
      (h := fun (_ : ℕ) (pr : ℕ × ℕ) => pr.2 * μ.condDen (finPrefix k f pr.1) (f pr.1).val)
      Computable.id (Computable.const 1) hstep).of_eq fun t => by
    induction t with
    | zero => rfl
    | succ t ih =>
      simp only [capitalNum, id_eq]
      rw [show Nat.rec 1 (fun y IH => IH * μ.condDen (finPrefix k f y) (f y).val) t =
          capitalNum μ f t from ih]

private theorem capitalDen_computable (μ : BornMeasure k) (f : ℕ → Fin k)
    (hf : Computable (fun i => (f i).val)) :
    Computable (capitalDen μ f) := by
  have hcond := condNumAt_computable μ f hf
  have hstep : Computable₂ fun (_ : ℕ) (pr : ℕ × ℕ) =>
      pr.2 * μ.condNum (finPrefix k f pr.1) (f pr.1).val :=
    Primrec.nat_mul.to_comp.comp (Computable.snd.comp (Computable.snd.comp Computable.id))
      (hcond.comp (Computable.fst.comp (Computable.snd.comp Computable.id)))
  refine (Computable.nat_rec (f := id) (g := fun _ => 1)
      (h := fun (_ : ℕ) (pr : ℕ × ℕ) => pr.2 * μ.condNum (finPrefix k f pr.1) (f pr.1).val)
      Computable.id (Computable.const 1) hstep).of_eq fun t => by
    induction t with
    | zero => rfl
    | succ t ih =>
      simp only [capitalDen, id_eq]
      rw [show Nat.rec 1 (fun y IH => IH * μ.condNum (finPrefix k f y) (f y).val) t =
          capitalDen μ f t from ih]

private theorem onPath_computable (μ : BornMeasure k) (f : ℕ → Fin k)
    (hf : Computable (fun i => (f i).val)) :
    Computable (fun p : List ℕ => decide (p = finPrefix k f p.length)) := by
  have hfin : Computable (fun p : List ℕ => finPrefix k f p.length) :=
    (finPrefix_computable μ f hf).comp Computable.list_length
  exact (Primrec.eq.decide.to_comp.comp Computable.encode (Computable.encode.comp hfin)).of_eq
    fun p => by simp [Encodable.encode_injective.eq_iff]

private theorem wrongChildBool_computable (μ : BornMeasure k) (f : ℕ → Fin k)
    (hf : Computable (fun i => (f i).val)) :
    Computable (wrongChildBool μ f) := by
  have hfin : Computable (fun p : List ℕ => finPrefix k f p.length) :=
    (finPrefix_computable μ f hf).comp Computable.list_length
  have hfinPred : Computable (fun p : List ℕ => finPrefix k f (p.length - 1)) :=
    (finPrefix_computable μ f hf).comp
      (Primrec.nat_sub.comp Primrec.list_length (Primrec.const 1)).to_comp
  have htakePred : Computable (fun p : List ℕ => p.take (p.length - 1)) :=
    Primrec.list_take.comp (Primrec.pred.comp Primrec.list_length) Primrec.id |>.to_comp
  have hlenPos : Computable fun p : List ℕ => decide (0 < p.length) :=
    (PrimrecPred.decide (Primrec.nat_lt.comp (Primrec.const 0) Primrec.list_length)).to_comp
  have hparentMatch : Computable fun p : List ℕ =>
      decide (p.take (p.length - 1) = finPrefix k f (p.length - 1)) :=
    (Primrec.eq.decide.to_comp.comp
      (Computable.encode.comp htakePred)
      (Computable.encode.comp hfinPred)).of_eq fun p => by
      simp [Encodable.encode_injective.eq_iff]
  have hnotOnPath : Computable fun p : List ℕ => decide (p ≠ finPrefix k f p.length) :=
    (Primrec.not.to_comp.comp (Primrec.eq.decide.to_comp.comp Computable.encode (Computable.encode.comp hfin))).of_eq
      fun p => by simp [Encodable.encode_injective.eq_iff]
  refine (Primrec.and.to_comp.comp hlenPos
    (Primrec.and.to_comp.comp hparentMatch hnotOnPath)).of_eq fun p => by
    simp [wrongChildBool, wrongChild]

private theorem hasWrongStepBool_computable (μ : BornMeasure k) (f : ℕ → Fin k)
    (hf : Computable (fun i => (f i).val)) :
    Computable (hasWrongStepBool μ f) := by
  have hwrong := wrongChildBool_computable μ f hf
  have htakeSucc : Computable₂ fun (p : List ℕ) (n : ℕ) => p.take (n + 1) :=
    Primrec.list_take.comp (Primrec.succ.comp Primrec.snd) Primrec.fst |>.to_comp
  have hwrongAt : Computable₂ fun (p : List ℕ) (n : ℕ) => wrongChildBool μ f (p.take (n + 1)) :=
    hwrong.comp₂ htakeSucc
  have hstep : Computable₂ fun (p : List ℕ) (pr : ℕ × Bool) =>
      pr.2 || wrongChildBool μ f (p.take (pr.1 + 1)) :=
    Primrec.or.to_comp.comp
      (Primrec.snd.comp (Primrec.snd.comp Primrec.id)).to_comp
      (hwrongAt.comp (Primrec.fst.comp Primrec.id).to_comp (Primrec.fst.comp Primrec.snd).to_comp)
  refine (Computable.nat_rec Computable.list_length (Computable.const false) hstep).of_eq fun p =>
    (hasWrongStepBool_eq_nat_rec μ f p).symm

private theorem dNum_computable (μ : BornMeasure k) (f : ℕ → Fin k)
    (hf : Computable (fun i => (f i).val)) :
    Computable (dNum μ f) := by
  classical
  refine (Computable.cond (onPath_computable μ f hf)
    ((capitalNum_computable μ f hf).comp (Computable.list_length.comp Computable.id))
    (Computable.cond (hasWrongStepBool_computable μ f hf)
      (Computable.const 0) (Computable.const 1))).of_eq fun p => by
    simp [dNum, Bool.cond_eq_ite]

private theorem dDen_computable (μ : BornMeasure k) (f : ℕ → Fin k)
    (hf : Computable (fun i => (f i).val)) :
    Computable (dDen μ f) := by
  classical
  refine (Computable.cond (onPath_computable μ f hf)
    ((capitalDen_computable μ f hf).comp (Computable.list_length.comp Computable.id))
    (Computable.const 1)).of_eq fun p => by simp [dDen]

def bet (μ : BornMeasure k) (f : ℕ → Fin k) (hf : Computable (fun i => (f i).val)) :
    CMartingale μ where
  dNum := dNum μ f
  dDen := dDen μ f
  compNum := dNum_computable μ f hf
  compDen := dDen_computable μ f hf
  posDen := by
    intro p
    by_cases h : p = finPrefix k f p.length
    · have hpos : 0 < capitalDen μ f p.length := capitalDen_pos μ f p.length
      unfold dDen
      rw [if_pos h]
      exact hpos
    · unfold dDen
      rw [if_neg h]
      simp
  fair := by
    intro p
    exact dFun_fair μ f p

theorem bet_d_eq (μ : BornMeasure k) (f : ℕ → Fin k) (hf : Computable (fun i => (f i).val))
    (p : List ℕ) :
    martingaleValue (bet μ f hf) p = dFun μ f p := by
  simp [martingaleValue, bet, dFun, dNum, dDen]

private theorem iterate_nondeg (μ : BornMeasure k) (f : ℕ → Fin k) {ε : ℚ} (hε : 0 < ε)
    (hμ : NonDegenerateAlong μ f ε) (m : ℕ) :
    ∃ t, (1 / (1 - ε)) ^ m ≤ capital μ f t := by
  induction m with
  | zero =>
    exact ⟨0, by simp [capital_zero]⟩
  | succ m ih =>
    obtain ⟨t₀, ht₀⟩ := ih
    obtain ⟨t₁, ht₁ge, hcond⟩ := hμ t₀
    have ht₁ : (1 / (1 - ε)) ^ m ≤ capital μ f t₁ :=
      le_trans ht₀ (capital_mono μ f ht₁ge)
    refine ⟨t₁ + 1, ?_⟩
    have hstep := capital_ge_of_nondeg μ f hε t₁ hcond
    have hpos : (0 : ℚ) ≤ 1 / (1 - ε) := by
      have hone := one_sub_eps_pos μ f hμ
      positivity
    calc ((1 / (1 - ε)) ^ (m + 1)) = (1 / (1 - ε)) ^ m * (1 / (1 - ε)) := by ring
      _ ≤ capital μ f t₁ * (1 / (1 - ε)) := by gcongr
      _ ≤ capital μ f (t₁ + 1) := hstep

theorem bet_succeeds (μ : BornMeasure k) (f : ℕ → Fin k) (hf : Computable (fun i => (f i).val))
    {ε : ℚ} (hε : 0 < ε) (hμ : NonDegenerateAlong μ f ε) : Succeeds (bet μ f hf) f := by
  intro B
  have hone := one_sub_eps_pos μ f hμ
  have hr : 1 < (1 / (1 - ε)) := (one_lt_div hone).mpr (by linarith [hε])
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt B hr
  obtain ⟨t, ht⟩ := iterate_nondeg μ f hε hμ m
  refine ⟨t, ?_⟩
  rw [bet_d_eq μ f hf (finPrefix k f t), dFun_onPath]
  exact lt_of_lt_of_le hm ht

end BetMartingale

/-! ### Main theorems -/

theorem computable_not_random {k : ℕ} (μ : BornMeasure k) (f : ℕ → Fin k) (ε : ℚ)
    (hε : 0 < ε) (hμ : NonDegenerateAlong μ f ε) (hf : Computable (fun i => (f i).val)) :
    ¬ ComputablyRandom μ f := by
  intro hcr
  exact hcr (BetMartingale.bet μ f hf) (BetMartingale.bet_succeeds μ f hf hε hμ)

theorem glimmer_not_computable {k : ℕ} (μ : BornMeasure k) (f : ℕ → Fin k) (ε : ℚ)
    (hε : 0 < ε) (hμ : NonDegenerateAlong μ f ε) (hg : Glimmer μ f) :
    ¬ Computable (fun i => (f i).val) := by
  intro hc
  exact hg.1 (BetMartingale.bet μ f hc) (BetMartingale.bet_succeeds μ f hc hε hμ)

theorem glimmer_disjoint_D {k : ℕ} (μ : BornMeasure k) (f : ℕ → Fin k) (ε : ℚ)
    (hε : 0 < ε) (hμ : NonDegenerateAlong μ f ε) (hg : Glimmer μ f) :
    (fun i => (f i).val) ∉ D :=
  fun hD => glimmer_not_computable μ f ε hε hμ hg ((transcript_characterisation _).mp hD)

theorem glimmer_subset_Cstrict {k : ℕ} (μ : BornMeasure k) (f : ℕ → Fin k) (ε : ℚ)
    (hε : 0 < ε) (hμ : NonDegenerateAlong μ f ε) (hg : Glimmer μ f) :
    (fun i => (f i).val) ∈ Cstrict := by
  refine ⟨mem_C _, ?_⟩
  exact glimmer_not_computable μ f ε hε hμ hg

/-- A limit-computable transcript is fixed by one finite program code plus the limit
operation: some computable approximant `g` stabilizes to `f`, and a single `Code` computes
`g` via `eval`. (Glimmer members inherit this via `Glimmer.2`.) -/
theorem glimmer_finite_description {f : ℕ → ℕ} (hf : LimitComputable f) :
    ∃ (c : Code) (g : ℕ → ℕ → ℕ),
      Computable (fun p : ℕ × ℕ => g p.1 p.2) ∧
        (∀ t, ∃ s₀, ∀ s ≥ s₀, g t s = f t) ∧
          eval c = fun p => Part.some (g p.unpair.1 p.unpair.2) := by
  obtain ⟨g, hg, hlim⟩ := hf
  have hgUnpair : Computable fun p : ℕ => g p.unpair.1 p.unpair.2 :=
    hg.comp (Computable.unpair.comp Computable.id)
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp
    (Partrec.nat_iff.1 (Partrec.some.comp hgUnpair))
  exact ⟨c, g, hg, hlim, hc⟩

theorem limitComputable_disjoint_compl :
    Disjoint {f | LimitComputable f} {f | ¬ LimitComputable f} := by
  rw [Set.disjoint_left]
  intro f hf hnf
  exact hnf hf

theorem limitComputable_not_finitely_determined :
    ¬ ∃ P, FinitelyDetermined P ∧
      (∀ f, LimitComputable f → P f) ∧ (∀ f, ¬ LimitComputable f → ¬ P f) := by
  exact not_finitely_determined_of_dense_pair limitComputable_dense notLimitComputable_dense
    limitComputable_disjoint_compl

end Substrate
