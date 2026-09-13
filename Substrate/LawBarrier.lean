import Substrate.Basic
import Substrate.Noncomputable
import Mathlib.Computability.Halting
import Mathlib.Computability.Reduce

/-!
# Substrate.LawBarrier

**Theorem 4 (Law-Certification Barrier).**  Even handed a candidate discrete law — a code
`e : Nat.Partrec.Code` alleged to generate the transcript of a computable `f` — an observer
cannot decide whether the law is correct, by reduction from the halting problem.

Reuses the halting-reduction *pattern* from `nems-lean` (`NemS.Diagonal.HaltingReduction`):
reduce from `ComputablePred.halting_problem` via a step-bounded `evaln` construction. This
repo has no code dependency on `nems-lean` (Mathlib only, per spec §8) — only the proof
technique is reused.

Construction: given `c : Code`, build `e_c` computing, on input `t`, `f t + 1` if `c` has
visibly halted on `0` within `t` steps (`evaln t c 0` is `some _`), else `f t`. Then `e_c`
matches `f` forever iff `c` never halts on `0`. The map `c ↦ e_c` is built uniformly and
computably via the $S^m_n$ theorem (`Nat.Partrec.Code.curry`).

**Theorem 4′ (`law_match_pi2_hard`).**  Sharpens the undecidability to Π⁰₂-hardness: the
totality set `Tot` many-one reduces to `LawMatches f`, via the sequential-composition
reduction that runs `c` to completion on each input and then emits `f`.  As `Tot` is
Π⁰₂-complete, `LawMatches f` is Π⁰₂-hard — strictly above the co-halting lower bound.

Status: A_Lean (`EPIC_001_SUD_PART_I` / Π⁰₂-hardness in `EPIC_005_SUD_PAPER_REVISION_2`) —
highest proof effort.
-/

namespace Substrate

open Nat.Partrec (Code)
open Nat.Partrec.Code (eval evaln curry)

/-! ### `HaltsOnZero` via bounded search -/

/-- `HaltsOnZero c` fails iff the bounded evaluator never reports a value on input `0`,
at any step bound. -/
theorem not_haltsOnZero_iff (c : Code) :
    ¬ HaltsOnZero c ↔ ∀ t, evaln t c 0 = none := by
  unfold HaltsOnZero
  constructor
  · intro hdom t
    cases hopt : evaln t c 0 with
    | none => rfl
    | some x =>
      have hx : x ∈ evaln t c 0 := by rw [hopt]; exact Option.mem_def.mpr rfl
      exact absurd (Part.dom_iff_mem.mpr ⟨x, Nat.Partrec.Code.evaln_sound hx⟩) hdom
  · intro hall hdom
    obtain ⟨x, hx⟩ := Part.dom_iff_mem.mp hdom
    obtain ⟨k, hk⟩ := Nat.Partrec.Code.evaln_complete.mp hx
    rw [hall k] at hk
    exact absurd hk (Option.not_mem_none x)

/-! ### The diagonal witness function -/

/-- `matchFn f c t` equals `f t` unless `c` has visibly halted on `0` within `t` steps,
in which case it is bumped by `1`. -/
def matchFn (f : ℕ → ℕ) (c : Code) (t : ℕ) : ℕ :=
  if (evaln t c 0).isSome then f t + 1 else f t

/-- `matchFn f c` agrees with `f` everywhere iff `c` never halts on `0`. -/
theorem matchFn_eq_f_iff (f : ℕ → ℕ) (c : Code) :
    (∀ t, matchFn f c t = f t) ↔ ¬ HaltsOnZero c := by
  rw [not_haltsOnZero_iff]
  constructor
  · intro h t
    by_contra hcontra
    have heq := h t
    unfold matchFn at heq
    rw [if_pos (Option.isSome_iff_ne_none.mpr hcontra)] at heq
    omega
  · intro hall t
    unfold matchFn
    rw [hall t]
    simp

/-- The diagonal witness as a single-variable function of the pairing `⟨code index, t⟩`. -/
def bigG (f : ℕ → ℕ) (p : ℕ) : ℕ :=
  matchFn f (Denumerable.ofNat Code p.unpair.1) p.unpair.2

theorem bigG_computable {f : ℕ → ℕ} (hf : Computable f) : Computable (bigG f) := by
  have hunpair1 : Computable (fun p : ℕ => p.unpair.1) := Computable.fst.comp Computable.unpair
  have hunpair2 : Computable (fun p : ℕ => p.unpair.2) := Computable.snd.comp Computable.unpair
  have hcode : Computable (fun p : ℕ => Denumerable.ofNat Code p.unpair.1) :=
    (Computable.ofNat Code).comp hunpair1
  have hevaln : Computable (fun p : ℕ => evaln p.unpair.2 (Denumerable.ofNat Code p.unpair.1) 0) :=
    ((Nat.Partrec.Code.primrec_evaln.to_comp).comp
      ((hunpair2.pair hcode).pair (Computable.const 0)))
  have hisSome : Computable
      (fun p : ℕ => (evaln p.unpair.2 (Denumerable.ofNat Code p.unpair.1) 0).isSome) :=
    Primrec.option_isSome.to_comp.comp hevaln
  have hf2 : Computable (fun p : ℕ => f p.unpair.2) := hf.comp hunpair2
  have hf2succ : Computable (fun p : ℕ => f p.unpair.2 + 1) :=
    (Computable.succ).comp hf2
  have hcond : Computable (fun p : ℕ =>
      cond (evaln p.unpair.2 (Denumerable.ofNat Code p.unpair.1) 0).isSome
        (f p.unpair.2 + 1) (f p.unpair.2)) :=
    Computable.cond hisSome hf2succ hf2
  refine hcond.of_eq (fun p => ?_)
  show (cond (evaln p.unpair.2 (Denumerable.ofNat Code p.unpair.1) 0).isSome
      (f p.unpair.2 + 1) (f p.unpair.2)) = bigG f p
  unfold bigG matchFn
  by_cases h : (evaln p.unpair.2 (Denumerable.ofNat Code p.unpair.1) 0).isSome <;> simp [h]

/-! ### The computable code-family `e : Code → Code` -/

/-- Predicate: code `e` matches computable transcript `f` at every time step. -/
def LawMatches (f : ℕ → ℕ) (e : Code) : Prop :=
  ∀ t, e.eval t = Part.some (f t)

/-- **Theorem 4 (Law-Certification Barrier).**  No candidate discrete law for a computable
`f` can be internally certified as matching `f` forever, on pain of deciding the halting
problem. -/
theorem law_match_undecidable (f : ℕ → ℕ) (hf : Computable f) :
    ¬ ComputablePred (LawMatches f) := by
  intro hpred
  have hpartrec : Nat.Partrec (fun p => Part.some (bigG f p)) :=
    Partrec.nat_iff.1 (Partrec.some.comp (bigG_computable hf))
  obtain ⟨cMaster, hcMaster⟩ := Nat.Partrec.Code.exists_code.mp hpartrec
  set e : Code → Code := fun c => curry cMaster (Encodable.encode c) with he
  have hcomp_e : Computable e := by
    have : Computable₂ curry := Nat.Partrec.Code.primrec₂_curry.to_comp
    exact this.comp (Computable.const cMaster) Computable.encode
  have heval : ∀ c t, eval (e c) t = Part.some (matchFn f c t) := by
    intro c t
    show eval (curry cMaster (Encodable.encode c)) t = Part.some (matchFn f c t)
    rw [Nat.Partrec.Code.eval_curry, hcMaster]
    show Part.some (bigG f (Nat.pair (Encodable.encode c) t)) = Part.some (matchFn f c t)
    congr 1
    unfold bigG
    rw [Nat.unpair_pair]
    simp [Denumerable.ofNat_encode]
  have hiff : ∀ c, LawMatches f (e c) ↔ ¬ HaltsOnZero c := by
    intro c
    unfold LawMatches
    constructor
    · intro hall
      apply (matchFn_eq_f_iff f c).1
      intro t
      exact Part.some_inj.mp ((heval c t).symm.trans (hall t))
    · intro nhall t
      rw [heval c t, (matchFn_eq_f_iff f c).2 nhall t]
  have hpred_e : ComputablePred (fun c => LawMatches f (e c)) :=
    ComputablePred.computable_of_manyOneReducible
      (ManyOneReducible.mk (LawMatches f) hcomp_e) hpred
  have hpred_not : ComputablePred (fun c => ¬ HaltsOnZero c) :=
    hpred_e.of_eq hiff
  have hpred_halts : ComputablePred HaltsOnZero :=
    (ComputablePred.not hpred_not).of_eq (fun c => by tauto)
  exact ComputablePred.halting_problem 0 hpred_halts

/-- **Corollary 4.1 (P30 bridge).**  Specialised to the observer's own dynamics: no total
internal certifier decides whether a candidate law code matches the observer's transcript —
the substrate law-certification instance of the no-total-self-certifier pattern (P30). -/
theorem law_match_undecidable_zero : ¬ ComputablePred (LawMatches (fun _ => 0)) :=
  law_match_undecidable (fun _ => 0) (Computable.const 0)

/-! ### Π⁰₂-hardness via totality

Two routes to `Tot ≤ₘ LawMatches f` are recorded here.

* The **step-bounded** route (`matchFnTot`, below) dualizes `matchFn`'s halting guard to a
  totality guard `∃ n ≤ t, failsAt c n`.  It gives a clean characterization
  (`matchFnTot_eq_f_iff`) but **cannot** yield a *computable* reduction: that guard is not
  uniformly decidable from bounded `evaln` stages (a slow-but-total code is indistinguishable
  from a non-halting one for arbitrarily many early stages), so the pairing witness is not
  computable.  This is why the earlier attempt stalled.

* The **sequential-composition** route (`seqMaster`, `law_match_pi2_hard`, below) sidesteps
  step-bounding entirely: run the coded program on input `t` *to completion* (unbounded),
  discard its output, and emit `f t`.  The resulting code matches `f` at every `t` iff the
  program halts on every input, i.e. iff it lies in `Tot`.  This is a genuine computable
  many-one reduction `Tot ≤₀ₘ LawMatches f`, hence (as `Tot` is Π⁰₂-complete) `LawMatches f`
  is Π⁰₂-hard — strictly above the co-halting lower bound of `law_match_undecidable`. -/

/-- Program `c` fails to halt on input `n`: no bounded stage ever reports a value. -/
def failsAt (c : Code) (n : ℕ) : Prop :=
  ∀ t, evaln t c n = none

/-- Totality: `c` halts on every input. -/
def Tot (c : Code) : Prop :=
  ∀ n, (eval c n).Dom

private theorem not_haltsOn_iff (c : Code) (n : ℕ) :
    ¬ (eval c n).Dom ↔ failsAt c n := by
  unfold failsAt
  constructor
  · intro hdom t
    cases hopt : evaln t c n with
    | none => rfl
    | some x =>
      have hx : x ∈ evaln t c n := by rw [hopt]; exact Option.mem_def.mpr rfl
      exact absurd (Part.dom_iff_mem.mpr ⟨x, Nat.Partrec.Code.evaln_sound hx⟩) hdom
  · intro hall hdom
    obtain ⟨x, hx⟩ := Part.dom_iff_mem.mp hdom
    obtain ⟨k, hk⟩ := Nat.Partrec.Code.evaln_complete.mp hx
    rw [hall k] at hk
    exact absurd hk (Option.not_mem_none x)

theorem not_tot_iff (c : Code) :
    ¬ Tot c ↔ ∃ n, failsAt c n := by
  constructor
  · intro hnt
    by_contra hall
    push Not at hall
    exact hnt fun n => by
      by_contra hnd
      exact hall n ((not_haltsOn_iff c n).1 hnd)
  · intro ⟨n, hf⟩ htot
    exact absurd (htot n) ((not_haltsOn_iff c n).2 hf)

/-- Dual of `matchFn`: bump once some input is permanently non-halting. -/
noncomputable def matchFnTot (f : ℕ → ℕ) (c : Code) (t : ℕ) : ℕ :=
  @ite _ (∃ n, n ≤ t ∧ failsAt c n) (Classical.propDecidable _) (f t + 1) (f t)

theorem matchFnTot_eq_f_iff (f : ℕ → ℕ) (c : Code) :
    (∀ t, matchFnTot f c t = f t) ↔ Tot c := by
  constructor
  · intro hall n
    by_contra hnd
    have hf : failsAt c n := (not_haltsOn_iff c n).1 hnd
    have ht' : ∃ k, k ≤ n ∧ failsAt c k := ⟨n, Nat.le_refl n, hf⟩
    have hne := hall n
    have hbump : matchFnTot f c n = f n + 1 := by simp [matchFnTot, ht']
    have heq : f n + 1 = f n := hbump.symm.trans hne
    omega
  · intro htot t
    by_cases h : ∃ n, n ≤ t ∧ failsAt c n
    · simp [matchFnTot, h]
      obtain ⟨n, _hnle, hf⟩ := h
      exact absurd (htot n) ((not_haltsOn_iff c n).2 hf)
    · simp [matchFnTot, h]

/-! ### The sequential-composition reduction `Tot ≤₀ₘ LawMatches f`

Given a code `c` and a computable `f`, the code returned by the reduction computes, on input
`t`, the partial value `(eval c t).bind (fun _ => Part.some (f t))` — equivalently
`(eval c t).map (fun _ => f t)`: run `c` on `t` to completion, ignore the result, and output
`f t`.  This value is `Part.some (f t)` exactly when `c` halts on `t`, so the code matches `f`
forever iff `c` is total. -/

/-- A `Part.map` by a constant equals that constant iff the underlying part is defined. -/
theorem part_map_const_eq_some_iff {p : Part ℕ} {v : ℕ} :
    p.map (fun _ => v) = Part.some v ↔ p.Dom := by
  rw [Part.eq_some_iff, Part.mem_map_iff]
  constructor
  · rintro ⟨a, ha, _⟩
    exact Part.dom_iff_mem.mpr ⟨a, ha⟩
  · intro hdom
    obtain ⟨a, ha⟩ := Part.dom_iff_mem.mp hdom
    exact ⟨a, ha, rfl⟩

/-- Master two-variable function of the reduction: on the pairing `⟨code index, t⟩`, run the
coded program on `t` to completion, discard the output, and return `f t`.  Partial recursive
in the pairing; defined at `⟨e, t⟩` iff the `e`-th program halts on `t`. -/
noncomputable def seqMaster (f : ℕ → ℕ) (p : ℕ) : Part ℕ :=
  (eval (Denumerable.ofNat Code p.unpair.1) p.unpair.2).map (fun _ => f p.unpair.2)

/-- `seqMaster f` is partial recursive: `eval` is partial recursive in its code/input pair
(`Nat.Partrec.Code.eval_part`), and the discard-then-emit continuation is computable from `f`. -/
theorem seqMaster_partrec {f : ℕ → ℕ} (hf : Computable f) : Nat.Partrec (seqMaster f) := by
  have hunpair1 : Computable (fun p : ℕ => p.unpair.1) := Computable.fst.comp Computable.unpair
  have hunpair2 : Computable (fun p : ℕ => p.unpair.2) := Computable.snd.comp Computable.unpair
  have hcode : Computable (fun p : ℕ => Denumerable.ofNat Code p.unpair.1) :=
    (Computable.ofNat Code).comp hunpair1
  have heval : Partrec (fun p : ℕ => eval (Denumerable.ofNat Code p.unpair.1) p.unpair.2) :=
    Nat.Partrec.Code.eval_part.comp hcode hunpair2
  have hg : Computable₂ (fun (p : ℕ) (_ : ℕ) => f p.unpair.2) :=
    hf.comp (hunpair2.comp Computable.fst)
  have hpart : Partrec (seqMaster f) := heval.map hg
  exact Partrec.nat_iff.1 hpart

/-- **Theorem 4′ (Π⁰₂-hardness of law-matching).**  For any computable `f`, the totality set
`Tot := {c | ∀ n, (eval c n).Dom}` many-one reduces to `LawMatches f`.  Since `Tot` is
Π⁰₂-complete (a standard recursion-theoretic fact, not formalized in Mathlib), `LawMatches f`
is Π⁰₂-hard — strictly stronger than the co-halting-hardness lower bound of
`law_match_undecidable`.  The reduction sends `c` to a code that runs `c` on each input to
completion and then emits `f`, so it matches `f` forever iff `c` is total. -/
theorem law_match_pi2_hard (f : ℕ → ℕ) (hf : Computable f) :
    ManyOneReducible Tot (LawMatches f) := by
  obtain ⟨cMaster, hcMaster⟩ := Nat.Partrec.Code.exists_code.mp (seqMaster_partrec hf)
  have heval : ∀ c t, eval (curry cMaster (Encodable.encode c)) t
      = (eval c t).map (fun _ => f t) := by
    intro c t
    rw [Nat.Partrec.Code.eval_curry, hcMaster]
    show seqMaster f (Nat.pair (Encodable.encode c) t) = (eval c t).map (fun _ => f t)
    unfold seqMaster
    rw [Nat.unpair_pair]
    simp [Denumerable.ofNat_encode]
  refine ⟨fun c => curry cMaster (Encodable.encode c), ?_, fun c => ?_⟩
  · have hcurry : Computable₂ curry := Nat.Partrec.Code.primrec₂_curry.to_comp
    exact hcurry.comp (Computable.const cMaster) Computable.encode
  · constructor
    · intro htot t
      have hgoal : eval (curry cMaster (Encodable.encode c)) t = Part.some (f t) := by
        rw [heval c t]
        exact part_map_const_eq_some_iff.mpr (htot t)
      exact hgoal
    · intro hlm n
      have hn : eval (curry cMaster (Encodable.encode c)) n = Part.some (f n) := hlm n
      rw [heval c n] at hn
      exact part_map_const_eq_some_iff.mp hn

/-- **Corollary (Π⁰₂-hardness, observer instance).**  Specialised to the constant transcript:
`Tot` many-one reduces to `LawMatches (fun _ => 0)`. -/
theorem law_match_pi2_hard_zero : ManyOneReducible Tot (LawMatches (fun _ => 0)) :=
  law_match_pi2_hard (fun _ => 0) (Computable.const 0)

end Substrate
