import Substrate.Basic
import Substrate.Discrete
import Substrate.Prefix
import Substrate.NotFinDet

/-!
# Substrate.AxisA

Axis-A transcript class: eventually periodic sequences = transcripts of finite-state worlds.

Status: A_Lean (`EPIC_005_SUD_PAPER_REVISION_2`).
-/

namespace Substrate

/-- Transcripts realizable by a world with finite state space. -/
def Dfin : Set (ℕ → ℕ) :=
  {f | ∃ w : World, Finite w.S ∧ w.transcriptFn = f}

/-! ### Finite-state prefix world (density witness) -/

def prefixWorld (p : List ℕ) : World where
  S := Fin (p.length + 1)
  init := 0
  step := fun s =>
    if h : s.val < p.length then
      ⟨s.val + 1, Nat.succ_lt_succ h⟩
    else
      ⟨p.length, Nat.lt_succ_self p.length⟩
  read := fun s => p.getD s.val 0

private theorem prefixWorld_state_lt {p : List ℕ} :
    ∀ {t : ℕ}, (ht : t < p.length) →
      (prefixWorld p).step^[t] (prefixWorld p).init = ⟨t, Nat.lt_trans ht (Nat.lt_succ_self p.length)⟩ := by
  intro t ht
  induction t with
  | zero => simp [prefixWorld]
  | succ t ih =>
    have iht : t < p.length := Nat.lt_trans (Nat.lt_succ_self t) ht
    calc
      (prefixWorld p).step^[t.succ] (prefixWorld p).init
      _ = (prefixWorld p).step ((prefixWorld p).step^[t] (prefixWorld p).init) := by
        rw [Function.iterate_succ_apply']
      _ = ⟨t + 1, Nat.lt_trans ht (Nat.lt_succ_self p.length)⟩ := by
        rw [ih iht]
        dsimp [prefixWorld]
        simp [iht]

theorem prefixWorld_transcript_eq_getD (p : List ℕ) {i : ℕ} (hi : i < p.length) :
    (prefixWorld p).transcriptFn i = p.getD i 0 := by
  have hstate := prefixWorld_state_lt (p := p) (t := i) hi
  change (prefixWorld p).read ((prefixWorld p).step^[i] (prefixWorld p).init) = p.getD i 0
  rw [hstate]
  simp [prefixWorld]

theorem prefixWorld_transcript_prefix (p : List ℕ) :
    Prefix (prefixWorld p).transcriptFn p.length = p := by
  rw [Prefix]
  simpa using (List.map_congr_left (fun i hi =>
    prefixWorld_transcript_eq_getD p (List.mem_range.mp hi))).trans (prefix_getD_eq p)

theorem prefixWorld_mem_Dfin (p : List ℕ) : (prefixWorld p).transcriptFn ∈ Dfin := by
  refine ⟨prefixWorld p, Finite.of_fintype (Fin (p.length + 1)), rfl⟩

/-! ### Eventually periodicity from finite state -/

theorem World.eventuallyPeriodic_of_finite {w : World} (hfin : Finite w.S) :
    ∃ N p, p > 0 ∧ ∀ n ≥ N, w.transcriptFn (n + p) = w.transcriptFn n := by
  classical
  haveI : Fintype w.S := Fintype.ofFinite w.S
  set m := Fintype.card w.S with hm
  by_cases h0 : m = 0
  · have hempty : IsEmpty w.S := Fintype.card_eq_zero_iff.mp h0
    exact IsEmpty.elim hempty w.init
  · set s : ℕ → w.S := fun t => w.step^[t] w.init with hs
    have hpigeon : ∃ i j : Fin (m + 1), i < j ∧ s i = s j := by
      by_contra hall
      push Not at hall
      have hinj : Function.Injective (fun i : Fin (m + 1) => s i) := by
        intro a b hab
        by_cases hle : a.val ≤ b.val
        · obtain hab' | hablt := Nat.eq_or_lt_of_le hle
          · exact Fin.ext hab'
          · exact absurd hab (hall a b hablt)
        · push Not at hle
          have hlt : b.val < a.val := hle
          exact absurd hab.symm (hall b a hlt)
      have : m + 1 ≤ m := by
        simpa [hm] using Fintype.card_le_of_injective (fun i : Fin (m + 1) => s i) hinj
      omega
    obtain ⟨i, j, hij, hsij⟩ := hpigeon
    set p := j.val - i.val with hpdef
    have hppos : 0 < p := by
      have := Fin.mk_lt_mk.mp hij
      omega
    refine ⟨i.val, p, hppos, ?_⟩
    intro n hn
    have hperiod : ∀ k, w.step^[j.val + k] w.init = w.step^[i.val + k] w.init := by
      intro k
      induction k with
      | zero => exact hsij.symm
      | succ k ih =>
        have hj := Function.iterate_succ_apply' w.step (↑j + k) w.init
        have hi' := Function.iterate_succ_apply' w.step (↑i + k) w.init
        rw [show ↑j + (k + 1) = Nat.succ (↑j + k) from by omega, hj]
        rw [show ↑i + (k + 1) = Nat.succ (↑i + k) from by omega, hi']
        exact congr_arg w.step ih
    show w.transcriptFn (n + p) = w.transcriptFn n
    show w.read (w.step^[n + p] w.init) = w.read (w.step^[n] w.init)
    rw [show n + p = j.val + (n - i.val) from by unfold p; omega, hperiod (n - i.val),
        show i.val + (n - i.val) = n from by omega]

/-! ### Eventually periodic ⇒ finite-state realisation -/

def periodicWorld (f : ℕ → ℕ) (N p : ℕ) (hp : 0 < p) : World :=
  haveI : NeZero (N + p) := ⟨by omega⟩
  { S := Fin (N + p)
    init := 0
    step := fun s =>
      if h : s.val + 1 < N + p then
        ⟨s.val + 1, h⟩
      else
        have hN : N < N + p := by omega
        ⟨N, hN⟩
    read := fun s => f s.val }

private theorem periodicWorld_state_lt {f : ℕ → ℕ} {N p : ℕ} (hp : 0 < p) :
    ∀ {t : ℕ}, (ht : t < N + p) →
      (periodicWorld f N p hp).step^[t] (periodicWorld f N p hp).init = ⟨t, ht⟩ := by
  intro t ht
  induction t with
  | zero => simp [periodicWorld]
  | succ t ih =>
    have iht : t < N + p := Nat.lt_trans (Nat.lt_succ_self t) ht
    calc
      (periodicWorld f N p hp).step^[t.succ] (periodicWorld f N p hp).init
      _ = (periodicWorld f N p hp).step
          ((periodicWorld f N p hp).step^[t] (periodicWorld f N p hp).init) := by
        rw [Function.iterate_succ_apply']
      _ = ⟨t + 1, ht⟩ := by
        rw [ih iht]
        dsimp [periodicWorld]
        simp [ht]

theorem eventuallyPeriodic_apply {f : ℕ → ℕ} {N p : ℕ} (hp : 0 < p)
    (hper : ∀ n ≥ N, f (n + p) = f n) {t : ℕ} (ht : N ≤ t) :
    f t = f (N + (t - N) % p) := by
  suffices h : ∀ q, f (N + q) = f (N + q % p) by
    trans f (N + (t - N))
    · exact congrArg f (Nat.add_sub_of_le ht).symm
    · exact h (t - N)
  intro q
  induction q using Nat.strong_induction_on with
  | _ q ih =>
    by_cases hq : q < p
    · simp [Nat.mod_eq_of_lt hq]
    · have hqp : q - p < q := Nat.sub_lt_self hp (by omega)
      have hq' : f (N + q) = f (N + (q - p)) := by
        have heq : N + q = (N + (q - p)) + p := by omega
        rw [heq]
        exact hper (N + (q - p)) (by omega)
      have hmod : (q - p) % p = q % p := by
        have hpq : p ≤ q := Nat.le_of_not_lt hq
        conv_rhs => rw [← Nat.sub_add_cancel hpq]
        rw [Nat.add_mod, Nat.mod_self, add_zero, Nat.mod_mod]
      calc f (N + q) = f (N + (q - p) % p) := by rw [hq', ih (q - p) hqp]
        _ = f (N + q % p) := by congr 1; exact congrArg (Nat.add N) hmod

private theorem periodicWorld_state_cycle {f : ℕ → ℕ} {N p : ℕ} (hp : 0 < p) :
    ∀ k, Fin.val ((periodicWorld f N p hp).step^[N + p + k]
      (periodicWorld f N p hp).init) = N + k % p := by
  intro k
  induction k with
  | zero =>
    have hlt : N + p - 1 < N + p := by omega
    have hstate := periodicWorld_state_lt (f := f) (N := N) (p := p) hp (t := N + p - 1) hlt
    have hsucc : (periodicWorld f N p hp).step^[N + p] (periodicWorld f N p hp).init =
        (periodicWorld f N p hp).step
          ((periodicWorld f N p hp).step^[N + p - 1] (periodicWorld f N p hp).init) := by
      rw [← Function.iterate_succ_apply' (periodicWorld f N p hp).step (N + p - 1)
        (periodicWorld f N p hp).init]
      congr 1
      exact (show Nat.succ (N + p - 1) = N + p by omega).symm
    calc Fin.val ((periodicWorld f N p hp).step^[N + p] (periodicWorld f N p hp).init)
        = Fin.val ((periodicWorld f N p hp).step ⟨N + p - 1, hlt⟩) := by
          rw [hsucc, hstate]
        _ = N := by
          dsimp [periodicWorld]
          have hn : ¬ (N + p - 1 + 1 < N + p) := by omega
          simp [Fin.val_mk, hn]
  | succ k ih =>
    calc Fin.val ((periodicWorld f N p hp).step^[N + p + k.succ] (periodicWorld f N p hp).init)
        = Fin.val ((periodicWorld f N p hp).step
            ((periodicWorld f N p hp).step^[N + p + k] (periodicWorld f N p hp).init)) := by
          rw [show N + p + k.succ = Nat.succ (N + p + k) from by omega, Function.iterate_succ_apply']
        _ = N + (k + 1) % p := by
          have hklt : N + k % p < N + p := by
            have := Nat.mod_lt k hp
            omega
          have hstate : (periodicWorld f N p hp).step^[N + p + k] (periodicWorld f N p hp).init =
              ⟨N + k % p, hklt⟩ := Fin.ext ih
          rw [show (periodicWorld f N p hp).step
              ((periodicWorld f N p hp).step^[N + p + k] (periodicWorld f N p hp).init)
              = (periodicWorld f N p hp).step ⟨N + k % p, hklt⟩ from congrArg _ hstate]
          dsimp [periodicWorld]
          by_cases h : k % p + 1 < p
          · have hcond : N + k % p + 1 < N + p := by omega
            have hval : (k + 1) % p = k % p + 1 := by
              calc (k + 1) % p = (k % p + 1 % p) % p := Nat.add_mod k 1 p
                _ = (k % p + 1) % p := by simp
                _ = k % p + 1 := Nat.mod_eq_of_lt h
            simp [Fin.val_mk, hcond, hval]
            omega
          · have hkmod : k % p = p - 1 := by omega
            have hplus : k % p + 1 = p := by omega
            have hcond : ¬ N + (p - 1) + 1 < N + p := by omega
            have hval : (k + 1) % p = 0 := by
              calc (k + 1) % p = (k % p + 1) % p := by simp [Nat.add_mod]
                _ = 0 := by rw [hplus, Nat.mod_self]
            simp [Fin.val_mk, hcond, hkmod, hval]

theorem periodicWorld_transcript {f : ℕ → ℕ} {N p : ℕ} (hp : 0 < p)
    (hper : ∀ n ≥ N, f (n + p) = f n) :
    (periodicWorld f N p hp).transcriptFn = f := by
  ext t
  dsimp [World.transcriptFn, World.transcript]
  by_cases ht : t < N + p
  · rw [@periodicWorld_state_lt f N p hp t ht]
    simp [periodicWorld]
  · have htge : N ≤ t := by omega
    have hcycle := periodicWorld_state_cycle (f := f) (N := N) (p := p) hp (t - (N + p))
    have hmod : (t - N) % p = (t - (N + p)) % p := by
      have h : (t - (N + p)) + p = t - N := by omega
      calc (t - N) % p = ((t - (N + p)) + p) % p := by rw [h]
        _ = ((t - (N + p)) % p + p % p) % p := by rw [Nat.add_mod]
        _ = (t - (N + p)) % p := by simp
    show (periodicWorld f N p hp).read
        ((periodicWorld f N p hp).step^[t] (periodicWorld f N p hp).init) = f t
    calc (periodicWorld f N p hp).read
          ((periodicWorld f N p hp).step^[t] (periodicWorld f N p hp).init)
        = (periodicWorld f N p hp).read
            ((periodicWorld f N p hp).step^[N + p + (t - (N + p))] (periodicWorld f N p hp).init) := by
          conv_lhs =>
            rw [show t = N + p + (t - (N + p)) from by omega]
        _ = f (N + (t - (N + p)) % p) := by
          simp [periodicWorld]
          exact congrArg f hcycle
        _ = f t := by
          trans f (N + (t - N) % p)
          · congr 1
            exact congrArg (Nat.add N) hmod.symm
          · exact (eventuallyPeriodic_apply hp hper htge).symm

theorem eventuallyPeriodic_mem_Dfin {f : ℕ → ℕ} {N p : ℕ} (hp : 0 < p)
    (hper : ∀ n ≥ N, f (n + p) = f n) : f ∈ Dfin := by
  refine ⟨(periodicWorld f N p hp), Finite.of_fintype (Fin (N + p)), periodicWorld_transcript hp hper⟩

/-! ### Characterisation and density -/

theorem Dfin_iff_eventuallyPeriodic (f : ℕ → ℕ) :
    f ∈ Dfin ↔ ∃ N p, p > 0 ∧ ∀ n ≥ N, f (n + p) = f n := by
  constructor
  · rintro ⟨w, hfin, rfl⟩
    obtain ⟨N, p, hp, hper⟩ := World.eventuallyPeriodic_of_finite hfin
    exact ⟨N, p, hp, hper⟩
  · rintro ⟨N, p, hp, hper⟩
    exact eventuallyPeriodic_mem_Dfin hp hper

def nonPeriodicExtension (p : List ℕ) : ℕ → ℕ :=
  fun t => if t < p.length then p.getD t 0 else t - p.length

theorem nonPeriodicExtension_prefix (p : List ℕ) :
    Prefix (nonPeriodicExtension p) p.length = p := by
  trans (List.range p.length).map (fun i => p.getD i 0)
  · apply List.map_congr_left
    intro i hi
    simp [nonPeriodicExtension, List.mem_range.mp hi]
  · exact prefix_getD_eq p

theorem identity_tail_not_eventuallyPeriodic (p : List ℕ) :
    ¬ ∃ N p', p' > 0 ∧ ∀ n ≥ N, nonPeriodicExtension p (n + p') = nonPeriodicExtension p n := by
  intro h
  obtain ⟨N, p', hp', hper⟩ := h
  set n := max N p.length with hn
  have hnge : n ≥ N := le_max_left _ _
  have hnge' : n ≥ p.length := le_max_right _ _
  have hf : nonPeriodicExtension p (n + p') = n + p' - p.length := by
    unfold nonPeriodicExtension
    split_ifs with hlt
    · exfalso; omega
    · rfl
  have hf' : nonPeriodicExtension p n = n - p.length := by
    unfold nonPeriodicExtension
    split_ifs with hlt
    · exfalso; omega
    · rfl
  have := hper n hnge
  rw [hf, hf'] at this
  omega

theorem Dfin_dense : ∀ p : List ℕ, ∃ f ∈ Dfin, Prefix f p.length = p := by
  intro p
  refine ⟨(prefixWorld p).transcriptFn, prefixWorld_mem_Dfin p, prefixWorld_transcript_prefix p⟩

theorem Dfin_compl_dense : ∀ p : List ℕ, ∃ f, f ∉ Dfin ∧ Prefix f p.length = p := by
  intro p
  refine ⟨nonPeriodicExtension p, ?_, nonPeriodicExtension_prefix p⟩
  intro hf
  obtain ⟨N, p', hp', hper⟩ := (Dfin_iff_eventuallyPeriodic _).mp hf
  exact identity_tail_not_eventuallyPeriodic p ⟨N, p', hp', hper⟩

theorem Dfin_disjoint_compl : Disjoint Dfin (Dfinᶜ) := by
  rw [Set.disjoint_left]
  intro f hf hfc
  exact hfc hf

theorem axisA_not_finitely_determined :
    ¬ ∃ P, FinitelyDetermined P ∧ (∀ f ∈ Dfin, P f) ∧ (∀ f ∈ Dfinᶜ, ¬ P f) := by
  exact not_finitely_determined_of_dense_pair Dfin_dense Dfin_compl_dense Dfin_disjoint_compl

end Substrate
