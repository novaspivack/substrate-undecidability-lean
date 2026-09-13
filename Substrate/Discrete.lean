import Substrate.Basic

/-!
# Substrate.Discrete

**Lemma 2.1:** `f ∈ D ↔ Computable f`.

(→) composition of computable `step`, `read`, iteration.
(←) take `S := ℕ`, `step := Nat.succ`, `read := f`.

Status: A_Lean (`EPIC_001_SUD_PART_I`).
-/

namespace Substrate

/-- Iterating a computable `step` from a computable basepoint is computable, via
`Computable.nat_rec` and the `Function.iterate_succ_apply'` recursion equation. -/
theorem World.iterate_computable {w : World} [Primcodable w.S]
    (hstep : Computable w.step) : Computable (fun t : ℕ => w.step^[t] w.init) := by
  have h : Computable fun t : ℕ =>
      Nat.rec (motive := fun _ => w.S) w.init (fun _ IH => w.step IH) t :=
    Computable.nat_rec (f := id) (g := fun _ : ℕ => w.init)
      (h := fun (_ : ℕ) (p : ℕ × w.S) => w.step p.2)
      Computable.id (Computable.const w.init)
      (hstep.comp (Computable.snd.comp Computable.snd))
  refine h.of_eq (fun t => ?_)
  induction t with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    show w.step (Nat.rec (motive := fun _ => w.S) w.init (fun _ IH => w.step IH) n) =
      w.step (w.step^[n] w.init)
    rw [ih]

/-- Every discrete world's transcript is computable. -/
theorem World.transcript_computable_of_discrete {w : World} (hw : DiscreteWorld w) :
    Computable w.transcriptFn := by
  obtain ⟨hp, hstep, hread⟩ := hw
  exact hread.comp (World.iterate_computable hstep)

/-- **Lemma 2.1 (transcript characterisation of `D`).** -/
theorem transcript_characterisation (f : ℕ → ℕ) : f ∈ D ↔ Computable f := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact World.transcript_computable_of_discrete hw
  · intro hf
    refine ⟨⟨ℕ, 0, Nat.succ, f⟩, ⟨inferInstance, Computable.succ, hf⟩, ?_⟩
    funext t
    show f (Nat.succ^[t] 0) = f t
    congr 1
    induction t with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply', ih]

end Substrate
