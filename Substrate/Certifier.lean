import Substrate.Basic
import Substrate.Prefix

/-!
# Substrate.Certifier

**Theorem 3:** no sound internal certifier fires for either substrate class.

(a) If `T` is sound for continuum (`run T f = true → f ∈ Cstrict`) then it never returns
`true` on any transcript.
(b) If `T` is sound for discreteness (`run T f = true → f ∈ D`) then it never returns
`true` on any transcript.

Both follow from Theorem 1: whatever prefix `T` looks at, both a `D`-witness and a
`Cstrict`-witness agree with it, so `T`'s verdict on that prefix cannot be sound for
either class without also firing (wrongly) on the other class's witness.

Status: A_Lean (`EPIC_001_SUD_PART_I`).
-/

namespace Substrate

/-- A test is *sound for continuum* if a positive verdict implies the transcript is
in the strict-continuum class. -/
def SoundForContinuum (T : InternalTest) : Prop :=
  ∀ f, T.run f = true → f ∈ Cstrict

/-- A test is *sound for discreteness* if a positive verdict implies the transcript
is in the discrete class. -/
def SoundForDiscreteness (T : InternalTest) : Prop :=
  ∀ f, T.run f = true → f ∈ D

theorem Prefix_length (f : ℕ → ℕ) (n : ℕ) : (Prefix f n).length = n := by
  simp [Prefix]

/-- **Theorem 3(a).**  A continuum-sound certifier never fires. -/
theorem sound_for_continuum_never_fires {T : InternalTest} (hsound : SoundForContinuum T) :
    ∀ f, T.run f ≠ true := by
  intro f₀ hf₀
  obtain ⟨d, hdD, hpd, c, hcC, hpc⟩ := prefix_indistinguishable (Prefix f₀ T.budget)
  have hpd' : Prefix d T.budget = Prefix f₀ T.budget := by
    rw [Prefix_length] at hpd; exact hpd
  have hrun_d : T.run d = true := by
    show T.verdict (Prefix d T.budget) = true
    rw [hpd']; exact hf₀
  exact Set.disjoint_left.mp D_disjoint_Cstrict hdD (hsound d hrun_d)

/-- **Theorem 3(b).**  A discreteness-sound certifier never fires. -/
theorem sound_for_discreteness_never_fires {T : InternalTest} (hsound : SoundForDiscreteness T) :
    ∀ f, T.run f ≠ true := by
  intro f₀ hf₀
  obtain ⟨d, hdD, hpd, c, hcC, hpc⟩ := prefix_indistinguishable (Prefix f₀ T.budget)
  have hpc' : Prefix c T.budget = Prefix f₀ T.budget := by
    rw [Prefix_length] at hpc; exact hpc
  have hrun_c : T.run c = true := by
    show T.verdict (Prefix c T.budget) = true
    rw [hpc']; exact hf₀
  exact Set.disjoint_left.mp D_disjoint_Cstrict (hsound c hrun_c) hcC

/-- **Theorem 3 (combined).**  A certifier of either substrate class is either
unsound or silent (never returns `true`). -/
theorem certifier_silent_or_unsound (T : InternalTest) :
    (SoundForContinuum T → ∀ f, T.run f ≠ true) ∧
    (SoundForDiscreteness T → ∀ f, T.run f ≠ true) :=
  ⟨sound_for_continuum_never_fires, sound_for_discreteness_never_fires⟩

end Substrate
