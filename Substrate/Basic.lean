import Mathlib

/-!
# Substrate.Basic

Worlds, observer transcripts, internal tests, and substrate transcript classes.

The observer channel is finite-alphabet (`read : S → ℕ`); all downstream
statements are about `ℕ → ℕ` (Baire space).
-/

namespace Substrate

/-- A world: state, dynamics, and a finite-resolution observer readout. -/
structure World where
  S : Type
  init : S
  step : S → S
  read : S → ℕ

namespace World

/-- The observer transcript: the only data an internal observer ever sees. -/
def transcript (w : World) (t : ℕ) : ℕ :=
  w.read (Nat.iterate w.step t w.init)

/-- Transcript as a stream `ℕ → ℕ`. -/
def transcriptFn (w : World) : ℕ → ℕ :=
  w.transcript

end World

/-- First `n` values of a transcript. -/
def Prefix (f : ℕ → ℕ) (n : ℕ) : List ℕ :=
  (List.range n).map f

/-- A finite-resource internal test: computable verdict on transcript prefixes. -/
structure InternalTest where
  budget : ℕ
  verdict : List ℕ → Bool
  comp : Computable verdict

namespace InternalTest

def run (T : InternalTest) (f : ℕ → ℕ) : Bool :=
  T.verdict (Prefix f T.budget)

end InternalTest

/-- A transcript property is finitely determined if some prefix length settles it
(topologically: clopen in Baire space under the product topology). -/
def FinitelyDetermined (P : (ℕ → ℕ) → Prop) : Prop :=
  ∃ n, ∀ f g, Prefix f n = Prefix g n → (P f ↔ P g)

/-- Discrete substrate: primcodable state, computable dynamics and readout. -/
def DiscreteWorld (w : World) : Prop :=
  ∃ _ : Primcodable w.S, Computable w.step ∧ Computable w.read

/-- Continuum substrate: state embeds in a finite product of reals (classical v1). -/
def ContinuumWorld (w : World) : Prop :=
  ∃ n, Nonempty (w.S ≃ (Fin n → ℝ))

/-- Transcripts realizable by some discrete world. -/
def D : Set (ℕ → ℕ) :=
  {f | ∃ w, DiscreteWorld w ∧ w.transcriptFn = f}

/-- Transcripts realizable by some continuum world. -/
def C : Set (ℕ → ℕ) :=
  {f | ∃ w, ContinuumWorld w ∧ w.transcriptFn = f}

/-- Strict continuum: continuum transcript that is not computable. -/
def Cstrict : Set (ℕ → ℕ) :=
  C \ {f | Computable f}

end Substrate
