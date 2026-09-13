import Substrate.Basic
import Substrate.Prefix

/-!
# Substrate.Embed

**Lemma 2.2 (Embedding):** every discrete world has a continuum world with the same
transcript; hence `D ⊆ C`.

`Prefix.lean` already establishes the stronger fact `mem_C : ∀ f, f ∈ C` (every
transcript whatsoever is continuum-realizable, since `ContinuumWorld` is classical
`ℝ` with unrestricted dynamics — see spec §2.2 modeling note). Lemma 2.2 is the
immediate specialisation to transcripts that happen to be discrete. The classical,
non-effective step is `Prefix.nonempty_equiv_finOne_real` (`Cardinal.eq`).

Status: A_Lean (`EPIC_001_SUD_PART_I`).
-/

namespace Substrate

/-- **Lemma 2.2.**  Every discrete transcript is also a continuum transcript. -/
theorem discrete_subset_continuum : D ⊆ C := fun f _ => mem_C f

end Substrate
