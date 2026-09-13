# Substrate Undecidability (Lean)

**Paper working title:** *Discrete or Continuous? Why No Internal Observer Can Decide, and What Can Adjudicate Instead*

**Series:** NEMS core suite — bridges to UGP via the MDL adjudication corollary.

Machine-check **Part I** (Theorems 1–4): internal observers cannot decide substrate discreteness from finite evidence or internal law-certification. **Part II** (Theorem 5): under PSC, substrate is an outsourced property; MDL is the unique admissible adjudicator (argument half cites P34/P84).

## Build

```bash
lake update
lake exe cache get   # optional, speeds first Mathlib build
lake build
```

**Toolchain:** Lean 4.29.1, Mathlib v4.29.1 (aligned with `nems-lean`).

**Policy:** zero `sorry`, zero custom axioms; `#print axioms` on all named theorems in CI.

## Axiom audit (2026-09-12)

All shipped named theorems depend only on standard Mathlib axioms: `propext`, `Classical.choice`, `Quot.sound`. Zero custom axioms.

Run: `lake env lean scripts/axiom_audit.lean`

| Theorem | Axioms |
|---------|--------|
| `transcript_characterisation` (Lemma 2.1) | propext, Classical.choice, Quot.sound |
| `discrete_subset_continuum` (Lemma 2.2) | propext, Classical.choice, Quot.sound |
| `exists_noncomputable_nat_fn` | propext, Classical.choice, Quot.sound |
| `prefix_indistinguishable` (Theorem 1) | propext, Classical.choice, Quot.sound |
| `substrate_not_finitely_determined` (Theorem 2) | propext, Classical.choice, Quot.sound |
| `certifier_silent_or_unsound` (Theorem 3) | propext, Classical.choice, Quot.sound |
| `law_match_undecidable` (Theorem 4) | propext, Classical.choice, Quot.sound |
| `law_match_undecidable_zero` (Corollary 4.1) | propext, Classical.choice, Quot.sound |
| `substrate_not_internally_decidable` (Theorem 5 Lean half) | propext, Classical.choice, Quot.sound |
| `discrete_not_internally_decidable` | propext, Classical.choice, Quot.sound |
| `D_countable` / `Cstrict_not_countable` | propext, Classical.choice, Quot.sound |
| `no_joint_substrate_decision` (Thm 5 cardinality strengthening) | propext, Classical.choice, Quot.sound |
| `acceptance_on_D_iff_Cstrict` (deterministic class advantage — **closed**) | propext, Classical.choice, Quot.sound |
| `D_null_geometric` / `Cstrict_full_mass_geometric` (substrate-class mass) | propext, Classical.choice, Quot.sound |
| `prob_accept_above_on_D_iff_Cstrict` (notational restatement — **not** ε-tolerant closure) | propext, Classical.choice, Quot.sound |
| `acceptance_mass_meets_both_classes` (global mass only, not class-conditional) | propext, Classical.choice, Quot.sound |
| `axisA_not_finitely_determined` (Axis A / eventually periodic) | propext, Classical.choice, Quot.sound |
| `Dfin_iff_eventuallyPeriodic` | propext, Classical.choice, Quot.sound |
| `glimmer_not_computable` (Theorem 5 / glimmer barrier) | propext, Classical.choice, Quot.sound |
| `computable_not_random` | propext, Classical.choice, Quot.sound |
| `bet_succeeds` | propext, Classical.choice, Quot.sound |
| `glimmer_finite_description` (limit-computable `f` has a single `Code` computing its approximant) | propext, Classical.choice, Quot.sound |
| `limitComputable_not_finitely_determined` | propext, Classical.choice, Quot.sound |
| `not_tot_iff` / `matchFnTot_eq_f_iff` (Π⁰₂ totality characterization) | propext, Classical.choice, Quot.sound |
| `law_match_pi2_hard` (Π⁰₂-hardness: `Tot ≤₀ₘ LawMatches f` — **closed**) | propext, Classical.choice, Quot.sound |
| `law_match_pi2_hard_zero` (observer instance) | propext, Classical.choice, Quot.sound |
| `seqMaster_partrec` / `part_map_const_eq_some_iff` (reduction support) | propext, Classical.choice, Quot.sound |

## Module map

| Module | Target |
|--------|--------|
| `Substrate/Basic.lean` | `World`, transcript, `D` / `C` / `Cstrict` |
| `Substrate/Discrete.lean` | Lemma 2.1 |
| `Substrate/Embed.lean` | Lemma 2.2 |
| `Substrate/Noncomputable.lean` | ∃ non-computable transcript |
| `Substrate/Prefix.lean` | Theorem 1 |
| `Substrate/NotFinDet.lean` | Theorem 2 |
| `Substrate/Certifier.lean` | Theorem 3 |
| `Substrate/LawBarrier.lean` | Theorem 4 (halting reduction via `evaln`); Theorem 4′ Π⁰₂-hardness (`Tot ≤₀ₘ LawMatches f`, sequential-composition reduction) |
| `Substrate/Outsourced.lean` | Theorem 5 (Lean half) |
| `Substrate/Cardinality.lean` | Thm 5 cardinality / joint-observer strengthening |
| `Substrate/Probabilistic.lean` | Deterministic class-advantage obstruction + Baire product measure infrastructure (§7 bullet 4 — partial; ε-tolerant open) |
| `Substrate/AxisA.lean` | Eventually periodic finite-state axis (Axis A) |
| `Substrate/Glimmer.lean` | Limit-computable / glimmer class + bet martingale barrier (Theorem 5) |

Build order: Basic → … → Outsourced → Cardinality → Probabilistic → AxisA → Glimmer.

## Paper

LaTeX source and bibliography: [`paper/Substrate_Undecidability.tex`](paper/Substrate_Undecidability.tex), [`paper/refs.bib`](paper/refs.bib) — compiled PDF at [`paper/Substrate_Undecidability.pdf`](paper/Substrate_Undecidability.pdf).

## Dependencies

- **Mathlib only** (v1)
- **Pattern reuse:** `nems-lean` halting reduction / `evaln` construction (`NemS.Diagonal.HaltingReduction`)

## License

See [`LICENSE`](LICENSE).
