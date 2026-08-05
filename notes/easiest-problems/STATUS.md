# Status

Last updated: 2026-08-05.

## Summary

**`adoCharZero` is proved, independently verified, submitted, accepted, and live on the
leaderboard.** Ado's theorem in characteristic zero — every finite-dimensional Lie
algebra over a field of characteristic zero admits a faithful finite-dimensional
representation — is fully formalized in
[`generated/adoCharZero/Submission/`](../../generated/adoCharZero/Submission),
40 files and ~7 000 lines, with no `sorry`, no added axiom, no `set_option` and
no `native_decide`.

**`adoIwasawa` is also proved** — the same statement over an *arbitrary* field,
which strictly subsumes `adoCharZero`. `Submission.lean` no longer carries the
benchmark `sorry`. Getting there required building **the Poincaré–Birkhoff–Witt
theorem**, which had never been formalized in Lean 4. See "The Iwasawa track"
below.

### `adoIwasawa` — verification

Rebuilt from a pristine clone of this repository:

| check | result |
| --- | --- |
| `lake build` | **succeeds**, 8 716 jobs |
| peak RSS | **6.82 GB** |
| warnings | exactly one: the trusted `Challenge.lean:9:8` `sorry` |
| `#print axioms adoIwasawa` | `[propext, Classical.choice, Quot.sound]` |
| `#print axioms Submission.adoIwasawa` | `[propext, Classical.choice, Quot.sound]` |
| `sorry` / `admit` / `axiom` / `set_option` / `native_decide` in the submission tree | none |
| `Challenge.lean`, `ChallengeDeps.lean`, `Solution.lean`, `config.json` | byte-identical to the upstream benchmark |
| size | 59 files, ~11 000 lines |

## `adoCharZero` — independent verification (2026-08-05)

Rebuilt from scratch in a clean workspace against the pinned toolchain
(`leanprover/lean4:v4.32.2`) and the pinned Mathlib
(`905b95818eb32af7874a58b427f50c1711a5e96c`):

| check | result |
| --- | --- |
| `lake build` | **succeeds**, 8 701 jobs, 61 s wall |
| peak RSS | **6.83 GB** |
| warnings | exactly one: `Challenge.lean:9:8: declaration uses 'sorry'` — the *trusted* benchmark statement, which is supposed to be a `sorry`. No warning anywhere in `Submission.lean` or `Submission/`. |
| `#print axioms Submission.adoCharZero` | `[propext, Classical.choice, Quot.sound]` |
| `#print axioms adoCharZero` (from `Solution.lean`) | `[propext, Classical.choice, Quot.sound]` |
| `sorry` / `admit` / `axiom` / `set_option` / `native_decide` in the submission tree | none |
| `Challenge.lean`, `ChallengeDeps.lean`, `Solution.lean` | byte-identical to `leanprover/lean-eval@cd57190` |

## Submission — accepted

* Issue [leanprover/lean-eval-submissions#945](https://github.com/leanprover/lean-eval-submissions/issues/945),
  filed 2026-08-05, pointing at commit `00c64353` of this repository.
  **Comparator verdict: `adoCharZero`: pass.** Recorded in `results/vilin97.json`
  under model `Opus-5`, and live on <https://lean-lang.org/eval/>: the
  `adoCharZero` row of the coverage matrix has exactly one solved cell out of 54,
  and the model page reads *"Problems uniquely solved by this model: Ado's theorem
  in characteristic zero"*.
* Issue #944 was the same submission filed through the API; the API silently drops
  the `submission` label for non-collaborators, so the evaluation workflow never
  fired. It was closed and re-filed through the issue template.

## Mathlib gaps filled — characteristic zero

All of the following were absent from Mathlib and from Mathlib master, and a scout
found no Lean 4 implementation anywhere (Lean Pool, Tau Ceti, Formal Conjectures,
GitHub code search). Mathlib's own `docs/1000.yaml` records Ado's theorem and PBW
as unformalized.

| ingredient | file | notes |
| --- | --- | --- |
| classical Lie nilradical | `Ado/Nilradical.lean` | Mathlib's `maxNilpotentIdeal` is the *module*-nilpotent notion and evaluates to `⊥` on the two-dimensional non-abelian algebra |
| `⁅L, L⁆ ⊓ rad L` is nilpotent | `Ado/DerivedRadical.lean` | via Lie's theorem plus Engel |
| Casimir element | `Ado/Casimir.lean` | built on the Killing complement of the trace-form radical, since the trace form is degenerate in general; needs a module form of Cartan's criterion, proved here as `lie_eq_zero_of_traceForm_eq_zero` |
| Weyl complete reducibility | `Ado/Weyl.lean` | via the Fitting decomposition `M = ker cᵏ ⊕ im cᵏ`, avoiding Schur's lemma and quotient modules |
| Whitehead's first lemma | `Ado/Levi.lean` | |
| **Levi decomposition** | `Ado/Levi.lean` (`exists_levi_subalgebra'`) | |
| extension of a Lie derivation to `U(L)` | `Ado/EnvDeriv.lean` | via the trivial square-zero extension |
| degree filtration on `U(L)`, `U(L)/J^k` finite-dimensional | `Ado/Filtration.lean`, `Ado/Truncation.lean` | the *spanning* half of PBW; the basis theorem is never needed |
| the solvable case | `Ado/Solvable.lean` | |

Prior work reused, with attribution: the abelian and nilpotent cases
(`Submission/Ado/Port/`) are a mechanical port of <https://github.com/Komyyy/ado>
by Miyahara Kō, Apache 2.0. Attribution is carried in the header of every ported
file.

## The Iwasawa track — the Poincaré–Birkhoff–Witt theorem

Characteristic `p` cannot use Levi's theorem. The textbook route (Strade–Farnsteiner)
goes through restricted Lie algebras, the restricted enveloping algebra and
restricted PBW; a scout confirmed that **neither PBW nor restricted Lie algebras
exist in Lean 4 anywhere** — not in Mathlib, not in any Mathlib PR (the only
PBW-titled PR, #36936, is categorical PBW for monads and is a four-`sorry` draft),
not in `Komyyy/ado` (characteristic zero by design, and it deliberately avoids PBW),
not in Lean Pool or Tau Ceti, and not in GitHub code search.

So PBW is being built here. Everything below is **sorry-free, zero-warning, and
depends only on `[propext, Classical.choice, Quot.sound]`**:

| module | lines | contents |
| --- | --- | --- |
| `PBW/Defs.lean` | 109 | the polynomial module `Poly K n`, the alignment relation, and Humphreys' recursion, made structural by a fuel parameter |
| `PBW/Props.lean` | 255 | fuel-irrelevance, **(A)** `act_of_aligned`, **(B)** `act_sub_mono_degLE`, and the `DegLE` calculus |
| `PBW/Action.lean` | 144 | truncation lemmas and **the aligned case of the Lie relation**, which is true by construction |
| `PBW/Module.lean` | 317 | **the Lie relation (C) in general** — `Poly K n` is a Lie module over `L` |
| `PBW/Env.lean` | 94 | `U(L)` acts on `Poly K n`; the evaluation map `u ↦ u • z⁰` |
| `PBW/Injective.lean` | 72 | **`ι : L → U(L)` is injective** for every finite-dimensional Lie algebra over a field |
| `PBW/Unitriangular.lean` | 134 | unitriangular families are linearly independent, and span |
| `PBW/Sorting.lean` | 282 | the spanning half of PBW: ordered monomials span `U(L)` |
| `PBW/Basis2.lean` | 379 | **the Poincaré–Birkhoff–Witt theorem**: `pbwBasis bas : Module.Basis (Mon n) K (U(L))`, the ordered monomials `∏ᵢ ι(xᵢ)^{aᵢ}` |
| `PBW/Pow.lean` | 424 | triangularity of `ρ(xⱼ)^k` and of the operators `Cⱼ` by which the central `p`-polynomials act |
| `PBW/DivMod.lean` | 176 | the bijection `Mon n ≃ {b : ∀ j, bⱼ < q} × Mon n` by division with remainder |
| `CharP/FiniteQuotient.lean` | 474 | `U(L)` modulo a two-sided ideal containing the `p`-polynomial relations is **finite-dimensional** (needs only the spanning half of PBW) |
| `CharP/Dispatch.lean` | 33 | reduces Ado–Iwasawa to the positive-characteristic case |
| `CharP/AdPow.lean` | 128 | `ad(a)^{pⁱ} = ad(a^{pⁱ})` in characteristic `p` |
| `CharP/Central.lean` | 304 | `p`-polynomial relations for endomorphisms, and the resulting **central elements of `U(L)`** |

### The one thing that had to be got right

Humphreys' recursion is

```
ρ(xᵢ) z^a = zᵢ z^a                                  if i ≼ a
ρ(xᵢ) z^a = ρ(xⱼ)(ρ(xᵢ) z^b) + ρ(⁅xᵢ, xⱼ⁆) z^b      otherwise
```

and the second branch must apply **`ρ(xⱼ)`**, not multiplication by `zⱼ`. With the
wrong version the hard case of (C) does not close — and the statement is in fact
false; a machine check found 20 violations at degree `≤ 3` on the three-dimensional
solvable algebra `⁅x₁,x₂⁆ = x₁`, `⁅x₂,x₃⁆ = x₁`. With the right version, the case
`j ≼ a`, `i > j` is true *term by term, by definition, in every degree*, which is
`lie_rel_aligned`. See [`pbw-proof.md`](pbw-proof.md) §6.5 for the counterexample
and §6.2–6.4 for the closing argument.

A second trap, recorded in `pbw-proof.md` §9.2: the Jacobi step must use the
**cyclic** identity (`lie_jacobi`). Expanding with `lie_lie` twice only proves
`2 • goal = 0`, which is worthless in characteristic 2.

### How `adoIwasawa` was closed

The route was shortened once the PBW module was in hand; see the final section of
[`iwasawa-blueprint.md`](iwasawa-blueprint.md). Nothing about `U(L)` beyond the
module is needed — no freeness over `K[c₁,…,cₙ]`, no finite-dimensional quotient
of `U(L)`. Working entirely inside `Poly K n`:

1. `PBW/Pow.lean` — triangularity of `ρ(xⱼ)^k`, and of the operators `Cⱼ` by which
   the central `p`-polynomials act: `C^m (z^b) = z^(b+q·m) + lower`;
2. `PBW/PowComm.lean` — word products of the `Cⱼ` are order-independent, because
   the underlying `cⱼ` are central; hence `Cⱼ ∘ C^m = C^(m+eⱼ)`;
3. `PBW/DivMod.lean` — the bijection `Mon n ≃ {b : ∀ j, bⱼ < q} × Mon n` given by
   division with remainder;
4. `PBW/Restricted.lean` — the resulting unitriangular basis of `Poly K n`, and the
   **separation lemma**: a `K`-combination of `z₁, …, zₙ` lying in `∑ⱼ range Cⱼ` is
   zero;
5. `CharP/FiniteRep.lean` — `Q := Poly K n / ∑ⱼ range Cⱼ` is finite-dimensional
   (spanned by the finitely many restricted monomials), `L` acts on it because the
   `Cⱼ` commute with the action, and the action is faithful by the separation
   lemma applied to `ρ(x)(z⁰) = ∑ᵢ (repr x)ᵢ zᵢ`. Together with
   `CharP/Dispatch.lean` this gives `hasFaithfulFinRep_any`, which discharges the
   benchmark hole.

## Findings worth reporting upstream to `leanprover/lean-eval`

* Five benchmark problems cannot be solved as generated, because their
  `ChallengeDeps.lean` contains `sorry` and so any proof of the statement depends
  on `sorryAx`, which no `config.json` permits: `hadwiger` (the `Submodule` proof
  fields of `valuations` are `sorry`), `conway_knot_not_smoothly_slice`,
  `conway_knot_topologically_slice`,
  `exists_topologically_slice_not_smoothly_slice` and
  `derived_solidification_free_CW_homology`.
* `LeanEval/KnotTheory/Quadrisecant.lean` and `LeanEval/Geometry/FaryMilnor.lean`
  write `ContDiff ℝ ⊤ r`, not `ContDiff ℝ (⊤ : ℕ∞) r`. Since Mathlib's smoothness
  exponent has type `WithTop ℕ∞`, the bare `⊤` is `ω`, so both files quantify over
  *real-analytic* knots and analytic isotopies, not smooth ones. Every other knot
  file in the repository (`KnotTheory/Prelude.lean`,
  `KnotTheory/PardonDistortion.lean`) writes the ascribed `(⊤ : ℕ∞)`, so this looks
  unintended. Machine-verified in
  [`contdiff-top-is-analytic.lean`](contdiff-top-is-analytic.lean): Mathlib's
  `Mathlib/Analysis/Calculus/ContDiff/FTaylorSeries.lean:118` defines
  `notation3 "ω" => (⊤ : WithTop ℕ∞)`, so `(⊤ : ℕ∞ω) = ω` by `rfl`,
  `ContDiff ℝ ⊤ f ↔ ContDiff ℝ ω f` by `Iff.rfl`,
  `((⊤ : ℕ∞) : ℕ∞ω) ≠ (⊤ : ℕ∞ω)` by `decide`, and `ContDiff ℝ ⊤ f → AnalyticOnNhd ℝ f univ`.
* `conway_knot_not_smoothly_slice` is exposed to a vacuity attack that its sibling
  `exists_topologically_slice_not_smoothly_slice` is protected against. `PLKnot`
  does not bundle simplicity, and no smooth knot's image can be
  ambient-homeomorphic to a self-intersecting polyline, so if the 78-vertex
  `braidClosure 4 conwayBraidWord` layout has a coordinate bug making it
  self-intersecting, `¬ conwayKnot.SmoothlySlice` is provable in an afternoon
  without any of Piccirillo's theorem. The companion hole `conwayKnot_isSimple`
  belongs to a *different* manifest problem, so it does not clamp this one.

## Build setup

Each workspace needs Mathlib. Rather than clone a second copy, hard-link the
prebuilt packages of a warmed-up workspace:

```bash
mkdir -p generated/<id>/.lake
cp -al <warm-workspace>/.lake/packages generated/<id>/.lake/packages
cd generated/<id> && lake update && lake build
```

Both `.lake` and `lake-manifest.json` are gitignored, so this does not travel with
the repository; redo it after a fresh clone. Peak RSS stays under 7 GB.

## Checkpointing

`leanprover/lean-eval` is not writable by this account
(`Permission to leanprover/lean-eval.git denied to Vilin97`), so checkpoints go to
`Vilin97/lean-eval-ado`, matching the existing per-problem naming
(`lean-eval-green-tao`, `lean-eval-furstenberg-measure`, …).
