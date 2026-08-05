# Status

Last updated: 2026-08-05.

## Summary

**`adoCharZero` is proved, independently verified, and submitted.**

Ado's theorem in characteristic zero — every finite-dimensional Lie algebra over
a field of characteristic zero admits a faithful finite-dimensional
representation — is fully formalized in
[`generated/adoCharZero/Submission/`](../../generated/adoCharZero/Submission),
40 files and ~7 000 lines, with no `sorry`, no added axiom, no `set_option` and
no `native_decide`.

`adoIwasawa` (the same statement over an arbitrary field) is **not** proved; its
`Submission.lean` still carries the benchmark `sorry`. It shares every file with
`adoCharZero` except `Main.lean` and needs §7 of
[`ado-informal.md`](ado-informal.md) on top: the full Poincaré–Birkhoff–Witt
theorem (including the linear-independence half, which the characteristic-zero
route deliberately avoids), restricted Lie algebras, the restricted PBW theorem
and the finite-dimensional `p`-envelope.

## Independent verification (2026-08-05)

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
| `#print axioms Submission.Ado.exists_levi_subalgebra'` | `[propext, Classical.choice, Quot.sound]` |
| `sorry` / `admit` / `axiom` / `set_option` / `native_decide` in the submission tree | none |
| `Challenge.lean`, `ChallengeDeps.lean`, `Solution.lean` | byte-identical to `leanprover/lean-eval@cd57190` |

`config.json` permits exactly `propext`, `Quot.sound`, `Classical.choice`, so
the axiom footprint is inside the allowance.

## Submission — accepted

* Issue [leanprover/lean-eval-submissions#945](https://github.com/leanprover/lean-eval-submissions/issues/945),
  filed 2026-08-05, pointing at commit `00c64353` of this repository.
  **Comparator verdict: `adoCharZero`: pass.** Recorded in
  `results/vilin97.json` under model `Opus-5`, and live on
  <https://lean-lang.org/eval/>: the `adoCharZero` row of the coverage matrix
  has exactly one solved cell out of 54, and the model page reads *"Problems
  uniquely solved by this model: Ado's theorem in characteristic zero"*.
  (`adoIwasawa` was attempted in the same run and correctly failed — its
  `Submission.lean` still carries the benchmark `sorry`.)
* Issue #944 was the same submission filed through the API; the API silently
  drops the `submission` label for non-collaborators, so the evaluation
  workflow never fired. It was closed and re-filed through the issue template.

## Mathlib gaps filled

All of the following were absent from Mathlib and from Mathlib master, and a
scout found no Lean 4 implementation anywhere (Lean Pool, Tau Ceti, Formal
Conjectures, GitHub code search). Mathlib's own `docs/1000.yaml` records Ado's
theorem and PBW as unformalized.

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
(`Submission/Ado/Port/`) are a mechanical port of
<https://github.com/Komyyy/ado> by Miyahara Kō, Apache 2.0. Attribution is
carried in the header of every ported file.

## Why PBW is not needed in characteristic zero

`Ado/PBW/Basis.lean` records the discovery that closed the project: the
linear-independence half of PBW is unnecessary. The port replaces the PBW basis
by an explicit filtration of the tensor algebra, so only the spanning half —
available here as `Submission.Ado.iSup_gen_pow_eq_top` — is used, and
faithfulness comes from the induction hypothesis instead of injectivity of `ι`.

The same file records that the originally planned lemma

```lean
theorem ι_notMem_genPow_two {x : L} (h : ι K x ∈ gen K L ^ 2) : x = 0
```

is **false** for every non-abelian `L`, since `ι ⁅x, y⁆ = ι x * ι y - ι y * ι x`
already lies in `gen K L ^ 2`. The counterexample is recorded as
`Submission.Ado.ι_lie_mem_genPow_two`.

## Findings worth reporting upstream

* Five benchmark problems cannot be solved as generated, because their
  `ChallengeDeps.lean` contains `sorry` and so any proof of the statement
  depends on `sorryAx`, which no `config.json` permits: `hadwiger`
  (the `Submodule` proof fields of `valuations` are `sorry`),
  `conway_knot_not_smoothly_slice`, `conway_knot_topologically_slice`,
  `exists_topologically_slice_not_smoothly_slice` and
  `derived_solidification_free_CW_homology`.
* `LeanEval/KnotTheory/Quadrisecant.lean` and `LeanEval/Geometry/FaryMilnor.lean`
  write `ContDiff ℝ ⊤ r`, not `ContDiff ℝ (⊤ : ℕ∞) r`. Since Mathlib's
  smoothness exponent has type `WithTop ℕ∞`, the bare `⊤` is `ω`, so both files
  quantify over *real-analytic* knots and analytic isotopies, not smooth ones.
  Every other knot file in the repository (`KnotTheory/Prelude.lean`,
  `KnotTheory/PardonDistortion.lean`) writes the ascribed `(⊤ : ℕ∞)`, so this
  looks unintended.
* `conway_knot_not_smoothly_slice` is exposed to a vacuity attack that its
  sibling `exists_topologically_slice_not_smoothly_slice` is protected against.
  `PLKnot` does not bundle simplicity, and no smooth knot's image can be
  ambient-homeomorphic to a self-intersecting polyline, so if the 78-vertex
  `braidClosure 4 conwayBraidWord` layout has a coordinate bug making it
  self-intersecting, `¬ conwayKnot.SmoothlySlice` is provable in an afternoon
  without any of Piccirillo's theorem. The companion hole `conwayKnot_isSimple`
  belongs to a *different* manifest problem, so it does not clamp this one.

## Next steps

1. Confirm #945 is accepted and that `adoCharZero` appears in
   `results/vilin97.json` and on <https://lean-lang.org/eval/>.
2. `adoIwasawa`, in dependency order: full PBW (§1 of `ado-informal.md`) →
   restricted Lie algebras and `u(𝔤)` → restricted PBW (Thm 7.3) →
   finite-dimensional `p`-envelope (Lem 7.4) → Thm 7.5. Characteristic `p` needs
   no structure theory at all, so §7 is short *given PBW*; PBW's
   linear-independence half is the whole cost.

## Build setup

Each workspace needs Mathlib. Rather than clone a second copy, hard-link the
prebuilt packages of a warmed-up workspace:

```bash
mkdir -p generated/<id>/.lake
cp -al <warm-workspace>/.lake/packages generated/<id>/.lake/packages
cd generated/<id> && lake update && lake build
```

Both `.lake` and `lake-manifest.json` are gitignored, so this does not travel
with the repository; redo it after a fresh clone. Peak RSS stays under 7 GB.

## Checkpointing

`leanprover/lean-eval` is not writable by this account
(`Permission to leanprover/lean-eval.git denied to Vilin97`), so checkpoints go
to `Vilin97/lean-eval-ado`, matching the existing per-problem naming
(`lean-eval-green-tao`, `lean-eval-furstenberg-measure`, …).
