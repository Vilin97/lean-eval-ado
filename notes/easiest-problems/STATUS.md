# Status

Last updated: 2026-08-04.

## Honest summary

**None of the three targets is solved, and none is close.** What exists is the
survey that selected them, complete informal proofs, dependency-ordered Lean
blueprints, and the first two compiling Lean files of the Ado development
(≈250 lines out of an estimated 8 000–10 500).

The estimate that matters: `adoCharZero` needs the Poincaré–Birkhoff–Witt
theorem, the Casimir element, Weyl's complete reducibility theorem, Whitehead's
first lemma, and the Levi decomposition. Mathlib has **none** of these — I
checked each by reading the source; `Mathlib/Algebra/Lie/Free.lean:36` and
`Mathlib/Algebra/Lie/SerreConstruction.lean:46` both explicitly record that PBW
is missing, and `Mathlib/Algebra/Lie/Cochain.lean` carries a
`TODO: coboundaries, cohomology`. That is a multi-month project, not a
single-session one. The same is true of the other 59 unsolved problems; see
[`SURVEY.md`](SURVEY.md) for the triage.

## What is verified

| file | lines | contents | build |
| --- | --- | --- | --- |
| `generated/adoCharZero/Submission/Ado/Basic.lean` | 105 | §0 reductions: `HasFaithfulFinRep`, direct sums of representations, `ad` kills exactly the centre, and the reduction of Ado to "faithful on the centre" | clean, no warnings |
| `generated/adoCharZero/Submission/Ado/DerivRep.lean` | 146 | §4 engine: `IsDeriv`, `⁅D, mulLeft a⁆ = mulLeft (D a)`, `⁅mulLeft a, mulLeft b⁆ = mulLeft (a*b - b*a)`, the combined representation `x ↦ mulLeft (f x) + D x` with its exact Lie-morphism criterion, and its kernel criterion | clean, no warnings |
| `generated/adoCharZero/Submission/Ado/Easy.lean` | 70 | **Ado's theorem proved in two complete special cases**: trivial centre (`ad` is faithful) and abelian (explicit `(dim L + 1)`-dimensional representation on `K × L`). Both hold over any field. | clean, no warnings |
| `generated/adoCharZero/Submission/Ado/Embed.lean` | 86 | Ado's property for `L` **iff** `L` embeds into a finite-dimensional associative `K`-algebra with brackets going to ring commutators. This is the bridge both constructive halves cross at the end (§3 with `U(N)/J(N)^k`, §7 with `u(𝔤̂)`). | clean, no warnings |
| `generated/adoCharZero/Submission/Ado/Closure.lean` | 63 | Ado's property is inherited along injective Lie morphisms (so passes to subalgebras — the §7 descent from the `p`-envelope) and is stable under products; plus **Ado for Lie algebras with trivial radical**, in particular semisimple ones. | clean, no warnings |

| `generated/adoCharZero/Submission/Ado/Filtration.lean` | 129 | The degree filtration on `U(L)`: `ι '' L` generates `U(L)` as an algebra (`adjoin_range_ι_eq_top`, by the retraction argument through the universal property), `⨆ j, gen ^ j = ⊤`, and each `gen ^ j` is finite-dimensional. **This is the spanning half of PBW, and it does not need the basis theorem.** | clean, no warnings |

| `generated/adoCharZero/Submission/Ado/Truncation.lean` | 82 | **`U(L) ⧸ J(L)^k` is finite-dimensional.** `filt k ⊔ augPow k = ⊤` splits `U(L)` into low degree and degree `≥ k`, and the quotient is the image of the finite-dimensional `filt k`. This is one of the two ingredients of Birkhoff's embedding theorem, and it needs no PBW basis theorem. | clean, no warnings |

All seven files are mirrored into `generated/adoIwasawa/Submission/Ado/`. Total
679 lines.

Birkhoff's theorem (§3) is now down to a single missing input: `N ∩ J(N)^k = ⊥`
for `k ≥ 2`, i.e. the *injectivity* half of PBW. Everything else it needs is
proved.

`#print axioms` on every proved declaration gives exactly
`[propext, Classical.choice, Quot.sound]` — no `sorryAx`, so these results
would pass comparator's axiom check as they stand.

`lake build Submission` in both `generated/adoCharZero` and
`generated/adoIwasawa` succeeds with exactly one warning, the intended `sorry`
on the benchmark theorem itself. No `set_option`, no `native_decide`, no added
axioms.

`lieHomOfMulLeftAddDeriv` is worth singling out: it isolates, as a single
verified criterion, the precise obstruction that makes Ado's theorem hard. A
representation `x ↦ mulLeft (f x) + D x` is a Lie morphism iff `D` is a Lie
morphism **and**

```
f ⁅x, y⁆ = f x * f y - f y * f x + D x (f y) - D y (f x).
```

Taking `f` to be the inclusion of a vector-space complement and `D = ad`, that
second condition holds automatically on `𝔞 × 𝔞` and on `𝔞 × 𝔪` but fails on
`𝔪 × 𝔪` unless `𝔪` is a subalgebra — which is exactly why the proof has to
proceed one dimension at a time (§5) or along a Levi complement (§6), and why
Levi's theorem cannot be dodged.

## Build setup

The worktree has no `.lake`. Rather than clone a second Mathlib (only ~18 GB of
disk free), each workspace symlinks the prebuilt one:

```bash
ln -sfn /Users/vasil/Github/lean-eval/.lake/packages generated/<id>/.lake/packages
cp /Users/vasil/Github/lean-eval/lake-manifest.json generated/<id>/
```

Both are gitignored, so this does not travel with the repo; redo it after a
fresh clone. Peak RSS during builds stays under 3 GB.

## Checkpointing

`leanprover/lean-eval` is not writable by this account
(`Permission to leanprover/lean-eval.git denied to Vilin97`), so checkpoints go
to the private repo `Vilin97/lean-eval-ado`, matching the existing per-problem
naming (`lean-eval-green-tao`, `lean-eval-szemeredi`, …). Delete it if it is not
wanted.

## Next steps, in dependency order

1. `Submission/Ado/PBW/SymAction.lean` — the action of `L` on `MvPolynomial (Fin n) K`
   defined by well-founded recursion on `(word length, index)`. This is the
   single highest-risk file in the project and blocks §3, §4 and §7.
2. `Submission/Ado/PBW/{Basis,Corollaries}.lean` — spanning by bubble-sort
   induction on inversions, independence by triangularity, then `ι` injective,
   `L ∩ J² = ⊥`, and `finrank (U/Jᵐ)`.
3. `Submission/Ado/Restricted/` — given PBW this finishes the **characteristic-`p`
   half of `adoIwasawa`** with no structure theory at all, and is the only
   complete result reachable early.
4. The characteristic-zero chain: nilradical → `[L,L] ∩ rad` nilpotent →
   Birkhoff → the extension step → solvable → Casimir/Weyl/Whitehead/Levi.

Two things worth reporting upstream to `leanprover/lean-eval` independently of
this work:

* `hadwiger` cannot be solved as generated — `valuations`' `Submodule` proof
  fields are `sorry` in `ChallengeDeps.lean`, so any proof of the statement
  depends on `sorryAx`, which `config.json` does not permit. The same `sorry`
  taint is in `conway_knot_not_smoothly_slice`,
  `conway_knot_topologically_slice`,
  `exists_topologically_slice_not_smoothly_slice` and
  `derived_solidification_free_CW_homology`.
* Nothing has been submitted to the leaderboard, because there is nothing
  submittable: a submission is scored only if comparator accepts it, and a
  `sorry` in `Submission.lean` is rejected outright.
