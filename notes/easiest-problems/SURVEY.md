# lean-eval: survey of the unsolved problems, and the choice of three targets

Date of survey: 2026-08-04.
Benchmark commit: `6af65bb1abb997a3cfabf3236e43ab5085a51dac` (`chore: regenerate generated/ workspaces`).
Toolchain: `leanprover/lean4:v4.32.2`, Mathlib `905b95818eb32af7874a58b427f50c1711a5e96c`.

## 1. Method

1. Cloned `leanprover/lean-eval-submissions` and unioned the key sets of
   `solved` across every `results/<login>.json` (41 result files). That gives the
   set of problem ids that comparator has accepted from *anyone*.
2. Diffed that against `generated/index.json` (237 problems).
3. Read the `Challenge.lean` of every unsolved problem, and the corresponding
   `LeanEval/**` source module (the trusted definitions), looking for
   * statements that are strictly weaker than the headline theorem,
   * definitions that are degenerate/vacuous,
   * hypothesis sets that are contradictory (which would make the problem cheap),
   * `sorry` in trusted dependencies (which makes the problem *impossible*).
4. Checked Mathlib, [Lean Pool](https://github.com/Vilin97/lean-pool) and
   [Tau Ceti](https://github.com/TauCetiProject/TauCeti) for reusable
   infrastructure.

**Counts.** 237 total, 177 solved, **60 unsolved**.

## 2. The axiom budget rules some problems out entirely

Every generated workspace pins

```json
"permitted_axioms": ["propext", "Quot.sound", "Classical.choice"]
```

so a solution whose *statement* depends on `sorryAx` can never be accepted.
Five problems have `sorry` inside their trusted `ChallengeDeps.lean`:

| problem | where the `sorry` is |
| --- | --- |
| `hadwiger` | `valuations`' `add_mem'`, `zero_mem'`, `smul_mem'` |
| `conway_knot_not_smoothly_slice` | inherited from the knot prelude |
| `conway_knot_topologically_slice` | inherited from the knot prelude |
| `exists_topologically_slice_not_smoothly_slice` | inherited from the knot prelude |
| `derived_solidification_free_CW_homology` | trusted scaffolding |

`hadwiger` is the clearest case: `Module.finrank ℝ (valuations n)` mentions
`valuations n`, whose `Submodule` proof fields are `sorry`, so
`#print axioms hadwiger` will always list `sorryAx`. This is a benchmark bug
worth reporting upstream, not a solving strategy.

## 3. Loophole hunt: negative result

I specifically checked the statements where a formalisation gap would be most
likely. All of them are faithful:

* `pardon_torus_knot_distortion` — `distortion K ≥ 1` is free (intrinsic
  distance dominates chord length), which settles `min p q ≤ 160` trivially, but
  the statement quantifies over all coprime `p, q`, so Pardon's linear bound is
  still needed.
* `exists_topologically_slice_not_smoothly_slice` — `PLKnot` does not bundle
  simplicity, so degenerate polylines are allowed; but a degenerate polyline's
  image is not ambient-homeomorphic to any smooth knot's image, so
  `TopologicallySlice` fails for it. No cheap witness.
* `Knot.SmoothlySlice` uses the round disk `{p | p.1^2 + p.2^2 ≤ 1}`, not
  `Metric.closedBall` on `ℝ × ℝ` (which is a square) — the authors document
  exactly this trap. The predicate is satisfiable (the unknot bounds
  `(x,y) ↦ ((x,y,0), 1 - x² - y²)`).
* `sphere_theorem_*` — `QuarterPinched` is not contradictory: it is stable under
  `X ↦ -X`, `Y ↦ -Y` and under replacing an orthonormal pair by another
  orthonormal basis of the same 2-plane, exactly as sectional curvature must be.
* `poincare_3d_topological` — `Empty` is not a counterexample: Mathlib's
  `SimplyConnectedSpace` forces the fundamental groupoid to be equivalent to
  `Discrete Unit`, hence nonemptiness.
* `two_ninety_theorem` — the `n = 0` case is killed by `hrep` (the empty form
  represents only `0`), everything else is the real Bhargava–Hanke theorem.
* `bourgain_polynomial_ergodic` — `F` carries no measurability constraint, so
  the only content is a.e. convergence; that *is* Bourgain's theorem.
* `duffin_schaeffer` — the convergent direction is Borel–Cantelli, the divergent
  direction is Koukoulopoulos–Maynard.
* `martinet_totally_real_towers` — `C` may be arbitrary, but Odlyzko's bounds
  force any witness family to be asymptotically good, i.e. an infinite class
  field tower (Golod–Shafarevich).
* `linnik` — the constant may be ineffective, but even ineffective polynomial
  bounds on the least prime in a progression need log-free zero-density
  estimates.

## 4. The 60 unsolved problems

| id | title | module |
| --- | --- | --- |
| `adoCharZero` | Ado's theorem in characteristic zero | `LeanEval.RepresentationTheory.AdoIwasawa` |
| `adoIwasawa` | Ado–Iwasawa theorem over an arbitrary field | `LeanEval.RepresentationTheory.AdoIwasawa` |
| `annulus_theorem_dim_four` | The Annulus Theorem in dimension 4 (Quinn) | `LeanEval.Topology.AnnulusTheoremDimFour` |
| `annulus_theorem_high_dim` | The Annulus Theorem in dimension ≥ 5 (Kirby) | `LeanEval.Topology.AnnulusTheoremHighDim` |
| `aspherical_integer_homology_four_sphere` | Existence of an aspherical integer homology 4-sphere | `LeanEval.Topology.AsphericalHomologySphere` |
| `bakerWustholz_linearForms_logs` | Baker–Wüstholz theorem on linear forms in logarithms | `LeanEval.NumberTheory.BakerWustholz` |
| `bourgain_polynomial_ergodic` | Bourgain's polynomial ergodic theorem | `LeanEval.Dynamics.BourgainErgodic` |
| `cdt_linearIndependent` | Linear independence results of Calegari–Dimitrov–Tang | `LeanEval.NumberTheory.CalegariDimitrovTangLinearIndependent` |
| `cerf_gamma_four` | Cerf's theorem Γ₄ = 0 | `LeanEval.Topology.CerfGammaFour` |
| `chen_theorem` | Chen's theorem | `LeanEval.NumberTheory.ChenTheorem` |
| `ckmrv_fourier_interpolation` | Fourier interpolation in dimensions 8 and 24 | `LeanEval.Analysis.CKMRVInterpolation` |
| `conway_knot_not_smoothly_slice` | The Conway knot is not smoothly slice | `LeanEval.KnotTheory.Piccirillo` |
| `conway_knot_topologically_slice` | The Conway knot is topologically slice | `LeanEval.KnotTheory.ConwayTopologicallySlice` |
| `derived_solidification_free_CW_homology` | Derived solidification of free CW complexes | `LeanEval.CondensedMathematics.DerivedSolidCWHomology` |
| `duffin_schaeffer` | Duffin–Schaeffer conjecture | `LeanEval.NumberTheory.DuffinSchaeffer` |
| `e8_irrep_tensor_square_decomp` | 779247-dim irreducible e₈-representation | `LeanEval.RepresentationTheory.ExceptionalLieTensorSquare` |
| `equichordal_point_unique` | Equichordal point theorem | `LeanEval.Geometry.Equichordal` |
| `exists_topologically_slice_not_smoothly_slice` | Topologically but not smoothly slice knot | `LeanEval.KnotTheory.SliceDichotomy` |
| `fermat_last_theorem` | Fermat's Last Theorem | `LeanEval.NumberTheory.FermatLastTheorem` |
| `five_transitive_card_classification` | Orders of 5-transitive finite permutation groups | `LeanEval.GroupTheory.MultiplyTransitive` |
| `friedlander_iwaniec` | Friedlander–Iwaniec theorem | `LeanEval.NumberTheory.FriedlanderIwaniec` |
| `g2_irrep_tensor_square_decomp` | 64-dim irreducible g₂-representation | `LeanEval.RepresentationTheory.ExceptionalLieTensorSquare` |
| `gorenstein_walter` | Gorenstein–Walter theorem | `LeanEval.GroupTheory.GorensteinWalter` |
| `hadwiger` | Hadwiger's theorem | `LeanEval.ConvexGeometry.Hadwiger` |
| `hilbert_smith_padic_dimension_three` | Hilbert–Smith in dimension 3 (Pardon) | `LeanEval.Topology.HilbertSmith3D` |
| `honeycomb_connective_constant` | Connective constant of the honeycomb lattice | `LeanEval.Combinatorics.HoneycombConnectiveConstant` |
| `jacobian_challenge_alggeo` | Jacobian of a smooth proper curve | `LeanEval.AlgebraicGeometry.JacobianChallenge` |
| `kepler_conjecture` | Kepler conjecture | `LeanEval.Geometry.KeplerConjecture` |
| `linnik` | Linnik's theorem (L = 5.5) | `LeanEval.NumberTheory.Linnik` |
| `mandelbar_not_path_connected` | Mandelbar is not path-connected | `LeanEval.ComplexAnalysis.Mandelbar` |
| `mandelbrot_boundary_dimh` | Hausdorff dimension of ∂M (Shishikura) | `LeanEval.Dynamics.MandelbrotBoundary` |
| `manolescu_triangulation_disproof` | Disproof of the triangulation conjecture | `LeanEval.Topology.ManolescuTriangulation` |
| `martinet_totally_real_towers` | Martinet's totally real towers | `LeanEval.NumberTheory.MartinetTotallyRealTowers` |
| `mazur_torsion` | Mazur's torsion theorem | `LeanEval.NumberTheory.MazurTorsion` |
| `milnor_exotic_sphere_seven` | Milnor's exotic 7-sphere | `LeanEval.Topology.MilnorExoticSphereSeven` |
| `morley_categoricity_theorem` | Morley's categoricity theorem | `LeanEval.ModelTheory.MorleyCategoricity` |
| `pardon_torus_knot_distortion` | Pardon's torus-knot distortion bound | `LeanEval.KnotTheory.PardonDistortion` |
| `pi_succ_sphere_n_mulEquiv_zmod_two` | π_{n+1}(Sⁿ) ≅ ℤ/2 for n ≥ 3 | `LeanEval.Topology.HomotopyGroups` |
| `poincare_3d_smooth` | 3D smooth Poincaré conjecture | `LeanEval.Topology.Poincare3DSmooth` |
| `poincare_3d_topological` | 3D topological Poincaré conjecture | `LeanEval.Topology.Poincare3DTopological` |
| `poincare_4d_topological` | 4D topological Poincaré conjecture | `LeanEval.Topology.Poincare4DTopological` |
| `poincare_high_dim_topological` | Generalized Poincaré in dim ≥ 5 | `LeanEval.Topology.PoincareHighDimTopological` |
| `ramanujan_petersson` | Ramanujan–Petersson for τ (Deligne) | `LeanEval.NumberTheory.RamanujanTau` |
| `riemann_hypothesis_iff_lagarias_elementary_criterion` | Lagarias criterion ⟺ RH | `LeanEval.NumberTheory.Lagarias` |
| `schreier_conjecture` | Schreier's conjecture | `LeanEval.GroupTheory.SchreierConjecture` |
| `shafarevich_relation_rank_bound` | Shafarevich's relation-rank bound | `LeanEval.NumberTheory.ShafarevichRelationRank` |
| `shafarevich_solvable_galois` | Solvable groups are Galois over ℚ | `LeanEval.NumberTheory.ShafarevichSolvableGalois` |
| `smale_conjecture` | Smale conjecture (Hatcher) | `LeanEval.Topology.SmaleConjecture` |
| `smooth_knot_has_quadrisecant` | Pannwitz–Kuperberg quadrisecant theorem | `LeanEval.KnotTheory.Quadrisecant` |
| `space_groups_230` | 230 space groups | `LeanEval.Geometry.SpaceGroups` |
| `sphere_theorem_differentiable` | Differentiable sphere theorem | `LeanEval.Geometry.SphereTheorem` |
| `sphere_theorem_topological` | Topological sphere theorem | `LeanEval.Geometry.SphereTheorem` |
| `ten_martini_problem` | Ten Martini Problem | `LeanEval.Analysis.TenMartini` |
| `two_ninety_theorem` | The 290 theorem | `LeanEval.NumberTheory.TwoNinetyTheorem` |
| `wang_zahl_kakeya_dimH` | 3D Kakeya conjecture | `LeanEval.Analysis.WangZahlKakeya` |
| `watanabe_four_dim_smale_disproof` | Watanabe's disproof of 4D Smale | `LeanEval.Topology.WatanabeSmaleDisproof` |
| `weil_conjectures` | Weil conjectures | `LeanEval.AlgebraicGeometry.WeilConjectures` |
| `weinstein_conjecture_dim3` | Weinstein conjecture in dim 3 (Taubes) | `LeanEval.Geometry.WeinsteinConjecture3D` |
| `whitney_embedding` | Whitney embedding theorem (2n) | `LeanEval.Geometry.WhitneyEmbedding` |
| `zhang_bounded_prime_gaps` | Bounded gaps between primes | `LeanEval.NumberTheory.BoundedPrimeGaps` |

## 5. Difficulty triage

**Class ∞ — needs CFSG.** `schreier_conjecture`, `gorenstein_walter`,
`five_transitive_card_classification`. No CFSG-free proof exists, and CFSG will
not be formalised this decade.

**Class ∞ — needs geometric topology Mathlib does not have at all.**
All the Poincaré variants, both annulus theorems, `cerf_gamma_four`,
`smale_conjecture`, `watanabe_four_dim_smale_disproof`,
`milnor_exotic_sphere_seven`, `manolescu_triangulation_disproof`,
`aspherical_integer_homology_four_sphere`, `hilbert_smith_padic_dimension_three`,
`pi_succ_sphere_n_mulEquiv_zmod_two`, all four knot-theory problems,
`smooth_knot_has_quadrisecant`, `whitney_embedding` (needs Sard *and* the
Whitney trick), `sphere_theorem_*` (needs Riemannian geometry + Ricci flow),
`weinstein_conjecture_dim3`.

**Class ∞ — analytic number theory beyond the big sieve.**
`zhang_bounded_prime_gaps`, `chen_theorem`, `friedlander_iwaniec`, `linnik`,
`duffin_schaeffer`, `ramanujan_petersson`, `bakerWustholz_linearForms_logs`,
`cdt_linearIndependent`, `mazur_torsion`, `martinet_totally_real_towers`,
`shafarevich_*`, `riemann_hypothesis_iff_lagarias_elementary_criterion`,
`two_ninety_theorem`, `fermat_last_theorem`.

**Class ∞ — everything else big.** `kepler_conjecture` (Flyspeck),
`weil_conjectures`, `jacobian_challenge_alggeo`,
`derived_solidification_free_CW_homology`, `ckmrv_fourier_interpolation`,
`ten_martini_problem`, `wang_zahl_kakeya_dimH`, `bourgain_polynomial_ergodic`,
`mandelbrot_boundary_dimh`, `mandelbar_not_path_connected`, `space_groups_230`,
`e8_/g2_irrep_tensor_square_decomp`, `equichordal_point_unique`.

**Remaining, and genuinely the smallest.**

| rank | id | why it is the least far away |
| --- | --- | --- |
| 1 | `adoCharZero` | Finite-dimensional algebra only. Every ingredient (PBW, Casimir/Weyl, Levi, Birkhoff, Zassenhaus) is classical, purely equational, and has no analytic or topological content. Mathlib already has `FreeLieAlgebra`, `UniversalEnvelopingAlgebra`, Engel, Lie's theorem, Cartan's criteria, the Killing form, weight theory and semisimplicity. |
| 2 | `adoIwasawa` | Strictly implies `adoCharZero`, and reuses everything from it; the extra work is the characteristic-`p` argument (Iwasawa / Jacobson), which is again pure algebra. Best value-per-unit-effort pair in the whole set. |
| 3 | `morley_categoricity_theorem` | Pure model theory. Mathlib's `FirstOrder.Language`, `Theory.ModelType`, `CompleteType`, `Satisfiability`, elementary embeddings and Löwenheim–Skolem give a real starting point; nothing analytic is involved. |

`honeycomb_connective_constant` would otherwise rank near here, but it is
already being formalised in
`Vilin97/lean-eval-honeycomb-connective-constant` (4.6k lines as of
2026-08-03), so working on it here would duplicate that effort.

## 6. What Mathlib is missing (verified by reading the source)

| needed for | Mathlib status |
| --- | --- |
| Poincaré–Birkhoff–Witt | **absent**. `Mathlib/Algebra/Lie/UniversalEnveloping.lean` has only `ι`, `lift`, `hom_ext`. `Free.lean:36` and `SerreConstruction.lean:46` both say PBW would be needed and is not there. |
| `ι : L → U(L)` injective | **absent** (a corollary of PBW). |
| Casimir element | **absent** (`grep -r asimir Mathlib` finds nothing). |
| Weyl complete reducibility | **absent**. |
| Whitehead's lemmas / `H¹ = H² = 0` | **absent**; `Mathlib/Algebra/Lie/Cochain.lean` only defines 1- and 2-cochains and `twoCocycle`, with `TODO: coboundaries, cohomology`. |
| Levi decomposition | **absent**. |
| Lie nilradical | **absent** (`LieAlgebra.radical` exists; the nilradical does not). |
| Morley rank / ω-stability | **absent**. |
| Prime and saturated models | **absent**. |
| Indiscernibles / Ehrenfeucht–Mostowski | **absent**. |

Useful things that *do* exist and will be reused:
`LieAlgebra.IsSolvable`, `LieAlgebra.IsNilpotent`, `LieAlgebra.radical`,
`LieAlgebra.derivedSeries`, Engel (`Algebra/Lie/Engel.lean`), Lie's theorem
(`Algebra/Lie/LieTheorem.lean`), Cartan's criteria
(`Algebra/Lie/CartanCriterion.lean`), the Killing/trace forms,
`LieAlgebra.IsSemisimple`, `LieAlgebra.SemiDirect`, `LieModule.IsIrreducible`,
`FreeLieAlgebra` with its universal property, `TensorAlgebra` and
`FreeAlgebra` with their bases, and `RingQuot`/`RingCon` quotients.

External libraries scouted: Lean Pool has `SelbergSieve4`, `SardMoreira`,
`PointwiseBirkhoff`, `RootSystem`, `WhiteheadTheorem`, `Polytopes`,
`Zeta3Irrational`, `RamanujanTauMissesPrimes`; Tau Ceti has
`Algebra/Lie/{GeneralLinear,Sl2}`, `Geometry/Lie/*`, `RepresentationTheory/*`,
`Topology/Triangulable.lean`. Neither has PBW, Ado, or anything model-theoretic.
