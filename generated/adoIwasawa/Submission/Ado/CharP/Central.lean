import Submission.Ado.CharP.AdPow
import Submission.Ado.EnvDeriv

/-!
# `p`-polynomial relations and central elements of `U(L)` in characteristic `p`

Let `K` be a field of prime characteristic `p` and let `L` be a finite-dimensional
Lie algebra over `K`. This file produces a supply of *central* elements of the
universal enveloping algebra `U(L)`, one for each `x : L`. Together with the
degree filtration of `Submission.Ado.Filtration` these are the elements used to
cut `U(L)` down to a finite-dimensional quotient in the characteristic `p` half
of the Ado–Iwasawa theorem.

## The argument

Everything rests on the identity `ad K a ^ p ^ i = ad K (a ^ p ^ i)` of
`Submission.Ado.ad_pow_char_pow`: in characteristic `p` the map `a ↦ ad K a` is
compatible with `p`-th powers. Consequently, if `x : L` satisfies a
*`p`-polynomial relation*

```
(ad x) ^ p ^ m = ∑ i : Fin m, lam i • (ad x) ^ p ^ i        (in `Module.End K L`)
```

then the element

```
c = ι x ^ p ^ m - ∑ i : Fin m, lam i • ι x ^ p ^ i          (in `U(L)`)
```

has `ad K c = 0`, i.e. is central. Indeed `ad K c` is a derivation of `U(L)`
(`Submission.Ado.ad_isDeriv`) which, by the displayed relation, kills every
generator `ι y`; a derivation of `U(L)` vanishing on `ι '' L` vanishes
identically (`Submission.Ado.isDeriv_ext`, which rests on
`Submission.Ado.adjoin_range_ι_eq_top`).

Such a relation always exists, and with an arbitrarily large exponent `m`:

* **existence** (`Submission.Ado.exists_pPolynomial_relation`) is pure linear
  algebra. The spans `S m = span K {A ^ p ^ i | i < m}` form an increasing chain
  of subspaces of the finite-dimensional space `Module.End K L`, hence stabilise;
  at a point of stabilisation `A ^ p ^ m ∈ S m`, which is the relation;
* **enlarging the exponent** (`Submission.Ado.exists_pPolynomial_relation_of_le`)
  is the freshman's dream. Reading the relation as `aeval A P = 0` for the
  polynomial `P = X ^ p ^ m' - ∑ i, C (lam i) * X ^ p ^ i` and raising `P` to the
  `p ^ k`-th power inside the *commutative* ring `Polynomial K` — where the
  iterated Frobenius `iterateFrobenius (Polynomial K) p k` is a ring
  homomorphism — turns it into a relation with exponent `m' + k` and coefficients
  `lam i ^ p ^ k` sitting in degrees `k + i < m' + k`.

## Main results

* `Submission.Ado.exists_pPolynomial_relation` — every endomorphism of a
  finite-dimensional vector space satisfies a `p`-polynomial relation;
* `Submission.Ado.exists_pPolynomial_relation_of_le` — such a relation can be
  transported to any larger exponent;
* `Submission.Ado.exists_pPolynomial_relation_of_ge` — the combination of the
  previous two: a relation exists for every sufficiently large exponent;
* `Submission.Ado.ad_isDeriv` — `ad K a` is a derivation of the associative
  algebra `A`;
* `Submission.Ado.central_pPolynomial`, `Submission.Ado.central_pPolynomial_mem_center`
  — the payoff: the `p`-polynomial in `ι x` attached to a `p`-polynomial relation
  for `ad x` is central in `U(L)`.

`Mathlib` makes `LieRing.ofAssociativeRing` a *local* instance only, so it is
re-enabled here for the last section, in order to speak about the universal
property of `U(L)`.
-/

universe u v

namespace Submission.Ado

open UniversalEnvelopingAlgebra

/-! ### Existence of a `p`-polynomial relation -/

section Linear

variable {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]

/-- **Every endomorphism of a finite-dimensional vector space satisfies a
`p`-polynomial relation.** For any `A : Module.End K V` there are `m ≥ 1` and
scalars `lam : Fin m → K` with `A ^ p ^ m = ∑ i, lam i • A ^ p ^ i`.

The proof is pure linear algebra and works for an arbitrary `p : ℕ`: the spans
`S m = span K {A ^ p ^ i | i < m}` form a monotone chain of submodules of the
Noetherian module `Module.End K V`, hence stabilise, and at any `m ≥ 1` with
`S m = S (m + 1)` the element `A ^ p ^ m` already lies in `S m`. -/
theorem exists_pPolynomial_relation [FiniteDimensional K V] (p : ℕ) (A : Module.End K V) :
    ∃ (m : ℕ) (lam : Fin m → K), 1 ≤ m ∧
      A ^ p ^ m = ∑ i : Fin m, lam i • A ^ p ^ (i : ℕ) := by
  obtain ⟨n, hn⟩ := monotone_stabilizes_iff_noetherian.mpr
    (inferInstance : IsNoetherian K (Module.End K V))
    ⟨fun j => Submodule.span K (Set.range fun i : Fin j => A ^ p ^ (i : ℕ)),
      fun a b hab => Submodule.span_mono (by rintro _ ⟨i, rfl⟩; exact ⟨Fin.castLE hab i, rfl⟩)⟩
  set m := max n 1 with hm
  have h1 := hn m (le_max_left _ _)
  have h2 := hn (m + 1) (le_trans (le_max_left _ _) (Nat.le_succ _))
  simp only [OrderHom.coe_mk] at h1 h2
  have hstab : Submodule.span K (Set.range fun i : Fin m => A ^ p ^ (i : ℕ))
      = Submodule.span K (Set.range fun i : Fin (m + 1) => A ^ p ^ (i : ℕ)) := h1.symm.trans h2
  have hmem : A ^ p ^ m ∈ Submodule.span K (Set.range fun i : Fin m => A ^ p ^ (i : ℕ)) := by
    rw [hstab]
    exact Submodule.subset_span ⟨⟨m, Nat.lt_succ_self m⟩, rfl⟩
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hmem
  exact ⟨m, c, le_max_right _ _, hc.symm⟩

end Linear

/-! ### Enlarging the exponent -/

section Uniform

variable {K : Type u} [Field K] {B : Type v} [Ring B] [Algebra K B]

/-- **A `p`-polynomial relation can be transported to any larger exponent.** If
`A ^ p ^ m' = ∑ i : Fin m', lam i • A ^ p ^ i` and `m' ≤ m`, then `A` satisfies a
`p`-polynomial relation with exponent `m` as well.

Writing the hypothesis as `aeval A P = 0` for `P = X ^ p ^ m' - ∑ i, C (lam i) * X ^ p ^ i`
and raising `P` to the `p ^ k`-th power for `k = m - m'` inside the commutative
characteristic `p` ring `Polynomial K`, the iterated Frobenius distributes over
the difference and the sum, producing the relation
`A ^ p ^ (k + m') = ∑ i : Fin m', lam i ^ p ^ k • A ^ p ^ (k + i)`; the remaining
`k` coefficients are set to `0`. -/
theorem exists_pPolynomial_relation_of_le (p : ℕ) [Fact p.Prime] [CharP K p] {A : B}
    {m' m : ℕ} {lam : Fin m' → K}
    (h : A ^ p ^ m' = ∑ i : Fin m', lam i • A ^ p ^ (i : ℕ)) (hle : m' ≤ m) :
    ∃ lam' : Fin m → K, A ^ p ^ m = ∑ i : Fin m, lam' i • A ^ p ^ (i : ℕ) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hle
  set P : Polynomial K :=
    Polynomial.X ^ p ^ m' - ∑ i : Fin m', Polynomial.C (lam i) * Polynomial.X ^ p ^ (i : ℕ)
    with hP
  have hzero : Polynomial.aeval A P = 0 := by
    simp only [hP, map_sub, map_sum, map_mul, Polynomial.aeval_C, Polynomial.aeval_X_pow,
      ← Algebra.smul_def, ← h, sub_self]
  have hX : ∀ n : ℕ, iterateFrobenius (Polynomial K) p k (Polynomial.X ^ n)
      = Polynomial.X ^ (p ^ k * n) := by
    intro n
    rw [map_pow, iterateFrobenius_def, ← pow_mul]
  have hfrob : P ^ p ^ k
      = Polynomial.X ^ p ^ (k + m')
        - ∑ i : Fin m', Polynomial.C (lam i ^ p ^ k) * Polynomial.X ^ p ^ (k + (i : ℕ)) := by
    rw [← iterateFrobenius_def (R := Polynomial K) p k, hP, map_sub, map_sum, hX, pow_add]
    refine congrArg _ (Finset.sum_congr rfl fun i _ => ?_)
    rw [map_mul, hX, iterateFrobenius_def, ← Polynomial.C_pow, pow_add]
  have hz2 : Polynomial.aeval A (P ^ p ^ k) = 0 := by
    rw [map_pow, hzero, zero_pow (pow_ne_zero k (Fact.out : p.Prime).ne_zero)]
  rw [hfrob, map_sub, map_sum] at hz2
  simp only [map_mul, Polynomial.aeval_C, Polynomial.aeval_X_pow, ← Algebra.smul_def] at hz2
  have hmain : A ^ p ^ (k + m') = ∑ i : Fin m', (lam i ^ p ^ k) • A ^ p ^ (k + (i : ℕ)) :=
    sub_eq_zero.mp hz2
  refine ⟨Fin.append (fun _ : Fin k => (0 : K)) fun i : Fin m' => lam i ^ p ^ k, ?_⟩
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right, zero_smul, Finset.sum_const_zero, zero_add]
  simpa using hmain

end Uniform

section Combined

variable {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]

/-- **Every sufficiently large exponent supports a `p`-polynomial relation.**
Combining `Submission.Ado.exists_pPolynomial_relation` with
`Submission.Ado.exists_pPolynomial_relation_of_le`: there is an `m₀ ≥ 1` such
that for every `m ≥ m₀` the endomorphism `A` satisfies a `p`-polynomial relation
of exponent `m`. -/
theorem exists_pPolynomial_relation_of_ge [FiniteDimensional K V] (p : ℕ) [Fact p.Prime]
    [CharP K p] (A : Module.End K V) :
    ∃ m₀ : ℕ, 1 ≤ m₀ ∧ ∀ m, m₀ ≤ m →
      ∃ lam : Fin m → K, A ^ p ^ m = ∑ i : Fin m, lam i • A ^ p ^ (i : ℕ) := by
  obtain ⟨m₀, lam, hm₀, hrel⟩ := exists_pPolynomial_relation p A
  exact ⟨m₀, hm₀, fun m hm => exists_pPolynomial_relation_of_le p hrel hm⟩

end Combined

/-! ### The adjoint action is a derivation -/

section Deriv

variable (K : Type u) {A : Type v} [Field K] [Ring A] [Algebra K A]

/-- The adjoint action `a ↦ ad K a` packaged as a `K`-linear map
`A →ₗ[K] Module.End K A`, so that it can be pushed through sums, differences and
scalar multiples. -/
def adLin : A →ₗ[K] Module.End K A :=
  LinearMap.mul K A - (LinearMap.mul K A).flip

@[simp]
theorem adLin_apply (a : A) : adLin K a = ad K a := rfl

/-- **The adjoint action is a derivation.** For every `a : A` the commutator
`ad K a : b ↦ a * b - b * a` satisfies the Leibniz rule
`ad K a (b * c) = ad K a b * c + b * ad K a c`. -/
theorem ad_isDeriv (a : A) : IsDeriv (ad K a) := by
  intro b c
  simp only [ad_apply]
  noncomm_ring

end Deriv

/-! ### Central elements of the universal enveloping algebra -/

section Central

variable {K L : Type u} [Field K] [LieRing L] [LieAlgebra K L]

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The augmentation `U(L) →ₐ[K] K`, i.e. the algebra morphism induced by the
zero morphism of Lie algebras `L → K`. It is only used here to see that `U(L)` is
nontrivial. -/
noncomputable def aug (K L : Type u) [Field K] [LieRing L] [LieAlgebra K L] :
    UniversalEnvelopingAlgebra K L →ₐ[K] K :=
  UniversalEnvelopingAlgebra.lift K (0 : L →ₗ⁅K⁆ K)

/-- `U(L)` is nontrivial, since it carries an algebra morphism onto `K`. -/
instance nontrivial_universalEnvelopingAlgebra :
    Nontrivial (UniversalEnvelopingAlgebra K L) :=
  (aug K L).toRingHom.domain_nontrivial

/-- `U(L)` inherits the characteristic of the base field. -/
instance charP_universalEnvelopingAlgebra (p : ℕ) [CharP K p] :
    CharP (UniversalEnvelopingAlgebra K L) p := charP_of_charP_base K p

/-- The adjoint action of a generator on a generator is the image of the Lie
bracket: `ad K (ι x) (ι y) = ι ⁅x, y⁆`. -/
theorem ad_ι_apply_ι (x y : L) :
    ad K (ι K x : UniversalEnvelopingAlgebra K L) (ι K y) = ι K ⁅x, y⁆ := by
  rw [ad_apply, ← LieRing.of_associative_ring_bracket, ← LieHom.map_lie]

/-- Iterating `Submission.Ado.ad_ι_apply_ι`: on generators, the powers of
`ad K (ι x)` are computed by the powers of `LieAlgebra.ad K L x`, namely
`(ad K (ι x)) ^ N (ι y) = ι ((ad x ^ N) y)`. -/
theorem ad_ι_pow_apply_ι (x y : L) (N : ℕ) :
    ((ad K (ι K x : UniversalEnvelopingAlgebra K L)) ^ N) (ι K y)
      = ι K ((LieAlgebra.ad K L x ^ N) y) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [pow_succ', Module.End.mul_apply, ih, pow_succ', Module.End.mul_apply,
        LieAlgebra.ad_apply, ad_ι_apply_ι]

/-- **`p`-polynomial relations produce central elements of `U(L)`.** Let `K` have
characteristic `p`, let `x : L` and suppose that the inner derivation
`LieAlgebra.ad K L x` satisfies the `p`-polynomial relation
`ad x ^ p ^ m = ∑ i : Fin m, lam i • ad x ^ p ^ i`. Then the corresponding
`p`-polynomial in `ι x`,

`c = ι x ^ p ^ m - ∑ i : Fin m, lam i • ι x ^ p ^ i`,

commutes with every element of `U(L)`.

Indeed `ad K c` is `K`-linear in `c` and compatible with `p`-th powers
(`Submission.Ado.ad_pow_char_pow`), so it equals
`ad K (ι x) ^ p ^ m - ∑ i, lam i • ad K (ι x) ^ p ^ i`; by
`Submission.Ado.ad_ι_pow_apply_ι` and the hypothesis it kills every generator
`ι y`. Being a derivation (`Submission.Ado.ad_isDeriv`) that vanishes on the
generating set `ι '' L`, it vanishes identically. -/
theorem central_pPolynomial (p : ℕ) [Fact p.Prime] [CharP K p] (x : L) {m : ℕ} (lam : Fin m → K)
    (h : LieAlgebra.ad K L x ^ p ^ m
      = ∑ i : Fin m, lam i • LieAlgebra.ad K L x ^ p ^ (i : ℕ))
    (u : UniversalEnvelopingAlgebra K L) :
    ((ι K x : UniversalEnvelopingAlgebra K L) ^ p ^ m
        - ∑ i : Fin m, lam i • (ι K x : UniversalEnvelopingAlgebra K L) ^ p ^ (i : ℕ)) * u
      = u * ((ι K x : UniversalEnvelopingAlgebra K L) ^ p ^ m
        - ∑ i : Fin m, lam i • (ι K x : UniversalEnvelopingAlgebra K L) ^ p ^ (i : ℕ)) := by
  set c : UniversalEnvelopingAlgebra K L :=
    (ι K x : UniversalEnvelopingAlgebra K L) ^ p ^ m
      - ∑ i : Fin m, lam i • (ι K x : UniversalEnvelopingAlgebra K L) ^ p ^ (i : ℕ) with hc
  have hadc : ad K c
      = (ad K (ι K x : UniversalEnvelopingAlgebra K L)) ^ p ^ m
        - ∑ i : Fin m, lam i • (ad K (ι K x : UniversalEnvelopingAlgebra K L)) ^ p ^ (i : ℕ) := by
    rw [hc, ← adLin_apply, map_sub, map_sum]
    simp only [map_smul, adLin_apply, ad_pow_char_pow]
  have hD : ad K c = 0 := by
    refine isDeriv_ext (ad_isDeriv K c) isDeriv_zero fun y => ?_
    have hy : ((LieAlgebra.ad K L x ^ p ^ m
        - ∑ i : Fin m, lam i • LieAlgebra.ad K L x ^ p ^ (i : ℕ)) : Module.End K L) y = 0 := by
      rw [h, sub_self, LinearMap.zero_apply]
    rw [LinearMap.sub_apply, LinearMap.sum_apply] at hy
    simp only [LinearMap.smul_apply] at hy
    rw [hadc, LinearMap.sub_apply, LinearMap.sum_apply, LinearMap.zero_apply]
    simp only [LinearMap.smul_apply, ad_ι_pow_apply_ι]
    simpa using congrArg (fun z : L => (ι K z : UniversalEnvelopingAlgebra K L)) hy
  have hu := congrArg (fun f : Module.End K (UniversalEnvelopingAlgebra K L) => f u) hD
  simp only [ad_apply, LinearMap.zero_apply] at hu
  linear_combination (norm := noncomm_ring) hu

/-- The `Subring.center` phrasing of `Submission.Ado.central_pPolynomial`. -/
theorem central_pPolynomial_mem_center (p : ℕ) [Fact p.Prime] [CharP K p] (x : L) {m : ℕ}
    (lam : Fin m → K)
    (h : LieAlgebra.ad K L x ^ p ^ m
      = ∑ i : Fin m, lam i • LieAlgebra.ad K L x ^ p ^ (i : ℕ)) :
    (ι K x : UniversalEnvelopingAlgebra K L) ^ p ^ m
        - ∑ i : Fin m, lam i • (ι K x : UniversalEnvelopingAlgebra K L) ^ p ^ (i : ℕ)
      ∈ Subring.center (UniversalEnvelopingAlgebra K L) :=
  Subring.mem_center_iff.2 fun u => (central_pPolynomial p x lam h u).symm

end Central

end Submission.Ado
