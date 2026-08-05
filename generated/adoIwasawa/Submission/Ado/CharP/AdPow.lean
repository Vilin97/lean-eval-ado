import ChallengeDeps

/-!
# `p`-th powers of the adjoint action in characteristic `p`

Let `K` be a commutative ring and let `A` be an associative (unital) `K`-algebra.
For `a : A` the *adjoint action* of `a` is the `K`-linear endomorphism

`Submission.Ado.ad K a : Module.End K A`, `b ↦ a * b - b * a`.

Writing `L a := LinearMap.mulLeft K a` and `R a := LinearMap.mulRight K a` we have
`ad K a = L a - R a`, and associativity of `A` says exactly that `L a` and `R a`
commute inside the ring `Module.End K A`. Moreover `L` is multiplicative and `R`
is *anti*-multiplicative, but since all the factors involved are powers of the
single element `a` this makes no difference: `L a ^ n = L (a ^ n)` and
`R a ^ n = R (a ^ n)` for every `n : ℕ` (`LinearMap.pow_mulLeft`,
`LinearMap.pow_mulRight`).

Consequently, if `A` has characteristic `p` for a prime `p`, then so does
`Module.End K A` (`Submission.Ado.charP_end`, obtained by transporting the
characteristic along the injective ring homomorphism `Algebra.lmul K A`), and the
freshman's dream for commuting elements gives

`ad K a ^ p = L a ^ p - R a ^ p = L (a ^ p) - R (a ^ p) = ad K (a ^ p)`.

An immediate induction upgrades this to all `p`-power exponents.

This is the identity underlying the *restricted* (`p`-)structure carried by any
Lie algebra of characteristic `p` arising from an associative algebra, and it is
one of the basic inputs for the characteristic `p` half of the Ado–Iwasawa
theorem.

## Main results

* `Submission.Ado.ad_pow_char`: `ad K a ^ p = ad K (a ^ p)`;
* `Submission.Ado.ad_pow_char_pow`: `ad K a ^ p ^ i = ad K (a ^ p ^ i)`.

Both are stated over an arbitrary commutative base ring `K`, with the
characteristic assumption `[CharP A p]` placed on the algebra itself. In the
situation of interest, where `K` is a field of characteristic `p` and `A` is a
nontrivial `K`-algebra, that hypothesis is supplied by
`Submission.Ado.charP_of_charP_base`.
-/

universe u v

namespace Submission.Ado

open LinearMap

section CommRingBase

variable (K : Type u) {A : Type v} [CommRing K] [Ring A] [Algebra K A]

/-- The adjoint action of `a : A` on the `K`-algebra `A`: the `K`-linear
endomorphism `b ↦ a * b - b * a`, i.e. the commutator with `a`. -/
def ad (a : A) : Module.End K A :=
  mulLeft K a - mulRight K a

@[simp]
theorem ad_apply (a b : A) : ad K a b = a * b - b * a :=
  rfl

/-- The adjoint action is the difference of left and right multiplication. -/
theorem ad_eq_mulLeft_sub_mulRight (a : A) : ad K a = mulLeft K a - mulRight K a :=
  rfl

/-- Left and right multiplication by the same element commute: this is exactly
associativity of `A`. -/
theorem commute_mulLeft_mulRight (a : A) : Commute (mulLeft K a) (mulRight K a) :=
  commute_mulLeft_right a a

/-- Left multiplication is multiplicative, so its powers are left multiplication
by the corresponding power. -/
theorem mulLeft_pow (a : A) (n : ℕ) : mulLeft K a ^ n = mulLeft K (a ^ n) :=
  pow_mulLeft K A a n

/-- Right multiplication is *anti*-multiplicative, but powers of a single element
commute with one another, so the powers of right multiplication by `a` are still
right multiplication by the corresponding power of `a`. -/
theorem mulRight_pow (a : A) (n : ℕ) : mulRight K a ^ n = mulRight K (a ^ n) :=
  pow_mulRight K A a n

/-- If the `K`-algebra `A` has characteristic `p`, then so does its ring of
`K`-linear endomorphisms: the algebra map `Algebra.lmul K A : A →ₐ[K] Module.End K A`
sending `a` to left multiplication by `a` is an injective ring homomorphism. -/
instance charP_end (p : ℕ) [CharP A p] : CharP (Module.End K A) p :=
  charP_of_injective_ringHom
    (f := (Algebra.lmul K A : A →ₐ[K] Module.End K A).toRingHom) Algebra.lmul_injective p

/-- **The `p`-th power of an adjoint action in characteristic `p`.** If `A` is an
associative `K`-algebra of prime characteristic `p`, then `ad` commutes with
taking `p`-th powers: `ad K a ^ p = ad K (a ^ p)`.

Indeed `ad K a = mulLeft K a - mulRight K a` is a difference of two commuting
elements of the characteristic `p` ring `Module.End K A`, so the `p`-th power
distributes over the subtraction. -/
theorem ad_pow_char (p : ℕ) [Fact p.Prime] [CharP A p] (a : A) : ad K a ^ p = ad K (a ^ p) := by
  rw [ad_eq_mulLeft_sub_mulRight, sub_pow_char_of_commute p (commute_mulLeft_mulRight K a),
    mulLeft_pow, mulRight_pow, ad_eq_mulLeft_sub_mulRight]

/-- **The `p ^ i`-th power of an adjoint action in characteristic `p`.** Iterating
`Submission.Ado.ad_pow_char` gives `ad K a ^ p ^ i = ad K (a ^ p ^ i)` for every
`i : ℕ`. -/
theorem ad_pow_char_pow (p : ℕ) [Fact p.Prime] [CharP A p] (a : A) (i : ℕ) :
    ad K a ^ p ^ i = ad K (a ^ p ^ i) := by
  induction i with
  | zero => simp
  | succ i ih => rw [pow_succ, pow_mul, ih, ad_pow_char, ← pow_mul, ← pow_succ]

end CommRingBase

section FieldBase

variable (K : Type u) {A : Type v} [Field K] [Ring A] [Algebra K A] [Nontrivial A]

/-- A nontrivial algebra over a field of characteristic `p` again has characteristic
`p`, because the structure map of a field into a nontrivial ring is injective.

This is the usual way to feed the hypothesis `[CharP A p]` of
`Submission.Ado.ad_pow_char` and `Submission.Ado.ad_pow_char_pow`, which are
otherwise stated for an arbitrary commutative base ring `K`. -/
theorem charP_of_charP_base (p : ℕ) [CharP K p] : CharP A p :=
  charP_of_injective_algebraMap (algebraMap K A).injective p

end FieldBase

end Submission.Ado
