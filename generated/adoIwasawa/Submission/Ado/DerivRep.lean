import ChallengeDeps

/-!
# Representations built from left multiplications and derivations

This is the algebraic engine of the extension step (§4 of the informal proof).

Let `A` be an associative `K`-algebra. `A` acts on itself by left multiplication,
and derivations of `A` act on `A` as well. The two interact by the identity

```
⁅D, mulLeft a⁆ = mulLeft (D a)          (`commutator_mulLeft`)
```

which says exactly that `a ↦ mulLeft a` is equivariant for the derivation
action. Consequently, given a Lie algebra `L`, a linear map `f : L →ₗ[K] A` and
a linear map `D : L →ₗ[K] Module.End K A` landing in derivations, the assignment

```
ρ x := mulLeft (f x) + D x
```

is a Lie algebra morphism `L →ₗ⁅K⁆ Module.End K A` as soon as

* `D` is itself a Lie algebra morphism, and
* `f ⁅x, y⁆ = f x * f y - f y * f x + D x (f y) - D y (f x)`.

Every representation constructed in the Ado development — Birkhoff's embedding
(§3), the solvable induction step (§5) and the Levi step (§6) — is an instance
of `lieHomOfMulLeftAddDeriv` below, for a different choice of `A`, `f` and `D`.
The "crossed" condition on `f` is exactly what fails for a naive vector-space
complement, which is why the Ado proof must extend either one dimension at a
time or along a Levi subalgebra (Remark 4.6 of the informal proof).
-/

universe u v

namespace Submission.Ado

variable {K : Type u} [Field K]
variable {A : Type v} [Ring A] [Algebra K A]

/-- A `K`-linear endomorphism of `A` satisfying the Leibniz rule. -/
def IsDeriv (D : Module.End K A) : Prop :=
  ∀ a b : A, D (a * b) = D a * b + a * D b

theorem IsDeriv.map_one {D : Module.End K A} (hD : IsDeriv D) : D 1 = 0 := by
  have h := hD 1 1
  simp only [one_mul, mul_one] at h
  have h2 : D 1 + 0 = D 1 + D 1 := by rw [add_zero]; exact h
  exact (add_left_cancel h2).symm

theorem isDeriv_zero : IsDeriv (0 : Module.End K A) := by
  intro a b; simp

/-- **The key identity.** For a derivation `D` of `A` and `a : A`, the
commutator of `D` with left multiplication by `a` is left multiplication by
`D a`. -/
theorem commutator_mulLeft {D : Module.End K A} (hD : IsDeriv D) (a : A) :
    ⁅D, LinearMap.mulLeft K a⁆ = LinearMap.mulLeft K (D a) := by
  ext b
  have h := hD a b
  simp only [LieRing.of_associative_ring_bracket, LinearMap.sub_apply,
    Module.End.mul_apply, LinearMap.mulLeft_apply]
  rw [h]
  abel

/-- Left multiplications bracket to left multiplication by the ring
commutator. -/
theorem commutator_mulLeft_mulLeft (a b : A) :
    ⁅LinearMap.mulLeft K a, LinearMap.mulLeft K b⁆
      = LinearMap.mulLeft K (a * b - b * a) := by
  ext c
  simp only [LieRing.of_associative_ring_bracket, LinearMap.sub_apply,
    Module.End.mul_apply, LinearMap.mulLeft_apply, sub_mul, mul_assoc]

/-- `mulLeft` bundled as a `K`-linear map `A →ₗ[K] Module.End K A`. -/
def mulLeftHom : A →ₗ[K] Module.End K A := LinearMap.mul K A

@[simp]
theorem mulLeftHom_apply (a : A) : (mulLeftHom : A →ₗ[K] Module.End K A) a
    = LinearMap.mulLeft K a := rfl

variable {L : Type u} [LieRing L] [LieAlgebra K L]

/-- **§4.5.** `x ↦ mulLeft (f x) + D x` is a morphism of Lie algebras provided
`D` is one and `f` satisfies the crossed condition. -/
def mulLeftAddDerivLin (f : L →ₗ[K] A) (D : L →ₗ[K] Module.End K A) :
    L →ₗ[K] Module.End K A :=
  (mulLeftHom : A →ₗ[K] Module.End K A).comp f + D

@[simp]
theorem mulLeftAddDerivLin_apply (f : L →ₗ[K] A) (D : L →ₗ[K] Module.End K A) (x : L) :
    mulLeftAddDerivLin f D x = LinearMap.mulLeft K (f x) + D x := rfl

def lieHomOfMulLeftAddDeriv
    (f : L →ₗ[K] A) (D : L →ₗ[K] Module.End K A)
    (hD : ∀ x : L, IsDeriv (D x))
    (hDlie : ∀ x y : L, D ⁅x, y⁆ = ⁅D x, D y⁆)
    (hf : ∀ x y : L, f ⁅x, y⁆ = f x * f y - f y * f x + D x (f y) - D y (f x)) :
    L →ₗ⁅K⁆ Module.End K A :=
  { mulLeftAddDerivLin f D with
    map_lie' := by
      intro x y
      show LinearMap.mulLeft K (f ⁅x, y⁆) + D ⁅x, y⁆
        = ⁅LinearMap.mulLeft K (f x) + D x, LinearMap.mulLeft K (f y) + D y⁆
      have e1 : ⁅LinearMap.mulLeft K (f x), LinearMap.mulLeft K (f y)⁆
          = LinearMap.mulLeft K (f x * f y - f y * f x) :=
        commutator_mulLeft_mulLeft _ _
      have e2 : ⁅D x, LinearMap.mulLeft K (f y)⁆
          = LinearMap.mulLeft K (D x (f y)) := commutator_mulLeft (hD x) _
      have e3 : ⁅LinearMap.mulLeft K (f x), D y⁆
          = -LinearMap.mulLeft K (D y (f x)) := by
        rw [← lie_skew, commutator_mulLeft (hD y)]
      rw [hf x y, hDlie x y, lie_add, add_lie, add_lie, e1, e2, e3]
      simp only [← mulLeftHom_apply, map_sub, map_add]
      abel }

@[simp]
theorem lieHomOfMulLeftAddDeriv_apply
    (f : L →ₗ[K] A) (D : L →ₗ[K] Module.End K A) (hD hDlie hf) (x : L) :
    lieHomOfMulLeftAddDeriv f D hD hDlie hf x
      = LinearMap.mulLeft K (f x) + D x := rfl

/-- A unital algebra acts faithfully on itself by left multiplication, so a
representation of the above shape kills `x` only if both `f x` and `D x`
vanish. This is how faithfulness is checked at every extension step. -/
theorem lieHomOfMulLeftAddDeriv_eq_zero_iff
    (f : L →ₗ[K] A) (D : L →ₗ[K] Module.End K A) (hD hDlie hf) (x : L) :
    lieHomOfMulLeftAddDeriv f D hD hDlie hf x = 0 ↔ f x = 0 ∧ D x = 0 := by
  constructor
  · intro hx
    have h1 : (LinearMap.mulLeft K (f x) + D x) (1 : A) = 0 := by
      rw [← lieHomOfMulLeftAddDeriv_apply f D hD hDlie hf x, hx]; rfl
    simp only [LinearMap.add_apply, LinearMap.mulLeft_apply, mul_one,
      (hD x).map_one, add_zero] at h1
    refine ⟨h1, ?_⟩
    have h2 : LinearMap.mulLeft K (f x) = (0 : Module.End K A) := by
      rw [h1]; ext b; simp
    rw [lieHomOfMulLeftAddDeriv_apply, h2, zero_add] at hx
    exact hx
  · rintro ⟨h1, h2⟩
    rw [lieHomOfMulLeftAddDeriv_apply, h1, h2, add_zero]
    ext b; simp

end Submission.Ado
