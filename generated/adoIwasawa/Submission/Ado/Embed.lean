import Submission.Ado.Basic
import Submission.Ado.DerivRep

/-!
# Ado's theorem is equivalent to embedding into a finite-dimensional algebra

The bridge that both halves of the Ado development cross at the very end:

> `L` has a faithful finite-dimensional representation **iff** `L` embeds into a
> finite-dimensional associative `K`-algebra, with brackets going to ring
> commutators.

The interesting direction is `←`: a unital algebra `A` acts faithfully on
itself by left multiplication, because `mulLeft a` applied to `1` returns `a`.
So an embedding `L ↪ A` immediately gives a representation on `A` itself.

This is exactly how the two constructive parts of the proof conclude:

* **Birkhoff (§3)**, with `A = U(N) ⧸ J(N)^k` — finite-dimensional by PBW, and
  `N ↪ A` because `N ∩ J² = ⊥`;
* **Ado–Iwasawa in characteristic `p` (§7)**, with `A = u(𝔤̂)` the restricted
  enveloping algebra of a finite-dimensional `p`-envelope of `L` — of dimension
  `p ^ dim 𝔤̂` by the restricted PBW theorem.

Since Mathlib makes `LieRing.ofAssociativeRing` a *local* instance only (a
global one would create a diamond on `A = M`), the commutator condition is
spelled out as a hypothesis rather than packaged as a `LieHom`.
-/

universe u

namespace Submission.Ado

variable {K L : Type u} [Field K] [LieRing L] [LieAlgebra K L]

/-- **The useful direction.** An injective `K`-linear map `L → A` into a
finite-dimensional algebra that turns Lie brackets into ring commutators gives a
faithful finite-dimensional representation of `L`, namely left multiplication on
`A`. -/
theorem hasFaithfulFinRep_of_injective_toAlgebra
    {A : Type u} [Ring A] [Algebra K A] [FiniteDimensional K A]
    (φ : L →ₗ[K] A) (hφ : ∀ x y : L, φ ⁅x, y⁆ = φ x * φ y - φ y * φ x)
    (hinj : Function.Injective φ) :
    HasFaithfulFinRep K L := by
  have hD : ∀ x : L, IsDeriv ((0 : L →ₗ[K] Module.End K A) x) := by
    intro x; simpa using isDeriv_zero (K := K) (A := A)
  have hDlie : ∀ x y : L, (0 : L →ₗ[K] Module.End K A) ⁅x, y⁆
      = ⁅(0 : L →ₗ[K] Module.End K A) x, (0 : L →ₗ[K] Module.End K A) y⁆ := by
    intro x y; simp
  have hf : ∀ x y : L, φ ⁅x, y⁆
      = φ x * φ y - φ y * φ x
        + (0 : L →ₗ[K] Module.End K A) x (φ y)
        - (0 : L →ₗ[K] Module.End K A) y (φ x) := by
    intro x y; simpa using hφ x y
  refine ⟨A, inferInstance, inferInstance, inferInstance,
    lieHomOfMulLeftAddDeriv φ 0 hD hDlie hf, ?_⟩
  refine injective_of_map_eq_zero _ fun x hx => ?_
  rw [lieHomOfMulLeftAddDeriv_eq_zero_iff] at hx
  have : φ x = φ 0 := by rw [hx.1, map_zero]
  exact hinj this

/-- **The easy direction.** A faithful finite-dimensional representation is in
particular an embedding into the finite-dimensional algebra `Module.End K V`. -/
theorem exists_injective_toAlgebra_of_hasFaithfulFinRep
    (h : HasFaithfulFinRep K L) :
    ∃ (A : Type u) (_ : Ring A) (_ : Algebra K A) (_ : FiniteDimensional K A)
      (φ : L →ₗ[K] A),
      (∀ x y : L, φ ⁅x, y⁆ = φ x * φ y - φ y * φ x) ∧ Function.Injective φ := by
  obtain ⟨V, _, _, _, ρ, hρ⟩ := h
  refine ⟨Module.End K V, inferInstance, inferInstance, inferInstance,
    (ρ : L →ₗ[K] Module.End K V), fun x y => ?_, hρ⟩
  have := ρ.map_lie x y
  rwa [LieRing.of_associative_ring_bracket] at this

/-- Ado's theorem for `L` is *equivalent* to `L` embedding into a
finite-dimensional associative algebra. -/
theorem hasFaithfulFinRep_iff_exists_injective_toAlgebra :
    HasFaithfulFinRep K L ↔
      ∃ (A : Type u) (_ : Ring A) (_ : Algebra K A) (_ : FiniteDimensional K A)
        (φ : L →ₗ[K] A),
        (∀ x y : L, φ ⁅x, y⁆ = φ x * φ y - φ y * φ x) ∧ Function.Injective φ := by
  refine ⟨exists_injective_toAlgebra_of_hasFaithfulFinRep, ?_⟩
  rintro ⟨A, _, _, _, φ, hφ, hinj⟩
  exact hasFaithfulFinRep_of_injective_toAlgebra φ hφ hinj

end Submission.Ado
