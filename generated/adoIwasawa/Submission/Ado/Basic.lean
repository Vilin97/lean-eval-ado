import ChallengeDeps

/-!
# Ado's theorem: the standard reductions

This file sets up the interface used throughout the `Submission.Ado`
development and proves the two elementary reductions of §0 of the informal
proof:

* `Submission.Ado.HasFaithfulFinRep` is the statement asked for by the
  benchmark, in a form convenient to manipulate;
* `Submission.Ado.hasFaithfulFinRep_of_ker_inf_center` reduces the theorem to
  producing a finite-dimensional representation which is merely injective *on
  the centre*, by taking the direct sum with the adjoint representation.

The second reduction is what makes the whole proof possible: the adjoint
representation is free and already has kernel exactly the centre, so all the
real work goes into the centre.
-/

universe u

namespace Submission.Ado

open LeanEval.RepresentationTheory.AdoIwasawa

variable (K L : Type u) [Field K] [LieRing L] [LieAlgebra K L]

/-- `L` has a faithful finite-dimensional representation over `K`. This is
verbatim the shape of the benchmark statement. -/
def HasFaithfulFinRep : Prop :=
  ∃ (V : Type u) (_ : AddCommGroup V) (_ : Module K V) (_ : FiniteDimensional K V)
    (ρ : L →ₗ⁅K⁆ Module.End K V), Function.Injective ρ

variable {K L}

/-- A Lie algebra morphism into `Module.End` is injective as soon as its kernel
is trivial, since `LieHom` is additive. -/
theorem injective_of_map_eq_zero {V : Type u} [AddCommGroup V] [Module K V]
    (ρ : L →ₗ⁅K⁆ Module.End K V) (h : ∀ x : L, ρ x = 0 → x = 0) :
    Function.Injective ρ := by
  intro x y hxy
  have hz : ρ (x - y) = 0 := by simp [map_sub, hxy]
  exact sub_eq_zero.mp (h _ hz)

/-- The direct sum of two finite-dimensional representations, as a morphism into
the endomorphisms of the product. -/
noncomputable def prodRep {V W : Type u} [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W]
    (ρ : L →ₗ⁅K⁆ Module.End K V) (σ : L →ₗ⁅K⁆ Module.End K W) :
    L →ₗ⁅K⁆ Module.End K (V × W) :=
  ((LinearMap.prodMapAlgHom K V W : _ →ₐ[K] _) : _ →ₗ⁅K⁆ _).comp (ρ.prod σ)

@[simp]
theorem prodRep_apply {V W : Type u} [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W]
    (ρ : L →ₗ⁅K⁆ Module.End K V) (σ : L →ₗ⁅K⁆ Module.End K W) (x : L) (p : V × W) :
    prodRep ρ σ x p = (ρ x p.1, σ x p.2) := rfl

/-- The kernel of a direct sum is the intersection of the kernels. -/
theorem prodRep_eq_zero_iff {V W : Type u} [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W]
    (ρ : L →ₗ⁅K⁆ Module.End K V) (σ : L →ₗ⁅K⁆ Module.End K W) (x : L) :
    prodRep ρ σ x = 0 ↔ ρ x = 0 ∧ σ x = 0 := by
  constructor
  · intro h
    constructor
    · ext v
      have := congrArg (fun f => (f (v, 0)).1) h
      simpa using this
    · ext w
      have := congrArg (fun f => (f (0, w)).2) h
      simpa using this
  · rintro ⟨h₁, h₂⟩
    ext p <;> simp [h₁, h₂]

/-- An element is killed by the adjoint representation exactly when it is
central. -/
theorem ad_eq_zero_iff (x : L) :
    LieAlgebra.ad K L x = 0 ↔ ∀ y : L, ⁅x, y⁆ = 0 := by
  constructor
  · intro h y
    have := congrArg (fun f => f y) h
    simpa [LieAlgebra.ad_apply] using this
  · intro h
    ext y
    simpa [LieAlgebra.ad_apply] using h y

/-- **§0, Lemma 0.1.** To produce a faithful finite-dimensional representation
it suffices to produce a finite-dimensional representation that is injective on
the centre: take its direct sum with the adjoint representation. -/
theorem hasFaithfulFinRep_of_center [FiniteDimensional K L]
    {V : Type u} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (ρ : L →ₗ⁅K⁆ Module.End K V)
    (h : ∀ x : L, ρ x = 0 → (∀ y : L, ⁅x, y⁆ = 0) → x = 0) :
    HasFaithfulFinRep K L := by
  refine ⟨V × L, inferInstance, inferInstance, inferInstance,
    prodRep ρ (LieAlgebra.ad K L), ?_⟩
  refine injective_of_map_eq_zero _ fun x hx => ?_
  rw [prodRep_eq_zero_iff] at hx
  exact h x hx.1 ((ad_eq_zero_iff x).mp hx.2)

end Submission.Ado
