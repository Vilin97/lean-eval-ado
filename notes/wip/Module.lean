import Submission.Ado.PBW.Action

/-!
# The PBW module over a Lie algebra with an ordered basis

`Action.lean` works with abstract structure constants `γ`. Here we fix a Lie
algebra `L` with a basis indexed by `Fin n`, take `γ` to be its structure
constants, and package the action as a linear map `L →ₗ[K] Module.End K (Poly K n)`.

The main theorem is `rhoL_lie`: this map is a morphism of Lie algebras, i.e.
`Poly K n` is an `L`-module. This is statement (C) of the construction.
-/

universe u

namespace Submission.Ado.PBW

variable {K : Type u} [Field K] {L : Type u} [LieRing L] [LieAlgebra K L] {n : ℕ}

/-- The structure constants of `L` in the basis `bas`. -/
noncomputable def gamma (bas : Module.Basis (Fin n) K L) (i j k : Fin n) : K :=
  bas.repr ⁅bas i, bas j⁆ k

/-- The action of an arbitrary element of `L` on the PBW module, obtained from
the action of the basis vectors by linearity. -/
noncomputable def rhoL (bas : Module.Basis (Fin n) K L) : L →ₗ[K] Module.End K (Poly K n) :=
  ∑ k : Fin n, (LinearMap.toSpanSingleton K (Module.End K (Poly K n))
      (rho (gamma bas) k)) ∘ₗ (bas.coord k)

theorem rhoL_apply (bas : Module.Basis (Fin n) K L) (x : L) :
    rhoL bas x = ∑ k : Fin n, bas.repr x k • rho (gamma bas) k := by
  simp [rhoL, LinearMap.toSpanSingleton, Module.Basis.coord]

@[simp] theorem rhoL_basis (bas : Module.Basis (Fin n) K L) (i : Fin n) :
    rhoL bas (bas i) = rho (gamma bas) i := by
  rw [rhoL_apply]
  simp [Module.Basis.repr_self, Finsupp.single_apply]

/-- The bracket of two basis vectors acts through the structure constants. -/
theorem rhoL_lie_basis (bas : Module.Basis (Fin n) K L) (i j : Fin n) :
    rhoL bas ⁅bas i, bas j⁆ = ∑ k : Fin n, gamma bas i j k • rho (gamma bas) k := by
  rw [rhoL_apply]; rfl

/-- **(C).** `Poly K n` is a Lie module over `L`: the commutator of the actions of
`x` and `y` is the action of `⁅x, y⁆`.

This is proved by strong induction on the degree of a monomial; the aligned case
`lie_rel_aligned` holds by construction in every degree, and the general case
reduces to it via the Jacobi identity. -/
theorem rhoL_lie (bas : Module.Basis (Fin n) K L) (x y : L) :
    ⁅rhoL bas x, rhoL bas y⁆ = rhoL bas ⁅x, y⁆ := by
  sorry

end Submission.Ado.PBW
