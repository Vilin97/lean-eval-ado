import Submission.Ado.Easy

/-!
# Closure properties of Ado's property

`HasFaithfulFinRep` is inherited along injective Lie morphisms and is stable
under binary products. Both are used in the assembly:

* inheritance along an injection is how the characteristic-`p` argument (§7)
  descends from a finite-dimensional `p`-envelope `𝔤̂ ⊇ L` back to `L`;
* the product statement is the trivial half of the observation that Ado's
  property only depends on `L` through a finite-dimensional algebra it embeds
  in.

The semisimple case is also recorded: a Lie algebra with trivial radical has
trivial centre, so its adjoint representation is already faithful, and Ado's
theorem needs no work at all there. All the difficulty of Ado's theorem lives
in the solvable radical.
-/

universe u

namespace Submission.Ado

variable {K L : Type u} [Field K] [LieRing L] [LieAlgebra K L]

/-- Ado's property is inherited along an injective Lie algebra morphism; in
particular it passes to Lie subalgebras. -/
theorem HasFaithfulFinRep.of_injective {L' : Type u} [LieRing L'] [LieAlgebra K L']
    (f : L' →ₗ⁅K⁆ L) (hf : Function.Injective f) (h : HasFaithfulFinRep K L) :
    HasFaithfulFinRep K L' := by
  obtain ⟨V, _, _, _, ρ, hρ⟩ := h
  exact ⟨V, inferInstance, inferInstance, inferInstance, ρ.comp f, hρ.comp hf⟩

/-- Ado's property is stable under binary products. -/
theorem HasFaithfulFinRep.prod {L₁ L₂ : Type u} [LieRing L₁] [LieAlgebra K L₁]
    [LieRing L₂] [LieAlgebra K L₂]
    (h₁ : HasFaithfulFinRep K L₁) (h₂ : HasFaithfulFinRep K L₂) :
    HasFaithfulFinRep K (L₁ × L₂) := by
  obtain ⟨V, _, _, _, ρ, hρ⟩ := h₁
  obtain ⟨W, _, _, _, σ, hσ⟩ := h₂
  refine ⟨V × W, inferInstance, inferInstance, inferInstance,
    prodRep (ρ.comp (LieHom.fst K L₁ L₂)) (σ.comp (LieHom.snd K L₁ L₂)), ?_⟩
  refine injective_of_map_eq_zero _ fun x hx => ?_
  rw [prodRep_eq_zero_iff] at hx
  have h1 : x.1 = 0 := hρ (by simpa using hx.1)
  have h2 : x.2 = 0 := hσ (by simpa using hx.2)
  exact Prod.ext h1 h2

/-- **Ado's theorem for Lie algebras with trivial radical** (in particular for
semisimple Lie algebras): the adjoint representation is already faithful, since
the centre is an abelian ideal and hence trivial. -/
theorem hasFaithfulFinRep_of_hasTrivialRadical [FiniteDimensional K L]
    [LieAlgebra.HasTrivialRadical K L] :
    HasFaithfulFinRep K L := by
  refine hasFaithfulFinRep_of_center_trivial fun x hx => ?_
  have hmem : x ∈ LieAlgebra.center K L :=
    (LieModule.mem_maxTrivSubmodule K L L x).mpr fun y => by
      rw [← lie_skew, hx y, neg_zero]
  rw [LieAlgebra.center_eq_bot K L, LieSubmodule.mem_bot] at hmem
  exact hmem

end Submission.Ado
