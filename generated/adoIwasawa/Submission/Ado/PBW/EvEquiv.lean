import Submission.Ado.PBW.Basis2

/-!
# The evaluation map is a linear isomorphism

A corollary of the Poincaré–Birkhoff–Witt theorem: the map

```
ev bas : U(L) →ₗ[K] Poly K n,   ev bas u = u • z⁰
```

is a `K`-linear isomorphism. Indeed `ev` carries the PBW basis `pbwMonomial bas a`
to `z^a + (lower degree)`, a unitriangular family over the identity of `Mon n`,
which is therefore a basis of `Poly K n`.

Concretely: `U(L)` is a free module on the ordered monomials, `Poly K n` is a free
module on the exponent vectors, and `ev` matches the two bases up to a unipotent
triangular change of coordinates.
-/

universe u

namespace Submission.Ado.PBW

open UniversalEnvelopingAlgebra

variable {K : Type u} [Field K] {L : Type u} [LieRing L] [LieAlgebra K L] {n : ℕ}

/-- The images of the ordered monomials under `ev` form a basis of the polynomial
module. -/
noncomputable def evPbwBasis (bas : Module.Basis (Fin n) K L) :
    Module.Basis (Mon n) K (Poly K n) :=
  Module.Basis.mk
    ((unitriangular_ev_pbwMonomial bas).linearIndependent Function.injective_id)
    (le_of_eq ((unitriangular_ev_pbwMonomial bas).span_eq_top
      Function.surjective_id).symm)

@[simp] theorem evPbwBasis_apply (bas : Module.Basis (Fin n) K L) (a : Mon n) :
    evPbwBasis bas a = ev bas (pbwMonomial bas a) :=
  Module.Basis.mk_apply _ _ _

theorem ev_injective (bas : Module.Basis (Fin n) K L) :
    Function.Injective (ev bas) := by
  rw [← LinearMap.ker_eq_bot]
  refine (Submodule.eq_bot_iff _).mpr fun u hu => ?_
  -- write `u` in the PBW basis
  have hrepr : u = (pbwBasis bas).repr.symm ((pbwBasis bas).repr u) := by simp
  set l := (pbwBasis bas).repr u with hl
  have hsum : ev bas u = Finsupp.linearCombination K
      (fun a => ev bas (pbwMonomial bas a)) l := by
    conv_lhs => rw [hrepr]
    rw [Module.Basis.repr_symm_apply, Finsupp.linearCombination_apply,
      Finsupp.linearCombination_apply, map_finsuppSum]
    exact Finsupp.sum_congr fun a _ => by rw [map_smul, pbwBasis_apply, pbwMonomial_eq_ofFn]
  have hzero : Finsupp.linearCombination K
      (fun a => ev bas (pbwMonomial bas a)) l = 0 := by
    rw [← hsum]; exact hu
  have hli := (unitriangular_ev_pbwMonomial bas).linearIndependent Function.injective_id
  have : l = 0 := linearIndependent_iff.mp hli l hzero
  have : (pbwBasis bas).repr u = 0 := this
  simpa using congrArg (pbwBasis bas).repr.symm this

theorem ev_surjective (bas : Module.Basis (Fin n) K L) :
    Function.Surjective (ev bas) := by
  rw [← LinearMap.range_eq_top]
  refine top_unique ?_
  rw [← (unitriangular_ev_pbwMonomial bas).span_eq_top Function.surjective_id,
    Submodule.span_le]
  rintro _ ⟨a, rfl⟩
  exact ⟨pbwMonomial bas a, rfl⟩

/-- **`ev` is a linear isomorphism `U(L) ≃ₗ[K] Poly K n`.** -/
noncomputable def evEquiv (bas : Module.Basis (Fin n) K L) :
    UniversalEnvelopingAlgebra K L ≃ₗ[K] Poly K n :=
  LinearEquiv.ofBijective (ev bas) ⟨ev_injective bas, ev_surjective bas⟩

@[simp] theorem evEquiv_apply (bas : Module.Basis (Fin n) K L)
    (u : UniversalEnvelopingAlgebra K L) : evEquiv bas u = ev bas u := rfl

end Submission.Ado.PBW
