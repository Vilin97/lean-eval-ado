import Submission.Ado.PBW.Env

/-!
# `ι : L → U(L)` is injective

The cheapest consequence of the PBW module: the canonical map from a
finite-dimensional Lie algebra to its universal enveloping algebra is injective.

Mathlib proves nothing of the kind — `Mathlib/Algebra/Lie/UniversalEnveloping.lean`
stops at the universal property — and `Mathlib/Algebra/Lie/Free.lean:44` records
that the missing ingredient is exactly the Poincaré–Birkhoff–Witt theorem.

The proof needs only clause (A) of the construction: `ρ(xᵢ)` sends the constant
monomial `z⁰` to the variable `zᵢ`, and the `zᵢ` are distinct basis vectors of
the polynomial module. So the composite `L → U(L) → Poly K n`, `x ↦ x • z⁰`,
is already injective.
-/

universe u

namespace Submission.Ado.PBW

open UniversalEnvelopingAlgebra

variable {K : Type u} [Field K] {L : Type u} [LieRing L] [LieAlgebra K L] {n : ℕ}

/-- The unit exponent vectors are pairwise distinct. -/
theorem e_injective : Function.Injective (e : Fin n → Mon n) := by
  intro i j hij
  by_contra hne
  have h1 : (e i : Mon n) i = 1 := e_apply_self i
  have h2 : (e j : Mon n) i = 0 := e_apply_of_ne (Ne.symm hne)
  rw [hij, h2] at h1
  exact one_ne_zero h1.symm

/-- `ev` sends `ι x` to the linear form `∑ᵢ (repr x)ᵢ · zᵢ`. -/
theorem ev_ι (bas : Module.Basis (Fin n) K L) (x : L) :
    ev bas (ι K x) = ∑ i : Fin n, bas.repr x i • (mono (e i) : Poly K n) := by
  rw [ev_apply, envAction_ι, rhoL_apply]
  simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply, rho_mono]
  exact Finset.sum_congr rfl fun i _ => by
    rw [act_of_aligned (aligned_zero i), zero_add]

/-- Evaluating that linear form at the exponent vector `eⱼ` recovers the `j`-th
coordinate. -/
theorem ev_ι_coeff (bas : Module.Basis (Fin n) K L) (x : L) (j : Fin n) :
    (ev bas (ι K x)) (e j) = bas.repr x j := by
  rw [ev_ι]
  simp only [Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.coe_smul, Pi.smul_apply,
    mono, Finsupp.single_apply, smul_eq_mul]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    rw [if_neg (fun h => hij (e_injective h)), mul_zero]
  · intro h; exact absurd (Finset.mem_univ j) h

/-- **`ι` is injective**, for a Lie algebra with a finite basis. -/
theorem ι_injective_of_basis (bas : Module.Basis (Fin n) K L) :
    Function.Injective (ι K : L → UniversalEnvelopingAlgebra K L) := by
  intro x y hxy
  refine bas.repr.injective (Finsupp.ext fun j => ?_)
  rw [← ev_ι_coeff bas x j, ← ev_ι_coeff bas y j, hxy]

/-- **`ι : L → U(L)` is injective** for every finite-dimensional Lie algebra over
a field. -/
theorem ι_injective [FiniteDimensional K L] :
    Function.Injective (ι K : L → UniversalEnvelopingAlgebra K L) :=
  ι_injective_of_basis (Module.finBasis K L)

end Submission.Ado.PBW
