import Submission.Ado.PBW.Injective
open Submission.Ado.PBW UniversalEnvelopingAlgebra

-- 1. The bracket on `Module.End` really is the commutator (not some trivial instance).
example (K M : Type) [Field K] [AddCommGroup M] [Module K M] (f g : Module.End K M) :
    ⁅f, g⁆ = f * g - g * f := rfl

-- 2. `rhoL_lie` unfolds to the honest commutator identity, applied pointwise.
example {K L : Type} [Field K] [LieRing L] [LieAlgebra K L] {n : ℕ}
    (bas : Module.Basis (Fin n) K L) (x y : L) (f : Poly K n) :
    rhoL bas x (rhoL bas y f) - rhoL bas y (rhoL bas x f) = rhoL bas ⁅x, y⁆ f := by
  have h := rhoL_lie bas x y
  have := congrArg (fun t : Module.End K (Poly K n) => t f) h
  simpa [LieRing.of_associative_ring_bracket, Module.End.mul_apply,
    LinearMap.sub_apply] using this

-- 3. The action is nondegenerate: distinct basis vectors go to distinct variables.
example {K L : Type} [Field K] [LieRing L] [LieAlgebra K L] {n : ℕ}
    (bas : Module.Basis (Fin n) K L) (i j : Fin n) (h : i ≠ j) :
    rhoL bas (bas i) (mono 0) ≠ rhoL bas (bas j) (mono 0) := by
  rw [rhoL_basis, rhoL_basis, rho_mono, rho_mono,
    act_of_aligned (aligned_zero i), act_of_aligned (aligned_zero j), zero_add, zero_add]
  intro hc
  exact h (e_injective (Finsupp.single_left_injective one_ne_zero hc))

-- 4. Nontriviality: `U(L)` of a nonzero f.d. Lie algebra has a nonzero element in the image of ι.
example {K L : Type} [Field K] [LieRing L] [LieAlgebra K L] [FiniteDimensional K L]
    (x : L) (hx : x ≠ 0) : (ι K x : UniversalEnvelopingAlgebra K L) ≠ 0 := by
  intro hc
  exact hx (ι_injective (by simpa using hc))
