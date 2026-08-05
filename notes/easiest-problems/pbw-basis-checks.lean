import Submission.Ado.PBW.Basis2
open Submission.Ado.PBW UniversalEnvelopingAlgebra

universe u
variable {K L : Type u} [Field K] [LieRing L] [LieAlgebra K L] {n : ℕ}

-- (1) It really is a `Module.Basis` of `U(L)` indexed by exponent vectors.
noncomputable example (bas : Module.Basis (Fin n) K L) :
    Module.Basis (Fin n →₀ ℕ) K (UniversalEnvelopingAlgebra K L) := pbwBasis bas

-- (2) Its `0`-th member is `1`.
example (bas : Module.Basis (Fin n) K L) : pbwBasis bas 0 = 1 := by
  rw [pbwBasis_apply]; simp

-- (3) NON-VACUITY: for a nonzero Lie algebra `U(L)` is infinite-dimensional over `K`,
--     because the basis is indexed by the infinite set of exponent vectors.
example (bas : Module.Basis (Fin (n + 1)) K L) :
    ¬ Module.Finite K (UniversalEnvelopingAlgebra K L) := by
  intro hfin
  haveI : Infinite (Fin (n + 1) →₀ ℕ) :=
    Infinite.of_injective (fun k : ℕ => Finsupp.single (0 : Fin (n + 1)) k)
      (fun a b hab => by simpa using congrArg (fun f : Fin (n + 1) →₀ ℕ => f 0) hab)
  haveI := Module.Finite.finite_basis (pbwBasis bas)
  exact not_finite (Mon (n + 1))

-- (4) The two halves are the honest statements.
example (bas : Module.Basis (Fin n) K L) :
    LinearIndependent K fun a : Mon n =>
      ((List.finRange n).map fun i => (ι K (bas i) : UniversalEnvelopingAlgebra K L) ^ a i).prod :=
  linearIndependent_pbwMonomial bas

example (bas : Module.Basis (Fin n) K L) :
    Submodule.span K (Set.range fun a : Mon n =>
      ((List.finRange n).map fun i =>
        (ι K (bas i) : UniversalEnvelopingAlgebra K L) ^ a i).prod) = ⊤ :=
  span_range_pbwMonomial bas
