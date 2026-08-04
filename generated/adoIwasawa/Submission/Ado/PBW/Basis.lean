import Submission.Ado.Port.Nilpotent
import Submission.Ado.Truncation

/-!
# Birkhoff's embedding theorem, via the ported nilpotent case

This file was originally intended to hold the Poincaré–Birkhoff–Witt basis
theorem. It does not: the linear-independence half of PBW turned out to be
unnecessary for Ado's theorem.

Instead, the nilpotent case of Ado's theorem is obtained from the port in
`Submission/Ado/Port/`, which is a mechanical port of
<https://github.com/Komyyy/ado> by Miyahara Kō (Apache 2.0). That development
replaces the PBW basis by an explicit filtration of the tensor algebra
(`lengthSubmodule`, `depthSubmodule`, `nilSubmodule`), so that only the
*spanning* half of PBW — already available here as
`Submission.Ado.iSup_gen_pow_eq_top` — is needed; faithfulness comes from the
induction hypothesis rather than from injectivity of `ι`.

The single result exported here is the translation of the ported
`LieAlgebra.IsAdo` into the `Submission.Ado.HasFaithfulFinRep` interface used
by the rest of this development.

## A warning about the statement this file was asked to prove

The originally requested statement

```
theorem ι_notMem_genPow_two {x : L} (h : ι K x ∈ gen K L ^ 2) : x = 0
```

is **false** for every non-abelian `L`: since `ι` is a Lie morphism,
`ι ⁅x, y⁆ = ι x * ι y - ι y * ι x ∈ gen K L ^ 2`, and `augPow K L 2` contains
`gen K L ^ 2`. See `Submission.Ado.ι_lie_mem_genPow_two` below, which records
the counterexample. The statement that Birkhoff's theorem actually needs is
`ι x ∈ augPow K L k → x = 0` for `k` exceeding the nilpotency class of `L`, and
that is bypassed entirely by the route taken here.
-/

universe u

namespace Submission.Ado

open UniversalEnvelopingAlgebra LieAlgebra LieModule

attribute [local instance 100] LieRing.ofAssociativeRing

variable {K L : Type u} [Field K] [LieRing L] [LieAlgebra K L]

/-- **The requested statement `ι x ∈ gen K L ^ 2 → x = 0` is false.** For any
`x y : L` the element `ι ⁅x, y⁆` lies in `gen K L ^ 2`, hence in
`augPow K L 2`. -/
theorem ι_lie_mem_genPow_two (x y : L) :
    (ι K ⁅x, y⁆ : UniversalEnvelopingAlgebra K L) ∈ gen K L ^ 2 := by
  have hx : (ι K x : UniversalEnvelopingAlgebra K L) ∈ gen K L := ι_mem_gen K L x
  have hy : (ι K y : UniversalEnvelopingAlgebra K L) ∈ gen K L := ι_mem_gen K L y
  have h : (ι K ⁅x, y⁆ : UniversalEnvelopingAlgebra K L)
      = ι K x * ι K y - ι K y * ι K x := by
    have := (ι K : L →ₗ⁅K⁆ UniversalEnvelopingAlgebra K L).map_lie x y
    rwa [LieRing.of_associative_ring_bracket] at this
  rw [h, pow_two]
  exact Submodule.sub_mem _ (Submodule.mul_mem_mul hx hy) (Submodule.mul_mem_mul hy hx)

theorem ι_lie_mem_augPow_two (x y : L) :
    (ι K ⁅x, y⁆ : UniversalEnvelopingAlgebra K L) ∈ augPow K L 2 :=
  genPow_le_augPow K L (le_refl 2) (ι_lie_mem_genPow_two x y)

/-- Any `LieAlgebra.IsAdo` witness gives a `HasFaithfulFinRep` witness: the
faithful finite-dimensional module `AdoSpace K L` is turned into a Lie algebra
morphism into `Module.End K (AdoSpace K L)` by `LieModule.toEnd`. -/
theorem hasFaithfulFinRep_of_isAdo [IsAdo K L] : HasFaithfulFinRep K L :=
  ⟨AdoSpace K L, inferInstance, inferInstance, inferInstance,
    LieModule.toEnd K L (AdoSpace K L), IsFaithful.injective_toEnd⟩

/-- **Ado's theorem for finite-dimensional nilpotent Lie algebras**, over an
arbitrary field. This is the substitute for Birkhoff's embedding theorem: it
supplies a faithful finite-dimensional representation of a nilpotent `L`
directly, with no reference to `U(L)`. -/
theorem hasFaithfulFinRep_of_isNilpotent [FiniteDimensional K L]
    [LieRing.IsNilpotent L] : HasFaithfulFinRep K L :=
  hasFaithfulFinRep_of_isAdo

/-- The stronger form kept by the ported development: the faithful module of a
nilpotent Lie algebra is moreover a nilpotent Lie module. This is what the
extension step of §4 needs in place of `U(L) ⧸ J(L) ^ k`. -/
theorem exists_faithful_nilpotent_rep [FiniteDimensional K L]
    [LieRing.IsNilpotent L] :
    ∃ (V : Type u) (_ : AddCommGroup V) (_ : Module K V) (_ : FiniteDimensional K V)
      (_ : LieRingModule L V) (_ : LieModule K L V),
      LieModule.IsNilpotent L V ∧ Function.Injective (LieModule.toEnd K L V) :=
  ⟨AdoSpace K L, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, IsFaithful.injective_toEnd⟩

end Submission.Ado
