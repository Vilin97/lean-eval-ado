import Submission.Ado.Basic

/-!
# Ado's theorem in the two extreme cases

Ado's theorem is hard exactly because of the centre: the adjoint representation
is faithful modulo the centre and free of charge, so all the work is in finding
a finite-dimensional representation that separates central elements.

The two extremes are easy and are proved here in full.

* `hasFaithfulFinRep_of_center_trivial` — when the centre is trivial, `ad`
  itself is already faithful.
* `hasFaithfulFinRep_of_isLieAbelian` — when `L` is abelian (so the centre is
  everything, and `ad = 0`), an explicit `(dim L + 1)`-dimensional
  representation works: `L` acts on `K × L` by `(t, y) ↦ (0, t • x)`. Any two
  such endomorphisms compose to zero, so they commute, which is precisely what
  an abelian `L` needs.

The abelian case is the base case of Birkhoff's embedding theorem (§3 of the
informal proof), and it is also the first case where the naive "adjoint
representation" strategy fails completely — for abelian `L` the adjoint
representation is the zero map.
-/

universe u

namespace Submission.Ado

variable {K L : Type u} [Field K] [LieRing L] [LieAlgebra K L]

/-- If the centre of `L` is trivial then the adjoint representation is faithful,
so Ado's theorem holds for `L`. -/
theorem hasFaithfulFinRep_of_center_trivial [FiniteDimensional K L]
    (h : ∀ x : L, (∀ y : L, ⁅x, y⁆ = 0) → x = 0) :
    HasFaithfulFinRep K L :=
  hasFaithfulFinRep_of_center (LieAlgebra.ad K L) fun x _ hx => h x hx

/-- The representation of an abelian Lie algebra `L` on `K × L` given by
`x ↦ ((t, y) ↦ (0, t • x))`. -/
def abelianRep [IsLieAbelian L] : L →ₗ⁅K⁆ Module.End K (K × L) where
  toFun x := (LinearMap.inr K K L).comp (LinearMap.smulRight (LinearMap.fst K K L) x)
  map_add' x y := by
    ext p <;> simp [smul_add]
  map_smul' t x := by
    ext p <;> simp [smul_smul, mul_comm]
  map_lie' {x y} := by
    have hxy : ⁅x, y⁆ = 0 := trivial_lie_zero L L x y
    rw [hxy]
    ext p <;>
      simp [LieRing.of_associative_ring_bracket, Module.End.mul_apply]

@[simp]
theorem abelianRep_apply [IsLieAbelian L] (x : L) (p : K × L) :
    abelianRep x p = (0, p.1 • x) := rfl

/-- The abelian representation is faithful: evaluate at `(1, 0)`. -/
theorem abelianRep_injective [IsLieAbelian L] :
    Function.Injective (abelianRep (K := K) (L := L)) := by
  refine injective_of_map_eq_zero _ fun x hx => ?_
  have h : abelianRep (K := K) x (1, 0) = 0 := by rw [hx]; rfl
  simpa using h

/-- **Ado's theorem for abelian Lie algebras.** Valid over any field, with no
hypothesis on the characteristic. -/
theorem hasFaithfulFinRep_of_isLieAbelian [FiniteDimensional K L] [IsLieAbelian L] :
    HasFaithfulFinRep K L :=
  ⟨K × L, inferInstance, inferInstance, inferInstance, abelianRep, abelianRep_injective⟩

end Submission.Ado
