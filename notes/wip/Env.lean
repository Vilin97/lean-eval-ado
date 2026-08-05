import Submission.Ado.PBW.Module

/-!
# From the PBW module to the universal enveloping algebra

Once the Lie relation (C) is available — as the hypothesis `hlie` below, which
`Submission.Ado.PBW.rhoL_lie` supplies — the action `rhoL` is a morphism of Lie
algebras `L →ₗ⁅K⁆ Module.End K (Poly K n)`, so the universal property of
`UniversalEnvelopingAlgebra` turns it into an algebra morphism
`U(L) →ₐ[K] Module.End K (Poly K n)`.

Evaluating at the constant monomial `z^0` gives the *evaluation map*

```
ev : U(L) → Poly K n,   ev u = (u • 1)
```

which sends the ordered monomial `ι(x_{i₁}) ⋯ ι(x_{i_k})` (indices nondecreasing)
to `z^{i₁} ⋯ z^{i_k}` plus terms of lower degree. Together with
`Submission.Ado.sortedSpan_eq_top` (the spanning half of PBW, proved in
`Submission/Ado/PBW/Sorting.lean`) this makes `ev` a linear isomorphism — the
Poincaré–Birkhoff–Witt theorem.

Everything in this file is stated with the Lie relation as an explicit
hypothesis, so the file is `sorry`-free and becomes unconditional the moment
`rhoL_lie` is closed.
-/

universe u

namespace Submission.Ado.PBW

open UniversalEnvelopingAlgebra

variable {K : Type u} [Field K] {L : Type u} [LieRing L] [LieAlgebra K L] {n : ℕ}

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The PBW action packaged as a morphism of Lie algebras. -/
noncomputable def rhoLie (bas : Module.Basis (Fin n) K L)
    (hlie : ∀ x y : L, ⁅rhoL bas x, rhoL bas y⁆ = rhoL bas ⁅x, y⁆) :
    L →ₗ⁅K⁆ Module.End K (Poly K n) where
  toFun := rhoL bas
  map_add' := map_add _
  map_smul' := map_smul _
  map_lie' {x y} := (hlie x y).symm

@[simp] theorem rhoLie_apply (bas : Module.Basis (Fin n) K L)
    (hlie : ∀ x y : L, ⁅rhoL bas x, rhoL bas y⁆ = rhoL bas ⁅x, y⁆) (x : L) :
    rhoLie bas hlie x = rhoL bas x := rfl

/-- The induced algebra morphism out of the universal enveloping algebra. -/
noncomputable def envAction (bas : Module.Basis (Fin n) K L)
    (hlie : ∀ x y : L, ⁅rhoL bas x, rhoL bas y⁆ = rhoL bas ⁅x, y⁆) :
    UniversalEnvelopingAlgebra K L →ₐ[K] Module.End K (Poly K n) :=
  UniversalEnvelopingAlgebra.lift K (rhoLie bas hlie)

@[simp] theorem envAction_ι (bas : Module.Basis (Fin n) K L)
    (hlie : ∀ x y : L, ⁅rhoL bas x, rhoL bas y⁆ = rhoL bas ⁅x, y⁆) (x : L) :
    envAction bas hlie (ι K x) = rhoL bas x := by
  simp [envAction]

/-- The evaluation map `u ↦ u • z⁰`. -/
noncomputable def ev (bas : Module.Basis (Fin n) K L)
    (hlie : ∀ x y : L, ⁅rhoL bas x, rhoL bas y⁆ = rhoL bas ⁅x, y⁆) :
    UniversalEnvelopingAlgebra K L →ₗ[K] Poly K n where
  toFun u := envAction bas hlie u (mono 0)
  map_add' u v := by simp
  map_smul' c u := by simp

@[simp] theorem ev_apply (bas : Module.Basis (Fin n) K L)
    (hlie : ∀ x y : L, ⁅rhoL bas x, rhoL bas y⁆ = rhoL bas ⁅x, y⁆)
    (u : UniversalEnvelopingAlgebra K L) :
    ev bas hlie u = envAction bas hlie u (mono 0) := rfl

@[simp] theorem ev_one (bas : Module.Basis (Fin n) K L)
    (hlie : ∀ x y : L, ⁅rhoL bas x, rhoL bas y⁆ = rhoL bas ⁅x, y⁆) :
    ev bas hlie 1 = mono 0 := by simp [ev]

/-- `ev` on a generator is the corresponding variable. -/
theorem ev_ι_basis (bas : Module.Basis (Fin n) K L)
    (hlie : ∀ x y : L, ⁅rhoL bas x, rhoL bas y⁆ = rhoL bas ⁅x, y⁆) (i : Fin n) :
    ev bas hlie (ι K (bas i)) = mono (e i) := by
  rw [ev_apply, envAction_ι, rhoL_basis, rho_mono, act_of_aligned (aligned_zero i), zero_add]

/-- `ev` is multiplicative in the sense needed to peel off a leading generator:
`ev (ι x * u) = ρ(x) (ev u)`. This is what drives the triangularity induction. -/
theorem ev_ι_mul (bas : Module.Basis (Fin n) K L)
    (hlie : ∀ x y : L, ⁅rhoL bas x, rhoL bas y⁆ = rhoL bas ⁅x, y⁆)
    (x : L) (u : UniversalEnvelopingAlgebra K L) :
    ev bas hlie (ι K x * u) = rhoL bas x (ev bas hlie u) := by
  simp only [ev_apply, map_mul, Module.End.mul_apply, envAction_ι]

end Submission.Ado.PBW
