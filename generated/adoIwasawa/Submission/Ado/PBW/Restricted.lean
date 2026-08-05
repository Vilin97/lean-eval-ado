import Submission.Ado.PBW.PowComm
import Submission.Ado.PBW.DivMod
import Submission.Ado.PBW.Unitriangular
import Submission.Ado.PBW.Injective

/-!
# The restricted-monomial basis of the polynomial module

Fix `q ≥ 2` and coefficients `μ`, and let `Cⱼ` be the operators of
`Submission/Ado/PBW/Pow.lean`, by which the `p`-polynomials `cⱼ` act on
`Poly K n`. By `bigCpow_mono_triangular`,

```
C^m (z^b) = z^(b + q·m) + (terms of degree < |b| + q|m|)
```

and by `Submission/Ado/PBW/DivMod.lean` the map `(b, m) ↦ b + q·m` is a bijection
from restricted exponent vectors times arbitrary ones onto all exponent vectors.
So the family

```
fam (b, m) := C^m (z^b),    b restricted
```

is unitriangular over a bijection, hence a **basis** of `Poly K n`.

The consequence the characteristic-`p` argument needs is the *separation* lemma
`coeff_eq_zero_of_mem_bigCRange`: a `K`-combination of the degree-one monomials
`z₁, …, zₙ` that lies in `∑ⱼ range Cⱼ` is zero. That is what makes the induced
action on `Poly K n / ∑ⱼ range Cⱼ` faithful.
-/

universe u

namespace Submission.Ado.PBW

open UniversalEnvelopingAlgebra

variable {K : Type u} [Field K] {L : Type u} [LieRing L] [LieAlgebra K L] {n : ℕ}

/-- The index set of the restricted basis: a restricted exponent vector together
with an arbitrary one. -/
abbrev RIndex (q : ℕ) (n : ℕ) : Type := {b : Mon n // IsRestricted q b} × Mon n

variable (bas : Module.Basis (Fin n) K L) (q : ℕ) (mu : Fin n → ℕ → K)

/-- The restricted-basis family `C^m (z^b)`. -/
noncomputable def fam (s : RIndex q n) : Poly K n :=
  bigCpow bas q mu s.2 (mono s.1)

@[simp] theorem fam_snd_zero (b : {b : Mon n // IsRestricted q b}) :
    fam bas q mu (b, 0) = mono (b : Mon n) := by
  rw [fam, bigCpow_zero]; rfl

/-- The family is unitriangular over the division-with-remainder bijection. -/
theorem fam_unitriangular : Unitriangular (monAdd q) (fam bas q mu) := fun s =>
  bigCpow_mono_triangular' bas q mu s.2 (s.1 : Mon n)

theorem fam_linearIndependent (hq : 0 < q) : LinearIndependent K (fam bas q mu) :=
  (fam_unitriangular bas q mu).linearIndependent (monAdd_injective hq)

theorem fam_span (hq : 0 < q) : Submodule.span K (Set.range (fam bas q mu)) = ⊤ :=
  (fam_unitriangular bas q mu).span_eq_top (monAdd_surjective hq)

/-- **The restricted-monomial basis of `Poly K n`.** -/
noncomputable def restrictedBasis (hq : 0 < q) :
    Module.Basis (RIndex q n) K (Poly K n) :=
  Module.Basis.mk (fam_linearIndependent bas q mu hq)
    (le_of_eq (fam_span bas q mu hq).symm)

@[simp] theorem restrictedBasis_apply (hq : 0 < q) (s : RIndex q n) :
    restrictedBasis bas q mu hq s = fam bas q mu s :=
  Module.Basis.mk_apply _ _ _

/-! ### Separation

The `m = 0` part of the family and the `m ≠ 0` part span complementary pieces. -/

theorem disjoint_span_fam (hq : 0 < q) :
    Disjoint (Submodule.span K (fam bas q mu '' {s : RIndex q n | s.2 = 0}))
      (Submodule.span K (fam bas q mu '' {s : RIndex q n | s.2 ≠ 0})) :=
  (fam_linearIndependent bas q mu hq).disjoint_span_image
    (by simp [Set.disjoint_left])

/-- The span of the `m ≠ 0` part of the family contains the range of every `Cⱼ`. -/
theorem range_bigC_le_span (hc : CentralElts bas q mu) (hq : 0 < q) (j : Fin n) :
    LinearMap.range (bigC bas q mu j)
      ≤ Submodule.span K (fam bas q mu '' {s : RIndex q n | s.2 ≠ 0}) := by
  rintro _ ⟨f, rfl⟩
  -- expand `f` in the basis and push `Cⱼ` through
  have hspan : f ∈ Submodule.span K (Set.range (fam bas q mu)) := by
    rw [fam_span bas q mu hq]; exact Submodule.mem_top
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hspan
  · rintro _ ⟨s, rfl⟩
    refine Submodule.subset_span ⟨(s.1, s.2 + e j), ?_, ?_⟩
    · intro hzero
      have hz : s.2 + e j = 0 := hzero
      have hj : (s.2 + e j) j = 0 := by simp [hz]
      rw [Finsupp.add_apply, e_apply_self] at hj
      omega
    · rw [fam, fam, ← Module.End.mul_apply, bigC_mul_bigCpow bas q mu hc]
  · simp
  · intro x y _ _ hx hy
    rw [map_add]; exact Submodule.add_mem _ hx hy
  · intro c x _ hx
    rw [map_smul]; exact Submodule.smul_mem _ _ hx

/-- **Separation.** A `K`-combination of the degree-one monomials that lies in the
sum of the ranges of the `Cⱼ` is zero. -/
theorem coeff_eq_zero_of_mem_bigCRange (hc : CentralElts bas q mu) (hq : 2 ≤ q)
    (lam : Fin n → K)
    (hmem : (∑ i : Fin n, lam i • (mono (e i) : Poly K n))
      ∈ ⨆ j : Fin n, LinearMap.range (bigC bas q mu j)) (i : Fin n) : lam i = 0 := by
  have hq0 : 0 < q := lt_of_lt_of_le two_pos hq
  -- the combination lies in the `m = 0` span …
  have h0 : (∑ i : Fin n, lam i • (mono (e i) : Poly K n))
      ∈ Submodule.span K (fam bas q mu '' {s : RIndex q n | s.2 = 0}) := by
    refine Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ ?_
    refine Submodule.subset_span ⟨(⟨e k, isRestricted_e hq k⟩, 0), rfl, ?_⟩
    simp
  -- … and in the `m ≠ 0` span
  have h1 : (∑ i : Fin n, lam i • (mono (e i) : Poly K n))
      ∈ Submodule.span K (fam bas q mu '' {s : RIndex q n | s.2 ≠ 0}) := by
    refine (iSup_le fun j => range_bigC_le_span bas q mu hc hq0 j) hmem
  -- so it is zero
  have hzero : (∑ i : Fin n, lam i • (mono (e i) : Poly K n)) = 0 :=
    (Submodule.disjoint_def.mp (disjoint_span_fam bas q mu hq0)) _ h0 h1
  -- read off the `i`-th coefficient
  have hval : (∑ k : Fin n, lam k • (mono (e k) : Poly K n)) (e i) = lam i := by
    rw [Finsupp.coe_finsetSum, Finset.sum_apply, Finset.sum_eq_single i]
    · simp [mono]
    · intro k _ hk
      simp only [Finsupp.coe_smul, Pi.smul_apply, mono, Finsupp.single_apply, smul_eq_mul]
      rw [if_neg fun h => hk (e_injective h), mul_zero]
    · intro h; exact absurd (Finset.mem_univ i) h
  rw [hzero] at hval
  simpa using hval.symm

end Submission.Ado.PBW
