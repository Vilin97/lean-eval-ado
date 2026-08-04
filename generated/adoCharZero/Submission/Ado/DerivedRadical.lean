import ChallengeDeps

/-!
# The nilpotency of `⁅L, L⁆ ⊓ radical L`

Let `K` be a field of characteristic zero and let `L` be a finite-dimensional Lie algebra over `K`.
This file proves the classical structure result that the ideal `⁅L, L⁆ ⊓ radical L` is a nilpotent
Lie algebra, together with the immediate consequence that `⁅radical L, radical L⁆` is nilpotent
(so that `radical L` is abelian modulo a nilpotent ideal).

## Main results

* `Submission.Ado.isNilpotent_of_le_derived_of_le_radical`: any Lie ideal of `L` contained both in
  `⁅L, L⁆` and in `radical L` is a nilpotent Lie algebra.
* `Submission.Ado.isNilpotent_derived_inf_radical`: `⁅L, L⁆ ⊓ radical L` is nilpotent.
* `Submission.Ado.isNilpotent_derived_radical`: `⁅radical L, radical L⁆` is nilpotent.

Note that `LieRing.IsNilpotent ↥I` is nilpotency of `I` *as a Lie algebra*, i.e. it is
`LieModule.IsNilpotent ↥I ↥I` and not the stronger `LieModule.IsNilpotent L ↥I`.

## Implementation notes

The heart of the argument is `Submission.Ado.isNilpotent_toEnd_aux`: over an algebraically closed
field of characteristic zero, if `I` is a solvable Lie ideal of `L` and `V` is a finite-dimensional
`L`-module, then every `x ∈ ⁅L, L⁆ ⊓ I` acts nilpotently on `V`. This is proved by induction on
`Module.finrank K V`. Lie's theorem (`LieModule.exists_nontrivial_weightSpace_of_isSolvable`)
supplies a weight `χ` of the solvable Lie algebra `I` on `V`; because `I` is an *ideal*, the
corresponding weight space is in fact an `L`-submodule `W` (`LieModule.weightSpaceOfIsLieTower`).
On `W` the element `x` acts as the scalar `χ x`, whose trace `χ x • finrank K W` vanishes because
`x ∈ ⁅L, L⁆`; characteristic zero then forces `χ x = 0`. So `x` kills `W` and, by induction, acts
nilpotently on `V ⧸ W`, hence nilpotently on `V`.

The general characteristic-zero case is deduced by base change to `AlgebraicClosure K`, using
`LieAlgebra.derivedSeriesOfIdeal_baseChange` to see that the base change of a solvable ideal is
solvable, and injectivity of `Module.End.baseChangeHom` to descend nilpotency. Finally Engel's
theorem (`LieAlgebra.isNilpotent_iff_forall`) converts `ad`-nilpotency into nilpotency of the Lie
algebra itself.
-/

universe u v w

namespace Submission.Ado

open LieAlgebra LieModule LieSubmodule Module

section AlgClosed

variable {K : Type u} {L : Type v} [Field K] [CharZero K] [IsAlgClosed K]
  [LieRing L] [LieAlgebra K L]

/-- Over an algebraically closed field of characteristic zero, an element of a solvable ideal
which also lies in the derived algebra acts nilpotently on every finite-dimensional module. -/
private theorem isNilpotent_toEnd_aux (I : LieIdeal K L) [LieAlgebra.IsSolvable I] (n : ℕ) :
    ∀ (V : Type w) [AddCommGroup V] [Module K V] [LieRingModule L V] [LieModule K L V]
      [FiniteDimensional K V], finrank K V ≤ n →
      ∀ x ∈ LieAlgebra.derivedSeries K L 1, x ∈ I →
      IsNilpotent (LieModule.toEnd K L V x) := by
  induction n with
  | zero =>
    intro V _ _ _ _ _ hle x _ _
    rcases subsingleton_or_nontrivial V with _ | _
    · exact ⟨1, by ext v; exact Subsingleton.elim _ _⟩
    · exact absurd hle (by simp [Module.finrank_pos.ne'])
  | succ n ih =>
    intro V _ _ _ _ _ hle x hx1 hx2
    rcases subsingleton_or_nontrivial V with _ | _
    · exact ⟨1, by ext v; exact Subsingleton.elim _ _⟩
    obtain ⟨χ, hχ⟩ := LieModule.exists_nontrivial_weightSpace_of_isSolvable K (↥I) V
    set W : LieSubmodule K L V := LieModule.weightSpaceOfIsLieTower K V ⇑χ
    have hWmem : ∀ v ∈ W, ∀ y : ↥I, ⁅y, v⁆ = χ y • v := by
      intro v hv y
      have hv' : v ∈ LieModule.weightSpace V ⇑χ := hv
      exact (LieModule.mem_weightSpace _ v).mp hv' y
    have hWnt : Nontrivial ↥W := hχ
    -- `x` acts on `W` as the scalar `χ x`
    have hact : LieModule.toEnd K L (↥W) x = χ ⟨x, hx2⟩ • (LinearMap.id : Module.End K ↥W) := by
      ext w
      have := hWmem (w : V) w.2 ⟨x, hx2⟩
      simpa using this
    -- its trace vanishes since `x ∈ ⁅L, L⁆`
    have htr : LinearMap.trace K ↥W (LieModule.toEnd K L (↥W) x) = 0 := by
      refine LieModule.trace_toEnd_eq_zero_of_mem_lcs K L (↥W) le_rfl ?_
      have : LieAlgebra.derivedSeries K L 1 = LieModule.lowerCentralSeries K L L 1 := by
        simp [LieAlgebra.derivedSeries, derivedSeriesOfIdeal, LieModule.lowerCentralSeries]
      rwa [this] at hx1
    -- hence the scalar is zero, and `x` annihilates `W`
    have hχx : χ ⟨x, hx2⟩ = 0 := by
      rw [hact, map_smul, LinearMap.trace_id] at htr
      have hne : (finrank K ↥W : K) ≠ 0 := Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
      simpa [hne] using htr
    have hzero : LieModule.toEnd K L (↥W) x = 0 := by rw [hact, hχx, zero_smul]
    have hann : ∀ v ∈ W, ⁅x, v⁆ = (0 : V) := by
      intro v hv
      have h1 : (LieModule.toEnd K L (↥W) x) ⟨v, hv⟩ = 0 := by rw [hzero]; rfl
      simpa using congrArg Subtype.val h1
    -- the quotient has smaller dimension, so the inductive hypothesis applies
    have hfr : finrank K (V ⧸ W) ≤ n := by
      have h1 : finrank K (V ⧸ W) + finrank K ↥W = finrank K V :=
        Submodule.finrank_quotient_add_finrank W.toSubmodule
      have h2 : 0 < finrank K ↥W := Module.finrank_pos
      omega
    obtain ⟨m, hm⟩ := ih (V ⧸ W) hfr x hx1 hx2
    refine ⟨m + 1, ?_⟩
    have key : ∀ (k : ℕ) (u : V),
        (LieModule.toEnd K L (V ⧸ W) x ^ k) (LieSubmodule.Quotient.mk (N := W) u)
          = LieSubmodule.Quotient.mk (N := W) ((LieModule.toEnd K L V x ^ k) u) := by
      intro k
      induction k with
      | zero => intro u; simp
      | succ k hk =>
        intro u
        rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply]
        rw [show (LieModule.toEnd K L (V ⧸ W) x) (LieSubmodule.Quotient.mk (N := W) u)
              = LieSubmodule.Quotient.mk (N := W) ((LieModule.toEnd K L V x) u) from rfl]
        exact hk _
    ext v
    have hmem : (LieModule.toEnd K L V x ^ m) v ∈ W := by
      rw [← LieSubmodule.Quotient.mk_eq_zero', ← key m v, hm]
      rfl
    rw [pow_succ', Module.End.mul_apply]
    simpa using hann _ hmem

/-- The algebraically closed case, in the form we shall use it. -/
private theorem isNilpotent_toEnd_of_isAlgClosed (I : LieIdeal K L) [LieAlgebra.IsSolvable I]
    (V : Type w) [AddCommGroup V] [Module K V] [LieRingModule L V] [LieModule K L V]
    [FiniteDimensional K V] {x : L} (hx1 : x ∈ LieAlgebra.derivedSeries K L 1) (hx2 : x ∈ I) :
    IsNilpotent (LieModule.toEnd K L V x) :=
  isNilpotent_toEnd_aux I (finrank K V) V le_rfl x hx1 hx2

end AlgClosed

section Descent

open TensorProduct

variable {K : Type u} {L : Type v} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L]

/-- If `I` is a solvable Lie ideal of `L`, then every element of `⁅L, L⁆ ⊓ I` is `ad`-nilpotent. -/
private theorem isNilpotent_ad_of_mem_derived_of_mem (I : LieIdeal K L)
    [LieAlgebra.IsSolvable I] {x : L} (hx1 : x ∈ LieAlgebra.derivedSeries K L 1) (hx2 : x ∈ I) :
    IsNilpotent (LieAlgebra.ad K L x) := by
  set A := AlgebraicClosure K
  have _i : CharZero A := charZero_of_injective_algebraMap (algebraMap K A).injective
  have _i2 : LieAlgebra.IsSolvable ↥(I.baseChange A) := by
    obtain ⟨k, hk⟩ := LieAlgebra.IsSolvable.solvable (R := K) (L := ↥I)
    rw [LieIdeal.derivedSeries_eq_bot_iff] at hk
    refine (LieAlgebra.isSolvable_iff A _).mpr ⟨k, ?_⟩
    rw [LieIdeal.derivedSeries_eq_bot_iff, LieAlgebra.derivedSeriesOfIdeal_baseChange, hk,
      LieSubmodule.baseChange_bot]
  have hm1 : (1 : A) ⊗ₜ[K] x ∈ LieAlgebra.derivedSeries A (A ⊗[K] L) 1 := by
    rw [LieAlgebra.derivedSeries_baseChange]
    exact Submodule.tmul_mem_baseChange_of_mem 1 hx1
  have hm2 : (1 : A) ⊗ₜ[K] x ∈ I.baseChange A := Submodule.tmul_mem_baseChange_of_mem 1 hx2
  have hnil : IsNilpotent
      (LieModule.toEnd A (A ⊗[K] L) (A ⊗[K] L) ((1 : A) ⊗ₜ[K] x)) :=
    isNilpotent_toEnd_of_isAlgClosed (I.baseChange A) (A ⊗[K] L) hm1 hm2
  rw [LieModule.toEnd_baseChange] at hnil
  have hbc_inj : Function.Injective (Module.End.baseChangeHom K A L) :=
    LinearMap.baseChangeHom_injective K L A
  rw [← IsNilpotent.map_iff hbc_inj]
  exact hnil

/-- Any Lie ideal contained in both `⁅L, L⁆` and the radical is a nilpotent Lie algebra. -/
theorem isNilpotent_of_le_derived_of_le_radical (J : LieIdeal K L)
    (h1 : J ≤ LieAlgebra.derivedSeries K L 1) (h2 : J ≤ LieAlgebra.radical K L) :
    LieRing.IsNilpotent ↥J := by
  rw [LieAlgebra.isNilpotent_iff_forall (R := K)]
  intro y
  exact LieSubalgebra.isNilpotent_ad_of_isNilpotent_ad (J : LieSubalgebra K L)
    (isNilpotent_ad_of_mem_derived_of_mem (LieAlgebra.radical K L) (h1 y.2) (h2 y.2))

end Descent

section Main

variable {K : Type u} {L : Type v} [Field K] [LieRing L] [LieAlgebra K L]

private lemma derivedSeries_one :
    LieAlgebra.derivedSeries K L 1 = ⁅(⊤ : LieIdeal K L), (⊤ : LieIdeal K L)⁆ := rfl

/-- `⁅L, L⁆ ⊓ radical L` is a nilpotent Lie algebra. -/
theorem isNilpotent_derived_inf_radical [CharZero K] [FiniteDimensional K L] :
    LieRing.IsNilpotent
      ↥(⁅(⊤ : LieIdeal K L), (⊤ : LieIdeal K L)⁆ ⊓ LieAlgebra.radical K L) :=
  isNilpotent_of_le_derived_of_le_radical _ (by rw [derivedSeries_one]; exact inf_le_left)
    inf_le_right

/-- Consequently the radical modulo it is abelian: `⁅rad L, rad L⁆` is nilpotent. -/
theorem isNilpotent_derived_radical [CharZero K] [FiniteDimensional K L] :
    LieRing.IsNilpotent ↥⁅LieAlgebra.radical K L, LieAlgebra.radical K L⁆ :=
  isNilpotent_of_le_derived_of_le_radical _
    (by rw [derivedSeries_one]; exact LieSubmodule.mono_lie le_top le_top)
    (LieSubmodule.lie_le_right _ _)

end Main

end Submission.Ado
