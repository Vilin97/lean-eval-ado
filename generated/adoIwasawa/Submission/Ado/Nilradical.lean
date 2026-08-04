import ChallengeDeps

/-!
# The nilradical of a Lie algebra

This file develops the *nilradical* of a Lie algebra `L` over a field `K`: the largest ideal of
`L` which is nilpotent **as a Lie algebra**.

The point to be careful about is that `LieRing.IsNilpotent ↥I` (the lower central series of the
Lie algebra `↥I` terminates) is strictly weaker than `LieModule.IsNilpotent L ↥I` (the lower
central series of `↥I` as an `L`-module terminates).  Mathlib already knows the latter notion:
`LieAlgebra.maxNilpotentIdeal` is the `sSup` of the ideals which are nilpotent as `L`-modules.
That is *not* the classical nilradical: for the two-dimensional non-abelian Lie algebra
`⟨h, x⟩`, `⁅h, x⁆ = x`, the ideal `K ∙ x` is abelian, hence nilpotent as a Lie algebra, while
`⁅L, K ∙ x⁆ = K ∙ x`, so it is not nilpotent as an `L`-module.  Consequently
`LieAlgebra.maxNilpotentIdeal` is `⊥` there whereas the nilradical is `K ∙ x`.

## Main definitions

* `Submission.Ado.lcsFrom`: the lower central series of an ideal `A` of `L`, computed as a
  descending chain of ideals *of `L`*, started at an arbitrary ideal.
* `Submission.Ado.nilRadical`: the `sSup` of all ideals which are nilpotent as Lie algebras.

## Main results

* `Submission.Ado.isNilpotent_sup`: a sum of two nilpotent ideals is a nilpotent ideal.
* `Submission.Ado.nilRadicalIsNilpotent`: in the finite-dimensional case the nilradical really is
  nilpotent, so it is the largest nilpotent ideal.
* `Submission.Ado.le_nilRadical`, `Submission.Ado.isNilpotent_iff_le_nilRadical`,
  `Submission.Ado.center_le_nilRadical`, `Submission.Ado.nilRadical_le_radical`.
* `Submission.Ado.nilRadical_map_equiv`: the nilradical is invariant under every automorphism of
  `L`, i.e. it is a characteristic ideal in the automorphism sense.
* `Submission.Ado.nilRadical_stable_inner`: the nilradical is stable under inner derivations.

The stronger statement that the nilradical is stable under *every* `LieDerivation K L L` is **not**
proved here.  The naive argument (for a nilpotent ideal `A` and a derivation `D`, the ideal
`A + D A` is again nilpotent) does not go through at this level of generality: writing `A⁽ᵏ⁾` for
the lower central series of `A` inside `L`, a derivation satisfies only `D (A⁽ᵏ⁾) ≤ A⁽ᵏ⁻¹⁾`, so
`ad (D a)` preserves the filtration without shifting it and no nilpotency of `A + D A` can be read
off from this filtration.

## Implementation notes

For an ideal `A` of `L` write `A⁽ᵏ⁾` for the `k`-th term of the lower central series of `A`
computed inside `L`.  The two useful variants are `lcsFrom A A`, which starts at `A` (so that
`lcsFrom A A k = ⊥` for some `k` exactly says that `↥A` is a nilpotent Lie algebra), and
`lcsFrom A ⊤`, which starts at `⊤`.  Because `A` is an *ideal*, `⁅A, ⊤⁆ ≤ A`, so the two series
interleave and the vanishing of one is equivalent to the vanishing of the other.

The proof that a sum of nilpotent ideals is nilpotent uses the `⊤`-based series: writing
`Aₚ := lcsFrom A ⊤ p` and `B_q := lcsFrom B ⊤ q`, the family `Aₚ ⊓ B_q` satisfies
`⁅A, Aₚ ⊓ B_q⁆ ≤ Aₚ₊₁ ⊓ B_q` and `⁅B, Aₚ ⊓ B_q⁆ ≤ Aₚ ⊓ B_q₊₁` (the second factor is preserved
simply because it is an ideal of `L`).  Hence the `k`-th term of the series of `A ⊔ B` is
contained in `⨆_{p + q = k} Aₚ ⊓ B_q`, which vanishes as soon as `k = m + n` with `A_m = ⊥` and
`B_n = ⊥`.
-/

universe u v

namespace Submission.Ado

open LieAlgebra LieModule

section LowerCentralSeries

variable {R : Type u} {L : Type v} [CommRing R] [LieRing L] [LieAlgebra R L]

/-- `lcsFrom A X k` is the `k`-th term of the lower central series of the ideal `A`, computed as
an ideal of the ambient Lie algebra `L` and started at the ideal `X`. Thus `lcsFrom A X 0 = X`
and `lcsFrom A X (k + 1) = ⁅A, lcsFrom A X k⁆`. -/
def lcsFrom (A X : LieIdeal R L) : ℕ → LieIdeal R L
  | 0 => X
  | k + 1 => ⁅A, lcsFrom A X k⁆

@[simp]
theorem lcsFrom_zero (A X : LieIdeal R L) : lcsFrom A X 0 = X := rfl

@[simp]
theorem lcsFrom_succ (A X : LieIdeal R L) (k : ℕ) :
    lcsFrom A X (k + 1) = ⁅A, lcsFrom A X k⁆ := rfl

theorem lcsFrom_mono_start (A : LieIdeal R L) {X Y : LieIdeal R L} (h : X ≤ Y) :
    ∀ k, lcsFrom A X k ≤ lcsFrom A Y k
  | 0 => h
  | k + 1 => LieSubmodule.mono_lie le_rfl (lcsFrom_mono_start A h k)

theorem lcsFrom_succ_le (A X : LieIdeal R L) (k : ℕ) :
    lcsFrom A X (k + 1) ≤ lcsFrom A X k :=
  LieSubmodule.lie_le_right _ _

theorem lcsFrom_antitone (A X : LieIdeal R L) {i j : ℕ} (h : i ≤ j) :
    lcsFrom A X j ≤ lcsFrom A X i := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  clear h
  induction d with
  | zero => exact le_rfl
  | succ d ih => exact le_trans (lcsFrom_succ_le A X (i + d)) ih

/-- Every term of the lower central series of `A` started at `A` is contained in `A`. -/
theorem lcsFrom_self_le (A : LieIdeal R L) (k : ℕ) : lcsFrom A A k ≤ A := by
  cases k with
  | zero => exact le_rfl
  | succ k => exact LieSubmodule.lie_le_left _ _

/-- The lower central series of the Lie algebra `↥A` is the pullback along `A.incl` of the
lower central series of `A` computed inside `L`. Compare
`LieIdeal.derivedSeries_eq_derivedSeriesOfIdeal_comap`. -/
theorem lowerCentralSeries_eq_comap (A : LieIdeal R L) (k : ℕ) :
    lowerCentralSeries R A A k = (lcsFrom A A k).comap A.incl := by
  induction k with
  | zero => simp [LieIdeal.comap_incl_self]
  | succ k ih =>
    rw [lowerCentralSeries_succ, ih, lcsFrom_succ,
      ← LieIdeal.comap_bracket_incl_of_le A le_rfl (lcsFrom_self_le A k),
      LieIdeal.comap_incl_self]

theorem lowerCentralSeries_map_incl (A : LieIdeal R L) (k : ℕ) :
    LieIdeal.map A.incl (lowerCentralSeries R A A k) = lcsFrom A A k := by
  rw [lowerCentralSeries_eq_comap, LieIdeal.map_comap_incl, inf_eq_right]
  exact lcsFrom_self_le A k

/-- An ideal `A` of `L` is nilpotent as a Lie algebra exactly when its lower central series,
computed inside `L` and started at `A`, reaches `⊥`. -/
theorem isNilpotent_iff_lcsFrom_self (A : LieIdeal R L) :
    LieRing.IsNilpotent A ↔ ∃ k, lcsFrom A A k = ⊥ := by
  rw [LieRing.IsNilpotent, LieModule.isNilpotent_iff R]
  refine exists_congr fun k => ?_
  rw [← lowerCentralSeries_map_incl A k, LieIdeal.map_eq_bot_iff, LieIdeal.ker_incl, le_bot_iff]

theorem lcsFrom_top_succ_le (A : LieIdeal R L) (k : ℕ) :
    lcsFrom A ⊤ (k + 1) ≤ lcsFrom A A k := by
  induction k with
  | zero => exact LieSubmodule.lie_le_left _ _
  | succ k ih => exact LieSubmodule.mono_lie le_rfl ih

/-- An ideal `A` of `L` is nilpotent as a Lie algebra exactly when its lower central series,
computed inside `L` and started at `⊤`, reaches `⊥`. -/
theorem isNilpotent_iff_lcsFrom_top (A : LieIdeal R L) :
    LieRing.IsNilpotent A ↔ ∃ k, lcsFrom A ⊤ k = ⊥ := by
  rw [isNilpotent_iff_lcsFrom_self]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k + 1, le_bot_iff.mp (le_trans (lcsFrom_top_succ_le A k) hk.le)⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, le_bot_iff.mp (le_trans (lcsFrom_mono_start A le_top k) hk.le)⟩

/-- Bracketing distributes over a finite supremum of ideals. -/
theorem lie_finsetSup_le {ι : Type*} (C : LieIdeal R L) (s : Finset ι) (f : ι → LieIdeal R L) :
    ⁅C, s.sup f⁆ ≤ s.sup fun i => ⁅C, f i⁆ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s _ ih =>
    rw [Finset.sup_insert, Finset.sup_insert, LieSubmodule.lie_sup]
    exact sup_le_sup_left ih _

/-- The heart of the matter: the `k`-th term of the lower central series of `A ⊔ B` is contained
in the supremum of the ideals `lcsFrom A ⊤ p ⊓ lcsFrom B ⊤ q` over all `p + q = k`. -/
theorem lcsFrom_sup_le (A B : LieIdeal R L) (k : ℕ) :
    lcsFrom (A ⊔ B) ⊤ k ≤
      (Finset.range (k + 1)).sup fun p => lcsFrom A ⊤ p ⊓ lcsFrom B ⊤ (k - p) := by
  induction k with
  | zero => simp
  | succ k ih =>
    refine le_trans (LieSubmodule.mono_lie le_rfl ih) ?_
    refine le_trans (lie_finsetSup_le _ _ _) (Finset.sup_le fun p hp => ?_)
    have hpk : p ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hp)
    rw [LieSubmodule.sup_lie]
    refine sup_le ?_ ?_
    · have hstep : ⁅A, lcsFrom A ⊤ p ⊓ lcsFrom B ⊤ (k - p)⁆ ≤
          lcsFrom A ⊤ (p + 1) ⊓ lcsFrom B ⊤ (k + 1 - (p + 1)) := by
        rw [show k + 1 - (p + 1) = k - p by omega]
        exact le_inf (LieSubmodule.mono_lie le_rfl inf_le_left)
          (le_trans (LieSubmodule.lie_le_right _ _) inf_le_right)
      exact le_trans hstep
        (Finset.le_sup (f := fun q => lcsFrom A ⊤ q ⊓ lcsFrom B ⊤ (k + 1 - q))
          (Finset.mem_range.mpr (show p + 1 < k + 1 + 1 by omega)))
    · have hstep : ⁅B, lcsFrom A ⊤ p ⊓ lcsFrom B ⊤ (k - p)⁆ ≤
          lcsFrom A ⊤ p ⊓ lcsFrom B ⊤ (k + 1 - p) := by
        rw [show k + 1 - p = (k - p) + 1 by omega]
        exact le_inf (le_trans (LieSubmodule.lie_le_right _ _) inf_le_left)
          (LieSubmodule.mono_lie le_rfl inf_le_right)
      exact le_trans hstep
        (Finset.le_sup (f := fun q => lcsFrom A ⊤ q ⊓ lcsFrom B ⊤ (k + 1 - q))
          (Finset.mem_range.mpr (show p < k + 1 + 1 by omega)))

theorem lcsFrom_sup_eq_bot {A B : LieIdeal R L} {m n : ℕ}
    (hA : lcsFrom A ⊤ m = ⊥) (hB : lcsFrom B ⊤ n = ⊥) :
    lcsFrom (A ⊔ B) ⊤ (m + n) = ⊥ := by
  refine le_bot_iff.mp (le_trans (lcsFrom_sup_le A B (m + n)) (Finset.sup_le fun p hp => ?_))
  have hpk : p ≤ m + n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hp)
  rcases le_or_gt m p with h | h
  · exact le_trans inf_le_left (le_trans (lcsFrom_antitone A ⊤ h) hA.le)
  · exact le_trans inf_le_right
      (le_trans (lcsFrom_antitone B ⊤ (show n ≤ m + n - p by omega)) hB.le)

/-- **Sum of two nilpotent ideals is a nilpotent ideal.**

Note that `LieRing.IsNilpotent ↥I` means that `I` is nilpotent *as a Lie algebra*; this is weaker
than nilpotency of `I` as an `L`-module, so this statement is not an instance of Mathlib's
`LieModule.instIsNilpotentSup`. -/
theorem isNilpotent_sup (I J : LieIdeal R L) [LieRing.IsNilpotent I] [LieRing.IsNilpotent J] :
    LieRing.IsNilpotent ↥(I ⊔ J) := by
  obtain ⟨m, hm⟩ := (isNilpotent_iff_lcsFrom_top I).mp ‹_›
  obtain ⟨n, hn⟩ := (isNilpotent_iff_lcsFrom_top J).mp ‹_›
  exact (isNilpotent_iff_lcsFrom_top _).mpr ⟨m + n, lcsFrom_sup_eq_bot hm hn⟩

theorem isNilpotent_bot : LieRing.IsNilpotent ↥(⊥ : LieIdeal R L) :=
  (isNilpotent_iff_lcsFrom_top _).mpr ⟨1, by simp⟩

end LowerCentralSeries

section NilRadical

variable (K : Type u) (L : Type v) [Field K] [LieRing L] [LieAlgebra K L]

/-- The **nilradical** of a Lie algebra: the supremum of all ideals which are nilpotent as Lie
algebras.  When `L` is finite-dimensional this is the largest nilpotent ideal, see
`Submission.Ado.nilRadicalIsNilpotent` and `Submission.Ado.le_nilRadical`. -/
def nilRadical : LieIdeal K L :=
  sSup { I : LieIdeal K L | LieRing.IsNilpotent I }

/-- The nilradical of a finite-dimensional Lie algebra is nilpotent. -/
instance nilRadicalIsNilpotent [FiniteDimensional K L] :
    LieRing.IsNilpotent (nilRadical K L) := by
  have hwf := LieSubmodule.wellFoundedGT_of_noetherian K L L
  rw [← CompleteLattice.isSupClosedCompact_iff_wellFoundedGT] at hwf
  refine hwf { I : LieIdeal K L | LieRing.IsNilpotent I } ⟨⊥, ?_⟩ fun I hI J hJ => ?_
  · exact isNilpotent_bot
  · rw [Set.mem_setOf_eq] at hI hJ ⊢
    exact @isNilpotent_sup _ _ _ _ _ I J hI hJ

variable {K L}

/-- Every nilpotent ideal is contained in the nilradical. -/
theorem le_nilRadical {I : LieIdeal K L} [LieRing.IsNilpotent I] : I ≤ nilRadical K L :=
  le_sSup ‹_›

/-- An ideal contained in a nilpotent ideal is nilpotent. -/
theorem isNilpotent_of_le {I J : LieIdeal K L} (h : I ≤ J) (_ : LieRing.IsNilpotent J) :
    LieRing.IsNilpotent I :=
  (LieIdeal.inclusion_injective h).lieAlgebra_isNilpotent

/-- In the finite-dimensional case, the nilradical is exactly the largest nilpotent ideal. -/
theorem isNilpotent_iff_le_nilRadical [FiniteDimensional K L] (I : LieIdeal K L) :
    LieRing.IsNilpotent I ↔ I ≤ nilRadical K L :=
  ⟨fun h => le_sSup h, fun h => isNilpotent_of_le h inferInstance⟩

variable (K L)

/-- The centre is contained in the nilradical. -/
theorem center_le_nilRadical : LieAlgebra.center K L ≤ nilRadical K L :=
  le_sSup (inferInstanceAs (LieRing.IsNilpotent (LieAlgebra.center K L)))

/-- The nilradical is contained in the solvable radical. -/
theorem nilRadical_le_radical : nilRadical K L ≤ LieAlgebra.radical K L :=
  sSup_le_sSup fun I (hI : LieRing.IsNilpotent I) =>
    (@LieAlgebra.isSolvable_of_isNilpotent I _ hI : LieAlgebra.IsSolvable I)

end NilRadical

section Characteristic

variable {K : Type u} {L : Type v} [Field K] [LieRing L] [LieAlgebra K L]

/-- The lower central series of an ideal is transported by an automorphism. -/
theorem lcsFrom_map_equiv (e : L ≃ₗ⁅K⁆ L) (A : LieIdeal K L) (k : ℕ) :
    lcsFrom (A.map e.toLieHom) ⊤ k = (lcsFrom A ⊤ k).map e.toLieHom := by
  induction k with
  | zero =>
    show (⊤ : LieIdeal K L) = (⊤ : LieIdeal K L).map e.toLieHom
    rw [← LieHom.idealRange_eq_map]
    exact (e.toLieHom.idealRange_eq_top_of_surjective e.surjective).symm
  | succ k ih => rw [lcsFrom_succ, lcsFrom_succ, ih, LieIdeal.map_bracket_eq _ e.surjective]

/-- The image of a nilpotent ideal under an automorphism is a nilpotent ideal. -/
theorem isNilpotent_map_equiv (e : L ≃ₗ⁅K⁆ L) (A : LieIdeal K L) [LieRing.IsNilpotent A] :
    LieRing.IsNilpotent ↥(A.map e.toLieHom) := by
  obtain ⟨k, hk⟩ := (isNilpotent_iff_lcsFrom_top A).mp ‹_›
  refine (isNilpotent_iff_lcsFrom_top _).mpr ⟨k, ?_⟩
  rw [lcsFrom_map_equiv, hk]
  simp

/-- **The nilradical is a characteristic ideal**: it is preserved by every automorphism of `L`. -/
theorem nilRadical_map_equiv (e : L ≃ₗ⁅K⁆ L) :
    (nilRadical K L).map e.toLieHom = nilRadical K L := by
  have key : ∀ f : L ≃ₗ⁅K⁆ L, (nilRadical K L).map f.toLieHom ≤ nilRadical K L := by
    intro f
    rw [LieIdeal.map_le_iff_le_comap]
    refine sSup_le fun I (hI : LieRing.IsNilpotent I) => ?_
    rw [← LieIdeal.map_le_iff_le_comap]
    exact le_sSup (@isNilpotent_map_equiv _ _ _ _ _ f I hI)
  refine le_antisymm (key e) ?_
  intro x hx
  have hx' : e.symm x ∈ nilRadical K L := key e.symm (LieIdeal.mem_map hx)
  simpa using LieIdeal.mem_map (f := e.toLieHom) hx'

/-- The nilradical is stable under every inner derivation — this is just the statement that it is
an ideal of `L`. The corresponding statement for a general `LieDerivation` is a substantially
deeper theorem and is *not* proved here. -/
theorem nilRadical_stable_inner (y x : L) (hx : x ∈ nilRadical K L) :
    LieDerivation.ad K L y x ∈ nilRadical K L := by
  simpa using LieSubmodule.lie_mem _ hx

end Characteristic

end Submission.Ado
