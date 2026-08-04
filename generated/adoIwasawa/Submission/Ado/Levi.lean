import Mathlib

/-!
# Levi's theorem: existence of a Levi subalgebra

For a finite-dimensional Lie algebra `L` over a field `K`, a *Levi subalgebra* is a Lie
subalgebra of `L` which is a vector-space complement of the radical of `L`.  This file proves
that a Levi subalgebra exists, **assuming Whitehead's first lemma** in the form of the
predicate `Submission.Ado.WhiteheadH1` below (which is supplied externally).

## Main results

* `Submission.Ado.WhiteheadH1`: the statement of Whitehead's first lemma, taken as a hypothesis.
* `Submission.Ado.whitehead_rel`: a relative reformulation of Whitehead's first lemma, for a
  Lie algebra `L` acting on a module killed by `radical K L`, via a cocycle vanishing on
  `radical K L`.
* `Submission.Ado.levi_central`: the case where the radical coincides with the centre.
* `Submission.Ado.levi_abelian_trivial_center`: the case of an abelian radical and trivial centre.
* `Submission.Ado.levi_reduce`: the reduction step along a nonzero proper ideal of the radical.
* `Submission.Ado.exists_levi_subalgebra`: **Levi's theorem**.
* `Submission.Ado.exists_levi_subalgebra_hasTrivialRadical`: a Levi subalgebra has trivial
  radical, i.e. is semisimple.

## Proof outline

Induction on `finrank K L`.  If the radical vanishes take `S = ⊤`.  If there is an ideal `J`
with `⊥ < J < radical K L` we take a Levi subalgebra `S̄` of `L ⧸ J`, pull it back to a
subalgebra `L'` of `L` whose radical is `J`, and recurse.  Otherwise the radical is a minimal
ideal, hence abelian, and either the centre is trivial or the radical is central; both cases are
handled by a `1`-cocycle argument inside the Lie module `L →ₗ[K] L`, using Whitehead's lemma.
-/

universe u

namespace Submission.Ado

open LieAlgebra Module

/-- Whitehead's first lemma, supplied externally: for a finite-dimensional Lie algebra `S`
over a field `K` with trivial radical and a finite-dimensional `S`-module `M`, every
`1`-cocycle `c : S → M` is a coboundary. -/
def WhiteheadH1 (K : Type u) [Field K] : Prop :=
  ∀ (S : Type u) [LieRing S] [LieAlgebra K S] [FiniteDimensional K S]
    [LieAlgebra.HasTrivialRadical K S]
    (M : Type u) [AddCommGroup M] [Module K M] [LieRingModule S M] [LieModule K S M]
    [FiniteDimensional K M]
    (c : S →ₗ[K] M), (∀ x y : S, c ⁅x, y⁆ = ⁅x, c y⁆ - ⁅y, c x⁆) →
      ∃ m : M, ∀ x : S, c x = ⁅x, m⁆

section Infrastructure

attribute [local instance 100] LieRing.ofAssociativeRing

variable {K : Type u} [Field K] {L L₂ : Type u} [LieRing L] [LieAlgebra K L]
  [LieRing L₂] [LieAlgebra K L₂]

/-- The canonical projection onto a quotient by a Lie ideal, as a morphism of Lie algebras. -/
def quotMk (I : LieIdeal K L) : L →ₗ⁅K⁆ L ⧸ I where
  toFun := LieSubmodule.Quotient.mk
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_lie' := rfl

@[simp] lemma quotMk_apply (I : LieIdeal K L) (x : L) :
    quotMk I x = LieSubmodule.Quotient.mk (N := I) x := rfl

lemma quotMk_surjective (I : LieIdeal K L) : Function.Surjective (quotMk I) :=
  Quot.mk_surjective

@[simp] lemma quotMk_ker (I : LieIdeal K L) : (quotMk I).ker = I := by
  ext x; simp [LieHom.mem_ker, LieSubmodule.Quotient.mk_eq_zero']

lemma quotMk_eq_zero_iff (I : LieIdeal K L) (x : L) : quotMk I x = 0 ↔ x ∈ I :=
  LieSubmodule.Quotient.mk_eq_zero'

lemma derivedSeriesOfIdeal_map_eq (f : L →ₗ⁅K⁆ L₂) (hf : Function.Surjective f) (k : ℕ)
    (I : LieIdeal K L) :
    (derivedSeriesOfIdeal K L k I).map f = derivedSeriesOfIdeal K L₂ k (I.map f) := by
  induction k with
  | zero => simp
  | succ k ih => simp only [derivedSeriesOfIdeal_succ, LieIdeal.map_bracket_eq f hf, ih]

lemma LieIdeal.map_comap_eq_of_surjective (f : L →ₗ⁅K⁆ L₂) (hf : Function.Surjective f)
    (J : LieIdeal K L₂) : (J.comap f).map f = J := by
  refine le_antisymm ?_ ?_
  · rw [LieIdeal.map_le]
    rintro _ ⟨x, hx, rfl⟩
    exact hx
  · intro y hy
    obtain ⟨x, rfl⟩ := hf y
    exact LieIdeal.mem_map (I := J.comap f) hy

/-- If `f : L → L₂` is a surjection with solvable kernel and `J` is a solvable ideal of `L₂`,
then `J.comap f` is solvable. -/
lemma isSolvable_comap (f : L →ₗ⁅K⁆ L₂) (hf : Function.Surjective f)
    (hker : IsSolvable ↥(f.ker)) (J : LieIdeal K L₂) (hJ : IsSolvable ↥J) :
    IsSolvable ↥(J.comap f) := by
  obtain ⟨l, hl⟩ := LieAlgebra.IsSolvable.solvable K ↥J
  obtain ⟨m, hm⟩ := LieAlgebra.IsSolvable.solvable K ↥(f.ker)
  rw [LieIdeal.derivedSeries_eq_bot_iff] at hl hm
  have key : derivedSeriesOfIdeal K L l (J.comap f) ≤ f.ker := by
    rw [← LieIdeal.map_eq_bot_iff, derivedSeriesOfIdeal_map_eq f hf,
      LieIdeal.map_comap_eq_of_surjective f hf, hl]
  rw [LieAlgebra.isSolvable_iff K]
  refine ⟨m + l, ?_⟩
  rw [LieIdeal.derivedSeries_eq_bot_iff]
  refine le_bot_iff.mp ?_
  calc derivedSeriesOfIdeal K L (m + l) (J.comap f)
      = derivedSeriesOfIdeal K L m (derivedSeriesOfIdeal K L l (J.comap f)) :=
        derivedSeriesOfIdeal_add _ _ _
    _ ≤ derivedSeriesOfIdeal K L m f.ker := derivedSeriesOfIdeal_mono key m
    _ ≤ ⊥ := le_of_eq hm

/-- The quotient of a Lie algebra by its radical has trivial radical. -/
lemma hasTrivialRadical_quot_radical [IsNoetherian K L] :
    HasTrivialRadical K (L ⧸ radical K L) := by
  rw [hasTrivialRadical_iff_no_solvable_ideals]
  intro Q hQ
  have hker : IsSolvable ↥((quotMk (radical K L)).ker) := by
    rw [quotMk_ker]; infer_instance
  have hs : IsSolvable ↥(Q.comap (quotMk (radical K L))) :=
    isSolvable_comap _ (quotMk_surjective _) hker Q hQ
  have hle : Q.comap (quotMk (radical K L)) ≤ radical K L :=
    (LieIdeal.solvable_iff_le_radical _ _ _).mp hs
  have := LieIdeal.map_comap_eq_of_surjective (quotMk (radical K L)) (quotMk_surjective _) Q
  rw [← this, ← le_bot_iff]
  refine (LieIdeal.map_le _ _ _).mpr ?_
  rintro _ ⟨x, hx, rfl⟩
  simpa using hle hx

/-- Lift a morphism of Lie algebras through a quotient. -/
def quotLift (I : LieIdeal K L) (f : L →ₗ⁅K⁆ L₂) (h : I ≤ f.ker) : (L ⧸ I) →ₗ⁅K⁆ L₂ where
  __ := Submodule.liftQ I.toSubmodule (f : L →ₗ[K] L₂) h
  map_lie' {x y} := by
    induction x using Quotient.inductionOn' with | _ a =>
    induction y using Quotient.inductionOn' with | _ b =>
    exact f.map_lie a b

@[simp] lemma quotLift_apply (I : LieIdeal K L) (f : L →ₗ⁅K⁆ L₂) (h : I ≤ f.ker) (x : L) :
    quotLift I f h (quotMk I x) = f x := rfl

/-- The image of a solvable ideal under a surjective morphism is solvable. -/
lemma isSolvable_map (f : L →ₗ⁅K⁆ L₂) (hf : Function.Surjective f) (I : LieIdeal K L)
    (hI : IsSolvable ↥I) : IsSolvable ↥(I.map f) := by
  obtain ⟨k, hk⟩ := LieAlgebra.IsSolvable.solvable K ↥I
  rw [LieIdeal.derivedSeries_eq_bot_iff] at hk
  rw [LieAlgebra.isSolvable_iff K]
  refine ⟨k, ?_⟩
  rw [LieIdeal.derivedSeries_eq_bot_iff, ← derivedSeriesOfIdeal_map_eq f hf, hk]
  simp

lemma hasTrivialRadical_of_surjective (f : L →ₗ⁅K⁆ L₂) (hf : Function.Surjective f)
    (hker : IsSolvable ↥(f.ker)) [HasTrivialRadical K L] : HasTrivialRadical K L₂ := by
  rw [hasTrivialRadical_iff_no_solvable_ideals]
  intro J hJ
  have h1 : IsSolvable ↥(J.comap f) := isSolvable_comap f hf hker J hJ
  have h2 : J.comap f = ⊥ := HasTrivialRadical.eq_bot_of_isSolvable _
  rw [← LieIdeal.map_comap_eq_of_surjective f hf J, h2]
  simp

/-- Whitehead's first lemma, in the form used below: the semisimple Lie algebra is replaced by
an arbitrary finite-dimensional Lie algebra `L`, the module `M` is assumed to be killed by the
radical, and the cocycle `c` is assumed to vanish on the radical. -/
theorem whitehead_rel (hW : WhiteheadH1 K) [FiniteDimensional K L]
    {M : Type u} [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
    [FiniteDimensional K M]
    (htriv : ∀ x ∈ radical K L, ∀ m : M, ⁅x, m⁆ = 0)
    (c : L →ₗ[K] M) (hcoc : ∀ x y : L, c ⁅x, y⁆ = ⁅x, c y⁆ - ⁅y, c x⁆)
    (hc0 : ∀ x ∈ radical K L, c x = 0) :
    ∃ m : M, ∀ x : L, c x = ⁅x, m⁆ := by
  set 𝔯 : LieIdeal K L := radical K L with h𝔯
  have hker : 𝔯 ≤ (LieModule.toEnd K L M).ker := by
    intro x hx
    rw [LieHom.mem_ker]
    ext m
    exact htriv x hx m
  let ψ : (L ⧸ 𝔯) →ₗ⁅K⁆ Module.End K M := quotLift 𝔯 (LieModule.toEnd K L M) hker
  letI : LieRingModule (L ⧸ 𝔯) M := LieRingModule.compLieHom M ψ
  letI : LieModule K (L ⧸ 𝔯) M := LieModule.compLieHom M ψ
  haveI : HasTrivialRadical K (L ⧸ 𝔯) := hasTrivialRadical_quot_radical
  have hbr : ∀ (x : L) (m : M), ⁅quotMk 𝔯 x, m⁆ = ⁅x, m⁆ := fun x m => rfl
  have hc0' : 𝔯.toSubmodule ≤ LinearMap.ker c := fun x hx => hc0 x hx
  let c' : (L ⧸ 𝔯) →ₗ[K] M := Submodule.liftQ 𝔯.toSubmodule c hc0'
  have hc' : ∀ x : L, c' (quotMk 𝔯 x) = c x := fun x => rfl
  have hcoc' : ∀ x y : L ⧸ 𝔯, c' ⁅x, y⁆ = ⁅x, c' y⁆ - ⁅y, c' x⁆ := by
    intro x y
    induction x using Quotient.inductionOn' with | _ a =>
    induction y using Quotient.inductionOn' with | _ b =>
    show c' (quotMk 𝔯 ⁅a, b⁆) = _
    rw [hc', hcoc a b]
    show _ = ⁅a, c' (quotMk 𝔯 b)⁆ - ⁅b, c' (quotMk 𝔯 a)⁆
    rw [hc', hc']
  obtain ⟨m, hm⟩ := hW (L ⧸ 𝔯) M c' hcoc'
  refine ⟨m, fun x => ?_⟩
  have := hm (quotMk 𝔯 x)
  rwa [hc' x, hbr x m] at this

end Infrastructure

section Central

attribute [local instance 100] LieRing.ofAssociativeRing

variable {K : Type u} [Field K]

/-- If `p` is a linear endomorphism with image inside `W` restricting to the identity on `W`,
then `ker p` is a complement of `W`. -/
lemma isCompl_ker_of_proj {V : Type*} [AddCommGroup V] [Module K V] (p : V →ₗ[K] V)
    (W : Submodule K V) (h1 : ∀ y, p y ∈ W) (h2 : ∀ b ∈ W, p b = b) :
    IsCompl (LinearMap.ker p) W := by
  constructor
  · rw [Submodule.disjoint_def]
    intro x hx hxW
    rw [LinearMap.mem_ker] at hx
    rw [← h2 x hxW, hx]
  · rw [codisjoint_iff, eq_top_iff]
    intro x _
    have hx : x = (x - p x) + p x := by abel
    rw [hx]
    refine Submodule.add_mem_sup ?_ (h1 x)
    simp [LinearMap.mem_ker, h2 (p x) (h1 x)]

variable {L : Type u} [LieRing L] [LieAlgebra K L]

/-- For a Lie ideal `I`, the linear endomorphisms of `L` with image in `I` that vanish on `I`
form a Lie submodule of `L →ₗ[K] L`. -/
def homSub (I : LieIdeal K L) : LieSubmodule K L (L →ₗ[K] L) where
  carrier := {φ | (∀ y, φ y ∈ I) ∧ (∀ b ∈ I, φ b = 0)}
  add_mem' {a b} ha hb :=
    ⟨fun y => by simpa using add_mem (ha.1 y) (hb.1 y), fun c hc => by simp [ha.2 c hc, hb.2 c hc]⟩
  zero_mem' := ⟨fun y => by simp, fun c _ => rfl⟩
  smul_mem' t a ha :=
    ⟨fun y => by simpa using Submodule.smul_mem _ t (ha.1 y), fun c hc => by simp [ha.2 c hc]⟩
  lie_mem {x φ} hφ := by
    refine ⟨fun y => ?_, fun c hc => ?_⟩
    · rw [LieHom.lie_apply]
      exact sub_mem (lie_mem_right K L I x _ (hφ.1 y)) (hφ.1 _)
    · rw [LieHom.lie_apply, hφ.2 c hc, hφ.2 _ (lie_mem_right K L I x c hc)]
      simp

@[simp] lemma mem_homSub {I : LieIdeal K L} {φ : L →ₗ[K] L} :
    φ ∈ homSub I ↔ (∀ y, φ y ∈ I) ∧ (∀ b ∈ I, φ b = 0) := Iff.rfl

theorem levi_central (hW : WhiteheadH1 K) [FiniteDimensional K L]
    (hcen : radical K L = center K L) :
    ∃ S : LieSubalgebra K L, IsCompl S.toSubmodule (radical K L).toSubmodule := by
  have hz : ∀ (x y : L), y ∈ radical K L → ⁅x, y⁆ = 0 := by
    intro x y hy
    rw [hcen] at hy
    exact (LieModule.mem_maxTrivSubmodule K L L y).mp hy x
  set M₁ : LieSubmodule K L (L →ₗ[K] L) := homSub (radical K L) with hM₁
  have hmem : ∀ φ : L →ₗ[K] L,
      (φ ∈ M₁ ↔ ((∀ y, φ y ∈ radical K L) ∧ (∀ b ∈ radical K L, φ b = 0))) := fun _ => Iff.rfl
  -- a linear retraction of `L` onto the radical
  obtain ⟨g, hg⟩ := (LieSubmodule.toSubmodule (radical K L)).subtype.exists_leftInverse_of_injective
    (Submodule.ker_subtype _)
  set q : L →ₗ[K] L := (LieSubmodule.toSubmodule (radical K L)).subtype ∘ₗ g with hqdef
  have hq1 : ∀ y, q y ∈ radical K L := fun y => (g y).2
  have hq2 : ∀ b ∈ radical K L, q b = b := by
    intro b hb
    have := congrFun (congrArg (fun f => f.toFun) hg) (⟨b, hb⟩ : ↑(LieSubmodule.toSubmodule (radical K L)))
    exact congrArg Subtype.val this
  -- the cocycle
  have hmemγ : ∀ x : L, (q ∘ₗ (LieAlgebra.ad K L x : L →ₗ[K] L)) ∈ M₁ := by
    intro x
    refine ⟨fun y => hq1 _, fun c hc => ?_⟩
    simp only [LinearMap.comp_apply, LieAlgebra.ad_apply, hz x c hc, map_zero]
  set γ : L →ₗ[K] ↑M₁ :=
    { toFun := fun x => ⟨q ∘ₗ (LieAlgebra.ad K L x : L →ₗ[K] L), hmemγ x⟩
      map_add' := by intro x y; ext z; simp
      map_smul' := by intro t x; ext z; simp } with hγ
  have hγapp : ∀ (x y : L), ((γ x : L →ₗ[K] L) y) = q ⁅x, y⁆ := fun x y => rfl
  have hcoc : ∀ x y : L, γ ⁅x, y⁆ = ⁅x, γ y⁆ - ⁅y, γ x⁆ := by
    intro x y
    ext z
    show q ⁅⁅x, y⁆, z⁆ = (⁅x, (γ y : L →ₗ[K] L)⁆ - ⁅y, (γ x : L →ₗ[K] L)⁆) z
    rw [LinearMap.sub_apply, LieHom.lie_apply, LieHom.lie_apply, hγapp, hγapp, hγapp, hγapp,
      hz x _ (hq1 ⁅y, z⁆), hz y _ (hq1 ⁅x, z⁆)]
    rw [show ⁅⁅x, y⁆, z⁆ = ⁅x, ⁅y, z⁆⁆ - ⁅y, ⁅x, z⁆⁆ by rw [leibniz_lie x y z]; abel]
    simp
    abel
  have hc0 : ∀ x ∈ radical K L, γ x = 0 := by
    intro x hx
    ext z
    show q ⁅x, z⁆ = (0 : L →ₗ[K] L) z
    rw [← lie_skew, hz z x hx, neg_zero, map_zero]
    simp
  have htriv : ∀ x ∈ radical K L, ∀ m : ↑M₁, ⁅x, m⁆ = 0 := by
    intro x hx m
    ext z
    show (⁅x, (m : L →ₗ[K] L)⁆) z = (0 : L →ₗ[K] L) z
    rw [LieHom.lie_apply, hz x _ (m.2.1 z), ← lie_skew x z, hz z x hx, neg_zero, m.2.2 0 (zero_mem _)]
    simp
  obtain ⟨φ, hφ⟩ := whitehead_rel hW htriv γ hcoc hc0
  set p : L →ₗ[K] L := q + (φ : L →ₗ[K] L) with hp
  have hp1 : ∀ y, p y ∈ radical K L := fun y => add_mem (hq1 y) (φ.2.1 y)
  have hp2 : ∀ b ∈ radical K L, p b = b := by
    intro b hb
    simp [hp, hq2 b hb, φ.2.2 b hb]
  have hplie : ∀ x y : L, p ⁅x, y⁆ = 0 := by
    intro x y
    have h : (γ x : L →ₗ[K] L) y = ((⁅x, φ⁆ : ↑M₁) : L →ₗ[K] L) y := by rw [hφ x]
    rw [hγapp x y] at h
    have e1 : ((⁅x, φ⁆ : ↑M₁) : L →ₗ[K] L) y = ⁅x, (φ : L →ₗ[K] L) y⁆
        - (φ : L →ₗ[K] L) ⁅x, y⁆ := rfl
    rw [e1, hz x _ (φ.2.1 y), zero_sub] at h
    simp [hp, h]
  refine ⟨{ LinearMap.ker p with
      lie_mem' := fun {x y} _ _ => by simp [LinearMap.mem_ker, hplie x y] }, ?_⟩
  exact isCompl_ker_of_proj p _ hp1 hp2

end Central

section AbelianTrivialCenter

attribute [local instance 100] LieRing.ofAssociativeRing

variable {K : Type u} [Field K] {L : Type u} [LieRing L] [LieAlgebra K L]

/-- The Lie submodule of `L →ₗ[K] L` spanned by the inner derivations `ad a` with `a` in an
ideal `I`. -/
def adSub (I : LieIdeal K L) : LieSubmodule K L (L →ₗ[K] L) where
  carrier := {φ | ∃ a ∈ I, ∀ y, φ y = ⁅a, y⁆}
  add_mem' := by
    rintro φ ψ ⟨a, ha, hφ⟩ ⟨b, hb, hψ⟩
    exact ⟨a + b, add_mem ha hb, fun y => by simp [hφ y, hψ y, add_lie]⟩
  zero_mem' := ⟨0, zero_mem _, fun y => by simp⟩
  smul_mem' t φ := by
    rintro ⟨a, ha, hφ⟩
    exact ⟨t • a, Submodule.smul_mem _ t ha, fun y => by simp [hφ y, smul_lie]⟩
  lie_mem {x φ} := by
    rintro ⟨a, ha, hφ⟩
    refine ⟨⁅x, a⁆, lie_mem_right K L I x a ha, fun y => ?_⟩
    rw [LieHom.lie_apply, hφ y, hφ ⁅x, y⁆, leibniz_lie x a y]
    abel

theorem levi_abelian_trivial_center (hW : WhiteheadH1 K) [FiniteDimensional K L]
    (habel : ∀ a ∈ radical K L, ∀ b ∈ radical K L, ⁅a, b⁆ = (0 : L))
    (hcen : center K L = ⊥) :
    ∃ S : LieSubalgebra K L, IsCompl S.toSubmodule (radical K L).toSubmodule := by
  have hcen' : ∀ a : L, (∀ y, ⁅a, y⁆ = (0 : L)) → a = 0 := by
    intro a ha
    have hmem : a ∈ center K L := by
      rw [LieModule.mem_maxTrivSubmodule]
      intro x
      rw [← lie_skew, ha x, neg_zero]
    rw [hcen] at hmem
    simpa using hmem
  -- a linear retraction of `L` onto the radical
  obtain ⟨g0, hg0⟩ :=
    (LieSubmodule.toSubmodule (radical K L)).subtype.exists_leftInverse_of_injective
      (Submodule.ker_subtype _)
  set f₀ : L →ₗ[K] L := (LieSubmodule.toSubmodule (radical K L)).subtype ∘ₗ g0 with hf₀def
  have hf1 : ∀ y, f₀ y ∈ radical K L := fun y => (g0 y).2
  have hf2 : ∀ b ∈ radical K L, f₀ b = b := by
    intro b hb
    have := congrFun (congrArg (fun f => f.toFun) hg0)
      (⟨b, hb⟩ : ↥(LieSubmodule.toSubmodule (radical K L)))
    exact congrArg Subtype.val this
  set V : LieSubmodule K L (L →ₗ[K] L) := homSub (radical K L) with hV
  set A : LieSubmodule K L (L →ₗ[K] L) := adSub (radical K L) with hA
  set A' : LieSubmodule K L ↥V := A.comap V.incl with hA'
  have hmemA' : ∀ v : ↥V, (v ∈ A' ↔ (v : L →ₗ[K] L) ∈ A) := fun v => Iff.rfl
  -- the cocycle
  have hc0mem : ∀ x : L, (⁅x, f₀⁆ : L →ₗ[K] L) ∈ V := by
    intro x
    refine ⟨fun y => ?_, fun b hb => ?_⟩
    · rw [LieHom.lie_apply]
      exact sub_mem (lie_mem_right K L (radical K L) x _ (hf1 y)) (hf1 _)
    · rw [LieHom.lie_apply, hf2 b hb, hf2 _ (lie_mem_right K L (radical K L) x b hb)]
      simp
  set c₀ : L →ₗ[K] ↥V :=
    { toFun := fun x => ⟨⁅x, f₀⁆, hc0mem x⟩
      map_add' := by intro x y; ext z; simp [add_lie]
      map_smul' := by intro t x; ext z; simp [smul_lie] } with hc₀
  have hc₀app : ∀ x : L, ((c₀ x : L →ₗ[K] L)) = ⁅x, f₀⁆ := fun x => rfl
  set c : L →ₗ[K] (↥V ⧸ A') :=
    (LieSubmodule.Quotient.mk' A').toLinearMap ∘ₗ c₀ with hc
  have hcapp : ∀ x : L, c x = LieSubmodule.Quotient.mk' A' (c₀ x) := fun x => rfl
  have hc₀coc : ∀ x y : L, c₀ ⁅x, y⁆ = ⁅x, c₀ y⁆ - ⁅y, c₀ x⁆ := by
    intro x y
    ext z
    show (⁅⁅x, y⁆, f₀⁆ : L →ₗ[K] L) z
        = ((⁅x, c₀ y⁆ : ↥V) : L →ₗ[K] L) z - ((⁅y, c₀ x⁆ : ↥V) : L →ₗ[K] L) z
    have e1 : ((⁅x, c₀ y⁆ : ↥V) : L →ₗ[K] L) = ⁅x, (⁅y, f₀⁆ : L →ₗ[K] L)⁆ := rfl
    have e2 : ((⁅y, c₀ x⁆ : ↥V) : L →ₗ[K] L) = ⁅y, (⁅x, f₀⁆ : L →ₗ[K] L)⁆ := rfl
    rw [e1, e2]
    have := leibniz_lie x y f₀
    rw [show (⁅⁅x, y⁆, f₀⁆ : L →ₗ[K] L) = ⁅x, (⁅y, f₀⁆ : L →ₗ[K] L)⁆ - ⁅y, (⁅x, f₀⁆ : L →ₗ[K] L)⁆ by
      rw [this]; abel]
    simp
  have hcoc : ∀ x y : L, c ⁅x, y⁆ = ⁅x, c y⁆ - ⁅y, c x⁆ := by
    intro x y
    rw [hcapp, hcapp, hcapp, hc₀coc x y, map_sub, LieModuleHom.map_lie, LieModuleHom.map_lie]
  have hcvanish : ∀ b ∈ radical K L, c b = 0 := by
    intro b hb
    have hin : (⁅b, f₀⁆ : L →ₗ[K] L) ∈ A := by
      refine ⟨-b, neg_mem hb, fun y => ?_⟩
      rw [LieHom.lie_apply, hf2 _ (lie_mem_left K L (radical K L) b y hb),
        habel b hb _ (hf1 y)]
      simp
    rw [hcapp, LieSubmodule.Quotient.mk_eq_zero]
    exact hin
  have htriv : ∀ x ∈ radical K L, ∀ m : (↥V ⧸ A'), ⁅x, m⁆ = 0 := by
    intro x hx m
    induction m using Quotient.inductionOn' with | _ v =>
    have hzero : (⁅x, v⁆ : ↥V) = 0 := by
      ext z
      show ((⁅x, v⁆ : ↥V) : L →ₗ[K] L) z = ((0 : ↥V) : L →ₗ[K] L) z
      have e1 : ((⁅x, v⁆ : ↥V) : L →ₗ[K] L) = ⁅x, (v : L →ₗ[K] L)⁆ := rfl
      rw [e1, LieHom.lie_apply, habel x hx _ (v.2.1 z),
        v.2.2 _ (lie_mem_left K L (radical K L) x z hx)]
      simp
    show ⁅x, LieSubmodule.Quotient.mk' A' v⁆ = 0
    rw [← LieModuleHom.map_lie, hzero, map_zero]
  obtain ⟨mm, hmm⟩ := whitehead_rel hW htriv c hcoc hcvanish
  obtain ⟨gv, hgv⟩ := LieSubmodule.Quotient.surjective_mk' A' mm
  set f : L →ₗ[K] L := f₀ - (gv : L →ₗ[K] L) with hf
  have hfA : ∀ x : L, (⁅x, f⁆ : L →ₗ[K] L) ∈ A := by
    intro x
    have h1 : c x = ⁅x, mm⁆ := hmm x
    rw [hcapp, ← hgv, ← LieModuleHom.map_lie, ← sub_eq_zero, ← map_sub,
      LieSubmodule.Quotient.mk_eq_zero] at h1
    have h2 : ((c₀ x - ⁅x, gv⁆ : ↥V) : L →ₗ[K] L) = ⁅x, f⁆ := by
      show (c₀ x : L →ₗ[K] L) - ((⁅x, gv⁆ : ↥V) : L →ₗ[K] L) = ⁅x, f⁆
      have e1 : ((⁅x, gv⁆ : ↥V) : L →ₗ[K] L) = ⁅x, (gv : L →ₗ[K] L)⁆ := rfl
      rw [e1, hc₀app, hf, lie_sub]
    rw [← h2]
    exact h1
  have hf1' : ∀ y, f y ∈ radical K L := by
    intro y
    exact sub_mem (hf1 y) (gv.2.1 y)
  have hf2' : ∀ b ∈ radical K L, f b = b := by
    intro b hb
    simp [hf, hf2 b hb, gv.2.2 b hb]
  -- the adjoint map, injective because the centre vanishes
  set T : L →ₗ[K] (L →ₗ[K] L) :=
    { toFun := fun a => (LieAlgebra.ad K L a : L →ₗ[K] L)
      map_add' := by intro a b; ext y; simp
      map_smul' := by intro t a; ext y; simp } with hT
  have hTapp : ∀ (a y : L), (T a) y = ⁅a, y⁆ := fun a y => rfl
  have hTinj : Function.Injective T := by
    intro a b hab
    have h : ∀ y, ⁅a, y⁆ = ⁅b, y⁆ := fun y => by
      rw [← hTapp a y, ← hTapp b y, hab]
    refine sub_eq_zero.mp (hcen' (a - b) fun y => ?_)
    rw [sub_lie, h y, sub_self]
  have hTlie : ∀ (x w : L), (⁅x, T w⁆ : L →ₗ[K] L) = T ⁅x, w⁆ := by
    intro x w
    ext z
    rw [LieHom.lie_apply, hTapp, hTapp, hTapp, leibniz_lie x w z]
    abel
  set Φ : L →ₗ[K] (L →ₗ[K] L) :=
    { toFun := fun x => ⁅x, f⁆
      map_add' := by intro x y; ext z; simp [add_lie]
      map_smul' := by intro t x; ext z; simp [smul_lie] } with hΦ
  have hΦapp : ∀ x : L, Φ x = (⁅x, f⁆ : L →ₗ[K] L) := fun x => rfl
  have hrange : ∀ x, Φ x ∈ LinearMap.range T := by
    intro x
    obtain ⟨a, _, hfa⟩ := hfA x
    exact ⟨a, by ext y; rw [hTapp, hΦapp]; exact (hfa y).symm⟩
  set ee := LinearEquiv.ofInjective T hTinj with hee
  set aa : L →ₗ[K] L :=
    (ee.symm : ↥(LinearMap.range T) →ₗ[K] L) ∘ₗ (Φ.codRestrict (LinearMap.range T) hrange)
    with haadef
  have haa : ∀ x, T (aa x) = Φ x := by
    intro x
    have h1 : ee (aa x) = Φ.codRestrict (LinearMap.range T) hrange x := by
      simp [haadef]
    have h2 := congrArg Subtype.val h1
    simpa [hee, LinearEquiv.ofInjective_apply] using h2
  have haaI : ∀ x, aa x ∈ radical K L := by
    intro x
    obtain ⟨a, haI, hfa⟩ := hfA x
    have : T (aa x) = T a := by
      rw [haa x]
      ext y
      rw [hΦapp, hTapp]
      exact hfa y
    rw [hTinj this]
    exact haI
  have haab : ∀ b ∈ radical K L, aa b = -b := by
    intro b hb
    refine hTinj ?_
    rw [haa b]
    ext y
    rw [hΦapp, hTapp, LieHom.lie_apply, hf2' _ (lie_mem_left K L (radical K L) b y hb),
      habel b hb _ (hf1' y)]
    simp
  have haacoc : ∀ x y : L, aa ⁅x, y⁆ = ⁅x, aa y⁆ - ⁅y, aa x⁆ := by
    intro x y
    refine hTinj ?_
    rw [haa, map_sub, ← hTlie, ← hTlie, haa, haa, hΦapp, hΦapp, hΦapp]
    have := leibniz_lie x y f
    rw [this]
    abel
  set p : L →ₗ[K] L := -aa with hp
  have hp1 : ∀ y, p y ∈ radical K L := fun y => by
    simpa [hp] using neg_mem (haaI y)
  have hp2 : ∀ b ∈ radical K L, p b = b := by
    intro b hb
    simp [hp, haab b hb]
  have hplie : ∀ x y : L, p ⁅x, y⁆ = ⁅x, p y⁆ - ⁅y, p x⁆ := by
    intro x y
    simp only [hp, LinearMap.neg_apply, haacoc x y, lie_neg]
    abel
  have hker : ∀ x y : L, p x = 0 → p y = 0 → p ⁅x, y⁆ = 0 := by
    intro x y hx hy
    rw [hplie x y, hx, hy]
    simp
  refine ⟨{ LinearMap.ker p with
      lie_mem' := fun {x y} hx hy =>
        LinearMap.mem_ker.mpr (hker x y (LinearMap.mem_ker.mp hx) (LinearMap.mem_ker.mp hy)) }, ?_⟩
  exact isCompl_ker_of_proj p _ hp1 hp2

end AbelianTrivialCenter

section Reduction

attribute [local instance 100] LieRing.ofAssociativeRing

variable {K : Type u} [Field K] {L L₂ : Type u} [LieRing L] [LieAlgebra K L]
  [LieRing L₂] [LieAlgebra K L₂]

lemma hasTrivialRadical_of_bijective (f : L →ₗ⁅K⁆ L₂) (hinj : Function.Injective f)
    (hsurj : Function.Surjective f) [HasTrivialRadical K L₂] : HasTrivialRadical K L := by
  have hker : f.ker = ⊥ := by
    ext x
    simp only [LieHom.mem_ker, LieSubmodule.mem_bot]
    exact ⟨fun h => hinj (by rw [h, map_zero]), fun h => by rw [h, map_zero]⟩
  rw [hasTrivialRadical_iff_no_solvable_ideals]
  intro I hI
  have h1 : IsSolvable ↥(I.map f) := isSolvable_map f hsurj I hI
  have h2 : I.map f = ⊥ := HasTrivialRadical.eq_bot_of_isSolvable _
  rw [LieIdeal.map_eq_bot_iff, hker] at h2
  exact le_bot_iff.mp h2

/-- A subalgebra complementing the radical has trivial radical. -/
lemma hasTrivialRadical_of_isCompl [FiniteDimensional K L] (S : LieSubalgebra K L)
    (hS : IsCompl S.toSubmodule (radical K L).toSubmodule) : HasTrivialRadical K ↥S := by
  haveI : HasTrivialRadical K (L ⧸ radical K L) := hasTrivialRadical_quot_radical
  refine hasTrivialRadical_of_bijective ((quotMk (radical K L)).comp S.incl) ?_ ?_
  · intro a b hab
    have hab' : quotMk (radical K L) (a : L) = quotMk (radical K L) (b : L) := hab
    have hz : quotMk (radical K L) ((a : L) - (b : L)) = 0 := by
      rw [map_sub]; exact sub_eq_zero.mpr hab'
    have h : (a : L) - (b : L) ∈ radical K L := (quotMk_eq_zero_iff _ _).mp hz
    have h2 : (a : L) - (b : L) ∈ S.toSubmodule := sub_mem a.2 b.2
    have hd := hS.disjoint
    rw [Submodule.disjoint_def] at hd
    exact Subtype.ext (sub_eq_zero.mp (hd _ h2 h))
  · intro y
    induction y using Quotient.inductionOn' with | _ x =>
    have hx : x ∈ S.toSubmodule ⊔ (radical K L).toSubmodule := by
      rw [hS.codisjoint.eq_top]; trivial
    rw [Submodule.mem_sup] at hx
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    refine ⟨⟨a, ha⟩, ?_⟩
    have h0 : quotMk (radical K L) b = 0 := by
      rw [quotMk_eq_zero_iff]
      simpa using hb
    show quotMk (radical K L) a = LieSubmodule.Quotient.mk (N := radical K L) (a + b)
    rw [← quotMk_apply, map_add, h0, add_zero]

/-- The key reduction step: if `J` is a nonzero proper ideal of the radical, we may build a
Levi subalgebra from ones for `L ⧸ J` and for the preimage of a Levi subalgebra of `L ⧸ J`. -/
private theorem levi_reduce (L : Type u) [LieRing L] [LieAlgebra K L] [FiniteDimensional K L]
    (ih : ∀ (M : Type u) [LieRing M] [LieAlgebra K M] [FiniteDimensional K M],
      Module.finrank K M < Module.finrank K L →
        ∃ S : LieSubalgebra K M, IsCompl S.toSubmodule (radical K M).toSubmodule)
    (J : LieIdeal K L) (hJle : J ≤ radical K L) (hJbot : J ≠ ⊥) (hJne : J ≠ radical K L) :
    ∃ S : LieSubalgebra K L, IsCompl S.toSubmodule (radical K L).toSubmodule := by
  haveI hJsolv : IsSolvable ↥J := LieAlgebra.le_solvable_ideal_solvable hJle inferInstance
  set π : L →ₗ⁅K⁆ (L ⧸ J) := quotMk J with hπ
  have hsurj : Function.Surjective π := quotMk_surjective J
  have hmemker : ∀ x : L, (π x = 0 ↔ x ∈ J) := fun x => quotMk_eq_zero_iff J x
  have hkerJ : IsSolvable ↥(π.ker) := by rw [hπ, quotMk_ker]; exact hJsolv
  have hmaple : (radical K L).map π ≤ radical K (L ⧸ J) :=
    (LieIdeal.solvable_iff_le_radical _ _ _).mp (isSolvable_map π hsurj _ inferInstance)
  have hcomple : (radical K (L ⧸ J)).comap π ≤ radical K L :=
    (LieIdeal.solvable_iff_le_radical _ _ _).mp (isSolvable_comap π hsurj hkerJ _ inferInstance)
  -- first recursive call: a Levi subalgebra of `L ⧸ J`
  have hJpos : 0 < Module.finrank K ↥(LieSubmodule.toSubmodule J) := by
    have hlt : (⊥ : Submodule K L) < LieSubmodule.toSubmodule J := by
      refine bot_lt_iff_ne_bot.mpr ?_
      simpa using hJbot
    simpa using Submodule.finrank_lt_finrank_of_lt hlt
  have hlt1 : Module.finrank K (L ⧸ J) < Module.finrank K L := by
    have h1 := Submodule.finrank_quotient_add_finrank (LieSubmodule.toSubmodule J)
    have h2 : Module.finrank K (L ⧸ J)
        = Module.finrank K (L ⧸ (LieSubmodule.toSubmodule J)) := rfl
    omega
  obtain ⟨Sb, hSb⟩ := ih (L ⧸ J) hlt1
  haveI : HasTrivialRadical K ↥Sb := hasTrivialRadical_of_isCompl Sb hSb
  set L' : LieSubalgebra K L := Sb.comap π with hL'
  have hmemL' : ∀ x : L, (x ∈ L' ↔ π x ∈ Sb) := fun x => Iff.rfl
  have hJL' : ∀ x ∈ J, x ∈ L' := by
    intro x hx
    rw [hmemL', (hmemker x).mpr hx]
    exact zero_mem _
  -- `L'` is a proper subalgebra
  have hL'ne : LieSubalgebra.toSubmodule L' ≠ ⊤ := by
    intro htop
    have hSbtop : Sb = ⊤ := by
      refine eq_top_iff.mpr fun y _ => ?_
      obtain ⟨x, rfl⟩ := hsurj y
      have hx : x ∈ LieSubalgebra.toSubmodule L' := by rw [htop]; trivial
      exact hx
    have hbot : radical K (L ⧸ J) = ⊥ := by
      have hd := hSb.disjoint
      rw [hSbtop] at hd
      simpa using hd
    have hmb : (radical K L).map π = ⊥ := le_bot_iff.mp (hbot ▸ hmaple)
    rw [LieIdeal.map_eq_bot_iff, hπ, quotMk_ker] at hmb
    exact hJne (le_antisymm hJle hmb)
  have hlt2 : Module.finrank K ↥L' < Module.finrank K L := Submodule.finrank_lt hL'ne
  -- the radical of `L'` is `J`
  set J' : LieIdeal K ↥L' := J.comap L'.incl with hJ'
  have hmemJ' : ∀ x : ↥L', (x ∈ J' ↔ (x : L) ∈ J) := fun x => Iff.rfl
  have hJ'solv : IsSolvable ↥J' := by
    refine Function.Injective.lieAlgebra_isSolvable
      (f := ({ toFun := fun x => (⟨((x : ↥L') : L), x.2⟩ : ↥J)
               map_add' := fun _ _ => rfl
               map_smul' := fun _ _ => rfl
               map_lie' := rfl } : ↥J' →ₗ⁅K⁆ ↥J)) ?_
    intro a b hab
    have hab2 : (⟨((a : ↥L') : L), a.2⟩ : ↥J) = ⟨((b : ↥L') : L), b.2⟩ := hab
    have h1 : ((a : ↥L') : L) = ((b : ↥L') : L) := congrArg (fun z : ↥J => (z : L)) hab2
    exact Subtype.ext (Subtype.ext h1)
  set ψ : ↥L' →ₗ⁅K⁆ ↥Sb :=
    { toFun := fun x => (⟨π (x : L), x.2⟩ : ↥Sb)
      map_add' := fun a b => Subtype.ext (by simp)
      map_smul' := fun t a => Subtype.ext (by simp)
      map_lie' := fun {a b} => Subtype.ext (by simp) } with hψ
  have hψapp : ∀ x : ↥L', ((ψ x : ↥Sb) : L ⧸ J) = π (x : L) := fun _ => rfl
  have hψsurj : Function.Surjective ψ := by
    intro sb
    obtain ⟨x, hx⟩ := hsurj (sb : L ⧸ J)
    have hxL' : x ∈ L' := by rw [hmemL', hx]; exact sb.2
    exact ⟨⟨x, hxL'⟩, Subtype.ext hx⟩
  have hψker : ψ.ker = J' := by
    ext x
    rw [LieHom.mem_ker, hmemJ', ← hmemker]
    constructor
    · intro h; exact (hψapp x).symm.trans (congrArg Subtype.val h)
    · intro h; exact Subtype.ext ((hψapp x).trans h)
  have hradL' : radical K ↥L' = J' := by
    refine le_antisymm ?_ ((LieIdeal.solvable_iff_le_radical _ _ _).mp hJ'solv)
    have h1 : IsSolvable ↥((radical K ↥L').map ψ) :=
      isSolvable_map ψ hψsurj _ inferInstance
    have h2 : (radical K ↥L').map ψ = ⊥ := HasTrivialRadical.eq_bot_of_isSolvable _
    rw [LieIdeal.map_eq_bot_iff, hψker] at h2
    exact h2
  -- second recursive call
  obtain ⟨S', hS'⟩ := ih ↥L' hlt2
  rw [hradL'] at hS'
  refine ⟨S'.map L'.incl, ?_, ?_⟩
  · rw [Submodule.disjoint_def]
    intro x hx hxr
    obtain ⟨s, hs, rfl⟩ := hx
    have hπs : π ((s : ↥L') : L) ∈ Sb := s.2
    have hπr : π ((s : ↥L') : L) ∈ radical K (L ⧸ J) :=
      hmaple (LieIdeal.mem_map (f := π) hxr)
    have hd := hSb.disjoint
    rw [Submodule.disjoint_def] at hd
    have hzero : π ((s : ↥L') : L) = 0 := hd _ hπs hπr
    have hsJ : s ∈ J' := (hmemJ' s).mpr ((hmemker _).mp hzero)
    have hd2 := hS'.disjoint
    rw [Submodule.disjoint_def] at hd2
    have hs0 : s = 0 := hd2 _ hs hsJ
    simp [hs0]
  · rw [codisjoint_iff, eq_top_iff]
    intro x _
    have hx : π x ∈ Sb.toSubmodule ⊔ (radical K (L ⧸ J)).toSubmodule := by
      rw [hSb.codisjoint.eq_top]; trivial
    rw [Submodule.mem_sup] at hx
    obtain ⟨sb, hsb, rb, hrb, hxsum⟩ := hx
    obtain ⟨u, hu⟩ := hsurj sb
    obtain ⟨r, hr⟩ := hsurj rb
    have hrrad : r ∈ radical K L := by
      refine hcomple ?_
      show π r ∈ radical K (L ⧸ J)
      rw [hr]
      exact hrb
    have huL' : u ∈ L' := by rw [hmemL', hu]; exact hsb
    have hw : x - r - u ∈ J := by
      refine (hmemker _).mp ?_
      rw [map_sub, map_sub, hr, hu, ← hxsum]
      abel
    have hvL' : u + (x - r - u) ∈ L' := add_mem huL' (hJL' _ hw)
    have hv : (⟨u + (x - r - u), hvL'⟩ : ↥L') ∈ (⊤ : Submodule K ↥L') := trivial
    rw [← hS'.codisjoint.eq_top, Submodule.mem_sup] at hv
    obtain ⟨s', hs', j', hj', hvsum⟩ := hv
    have hvcoe : ((s' : ↥L') : L) + ((j' : ↥L') : L) = u + (x - r - u) :=
      congrArg Subtype.val hvsum
    have hxeq : x = ((s' : ↥L') : L) + (r + ((j' : ↥L') : L)) := by
      have : ((s' : ↥L') : L) + ((j' : ↥L') : L) = x - r := by rw [hvcoe]; abel
      rw [show ((s' : ↥L') : L) + (r + ((j' : ↥L') : L))
          = (((s' : ↥L') : L) + ((j' : ↥L') : L)) + r by abel, this]
      abel
    rw [hxeq]
    refine Submodule.add_mem_sup ?_ (add_mem hrrad (hJle ((hmemJ' j').mp hj')))
    exact ⟨s', hs', rfl⟩

/-- One step of the induction establishing the Levi decomposition. -/
private theorem levi_step (hW : WhiteheadH1 K) (L : Type u) [LieRing L] [LieAlgebra K L]
    [FiniteDimensional K L]
    (ih : ∀ (M : Type u) [LieRing M] [LieAlgebra K M] [FiniteDimensional K M],
      Module.finrank K M < Module.finrank K L →
        ∃ S : LieSubalgebra K M, IsCompl S.toSubmodule (radical K M).toSubmodule) :
    ∃ S : LieSubalgebra K L, IsCompl S.toSubmodule (radical K L).toSubmodule := by
  by_cases h0 : radical K L = ⊥
  · exact ⟨⊤, by rw [h0]; simpa using isCompl_top_bot⟩
  by_cases hab : ∀ a ∈ radical K L, ∀ b ∈ radical K L, ⁅a, b⁆ = (0 : L)
  · by_cases hz : center K L = ⊥
    · exact levi_abelian_trivial_center hW hab hz
    · by_cases hz2 : center K L = radical K L
      · exact levi_central hW hz2.symm
      · exact levi_reduce L ih (center K L) (center_le_radical K L) hz hz2
  · -- the radical is not abelian: reduce along its derived ideal
    have hd1 : derivedSeriesOfIdeal K L 1 (radical K L) = ⁅radical K L, radical K L⁆ := by
      rw [derivedSeriesOfIdeal_succ, derivedSeriesOfIdeal_zero]
    refine levi_reduce L ih ⁅radical K L, radical K L⁆ (LieSubmodule.lie_le_right _ _) ?_ ?_
    · intro hbot
      rw [← hd1, ← LieAlgebra.abelian_iff_derived_one_eq_bot] at hbot
      exact hab fun a ha b hb =>
        congrArg Subtype.val (hbot.trivial (⟨a, ha⟩ : ↥(radical K L)) ⟨b, hb⟩)
    · intro heq
      obtain ⟨k, hk⟩ := LieAlgebra.IsSolvable.solvable K ↥(radical K L)
      rw [LieIdeal.derivedSeries_eq_bot_iff] at hk
      have hall : ∀ n, derivedSeriesOfIdeal K L n (radical K L) = radical K L := by
        intro n
        induction n with
        | zero => simp
        | succ n ihn => rw [derivedSeriesOfIdeal_succ, ihn]; exact heq
      rw [hall k] at hk
      exact h0 hk

end Reduction

section Main

variable {K L : Type u} [Field K] [LieRing L] [LieAlgebra K L]

/-- **Levi's theorem** (existence of a Levi subalgebra), assuming Whitehead's first lemma.

For a finite-dimensional Lie algebra `L` over a field `K` of characteristic zero there is a
Lie subalgebra `S ≤ L` which is a vector-space complement of the radical of `L`. -/
theorem exists_levi_subalgebra (hW : WhiteheadH1 K) [CharZero K] [FiniteDimensional K L] :
    ∃ S : LieSubalgebra K L,
      IsCompl S.toSubmodule (LieAlgebra.radical K L).toSubmodule := by
  suffices H : ∀ (n : ℕ) (M : Type u) [LieRing M] [LieAlgebra K M] [FiniteDimensional K M],
      Module.finrank K M ≤ n →
      ∃ S : LieSubalgebra K M, IsCompl S.toSubmodule (radical K M).toSubmodule by
    exact H (Module.finrank K L) L le_rfl
  intro n
  induction n with
  | zero =>
    intro M _ _ _ hM
    exact levi_step hW M (fun N _ _ _ h => absurd h (by omega))
  | succ n ihn =>
    intro M _ _ _ hM
    exact levi_step hW M (fun N _ _ _ h => ihn N (by omega))

/-- A Levi subalgebra has trivial radical (equivalently, in characteristic zero, is
semisimple). -/
theorem exists_levi_subalgebra_hasTrivialRadical (hW : WhiteheadH1 K) [CharZero K]
    [FiniteDimensional K L] :
    ∃ S : LieSubalgebra K L,
      IsCompl S.toSubmodule (LieAlgebra.radical K L).toSubmodule ∧
        LieAlgebra.HasTrivialRadical K S := by
  obtain ⟨S, hS⟩ := exists_levi_subalgebra (L := L) hW
  exact ⟨S, hS, hasTrivialRadical_of_isCompl S hS⟩

end Main



end Submission.Ado
