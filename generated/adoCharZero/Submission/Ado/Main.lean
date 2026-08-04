import Submission.Ado.Solvable
import Submission.Ado.Levi
import Submission.Ado.Closure

/-!
# Ado's theorem in characteristic zero

This file assembles the whole development: §6 of the informal proof, the *Levi
step*, which upgrades Ado's theorem for the (solvable) radical `𝔯` of `L` to
Ado's theorem for `L` itself.

## The argument

Write `𝔯 = radical K L`.  By Levi's theorem (`exists_levi_subalgebra'`) there is a Lie
**subalgebra** `𝔰 ≤ L` which is a vector-space complement of `𝔯`.  Let `σ : L →ₗ[K] L` be the
projection onto `𝔰` along `𝔯`; because `𝔰` is a subalgebra and `𝔯` is an ideal, `σ` is a
morphism of Lie algebras, and `x ↦ x - σ x` is the "crossed" projection onto `𝔯`.

Ado's theorem for the solvable algebra `𝔯`
(`exists_faithful_nilpotent_on_nilRadical_of_isSolvable`) supplies a faithful
finite-dimensional representation `ρ₀` of `𝔯` which is nilpotent on `nilRadical K 𝔯`;
`exists_good_ideal` turns it into a two-sided ideal `I` of `U(𝔯)` such that `W := U(𝔯) ⧸ I ^ m`
is finite-dimensional and `𝔯` still injects into `W`.

For `s ∈ L` the operator `z ↦ ⁅s, z⁆` is a derivation of `𝔯` carrying `𝔯` into `⁅L, L⁆ ⊓ 𝔯`,
which is nilpotent (`isNilpotent_derived_inf_radical`) and hence inside `nilRadical K L`;
therefore its extension to `U(𝔯)` preserves `I ^ m` (`envDeriv_mem_genIdeal`) and descends to
`W`.  Feeding

* `f x = ` class of `ι (x - σ x)` in `W`, and
* `D x = ` the descended derivation attached to `σ x`

to `lieHomOfMulLeftAddDeriv` produces a representation `ρ : L →ₗ⁅K⁆ End K W`.  If `ρ x = 0` then
`f x = 0`, so `x = σ x ∈ 𝔰`; if moreover `x` is central then `x ∈ center K L ≤ 𝔯`, and
`𝔰 ⊓ 𝔯 = ⊥` forces `x = 0`.  So `ρ` is injective on the centre and
`hasFaithfulFinRep_of_center` finishes the proof.

## Main results

* `Submission.Ado.levi_step`: the Levi step, for an arbitrary solvable ideal admitting a
  subalgebra complement.
* `Submission.Ado.hasFaithfulFinRep_charZero`: **Ado's theorem in characteristic zero.**
-/

universe u v

namespace Submission.Ado

open UniversalEnvelopingAlgebra LieAlgebra LieModule Module

attribute [local instance 100] LieRing.ofAssociativeRing

/-! ### Functoriality of `liftEndQuot` -/

section LiftEndQuot

variable {K : Type u} [Field K] {A : Type v} [Ring A] [Algebra K A]

theorem liftEndQuot_congr {P : Submodule K A} (hP : IsTwoSidedSub P) {E₁ E₂ : Module.End K A}
    (h₁ : ∀ u ∈ P, E₁ u ∈ P) (h₂ : ∀ u ∈ P, E₂ u ∈ P) (h : E₁ = E₂) :
    liftEndQuot hP E₁ h₁ = liftEndQuot hP E₂ h₂ := by
  subst h; rfl

theorem liftEndQuot_add {P : Submodule K A} (hP : IsTwoSidedSub P) {E₁ E₂ : Module.End K A}
    (h₁ : ∀ u ∈ P, E₁ u ∈ P) (h₂ : ∀ u ∈ P, E₂ u ∈ P) (h : ∀ u ∈ P, (E₁ + E₂) u ∈ P) :
    liftEndQuot hP (E₁ + E₂) h = liftEndQuot hP E₁ h₁ + liftEndQuot hP E₂ h₂ := by
  refine LinearMap.ext ?_
  rintro ⟨a⟩
  rfl

theorem liftEndQuot_smul {P : Submodule K A} (hP : IsTwoSidedSub P) (t : K)
    {E : Module.End K A} (hE : ∀ u ∈ P, E u ∈ P) (h : ∀ u ∈ P, (t • E) u ∈ P) :
    liftEndQuot hP (t • E) h = t • liftEndQuot hP E hE := by
  refine LinearMap.ext ?_
  rintro ⟨a⟩
  rfl

theorem liftEndQuot_lie {P : Submodule K A} (hP : IsTwoSidedSub P) {E₁ E₂ : Module.End K A}
    (h₁ : ∀ u ∈ P, E₁ u ∈ P) (h₂ : ∀ u ∈ P, E₂ u ∈ P) (h : ∀ u ∈ P, ⁅E₁, E₂⁆ u ∈ P) :
    liftEndQuot hP ⁅E₁, E₂⁆ h = ⁅liftEndQuot hP E₁ h₁, liftEndQuot hP E₂ h₂⁆ := by
  refine LinearMap.ext ?_
  rintro ⟨a⟩
  rfl

end LiftEndQuot

/-! ### A linear family of derivations, extended to the enveloping algebra and pushed to a
quotient -/

section QuotEnvDeriv

variable {K M N : Type u} [Field K] [LieRing M] [LieAlgebra K M] [LieRing N] [LieAlgebra K N]

theorem envDeriv_congr {D₁ D₂ : N →ₗ[K] N}
    (h₁ : ∀ x y : N, D₁ ⁅x, y⁆ = ⁅D₁ x, y⁆ + ⁅x, D₁ y⁆)
    (h₂ : ∀ x y : N, D₂ ⁅x, y⁆ = ⁅D₂ x, y⁆ + ⁅x, D₂ y⁆) (h : D₁ = D₂) :
    envDeriv D₁ h₁ = envDeriv D₂ h₂ := by
  subst h; rfl

variable (D : M →ₗ[K] N →ₗ[K] N)
  (hD : ∀ x : M, ∀ a b : N, D x ⁅a, b⁆ = ⁅D x a, b⁆ + ⁅a, D x b⁆)
  {P : Submodule K (UniversalEnvelopingAlgebra K N)} (hP : IsTwoSidedSub P)
  (hpres : ∀ x : M, ∀ u ∈ P, envDeriv (D x) (hD x) u ∈ P)

/-- Given a `K`-linear family `D` of derivations of `N`, the induced `K`-linear family of
derivations of `U(N) ⧸ P`. -/
noncomputable def quotEnvDeriv :
    M →ₗ[K] Module.End K (UniversalEnvelopingAlgebra K N ⧸ toIdeal P hP) where
  toFun x := liftEndQuot hP (envDeriv (D x) (hD x)) (hpres x)
  map_add' a b := by
    have hab : ∀ p r : N, (D a + D b) ⁅p, r⁆ = ⁅(D a + D b) p, r⁆ + ⁅p, (D a + D b) r⁆ := by
      intro p r
      simp only [LinearMap.add_apply, hD a p r, hD b p r, add_lie, lie_add]
      abel
    have hpres' : ∀ u ∈ P, (envDeriv (D a) (hD a) + envDeriv (D b) (hD b)) u ∈ P := fun u hu =>
      Submodule.add_mem _ (hpres a u hu) (hpres b u hu)
    have h1 : envDeriv (D (a + b)) (hD (a + b))
        = envDeriv (D a) (hD a) + envDeriv (D b) (hD b) := by
      rw [envDeriv_congr (hD (a + b)) hab (map_add D a b),
        envDeriv_add (D a) (D b) (hD a) (hD b) hab]
    rw [liftEndQuot_congr hP (hpres (a + b)) hpres' h1,
      liftEndQuot_add hP (hpres a) (hpres b) hpres']
  map_smul' t a := by
    have hta : ∀ p r : N, (t • D a) ⁅p, r⁆ = ⁅(t • D a) p, r⁆ + ⁅p, (t • D a) r⁆ := by
      intro p r
      simp only [LinearMap.smul_apply, hD a p r, smul_add, smul_lie, lie_smul]
    have hpres' : ∀ u ∈ P, (t • envDeriv (D a) (hD a)) u ∈ P := fun u hu =>
      Submodule.smul_mem _ t (hpres a u hu)
    have h1 : envDeriv (D (t • a)) (hD (t • a)) = t • envDeriv (D a) (hD a) := by
      rw [envDeriv_congr (hD (t • a)) hta (map_smul D t a),
        envDeriv_smul (D a) (hD a) t hta]
    rw [liftEndQuot_congr hP (hpres (t • a)) hpres' h1,
      liftEndQuot_smul hP t (hpres a) hpres']
    rfl

theorem quotEnvDeriv_mk (x : M) (u : UniversalEnvelopingAlgebra K N) :
    quotEnvDeriv D hD hP hpres x
        (Submodule.Quotient.mk u : UniversalEnvelopingAlgebra K N ⧸ toIdeal P hP)
      = Submodule.Quotient.mk (envDeriv (D x) (hD x) u) := rfl

theorem isDeriv_quotEnvDeriv (x : M) : IsDeriv (quotEnvDeriv D hD hP hpres x) :=
  isDeriv_liftEndQuot hP (hpres x) (envDeriv_isDeriv (D x) (hD x))

theorem quotEnvDeriv_lie (hDlie : ∀ x y : M, D ⁅x, y⁆ = ⁅D x, D y⁆) (x y : M) :
    quotEnvDeriv D hD hP hpres ⁅x, y⁆
      = ⁅quotEnvDeriv D hD hP hpres x, quotEnvDeriv D hD hP hpres y⁆ := by
  have hbr : ∀ (E₁ E₂ : N →ₗ[K] N) (a : N), (⁅E₁, E₂⁆ : N →ₗ[K] N) a = E₁ (E₂ a) - E₂ (E₁ a) :=
    fun _ _ _ => rfl
  have hxy : ∀ p r : N, ⁅D x, D y⁆ ⁅p, r⁆ = ⁅⁅D x, D y⁆ p, r⁆ + ⁅p, ⁅D x, D y⁆ r⁆ := by
    intro p r
    rw [hbr, hbr, hbr, hD y p r, hD x p r, map_add, map_add, hD x (D y p) r, hD x p (D y r),
      hD y (D x p) r, hD y p (D x r)]
    simp only [sub_lie, lie_sub]
    abel
  have hpres' : ∀ u ∈ P, ⁅envDeriv (D x) (hD x), envDeriv (D y) (hD y)⁆ u ∈ P := by
    intro u hu
    have hval : ⁅envDeriv (D x) (hD x), envDeriv (D y) (hD y)⁆ u
        = envDeriv (D x) (hD x) (envDeriv (D y) (hD y) u)
          - envDeriv (D y) (hD y) (envDeriv (D x) (hD x) u) := rfl
    rw [hval]
    exact Submodule.sub_mem _ (hpres x _ (hpres y u hu)) (hpres y _ (hpres x u hu))
  have h1 : envDeriv (D ⁅x, y⁆) (hD ⁅x, y⁆)
      = ⁅envDeriv (D x) (hD x), envDeriv (D y) (hD y)⁆ := by
    rw [envDeriv_congr (hD ⁅x, y⁆) hxy (hDlie x y), envDeriv_lie (D x) (D y) (hD x) (hD y) hxy]
  show liftEndQuot hP (envDeriv (D ⁅x, y⁆) (hD ⁅x, y⁆)) (hpres ⁅x, y⁆)
      = ⁅liftEndQuot hP (envDeriv (D x) (hD x)) (hpres x),
        liftEndQuot hP (envDeriv (D y) (hD y)) (hpres y)⁆
  rw [liftEndQuot_congr hP (hpres ⁅x, y⁆) hpres' h1,
    liftEndQuot_lie hP (hpres x) (hpres y) hpres']

end QuotEnvDeriv

/-! ### The Levi step -/

section LeviStep

variable {K L : Type u} [Field K] [LieRing L] [LieAlgebra K L]

/-- An element of an ideal `A` of `L` which lies in the nilradical of `L` lies in the nilradical
of `A`. -/
theorem mem_nilRadical_of_coe_mem [FiniteDimensional K L] (A : LieIdeal K L) (z : ↥A)
    (hz : (z : L) ∈ nilRadical K L) : z ∈ nilRadical K ↥A := by
  set N₁ : LieIdeal K ↥A := LieIdeal.comap A.incl (nilRadical K L) with hN₁
  let g : ↥N₁ →ₗ⁅K⁆ ↥(nilRadical K L) :=
    { toFun := fun w => ⟨((w : ↥A) : L), w.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      map_lie' := rfl }
  have hginj : Function.Injective g := by
    intro a b hab
    have h1 := congrArg (fun w : ↥(nilRadical K L) => (w : L)) hab
    exact Subtype.ext (Subtype.ext h1)
  haveI : LieRing.IsNilpotent ↥N₁ := hginj.lieAlgebra_isNilpotent
  exact le_nilRadical (I := N₁) (show z ∈ N₁ from hz)

/-- **§6, the Levi step.** Let `R` be a solvable ideal of `L` which contains the centre and is
such that `⁅L, R⁆` consists of elements of the nilradical, and suppose `R` admits a Lie
subalgebra as a vector-space complement.  Then `L` has a faithful finite-dimensional
representation. -/
theorem levi_step [CharZero K] [FiniteDimensional K L]
    {R : LieIdeal K L} [LieAlgebra.IsSolvable ↥R] (S : LieSubalgebra K L)
    (hcompl : IsCompl S.toSubmodule (LieSubmodule.toSubmodule R))
    (hcen : LieAlgebra.center K L ≤ R)
    (hnil : ∀ x y : L, y ∈ R → ⁅x, y⁆ ∈ nilRadical K L) :
    HasFaithfulFinRep K L := by
  classical
  -- `R` is stable under left brackets too
  have hlieleft : ∀ a b : L, a ∈ R → ⁅a, b⁆ ∈ R := by
    intro a b ha
    have h : ⁅a, b⁆ = -⁅b, a⁆ := by rw [← lie_skew b a, neg_neg]
    rw [h]
    exact neg_mem (R.lie_mem ha)
  -- the linear projection onto `S` along `R`
  set σ : L →ₗ[K] L := (S.toSubmodule).projection (LieSubmodule.toSubmodule R) hcompl with hσdef
  have hσmem : ∀ x : L, σ x ∈ S := fun x => Submodule.projection_apply_mem hcompl x
  have hsubmem : ∀ x : L, x - σ x ∈ R := fun x => Submodule.sub_projection_mem hcompl x
  have hσS : ∀ x : L, x ∈ S → σ x = x := fun x hx =>
    Submodule.projection_apply_of_mem_left hcompl hx
  have hσR : ∀ x : L, x ∈ R → σ x = 0 := fun x hx =>
    Submodule.projection_apply_of_mem_right hcompl hx
  -- `σ` is a morphism of Lie algebras: this is where `S` being a subalgebra is used
  have hσlie : ∀ x y : L, σ ⁅x, y⁆ = ⁅σ x, σ y⁆ := by
    intro x y
    have hdecomp : ⁅x, y⁆ = ⁅σ x, σ y⁆ +
        (⁅σ x, y - σ y⁆ + ⁅x - σ x, σ y⁆ + ⁅x - σ x, y - σ y⁆) := by
      simp only [lie_sub, sub_lie]
      abel
    have hSmem : ⁅σ x, σ y⁆ ∈ S := S.lie_mem (hσmem x) (hσmem y)
    have hRmem : ⁅σ x, y - σ y⁆ + ⁅x - σ x, σ y⁆ + ⁅x - σ x, y - σ y⁆ ∈ R :=
      R.add_mem (R.add_mem (R.lie_mem (hsubmem y)) (hlieleft _ _ (hsubmem x)))
        (R.lie_mem (hsubmem y))
    rw [hdecomp, map_add, hσS _ hSmem, hσR _ hRmem, add_zero]
  -- the derivation of `R` attached to an element of `L`
  set Dof : L →ₗ[K] ↥R →ₗ[K] ↥R :=
    { toFun := fun x =>
        { toFun := fun z => ⟨⁅x, (z : L)⁆, R.lie_mem z.2⟩
          map_add' := fun a b => Subtype.ext (by simp)
          map_smul' := fun t a => Subtype.ext (by simp) }
      map_add' := fun a b => LinearMap.ext fun z => Subtype.ext (by simp [add_lie])
      map_smul' := fun t a => LinearMap.ext fun z => Subtype.ext (by simp) } with hDofdef
  have hDofval : ∀ (x : L) (z : ↥R), ((Dof x z : ↥R) : L) = ⁅x, (z : L)⁆ := fun _ _ => rfl
  have hDofderiv : ∀ x : L, ∀ a b : ↥R, Dof x ⁅a, b⁆ = ⁅Dof x a, b⁆ + ⁅a, Dof x b⁆ := by
    intro x a b
    apply Subtype.ext
    show ⁅x, ⁅(a : L), (b : L)⁆⁆ = _
    rw [leibniz_lie x (a : L) (b : L)]
    rfl
  have hDoflie : ∀ x y : L, Dof ⁅x, y⁆ = ⁅Dof x, Dof y⁆ := by
    intro x y
    refine LinearMap.ext fun z => Subtype.ext ?_
    show ⁅⁅x, y⁆, (z : L)⁆ = ⁅x, ⁅y, (z : L)⁆⁆ - ⁅y, ⁅x, (z : L)⁆⁆
    rw [lie_lie]
  -- the composite family, indexed by `L` through `σ`
  set Dσ : L →ₗ[K] ↥R →ₗ[K] ↥R := Dof.comp σ with hDσdef
  have hDσval : ∀ x : L, Dσ x = Dof (σ x) := fun _ => rfl
  have hDσderiv : ∀ x : L, ∀ a b : ↥R, Dσ x ⁅a, b⁆ = ⁅Dσ x a, b⁆ + ⁅a, Dσ x b⁆ := fun x =>
    hDofderiv (σ x)
  have hDσlie : ∀ x y : L, Dσ ⁅x, y⁆ = ⁅Dσ x, Dσ y⁆ := by
    intro x y
    show Dof (σ ⁅x, y⁆) = ⁅Dof (σ x), Dof (σ y)⁆
    rw [hσlie x y, hDoflie]
  -- the derivations land in the nilradical of `R`
  have hDσnil : ∀ (x : L) (z : ↥R),
      Dσ x z ∈ LieSubmodule.toSubmodule (nilRadical K ↥R) := by
    intro x z
    refine mem_nilRadical_of_coe_mem R _ ?_
    show ⁅σ x, (z : L)⁆ ∈ nilRadical K L
    exact hnil _ _ z.2
  -- Ado's theorem for the solvable ideal `R`
  obtain ⟨V₀, i1, i2, i3, ρ₀, hinj, hnil0⟩ :=
    exists_faithful_nilpotent_on_nilRadical_of_isSolvable (K := K) (L := ↥R)
  letI := i1; letI := i2; letI := i3
  obtain ⟨I, m, hI, hm1, hJI, hfaith, E, hE, hEtop⟩ := exists_good_ideal ρ₀ hinj hnil0
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have hP : IsTwoSidedSub (I ^ (m' + 1)) := hI.pow m'
  -- the extended derivations preserve every power of `I`
  have hΔJ : ∀ (x : L) (u : UniversalEnvelopingAlgebra K ↥R),
      envDeriv (Dσ x) (hDσderiv x) u ∈
        genIdeal (LieSubmodule.toSubmodule (nilRadical K ↥R)) :=
    fun x => envDeriv_mem_genIdeal (Dσ x) (hDσderiv x) (hDσnil x)
  have hΔP : ∀ (x : L) (r : ℕ), ∀ u ∈ I ^ r, envDeriv (Dσ x) (hDσderiv x) u ∈ I ^ r := by
    intro x r
    induction r with
    | zero =>
      intro u hu
      rw [pow_zero] at hu ⊢
      obtain ⟨c, rfl⟩ := Submodule.mem_one.mp hu
      rw [Algebra.algebraMap_eq_smul_one, map_smul, envDeriv_one, smul_zero]
      exact Submodule.zero_mem _
    | succ r ih =>
      intro u hu
      rw [pow_succ] at hu ⊢
      refine Submodule.mul_induction_on hu ?_ ?_
      · intro a ha b hb
        rw [envDeriv_isDeriv (Dσ x) (hDσderiv x) a b]
        exact Submodule.add_mem _ (Submodule.mul_mem_mul (ih a ha) hb)
          (Submodule.mul_mem_mul ha (hJI (hΔJ x b)))
      · intro a b ha hb
        rw [map_add]
        exact Submodule.add_mem _ ha hb
  -- the finite-dimensional algebra `W`
  haveI : FiniteDimensional K
      (UniversalEnvelopingAlgebra K ↥R ⧸ toIdeal (I ^ (m' + 1)) hP) :=
    finiteDimensional_quotient_toIdeal hP hE hEtop
  set W := UniversalEnvelopingAlgebra K ↥R ⧸ toIdeal (I ^ (m' + 1)) hP with hWdef
  set q : UniversalEnvelopingAlgebra K ↥R →ₐ[K] W :=
    Ideal.Quotient.mkₐ K (toIdeal (I ^ (m' + 1)) hP) with hq
  have hqzero : ∀ u, q u = 0 ↔ u ∈ I ^ (m' + 1) := by
    intro u
    rw [hq]
    exact Ideal.Quotient.eq_zero_iff_mem
  -- the crossed projection onto `R`
  set proj : L →ₗ[K] ↥R :=
    { toFun := fun x => ⟨x - σ x, hsubmem x⟩
      map_add' := fun a b => Subtype.ext (by
        show a + b - σ (a + b) = a - σ a + (b - σ b)
        rw [map_add]; abel)
      map_smul' := fun t a => Subtype.ext (by
        show t • a - σ (t • a) = t • (a - σ a)
        rw [map_smul, smul_sub]) } with hprojdef
  have hprojval : ∀ x : L, ((proj x : ↥R) : L) = x - σ x := fun _ => rfl
  set f : L →ₗ[K] W :=
    (q.toLinearMap).comp
      (((ι K : ↥R →ₗ⁅K⁆ UniversalEnvelopingAlgebra K ↥R) : ↥R →ₗ[K] _).comp proj) with hf
  have hfval : ∀ x : L, f x = q (ι K (proj x)) := fun _ => rfl
  -- the family of derivations of `W`
  set Drep : L →ₗ[K] Module.End K W :=
    quotEnvDeriv Dσ hDσderiv hP (fun x => hΔP x (m' + 1)) with hDrepdef
  have hderiv : ∀ x : L, IsDeriv (Drep x) := fun x =>
    isDeriv_quotEnvDeriv Dσ hDσderiv hP (fun x => hΔP x (m' + 1)) x
  have hDlie : ∀ x y : L, Drep ⁅x, y⁆ = ⁅Drep x, Drep y⁆ :=
    quotEnvDeriv_lie Dσ hDσderiv hP (fun x => hΔP x (m' + 1)) hDσlie
  have hDrepq : ∀ (x : L) (z : ↥R), Drep x (q (ι K z)) = q (ι K (Dσ x z)) := by
    intro x z
    show (Submodule.Quotient.mk (envDeriv (Dσ x) (hDσderiv x) (ι K z)) : W) = _
    rw [envDeriv_ι]
    rfl
  -- the crossed condition
  have hkeyL : ∀ x y : L,
      proj ⁅x, y⁆ = ⁅proj x, proj y⁆ + Dσ x (proj y) - Dσ y (proj x) := by
    intro x y
    apply Subtype.ext
    have h1 : ⁅x, σ y⁆ = -⁅σ y, x⁆ := by rw [← lie_skew (σ y) x, neg_neg]
    have h2 : ⁅σ y, σ x⁆ = -⁅σ x, σ y⁆ := by rw [← lie_skew (σ x) (σ y), neg_neg]
    show ⁅x, y⁆ - σ ⁅x, y⁆
        = ⁅x - σ x, y - σ y⁆ + ⁅σ x, y - σ y⁆ - ⁅σ y, x - σ x⁆
    rw [hσlie x y]
    simp only [sub_lie, lie_sub, h1, h2]
    abel
  have hlie : ∀ z w : ↥R, (ι K ⁅z, w⁆ : UniversalEnvelopingAlgebra K ↥R)
      = ι K z * ι K w - ι K w * ι K z := by
    intro z w
    rw [← LieRing.of_associative_ring_bracket]
    exact LieHom.map_lie (ι K) z w
  have hU : ∀ x y : L, (ι K (proj ⁅x, y⁆) : UniversalEnvelopingAlgebra K ↥R)
      = ι K (proj x) * ι K (proj y) - ι K (proj y) * ι K (proj x)
        + ι K (Dσ x (proj y)) - ι K (Dσ y (proj x)) := by
    intro x y
    rw [hkeyL x y, map_sub, map_add, hlie]
  have hcrossed : ∀ x y : L,
      f ⁅x, y⁆ = f x * f y - f y * f x + Drep x (f y) - Drep y (f x) := by
    intro x y
    simp only [hfval, hDrepq]
    rw [hU x y]
    simp only [map_sub, map_add, map_mul]
  set ρ : L →ₗ⁅K⁆ Module.End K W :=
    lieHomOfMulLeftAddDeriv f Drep hderiv hDlie hcrossed with hρ
  -- injectivity on the centre
  refine hasFaithfulFinRep_of_center ρ ?_
  intro x hx hcent
  rw [hρ, lieHomOfMulLeftAddDeriv_eq_zero_iff] at hx
  have hfx : q (ι K (proj x)) = 0 := by rw [← hfval]; exact hx.1
  have hprojx : proj x = 0 := hfaith _ ((hqzero _).mp hfx)
  have hxS : x ∈ S.toSubmodule := by
    have h : ((proj x : ↥R) : L) = 0 := by rw [hprojx]; rfl
    rw [hprojval x] at h
    rw [sub_eq_zero.mp h]
    exact Submodule.projection_apply_mem hcompl x
  have hxR : x ∈ LieSubmodule.toSubmodule R := by
    have hc : x ∈ LieAlgebra.center K L :=
      (LieModule.mem_maxTrivSubmodule K L L x).mpr fun y => by
        rw [← lie_skew, hcent y, neg_zero]
    exact hcen hc
  have hbot : x ∈ (⊥ : Submodule K L) := by
    rw [← hcompl.inf_eq_bot]
    exact ⟨hxS, hxR⟩
  exact (Submodule.mem_bot K).mp hbot

/-- **Ado's theorem in characteristic zero.**  Every finite-dimensional Lie algebra over a field
of characteristic zero has a faithful finite-dimensional representation. -/
theorem hasFaithfulFinRep_charZero [CharZero K] [FiniteDimensional K L] :
    HasFaithfulFinRep K L := by
  obtain ⟨S, hcompl⟩ := exists_levi_subalgebra' (K := K) (L := L)
  refine levi_step S hcompl (LieAlgebra.center_le_radical K L) ?_
  intro x y hy
  haveI : LieRing.IsNilpotent
      ↥(⁅(⊤ : LieIdeal K L), (⊤ : LieIdeal K L)⁆ ⊓ LieAlgebra.radical K L : LieIdeal K L) :=
    isNilpotent_derived_inf_radical
  refine le_nilRadical (I := ⁅(⊤ : LieIdeal K L), (⊤ : LieIdeal K L)⁆ ⊓ LieAlgebra.radical K L)
    ⟨?_, LieSubmodule.lie_mem _ hy⟩
  exact LieSubmodule.lie_coe_mem_lie (⟨x, trivial⟩ : ↥(⊤ : LieIdeal K L))
    (⟨y, trivial⟩ : ↥(⊤ : LieSubmodule K L L))

end LeviStep

end Submission.Ado
