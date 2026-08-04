import Submission.Ado.Casimir

/-!
# Weyl's theorem on complete reducibility and Whitehead's first lemma

Let `K` be a field of characteristic zero and `L` a finite-dimensional semisimple Lie algebra
over `K` (`LieAlgebra.HasTrivialRadical K L`).  This file proves:

* `Submission.Ado.exists_isCompl_of_lie_mem'` — the key case: if `M` is a finite-dimensional
  `L`-module and `N` is a submodule with `⁅L, M⁆ ≤ N`, then `N` has an `L`-module complement;
* `Submission.Ado.whitehead_h1` — **Whitehead's first lemma**: every `1`-cocycle
  `c : L →ₗ[K] M` (i.e. `c ⁅x, y⁆ = ⁅x, c y⁆ - ⁅y, c x⁆`) is a coboundary, `c x = ⁅x, m⁆`;
* `Submission.Ado.exists_isCompl_of_hasTrivialRadical` — **Weyl's theorem**: every
  `L`-submodule of a finite-dimensional `L`-module has an `L`-module complement.

## Outline of the proofs

The key case is proved by induction on `dim M` using the Casimir element `c` of `M` built in
`Submission.Ado.Casimir`.  Since the trace form of `M` need not be nondegenerate on `L`, the
Casimir element is built for the ideal `traceCore K L M`, the Killing-orthogonal complement of
the radical `traceRadical K L M` of the trace form.  On that ideal the trace form is
nondegenerate, the Casimir element still commutes with all of `L` (because the two ideals
commute), and its trace is `dim (traceCore K L M)`, which is nonzero unless `L` acts trivially
on `M` (a form of Cartan's criterion, `lie_eq_zero_of_traceForm_eq_zero`).

Given that, `c` maps `M` into `N` and is not nilpotent, so the Fitting decomposition
`M = ker cᵏ ⊕ im cᵏ` has a nonzero second summand contained in `N`; the induction hypothesis
applied to `ker cᵏ` finishes the proof.

Whitehead's first lemma follows by applying the key case to `M × K` with the action
`x · (m, t) = (⁅x, m⁆ + t • c x, 0)`, and Weyl's theorem follows from Whitehead's lemma applied
to the module of `K`-linear maps `V → W` vanishing on `W`, the cocycle being the coboundary of
a `K`-linear projection of `V` onto `W`.
-/

namespace Submission.Ado

open Module (finrank)
open LinearMap (trace)

universe u

section Semisimple

variable (K L : Type*) [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L] [LieAlgebra.HasTrivialRadical K L]

/-- A semisimple Lie algebra is its own derived subalgebra. -/
theorem lie_top_top_eq_top : ⁅(⊤ : LieIdeal K L), (⊤ : LieIdeal K L)⁆ = ⊤ := by
  set D : LieIdeal K L := ⁅(⊤ : LieIdeal K L), (⊤ : LieIdeal K L)⁆ with hD
  have hc : IsCompl D (LieIdeal.killingCompl K L D) := LieIdeal.isCompl_killingCompl D
  have hEbot : LieIdeal.killingCompl K L D = ⊥ := by
    refine (LieAlgebra.hasTrivialRadical_iff_no_abelian_ideals K L).mp inferInstance _
      ((LieSubmodule.lie_abelian_iff_lie_self_eq_bot _).mpr (le_bot_iff.mp ?_))
    refine le_trans (le_inf ?_ (LieSubmodule.lie_le_left _ _)) (le_of_eq hc.inf_eq_bot)
    rw [hD]
    exact LieSubmodule.mono_lie le_top le_top
  have h := hc.sup_eq_top
  rwa [hEbot, sup_bot_eq] at h

variable {M : Type*} [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]

/-- Since `L = ⁅L, L⁆`, the first term of the lower central series of `M` is contained in the
second one. -/
theorem lie_top_le_lie_lie_top :
    ⁅(⊤ : LieIdeal K L), (⊤ : LieSubmodule K L M)⁆ ≤
      ⁅(⊤ : LieIdeal K L), ⁅(⊤ : LieIdeal K L), (⊤ : LieSubmodule K L M)⁆⁆ := by
  have key : ∀ x ∈ (⁅(⊤ : LieIdeal K L), (⊤ : LieIdeal K L)⁆ : LieIdeal K L), ∀ m : M,
      ⁅x, m⁆ ∈ ⁅(⊤ : LieIdeal K L), ⁅(⊤ : LieIdeal K L), (⊤ : LieSubmodule K L M)⁆⁆ := by
    intro x hx
    rw [← LieSubmodule.mem_toSubmodule, LieSubmodule.lieIdeal_oper_eq_linear_span'] at hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
        obtain ⟨a, -, b, -, rfl⟩ := hy
        intro m
        rw [lie_lie]
        exact sub_mem
          (LieSubmodule.lie_mem_lie (LieSubmodule.mem_top a)
            (LieSubmodule.lie_mem_lie (LieSubmodule.mem_top b) (LieSubmodule.mem_top m)))
          (LieSubmodule.lie_mem_lie (LieSubmodule.mem_top b)
            (LieSubmodule.lie_mem_lie (LieSubmodule.mem_top a) (LieSubmodule.mem_top m)))
    | zero => intro m; simp
    | add y z _ _ hy hz => intro m; rw [add_lie]; exact add_mem (hy m) (hz m)
    | smul c y _ hy => intro m; rw [smul_lie]; exact Submodule.smul_mem _ c (hy m)
  rw [LieSubmodule.lie_le_iff]
  intro x _ m _
  exact key x (by rw [lie_top_top_eq_top K L]; exact LieSubmodule.mem_top x) m

/-- **Cartan's criterion, module form.** If the trace form of a module over a semisimple Lie
algebra vanishes identically, then the action is trivial. -/
theorem lie_eq_zero_of_traceForm_eq_zero [FiniteDimensional K M]
    (h : LieModule.traceForm K L M = 0) (x : L) (m : M) : ⁅x, m⁆ = 0 := by
  have hnil0 : LieModule.IsNilpotent (LieAlgebra.derivedSeries K L 1) M :=
    LieModule.isNilpotent_derivedSeries_of_traceForm_eq_zero h
  rw [show LieAlgebra.derivedSeries K L 1 = ⊤ from lie_top_top_eq_top K L] at hnil0
  have hnil : LieModule.IsNilpotent L M := by
    rw [LieModule.isNilpotent_iff_forall' (R := K)]
    exact fun y => (LieModule.isNilpotent_iff_forall' (R := K)).mp hnil0
      ⟨y, LieSubmodule.mem_top y⟩
  obtain ⟨k, hk⟩ := (LieModule.isNilpotent_iff K L M).mp hnil
  have hlcs1 : LieModule.lowerCentralSeries K L M 1 =
      ⁅(⊤ : LieIdeal K L), (⊤ : LieSubmodule K L M)⁆ := rfl
  have hmono : ∀ j : ℕ, ⁅(⊤ : LieIdeal K L), (⊤ : LieSubmodule K L M)⁆ ≤
      LieModule.lowerCentralSeries K L M (j + 1) := by
    intro j
    induction j with
    | zero => exact le_of_eq hlcs1.symm
    | succ j ih =>
        rw [LieModule.lowerCentralSeries_succ]
        exact le_trans (lie_top_le_lie_lie_top K L) (LieSubmodule.mono_lie_right _ ih)
  have hbot : ⁅(⊤ : LieIdeal K L), (⊤ : LieSubmodule K L M)⁆ = ⊥ := by
    refine le_bot_iff.mp (le_trans (hmono k) (le_of_eq ?_))
    rw [LieModule.lowerCentralSeries_succ, hk, LieSubmodule.lie_bot]
  exact (LieSubmodule.lie_eq_bot_iff _ _).mp hbot x (LieSubmodule.mem_top x) m
    (LieSubmodule.mem_top m)

end Semisimple

section CasimirSetup

variable (K L M : Type*) [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L] [LieAlgebra.HasTrivialRadical K L]
  [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]

/-- The radical of the trace form of `M`, a Lie ideal of `L`. -/
noncomputable def traceRadical : LieIdeal K L :=
  LieAlgebra.InvariantForm.orthogonal (LieModule.traceForm K L M)
    (LieModule.traceForm_lieInvariant K L M) ⊤

omit [CharZero K] [FiniteDimensional K L] [LieAlgebra.HasTrivialRadical K L] in
theorem mem_traceRadical {y : L} :
    y ∈ traceRadical K L M ↔ ∀ x : L, LieModule.traceForm K L M x y = 0 := by
  rw [traceRadical, LieAlgebra.InvariantForm.mem_orthogonal]
  exact ⟨fun h x => h x (LieSubmodule.mem_top x), fun h x _ => h x⟩

/-- A Killing-orthogonal complement of the trace radical.  The trace form of `M` restricts to a
nondegenerate form on it, so it carries a Casimir element. -/
noncomputable def traceCore : LieIdeal K L := LieIdeal.killingCompl K L (traceRadical K L M)

theorem isCompl_traceRadical_traceCore : IsCompl (traceRadical K L M) (traceCore K L M) :=
  LieIdeal.isCompl_killingCompl _

/-- Every element of `L` splits as a sum of an element of the trace radical and an element of
the trace core. -/
theorem exists_add_mem_traceRadical_traceCore (z : L) :
    ∃ r ∈ traceRadical K L M, ∃ l ∈ traceCore K L M, r + l = z := by
  have h : (traceRadical K L M).toSubmodule ⊔ (traceCore K L M).toSubmodule = ⊤ := by
    rw [← LieSubmodule.sup_toSubmodule, (isCompl_traceRadical_traceCore K L M).sup_eq_top,
      LieSubmodule.top_toSubmodule]
  exact Submodule.mem_sup.mp (h ▸ Submodule.mem_top)

theorem traceForm_traceCore_nondegenerate :
    (LieModule.traceForm K (traceCore K L M) M).Nondegenerate := by
  have hsep : ∀ x : traceCore K L M,
      (∀ y : traceCore K L M, LieModule.traceForm K (traceCore K L M) M x y = 0) → x = 0 := by
    intro x hx
    have hmem : (x : L) ∈ traceRadical K L M := by
      rw [mem_traceRadical]
      intro z
      obtain ⟨r, hr, l, hl, rfl⟩ := exists_add_mem_traceRadical_traceCore K L M z
      rw [map_add, LinearMap.add_apply]
      have h1 : LieModule.traceForm K L M r (x : L) = 0 := by
        rw [LieModule.traceForm_comm K L M]
        exact (mem_traceRadical K L M).mp hr (x : L)
      have h2 : LieModule.traceForm K L M l (x : L) = 0 := by
        rw [LieModule.traceForm_comm K L M]
        exact hx ⟨l, hl⟩
      rw [h1, h2, add_zero]
    have hbot : (x : L) ∈ traceRadical K L M ⊓ traceCore K L M := ⟨hmem, x.2⟩
    rw [(isCompl_traceRadical_traceCore K L M).inf_eq_bot] at hbot
    exact Subtype.ext (by simpa using hbot)
  refine ⟨hsep, fun y hy => hsep y fun z => ?_⟩
  rw [LieModule.traceForm_comm K (traceCore K L M) M]
  exact hy z

/-- The Casimir element attached to the module `M`. -/
noncomputable def weylCasimir : Module.End K M :=
  casimirOfBasis (traceForm_traceCore_nondegenerate K L M)
    (Module.finBasis K (traceCore K L M))

theorem trace_weylCasimir [FiniteDimensional K M] :
    trace K M (weylCasimir K L M) = (finrank K (traceCore K L M) : K) :=
  trace_casimirOfBasis _ _

/-- Elements of the trace radical act trivially on the trace core. -/
theorem lie_eq_zero_of_mem_traceRadical_traceCore {r l : L} (hr : r ∈ traceRadical K L M)
    (hl : l ∈ traceCore K L M) : ⁅r, l⁆ = 0 := by
  have h : ⁅traceRadical K L M, traceCore K L M⁆ = (⊥ : LieIdeal K L) :=
    le_bot_iff.mp (le_trans (LieSubmodule.lie_le_inf _ _)
      (le_of_eq (isCompl_traceRadical_traceCore K L M).inf_eq_bot))
  exact (LieSubmodule.lie_eq_bot_iff _ _).mp h r hr l hl

/-- The Casimir element commutes with the action of every element of `L`. -/
theorem commute_weylCasimir (x : L) :
    Commute (LieModule.toEnd K L M x) (weylCasimir K L M) := by
  obtain ⟨r, hr, l, hl, rfl⟩ := exists_add_mem_traceRadical_traceCore K L M x
  rw [map_add]
  refine Commute.add_left ?_ ?_
  · refine commute_casimirOfBasis _ _ _ fun y => ?_
    have hzero : LieModule.toEnd K L M ⁅r, (y : L)⁆ = 0 := by
      rw [lie_eq_zero_of_mem_traceRadical_traceCore K L M hr y.2, map_zero]
    rw [toEnd_lie_eq K L M, sub_eq_zero] at hzero
    exact hzero
  · have : LieModule.toEnd K L M l =
        LieModule.toEnd K (traceCore K L M) M ⟨l, hl⟩ := rfl
    rw [this]
    exact casimirOfBasis_mul_comm _ _ _

/-- The Casimir element maps `M` into any submodule containing `⁅L, M⁆`. -/
theorem weylCasimir_mem (N : LieSubmodule K L M) (hN : ∀ (x : L) (m : M), ⁅x, m⁆ ∈ N) (m : M) :
    weylCasimir K L M m ∈ N := by
  rw [weylCasimir, casimirOfBasis_apply]
  exact Submodule.sum_mem _ fun i _ => hN _ _

/-- The Casimir element is a map of `L`-modules. -/
theorem weylCasimir_apply_lie (x : L) (m : M) :
    weylCasimir K L M ⁅x, m⁆ = ⁅x, weylCasimir K L M m⁆ := by
  have h := congrArg (fun f : Module.End K M => f m) (commute_weylCasimir K L M x)
  simpa [Module.End.mul_apply] using h.symm

theorem traceForm_eq_zero_of_traceCore_eq_bot (h : traceCore K L M = ⊥) :
    LieModule.traceForm K L M = 0 := by
  have htop : traceRadical K L M = ⊤ := by
    have h2 := (isCompl_traceRadical_traceCore K L M).sup_eq_top
    rwa [h, sup_bot_eq] at h2
  ext x y
  exact (mem_traceRadical K L M).mp (by rw [htop]; exact LieSubmodule.mem_top y) x

theorem finrank_traceCore_ne_zero [FiniteDimensional K M]
    (hnt : ¬ ∀ (x : L) (m : M), ⁅x, m⁆ = 0) : finrank K (traceCore K L M) ≠ 0 := by
  intro h
  refine hnt fun x m => lie_eq_zero_of_traceForm_eq_zero K L
    (traceForm_eq_zero_of_traceCore_eq_bot K L M ?_) x m
  rw [← LieSubmodule.toSubmodule_inj, LieSubmodule.bot_toSubmodule]
  exact Submodule.finrank_eq_zero.mp h

/-- If the action of `L` on `M` is nontrivial, the Casimir element is not nilpotent. -/
theorem not_isNilpotent_weylCasimir [FiniteDimensional K M]
    (hnt : ¬ ∀ (x : L) (m : M), ⁅x, m⁆ = 0) : ¬ IsNilpotent (weylCasimir K L M) := by
  intro hnil
  have h0 : trace K M (weylCasimir K L M) = 0 :=
    (LinearMap.isNilpotent_trace_of_isNilpotent hnil).eq_zero
  rw [trace_weylCasimir] at h0
  exact finrank_traceCore_ne_zero K L M hnt (by exact_mod_cast h0)

end CasimirSetup

universe v

section Aux

variable (K L : Type*) [Field K] [LieRing L]
  {M : Type v} [AddCommGroup M] [Module K M] [LieRingModule L M]

/-- The kernel of an endomorphism commuting with the `L`-action, as a Lie submodule. -/
def kerLie (c : Module.End K M) (hc : ∀ (x : L) (m : M), c ⁅x, m⁆ = ⁅x, c m⁆) :
    LieSubmodule K L M where
  __ := LinearMap.ker c
  lie_mem := by
    intro x m hm
    simp only [Submodule.mem_toAddSubmonoid, AddSubsemigroup.mem_carrier,
      AddSubmonoid.mem_toSubsemigroup, LinearMap.mem_ker] at hm ⊢
    rw [hc, hm, lie_zero]

@[simp] theorem kerLie_toSubmodule (c : Module.End K M)
    (hc : ∀ (x : L) (m : M), c ⁅x, m⁆ = ⁅x, c m⁆) :
    (kerLie K L c hc).toSubmodule = LinearMap.ker c := rfl

/-- The range of an endomorphism commuting with the `L`-action, as a Lie submodule. -/
def rangeLie (c : Module.End K M) (hc : ∀ (x : L) (m : M), c ⁅x, m⁆ = ⁅x, c m⁆) :
    LieSubmodule K L M where
  __ := LinearMap.range c
  lie_mem := by
    intro x m hm
    simp only [Submodule.mem_toAddSubmonoid, AddSubsemigroup.mem_carrier,
      AddSubmonoid.mem_toSubsemigroup, LinearMap.mem_range] at hm ⊢
    obtain ⟨v, rfl⟩ := hm
    exact ⟨⁅x, v⁆, hc x v⟩

@[simp] theorem rangeLie_toSubmodule (c : Module.End K M)
    (hc : ∀ (x : L) (m : M), c ⁅x, m⁆ = ⁅x, c m⁆) :
    (rangeLie K L c hc).toSubmodule = LinearMap.range c := rfl

/-- If `L` acts trivially on `M`, every `K`-subspace is an `L`-submodule and complements exist. -/
theorem exists_isCompl_of_trivial (htriv : ∀ (x : L) (m : M), ⁅x, m⁆ = 0)
    (N : LieSubmodule K L M) : ∃ X : LieSubmodule K L M, IsCompl N X := by
  obtain ⟨q, hq⟩ := Submodule.exists_isCompl N.toSubmodule
  refine ⟨{ __ := q, lie_mem := ?_ }, LieSubmodule.isCompl_toSubmodule.mp hq⟩
  intro x m _
  simp only [Submodule.mem_toAddSubmonoid, AddSubsemigroup.mem_carrier,
    AddSubmonoid.mem_toSubsemigroup] at *
  rw [htriv]
  exact q.zero_mem

end Aux

section MainInduction

variable (K L : Type*) [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L] [LieAlgebra.HasTrivialRadical K L]

/-- **The key case of Weyl's theorem.**  If `L` is semisimple, `M` is a finite-dimensional
`L`-module and `N` is a submodule containing `⁅L, M⁆`, then `N` has an `L`-module complement
(which is then necessarily a trivial `L`-module). -/
theorem exists_isCompl_of_lie_mem : ∀ (n : ℕ) {M : Type v} [AddCommGroup M] [Module K M]
    [LieRingModule L M] [LieModule K L M] [FiniteDimensional K M],
    finrank K M ≤ n → ∀ N : LieSubmodule K L M, (∀ (x : L) (m : M), ⁅x, m⁆ ∈ N) →
      ∃ X : LieSubmodule K L M, IsCompl N X := by
  intro n
  induction n with
  | zero =>
      intro M _ _ _ _ _ hn N _
      have hs : Subsingleton M := (Module.finrank_zero_iff (R := K)).mp (Nat.le_zero.mp hn)
      exact exists_isCompl_of_trivial K L (fun x m => by rw [Subsingleton.elim m 0, lie_zero]) N
  | succ n ih =>
      intro M _ _ _ _ _ hn N hN
      by_cases htriv : ∀ (x : L) (m : M), ⁅x, m⁆ = 0
      · exact exists_isCompl_of_trivial K L htriv N
      set c : Module.End K M := weylCasimir K L M with hcdef
      have hcl : ∀ (x : L) (m : M), c ⁅x, m⁆ = ⁅x, c m⁆ := weylCasimir_apply_lie K L M
      have hcpow : ∀ (k : ℕ) (x : L) (m : M), (c ^ k) ⁅x, m⁆ = ⁅x, (c ^ k) m⁆ := by
        intro k
        induction k with
        | zero => intro x m; simp
        | succ k ihk =>
            intro x m
            rw [pow_succ', Module.End.mul_apply, Module.End.mul_apply, ihk, hcl]
      obtain ⟨k0, hk0⟩ := Filter.eventually_atTop.mp
        (LinearMap.eventually_isCompl_ker_pow_range_pow c)
      have hfit : IsCompl (LinearMap.ker (c ^ (k0 + 1))) (LinearMap.range (c ^ (k0 + 1))) :=
        hk0 (k0 + 1) (Nat.le_succ k0)
      set M0 : LieSubmodule K L M := kerLie K L (c ^ (k0 + 1)) (hcpow (k0 + 1)) with hM0def
      set M1 : LieSubmodule K L M := rangeLie K L (c ^ (k0 + 1)) (hcpow (k0 + 1)) with hM1def
      have hfitL : IsCompl M0 M1 := LieSubmodule.isCompl_toSubmodule.mp hfit
      -- the positive Fitting component lies inside `N`
      have hM1N : M1 ≤ N := by
        intro m hm
        obtain ⟨v, rfl⟩ : ∃ v, (c ^ (k0 + 1)) v = m := hm
        rw [pow_succ', Module.End.mul_apply, hcdef]
        exact weylCasimir_mem K L M N hN _
      -- the Casimir element is not nilpotent, so the positive Fitting component is nonzero
      have hM1ne : M1 ≠ ⊥ := by
        intro hbot
        refine not_isNilpotent_weylCasimir K L M htriv ⟨k0 + 1, ?_⟩
        have : LinearMap.range (c ^ (k0 + 1)) = ⊥ := by
          rw [← rangeLie_toSubmodule K L (c ^ (k0 + 1)) (hcpow (k0 + 1)), ← hM1def, hbot,
            LieSubmodule.bot_toSubmodule]
        exact LinearMap.range_eq_bot.mp this
      -- hence `M0` is a proper submodule and we may apply the inductive hypothesis to it
      have hM0top : M0 ≠ ⊤ := by
        intro htop
        exact hM1ne (by simpa [htop] using hfitL.inf_eq_bot)
      have hlt : finrank K M0 < finrank K M := by
        have h1 : M0.toSubmodule < ⊤ := lt_of_le_of_ne le_top (by
          intro h
          exact hM0top (by rw [← LieSubmodule.toSubmodule_inj, h, LieSubmodule.top_toSubmodule]))
        have h2 : finrank K M0.toSubmodule < finrank K (⊤ : Submodule K M) :=
          Submodule.finrank_lt_finrank_of_lt h1
        rwa [finrank_top] at h2
      obtain ⟨X0, hX0⟩ := ih (M := M0) (by omega) (LieSubmodule.comap M0.incl N)
        (fun x m => LieSubmodule.mem_comap.mpr (hN x (m : M)))
      refine ⟨LieSubmodule.map M0.incl X0, ?_, ?_⟩
      · refine disjoint_iff.mpr (eq_bot_iff.mpr fun m hm => ?_)
        have hmN : m ∈ N := hm.1
        have hmX : m ∈ LieSubmodule.map M0.incl X0 := hm.2
        obtain ⟨y, hy, rfl⟩ := (LieSubmodule.mem_map _).mp hmX
        have hyb : y ∈ LieSubmodule.comap M0.incl N ⊓ X0 :=
          ⟨LieSubmodule.mem_comap.mpr hmN, hy⟩
        rw [hX0.inf_eq_bot, LieSubmodule.mem_bot] at hyb
        show M0.incl y ∈ (⊥ : LieSubmodule K L M)
        rw [hyb, LieSubmodule.mem_bot, map_zero]
      · rw [codisjoint_iff, eq_top_iff]
        intro m _
        have hmem : m ∈ M0 ⊔ M1 := by rw [hfitL.sup_eq_top]; exact LieSubmodule.mem_top m
        rw [← LieSubmodule.mem_toSubmodule, LieSubmodule.sup_toSubmodule,
          Submodule.mem_sup] at hmem
        obtain ⟨a, ha, b, hb, rfl⟩ := hmem
        have ha0 : (⟨a, ha⟩ : M0) ∈ LieSubmodule.comap M0.incl N ⊔ X0 := by
          rw [hX0.sup_eq_top]; exact LieSubmodule.mem_top _
        rw [← LieSubmodule.mem_toSubmodule, LieSubmodule.sup_toSubmodule,
          Submodule.mem_sup] at ha0
        obtain ⟨p, hp, q, hq, hpq⟩ := ha0
        have hA : (p : M) + (q : M) = a := congrArg Subtype.val hpq
        rw [← LieSubmodule.mem_toSubmodule, LieSubmodule.sup_toSubmodule, Submodule.mem_sup]
        refine ⟨(p : M) + b, N.add_mem hp (hM1N hb), (q : M), ?_, ?_⟩
        · exact (LieSubmodule.mem_map _).mpr ⟨q, hq, rfl⟩
        · rw [← hA]; abel

/-- **The key case of Weyl's theorem**, stated without the auxiliary induction parameter. -/
theorem exists_isCompl_of_lie_mem' {M : Type v} [AddCommGroup M] [Module K M]
    [LieRingModule L M] [LieModule K L M] [FiniteDimensional K M]
    (N : LieSubmodule K L M) (hN : ∀ (x : L) (m : M), ⁅x, m⁆ ∈ N) :
    ∃ X : LieSubmodule K L M, IsCompl N X :=
  exists_isCompl_of_lie_mem K L (finrank K M) le_rfl N hN

end MainInduction

section Whitehead

variable {K S M : Type*} [Field K] [CharZero K] [LieRing S] [LieAlgebra K S]
  [AddCommGroup M] [Module K M] [LieRingModule S M] [LieModule K S M]

/-- Given a `1`-cocycle `c : S → M`, the `S`-module structure on `M × K` given by
`x · (m, t) = (⁅x, m⁆ + t • c x, 0)`. -/
@[implicit_reducible]
def cocycleModule (c : S →ₗ[K] M) (hc : ∀ x y : S, c ⁅x, y⁆ = ⁅x, c y⁆ - ⁅y, c x⁆) :
    LieRingModule S (M × K) where
  bracket x p := (⁅x, p.1⁆ + p.2 • c x, 0)
  add_lie x y p := by
    simp only [Prod.mk_add_mk, Prod.mk.injEq, add_zero, and_true, map_add, add_lie, smul_add]
    abel
  lie_add x p q := by
    simp only [Prod.fst_add, Prod.snd_add, Prod.mk_add_mk, Prod.mk.injEq, add_zero, and_true,
      lie_add, add_smul]
    abel
  leibniz_lie x y p := by
    simp only [Prod.mk_add_mk, Prod.mk.injEq, add_zero, and_true, zero_smul, lie_add]
    rw [leibniz_lie, hc, lie_smul, lie_smul, smul_sub]
    abel

omit [CharZero K] in
theorem cocycleLieModule (c : S →ₗ[K] M) (hc : ∀ x y : S, c ⁅x, y⁆ = ⁅x, c y⁆ - ⁅y, c x⁆) :
    letI := cocycleModule c hc
    LieModule K S (M × K) :=
  letI := cocycleModule c hc
  { smul_lie := fun t x p => by
      change (⁅t • x, p.1⁆ + p.2 • c (t • x), 0) = t • (⁅x, p.1⁆ + p.2 • c x, (0 : K))
      simp only [smul_lie, map_smul, Prod.smul_mk, smul_zero, smul_add, smul_comm p.2 t]
    lie_smul := fun t x p => by
      change (⁅x, (t • p).1⁆ + (t • p).2 • c x, 0) = t • (⁅x, p.1⁆ + p.2 • c x, (0 : K))
      simp only [Prod.smul_fst, Prod.smul_snd, lie_smul, Prod.smul_mk, smul_zero,
        smul_add, smul_assoc] }

/-- **Whitehead's first lemma.**  For a semisimple Lie algebra `S` in characteristic zero acting
on a finite-dimensional module `M`, every `1`-cocycle is a coboundary. -/
theorem whitehead_h1 [FiniteDimensional K S] [LieAlgebra.HasTrivialRadical K S]
    [FiniteDimensional K M] (c : S →ₗ[K] M)
    (hc : ∀ x y : S, c ⁅x, y⁆ = ⁅x, c y⁆ - ⁅y, c x⁆) :
    ∃ m : M, ∀ x : S, c x = ⁅x, m⁆ := by
  letI : LieRingModule S (M × K) := cocycleModule c hc
  haveI : LieModule K S (M × K) := cocycleLieModule c hc
  have hbr : ∀ (x : S) (p : M × K), ⁅x, p⁆ = (⁅x, p.1⁆ + p.2 • c x, (0 : K)) := fun _ _ => rfl
  set N : LieSubmodule K S (M × K) :=
    { __ := LinearMap.ker (LinearMap.snd K M K)
      lie_mem := by
        intro x p _
        simp only [Submodule.mem_toAddSubmonoid, AddSubsemigroup.mem_carrier,
          AddSubmonoid.mem_toSubsemigroup, LinearMap.mem_ker, LinearMap.snd_apply, hbr] } with hNdef
  have hN : ∀ (x : S) (p : M × K), ⁅x, p⁆ ∈ N := by
    intro x p
    simp only [hNdef, LieSubmodule.mem_mk_iff', LinearMap.mem_ker, LinearMap.snd_apply, hbr]
  obtain ⟨X, hX⟩ := exists_isCompl_of_lie_mem' K S N hN
  have htop : ((0 : M), (1 : K)) ∈ N ⊔ X := by
    rw [hX.sup_eq_top]; exact LieSubmodule.mem_top _
  rw [← LieSubmodule.mem_toSubmodule, LieSubmodule.sup_toSubmodule, Submodule.mem_sup] at htop
  obtain ⟨a, ha, b, hb, hab⟩ := htop
  have ha2 : a.2 = 0 := ha
  have hb2 : b.2 = 1 := by
    have := congrArg Prod.snd hab
    simp only [Prod.snd_add] at this
    rw [ha2, zero_add] at this
    exact this
  refine ⟨-b.1, fun x => ?_⟩
  have hxb : ⁅x, b⁆ = 0 := by
    have h1 : ⁅x, b⁆ ∈ N := hN x b
    have h2 : ⁅x, b⁆ ∈ X := X.lie_mem hb
    have h3 : ⁅x, b⁆ ∈ N ⊓ X := ⟨h1, h2⟩
    rw [hX.inf_eq_bot, LieSubmodule.mem_bot] at h3
    exact h3
  rw [hbr, hb2, one_smul, Prod.mk_eq_zero] at hxb
  have h4 : c x = -⁅x, b.1⁆ := by
    rw [eq_neg_iff_add_eq_zero, add_comm]
    exact hxb.1
  rw [h4, lie_neg]

/-- The statement of Whitehead's first lemma over `K`, in the packaged form consumed by the
Levi decomposition. -/
def WhiteheadH1 (K : Type u) [Field K] : Prop :=
  ∀ (S : Type u) [LieRing S] [LieAlgebra K S] [FiniteDimensional K S]
    [LieAlgebra.HasTrivialRadical K S]
    (M : Type u) [AddCommGroup M] [Module K M] [LieRingModule S M] [LieModule K S M]
    [FiniteDimensional K M]
    (c : S →ₗ[K] M), (∀ x y : S, c ⁅x, y⁆ = ⁅x, c y⁆ - ⁅y, c x⁆) →
      ∃ m : M, ∀ x : S, c x = ⁅x, m⁆

/-- **Whitehead's first lemma** holds over every field of characteristic zero. -/
theorem whiteheadH1 (K : Type u) [Field K] [CharZero K] : WhiteheadH1 K :=
  fun _ _ _ _ _ _ _ _ _ _ _ c hc => whitehead_h1 c hc

end Whitehead

section Hom

variable (K L V N : Type*) [CommRing K] [LieRing L] [LieAlgebra K L]
  [AddCommGroup V] [Module K V] [LieRingModule L V] [LieModule K L V]
  [AddCommGroup N] [Module K N] [LieRingModule L N] [LieModule K L N]

/-- The `L`-module structure on `V →ₗ[K] N` given by `⁅x, f⁆ v = ⁅x, f v⁆ - f ⁅x, v⁆`. -/
@[implicit_reducible]
def homLieRingModule : LieRingModule L (V →ₗ[K] N) where
  bracket x f :=
    { toFun := fun v => ⁅x, f v⁆ - f ⁅x, v⁆
      map_add' := fun v w => by simp only [lie_add, map_add]; abel
      map_smul' := fun t v => by simp only [lie_smul, map_smul, RingHom.id_apply, smul_sub] }
  add_lie x y f := by
    ext v
    show ⁅x + y, f v⁆ - f ⁅x + y, v⁆ = (⁅x, f v⁆ - f ⁅x, v⁆) + (⁅y, f v⁆ - f ⁅y, v⁆)
    rw [add_lie, add_lie, map_add]
    abel
  lie_add x f g := by
    ext v
    show ⁅x, (f + g) v⁆ - (f + g) ⁅x, v⁆ = (⁅x, f v⁆ - f ⁅x, v⁆) + (⁅x, g v⁆ - g ⁅x, v⁆)
    rw [LinearMap.add_apply, LinearMap.add_apply, lie_add]
    abel
  leibniz_lie x y f := by
    ext v
    show ⁅x, ⁅y, f v⁆ - f ⁅y, v⁆⁆ - (⁅y, f ⁅x, v⁆⁆ - f ⁅y, ⁅x, v⁆⁆) =
      (⁅⁅x, y⁆, f v⁆ - f ⁅⁅x, y⁆, v⁆) + (⁅y, ⁅x, f v⁆ - f ⁅x, v⁆⁆ - (⁅x, f ⁅y, v⁆⁆ -
        f ⁅x, ⁅y, v⁆⁆))
    rw [lie_lie, lie_lie (x := x) (y := y) (m := v), map_sub, lie_sub, lie_sub]
    abel

attribute [local instance] homLieRingModule

/-- `V →ₗ[K] N` is a Lie module. -/
theorem homLieModule : LieModule K L (V →ₗ[K] N) where
  smul_lie t x f := by
    ext v
    show ⁅t • x, f v⁆ - f ⁅t • x, v⁆ = t • (⁅x, f v⁆ - f ⁅x, v⁆)
    rw [smul_lie, smul_lie, map_smul, smul_sub]
  lie_smul t x f := by
    ext v
    show ⁅x, (t • f) v⁆ - (t • f) ⁅x, v⁆ = t • (⁅x, f v⁆ - f ⁅x, v⁆)
    rw [LinearMap.smul_apply, LinearMap.smul_apply, lie_smul, smul_sub]

attribute [local instance] homLieModule

variable {K L V N}

@[simp] theorem hom_lie_apply (x : L) (f : V →ₗ[K] N) (v : V) :
    ⁅x, f⁆ v = ⁅x, f v⁆ - f ⁅x, v⁆ := rfl

end Hom

section Weyl

variable (K L V : Type*) [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [AddCommGroup V] [Module K V] [LieRingModule L V] [LieModule K L V]

attribute [local instance] homLieRingModule homLieModule

/-- The `L`-submodule of `V →ₗ[K] W` consisting of the maps vanishing on `W`. -/
def homVanishing (W : LieSubmodule K L V) : LieSubmodule K L (V →ₗ[K] W) where
  carrier := {f | ∀ w : W, f (w : V) = 0}
  add_mem' hf hg := fun w => by
    simp only [LinearMap.add_apply, hf w, hg w, add_zero]
  zero_mem' := fun _ => rfl
  smul_mem' t f hf := fun w => by simp only [LinearMap.smul_apply, hf w, smul_zero]
  lie_mem := by
    intro x f hf w
    show ⁅x, f (w : V)⁆ - f ⁅x, (w : V)⁆ = 0
    have hbr : (⁅x, (w : V)⁆ : V) = ((⁅x, w⁆ : W) : V) := rfl
    rw [hf w, lie_zero, hbr, hf ⁅x, w⁆, sub_zero]

variable {K L V}
variable [FiniteDimensional K L] [LieAlgebra.HasTrivialRadical K L] [FiniteDimensional K V]

/-- **Weyl's theorem on complete reducibility.**  Every submodule of a finite-dimensional module
over a semisimple Lie algebra in characteristic zero has a complement. -/
theorem exists_isCompl_of_hasTrivialRadical (W : LieSubmodule K L V) :
    ∃ W' : LieSubmodule K L V, IsCompl W W' := by
  obtain ⟨q, hq⟩ := Submodule.exists_isCompl W.toSubmodule
  set π : V →ₗ[K] W := W.toSubmodule.projectionOnto q hq with hπdef
  have hπW : ∀ w : W, π (w : V) = w := fun w =>
    Submodule.projectionOnto_apply_left hq w
  have hmem : ∀ x : L, ⁅x, π⁆ ∈ homVanishing K L V W := by
    intro x w
    show ⁅x, π (w : V)⁆ - π ⁅x, (w : V)⁆ = 0
    have hbr : (⁅x, (w : V)⁆ : V) = ((⁅x, w⁆ : W) : V) := rfl
    rw [hπW w, hbr, hπW ⁅x, w⁆, sub_self]
  -- the coboundary of the projection `π` is a cocycle with values in `homVanishing`
  set c : L →ₗ[K] homVanishing K L V W :=
    { toFun := fun x => ⟨⁅x, π⁆, hmem x⟩
      map_add' := fun x y => Subtype.ext (add_lie x y π)
      map_smul' := fun t x => Subtype.ext (smul_lie t x π) } with hcdef
  have hcocycle : ∀ x y : L, c ⁅x, y⁆ = ⁅x, c y⁆ - ⁅y, c x⁆ := fun x y =>
    Subtype.ext (lie_lie x y π)
  obtain ⟨f, hf⟩ := whitehead_h1 c hcocycle
  -- `g` is an `L`-module retraction of `V` onto `W`
  set g : V →ₗ[K] W := π - (f : V →ₗ[K] W) with hgdef
  have hgW : ∀ w : W, g (w : V) = w := by
    intro w
    rw [hgdef, LinearMap.sub_apply, hπW w, f.2 w, sub_zero]
  have hgeq : ∀ (x : L) (v : V), g ⁅x, v⁆ = ⁅x, g v⁆ := by
    intro x v
    have hcoe : ⁅x, π⁆ = ⁅x, (f : V →ₗ[K] W)⁆ := congrArg Subtype.val (hf x)
    have h0 : ⁅x, g⁆ = 0 := by rw [hgdef, lie_sub, hcoe, sub_self]
    have h1 := congrArg (fun F : V →ₗ[K] W => F v) h0
    simp only [hom_lie_apply, LinearMap.zero_apply, sub_eq_zero] at h1
    exact h1.symm
  refine ⟨{ carrier := {v : V | g v = 0}
            add_mem' := by intro a b ha hb; simp only [Set.mem_setOf_eq, map_add] at *;
                           rw [ha, hb, add_zero]
            zero_mem' := by simp
            smul_mem' := by intro t a ha; simp only [Set.mem_setOf_eq, map_smul] at *;
                            rw [ha, smul_zero]
            lie_mem := by
              intro x v hv
              show g ⁅x, v⁆ = 0
              rw [hgeq, show g v = 0 from hv, lie_zero] }, ?_, ?_⟩
  · refine disjoint_iff.mpr (eq_bot_iff.mpr fun v hv => ?_)
    have hvW : v ∈ W := hv.1
    have hv0 : g v = 0 := hv.2
    rw [LieSubmodule.mem_bot]
    have := hgW ⟨v, hvW⟩
    rw [hv0] at this
    exact congrArg Subtype.val this.symm
  · refine codisjoint_iff.mpr (eq_top_iff.mpr fun v _ => ?_)
    rw [← LieSubmodule.mem_toSubmodule, LieSubmodule.sup_toSubmodule, Submodule.mem_sup]
    refine ⟨(g v : V), (g v).2, v - (g v : V), ?_, by abel⟩
    show g (v - (g v : V)) = 0
    rw [map_sub, hgW (g v), sub_self]

end Weyl

end Submission.Ado
