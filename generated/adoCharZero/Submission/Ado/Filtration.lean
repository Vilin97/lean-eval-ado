import Submission.Ado.Embed

/-!
# The degree filtration on a universal enveloping algebra

Birkhoff's embedding theorem (§3 of the informal proof) needs two facts about
`U(L)`:

1. `U(L) ⧸ J(L)^k` is finite-dimensional, where `J(L)` is the augmentation
   ideal;
2. `L ∩ J(L)^k = ⊥` for `k ≥ 2`.

Only the second needs the Poincaré–Birkhoff–Witt basis theorem. The first needs
just the *spanning* half, and that is what this file establishes, without PBW.

The tool is the `K`-submodule `gen K L` spanned by `ι '' L`. Its powers
`gen ^ j` are the spans of `j`-fold products of generators, and the two facts
proved here are

* `Submission.Ado.iSup_gen_pow_eq_top` — `⨆ j, gen ^ j = ⊤`, i.e. `ι '' L`
  generates `U(L)` as an algebra;
* `Submission.Ado.finiteDimensional_genPow` — each `gen ^ j` is
  finite-dimensional when `L` is,

from which finite-dimensionality of `U(L) ⧸ J(L)^k` follows by writing
`⊤ = (⨆ j ≤ k, gen ^ j) ⊔ J(L)^(k+1)`.

`Mathlib` makes `LieRing.ofAssociativeRing` a *local* instance only, so it is
re-enabled here for the duration of the file in order to use
`UniversalEnvelopingAlgebra.lift`.
-/

universe u

namespace Submission.Ado

open UniversalEnvelopingAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

variable (K L : Type u) [Field K] [LieRing L] [LieAlgebra K L]

/-- The `K`-span of the image of `L` in its universal enveloping algebra. -/
def gen : Submodule K (UniversalEnvelopingAlgebra K L) :=
  Submodule.span K (Set.range (ι K : L → UniversalEnvelopingAlgebra K L))

theorem ι_mem_gen (x : L) : (ι K x : UniversalEnvelopingAlgebra K L) ∈ gen K L :=
  Submodule.subset_span ⟨x, rfl⟩

/-- `ι '' L` generates `U(L)` as a `K`-algebra. Proved by the standard
retraction argument: the inclusion of the generated subalgebra splits the
universal property. -/
theorem adjoin_range_ι_eq_top :
    Algebra.adjoin K (Set.range (ι K : L → UniversalEnvelopingAlgebra K L)) = ⊤ := by
  set S := Algebra.adjoin K (Set.range (ι K : L → UniversalEnvelopingAlgebra K L))
  have hmem : ∀ x : L, (ι K x : UniversalEnvelopingAlgebra K L) ∈ S := fun x =>
    Algebra.subset_adjoin ⟨x, rfl⟩
  let f₀ : L →ₗ⁅K⁆ S :=
    { toFun := fun x => ⟨ι K x, hmem x⟩
      map_add' := fun x y => by ext; simp
      map_smul' := fun t x => by ext; simp
      map_lie' := fun {x y} => by
        ext
        simp [LieRing.of_associative_ring_bracket] }
  have hid : (S.val).comp (lift K f₀) = AlgHom.id K (UniversalEnvelopingAlgebra K L) := by
    apply hom_ext
    ext x
    simp [f₀]
  refine top_unique fun u _ => ?_
  have : u = S.val (lift K f₀ u) := by
    conv_lhs => rw [← AlgHom.id_apply (R := K) u, ← hid]
    rfl
  rw [this]
  exact (lift K f₀ u).2

/-- Every element of `U(L)` lies in some `gen ^ j`: it is a sum of products of
generators. -/
theorem exists_mem_gen_pow (u : UniversalEnvelopingAlgebra K L) :
    u ∈ ⨆ j : ℕ, gen K L ^ j := by
  have hmono : ∀ v ∈ Submonoid.closure
      (Set.range (ι K : L → UniversalEnvelopingAlgebra K L)), ∃ j, v ∈ gen K L ^ j := by
    intro v hv
    induction hv using Submonoid.closure_induction with
    | one => exact ⟨0, by simpa using Submodule.mem_one.mpr ⟨1, by simp⟩⟩
    | mem x hx => exact ⟨1, by rw [pow_one]; exact Submodule.subset_span hx⟩
    | mul x y _ _ ihx ihy =>
        obtain ⟨i, hi⟩ := ihx
        obtain ⟨j, hj⟩ := ihy
        exact ⟨i + j, by rw [pow_add]; exact Submodule.mul_mem_mul hi hj⟩
  have htop : (⊤ : Submodule K (UniversalEnvelopingAlgebra K L))
      ≤ ⨆ j : ℕ, gen K L ^ j := by
    rw [← Algebra.top_toSubmodule, ← adjoin_range_ι_eq_top K L, Algebra.adjoin_eq_span,
      Submodule.span_le]
    intro v hv
    obtain ⟨j, hj⟩ := hmono v hv
    exact (le_iSup (fun j : ℕ => gen K L ^ j) j) hj
  exact htop trivial

/-- `⨆ j, gen ^ j = ⊤`. -/
theorem iSup_gen_pow_eq_top : (⨆ j : ℕ, gen K L ^ j) = ⊤ :=
  top_unique fun u _ => exists_mem_gen_pow K L u

/-- `gen` is the range of `ι` regarded as a `K`-linear map. -/
theorem gen_eq_range :
    gen K L
      = LinearMap.range ((ι K : L →ₗ⁅K⁆ UniversalEnvelopingAlgebra K L) : L →ₗ[K] _) := by
  refine le_antisymm ?_ ?_
  · rw [gen, Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    exact ⟨x, rfl⟩
  · rintro _ ⟨x, rfl⟩
    exact ι_mem_gen K L x

variable [FiniteDimensional K L]

/-- `gen` is finitely generated, since `L` is finite-dimensional. -/
theorem gen_fg : (gen K L).FG := by
  rw [gen_eq_range, LinearMap.range_eq_map]
  exact (IsNoetherian.noetherian (⊤ : Submodule K L)).map _

/-- Every power of `gen` is finitely generated, hence finite-dimensional: the
`j`-fold products of generators span a finite-dimensional space. -/
theorem genPow_fg (j : ℕ) : (gen K L ^ j).FG :=
  (gen_fg K L).pow j

instance finiteDimensional_genPow (j : ℕ) : FiniteDimensional K ↥(gen K L ^ j) :=
  Module.Finite.iff_fg.mpr (genPow_fg K L j)

end Submission.Ado
