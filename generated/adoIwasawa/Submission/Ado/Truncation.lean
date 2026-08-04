import Submission.Ado.Filtration

/-!
# Finite-dimensionality of the truncated enveloping algebra

Birkhoff's embedding theorem represents a nilpotent Lie algebra `N` on
`U(N) ⧸ J(N)^k`. Two things must be checked about that space: that it is
finite-dimensional, and that `N` injects into it. This file settles the first,
which — as `Filtration.lean` already showed — needs only the spanning half of
Poincaré–Birkhoff–Witt, not the basis theorem.

Write `gen` for the `K`-span of `ι '' L` in `U(L)`. Then

* `filt k = ⨆ j < k, gen ^ j` is the span of products of fewer than `k`
  generators, and is finite-dimensional;
* `augPow k = ⨆ j, gen ^ (j + k)` is the span of products of at least `k`
  generators — the `k`-th power of the augmentation ideal;
* `filt k ⊔ augPow k = ⊤`, because every `gen ^ j` lands in one side or the
  other according to whether `j < k`.

Hence `U(L) ⧸ augPow k` is a quotient of the finite-dimensional `filt k`.
-/

universe u

namespace Submission.Ado

open UniversalEnvelopingAlgebra

variable (K L : Type u) [Field K] [LieRing L] [LieAlgebra K L]

/-- Products of fewer than `k` generators. -/
def filt (k : ℕ) : Submodule K (UniversalEnvelopingAlgebra K L) :=
  ⨆ j : Fin k, gen K L ^ (j : ℕ)

/-- Products of at least `k` generators: the `k`-th power of the augmentation
ideal, as a `K`-submodule. -/
def augPow (k : ℕ) : Submodule K (UniversalEnvelopingAlgebra K L) :=
  ⨆ j : ℕ, gen K L ^ (j + k)

theorem genPow_le_filt {j k : ℕ} (h : j < k) : gen K L ^ j ≤ filt K L k :=
  le_iSup (fun i : Fin k => gen K L ^ (i : ℕ)) ⟨j, h⟩

theorem genPow_le_augPow {j k : ℕ} (h : k ≤ j) : gen K L ^ j ≤ augPow K L k := by
  have hj : j = (j - k) + k := (Nat.sub_add_cancel h).symm
  rw [hj]
  exact le_iSup (fun i : ℕ => gen K L ^ (i + k)) (j - k)

/-- Every element of `U(L)` splits as a low-degree part plus a part of degree at
least `k`. -/
theorem sup_filt_augPow (k : ℕ) : filt K L k ⊔ augPow K L k = ⊤ := by
  rw [eq_top_iff, ← iSup_gen_pow_eq_top K L]
  refine iSup_le fun j => ?_
  by_cases h : j < k
  · exact le_sup_of_le_left (genPow_le_filt K L h)
  · exact le_sup_of_le_right (genPow_le_augPow K L (Nat.le_of_not_lt h))

variable [FiniteDimensional K L]

theorem filt_fg (k : ℕ) : (filt K L k).FG :=
  Submodule.fg_iSup _ fun j => genPow_fg K L (j : ℕ)

instance finiteDimensional_filt (k : ℕ) : FiniteDimensional K ↥(filt K L k) :=
  Module.Finite.iff_fg.mpr (filt_fg K L k)

/-- **The truncated enveloping algebra is finite-dimensional.** -/
instance finiteDimensional_quotient_augPow (k : ℕ) :
    FiniteDimensional K (UniversalEnvelopingAlgebra K L ⧸ augPow K L k) := by
  have hsurj : Function.Surjective
      (((augPow K L k).mkQ).comp ((filt K L k).subtype)) := by
    intro y
    obtain ⟨u, rfl⟩ := (augPow K L k).mkQ_surjective y
    have hu : u ∈ filt K L k ⊔ augPow K L k := by
      rw [sup_filt_augPow K L k]; trivial
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hu
    refine ⟨⟨a, ha⟩, ?_⟩
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, Submodule.mkQ_apply]
    rw [Submodule.Quotient.eq]
    simpa using (augPow K L k).neg_mem hb
  exact Module.Finite.of_surjective _ hsurj

end Submission.Ado
