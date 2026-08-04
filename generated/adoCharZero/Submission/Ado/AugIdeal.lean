import Submission.Ado.Truncation

/-!
# The augmentation filtration is multiplicative

`augPow k` — the span of products of at least `k` generators of `U(L)` — is a
two-sided ideal, and the filtration it defines is multiplicative:

```
augPow k * augPow l ≤ augPow (k + l)
```

These are the submodule-level facts underlying Lemma 4.4 of the informal proof,
where a derivation `D` of `L` with `D L ⊆ N` is shown to satisfy
`D̃ (augPow k) ⊆ augPow k`: the Leibniz rule replaces one factor of a `k`-fold
product by something again in the ideal, and multiplicativity keeps the result
in degree `≥ k`.

Everything here is formal consequence of `gen ^ i * gen ^ j = gen ^ (i + j)`
together with `⨆ j, gen ^ j = ⊤` from `Filtration.lean`; no PBW input is used.
-/

universe u

namespace Submission.Ado

open UniversalEnvelopingAlgebra

variable (K L : Type u) [Field K] [LieRing L] [LieAlgebra K L]

theorem augPow_def (k : ℕ) : augPow K L k = ⨆ j : ℕ, gen K L ^ (j + k) := rfl

theorem genPow_mul_augPow_le (j k : ℕ) :
    gen K L ^ j * augPow K L k ≤ augPow K L k := by
  rw [augPow_def, Submodule.mul_iSup]
  refine iSup_le fun i => ?_
  rw [← pow_add]
  exact genPow_le_augPow K L (by omega)

theorem augPow_mul_genPow_le (j k : ℕ) :
    augPow K L k * gen K L ^ j ≤ augPow K L k := by
  rw [augPow_def, Submodule.iSup_mul]
  refine iSup_le fun i => ?_
  rw [← pow_add]
  exact genPow_le_augPow K L (by omega)

/-- `augPow k` is a left ideal. -/
theorem top_mul_augPow_le (k : ℕ) :
    (⊤ : Submodule K (UniversalEnvelopingAlgebra K L)) * augPow K L k ≤ augPow K L k := by
  conv_lhs => rw [← iSup_gen_pow_eq_top K L]
  rw [Submodule.iSup_mul]
  exact iSup_le fun j => genPow_mul_augPow_le K L j k

/-- `augPow k` is a right ideal. -/
theorem augPow_mul_top_le (k : ℕ) :
    augPow K L k * (⊤ : Submodule K (UniversalEnvelopingAlgebra K L)) ≤ augPow K L k := by
  conv_lhs => rw [← iSup_gen_pow_eq_top K L]
  rw [Submodule.mul_iSup]
  exact iSup_le fun j => augPow_mul_genPow_le K L j k

/-- The augmentation filtration is multiplicative. -/
theorem augPow_mul_augPow_le (k l : ℕ) :
    augPow K L k * augPow K L l ≤ augPow K L (k + l) := by
  rw [augPow_def K L k, Submodule.iSup_mul]
  refine iSup_le fun i => ?_
  rw [augPow_def K L l, Submodule.mul_iSup]
  refine iSup_le fun j => ?_
  rw [← pow_add]
  exact genPow_le_augPow K L (by omega)

/-- The filtration is decreasing. -/
theorem augPow_antitone {k l : ℕ} (h : k ≤ l) : augPow K L l ≤ augPow K L k := by
  rw [augPow_def K L l]
  refine iSup_le fun j => ?_
  exact genPow_le_augPow K L (by omega)

@[simp]
theorem augPow_zero : augPow K L 0 = ⊤ := by
  rw [augPow_def]
  simpa using iSup_gen_pow_eq_top K L

@[simp]
theorem filt_zero : filt K L 0 = ⊥ := by
  rw [filt]
  simp

theorem filt_mono {k l : ℕ} (h : k ≤ l) : filt K L k ≤ filt K L l := by
  rw [filt]
  exact iSup_le fun j => genPow_le_filt K L (lt_of_lt_of_le j.isLt h)

/-- Degree `< k` and degree `≥ k` meet only in `⊥` exactly when `L` injects
into the truncation; recorded here as the statement that the two pieces do
cover `U(L)`, which is all that finite-dimensionality needs. -/
theorem mem_sup_filt_augPow (k : ℕ) (u : UniversalEnvelopingAlgebra K L) :
    u ∈ filt K L k ⊔ augPow K L k := by
  rw [sup_filt_augPow K L k]
  trivial

end Submission.Ado
