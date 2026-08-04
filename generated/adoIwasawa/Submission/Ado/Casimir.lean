import ChallengeDeps

/-!
# The Casimir element of a representation with nondegenerate trace form

Let `K` be a field, `L` a finite-dimensional Lie algebra over `K` and `V` a
finite-dimensional `L`-module, with structure map `ρ = LieModule.toEnd K L V`.
The *trace form* of the representation is the symmetric bilinear form

```
β x y = trace (ρ x ∘ ρ y)
```

(this is `LieModule.traceForm K L V`).  If `β` is nondegenerate, and `(eᵢ)`,
`(fᵢ)` are bases of `L` dual to each other for `β`, then the **Casimir element**

```
c = ∑ i, ρ (eᵢ) ∘ ρ (fᵢ) : Module.End K V
```

is independent of the choice of dual bases, commutes with the image of `ρ`, and
has trace `dim L`.  We prove the last two properties here; independence of the
basis is not needed downstream and is not proved.

## Main definitions

* `Submission.Ado.casimirOfBasis` — the Casimir element attached to a basis `b`
  of `L` (the dual basis is `LinearMap.BilinForm.dualBasis`).
* `Submission.Ado.casimir` — the Casimir element for the canonical basis
  `Module.finBasis K L`.

## Main results

* `Submission.Ado.casimirOfBasis_comm` / `Submission.Ado.casimir_comm` —
  `⁅ρ x, c⁆ = 0` for every `x : L`.
* `Submission.Ado.trace_casimirOfBasis` / `Submission.Ado.trace_casimir` —
  `trace K V c = dim K L`.
-/

namespace Submission.Ado

open Module (finrank)
open LinearMap (trace)

section Casimir

variable {K L V ι : Type*} [Field K] [LieRing L] [LieAlgebra K L]
  [AddCommGroup V] [Module K V] [LieRingModule L V] [LieModule K L V]
  [Fintype ι] [DecidableEq ι]

variable (K L V) in
/-- The trace form of a Lie module is symmetric, as a `LinearMap.BilinForm.IsSymm`. -/
theorem traceForm_isSymm' : (LieModule.traceForm K L V).IsSymm :=
  ⟨LieModule.traceForm_comm K L V⟩

variable (K L V) in
/-- The structure map of a Lie module turns brackets into ring commutators. -/
theorem toEnd_lie_eq (y z : L) :
    LieModule.toEnd K L V ⁅y, z⁆ =
      LieModule.toEnd K L V y * LieModule.toEnd K L V z -
        LieModule.toEnd K L V z * LieModule.toEnd K L V y :=
  (LieModule.toEnd K L V).map_lie y z

/-- The Casimir element attached to a basis `b` of `L`: it is `∑ i, ρ (b i) ∘ ρ (b' i)`
where `b'` is the basis dual to `b` for the trace form. -/
noncomputable def casimirOfBasis (hβ : (LieModule.traceForm K L V).Nondegenerate)
    (b : Module.Basis ι K L) : Module.End K V :=
  ∑ i, LieModule.toEnd K L V (b i) *
    LieModule.toEnd K L V ((LieModule.traceForm K L V).dualBasis hβ b i)

/-- The coordinates of `y : L` in the basis `b` are the trace-form pairings with the
dual basis. -/
theorem repr_eq_traceForm_dualBasis (hβ : (LieModule.traceForm K L V).Nondegenerate)
    (b : Module.Basis ι K L) (y : L) (i : ι) :
    b.repr y i = LieModule.traceForm K L V y ((LieModule.traceForm K L V).dualBasis hβ b i) := by
  conv_lhs =>
    rw [← LinearMap.BilinForm.dualBasis_dualBasis hβ (traceForm_isSymm' K L V) b]
  exact LinearMap.BilinForm.dualBasis_repr_apply hβ _ y i

/-- The Casimir element commutes with the image of the representation. -/
theorem casimirOfBasis_mul_comm (hβ : (LieModule.traceForm K L V).Nondegenerate)
    (b : Module.Basis ι K L) (x : L) :
    LieModule.toEnd K L V x * casimirOfBasis hβ b =
      casimirOfBasis hβ b * LieModule.toEnd K L V x := by
  set ρ := LieModule.toEnd K L V with hρ
  set b' := (LieModule.traceForm K L V).dualBasis hβ b with hb'
  -- expansion of `⁅x, b i⁆` in the basis `b`
  have hb : ∀ i, ⁅x, b i⁆ =
      ∑ j, (LieModule.traceForm K L V ⁅x, b i⁆ (b' j)) • b j := by
    intro i
    conv_lhs => rw [← b.sum_repr ⁅x, b i⁆]
    exact Finset.sum_congr rfl fun j _ => by
      rw [repr_eq_traceForm_dualBasis hβ b]
  -- expansion of `⁅x, b' i⁆` in the basis `b'`; note the transposed, negated coefficients
  have hbd : ∀ i, ⁅x, b' i⁆ =
      ∑ j, (-(LieModule.traceForm K L V ⁅x, b j⁆ (b' i))) • b' j := by
    intro i
    conv_lhs => rw [← b'.sum_repr ⁅x, b' i⁆]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    have h1 : b'.repr ⁅x, b' i⁆ j = LieModule.traceForm K L V ⁅x, b' i⁆ (b j) := by
      rw [hb']; exact LinearMap.BilinForm.dualBasis_repr_apply hβ b _ j
    rw [h1, LieModule.traceForm_apply_lie_apply' K L V,
      LieModule.traceForm_comm K L V (b' i) ⁅x, b j⁆]
  have hc : casimirOfBasis hβ b = ∑ i, ρ (b i) * ρ (b' i) := rfl
  rw [← sub_eq_zero, hc, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  have hstep : ∀ i : ι, ρ x * (ρ (b i) * ρ (b' i)) - ρ (b i) * ρ (b' i) * ρ x =
      ρ ⁅x, b i⁆ * ρ (b' i) + ρ (b i) * ρ ⁅x, b' i⁆ := by
    intro i
    rw [hρ, toEnd_lie_eq K L V, toEnd_lie_eq K L V]
    noncomm_ring
  rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hstep i, Finset.sum_add_distrib]
  have h1 : (∑ i, ρ ⁅x, b i⁆ * ρ (b' i)) =
      ∑ i, ∑ j, (LieModule.traceForm K L V ⁅x, b i⁆ (b' j)) • (ρ (b j) * ρ (b' i)) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    conv_lhs => rw [hb i]
    rw [map_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by rw [map_smul, smul_mul_assoc]
  have h2 : (∑ i, ρ (b i) * ρ ⁅x, b' i⁆) =
      ∑ i, ∑ j, (-(LieModule.traceForm K L V ⁅x, b j⁆ (b' i))) • (ρ (b i) * ρ (b' j)) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hbd i, map_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [map_smul, mul_smul_comm]
  have h3 : (∑ i, ∑ j, (-(LieModule.traceForm K L V ⁅x, b j⁆ (b' i))) • (ρ (b i) * ρ (b' j))) =
      -∑ i, ∑ j, (LieModule.traceForm K L V ⁅x, b i⁆ (b' j)) • (ρ (b j) * ρ (b' i)) := by
    rw [Finset.sum_comm]
    simp [neg_smul]
  rw [h1, h2, h3, add_neg_cancel]

/-- The Casimir element is a morphism of `L`-modules: it brackets to zero against the
image of the representation. -/
theorem casimirOfBasis_comm (hβ : (LieModule.traceForm K L V).Nondegenerate)
    (b : Module.Basis ι K L) (x : L) :
    ⁅LieModule.toEnd K L V x, casimirOfBasis hβ b⁆ = 0 := by
  show LieModule.toEnd K L V x * casimirOfBasis hβ b -
    casimirOfBasis hβ b * LieModule.toEnd K L V x = 0
  rw [sub_eq_zero]
  exact casimirOfBasis_mul_comm hβ b x

/-- The Casimir element commutes with the action of `L` on `V`. -/
theorem casimirOfBasis_apply_lie (hβ : (LieModule.traceForm K L V).Nondegenerate)
    (b : Module.Basis ι K L) (x : L) (v : V) :
    casimirOfBasis hβ b ⁅x, v⁆ = ⁅x, casimirOfBasis hβ b v⁆ := by
  have := casimirOfBasis_mul_comm hβ b x
  have h := congrArg (fun f : Module.End K V => f v) this
  simpa [Module.End.mul_apply] using h.symm

/-- The value of the Casimir element on a vector, written with Lie brackets. -/
theorem casimirOfBasis_apply (hβ : (LieModule.traceForm K L V).Nondegenerate)
    (b : Module.Basis ι K L) (v : V) :
    casimirOfBasis hβ b v =
      ∑ i, ⁅b i, ⁅((LieModule.traceForm K L V).dualBasis hβ b i : L), v⁆⁆ := by
  simp [casimirOfBasis, LinearMap.sum_apply, Module.End.mul_apply,
    LieModule.toEnd_apply_apply]

/-- Anything commuting with the image of the representation commutes with the Casimir element. -/
theorem commute_casimirOfBasis (hβ : (LieModule.traceForm K L V).Nondegenerate)
    (b : Module.Basis ι K L) (f : Module.End K V)
    (hf : ∀ x : L, Commute f (LieModule.toEnd K L V x)) :
    Commute f (casimirOfBasis hβ b) :=
  Commute.sum_right _ _ _ fun _ _ => (hf _).mul_right (hf _)

/-- The trace of the Casimir element is the dimension of `L`. -/
theorem trace_casimirOfBasis [FiniteDimensional K V]
    (hβ : (LieModule.traceForm K L V).Nondegenerate) (b : Module.Basis ι K L) :
    trace K V (casimirOfBasis hβ b) = (finrank K L : K) := by
  rw [casimirOfBasis, map_sum]
  have : ∀ i : ι, trace K V (LieModule.toEnd K L V (b i) *
      LieModule.toEnd K L V ((LieModule.traceForm K L V).dualBasis hβ b i)) = 1 := by
    intro i
    rw [Module.End.mul_eq_comp, ← LieModule.traceForm_apply_apply K L V,
      LinearMap.BilinForm.apply_dualBasis_right hβ (traceForm_isSymm' K L V) b i i, if_pos rfl]
  rw [Finset.sum_congr rfl fun i _ => this i]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
    Module.finrank_eq_card_basis b]

end Casimir

section CanonicalCasimir

variable (K L V : Type*) [Field K] [LieRing L] [LieAlgebra K L]
  [AddCommGroup V] [Module K V] [LieRingModule L V] [LieModule K L V]
  [FiniteDimensional K L]

/-- The Casimir element of a representation whose trace form is nondegenerate. -/
noncomputable def casimir (hβ : (LieModule.traceForm K L V).Nondegenerate) :
    Module.End K V :=
  casimirOfBasis hβ (Module.finBasis K L)

variable {K L V}

theorem casimir_comm (hβ : (LieModule.traceForm K L V).Nondegenerate) (x : L) :
    ⁅LieModule.toEnd K L V x, casimir K L V hβ⁆ = 0 :=
  casimirOfBasis_comm hβ _ x

theorem casimir_mul_comm (hβ : (LieModule.traceForm K L V).Nondegenerate) (x : L) :
    LieModule.toEnd K L V x * casimir K L V hβ =
      casimir K L V hβ * LieModule.toEnd K L V x :=
  casimirOfBasis_mul_comm hβ _ x

theorem casimir_apply_lie (hβ : (LieModule.traceForm K L V).Nondegenerate) (x : L) (v : V) :
    casimir K L V hβ ⁅x, v⁆ = ⁅x, casimir K L V hβ v⁆ :=
  casimirOfBasis_apply_lie hβ _ x v

theorem trace_casimir [FiniteDimensional K V]
    (hβ : (LieModule.traceForm K L V).Nondegenerate) :
    trace K V (casimir K L V hβ) = (finrank K L : K) :=
  trace_casimirOfBasis hβ _

end CanonicalCasimir

section OfRepresentation

/-!
The results above are phrased for a Lie module `V`, whose structure map is
`LieModule.toEnd K L V : L →ₗ⁅K⁆ Module.End K V`.  This section restates them for an
arbitrary representation `ρ : L →ₗ⁅K⁆ Module.End K V`, which is the same data.
-/

variable {K L V : Type*} [Field K] [LieRing L] [LieAlgebra K L]
  [AddCommGroup V] [Module K V]

/-- The `L`-module structure on `V` determined by a representation `ρ`. -/
@[implicit_reducible]
def repModule (ρ : L →ₗ⁅K⁆ Module.End K V) : LieRingModule L V :=
  LieRingModule.compLieHom V ρ

theorem repLieModule (ρ : L →ₗ⁅K⁆ Module.End K V) :
    letI := repModule ρ
    LieModule K L V :=
  LieModule.compLieHom V ρ

@[simp] theorem repModule_lie (ρ : L →ₗ⁅K⁆ Module.End K V) (x : L) (v : V) :
    letI := repModule ρ
    ⁅x, v⁆ = ρ x v := rfl

theorem toEnd_repModule (ρ : L →ₗ⁅K⁆ Module.End K V) :
    letI := repModule ρ
    haveI := repLieModule ρ
    LieModule.toEnd K L V = ρ := rfl

/-- The trace form of a representation is `β x y = trace (ρ x ∘ ρ y)`. -/
theorem traceForm_repModule (ρ : L →ₗ⁅K⁆ Module.End K V) (x y : L) :
    letI := repModule ρ
    haveI := repLieModule ρ
    LieModule.traceForm K L V x y = trace K V (ρ x * ρ y) := rfl

/-- **The Casimir element of a representation.**  If the trace form
`β x y = trace (ρ x ∘ ρ y)` of a representation `ρ : L →ₗ⁅K⁆ Module.End K V` is nondegenerate,
the associated Casimir element `c` satisfies `⁅ρ x, c⁆ = 0` for every `x : L`, and its trace
is `dim K L`. -/
theorem casimir_of_rep [FiniteDimensional K L] [FiniteDimensional K V]
    (ρ : L →ₗ⁅K⁆ Module.End K V) :
    letI := repModule ρ
    haveI := repLieModule ρ
    ∀ hβ : (LieModule.traceForm K L V).Nondegenerate,
      (∀ x : L, ⁅ρ x, casimir K L V hβ⁆ = 0) ∧
        trace K V (casimir K L V hβ) = (finrank K L : K) := by
  letI := repModule ρ
  haveI := repLieModule ρ
  exact fun hβ => ⟨fun x => casimir_comm hβ x, trace_casimir hβ⟩

end OfRepresentation

end Submission.Ado
