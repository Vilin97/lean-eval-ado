import Submission.Ado.PBW.Props

/-!
# Unitriangular families in the polynomial module

A family `f : ι → Poly K n` is *unitriangular* over an indexing map
`φ : ι → Mon n` when

```
f s = z^(φ s) + (terms of degree < |φ s|)
```

Such a family is linearly independent as soon as `φ` is injective, and spans as
soon as `φ` is surjective; so a unitriangular family over a bijection is a basis.

This is the abstract half of the Poincaré–Birkhoff–Witt basis theorem: the
concrete half is the computation that the evaluation map sends the ordered
monomial `ι(x_{i₁}) ⋯ ι(x_{i_k})` to `z^{i₁} ⋯ z^{i_k}` plus lower-degree terms.
-/

universe u v

namespace Submission.Ado.PBW

variable {K : Type u} [Field K] {n : ℕ}

/-- `f` is supported in degrees `< d`. -/
def DegLT (f : Poly K n) (d : ℕ) : Prop := ∀ c ∈ f.support, c.degree < d

theorem DegLT_zero_iff {f : Poly K n} : DegLT f 0 ↔ f = 0 := by
  constructor
  · intro h
    refine Finsupp.ext fun c => ?_
    by_contra hc
    exact absurd (h c (Finsupp.mem_support_iff.mpr hc)) (Nat.not_lt_zero _)
  · rintro rfl c hc
    simp at hc

theorem DegLT.degLE {f : Poly K n} {d : ℕ} (h : DegLT f (d + 1)) : DegLE f d :=
  fun c hc => Nat.lt_succ_iff.mp (h c hc)

/-- A polynomial of degree `< d` vanishes at every exponent vector of degree `≥ d`. -/
theorem DegLT.apply_eq_zero {f : Poly K n} {d : ℕ} (h : DegLT f d) {c : Mon n}
    (hc : d ≤ c.degree) : f c = 0 := by
  by_contra hne
  exact absurd (h c (Finsupp.mem_support_iff.mpr hne)) (not_lt.mpr hc)

/-- A polynomial is the sum of its monomials. -/
theorem sum_smul_mono (g : Poly K n) : ∑ c ∈ g.support, g c • (mono c : Poly K n) = g := by
  conv_rhs => rw [← Finsupp.sum_single g]
  rw [Finsupp.sum]
  exact Finset.sum_congr rfl fun c _ => by
    rw [mono, Finsupp.smul_single, smul_eq_mul, mul_one]

/-- Every polynomial lies in the span of the monomials in its support. -/
theorem mem_span_of_support {S : Submodule K (Poly K n)} {g : Poly K n}
    (h : ∀ c ∈ g.support, (mono c : Poly K n) ∈ S) : g ∈ S := by
  rw [← sum_smul_mono g]
  exact Submodule.sum_mem _ fun c hc => Submodule.smul_mem _ _ (h c hc)

/-- The defining property of a unitriangular family. -/
def Unitriangular {ι : Type v} (φ : ι → Mon n) (f : ι → Poly K n) : Prop :=
  ∀ s, DegLT (f s - mono (φ s)) (φ s).degree

/-- A unitriangular member evaluates to `1` at its own leading exponent. -/
theorem Unitriangular.apply_self {ι : Type v} {φ : ι → Mon n} {f : ι → Poly K n}
    (h : Unitriangular φ f) (s : ι) : f s (φ s) = 1 := by
  have h0 := (h s).apply_eq_zero (le_refl (φ s).degree)
  rw [Finsupp.sub_apply] at h0
  have hm : (mono (φ s) : Poly K n) (φ s) = 1 := by simp [mono]
  rw [hm, sub_eq_zero] at h0
  exact h0

/-- A unitriangular member vanishes at any exponent vector of degree at least its
own, other than its own leading exponent. -/
theorem Unitriangular.apply_of_ne {ι : Type v} {φ : ι → Mon n} {f : ι → Poly K n}
    (h : Unitriangular φ f) (s : ι) {c : Mon n} (hdeg : (φ s).degree ≤ c.degree)
    (hne : c ≠ φ s) : f s c = 0 := by
  have := (h s).apply_eq_zero hdeg
  rw [Finsupp.sub_apply] at this
  have hm : (mono (φ s) : Poly K n) c = 0 := by
    simp [mono, Ne.symm hne]
  rw [hm, sub_zero] at this
  exact this

/-- A unitriangular family over an injective index map is linearly independent. -/
theorem Unitriangular.linearIndependent {ι : Type v} {φ : ι → Mon n} {f : ι → Poly K n}
    (h : Unitriangular φ f) (hφ : Function.Injective φ) : LinearIndependent K f := by
  classical
  rw [linearIndependent_iff]
  intro l hl
  by_contra hne
  obtain ⟨s, hs⟩ : l.support.Nonempty := Finsupp.support_nonempty_iff.mpr hne
  -- pick an index of maximal leading degree
  obtain ⟨s₀, hs₀mem, hs₀max⟩ :=
    l.support.exists_max_image (fun t => (φ t).degree) ⟨s, hs⟩
  have hzero : (Finsupp.linearCombination K f l) (φ s₀) = 0 := by rw [hl]; rfl
  rw [Finsupp.linearCombination_apply, Finsupp.sum, Finsupp.coe_finsetSum,
    Finset.sum_apply] at hzero
  have hterm : ∀ t ∈ l.support, (l t • f t) (φ s₀) = if t = s₀ then l s₀ else 0 := by
    intro t ht
    rw [Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]
    by_cases htt : t = s₀
    · subst htt; rw [if_pos rfl, h.apply_self t, mul_one]
    · rw [if_neg htt, h.apply_of_ne t (hs₀max t ht) (fun hc => htt (hφ hc.symm)), mul_zero]
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' l.support s₀, if_pos hs₀mem] at hzero
  exact (Finsupp.mem_support_iff.mp hs₀mem) hzero

/-- A unitriangular family over a surjective index map spans. -/
theorem Unitriangular.span_eq_top {ι : Type v} {φ : ι → Mon n} {f : ι → Poly K n}
    (h : Unitriangular φ f) (hφ : Function.Surjective φ) :
    Submodule.span K (Set.range f) = ⊤ := by
  classical
  set S : Submodule K (Poly K n) := Submodule.span K (Set.range f) with hS
  -- every monomial lies in `S`, by strong induction on its degree
  have hmono : ∀ d : ℕ, ∀ a : Mon n, a.degree ≤ d → (mono a : Poly K n) ∈ S := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
        intro a ha
        obtain ⟨s, rfl⟩ := hφ a
        have hfs : f s ∈ S := Submodule.subset_span ⟨s, rfl⟩
        have hcorr : (f s - mono (φ s)) ∈ S := by
          refine mem_span_of_support fun c hc => ?_
          have hlt : c.degree < (φ s).degree := h s c hc
          exact ih (d - 1) (by omega) c (by omega)
        have : (mono (φ s) : Poly K n) = f s - (f s - mono (φ s)) := by abel
        rw [this]
        exact Submodule.sub_mem _ hfs hcorr
  -- monomials span the whole polynomial module
  refine top_unique fun g _ => ?_
  exact mem_span_of_support fun c _ => hmono c.degree c le_rfl

end Submission.Ado.PBW
