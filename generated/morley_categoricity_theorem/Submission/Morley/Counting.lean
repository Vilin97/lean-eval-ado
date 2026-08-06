import Mathlib
import Submission.Morley.StronglyMinimal

/-!
# Counting formulas

The Baldwin–Lachlan chapter of this development, `Submission/Morley/StronglyMinimal.lean`, works
with *definable sets* (`FirstOrder.Language.Set.Definable`), which is a notion internal to one
fixed structure.  The passage from a model to an elementary extension — needed to know that a
minimal set stays minimal — has to be carried out at the level of *formulas*, and for that one
needs to say "the set defined by `χ` over the parameters `z` has at least `k` elements" by a
formula in the parameters `z`.  That is what this file provides.

## Main definitions

* `Submission.Morley.fiber χ z`: the subset of `M` defined by the formula `χ`, in variables
  `α ⊕ Fin 1`, when the `α`-block is interpreted by `z` and the `Fin 1`-block is the free variable.
* `Submission.Morley.atLeastF χ k`: a formula in the variables `α` saying that `fiber χ z` has at
  least `k` elements.

## Main results

* `Submission.Morley.realize_atLeastF`: the semantics of `atLeastF`, in the "injective `k`-tuple"
  form used throughout `Submission/Morley/StronglyMinimal.lean`.
* `Submission.Morley.finite_ncard_le_of_not_realize_atLeastF` and
  `Submission.Morley.not_realize_atLeastF_of_ncard_le`: the translation into cardinalities.
* `Submission.Morley.infinite_fiber_of_forall_realize_atLeastF`: a fibre satisfying every counting
  formula is infinite.
-/

namespace Submission.Morley

open Cardinal Set FirstOrder Language Theory

variable {L : FirstOrder.Language.{0, 0}}

/-! ## Fibres of a formula -/

/-- The subset of `M` defined by a formula `χ` in the variables `α ⊕ Fin 1`, with the `α`-block
interpreted by the tuple `z` and the `Fin 1`-block left free. -/
def fiber {M : Type} [L.Structure M] {α : Type} (χ : L.Formula (α ⊕ Fin 1)) (z : α → M) :
    Set M :=
  {x : M | χ.Realize (Sum.elim z fun _ => x)}

theorem mem_fiber_iff {M : Type} [L.Structure M] {α : Type} {χ : L.Formula (α ⊕ Fin 1)}
    {z : α → M} {x : M} : x ∈ fiber χ z ↔ χ.Realize (Sum.elim z fun _ => x) := Iff.rfl

/-! ## The counting formulas -/

/-- `atLeastF χ k` is a formula in the variables `α` which says that the fibre of `χ` over the
`α`-block has at least `k` elements: there are `k` pairwise distinct elements satisfying `χ`. -/
noncomputable def atLeastF {α : Type} (χ : L.Formula (α ⊕ Fin 1)) (k : ℕ) : L.Formula α :=
  Formula.iExs (Fin k)
    ((Formula.iInf fun i : Fin k => χ.relabel (Sum.map id fun _ : Fin 1 => i)) ⊓
      Formula.iInf fun p : {p : Fin k × Fin k // p.1 ≠ p.2} =>
        Formula.not
          ((Term.var (Sum.inr p.1.1) : L.Term (α ⊕ Fin k)).equal (Term.var (Sum.inr p.1.2))))

variable {M : Type} [L.Structure M] {α : Type} {χ : L.Formula (α ⊕ Fin 1)} {z : α → M}

/-- **The semantics of the counting formulas.** -/
theorem realize_atLeastF (k : ℕ) :
    (atLeastF χ k).Realize z ↔
      ∃ v : Fin k → M, Function.Injective v ∧ ∀ i, v i ∈ fiber χ z := by
  rw [atLeastF, Formula.realize_iExs]
  refine exists_congr fun v => ?_
  rw [Formula.realize_inf, Formula.realize_iInf, Formula.realize_iInf]
  have hcomp : ∀ i : Fin k,
      (Sum.elim z v) ∘ (Sum.map id fun _ : Fin 1 => i) = Sum.elim z fun _ : Fin 1 => v i := by
    intro i
    funext x
    rcases x with a | j
    · rfl
    · rfl
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun a b hab => ?_, fun i => ?_⟩
    · by_contra hne
      have := h2 ⟨(a, b), hne⟩
      rw [Formula.realize_not, Formula.realize_equal] at this
      exact this (by simpa using hab)
    · have := h1 i
      rw [Formula.realize_relabel, hcomp i] at this
      exact this
  · rintro ⟨hinj, hmem⟩
    refine ⟨fun i => ?_, fun p => ?_⟩
    · rw [Formula.realize_relabel, hcomp i]
      exact hmem i
    · rw [Formula.realize_not, Formula.realize_equal]
      intro hcon
      exact p.2 (hinj (by simpa using hcon))

/-- A fibre failing the counting formula for `n + 1` is finite with at most `n` elements. -/
theorem finite_ncard_le_of_not_realize_atLeastF {n : ℕ} (h : ¬ (atLeastF χ (n + 1)).Realize z) :
    (fiber χ z).Finite ∧ (fiber χ z).ncard ≤ n :=
  finite_ncard_le_of_no_injective (by rwa [realize_atLeastF] at h)

/-- A finite fibre with at most `n` elements fails the counting formula for `n + 1`. -/
theorem not_realize_atLeastF_of_ncard_le {n : ℕ} (hfin : (fiber χ z).Finite)
    (hc : (fiber χ z).ncard ≤ n) : ¬ (atLeastF χ (n + 1)).Realize z := by
  rw [realize_atLeastF]
  exact no_injective_of_ncard_le hfin hc

/-- A fibre satisfying every counting formula is infinite. -/
theorem infinite_fiber_of_forall_realize_atLeastF (h : ∀ k : ℕ, (atLeastF χ k).Realize z) :
    (fiber χ z).Infinite := by
  intro hfin
  exact not_realize_atLeastF_of_ncard_le hfin le_rfl (h ((fiber χ z).ncard + 1))

/-- An infinite fibre satisfies every counting formula. -/
theorem realize_atLeastF_of_infinite (h : (fiber χ z).Infinite) (k : ℕ) :
    (atLeastF χ k).Realize z := by
  classical
  obtain ⟨t, hts, htc⟩ := h.exists_subset_card_eq k
  rw [realize_atLeastF]
  refine ⟨fun i => ((t.equivFin.symm (Fin.cast htc.symm i) : M)), ?_, ?_⟩
  · intro i j hij
    have := t.equivFin.symm.injective (Subtype.ext hij)
    simpa using this
  · intro i
    have := hts (t.equivFin.symm (Fin.cast htc.symm i)).2
    simpa using this

/-- A fibre is infinite exactly when it satisfies every counting formula. -/
theorem infinite_fiber_iff_forall_realize_atLeastF :
    (fiber χ z).Infinite ↔ ∀ k : ℕ, (atLeastF χ k).Realize z :=
  ⟨fun h k => realize_atLeastF_of_infinite h k, infinite_fiber_of_forall_realize_atLeastF⟩

end Submission.Morley
