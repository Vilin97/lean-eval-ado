import Mathlib
import Submission.Morley.Stable

/-!
# Complete `1`-types over a parameter set, as sets of formulas

A complete `1`-type over a parameter set `A ⊆ M` is defined in `Submission.Morley.Stable` as a
maximal consistent extension `p : S₁ L A` of `Th(M_A)` in the language `L[[A]][[Fin 1]]`.  For the
compactness arguments of `Submission.Morley.Realize` it is more convenient to see `p` as a set
`typeForms p` of honest `L`-formulas `φ : L.Formula (↥A ⊕ Fin 1)`, whose `Sum.inl` variables range
over the parameters and whose single `Sum.inr` variable is the free variable of the type.

## Main results

* `Submission.Morley.exists_realize_of_finset_typeForms`: a complete `1`-type over `A ⊆ M` is
  *finitely satisfiable in `M` itself* — any finite subset of `typeForms p` is realized by an
  element of `M`.
* `Submission.Morley.typeOfElem_eq_of_forall_realize`: conversely, an element of `M` satisfying
  every formula of `typeForms p` realizes `p`.
-/

namespace Submission.Morley

open Cardinal Set FirstOrder FirstOrder.Language Theory

variable {L : FirstOrder.Language.{0, 0}} {M : Type} [L.Structure M] [Nonempty M]

/-- The `L`-formulas in the parameters `A` and one free variable which belong to `p`. -/
def typeForms {A : Set M} (p : S₁ L A) : Set (L.Formula (↥A ⊕ Fin 1)) :=
  {φ | Formula.equivSentence (BoundedFormula.constantsVarsEquiv.symm φ) ∈ p}

omit [Nonempty M] in
/-- Membership in `typeForms p`, unfolded. -/
theorem mem_typeForms {A : Set M} {p : S₁ L A} {φ : L.Formula (↥A ⊕ Fin 1)} :
    φ ∈ typeForms p ↔ Formula.equivSentence (BoundedFormula.constantsVarsEquiv.symm φ) ∈ p :=
  Iff.rfl

omit [Nonempty M] in
/-- Reading an `L`-formula in the parameters `A` and one free variable as an `L[[A]]`-formula in
one free variable does not change what it says about `M`. -/
theorem realize_constantsVarsEquiv_symm {A : Set M} (φ : L.Formula (↥A ⊕ Fin 1))
    (w : Fin 1 → M) :
    Formula.Realize (BoundedFormula.constantsVarsEquiv.symm φ) w ↔
      φ.Realize (Sum.elim (fun x : ↥A => (x : M)) w) := by
  have h := BoundedFormula.realize_constantsVarsEquiv (M := M) (L := L) (α := ↥A) (β := Fin 1)
    (n := 0) (φ := BoundedFormula.constantsVarsEquiv.symm φ) (v := w) (xs := default)
  rw [Equiv.apply_symm_apply] at h
  exact h.symm

/-- The single `L[[A]]`-sentence saying that some element satisfies every formula of the finite
set `t`. -/
noncomputable def finsetSentence {A : Set M} (t : Finset (L.Formula (↥A ⊕ Fin 1))) :
    (L[[↥A]]).Sentence :=
  Formula.iExs (Fin 1) (Formula.relabel Sum.inr
    (Formula.iInf fun φ : {φ : L.Formula (↥A ⊕ Fin 1) // φ ∈ t} =>
      BoundedFormula.constantsVarsEquiv.symm (φ : L.Formula (↥A ⊕ Fin 1))))

omit [L.Structure M] [Nonempty M] in
/-- `finsetSentence t` says exactly what it should in any `L[[A]]`-structure. -/
theorem realize_finsetSentence {A : Set M} (t : Finset (L.Formula (↥A ⊕ Fin 1)))
    (N : Type) [(L[[↥A]]).Structure N] :
    N ⊨ finsetSentence t ↔
      ∃ w : Fin 1 → N, ∀ φ ∈ t,
        Formula.Realize (BoundedFormula.constantsVarsEquiv.symm φ) w := by
  simp [finsetSentence, Sentence.Realize, Formula.realize_iExs, Formula.realize_relabel,
    Formula.realize_iInf, Function.comp_def]

omit [Nonempty M] in
/-- Two complete types one of which contains the other are equal: a complete type is a *maximal*
consistent theory. -/
theorem completeType_eq_of_subset {A : Set M} {p q : S₁ L A}
    (h : (p : ((L[[↥A]])[[Fin 1]]).Theory) ⊆ (q : ((L[[↥A]])[[Fin 1]]).Theory)) : q = p := by
  refine SetLike.coe_injective (Set.Subset.antisymm (fun σ hσ => ?_) h)
  by_contra hσp
  exact CompleteType.false_of_mem_of_not_mem q.isMaximal.1 hσ
    (h (((CompleteType.not_mem_iff p σ).2 hσp)))

omit [Nonempty M] in
/-- A complete `1`-type over a parameter set `A ⊆ M` is finitely satisfiable in `M` itself. -/
theorem exists_realize_of_finset_typeForms {A : Set M} (p : S₁ L A)
    (t : Finset (L.Formula (↥A ⊕ Fin 1))) (ht : ↑t ⊆ typeForms p) :
    ∃ a : M, ∀ φ ∈ t, φ.Realize (Sum.elim (fun x : ↥A => (x : M)) fun _ => a) := by
  classical
  obtain ⟨N, w, hw⟩ := exists_modelType_realizes (L := L) A p
  have hN : N ⊨ finsetSentence t := by
    refine (realize_finsetSentence t N).2 ⟨w, fun φ hφ => ?_⟩
    have : Formula.equivSentence (BoundedFormula.constantsVarsEquiv.symm φ) ∈
        (paramTheory L A).typeOf w := by
      rw [hw]; exact ht hφ
    exact CompleteType.formula_mem_typeOf.1 this
  have hM : M ⊨ finsetSentence t := by
    by_contra hc
    have hnot : (finsetSentence t).not ∈ paramTheory L A :=
      mem_paramTheory.2 ((Sentence.realize_not M).2 hc)
    exact ((Sentence.realize_not (N : Type)).1 (N.is_model.realize_of_mem _ hnot)) hN
  obtain ⟨v, hv⟩ := (realize_finsetSentence t M).1 hM
  refine ⟨v 0, fun φ hφ => ?_⟩
  have hveq : (fun _ : Fin 1 => v 0) = v := by
    funext i; fin_cases i; rfl
  rw [hveq]
  exact (realize_constantsVarsEquiv_symm φ v).1 (hv φ hφ)

/-- An element of `M` satisfying every formula of `p` realizes `p`. -/
theorem typeOfElem_eq_of_forall_realize {A : Set M} (p : S₁ L A) (a : M)
    (ha : ∀ φ ∈ typeForms p, φ.Realize (Sum.elim (fun x : ↥A => (x : M)) fun _ => a)) :
    typeOfElem A a = p := by
  refine completeType_eq_of_subset fun σ hσ => ?_
  set ψ : (L[[↥A]]).Formula (Fin 1) := Formula.equivSentence.symm σ with hψ
  have hmem : BoundedFormula.constantsVarsEquiv ψ ∈ typeForms p := by
    rw [mem_typeForms, Equiv.symm_apply_apply, hψ, Equiv.apply_symm_apply]
    exact hσ
  have hreal := ha _ hmem
  rw [← realize_constantsVarsEquiv_symm, Equiv.symm_apply_apply] at hreal
  exact mem_typeOfElem.2 hreal

end Submission.Morley
