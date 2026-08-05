/-
# Ehrenfeucht–Mostowski models and their type-counting property

A chapter of Morley's categoricity theorem.
-/
import Mathlib
import Submission.Morley.Indiscernibles

namespace Submission.Morley

open Cardinal FirstOrder.Language

universe u v w

/-! ## Order indiscernible sequences -/

section Indiscernible

variable {L : FirstOrder.Language.{u, v}} {M : Type w} [L.Structure M] {I : Type*} [LinearOrder I]

variable {a : I → M}

/-- An order indiscernible family which takes two distinct values is injective. -/
theorem IsOrderIndiscernible.injective (ha : IsOrderIndiscernible L a) {i₀ j₀ : I}
    (hlt : i₀ < j₀) (hne : a i₀ ≠ a j₀) : Function.Injective a := by
  have hmono : ∀ x y : I, x < y → StrictMono ![x, y] := by
    intro x y hxy k l hkl
    fin_cases k <;> fin_cases l <;> simp_all
  have main : ∀ x y : I, x < y → a x ≠ a y := by
    intro x y hxy
    have h := ha 2 ((FirstOrder.Language.Term.var 0).equal (FirstOrder.Language.Term.var 1))
      ![x, y] ![i₀, j₀] (hmono x y hxy) (hmono i₀ j₀ hlt)
    simp only [Formula.realize_equal, Term.realize_var, Function.comp_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one] at h
    exact fun hh => hne (h.mp hh)
  intro x y hxy
  rcases lt_trichotomy x y with h | h | h
  · exact absurd hxy (main x y h)
  · exact h
  · exact absurd hxy.symm (main y x h)

/-- The main use of indiscernibility: if `g : I → I` is strictly monotone on a set `s`, then
precomposing a valuation indexed by `s` with `g` does not change the truth value of a formula. -/
theorem IsOrderIndiscernible.realize_comp (ha : IsOrderIndiscernible L a) {s : Set I} (g : I → I)
    (hg : StrictMonoOn g s) (φ : L.Formula s) :
    ((φ.Realize fun x : s => a (x : I)) ↔ (φ.Realize fun x : s => a (g (x : I)))) := by
  classical
  obtain ⟨N, e, -⟩ : ∃ (N : ℕ) (_ : Fin N ≃o φ.freeVarFinset), True :=
    ⟨_, φ.freeVarFinset.orderIsoOfFin rfl, trivial⟩
  set ι : Fin N → I := fun k => (((e k : s) : I)) with hι
  have hmem : ∀ k, ι k ∈ s := fun k => (e k : s).2
  have hιmono : StrictMono ι := fun k l hkl => e.lt_iff_lt.mpr hkl
  have hι'mono : StrictMono (g ∘ ι) := fun k l hkl => hg (hmem k) (hmem l) (hιmono hkl)
  have h1 : Formula.Realize (φ.restrictFreeVar (⇑e.symm)) (a ∘ ι) ↔
      (φ.Realize fun x : s => a (x : I)) :=
    BoundedFormula.realize_restrictFreeVar _ fun y => by
      simp only [Function.comp_apply, hι, OrderIso.apply_symm_apply]
  have h2 : Formula.Realize (φ.restrictFreeVar (⇑e.symm)) (a ∘ (g ∘ ι)) ↔
      (φ.Realize fun x : s => a (g (x : I))) :=
    BoundedFormula.realize_restrictFreeVar _ fun y => by
      simp only [Function.comp_apply, hι, OrderIso.apply_symm_apply]
  rw [← h1, ← h2]
  exact ha N (φ.restrictFreeVar (⇑e.symm)) ι (g ∘ ι) hιmono hι'mono

end Indiscernible

/-- Existence of order indiscernibles, supplied by the Ramsey chapter. -/
def IndiscerniblesExist (L : FirstOrder.Language.{0, 0}) : Prop :=
  ∀ (T : L.Theory) (_ : T.IsSatisfiable)
    (_ : ∀ M : FirstOrder.Language.Theory.ModelType.{0, 0, 0} T, Infinite M)
    (I : Type) [LinearOrder I],
    ∃ (M : FirstOrder.Language.Theory.ModelType.{0, 0, 0} T) (a : I → M),
      IsOrderIndiscernible L a

/-! ## Coding positions relative to a subset of a well-ordered index set

The type-counting property below needs the index order `I` to be **well-ordered**, not merely
linear.  This is not an artefact of the proof: for `T` the theory of dense linear orders,
`I = ℝ`, `a` the identity and `A = {a_q : q ∈ ℚ}`, the elements `a_r` with `r` irrational have
pairwise distinct types over the countable set `A`, so continuum many types over a countable
set are realised in `EM(ℝ)`.  Well-orderedness is what makes the number of cuts of a subset
`J ⊆ I` that are realised in `I` at most `#J + 1`: each such cut is `{j ∈ J | j < x}` and is
determined by the least element of `J` above `x`.  Morley's proof only ever uses `EM(κ)` for
ordinals/cardinals `κ`, which are well-ordered. -/

section IdxCode

variable {I : Type*} [LinearOrder I] [WellFoundedLT I]

open scoped Classical in
/-- The least element of `J` which is `≥ x`, if there is one. -/
noncomputable def cutTop (J : Set I) (x : I) : Option J :=
  if h : {y : I | y ∈ J ∧ x ≤ y}.Nonempty then
    some ⟨wellFounded_lt.min _ h, (wellFounded_lt.min_mem _ h).1⟩
  else none

open scoped Classical in
/-- The membership component of the index code. -/
noncomputable def memCode (J : Set I) (x : I) : Option J :=
  if h : x ∈ J then some ⟨x, h⟩ else none

/-- The *index code* of `x : I` relative to `J ⊆ I`: the least element of `J` above `x`
(if any), together with `x` itself when `x` happens to lie in `J`.

When `I` is well-ordered this is a small amount of data (there are at most `#J + 1` possible
values of each component), and it completely determines the position of `x` relative to every
element of `J`. -/
noncomputable def idxCode (J : Set I) (x : I) : Option J × Option J :=
  (cutTop J x, memCode J x)

open scoped Classical in
theorem lt_cutTop_iff {J : Set I} {x j : I} (hj : j ∈ J) :
    (j < x ↔ (cutTop J x).elim True fun m => j < (m : I)) := by
  rw [cutTop]
  split_ifs with h
  · simp only [Option.elim]
    have hmem : wellFounded_lt.min {y : I | y ∈ J ∧ x ≤ y} h ∈ {y : I | y ∈ J ∧ x ≤ y} :=
      wellFounded_lt.min_mem _ h
    constructor
    · intro hjx
      exact lt_of_lt_of_le hjx hmem.2
    · intro hjm
      by_contra hc
      push Not at hc
      exact wellFounded_lt.not_lt_min {y : I | y ∈ J ∧ x ≤ y} ⟨hj, hc⟩ hjm
  · simp only [Option.elim, iff_true]
    by_contra hc
    push Not at hc
    exact h ⟨j, hj, hc⟩

theorem lt_iff_of_idxCode_eq {J : Set I} {x y : I} (h : idxCode J x = idxCode J y) {j : I}
    (hj : j ∈ J) : (j < x ↔ j < y) := by
  have hc : cutTop J x = cutTop J y := congrArg Prod.fst h
  rw [lt_cutTop_iff hj, lt_cutTop_iff hj, hc]

open scoped Classical in
theorem eq_of_idxCode_eq {J : Set I} {x y : I} (h : idxCode J x = idxCode J y) (hx : x ∈ J) :
    y = x := by
  have hc : memCode J x = memCode J y := congrArg Prod.snd h
  rw [memCode, memCode, dif_pos hx] at hc
  by_cases hy : y ∈ J
  · rw [dif_pos hy] at hc
    exact (congrArg Subtype.val (Option.some.inj hc)).symm
  · rw [dif_neg hy] at hc
    exact absurd hc (by simp)

theorem gt_iff_of_idxCode_eq {J : Set I} {x y : I} (h : idxCode J x = idxCode J y) {j : I}
    (hj : j ∈ J) : (x < j ↔ y < j) := by
  have h1 := lt_iff_of_idxCode_eq h hj
  have h2 : x = j ↔ y = j := by
    constructor
    · rintro rfl; exact eq_of_idxCode_eq h hj
    · rintro rfl; exact eq_of_idxCode_eq h.symm hj
  constructor
  · intro hxj
    rcases lt_trichotomy y j with hh | hh | hh
    · exact hh
    · exact absurd (h2.mpr hh) (ne_of_lt hxj)
    · exact absurd (h1.mpr hh) (not_lt.mpr hxj.le)
  · intro hyj
    rcases lt_trichotomy x j with hh | hh | hh
    · exact hh
    · exact absurd (h2.mp hh) (ne_of_lt hyj)
    · exact absurd (h1.mp hh) (not_lt.mpr hyj.le)

end IdxCode

/-! ## Skolem hulls and Ehrenfeucht–Mostowski models

Mathlib's `FirstOrder.Language.skolem₁` only provides the *first* step of a Skolemisation.
That is all that is needed here: by `Substructure.elementarySkolem₁Reduct`, *every*
substructure of a structure in the language `L.sum L.skolem₁` (equipped with the canonical
choice-based Skolem functions) is already an elementary substructure for `L`.  Hence Skolem
hulls can be taken with plain `Substructure.closure` in `L.sum L.skolem₁`, and no recursive
Skolemisation of the language is required. -/

section EM

variable {L : FirstOrder.Language.{0, 0}} {M : Type} [(L.sum L.skolem₁).Structure M]
variable {I : Type} [LinearOrder I]

/-- The Skolem hull of the range of `a : I → M`: the closure of `Set.range a` under all the
Skolem function symbols of `L.sum L.skolem₁`.  When the Skolem functions really are Skolem
functions this is an elementary `L`-substructure of `M`; see `EM`. -/
noncomputable def EMSub (L : FirstOrder.Language.{0, 0}) {M : Type}
    [(L.sum L.skolem₁).Structure M] {I : Type} [LinearOrder I] (a : I → M) :
    (L.sum L.skolem₁).Substructure M :=
  Substructure.closure (L.sum L.skolem₁) (Set.range a)

theorem mem_EMSub_iff' (a : I → M) (x : M) :
    x ∈ EMSub L a ↔ x ∈ Substructure.closure (L.sum L.skolem₁) (Set.range a) := Iff.rfl

/-- Every element of the Skolem hull is the value of a Skolem term at a strictly increasing
tuple of indices, and conversely.  This is the combinatorial heart of the whole chapter. -/
theorem mem_EMSub_iff {a : I → M} {x : M} :
    x ∈ EMSub L a ↔ ∃ (n : ℕ) (t : (L.sum L.skolem₁).Term (Fin n)) (i : Fin n → I),
      StrictMono i ∧ t.realize (a ∘ i) = x := by
  classical
  rw [mem_EMSub_iff', Substructure.mem_closure_iff_exists_term]
  constructor
  · rintro ⟨t, rfl⟩
    have hidx : ∀ y : (Set.range a), ∃ i : I, a i = (y : M) := fun y => y.2
    choose idx hidx using hidx
    have hcomp : (a ∘ idx) = ((↑) : Set.range a → M) := funext hidx
    have ht₁r : (t.relabel idx).realize a = t.realize ((↑) : Set.range a → M) := by
      rw [Term.realize_relabel, hcomp]
    obtain ⟨N, e, -⟩ : ∃ (N : ℕ) (_ : Fin N ≃o (t.relabel idx).varFinset), True :=
      ⟨_, (t.relabel idx).varFinset.orderIsoOfFin rfl, trivial⟩
    refine ⟨N, (t.relabel idx).restrictVar (⇑e.symm), fun k => ((e k : I)), ?_, ?_⟩
    · exact fun k l hkl => e.lt_iff_lt.mpr hkl
    · rw [← ht₁r]
      refine Term.realize_restrictVar a fun y => ?_
      simp only [Function.comp_apply, OrderIso.apply_symm_apply]
  · rintro ⟨n, t, i, -, rfl⟩
    refine ⟨t.relabel fun k => (⟨a (i k), ⟨i k, rfl⟩⟩ : Set.range a), ?_⟩
    rw [Term.realize_relabel]
    rfl

theorem range_subset_EMSub (a : I → M) : Set.range a ⊆ (EMSub L a : Set M) := fun x hx => by
  rw [SetLike.mem_coe, mem_EMSub_iff']
  exact Substructure.subset_closure hx

theorem card_functions_skolem_le (hL : L.card ≤ ℵ₀) :
    #(Σ n, (L.sum L.skolem₁).Functions n) ≤ ℵ₀ :=
  card_functions_sum_skolem₁_le.trans (max_le le_rfl hL)

/-- The Skolem hull has cardinality at most `max ℵ₀ #I`. -/
theorem card_EMSub_le (hL : L.card ≤ ℵ₀) (a : I → M) : #(EMSub L a) ≤ max ℵ₀ #I := by
  have h := Substructure.lift_card_closure_le (L := L.sum L.skolem₁) (s := Set.range a)
  simp only [Cardinal.lift_id] at h
  have he : #(EMSub L a) = #(Substructure.closure (L.sum L.skolem₁) (Set.range a)) := rfl
  rw [he]
  refine h.trans (max_le (le_max_left _ _) ?_)
  refine Cardinal.add_le_of_le (le_max_left _ _) ?_ ?_
  · exact Cardinal.mk_range_le.trans (le_max_right _ _)
  · exact (card_functions_skolem_le hL).trans (le_max_left _ _)

end EM

section EMCanonical

variable {L : FirstOrder.Language.{0, 0}} {M : Type} [L.Structure M] [Nonempty M]
variable {I : Type} [LinearOrder I]

/-- The Ehrenfeucht–Mostowski model attached to a family `a : I → M`: the Skolem hull of the
range of `a` inside `M`, taken with respect to Mathlib's canonical (choice-based) Skolem
functions.  It is an elementary `L`-substructure of `M`. -/
noncomputable def EM (L : FirstOrder.Language.{0, 0}) {M : Type} [L.Structure M] [Nonempty M]
    {I : Type} [LinearOrder I] (a : I → M) : L.ElementarySubstructure M :=
  Substructure.elementarySkolem₁Reduct (EMSub L a)

theorem coe_EM (a : I → M) : (EM L a : Set M) = (EMSub L a : Set M) := rfl

theorem mem_EM_iff {a : I → M} {x : M} :
    x ∈ EM L a ↔ ∃ (n : ℕ) (t : (L.sum L.skolem₁).Term (Fin n)) (i : Fin n → I),
      StrictMono i ∧ t.realize (a ∘ i) = x := mem_EMSub_iff

theorem range_subset_EM (a : I → M) : Set.range a ⊆ (EM L a : Set M) := range_subset_EMSub a

/-- `EM L a` is an elementary substructure, hence models every theory that `M` models.
This is the statement `EM(I) ⊨ T`. -/
theorem EM_model (T : L.Theory) [M ⊨ T] (a : I → M) : (EM L a : Type) ⊨ T := inferInstance

/-- `EM L a` has cardinality at most `max ℵ₀ #I = #I + ℵ₀`. -/
theorem card_EM_le (hL : L.card ≤ ℵ₀) (a : I → M) : #(EM L a) ≤ max ℵ₀ #I :=
  card_EMSub_le hL a

/-- If `a` is injective and `M` is infinite then `EM L a` has cardinality exactly
`max ℵ₀ #I = #I + ℵ₀`. -/
theorem card_EM_eq (hL : L.card ≤ ℵ₀) [Infinite M] {a : I → M} (hinj : Function.Injective a) :
    #(EM L a) = max ℵ₀ #I := by
  refine le_antisymm (card_EM_le hL a) (max_le ?_ ?_)
  · have hinf : Infinite (EM L a) :=
      ((EM L a).elementarilyEquivalent).infinite_iff.2 (inferInstance : Infinite M)
    exact Cardinal.infinite_iff.1 hinf
  · have h1 : #I = #(Set.range a) := (Cardinal.mk_range_eq a hinj).symm
    rw [h1]
    exact Cardinal.mk_le_mk_of_subset (range_subset_EM (L := L) a)

/-- `#EM(I) ≤ #I + ℵ₀`. -/
theorem card_EM_le' (hL : L.card ≤ ℵ₀) (a : I → M) : #(EM L a) ≤ #I + ℵ₀ := by
  rw [add_comm, Cardinal.add_eq_max le_rfl]
  exact card_EM_le hL a

/-- `#EM(I) = #I + ℵ₀`. -/
theorem card_EM_eq' (hL : L.card ≤ ℵ₀) [Infinite M] {a : I → M} (hinj : Function.Injective a) :
    #(EM L a) = #I + ℵ₀ := by
  rw [add_comm, Cardinal.add_eq_max le_rfl]
  exact card_EM_eq hL hinj

end EMCanonical

/-! ## Types over a parameter set -/

/-- The type of `b : M` over the parameter set `A ⊆ M`: the set of all pairs consisting of a
formula `φ(x₀,…,x_{m-1}, y)` and a tuple of parameters from `A` that `b` satisfies.  Two
elements have the same `emTypeOver L A` exactly when they satisfy the same `L`-formulas with
parameters in `A`, so `Set.range (emTypeOver L A)` is the set of `1`-types over `A` realised. -/
def emTypeOver (L : FirstOrder.Language.{u, v}) {M : Type w} [L.Structure M] (A : Set M) (b : M) :
    Set ((m : ℕ) × L.Formula (Fin m ⊕ Fin 1) × (Fin m → A)) :=
  {p | p.2.1.Realize (Sum.elim (fun r => ((p.2.2 r : M))) fun _ => b)}

/-! ## The type-counting property -/

section Counting

variable {L : FirstOrder.Language.{0, 0}} {M : Type} [L.Structure M]
  [(L.sum L.skolem₁).Structure M]
  [(FirstOrder.Language.LHom.sumInl : L →ᴸ L.sum L.skolem₁).IsExpansionOn M]
variable {I : Type} [LinearOrder I] [WellFoundedLT I]

/-- **Key lemma.**  If two Skolem terms are the *same* term `t` evaluated at two strictly
increasing index tuples with the same index codes relative to `J`, then their values realize
the same type over any parameter set `A` all of whose elements are values of Skolem terms at
indices from `J`. -/
theorem typeOver_eq_of_idxCode_eq {a : I → M}
    (ha : IsOrderIndiscernible (L.sum L.skolem₁) a) {A : Set M} {J : Set I}
    (hAJ : ∀ c : A, ∃ (m : ℕ) (s : (L.sum L.skolem₁).Term (Fin m)) (p : Fin m → I),
      (∀ k, p k ∈ J) ∧ s.realize (a ∘ p) = (c : M))
    {n : ℕ} (t : (L.sum L.skolem₁).Term (Fin n)) {i i' : Fin n → I}
    (hi : StrictMono i) (hi' : StrictMono i')
    (hkey : ∀ k, idxCode J (i k) = idxCode J (i' k)) :
    emTypeOver L A (t.realize (a ∘ i)) = emTypeOver L A (t.realize (a ∘ i')) := by
  classical
  choose mA sA pA hpA hsA using hAJ
  set g : I → I := fun x => if h : ∃ k, i k = x then i' h.choose else x with hgdef
  have hg2 : ∀ k, g (i k) = i' k := by
    intro k
    have h : ∃ k', i k' = i k := ⟨k, rfl⟩
    simp only [hgdef, dif_pos h]
    exact congrArg i' (hi.injective h.choose_spec)
  have hgJ : ∀ x ∈ J, g x = x := by
    intro x hx
    by_cases h : ∃ k, i k = x
    · obtain ⟨k, hk⟩ := h
      subst hk
      rw [hg2 k]
      exact eq_of_idxCode_eq (hkey k) hx
    · simp only [hgdef, dif_neg h]
  have hval : ∀ x ∈ J ∪ Set.range i, (x ∈ J ∧ g x = x) ∨ ∃ k, x = i k ∧ g x = i' k := by
    rintro x (hx | ⟨k, rfl⟩)
    · exact Or.inl ⟨hx, hgJ x hx⟩
    · exact Or.inr ⟨k, rfl, hg2 k⟩
  have hgs : StrictMonoOn g (J ∪ Set.range i) := by
    rintro x hx y hy hxy
    rcases hval x hx with ⟨hxJ, hgx⟩ | ⟨k, rfl, hgx⟩ <;>
      rcases hval y hy with ⟨hyJ, hgy⟩ | ⟨l, rfl, hgy⟩
    · rw [hgx, hgy]; exact hxy
    · rw [hgx, hgy]; exact (lt_iff_of_idxCode_eq (hkey l) hxJ).mp hxy
    · rw [hgx, hgy]; exact (gt_iff_of_idxCode_eq (hkey k) hyJ).mp hxy
    · rw [hgx, hgy]; exact hi' (hi.lt_iff_lt.mp hxy)
  ext p
  obtain ⟨m, φ, c⟩ := p
  simp only [emTypeOver, Set.mem_setOf_eq]
  set σ : (Fin m ⊕ Fin 1) → (L.sum L.skolem₁).Term ↥(J ∪ Set.range i) :=
    Sum.elim
      (fun r => (sA (c r)).relabel fun q =>
        (⟨pA (c r) q, Or.inl (hpA (c r) q)⟩ : ↥(J ∪ Set.range i)))
      (fun _ => t.relabel fun k => (⟨i k, Or.inr ⟨k, rfl⟩⟩ : ↥(J ∪ Set.range i))) with hσ
  set ψ : (L.sum L.skolem₁).Formula ↥(J ∪ Set.range i) :=
    ((FirstOrder.Language.LHom.sumInl : L →ᴸ L.sum L.skolem₁).onFormula φ).subst σ with hψ
  have key : ∀ v : ↥(J ∪ Set.range i) → M,
      (Formula.Realize ψ v ↔ φ.Realize fun x => (σ x).realize v) := by
    intro v
    rw [hψ]
    exact BoundedFormula.realize_subst.trans (LHom.realize_onFormula _ φ)
  have v1 : (fun x => (σ x).realize fun y : ↥(J ∪ Set.range i) => a (y : I)) =
      Sum.elim (fun r => ((c r : M))) fun _ => t.realize (a ∘ i) := by
    funext x
    rcases x with r | r
    · simp only [hσ, Sum.elim_inl, Term.realize_relabel]
      exact hsA (c r)
    · simp only [hσ, Sum.elim_inr, Term.realize_relabel]
      rfl
  have v2 : (fun x => (σ x).realize fun y : ↥(J ∪ Set.range i) => a (g (y : I))) =
      Sum.elim (fun r => ((c r : M))) fun _ => t.realize (a ∘ i') := by
    funext x
    rcases x with r | r
    · simp only [hσ, Sum.elim_inl, Term.realize_relabel]
      rw [← hsA (c r)]
      congr 1
      funext q
      exact congrArg a (hgJ _ (hpA (c r) q))
    · simp only [hσ, Sum.elim_inr, Term.realize_relabel]
      congr 1
      funext k
      exact congrArg a (hg2 k)
  have E1 := key fun y : ↥(J ∪ Set.range i) => a (y : I)
  have E2 := key fun y : ↥(J ∪ Set.range i) => a (g (y : I))
  rw [v1] at E1
  rw [v2] at E2
  rw [← E1, ← E2]
  exact ha.realize_comp g hgs ψ

/-- **The type-counting property of Ehrenfeucht–Mostowski models** (version with an explicit
index set `J`).  If every element of `A` is a Skolem term evaluated at indices from `J`, and
`#J ≤ μ` for an infinite cardinal `μ`, then at most `μ` types over `A` are realised in
`EM L a`. -/
theorem card_typeOver_image_le_of_index {a : I → M}
    (hL : L.card ≤ ℵ₀) (ha : IsOrderIndiscernible (L.sum L.skolem₁) a)
    {A : Set M} {J : Set I}
    (hAJ : ∀ c : A, ∃ (m : ℕ) (s : (L.sum L.skolem₁).Term (Fin m)) (p : Fin m → I),
      (∀ k, p k ∈ J) ∧ s.realize (a ∘ p) = (c : M))
    {μ : Cardinal.{0}} (hJ : #J ≤ μ) (hμ : ℵ₀ ≤ μ) :
    #(emTypeOver L A '' (EMSub L a : Set M)) ≤ μ := by
  classical
  haveI : Countable (Σ n, (L.sum L.skolem₁).Functions n) :=
    Cardinal.mk_le_aleph0_iff.mp (card_functions_skolem_le hL)
  set f : ((n : ℕ) × ((L.sum L.skolem₁).Term (Fin n) × (Fin n → Option J × Option J))) →
      Set ((m : ℕ) × L.Formula (Fin m ⊕ Fin 1) × (Fin m → A)) := fun d =>
    if h : ∃ i : Fin d.1 → I, StrictMono i ∧ ∀ k, idxCode J (i k) = d.2.2 k then
      emTypeOver L A (d.2.1.realize (a ∘ h.choose))
    else ∅ with hf
  have hsub : emTypeOver L A '' (EMSub L a : Set M) ⊆ Set.range f := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨n, t, i, hi, rfl⟩ := mem_EMSub_iff.mp hx
    have hex : ∃ i' : Fin n → I, StrictMono i' ∧ ∀ k, idxCode J (i' k) = idxCode J (i k) :=
      ⟨i, hi, fun _ => rfl⟩
    refine ⟨⟨n, t, fun k => idxCode J (i k)⟩, ?_⟩
    rw [hf]
    simp only [dif_pos hex]
    exact typeOver_eq_of_idxCode_eq ha hAJ t hex.choose_spec.1 hi
      fun k => hex.choose_spec.2 k
  refine (Cardinal.mk_le_mk_of_subset hsub).trans (Cardinal.mk_range_le.trans ?_)
  have hOpt : #(Option J) ≤ μ := by
    rw [Cardinal.mk_option]
    exact (add_le_add hJ (Cardinal.one_le_aleph0.trans hμ)).trans
      (le_of_eq (Cardinal.add_eq_self hμ))
  have hK : #(Option J × Option J) ≤ μ := by
    calc #(Option J × Option J) = #(Option J) * #(Option J) := by
          rw [Cardinal.mk_prod]
          simp
      _ ≤ μ * μ := mul_le_mul' hOpt hOpt
      _ = μ := Cardinal.mul_eq_self hμ
  rw [Cardinal.mk_sigma]
  refine (Cardinal.sum_le_sum _ (fun _ => μ) ?_).trans ?_
  · intro n
    have h1 : #((L.sum L.skolem₁).Term (Fin n)) ≤ μ := Cardinal.mk_le_aleph0.trans hμ
    have h2 : #(Fin n → Option J × Option J) ≤ μ :=
      (Cardinal.mk_le_of_injective List.ofFn_injective).trans
        ((Cardinal.mk_list_le_max _).trans (max_le hμ hK))
    calc #((L.sum L.skolem₁).Term (Fin n) × (Fin n → Option J × Option J))
        = #((L.sum L.skolem₁).Term (Fin n)) * #(Fin n → Option J × Option J) := by
          rw [Cardinal.mk_prod]
          simp
      _ ≤ μ * μ := mul_le_mul' h1 h2
      _ = μ := Cardinal.mul_eq_self hμ
  · rw [Cardinal.sum_const']
    simpa using (Cardinal.mul_eq_max le_rfl hμ).trans_le (le_of_eq (max_eq_right hμ))

/-- **The type-counting property of Ehrenfeucht–Mostowski models.**

If `A` is a subset of the Ehrenfeucht–Mostowski model `EM L a` of size at most an infinite
cardinal `μ`, then at most `μ` types over `A` are realised in `EM L a`.

Every element of `EM L a` is `t(a_{i₁},…,a_{i_n})` for a Skolem term `t` and indices
`i₁ < ⋯ < i_n`; by indiscernibility its type over `A` depends only on `t` together with the
index codes of `i₁,…,i_n` relative to the (at most `μ` many) indices occurring in the terms
naming the elements of `A`.  There are at most `μ` such data because the language is
countable. -/
theorem card_realizedTypes_le {a : I → M}
    (hL : L.card ≤ ℵ₀) (ha : IsOrderIndiscernible (L.sum L.skolem₁) a)
    {A : Set M} (hA : A ⊆ (EMSub L a : Set M)) {μ : Cardinal.{0}} (hAμ : #A ≤ μ) (hμ : ℵ₀ ≤ μ) :
    #(emTypeOver L A '' (EMSub L a : Set M)) ≤ μ := by
  classical
  have hmem : ∀ c : A, ∃ (m : ℕ) (t : (L.sum L.skolem₁).Term (Fin m)) (p : Fin m → I),
      StrictMono p ∧ t.realize (a ∘ p) = (c : M) := fun c => mem_EMSub_iff.mp (hA c.2)
  choose mA sA pA _hpA hsA using hmem
  have hmemJ : ∀ (c : A) (k : Fin (mA c)), pA c k ∈ ⋃ c' : A, Set.range (pA c') :=
    fun c k => Set.mem_iUnion.mpr ⟨c, ⟨k, rfl⟩⟩
  have hJsub : (⋃ c : A, Set.range (pA c)) ⊆
      Set.range fun q : (Σ c : A, Fin (mA c)) => pA q.1 q.2 := by
    rintro x hx
    rw [Set.mem_iUnion] at hx
    obtain ⟨c, k, rfl⟩ := hx
    exact ⟨⟨c, k⟩, rfl⟩
  have hJcard : #(⋃ c : A, Set.range (pA c)) ≤ μ := by
    refine (Cardinal.mk_le_mk_of_subset hJsub).trans (Cardinal.mk_range_le.trans ?_)
    rw [Cardinal.mk_sigma]
    refine (Cardinal.sum_le_sum _ (fun _ => μ) ?_).trans ?_
    · intro c
      calc #(Fin (mA c)) = (mA c : Cardinal) := Cardinal.mk_fin _
        _ ≤ ℵ₀ := Cardinal.natCast_lt_aleph0.le
        _ ≤ μ := hμ
    · rw [Cardinal.sum_const']
      exact (mul_le_mul' hAμ le_rfl).trans (le_of_eq (Cardinal.mul_eq_self hμ))
  exact card_typeOver_image_le_of_index hL ha
    (J := ⋃ c : A, Set.range (pA c))
    (fun c => ⟨mA c, sA c, pA c, hmemJ c, hsA c⟩) hJcard hμ

/-- The special case `μ = ℵ₀` used in Morley's proof: only countably many types over a
countable subset of an Ehrenfeucht–Mostowski model are realised in it. -/
theorem countable_realizedTypes {a : I → M}
    (hL : L.card ≤ ℵ₀) (ha : IsOrderIndiscernible (L.sum L.skolem₁) a)
    {A : Set M} (hA : A ⊆ (EMSub L a : Set M)) (hAc : A.Countable) :
    (emTypeOver L A '' (EMSub L a : Set M)).Countable :=
  Cardinal.mk_le_aleph0_iff.mp
    (card_realizedTypes_le hL ha hA (Cardinal.mk_le_aleph0_iff.mpr hAc) le_rfl)
  |>.to_set

end Counting

section CountingCanonical

variable {L : FirstOrder.Language.{0, 0}} {M : Type} [L.Structure M] [Nonempty M]
variable {I : Type} [LinearOrder I] [WellFoundedLT I]

/-- **The type-counting property**, stated for the canonical Ehrenfeucht–Mostowski model
`EM L a` (which has the same underlying set as the Skolem hull `EMSub L a`). -/
theorem card_realizedTypes_le_EM {a : I → M} (hL : L.card ≤ ℵ₀)
    (ha : IsOrderIndiscernible (L.sum L.skolem₁) a)
    {A : Set M} (hA : A ⊆ (EM L a : Set M)) {μ : Cardinal.{0}} (hAμ : #A ≤ μ) (hμ : ℵ₀ ≤ μ) :
    #(emTypeOver L A '' (EM L a : Set M)) ≤ μ :=
  card_realizedTypes_le hL ha hA hAμ hμ

end CountingCanonical

/-! ## Skolem axioms

`Language.skolem₁` provides a function symbol `f_φ` of arity `n` for every `L`-formula
`φ(x₀,…,x_{n-1}, y)`.  A structure for `L.sum L.skolem₁` interprets these symbols by *arbitrary*
functions; the following theory forces them to be genuine Skolem functions.  Mathlib's canonical
(choice-based) expansion satisfies it, and satisfying it is exactly what makes Skolem hulls
elementary.  This lets us run the construction inside an arbitrary model produced by the Ramsey
chapter, whose Skolem functions need not be the canonical ones. -/

section SkolemTheory

variable (L : FirstOrder.Language.{0, 0})

/-- The function symbol of `L.sum L.skolem₁` which is meant to be a Skolem function for the
formula `φ(x̄, y)`. -/
def skolemFun {n : ℕ} (φ : L.BoundedFormula Empty (n + 1)) : (L.sum L.skolem₁).Functions n :=
  Sum.inr φ

/-- The Skolem axiom for `φ(x̄, y)`: `∀ x̄, (∃ y, φ(x̄, y)) → (∃ y, y = f_φ(x̄) ∧ φ(x̄, y))`. -/
def skolemAxiom {n : ℕ} (φ : L.BoundedFormula Empty (n + 1)) : (L.sum L.skolem₁).Sentence :=
  ((LHom.sumInl.onBoundedFormula φ : (L.sum L.skolem₁).BoundedFormula Empty (n + 1)).ex.imp
    (((Term.var (Sum.inr (Fin.last n)) :
          (L.sum L.skolem₁).Term (Empty ⊕ Fin (n + 1))).bdEqual
        (Term.func (skolemFun L φ) fun k =>
          Term.var (Sum.inr k.castSucc)) ⊓
      (LHom.sumInl.onBoundedFormula φ :
        (L.sum L.skolem₁).BoundedFormula Empty (n + 1))).ex)).alls

/-- The theory of all Skolem axioms for `L`. -/
def skolemTheory : (L.sum L.skolem₁).Theory :=
  Set.range fun p : (Σ n : ℕ, L.BoundedFormula Empty (n + 1)) => skolemAxiom L p.2

variable {L}

theorem realize_skolemAxiom {M : Type} [L.Structure M] [(L.sum L.skolem₁).Structure M]
    [(FirstOrder.Language.LHom.sumInl : L →ᴸ L.sum L.skolem₁).IsExpansionOn M]
    {n : ℕ} (φ : L.BoundedFormula Empty (n + 1)) :
    M ⊨ skolemAxiom L φ ↔ ∀ x : Fin n → M, (∃ b : M, φ.Realize default (Fin.snoc x b)) →
      φ.Realize default
        (Fin.snoc x (Structure.funMap (skolemFun L φ) x)) := by
  simp only [skolemAxiom, Sentence.Realize, BoundedFormula.realize_alls,
    BoundedFormula.realize_imp, BoundedFormula.realize_ex, BoundedFormula.realize_inf,
    BoundedFormula.realize_bdEqual, Term.realize_var, Term.realize_func, Sum.elim_inr,
    LHom.realize_onBoundedFormula, Fin.snoc_last, Fin.snoc_castSucc]
  constructor
  · intro h x hx
    obtain ⟨b, hb1, hb2⟩ := h x hx
    rwa [hb1] at hb2
  · exact fun h x hx => ⟨_, rfl, h x hx⟩

/-- Mathlib's canonical, choice-based Skolem expansion satisfies the Skolem axioms. -/
theorem model_skolemTheory (L : FirstOrder.Language.{0, 0}) (M : Type) [L.Structure M]
    [Nonempty M] : M ⊨ skolemTheory L := by
  refine ⟨?_⟩
  rintro _ ⟨⟨n, φ⟩, rfl⟩
  show M ⊨ skolemAxiom L φ
  rw [realize_skolemAxiom]
  intro x hx
  exact Classical.epsilon_spec (p := fun b => φ.Realize default (Fin.snoc x b)) hx

/-- **Tarski–Vaught for Skolem hulls.**  In a model of the Skolem axioms, the `L`-reduct of
every `L.sum L.skolem₁`-substructure is an elementary `L`-substructure. -/
theorem substructureReduct_isElementary_of_skolemTheory {M : Type} [L.Structure M]
    [(L.sum L.skolem₁).Structure M]
    [(FirstOrder.Language.LHom.sumInl : L →ᴸ L.sum L.skolem₁).IsExpansionOn M]
    (hM : M ⊨ skolemTheory L) (S : (L.sum L.skolem₁).Substructure M) :
    (LHom.sumInl.substructureReduct S).IsElementary := by
  apply (LHom.sumInl.substructureReduct S).isElementary_of_exists
  intro n φ x b h
  refine ⟨⟨Structure.funMap (skolemFun L φ) ((↑) ∘ x), ?_⟩, ?_⟩
  · exact S.fun_mem _ _ fun i => (x i).2
  · exact (realize_skolemAxiom φ).mp
      (Theory.realize_sentence_of_mem (M := M) (skolemTheory L) ⟨⟨n, φ⟩, rfl⟩) ((↑) ∘ x) ⟨b, h⟩

/-- The Ehrenfeucht–Mostowski model inside a model of the Skolem axioms: the Skolem hull of
`Set.range a`, an elementary `L`-substructure. -/
noncomputable def EMOf {M : Type} [L.Structure M] [(L.sum L.skolem₁).Structure M]
    [(FirstOrder.Language.LHom.sumInl : L →ᴸ L.sum L.skolem₁).IsExpansionOn M]
    (hM : M ⊨ skolemTheory L) {I : Type} [LinearOrder I] (a : I → M) :
    L.ElementarySubstructure M :=
  ⟨LHom.sumInl.substructureReduct (EMSub L a),
    substructureReduct_isElementary_of_skolemTheory hM _⟩

theorem coe_EMOf {M : Type} [L.Structure M] [(L.sum L.skolem₁).Structure M]
    [(FirstOrder.Language.LHom.sumInl : L →ᴸ L.sum L.skolem₁).IsExpansionOn M]
    (hM : M ⊨ skolemTheory L) {I : Type} [LinearOrder I] (a : I → M) :
    (EMOf hM a : Set M) = (EMSub L a : Set M) := rfl

end SkolemTheory

/-! ## Existence of Ehrenfeucht–Mostowski models -/

section Existence

variable {L : FirstOrder.Language.{0, 0}}

/-- The `L.sum L.skolem₁`-theory whose models are Skolemised models of `T`. -/
def emTheory (L : FirstOrder.Language.{0, 0}) (T : L.Theory) : (L.sum L.skolem₁).Theory :=
  FirstOrder.Language.LHom.sumInl.onTheory T ∪ skolemTheory L

/-- Bundled Ehrenfeucht–Mostowski data: a Skolemised model of `T` together with an
order-indiscernible `I`-indexed sequence in it. -/
structure EMData (L : FirstOrder.Language.{0, 0}) (T : L.Theory) (I : Type) [LinearOrder I] where
  /-- The ambient model. -/
  Carrier : Type
  [str : L.Structure Carrier]
  [strSkolem : (L.sum L.skolem₁).Structure Carrier]
  [expansion :
    (FirstOrder.Language.LHom.sumInl : L →ᴸ L.sum L.skolem₁).IsExpansionOn Carrier]
  [nonempty : Nonempty Carrier]
  [model : Carrier ⊨ T]
  /-- The Skolem function symbols really are interpreted by Skolem functions. -/
  skolem : Carrier ⊨ skolemTheory L
  /-- The indiscernible sequence. -/
  seq : I → Carrier
  /-- The sequence is order indiscernible for the Skolem language. -/
  indiscernible : IsOrderIndiscernible (L.sum L.skolem₁) seq

attribute [instance] EMData.str EMData.strSkolem EMData.expansion EMData.nonempty EMData.model

namespace EMData

variable {T : L.Theory} {I : Type} [LinearOrder I] (d : EMData L T I)

/-- The Ehrenfeucht–Mostowski model `EM(I)`: the Skolem hull of the indiscernible sequence.
It is an elementary `L`-substructure of the ambient model. -/
noncomputable def toEM : L.ElementarySubstructure d.Carrier := EMOf d.skolem d.seq

theorem coe_toEM : (d.toEM : Set d.Carrier) = (EMSub L d.seq : Set d.Carrier) := rfl

/-- `EM(I) ⊨ T`. -/
theorem toEM_model : (d.toEM : Type) ⊨ T := inferInstance

/-- `#EM(I) ≤ #I + ℵ₀`. -/
theorem card_toEM_le (hL : L.card ≤ ℵ₀) : #(d.toEM) ≤ max ℵ₀ #I := card_EMSub_le hL d.seq

/-- The type-counting property of `EM(I)`. -/
theorem card_realizedTypes_le [WellFoundedLT I] (hL : L.card ≤ ℵ₀) {A : Set d.Carrier}
    (hA : A ⊆ (d.toEM : Set d.Carrier)) {μ : Cardinal.{0}} (hAμ : #A ≤ μ) (hμ : ℵ₀ ≤ μ) :
    #(emTypeOver L A '' (d.toEM : Set d.Carrier)) ≤ μ :=
  Submission.Morley.card_realizedTypes_le hL d.indiscernible hA hAμ hμ

end EMData

/-- **Existence of Ehrenfeucht–Mostowski models.**  Given the Ramsey chapter's
`IndiscerniblesExist` for the Skolem language `L.sum L.skolem₁`, every satisfiable `L`-theory
all of whose models are infinite admits, for every linear order `I`, Ehrenfeucht–Mostowski data
over `I`; the resulting model `EM(I)` satisfies `T` and has cardinality at most `#I + ℵ₀`. -/
theorem nonempty_EMData (hInd : IndiscerniblesExist (L.sum L.skolem₁)) (T : L.Theory)
    (hT : T.IsSatisfiable)
    (hInf : ∀ N : FirstOrder.Language.Theory.ModelType.{0, 0, 0} T, Infinite N)
    (I : Type) [LinearOrder I] : Nonempty (EMData L T I) := by
  have hsat : (emTheory L T).IsSatisfiable := by
    obtain ⟨M⟩ := hT
    have h1 : (M : Type) ⊨ FirstOrder.Language.LHom.sumInl.onTheory T :=
      (LHom.onTheory_model (FirstOrder.Language.LHom.sumInl : L →ᴸ L.sum L.skolem₁) T).2
        inferInstance
    have h2 : (M : Type) ⊨ skolemTheory L := model_skolemTheory L (M : Type)
    haveI h3 : (M : Type) ⊨ emTheory L T := Theory.model_union_iff.2 ⟨h1, h2⟩
    exact Theory.Model.isSatisfiable (M : Type)
  have hinf : ∀ N : FirstOrder.Language.Theory.ModelType.{0, 0, 0} (emTheory L T),
      Infinite N := by
    intro N
    letI : L.Structure (N : Type) :=
      (FirstOrder.Language.LHom.sumInl : L →ᴸ L.sum L.skolem₁).reduct (N : Type)
    have hN : (N : Type) ⊨ emTheory L T := inferInstance
    haveI : (N : Type) ⊨ T :=
      (LHom.onTheory_model (FirstOrder.Language.LHom.sumInl : L →ᴸ L.sum L.skolem₁) T).1
        (Theory.model_union_iff.1 hN).1
    exact hInf (FirstOrder.Language.Theory.ModelType.of T (N : Type))
  obtain ⟨N, a, ha⟩ := hInd (emTheory L T) hsat hinf I
  letI : L.Structure (N : Type) :=
      (FirstOrder.Language.LHom.sumInl : L →ᴸ L.sum L.skolem₁).reduct (N : Type)
  have hN : (N : Type) ⊨ emTheory L T := inferInstance
  haveI : (N : Type) ⊨ T :=
    (LHom.onTheory_model (FirstOrder.Language.LHom.sumInl : L →ᴸ L.sum L.skolem₁) T).1
      (Theory.model_union_iff.1 hN).1
  exact ⟨{ Carrier := (N : Type)
           skolem := (Theory.model_union_iff.1 hN).2
           seq := a
           indiscernible := ha }⟩

end Existence

end Submission.Morley
