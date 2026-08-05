import Mathlib
import Submission.Morley.Prime
import Submission.Morley.Stable

/-!
# Density of the isolated types, and existence of prime models

This file closes the two gaps left open by `Submission/Morley/Prime.lean`.
-/

universe u v w w'

open Cardinal Set FirstOrder Language Theory Theory.CompleteType

namespace Submission.Morley

/-! ## Consistency over a parameter set is realisation in the model -/

section Realization

variable {L : FirstOrder.Language.{u, v}} {M : Type w} [L.Structure M] [Nonempty M] {A : Set M}
variable {α : Type w'}

/-- A formula with parameters in `A` is consistent with `Th(M_A)` -- that is, the basic clopen set
it determines in the space of complete types over `A` is nonempty -- exactly when it is realised
in `M` itself. -/
theorem nonempty_typesWith_iff (φ : (L[[A]]).Formula α) :
    ((paramTheory L A).typesWith (Formula.equivSentence φ)).Nonempty ↔
      ∃ v : α → M, φ.Realize v := by
  constructor
  · rintro ⟨p, hp⟩
    obtain ⟨K, v, hv⟩ := Theory.exists_modelType_is_realized_in (paramTheory L A) p
    have hmem : Formula.equivSentence φ ∈ (paramTheory L A).typeOf v := by
      rw [hv]; exact (CompleteType.mem_typesWith_iff _ _).1 hp
    have hφv : φ.Realize v := CompleteType.formula_mem_typeOf.1 hmem
    exact (completeTheory.isComplete (L := L[[A]]) M).exists_realize_of_isComplete v φ hφv M
  · rintro ⟨v, hv⟩
    exact ⟨(paramTheory L A).typeOf v,
      (CompleteType.mem_typesWith_iff _ _).2 (CompleteType.formula_mem_typeOf.2 hv)⟩

/-- If one formula over `A` implies another in `M`, then the corresponding basic clopen sets are
nested. -/
theorem typesWith_subset_of_realize_imp {φ ψ : (L[[A]]).Formula α}
    (h : ∀ v : α → M, φ.Realize v → ψ.Realize v) :
    (paramTheory L A).typesWith (Formula.equivSentence φ) ⊆
      (paramTheory L A).typesWith (Formula.equivSentence ψ) := by
  intro p hp
  by_contra hq
  have h1 : Formula.equivSentence (φ ⊓ ∼ψ) ∈ p := by
    rw [Formula.equivSentence_inf, CompleteType.inf_mem_iff]
    refine ⟨(CompleteType.mem_typesWith_iff _ _).1 hp, ?_⟩
    rw [Formula.equivSentence_not]
    exact (CompleteType.not_mem_iff p _).2
      fun hc => hq ((CompleteType.mem_typesWith_iff _ _).2 hc)
  obtain ⟨v, hv⟩ := (nonempty_typesWith_iff (φ ⊓ ∼ψ)).1
    ⟨p, (CompleteType.mem_typesWith_iff _ _).2 h1⟩
  rw [Formula.realize_inf, Formula.realize_not] at hv
  exact hv.2 (h v hv.1)

/-- Conversely, nested basic clopen sets mean the corresponding implication holds in `M`. -/
theorem realize_imp_of_typesWith_subset {φ ψ : (L[[A]]).Formula α}
    (h : (paramTheory L A).typesWith (Formula.equivSentence φ) ⊆
      (paramTheory L A).typesWith (Formula.equivSentence ψ)) :
    ∀ v : α → M, φ.Realize v → ψ.Realize v := by
  intro v hv
  exact CompleteType.formula_mem_typeOf.1 ((CompleteType.mem_typesWith_iff _ _).1
    (h ((CompleteType.mem_typesWith_iff _ _).2 (CompleteType.formula_mem_typeOf.2 hv))))

/-- Two formulas over `A` with no common realisation in `M` determine disjoint basic clopen
sets. -/
theorem typesWith_disjoint_of_not_realize {φ ψ : (L[[A]]).Formula α}
    (h : ∀ v : α → M, ¬(φ.Realize v ∧ ψ.Realize v)) :
    Disjoint ((paramTheory L A).typesWith (Formula.equivSentence φ))
      ((paramTheory L A).typesWith (Formula.equivSentence ψ)) := by
  rw [Set.disjoint_iff_inter_eq_empty, ← CompleteType.typesWith_inf,
    ← Formula.equivSentence_inf, ← Set.not_nonempty_iff_eq_empty]
  intro hne
  obtain ⟨v, hv⟩ := (nonempty_typesWith_iff (φ ⊓ ψ)).1 hne
  rw [Formula.realize_inf] at hv
  exact h v hv

/-- Conversely, disjoint basic clopen sets mean the two formulas have no common realisation. -/
theorem not_realize_of_typesWith_disjoint {φ ψ : (L[[A]]).Formula α}
    (h : Disjoint ((paramTheory L A).typesWith (Formula.equivSentence φ))
      ((paramTheory L A).typesWith (Formula.equivSentence ψ))) :
    ∀ v : α → M, ¬(φ.Realize v ∧ ψ.Realize v) := by
  rintro v ⟨h1, h2⟩
  exact Set.disjoint_left.1 h
    ((CompleteType.mem_typesWith_iff _ _).2 (CompleteType.formula_mem_typeOf.2 h1))
    ((CompleteType.mem_typesWith_iff _ _).2 (CompleteType.formula_mem_typeOf.2 h2))

end Realization

/-! ## Restricting the parameters of a formula -/

section Params

variable {L : FirstOrder.Language.{u, v}} {M : Type w} [L.Structure M]

/-- A parameter-free formula in one free variable together with a tuple of parameters from `B`
determines a formula of `L[[B]]` in one free variable, realised exactly where the substitution
instance is. -/
theorem exists_formula_of_params {B : Set M} {n : ℕ} (χ : L.Formula (Fin 1 ⊕ Fin n))
    (c : Fin n → B) :
    ∃ θ : (L[[B]]).Formula (Fin 1), ∀ v : Fin 1 → M,
      θ.Realize v ↔ χ.Realize (Sum.elim v fun i => ((c i : M))) := by
  classical
  refine ⟨BoundedFormula.constantsVarsEquiv.symm
    (χ.relabel (Sum.elim Sum.inr fun i => Sum.inl (c i))), fun v => ?_⟩
  have h := BoundedFormula.realize_constantsVarsEquiv (M := M) (L := L) (α := B) (β := Fin 1)
    (n := 0) (φ := BoundedFormula.constantsVarsEquiv.symm
      (χ.relabel (Sum.elim Sum.inr fun i => Sum.inl (c i)))) (v := v) (xs := default)
  rw [Equiv.apply_symm_apply] at h
  refine h.symm.trans ?_
  show Formula.Realize (χ.relabel (Sum.elim Sum.inr fun i => Sum.inl (c i)))
    (Sum.elim (fun a : B => ((a : M))) v) ↔ _
  rw [Formula.realize_relabel,
    show (Sum.elim (fun a : B => ((a : M))) v) ∘ (Sum.elim Sum.inr fun i => Sum.inl (c i)) =
      Sum.elim v fun i => ((c i : M)) from by funext x; rcases x with j | i <;> rfl]

end Params

/-! ## Density of the isolated types from ω-stability -/

section Dense

variable {L : FirstOrder.Language.{u, v}} {M : Type w} [L.Structure M] {A : Set M}

/-- If the isolated types are not dense in the space of complete `1`-types over `A`, then some
basic clopen set of that space is nonempty and contains no isolated type. -/
theorem exists_typesWith_not_isIsolated (h : ¬ IsolatedDenseOn L M A) :
    ∃ σ : ((L[[A]])[[Fin 1]]).Sentence, ((paramTheory L A).typesWith σ).Nonempty ∧
      ∀ p ∈ (paramTheory L A).typesWith σ, ¬ p.IsIsolated := by
  by_contra hcon
  push Not at hcon
  refine h ?_
  rw [IsolatedDenseOn, CompleteType.isTopologicalBasis_range_typesWith.dense_iff]
  rintro o ⟨σ, rfl⟩ hne
  obtain ⟨p, hp, hiso⟩ := hcon σ hne
  exact ⟨p, hp, hiso⟩

/-- **Failure of density produces a binary tree.**  If the isolated types are not dense in the
space of complete `1`-types over `A`, then the non-isolated part contains a nonempty basic clopen
set, and the Cantor--Bendixson splitting of `CompleteType.exists_isolated_splitting` builds a full
binary tree of formulas over `A` inside it. -/
theorem nonempty_binaryTree_of_not_isolatedDenseOn (h : ¬ IsolatedDenseOn L M A) :
    Nonempty (BinaryTree (paramTheory L A) (Fin 1)) := by
  obtain ⟨σ, hne, hni⟩ := exists_typesWith_not_isIsolated h
  obtain ⟨g, hP, hmono, hdisj⟩ := exists_dyadic (paramTheory L A).typesWith
    (fun τ => ((paramTheory L A).typesWith τ).Nonempty ∧
      ∀ p ∈ (paramTheory L A).typesWith τ, ¬ p.IsIsolated) ⟨σ, hne, hni⟩
    (by
      rintro τ ⟨hτ1, hτ2⟩
      obtain ⟨χ, h1, h2, h3, h4⟩ := CompleteType.exists_isolated_splitting τ hτ1 hτ2
      refine ⟨τ ⊓ χ, τ ⊓ ∼χ, ?_, ?_, ?_, ⟨h1, h3⟩, ⟨h2, h4⟩⟩
      · rw [CompleteType.typesWith_inf]; exact Set.inter_subset_left
      · rw [CompleteType.typesWith_inf]; exact Set.inter_subset_left
      · rw [CompleteType.typesWith_inf, CompleteType.typesWith_inf, CompleteType.typesWith_not]
        exact Set.disjoint_left.2 fun x hx hx' => hx'.2 hx.2)
  exact ⟨⟨g, fun s => (hP s).1, hmono, hdisj⟩⟩

variable [Nonempty M]

/-- **The parameters of a binary tree can be taken countable.**  A binary tree of formulas over
`A` has countably many nodes, each mentioning finitely many parameters, so the whole tree lives
over a countable subset `A₀ ⊆ A`; consistency, implication and contradiction of the nodes are all
equivalent to statements about realisation in `M`, so they transfer to `A₀`. -/
theorem exists_binaryTree_countable_subset (t : BinaryTree (paramTheory L A) (Fin 1)) :
    ∃ A₀ : Set M, A₀ ⊆ A ∧ A₀.Countable ∧
      Nonempty (BinaryTree (paramTheory L A₀) (Fin 1)) := by
  classical
  set F : List Bool → (L[[A]]).Formula (Fin 1) :=
    fun s => Formula.equivSentence.symm (t.form s) with hFdef
  have hF : ∀ s, Formula.equivSentence (F s) = t.form s :=
    fun s => Equiv.apply_symm_apply _ _
  choose nn bb ψψ hψψ using fun s : List Bool => Formula.exists_fin_params (F s)
  set A₀ : Set M := ⋃ s : List Bool, Set.range (fun i : Fin (nn s) => ((bb s i : M))) with hA₀
  have hmem : ∀ (s : List Bool) (i : Fin (nn s)), ((bb s i : M)) ∈ A₀ := by
    intro s i
    rw [hA₀]
    exact Set.mem_iUnion.2 ⟨s, ⟨i, rfl⟩⟩
  choose θ hθ using fun s : List Bool =>
    exists_formula_of_params (B := A₀) (ψψ s) (fun i => (⟨((bb s i : M)), hmem s i⟩ : A₀))
  have key : ∀ (s : List Bool) (v : Fin 1 → M), (θ s).Realize v ↔ (F s).Realize v := by
    intro s v
    rw [hθ s v, hψψ s v]
  refine ⟨A₀, ?_, ?_, ⟨⟨fun s => Formula.equivSentence (θ s), ?_, ?_, ?_⟩⟩⟩
  · rw [hA₀]
    exact Set.iUnion_subset fun s => by rintro _ ⟨i, rfl⟩; exact (bb s i).2
  · rw [hA₀]
    exact Set.countable_iUnion fun s => Set.countable_range _
  · intro s
    refine (nonempty_typesWith_iff (θ s)).2 ?_
    obtain ⟨v, hv⟩ := (nonempty_typesWith_iff (F s)).1 (by rw [hF s]; exact t.consistent s)
    exact ⟨v, (key s v).2 hv⟩
  · intro b s
    refine typesWith_subset_of_realize_imp fun v hv => ?_
    refine (key s v).2 (realize_imp_of_typesWith_subset ?_ v ((key (b :: s) v).1 hv))
    rw [hF, hF]
    exact t.mono b s
  · intro s
    refine typesWith_disjoint_of_not_realize fun v hv => ?_
    refine not_realize_of_typesWith_disjoint (φ := F (false :: s)) (ψ := F (true :: s)) ?_ v
      ⟨(key _ v).1 hv.1, (key _ v).1 hv.2⟩
    rw [hF, hF]
    exact t.disjoint s

end Dense

/-! ## Isolated types are dense in an ω-stable theory -/

section Density

/-- **The isolated types are dense in an `ω`-stable theory.**

If the isolated types failed to be dense in some space `S₁(A)`, the non-isolated part would
contain a nonempty basic clopen set; the Cantor--Bendixson splitting inside it produces a full
binary tree of formulas over `A`, whose countably many nodes mention only countably many
parameters, so the tree may be taken over a countable subset `A₀ ⊆ A`.  A binary tree of formulas
over a countable parameter set gives `2 ^ ℵ₀` complete `1`-types there, contradicting
`ω`-stability. -/
theorem isolatedDense_of_isOmegaStable {L : FirstOrder.Language.{0, 0}} {T : L.Theory}
    (_hL : L.card ≤ ℵ₀) (h : IsOmegaStable.{0, 0, 0} T) : IsolatedDense.{0, 0, 0} T := by
  intro M A
  by_contra hnd
  obtain ⟨t⟩ := nonempty_binaryTree_of_not_isolatedDenseOn hnd
  obtain ⟨A₀, -, hA₀c, ⟨t₀⟩⟩ := exists_binaryTree_countable_subset t
  exact not_isOmegaStable_of_binaryTree M A₀ hA₀c 1 le_rfl t₀ h

end Density

/-! ## Two closure properties of isolation -/

section IsolationLemmas

variable {L : FirstOrder.Language.{u, v}} {M : Type w} [L.Structure M] [Nonempty M]

/-- **Isolation is preserved by reindexing.**  If a tuple has isolated type then so does every
tuple obtained from it by repeating and dropping coordinates. -/
theorem isIsolated_typeOf_comp {T : L.Theory} [M ⊨ T] (hT : T.IsComplete) {α : Type}
    [Finite α] {β : Type} (v : β → M) (f : α → β) (h : (T.typeOf v).IsIsolated) :
    (T.typeOf (v ∘ f)).IsIsolated := by
  classical
  rw [CompleteType.isIsolated_typeOf_iff_of_isComplete hT] at h ⊢
  obtain ⟨φ, hφv, hφu⟩ := h
  refine ⟨((Formula.relabel Sum.inr φ ⊓
      Formula.iInf fun j : α =>
        Term.equal (Term.var (Sum.inl j)) (Term.var (Sum.inr (f j))) :
      L.Formula (α ⊕ β))).existsRight, ?_, ?_⟩
  · rw [Formula.realize_existsRight]
    refine ⟨v, ?_⟩
    rw [Formula.realize_inf, Formula.realize_relabel, Formula.realize_iInf]
    exact ⟨hφv, fun j => by simp⟩
  · intro b hb
    rw [Formula.realize_existsRight] at hb
    obtain ⟨y, hy⟩ := hb
    rw [Formula.realize_inf, Formula.realize_relabel, Formula.realize_iInf] at hy
    have hby : b = y ∘ f := by
      funext j
      have hj := hy.2 j
      rw [Formula.realize_equal] at hj
      simpa using hj
    rw [hby]
    exact CompleteType.typeOf_comp_eq_of_typeOf_eq f y v (hφu y hy.1)

variable {B : Set M}

/-- Two tuples with the same type over `B` still have the same type after the same tuple of
parameters from `B` is prefixed. -/
theorem typeOf_sum_congr {m : ℕ} {β : Type} (d : Fin m → B) {y z : β → M}
    (h : ((L[[B]]).completeTheory M).typeOf z = ((L[[B]]).completeTheory M).typeOf y) :
    ((L[[B]]).completeTheory M).typeOf (Sum.elim (fun i => ((d i : M))) z) =
      ((L[[B]]).completeTheory M).typeOf (Sum.elim (fun i => ((d i : M))) y) := by
  classical
  refine CompleteType.typeOf_eq_of_realize_imp _ _ fun θ hθ => ?_
  have hsubst : ∀ w : β → M,
      Formula.Realize (θ.subst (Sum.elim (fun i => (L.con (d i)).term) fun j => Term.var j)) w ↔
        θ.Realize (Sum.elim (fun i => ((d i : M))) w) := by
    intro w
    have hfun : (fun a : Fin m ⊕ β => Term.realize w
        (Sum.elim (fun i : Fin m => (L.con (d i)).term) (fun j : β => Term.var j) a)) =
        Sum.elim (fun i => ((d i : M))) w := by
      funext x
      rcases x with i | j
      · simp
      · rfl
    simp only [Formula.Realize, BoundedFormula.realize_subst, hfun]
  rw [← hsubst z] at hθ
  rw [← hsubst y]
  exact (CompleteType.realize_iff_of_typeOf_eq z y h _).1 hθ

/-- **The mixed-tuple isolation lemma.**  A tuple of parameters from `B` followed by a tuple whose
type over `B` is isolated has isolated type over `B`. -/
theorem isIsolated_typeOf_sum_of_mem {m : ℕ} {β : Type} (d : Fin m → B) {y : β → M}
    (hy : (((L[[B]]).completeTheory M).typeOf y).IsIsolated) :
    (((L[[B]]).completeTheory M).typeOf (Sum.elim (fun i => ((d i : M))) y)).IsIsolated := by
  classical
  have hT : ((L[[B]]).completeTheory M).IsComplete := completeTheory.isComplete (L := L[[B]]) M
  rw [CompleteType.isIsolated_typeOf_iff_of_isComplete hT] at hy ⊢
  obtain ⟨ψ, hψy, hψu⟩ := hy
  refine ⟨(Formula.iInf fun i : Fin m =>
      Term.equal (Term.var (Sum.inl i)) (L.con (d i)).term) ⊓ ψ.relabel Sum.inr, ?_, ?_⟩
  · rw [Formula.realize_inf, Formula.realize_iInf, Formula.realize_relabel]
    exact ⟨fun i => by simp, hψy⟩
  · intro u hu
    rw [Formula.realize_inf, Formula.realize_iInf, Formula.realize_relabel] at hu
    have hul : ∀ i, u (Sum.inl i) = ((d i : M)) := by
      intro i
      have hi := hu.1 i
      rw [Formula.realize_equal] at hi
      simpa using hi
    have hu' : u = Sum.elim (fun i => ((d i : M))) (u ∘ Sum.inr) := by
      funext x
      rcases x with i | j
      · exact hul i
      · rfl
    rw [hu']
    exact typeOf_sum_congr d (hψu _ hu.2)

end IsolationLemmas

/-! ## Transferring isolation to an elementary substructure -/

section Transfer

variable {L : FirstOrder.Language.{u, v}} {M : Type w} [L.Structure M]

/-- Realising a parameter-free formula at a tuple from an elementary substructure `S` together
with parameters from `A' ⊆ S` gives the same answer in `S` and in `M`. -/
theorem realize_sum_transfer (S : L.ElementarySubstructure M) {A : Set M} {A' : Set S}
    (j : A' → A) (hj : ∀ a : A', ((a : S) : M) = ((j a : M))) {k : ℕ}
    (χ : L.Formula (A' ⊕ Fin k)) (c : Fin k → S) :
    χ.Realize (Sum.elim (fun a : A' => ((a : S))) c) ↔
      (χ.relabel (Sum.map j id)).Realize
        (Sum.elim (fun a : A => ((a : M))) fun i => ((c i : M))) := by
  rw [Formula.realize_relabel,
    show (Sum.elim (fun a : A => ((a : M))) fun i => ((c i : M))) ∘ (Sum.map j id) =
      (fun z => (((Sum.elim (fun a : A' => ((a : S))) c) z : S) : M)) from by
      funext z
      rcases z with a | i
      · exact (hj a).symm
      · rfl]
  exact (S.subtype.map_formula χ (Sum.elim (fun a : A' => ((a : S))) c)).symm

variable (S : L.ElementarySubstructure M) {A : Set M} {A' : Set S}

/-- A formula with parameters in `A ⊆ M` can be pulled back to a formula with parameters in the
copy `A'` of `A` inside an elementary substructure `S`. -/
theorem exists_formula_down (e : A' ≃ A) (he : ∀ a : A', ((a : S) : M) = ((e a : M))) {k : ℕ}
    (φ : (L[[A]]).Formula (Fin k)) :
    ∃ θ : (L[[A']]).Formula (Fin k), ∀ c : Fin k → S,
      θ.Realize c ↔ φ.Realize (fun i => ((c i : M))) := by
  classical
  refine ⟨BoundedFormula.constantsVarsEquiv.symm
    (Formula.relabel (Sum.map (⇑e.symm) id) (BoundedFormula.constantsVarsEquiv φ)), fun c => ?_⟩
  have h1 := BoundedFormula.realize_constantsVarsEquiv (M := (S : Type w)) (L := L) (α := A')
    (β := Fin k) (n := 0) (φ := BoundedFormula.constantsVarsEquiv.symm
      (Formula.relabel (Sum.map (⇑e.symm) id) (BoundedFormula.constantsVarsEquiv φ)))
    (v := c) (xs := default)
  rw [Equiv.apply_symm_apply] at h1
  have h2 := realize_sum_transfer S (⇑e) he
    (Formula.relabel (Sum.map (⇑e.symm) id) (BoundedFormula.constantsVarsEquiv φ)) c
  have h3 := BoundedFormula.realize_constantsVarsEquiv (M := M) (L := L) (α := A)
    (β := Fin k) (n := 0) (φ := φ) (v := fun i => ((c i : M))) (xs := default)
  refine h1.symm.trans (h2.trans (Iff.trans ?_ h3))
  rw [Formula.realize_relabel, Formula.realize_relabel,
    show ((Sum.elim (fun a : A => ((a : M))) fun i => ((c i : M))) ∘ (Sum.map (⇑e) id)) ∘
        (Sum.map (⇑e.symm) id) = Sum.elim (fun a : A => ((a : M))) fun i => ((c i : M)) from by
      funext z
      rcases z with a | i
      · simp
      · rfl]
  exact Iff.rfl

/-- A formula with parameters in `A' ⊆ S` can be pushed forward to a formula with parameters in
the image `A` of `A'` in `M`. -/
theorem exists_formula_up (e : A' ≃ A) (he : ∀ a : A', ((a : S) : M) = ((e a : M))) {k : ℕ}
    (θ : (L[[A']]).Formula (Fin k)) :
    ∃ φ : (L[[A]]).Formula (Fin k), ∀ c : Fin k → S,
      θ.Realize c ↔ φ.Realize (fun i => ((c i : M))) := by
  classical
  refine ⟨BoundedFormula.constantsVarsEquiv.symm
    (Formula.relabel (Sum.map (⇑e) id) (BoundedFormula.constantsVarsEquiv θ)), fun c => ?_⟩
  have h1 := BoundedFormula.realize_constantsVarsEquiv (M := (S : Type w)) (L := L) (α := A')
    (β := Fin k) (n := 0) (φ := θ) (v := c) (xs := default)
  have h2 := realize_sum_transfer S (⇑e) he (BoundedFormula.constantsVarsEquiv θ) c
  have h3 := BoundedFormula.realize_constantsVarsEquiv (M := M) (L := L) (α := A)
    (β := Fin k) (n := 0) (φ := BoundedFormula.constantsVarsEquiv.symm
      (Formula.relabel (Sum.map (⇑e) id) (BoundedFormula.constantsVarsEquiv θ)))
    (v := fun i => ((c i : M))) (xs := default)
  rw [Equiv.apply_symm_apply] at h3
  exact h1.symm.trans (h2.trans h3)

variable [Nonempty M]

/-- **Transporting isolation down to an elementary substructure.**  If a tuple of elements of an
elementary substructure `S ≼ M` has isolated type over `A ⊆ S` computed in `M`, then it has
isolated type over the copy of `A` inside `S`, computed in `S`. -/
theorem isIsolated_typeOf_of_elementarySubstructure (e : A' ≃ A)
    (he : ∀ a : A', ((a : S) : M) = ((e a : M))) {k : ℕ} (x : Fin k → S)
    (h : (((L[[A]]).completeTheory M).typeOf fun i => ((x i : M))).IsIsolated) :
    (((L[[A']]).completeTheory (S : Type w)).typeOf x).IsIsolated := by
  classical
  rw [CompleteType.isIsolated_typeOf_iff_of_isComplete
    (completeTheory.isComplete (L := L[[A]]) M)] at h
  rw [CompleteType.isIsolated_typeOf_iff_of_isComplete
    (completeTheory.isComplete (L := L[[A']]) (S : Type w))]
  obtain ⟨φ, hφx, hφu⟩ := h
  obtain ⟨θ, hθ⟩ := exists_formula_down S e he φ
  refine ⟨θ, (hθ x).2 hφx, fun c hc => ?_⟩
  have hMc : ((L[[A]]).completeTheory M).typeOf (fun i => ((c i : M))) =
      ((L[[A]]).completeTheory M).typeOf (fun i => ((x i : M))) := hφu _ ((hθ c).1 hc)
  refine CompleteType.typeOf_eq_of_realize_imp _ _ fun ξ hξ => ?_
  obtain ⟨ξ', hξ'⟩ := exists_formula_up S e he ξ
  exact (hξ' x).2 ((CompleteType.realize_iff_of_typeOf_eq _ _ hMc ξ').1 ((hξ' c).1 hξ))

end Transfer

/-! ## A recursion principle for sequences -/

section Recursion

variable {X : Type*}

/-- Pad a finite tuple to an infinite sequence with a fixed junk value. -/
private def padSeq (m₀ : X) {n : ℕ} (x : Fin n → X) : ℕ → X :=
  fun i => if h : i < n then x ⟨i, h⟩ else m₀

private theorem padSeq_apply (m₀ : X) {n : ℕ} (x : Fin n → X) {i : ℕ} (hi : i < n) :
    padSeq m₀ x i = x ⟨i, hi⟩ := by
  simp [padSeq, hi]

/-- Build a sequence from a one-step extension property. -/
private theorem exists_seq_of_snoc (P : ∀ n : ℕ, (Fin n → X) → Prop) (h0 : P 0 Fin.elim0)
    (hstep : ∀ (n : ℕ) (x : Fin n → X), P n x → ∃ b : X, P (n + 1) (Fin.snoc x b)) :
    ∃ c : ℕ → X, ∀ n : ℕ, P n fun i : Fin n => c i := by
  classical
  let F : ∀ n : ℕ, { x : Fin n → X // P n x } := fun n =>
    Nat.rec (motive := fun n => { x : Fin n → X // P n x }) ⟨Fin.elim0, h0⟩
      (fun k ih => ⟨Fin.snoc ih.1 (hstep k ih.1 ih.2).choose, (hstep k ih.1 ih.2).choose_spec⟩) n
  have hsucc : ∀ k : ℕ, (F (k + 1)).1 = Fin.snoc (F k).1 (hstep k (F k).1 (F k).2).choose :=
    fun _ => rfl
  refine ⟨fun n => (F (n + 1)).1 (Fin.last n), fun n => ?_⟩
  have key : ∀ n : ℕ, ∀ i : Fin n, (F n).1 i = (F ((i : ℕ) + 1)).1 (Fin.last (i : ℕ)) := by
    intro n
    induction n with
    | zero => exact fun i => i.elim0
    | succ k ih =>
      intro i
      induction i using Fin.lastCases with
      | last => rfl
      | cast j =>
        rw [hsucc k, Fin.snoc_castSucc]
        simpa using ih j
  have heq : (fun i : Fin n => (F ((i : ℕ) + 1)).1 (Fin.last (i : ℕ))) = (F n).1 :=
    funext fun i => (key n i).symm
  exact heq ▸ (F n).2

/-- **Recursion for sequences.**  If `F j u b` depends on `u` only through its first `j` values,
and for every stage `j` and every sequence `u` some `b` satisfies `F j u b`, then there is a
sequence `v` with `F j v (v j)` for every `j`. -/
theorem exists_seq_of_step [Nonempty X] (F : ℕ → (ℕ → X) → X → Prop)
    (hF : ∀ (j : ℕ) (u u' : ℕ → X), (∀ i, i < j → u i = u' i) → ∀ b, F j u b → F j u' b)
    (hstep : ∀ (j : ℕ) (u : ℕ → X), ∃ b, F j u b) :
    ∃ v : ℕ → X, ∀ j, F j v (v j) := by
  classical
  obtain ⟨m₀⟩ := ‹Nonempty X›
  obtain ⟨c, hc⟩ := exists_seq_of_snoc
    (fun n x => ∀ (j : ℕ) (hj : j < n), F j (padSeq m₀ x) (x ⟨j, hj⟩))
    (fun j hj => absurd hj (Nat.not_lt_zero j))
    (by
      intro n x hx
      obtain ⟨b, hb⟩ := hstep n (padSeq m₀ x)
      have hagree : ∀ i, i < n → padSeq m₀ x i = padSeq m₀ (Fin.snoc x b) i := by
        intro i hi
        rw [padSeq_apply m₀ x hi, padSeq_apply m₀ (Fin.snoc x b) (hi.trans (Nat.lt_succ_self n)),
          show (⟨i, hi.trans (Nat.lt_succ_self n)⟩ : Fin (n + 1)) = Fin.castSucc ⟨i, hi⟩ from rfl,
          Fin.snoc_castSucc]
      refine ⟨b, fun j hj => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj' | rfl
      · rw [show (⟨j, hj⟩ : Fin (n + 1)) = Fin.castSucc ⟨j, hj'⟩ from rfl, Fin.snoc_castSucc]
        exact hF j _ _ (fun i hi => hagree i (hi.trans hj')) _ (hx j hj')
      · rw [show (⟨j, hj⟩ : Fin (j + 1)) = Fin.last j from rfl, Fin.snoc_last]
        exact hF j _ _ hagree _ hb)
  refine ⟨c, fun j => ?_⟩
  exact hF j _ c (fun i hi => padSeq_apply m₀ _ (hi.trans (Nat.lt_succ_self j))) _
    (hc (j + 1) j (Nat.lt_succ_self j))

end Recursion

/-! ## The constructible countable elementary submodel -/

section PrimeExistence

/-- The tasks of the construction: a parameter-free formula in one free variable with `n`
parameter slots, each slot named either by an index into a fixed enumeration of the parameter set
`A` or by an index into the sequence of elements constructed so far. -/
abbrev ConstructionTask (L : FirstOrder.Language.{0, 0}) : Type :=
  Σ n : ℕ, L.Formula (Fin 1 ⊕ Fin n) × (Fin n → ℕ ⊕ ℕ)

variable {L : FirstOrder.Language.{0, 0}}

/-- **The constructible elementary submodel.**  If the isolated types are dense over every
parameter set inside `M` and `A ⊆ M` is countable, there is a countable elementary substructure
of `M` containing `A` every finite tuple of which has isolated type over `A`.

The submodel is built one element at a time: at each stage a task is handled, adding a witness of
*isolated* type over the parameters accumulated so far to a formula that is realised in `M`.  The
bookkeeping ensures every task is handled at arbitrarily late stages, so the resulting set meets
every nonempty definable set with parameters in it, hence is an elementary substructure. -/
theorem exists_atomic_elementarySubstructure {M : Type} [L.Structure M] [Nonempty M]
    [Countable L.Symbols] (hd : ∀ B : Set M, IsolatedDenseOn L M B) {A : Set M}
    (hA : A.Countable) :
    ∃ S : L.ElementarySubstructure M, A ⊆ (S : Set M) ∧ (S : Set M).Countable ∧
      ∀ (k : ℕ) (x : Fin k → M), (∀ i, x i ∈ (S : Set M)) →
        (((L[[A]]).completeTheory M).typeOf x).IsIsolated := by
  classical
  haveI : Nonempty (ConstructionTask L) := ⟨⟨0, ⊥, Fin.elim0⟩⟩
  obtain ⟨α, hα⟩ := Set.countable_iff_exists_subset_range.1 hA
  obtain ⟨τ, hτ⟩ := exists_surjective_nat (ConstructionTask L)
  set tsk : ℕ → ConstructionTask L := fun j => τ (Nat.unpair j).1 with htsk
  -- the one-step construction
  have key : ∀ (j : ℕ) (u : ℕ → M) (t : ConstructionTask L), ∃ b : M,
      (((L[[↥(A ∪ u '' {i | i < j})]]).completeTheory M).typeOf fun _ : Fin 1 => b).IsIsolated ∧
      ((∀ i, Sum.elim (fun m => α m ∈ A) (fun m : ℕ => m < j) (t.2.2 i)) →
        (∃ y : M, t.2.1.Realize (Sum.elim (fun _ => y) fun i => Sum.elim α u (t.2.2 i))) →
        t.2.1.Realize (Sum.elim (fun _ => b) fun i => Sum.elim α u (t.2.2 i))) := by
    rintro j u ⟨n, ψ, k⟩
    by_cases hact : (∀ i, Sum.elim (fun m => α m ∈ A) (fun m : ℕ => m < j) (k i)) ∧
        ∃ y : M, ψ.Realize (Sum.elim (fun _ => y) fun i => Sum.elim α u (k i))
    · obtain ⟨hva, y, hy⟩ := hact
      have hmemD : ∀ i, Sum.elim α u (k i) ∈ A ∪ u '' {i | i < j} := by
        intro i
        have hi := hva i
        rcases hki : k i with m | m
        · rw [hki] at hi
          exact Or.inl hi
        · rw [hki] at hi
          exact Or.inr ⟨m, hi, rfl⟩
      obtain ⟨θ, hθ⟩ := exists_formula_of_params (B := A ∪ u '' {i | i < j}) ψ
        fun i => (⟨Sum.elim α u (k i), hmemD i⟩ : ↥(A ∪ u '' {i | i < j}))
      obtain ⟨b, hb1, hb2⟩ := exists_realize_isIsolated_of_isolatedDense
        (hd (A ∪ u '' {i | i < j})) θ (fun _ => y) ((hθ (fun _ => y)).2 hy)
      exact ⟨b, hb2, fun _ _ => (hθ (fun _ => b)).1 hb1⟩
    · obtain ⟨b, -, hb2⟩ := exists_realize_isIsolated_of_isolatedDense
        (hd (A ∪ u '' {i | i < j})) ⊤ (fun _ => Classical.arbitrary M) (by simp)
      exact ⟨b, hb2, fun hva hex => absurd ⟨hva, hex⟩ hact⟩
  obtain ⟨v, hv⟩ := exists_seq_of_step
    (fun j u b =>
      (((L[[↥(A ∪ u '' {i | i < j})]]).completeTheory M).typeOf fun _ : Fin 1 => b).IsIsolated ∧
      ∀ t : ConstructionTask L, tsk j = t →
        (∀ i, Sum.elim (fun m => α m ∈ A) (fun m : ℕ => m < j) (t.2.2 i)) →
        (∃ y : M, t.2.1.Realize (Sum.elim (fun _ => y) fun i => Sum.elim α u (t.2.2 i))) →
        t.2.1.Realize (Sum.elim (fun _ => b) fun i => Sum.elim α u (t.2.2 i)))
    (by
      rintro j u u' huu' b ⟨h1, h2⟩
      have himg : u '' {i | i < j} = u' '' {i | i < j} :=
        Set.image_congr fun i hi => huu' i hi
      have hnmz : ∀ z : ℕ ⊕ ℕ, Sum.elim (fun m => α m ∈ A) (fun m : ℕ => m < j) z →
          Sum.elim α u' z = Sum.elim α u z := by
        rintro (m | m) hz
        · rfl
        · exact (huu' m hz).symm
      refine ⟨himg ▸ h1, fun t htt hva hex => ?_⟩
      have heq : (fun i => Sum.elim α u' (t.2.2 i)) = fun i => Sum.elim α u (t.2.2 i) :=
        funext fun i => hnmz _ (hva i)
      rw [heq]
      exact h2 t htt hva (by rw [← heq]; exact hex))
    (by
      intro j u
      obtain ⟨b, hb1, hb2⟩ := key j u (tsk j)
      exact ⟨b, hb1, fun t htt => htt ▸ hb2⟩)
  -- the set built by the construction
  have hDC : ∀ j : ℕ, A ∪ v '' {i | i < j} ⊆ A ∪ Set.range v :=
    fun j => Set.union_subset_union_right _ (Set.image_subset_range _ _)
  -- every finite tuple from a stage of the construction has isolated type over `A`
  have hatomic : ∀ (j k : ℕ) (x : Fin k → M), (∀ i, x i ∈ A ∪ v '' {i | i < j}) →
      (((L[[A]]).completeTheory M).typeOf x).IsIsolated := by
    intro j
    induction j with
    | zero =>
      intro k x hx
      have hx' : ∀ i, x i ∈ A := by
        intro i
        rcases hx i with h | ⟨m, hm, -⟩
        · exact h
        · exact absurd hm (Nat.not_lt_zero m)
      exact isIsolated_typeOf_of_mem (L := L) (M := M) (A := A) fun i => ⟨x i, hx' i⟩
    | succ j ih =>
      intro k x hx
      set Dj : Set M := A ∪ v '' {i | i < j} with hDj
      have hsub : ∀ i, x i ∈ Dj ∨ x i = v j := by
        intro i
        rcases hx i with h | ⟨m, hm, hmv⟩
        · exact Or.inl (Or.inl h)
        · rcases Nat.lt_succ_iff_lt_or_eq.1 hm with hm' | rfl
          · exact Or.inl (Or.inr ⟨m, hm', hmv⟩)
          · exact Or.inr hmv.symm
      set S : Finset (Fin k) := Finset.univ.filter (fun i => x i ∈ Dj) with hS
      have hmemS : ∀ i : Fin k, i ∈ S ↔ x i ∈ Dj := by
        intro i; simp [hS]
      set d : Fin S.card → ↥Dj :=
        fun r => ⟨x (S.equivFin.symm r), (hmemS _).1 (S.equivFin.symm r).2⟩ with hd'
      set y : (Fin S.card ⊕ Fin 1) → M :=
        Sum.elim (fun r => ((d r : M))) (fun _ => v j) with hy
      set f : Fin k → Fin S.card ⊕ Fin 1 :=
        fun i => if h : x i ∈ Dj then Sum.inl (S.equivFin ⟨i, (hmemS i).2 h⟩) else Sum.inr 0
        with hf
      have hyf : y ∘ f = x := by
        funext i
        by_cases h : x i ∈ Dj
        · simp only [Function.comp_apply, hf, dif_pos h, hy, Sum.elim_inl, hd',
            Equiv.symm_apply_apply]
        · rcases hsub i with h' | h'
          · exact absurd h' h
          · simp only [Function.comp_apply, hf, dif_neg h, hy, Sum.elim_inr]
            exact h'.symm
      have hyj : (((L[[Dj]]).completeTheory M).typeOf y).IsIsolated :=
        isIsolated_typeOf_sum_of_mem d (hv j).1
      have hyA : (((L[[A]]).completeTheory M).typeOf y).IsIsolated := by
        refine CompleteType.isIsolated_typeOf_trans Set.subset_union_left y ?_ hyj
        intro nn bb
        exact ih nn (fun i => ((bb i : M))) fun i => (bb i).2
      rw [← hyf]
      exact isIsolated_typeOf_comp (completeTheory.isComplete (L := L[[A]]) M) y f hyA
  -- the set is closed under witnesses, hence an elementary substructure
  have hmeets : L.MeetsDefinable (A ∪ Set.range v) := by
    rintro D hDne ⟨φ, hφ⟩
    obtain ⟨n, b, ψ, hψ⟩ := Formula.exists_fin_params φ
    have hname : ∀ i : Fin n, ∃ z : ℕ ⊕ ℕ,
        Sum.elim (fun m => α m ∈ A) (fun _ : ℕ => True) z ∧ Sum.elim α v z = ((b i : M)) := by
      intro i
      rcases (b i).2 with hb | ⟨m, hm⟩
      · obtain ⟨m, hm⟩ := hα hb
        exact ⟨Sum.inl m, by show α m ∈ A; rw [hm]; exact hb, hm⟩
      · exact ⟨Sum.inr m, trivial, hm⟩
    choose kk hk1 hk2 using hname
    obtain ⟨p, hp⟩ := hτ ⟨n, ψ, kk⟩
    obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ i : Fin n,
        Sum.elim (fun _ : ℕ => 0) (fun m : ℕ => m + 1) (kk i) ≤ N :=
      ⟨Finset.univ.sup fun i : Fin n =>
        Sum.elim (fun _ : ℕ => 0) (fun m : ℕ => m + 1) (kk i), fun i => Finset.le_sup
          (f := fun i : Fin n => Sum.elim (fun _ : ℕ => 0) (fun m : ℕ => m + 1) (kk i))
          (Finset.mem_univ i)⟩
    have hjtsk : tsk (Nat.pair p N) = ⟨n, ψ, kk⟩ := by
      rw [htsk]; simpa using hp
    have hvalid : ∀ i, Sum.elim (fun m => α m ∈ A) (fun m : ℕ => m < Nat.pair p N) (kk i) := by
      intro i
      have hle := hN i
      have hjN : N ≤ Nat.pair p N := Nat.right_le_pair p N
      have hk1i := hk1 i
      rcases hki : kk i with m | m
      · rw [hki] at hk1i
        exact hk1i
      · rw [hki] at hle
        exact lt_of_lt_of_le hle hjN
    obtain ⟨x0, hx0⟩ := hDne
    have hx0φ : φ.Realize (fun _ => x0) := by
      have hmem : (fun _ : Fin 1 => x0) ∈ {x : Fin 1 → M | x 0 ∈ D} := hx0
      rw [hφ] at hmem
      exact hmem
    have hbk : (fun i => Sum.elim α v (kk i)) = fun i => ((b i : M)) := funext hk2
    have hex : ∃ y : M, ψ.Realize (Sum.elim (fun _ => y) fun i => Sum.elim α v (kk i)) := by
      refine ⟨x0, ?_⟩
      rw [hbk]
      exact (hψ (fun _ => x0)).1 hx0φ
    have hconcl := (hv (Nat.pair p N)).2 ⟨n, ψ, kk⟩ hjtsk hvalid hex
    rw [hbk] at hconcl
    have hvjφ : φ.Realize (fun _ => v (Nat.pair p N)) := (hψ _).2 hconcl
    refine ⟨v (Nat.pair p N), ?_, Or.inr ⟨Nat.pair p N, rfl⟩⟩
    have hmem : (fun _ : Fin 1 => v (Nat.pair p N)) ∈ setOf φ.Realize := hvjφ
    rw [← hφ] at hmem
    exact hmem
  have hcoe : ((hmeets.toElementarySubstructure : L.ElementarySubstructure M) : Set M) =
      A ∪ Set.range v := hmeets.closure_eq_self
  refine ⟨hmeets.toElementarySubstructure, ?_, ?_, ?_⟩
  · rw [hcoe]; exact Set.subset_union_left
  · rw [hcoe]; exact hA.union (Set.countable_range v)
  · intro k x hx
    rw [hcoe] at hx
    have hxj : ∀ i, ∃ j : ℕ, x i ∈ A ∪ v '' {i | i < j} := by
      intro i
      rcases hx i with h | ⟨m, hm⟩
      · exact ⟨0, Or.inl h⟩
      · exact ⟨m + 1, Or.inr ⟨m, Nat.lt_succ_self m, hm⟩⟩
    choose jj hjj using hxj
    obtain ⟨J, hJ⟩ : ∃ J : ℕ, ∀ i : Fin k, jj i ≤ J :=
      ⟨Finset.univ.sup jj, fun i => Finset.le_sup (f := jj) (Finset.mem_univ i)⟩
    refine hatomic J k x fun i => ?_
    rcases hjj i with h | ⟨mm, hmm, hmv⟩
    · exact Or.inl h
    · exact Or.inr ⟨mm, lt_of_lt_of_le hmm (hJ i), hmv⟩

end PrimeExistence

/-! ## Existence of prime models -/

section Prime

variable {L : FirstOrder.Language.{0, 0}}

/-- **Prime models exist over every countable set.**

If the isolated types are dense in every space of complete `1`-types -- which, by
`Submission.Morley.isolatedDense_of_isOmegaStable`, holds in an `ω`-stable theory -- then over
every countable subset `A` of a model `M` of `T` there is a prime model: a countable model `N` of
`T`, an elementary embedding `f : N ↪ₑ[L] M`, and a subset `A'` of `N` carried by `f` onto `A`,
such that `N` is prime over `A'`.

`N` is the *constructible* submodel over `A`: an increasing chain of parameter sets is built
inside `M`, one element at a time, each new element realising an isolated type over the
parameters accumulated so far, while a Tarski--Vaught bookkeeping guarantees the union is an
elementary substructure.  Constructibility implies atomicity, and a countable atomic model is
prime (`Submission.Morley.isPrime_of_isAtomic`). -/
theorem exists_prime_of_isolatedDense {T : L.Theory} (hL : L.card ≤ ℵ₀)
    (h : IsolatedDense.{0, 0, 0} T) (M : T.ModelType.{0, 0, 0}) (A : Set M) (hA : A.Countable) :
    ∃ (N : T.ModelType.{0, 0, 0}) (f : N ↪ₑ[L] M) (A' : Set N),
      (fun x : N => (f x : M)) '' A' = A ∧ Countable N ∧ IsPrime N A' := by
  classical
  haveI : Countable L.Symbols := countable_symbols_of_card_le_aleph0 hL
  obtain ⟨S, hAS, hScount, hatom⟩ :=
    exists_atomic_elementarySubstructure (M := (M : Type)) (fun B => h M B) hA
  haveI hcS : Countable ↥S := hScount.to_subtype
  set A' : Set ↥S := Subtype.val ⁻¹' A with hA'
  let e : ↥A' ≃ ↥A :=
    { toFun := fun a => ⟨((a : ↥S) : M), a.2⟩
      invFun := fun b => ⟨⟨(b : M), hAS b.2⟩, b.2⟩
      left_inv := fun a => Subtype.ext (Subtype.ext rfl)
      right_inv := fun b => Subtype.ext rfl }
  have he : ∀ a : ↥A', ((a : ↥S) : M) = ((e a : M)) := fun _ => rfl
  haveI : Countable ↥(S.toModel T) := hcS
  refine ⟨S.toModel T, S.subtype, A', ?_, inferInstance, ?_⟩
  · show (Subtype.val : ↥S → ↥M) '' (Subtype.val ⁻¹' A) = A
    exact Set.image_preimage_eq_of_subset (by rw [Subtype.range_coe]; exact hAS)
  · refine isPrime_of_isAtomic ?_
    intro k x
    let x' : Fin k → ↥S := x
    exact isIsolated_typeOf_of_elementarySubstructure S e he x'
      (hatom k (fun i => ((x' i : ↥M))) fun i => (x' i).2)

/-- **Prime models exist over every countable set in an `ω`-stable theory.**  Combining
`Submission.Morley.isolatedDense_of_isOmegaStable` with
`Submission.Morley.exists_prime_of_isolatedDense`. -/
theorem exists_prime_of_isOmegaStable {T : L.Theory} (hL : L.card ≤ ℵ₀)
    (hst : IsOmegaStable.{0, 0, 0} T) (M : T.ModelType.{0, 0, 0}) (A : Set M)
    (hA : A.Countable) :
    ∃ (N : T.ModelType.{0, 0, 0}) (f : N ↪ₑ[L] M) (A' : Set N),
      (fun x : N => (f x : M)) '' A' = A ∧ Countable N ∧ IsPrime N A' :=
  exists_prime_of_isolatedDense hL (isolatedDense_of_isOmegaStable hL hst) M A hA

end Prime
