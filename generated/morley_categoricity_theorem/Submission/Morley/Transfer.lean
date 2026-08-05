import Mathlib
import Submission.Morley.Port.All
import Submission.Morley.Stable

/-!
# Stability transfer and categoricity

This file closes the two stability-theoretic gaps in the formalisation of Morley's categoricity
theorem left open by `Submission/Morley/Stable.lean`.

## Main results

* `Submission.Morley.stable_of_omegaStable` (and its `1`-type variant
  `Submission.Morley.stable_of_omegaStable'`): **ω-stable implies `κ`-stable** for every infinite
  `κ`, in a countable language.  Unconditional.
* `Submission.Morley.isOmegaStable_of_categorical` (and its `1`-type variant
  `Submission.Morley.omegaStable_of_categorical`): **`κ`-categorical implies ω-stable**, for a
  complete theory with only infinite models in a countable language and `ℵ₀ < κ`.  This is proved
  *conditionally* on the Ehrenfeucht–Mostowski type-counting bound
  `Submission.Morley.EMTypeBoundAt`, which is taken as an explicit hypothesis.
* `Submission.Morley.stable_of_categorical`: the two combined.

## Implementation

The first result rests on a **syntactic push-down**: a binary tree of formulas over a parameter set
`A` mentions only countably many parameters, so it descends to a countable `A₀ ⊆ A`
(`Submission.Morley.exists_countable_binaryTree`).  The semantic engine making the descent possible
is `Submission.Morley.typesWith_nonempty_iff_exists_realize`, which says that a formula with
parameters in `A` is consistent with `Th(M_A)` exactly when it is realised in `M` itself; this makes
consistency depend only on which parameters actually occur.

The second result rests on two halves.  The half proved here, unconditionally, is
`Submission.Morley.exists_modelType_card_eq_not_fewSeqTypesAt`: if there are uncountably many
`n`-types over a countable parameter set, then in every uncountable cardinal `κ` there is a model of
size `κ` realising uncountably many `n`-types over a countable parameter *sequence*.  It is proved
by compactness (`Submission.Morley.isSatisfiable_typeFamilyTheory`, which realises a whole family of
types at once) followed by upward and downward Löwenheim–Skolem.  The other half, that
Ehrenfeucht–Mostowski models realise few types, is the hypothesis `EMTypeBoundAt`.

The counting invariant `Submission.Morley.FewSeqTypesAt` is phrased with a parameter *sequence*
`b : ℕ → M` rather than a parameter set, because in that form it transports verbatim along
elementary embeddings (`Submission.Morley.FewSeqTypesAt.of_elementaryEmbedding`), which is what
lets categoricity be applied.  `Submission.Morley.fewSeqTypesAt_of_mk_realizedTypes_le` bridges it
back to the usual count of types realised over a countable parameter set.
-/

universe u v w w'

open Cardinal Set FirstOrder Language Theory

namespace Submission.Morley

/-! ## Consistency of a formula with parameters -/

section Key

variable {L : FirstOrder.Language.{u, v}} {M : Type w} [L.Structure M]

theorem exists_realize_iff_models_exClosure [Nonempty M] {α : Type*} [DecidableEq α]
    (φ : (L[[α]]).Sentence) :
    (∃ v : α → M, (Formula.equivSentence.symm φ).Realize v) ↔
      M ⊨ (Formula.equivSentence.symm φ).exClosure := by
  classical
  rw [← Formula.exists_realize_equivSentence_iff_realize_exClosure]
  simp only [Equiv.apply_symm_apply]
  exact exists_congr fun v => Formula.realize_equivSentence_symm M φ v

variable (L) in
/-- **A formula with parameters in `A` is consistent with `Th(M_A)` exactly when it is realised in
`M` itself.**  This is the key semantic tool of this file: it makes consistency of a formula with
parameters in a set `A ⊆ M` a statement about `M`, hence independent of which parameter set
containing the relevant parameters is used. -/
theorem typesWith_nonempty_iff_exists_realize [Nonempty M] (A : Set M) {α : Type*} [DecidableEq α]
    (φ : ((L[[A]])[[α]]).Sentence) :
    ((paramTheory L A).typesWith φ).Nonempty ↔
      ∃ v : α → M, (Formula.equivSentence.symm φ).Realize v := by
  classical
  constructor
  · rintro ⟨p, hp⟩
    by_contra hcon
    push Not at hcon
    have hnot : ¬ M ⊨ (Formula.equivSentence.symm φ).exClosure := by
      rw [← exists_realize_iff_models_exClosure]
      rintro ⟨v, hv⟩
      exact hcon v hv
    -- so the negation of the existential closure is in `paramTheory L A`
    have hmem : ∼((Formula.equivSentence.symm φ).exClosure) ∈ paramTheory L A := by
      simpa [Sentence.Realize] using hnot
    have hmem' : ((L[[A]]).lhomWithConstants α).onSentence
        (∼((Formula.equivSentence.symm φ).exClosure)) ∈ p := p.subset ⟨_, hmem, rfl⟩
    obtain ⟨N⟩ := p.isMaximal.1
    letI : (L[[A]]).Structure N := ((L[[A]]).lhomWithConstants α).reduct N
    have h1 : N ⊨ φ := N.is_model.realize_of_mem _ hp
    have h2 : N ⊨ ((L[[A]]).lhomWithConstants α).onSentence
        (∼((Formula.equivSentence.symm φ).exClosure)) := N.is_model.realize_of_mem _ hmem'
    rw [LHom.realize_onSentence, Sentence.realize_not] at h2
    refine h2 ?_
    rw [← exists_realize_iff_models_exClosure]
    exact ⟨fun a => ((L[[A]]).con a : N),
      (Formula.realize_equivSentence_symm_con (N : Type _) φ).2 h1⟩
  · rintro ⟨v, hv⟩
    exact ⟨typeOver A v, by simpa using hv⟩

end Key

section Descent

variable {L : FirstOrder.Language.{u, v}} {M : Type w} [L.Structure M]

/-- Two sentences, one with parameters in `A₀` and one with parameters in `A`, **agree on `M`**
when they are realised by exactly the same elements of `M`. -/
def SentAgree (A₀ A : Set M) (φ₀ : ((L[[A₀]])[[Fin 1]]).Sentence)
    (φ : ((L[[A]])[[Fin 1]]).Sentence) : Prop :=
  ∀ v : Fin 1 → M, (Formula.equivSentence.symm φ₀).Realize v ↔
    (Formula.equivSentence.symm φ).Realize v

theorem exists_sentAgree {ι : Type*} [Countable ι] (A : Set M)
    (φ : ι → ((L[[A]])[[Fin 1]]).Sentence) :
    ∃ A₀ : Set M, A₀ ⊆ A ∧ A₀.Countable ∧
      ∃ φ₀ : ι → ((L[[A₀]])[[Fin 1]]).Sentence, ∀ i, SentAgree A₀ A (φ₀ i) (φ i) := by
  classical
  set ψ : ι → L.BoundedFormula (A ⊕ Fin 1) 0 := fun i =>
    BoundedFormula.constantsVarsEquiv (Formula.equivSentence.symm (φ i)) with hψ
  set A₀ : Set M := ⋃ i, ((↑) '' ((ψ i).freeVarFinset.toLeft : Set A)) with hA₀
  have hmemA₀ : ∀ (i : ι) (x : A), x ∈ (ψ i).freeVarFinset.toLeft → (x : M) ∈ A₀ := by
    intro i x hx
    exact Set.mem_iUnion.2 ⟨i, ⟨x, hx, rfl⟩⟩
  have hsub : A₀ ⊆ A := by
    rw [hA₀]
    refine Set.iUnion_subset fun i => ?_
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hcount : A₀.Countable :=
    Set.countable_iUnion fun i => (Set.Finite.image _ ((ψ i).freeVarFinset.toLeft.finite_toSet))
      |>.countable
  set g : ∀ i, (ψ i).freeVarFinset → (A₀ ⊕ Fin 1) := fun i z =>
    match hz : z.1 with
    | Sum.inl x => Sum.inl ⟨(x : M), hmemA₀ i x (Finset.mem_toLeft.2 (hz ▸ z.2))⟩
    | Sum.inr w => Sum.inr w with hg
  refine ⟨A₀, hsub, hcount, fun i =>
    Formula.equivSentence (BoundedFormula.constantsVarsEquiv.symm
      ((ψ i).restrictFreeVar (g i))), fun i v => ?_⟩
  have e1 : ∀ X : L.BoundedFormula (A₀ ⊕ Fin 1) 0,
      Formula.Realize (BoundedFormula.constantsVarsEquiv.symm X : (L[[A₀]]).Formula (Fin 1)) v ↔
        X.Realize (Sum.elim (fun a : A₀ => (a : M)) v) default := by
    intro X
    have h := BoundedFormula.realize_constantsVarsEquiv (M := M) (L := L) (α := (A₀ : Set M))
      (φ := BoundedFormula.constantsVarsEquiv.symm X) (v := v) (xs := default)
    rw [Equiv.apply_symm_apply] at h
    exact h.symm
  have e2 : Formula.Realize (Formula.equivSentence.symm (φ i)) v ↔
      (ψ i).Realize (Sum.elim (fun a : A => (a : M)) v) default :=
    (BoundedFormula.realize_constantsVarsEquiv (M := M) (L := L) (α := (A : Set M))
      (φ := Formula.equivSentence.symm (φ i)) (v := v) (xs := default)).symm
  simp only [Equiv.symm_apply_apply]
  rw [e1, e2]
  refine BoundedFormula.realize_restrictFreeVar _ ?_
  rintro ⟨z, hz⟩
  cases z <;> simp [hg]

/-! ### Boolean combinations -/

theorem equivSentence_symm_inf {K : FirstOrder.Language.{u, v}} {α : Type*}
    (φ ψ : K[[α]].Sentence) :
    Formula.equivSentence.symm (φ ⊓ ψ) =
      Formula.equivSentence.symm φ ⊓ Formula.equivSentence.symm ψ := rfl

theorem equivSentence_symm_not {K : FirstOrder.Language.{u, v}} {α : Type*}
    (φ : K[[α]].Sentence) :
    Formula.equivSentence.symm (∼φ) = ∼(Formula.equivSentence.symm φ) := rfl

theorem SentAgree.inf {A₀ A : Set M} {φ₀ ψ₀ : ((L[[A₀]])[[Fin 1]]).Sentence}
    {φ ψ : ((L[[A]])[[Fin 1]]).Sentence} (h₁ : SentAgree A₀ A φ₀ φ) (h₂ : SentAgree A₀ A ψ₀ ψ) :
    SentAgree A₀ A (φ₀ ⊓ ψ₀) (φ ⊓ ψ) := by
  intro v
  rw [equivSentence_symm_inf, equivSentence_symm_inf]
  simp only [Formula.realize_inf]
  exact and_congr (h₁ v) (h₂ v)

theorem SentAgree.not {A₀ A : Set M} {φ₀ : ((L[[A₀]])[[Fin 1]]).Sentence}
    {φ : ((L[[A]])[[Fin 1]]).Sentence} (h : SentAgree A₀ A φ₀ φ) :
    SentAgree A₀ A (∼φ₀) (∼φ) := by
  intro v
  rw [equivSentence_symm_not, equivSentence_symm_not]
  simp only [Formula.realize_not]
  exact not_congr (h v)

theorem nonempty_typesWith_congr [Nonempty M] {A₀ A : Set M}
    {φ₀ : ((L[[A₀]])[[Fin 1]]).Sentence} {φ : ((L[[A]])[[Fin 1]]).Sentence}
    (h : SentAgree A₀ A φ₀ φ) :
    ((paramTheory L A₀).typesWith φ₀).Nonempty ↔ ((paramTheory L A).typesWith φ).Nonempty := by
  rw [typesWith_nonempty_iff_exists_realize, typesWith_nonempty_iff_exists_realize]
  exact exists_congr h

end Descent

/-! ### Disjointness and inclusion of basic clopen sets -/

section Clopen

variable {K : FirstOrder.Language.{u, v}} {T : K.Theory} {α : Type*}

theorem typesWith_disjoint_iff_not_nonempty (φ ψ : K[[α]].Sentence) :
    Disjoint (T.typesWith φ) (T.typesWith ψ) ↔ ¬ (T.typesWith (φ ⊓ ψ)).Nonempty := by
  rw [CompleteType.typesWith_inf, Set.not_nonempty_iff_eq_empty, Set.disjoint_iff_inter_eq_empty]

theorem typesWith_subset_iff_not_nonempty (φ ψ : K[[α]].Sentence) :
    T.typesWith φ ⊆ T.typesWith ψ ↔ ¬ (T.typesWith (φ ⊓ ∼ψ)).Nonempty := by
  rw [← typesWith_disjoint_iff_not_nonempty, CompleteType.typesWith_not,
    Set.disjoint_compl_right_iff_subset]

end Clopen

section Transfer

variable {L : FirstOrder.Language.{u, v}} {M : Type w} [L.Structure M] [Nonempty M]

/-- **Descent of a binary tree of formulas to a countable parameter set.**  A binary tree of
formulas over a parameter set `A` only mentions countably many parameters, so it descends to a
binary tree over a countable subset `A₀ ⊆ A`. -/
theorem exists_countable_binaryTree {A : Set M} (t : BinaryTree (paramTheory L A) (Fin 1)) :
    ∃ A₀ : Set M, A₀ ⊆ A ∧ A₀.Countable ∧
      Nonempty (BinaryTree (paramTheory L A₀) (Fin 1)) := by
  obtain ⟨A₀, hsub, hcount, F, hF⟩ := exists_sentAgree A t.form
  refine ⟨A₀, hsub, hcount, ⟨⟨F, fun s => ?_, fun b s => ?_, fun s => ?_⟩⟩⟩
  · rw [nonempty_typesWith_congr (hF s)]
    exact t.consistent s
  · rw [typesWith_subset_iff_not_nonempty,
      nonempty_typesWith_congr ((hF (b :: s)).inf (hF s).not),
      ← typesWith_subset_iff_not_nonempty]
    exact t.mono b s
  · rw [typesWith_disjoint_iff_not_nonempty,
      nonempty_typesWith_congr ((hF (false :: s)).inf (hF (true :: s))),
      ← typesWith_disjoint_iff_not_nonempty]
    exact t.disjoint s

end Transfer

/-! ## Stability transfer -/

section Stability

variable {L : FirstOrder.Language.{0, 0}}

/-- **ω-stability for `1`-types implies `κ`-stability for every infinite `κ`.**

If `κ`-stability failed there would be a binary tree of formulas over a parameter set of size at
most `κ` (`Submission.Morley.exists_binaryTree_of_not_stable`); such a tree only mentions countably
many parameters, so it descends to a countable parameter set
(`Submission.Morley.exists_countable_binaryTree`), contradicting ω-stability
(`Submission.Morley.not_omegaStable_of_binaryTree`). -/
theorem stable_of_omegaStable' {T : L.Theory} (hL : L.card ≤ ℵ₀) (h : OmegaStable.{0, 0, 0} T)
    {κ : Cardinal.{0}} (hκ : ℵ₀ ≤ κ) : Stable κ T := by
  by_contra hns
  obtain ⟨M, A, hA, ⟨t⟩⟩ := exists_binaryTree_of_not_stable hκ (hL.trans hκ) hns
  obtain ⟨A₀, -, hcount, ⟨t₀⟩⟩ := exists_countable_binaryTree t
  exact not_omegaStable_of_binaryTree M A₀
    (Cardinal.mk_le_aleph0_iff.2 (Set.countable_coe_iff.2 hcount)) t₀ h

/-- **ω-stability implies `κ`-stability for every infinite `κ`.**  See
`Submission.Morley.stable_of_omegaStable'` for the version that only assumes ω-stability for
`1`-types. -/
theorem stable_of_omegaStable {T : L.Theory} (hL : L.card ≤ ℵ₀) (h : IsOmegaStable.{0, 0, 0} T)
    {κ : Cardinal.{0}} (hκ : ℵ₀ ≤ κ) : Stable κ T :=
  stable_of_omegaStable' hL h.omegaStable hκ

end Stability

/-! ## Types over a countable parameter sequence

The counting invariant used in the proof that categoricity implies ω-stability is phrased in terms
of a *sequence* `b : ℕ → M` of parameters rather than a parameter set.  The point is that this
formulation transports verbatim along elementary embeddings, which is what makes the categoricity
step work; `Submission.Morley.fewSeqTypes_of_mk_realizedTypes_le` relates it back to the usual
count of realised types over a countable parameter set. -/

section SeqTypes

variable {L : FirstOrder.Language.{u, v}}

/-- `tpSeq b a` is the set of formulas, in parameter variables `ℕ` and object variables `Fin n`,
satisfied by the tuple `a` when the parameter variables are interpreted by the sequence `b`.
It is the "type of `a` over `b`", encoded so as to be independent of the ambient structure. -/
def tpSeq (L : FirstOrder.Language.{u, v}) (M : Type w) [L.Structure M] (n : ℕ) (b : ℕ → M)
    (a : Fin n → M) : Set (L.Formula (ℕ ⊕ Fin n)) :=
  {χ | χ.Realize (Sum.elim b a)}

/-- `FewSeqTypesAt L M n` holds when over every countable parameter sequence the `n`-tuples of `M`
realise only countably many types. -/
def FewSeqTypesAt (L : FirstOrder.Language.{u, v}) (M : Type w) [L.Structure M] (n : ℕ) : Prop :=
  ∀ b : ℕ → M, #(Set.range (tpSeq L M n b)) ≤ ℵ₀

/-- `FewSeqTypes L M` holds when over every countable parameter sequence the tuples of `M` realise
only countably many types, in every finite number of variables. -/
def FewSeqTypes (L : FirstOrder.Language.{u, v}) (M : Type w) [L.Structure M] : Prop :=
  ∀ n : ℕ, FewSeqTypesAt L M n

theorem tpSeq_comp {M : Type w} {N : Type w'} [L.Structure M] [L.Structure N] (e : M ↪ₑ[L] N)
    (n : ℕ) (b : ℕ → M) (a : Fin n → M) :
    tpSeq L N n (⇑e ∘ b) (⇑e ∘ a) = tpSeq L M n b a := by
  ext χ
  simp only [tpSeq, Set.mem_setOf_eq, ← Sum.comp_elim]
  exact e.map_formula χ (Sum.elim b a)

/-- Having few types over countable parameter sequences passes to substructures: if `M`
elementarily embeds into `N` and `N` has few types, so does `M`. -/
theorem FewSeqTypesAt.of_elementaryEmbedding {M : Type w} {N : Type w'} [L.Structure M]
    [L.Structure N] {n : ℕ} (h : FewSeqTypesAt L N n) (e : M ↪ₑ[L] N) : FewSeqTypesAt L M n := by
  intro b
  refine le_trans ?_ (h (⇑e ∘ b))
  refine Cardinal.mk_le_mk_of_subset ?_
  rintro _ ⟨a, rfl⟩
  exact ⟨⇑e ∘ a, tpSeq_comp e n b a⟩

theorem FewSeqTypes.of_elementaryEmbedding {M : Type w} {N : Type w'} [L.Structure M]
    [L.Structure N] (h : FewSeqTypes L N) (e : M ↪ₑ[L] N) : FewSeqTypes L M :=
  fun n => (h n).of_elementaryEmbedding e

variable {M : Type} [L.Structure M] [Nonempty M]

/-- **Few realised types over countable parameter sets implies few types over countable parameter
sequences.**  This is the bridge between the invariant `Submission.Morley.FewSeqTypesAt` and the
usual statement about the spaces `S_n(A)`. -/
theorem fewSeqTypesAt_of_mk_realizedTypes_le (n : ℕ)
    (h : ∀ (A : Set M), #A ≤ ℵ₀ →
      #((paramTheory L A).realizedTypes M (Fin n)) ≤ ℵ₀) :
    FewSeqTypesAt L M n := by
  classical
  intro b
  set A : Set M := Set.range b with hA
  have hAc : #A ≤ ℵ₀ := by
    rw [hA]
    exact (Cardinal.mk_range_le).trans (by simp)
  set β : ℕ → A := fun m => ⟨b m, Set.mem_range_self m⟩ with hβ
  -- transporting a formula in the parameter variables `ℕ` to one with parameters in `A`
  set relab : L.Formula (ℕ ⊕ Fin n) → (L[[A]]).Formula (Fin n) := fun χ =>
    BoundedFormula.constantsVarsEquiv.symm (Formula.relabel (Sum.map β id) χ) with hrelab
  have hrealize : ∀ (χ : L.Formula (ℕ ⊕ Fin n)) (a : Fin n → M),
      (relab χ).Realize a ↔ χ.Realize (Sum.elim b a) := by
    intro χ a
    have h1 : Formula.Realize (relab χ) a ↔
        (Formula.relabel (Sum.map β id) χ).Realize (Sum.elim (fun x : A => (x : M)) a) := by
      have h := BoundedFormula.realize_constantsVarsEquiv (M := M) (L := L) (α := (A : Set M))
        (φ := BoundedFormula.constantsVarsEquiv.symm (Formula.relabel (Sum.map β id) χ))
        (v := a) (xs := default)
      rw [Equiv.apply_symm_apply] at h
      exact h.symm
    rw [h1, Formula.realize_relabel]
    refine iff_of_eq (congrArg _ ?_)
    funext z
    cases z <;> rfl
  -- the type over `A` of a tuple determines its type over `b`
  have hdet : ∀ a a' : Fin n → M,
      (typeOver A a : CompleteTypeOver L A (Fin n)) = typeOver A a' →
      tpSeq L M n b a = tpSeq L M n b a' := by
    intro a a' he
    ext χ
    simp only [tpSeq, Set.mem_setOf_eq]
    rw [← hrealize χ a, ← hrealize χ a', ← formula_mem_typeOver, ← formula_mem_typeOver, he]
  refine le_trans ?_ (h A hAc)
  refine Cardinal.mk_le_of_surjective
    (f := fun q : ((paramTheory L A).realizedTypes M (Fin n)) =>
      (⟨tpSeq L M n b (Classical.choose q.2), ⟨_, rfl⟩⟩ :
        (Set.range (tpSeq L M n b)))) ?_
  rintro ⟨_, a, rfl⟩
  refine ⟨⟨typeOver A a, ⟨a, rfl⟩⟩, ?_⟩
  have hc := Classical.choose_spec
    (⟨a, rfl⟩ : ∃ x, (typeOver A x : CompleteTypeOver L A (Fin n)) = typeOver A a)
  exact Subtype.ext (hdet _ _ hc)

end SeqTypes

/-! ## Realising a family of types simultaneously -/

section Realizing

/-- Reading off the truth value of a sentence with constants that have been renamed along
`g : γ → δ`, in a structure where the `δ`-constants are interpreted by `val`. -/
theorem realize_onSentence_lhomWithConstantsMap {K : FirstOrder.Language.{u, v}} {M : Type w}
    [K.Structure M] {γ δ : Type*} (g : γ → δ) (val : δ → M) (φ : (K[[γ]]).Sentence) :
    letI := constantsOn.structure val
    (M ⊨ (K.lhomWithConstantsMap g).onSentence φ) ↔
      (Formula.equivSentence.symm φ).Realize (val ∘ g) := by
  letI : (constantsOn γ).Structure M := constantsOn.structure (val ∘ g)
  letI : (constantsOn δ).Structure M := constantsOn.structure val
  haveI : (LHom.constantsOnMap g).IsExpansionOn M := constantsOnMap_isExpansionOn rfl
  haveI : (K.lhomWithConstantsMap g).IsExpansionOn M := LHom.sumMap_isExpansionOn _ _ _
  rw [LHom.realize_onSentence]
  exact (Formula.realize_equivSentence_symm M φ (val ∘ g)).symm

variable {L : FirstOrder.Language.{0, 0}} {M : Type} [L.Structure M] [Nonempty M]

variable (L) in
/-- The theory, in the language of `L[[A]]` with an extra block of constants for every index `x`,
which says that the block of constants indexed by `x` realises the type `p x`. -/
def typeFamilyTheory (A : Set M) {n : ℕ} {X : Type} (p : X → CompleteTypeOver L A (Fin n)) :
    ((L[[A]])[[X × Fin n]]).Theory :=
  ((L[[A]]).lhomWithConstants (X × Fin n)).onTheory (paramTheory L A) ∪
    ⋃ x : X, ((L[[A]]).lhomWithConstantsMap (fun i : Fin n => (x, i))).onSentence ''
      ((p x : ((L[[A]])[[Fin n]]).Theory))

variable (L) in
/-- **Any family of complete types over the same parameter set is simultaneously realisable.**
Proved by compactness: a finite piece of the theory only demands, for each of finitely many
indices, that finitely many formulas of a single complete type be realised, and a finite subset of
a complete type over `A` is realised in `M` itself. -/
theorem isSatisfiable_typeFamilyTheory (A : Set M) {n : ℕ} {X : Type}
    (p : X → CompleteTypeOver L A (Fin n)) : (typeFamilyTheory L A p).IsSatisfiable := by
  classical
  rw [Theory.isSatisfiable_iff_isFinitelySatisfiable]
  intro T0 hT0
  set r : X → ((L[[A]])[[Fin n]]).Sentence → ((L[[A]])[[X × Fin n]]).Sentence := fun x =>
    ((L[[A]]).lhomWithConstantsMap (fun i : Fin n => (x, i))).onSentence with hr
  have hrinj : ∀ x : X, Function.Injective (r x) := by
    intro x
    exact LHom.onSentence_injective _
      (lhomWithConstantsMap_injective ⟨fun i : Fin n => (x, i), fun i j h => congrArg Prod.snd h⟩)
  set S : X → Set (((L[[A]])[[Fin n]]).Sentence) := fun x =>
    {φ | φ ∈ p x ∧ r x φ ∈ T0} with hS
  have hSfin : ∀ x : X, (S x).Finite := by
    intro x
    refine Set.Finite.subset (Set.Finite.preimage ((hrinj x).injOn) T0.finite_toSet) ?_
    rintro φ ⟨-, hφ⟩
    exact hφ
  have hval : ∀ x : X, ∃ v : Fin n → M, ∀ φ ∈ S x, (Formula.equivSentence.symm φ).Realize v := by
    intro x
    set t : Finset (((L[[A]])[[Fin n]]).Sentence) := (hSfin x).toFinset with ht
    have htsub : (t : ((L[[A]])[[Fin n]]).Theory) ⊆ (p x : ((L[[A]])[[Fin n]]).Theory) := by
      intro φ hφ
      exact ((hSfin x).mem_toFinset.1 hφ).1
    have hmem : t.toList.foldr (· ⊓ ·) ⊤ ∈ p x := CompleteType.toList_foldr_inf_mem.2 htsub
    obtain ⟨v, hv⟩ := (typesWith_nonempty_iff_exists_realize L A _).1 ⟨p x, hmem⟩
    refine ⟨v, fun φ hφ => ?_⟩
    have hv' : t.toList.foldr (· ⊓ ·) ⊤ ∈ typeOver A v := mem_typeOver.2 hv
    exact mem_typeOver.1 (CompleteType.toList_foldr_inf_mem.1 hv'
      ((hSfin x).mem_toFinset.2 hφ))
  choose val hvalspec using hval
  letI : (constantsOn (X × Fin n)).Structure M :=
    constantsOn.structure (fun q : X × Fin n => val q.1 q.2)
  haveI : M ⊨ (T0 : ((L[[A]])[[X × Fin n]]).Theory) := by
    rw [Theory.model_iff]
    intro σ hσ
    rcases hT0 hσ with h1 | h2
    · obtain ⟨τ, hτ, rfl⟩ := h1
      rw [LHom.realize_onSentence]
      exact hτ
    · rw [Set.mem_iUnion] at h2
      obtain ⟨x, φ, hφ, rfl⟩ := h2
      rw [realize_onSentence_lhomWithConstantsMap]
      exact hvalspec x φ ⟨hφ, hσ⟩
  exact Theory.Model.isSatisfiable M

/-- **A model realising an injective family of types has uncountably many types over a countable
parameter sequence.** -/
theorem exists_modelType_witnesses {T : L.Theory} (M : T.ModelType.{0, 0, 0}) (A : Set M)
    (hA : #A ≤ ℵ₀) {n : ℕ} {X : Type} (p : X → CompleteTypeOver L A (Fin n))
    (hp : Function.Injective p) :
    ∃ (N : T.ModelType.{0, 0, 0}) (b : ℕ → N) (w : X → (Fin n → N)),
      Function.Injective (fun x => tpSeq L N n b (w x)) := by
  classical
  obtain ⟨P⟩ := isSatisfiable_typeFamilyTheory L (M := M) A p
  letI : (L[[A]]).Structure P := ((L[[A]]).lhomWithConstants (X × Fin n)).reduct P
  letI : L.Structure P := (L.lhomWithConstants A).reduct P
  haveI hPA : P ⊨ paramTheory L A :=
    (LHom.onTheory_model _ _).1 (P.is_model.mono Set.subset_union_left)
  have hTsub : (L.lhomWithConstants A).onTheory T ⊆ paramTheory L A := by
    rintro _ ⟨τ, hτ, rfl⟩
    rw [mem_paramTheory, LHom.realize_onSentence]
    exact M.is_model.realize_of_mem _ hτ
  haveI : P ⊨ T := (LHom.onTheory_model _ _).1 (hPA.mono hTsub)
  -- the realising tuples
  set w : X → (Fin n → P) := fun x i => (((L[[A]]).con (x, i) : ((L[[A]])[[X × Fin n]]).Constants) :
    P) with hw
  have hwreal : ∀ (x : X) (φ : ((L[[A]])[[Fin n]]).Sentence), φ ∈ p x →
      (Formula.equivSentence.symm φ).Realize (w x) := by
    intro x φ hφ
    letI : ((L[[A]])[[Fin n]]).Structure P :=
      ((L[[A]]).lhomWithConstantsMap (fun i : Fin n => ((x, i) : X × Fin n))).reduct P
    haveI : ((L[[A]]).lhomWithConstants (Fin n)).IsExpansionOn P := ⟨fun _ _ => rfl, fun _ _ => rfl⟩
    have hmem : P ⊨ ((L[[A]]).lhomWithConstantsMap
        (fun i : Fin n => ((x, i) : X × Fin n))).onSentence φ :=
      P.is_model.realize_of_mem _ (Set.subset_union_right (Set.mem_iUnion.2 ⟨x, φ, hφ, rfl⟩))
    rw [LHom.realize_onSentence] at hmem
    exact (Formula.realize_equivSentence_symm_con (P : Type _) φ).2 hmem
  -- an enumeration of the parameters by natural numbers
  haveI : Countable A := Cardinal.mk_le_aleph0_iff.1 hA
  obtain ⟨j, hj⟩ := (inferInstance : Countable A).exists_injective_nat
  set b : ℕ → P := fun m => if h : ∃ a : A, j a = m then
    ((L.con (Classical.choose h) : (L[[A]]).Constants) : P) else Classical.arbitrary P with hb
  have hbj : ∀ a : A, b (j a) = ((L.con a : (L[[A]]).Constants) : P) := by
    intro a
    have h : ∃ a' : A, j a' = j a := ⟨a, rfl⟩
    rw [hb]
    simp only [dif_pos h]
    exact congrArg _ (congrArg _ (hj (Classical.choose_spec h)))
  -- turning a formula with parameters in `A` into one with parameters indexed by `ℕ`
  set sep : ((L[[A]])[[Fin n]]).Sentence → L.Formula (ℕ ⊕ Fin n) := fun ψ =>
    Formula.relabel (Sum.map j id)
      (BoundedFormula.constantsVarsEquiv (Formula.equivSentence.symm ψ)) with hsep
  have hsepr : ∀ (ψ : ((L[[A]])[[Fin n]]).Sentence) (v : Fin n → P),
      (sep ψ).Realize (Sum.elim b v) ↔ (Formula.equivSentence.symm ψ).Realize v := by
    intro ψ v
    rw [hsep]
    simp only
    rw [Formula.realize_relabel]
    have he : (Sum.elim b v) ∘ (Sum.map j id) =
        Sum.elim (fun a : A => ((L.con a : (L[[A]]).Constants) : P)) v := by
      funext z
      cases z with
      | inl a => exact hbj a
      | inr i => rfl
    rw [he]
    exact BoundedFormula.realize_constantsVarsEquiv
  refine ⟨Theory.ModelType.of T P, b, w, fun x y hxy => ?_⟩
  by_contra hne
  have hpne : p x ≠ p y := fun h => hne (hp h)
  obtain ⟨φ, hφ⟩ : ∃ φ : ((L[[A]])[[Fin n]]).Sentence, ¬ (φ ∈ p x ↔ φ ∈ p y) := by
    by_contra hc
    push Not at hc
    exact hpne (SetLike.ext hc)
  have hmain : ∀ z z' : X, (∃ ψ : ((L[[A]])[[Fin n]]).Sentence, ψ ∈ p z ∧ ψ ∉ p z') →
      tpSeq L (Theory.ModelType.of T P) n b (w z) ≠
        tpSeq L (Theory.ModelType.of T P) n b (w z') := by
    rintro z z' ⟨ψ, hψ, hψ'⟩ heq
    have h1 : sep ψ ∈ tpSeq L (Theory.ModelType.of T P) n b (w z) :=
      (hsepr ψ (w z)).2 (hwreal z ψ hψ)
    have h2 : ¬ (Formula.equivSentence.symm ψ).Realize (w z') := by
      have := hwreal z' (∼ψ) ((CompleteType.not_mem_iff _ _).2 hψ')
      rwa [equivSentence_symm_not, Formula.realize_not] at this
    have h3 : sep ψ ∈ tpSeq L (Theory.ModelType.of T P) n b (w z') := heq ▸ h1
    exact h2 ((hsepr ψ (w z')).1 h3)
  by_cases hx : φ ∈ p x
  · exact hmain x y ⟨φ, hx, fun h => hφ ⟨fun _ => h, fun _ => hx⟩⟩ hxy
  · exact hmain y x ⟨φ, by tauto, hx⟩ hxy.symm

/-- **Löwenheim–Skolem for the witnesses**: a family of tuples with pairwise distinct types over a
countable parameter sequence can be moved into a model of any prescribed infinite cardinality at
least the size of the family. -/
theorem exists_modelType_card_eq_witnesses {T : L.Theory} (hL : L.card ≤ ℵ₀)
    (hInf : ∀ N : T.ModelType.{0, 0, 0}, Infinite N) (N : T.ModelType.{0, 0, 0}) {n : ℕ}
    {X : Type} (b : ℕ → N) (w : X → (Fin n → N))
    (hinj : Function.Injective (fun x => tpSeq L N n b (w x)))
    {κ : Cardinal.{0}} (hκ : ℵ₀ ≤ κ) (hXκ : #X ≤ κ) :
    ∃ (N' : T.ModelType.{0, 0, 0}) (b' : ℕ → N') (w' : X → (Fin n → N')),
      #N' = κ ∧ Function.Injective (fun x => tpSeq L N' n b' (w' x)) := by
  classical
  haveI : Infinite N := hInf N
  have hLκ : L.card ≤ κ := hL.trans hκ
  -- step 1: an elementary extension of `N` of size at least `κ`
  obtain ⟨N₁, ⟨e⟩, hN₁⟩ := exists_elementaryEmbedding_card_eq_of_ge L (N : Type) (max κ #N)
    (by simpa using hLκ.trans (le_max_left _ _)) (by simp)
  haveI : N₁ ⊨ T := (e.theory_model_iff T).1 N.is_model
  -- step 2: an elementary substructure of size exactly `κ` containing the witnesses
  set s : Set N₁ := Set.range (fun z : ℕ ⊕ (X × Fin n) =>
    Sum.elim (fun m => e (b m)) (fun q => e (w q.1 q.2)) z) with hs
  have hscard : #s ≤ κ := by
    refine Cardinal.mk_range_le.trans ?_
    rw [Cardinal.mk_sum, Cardinal.mk_prod]
    simp only [Cardinal.mk_nat, Cardinal.mk_fin, Cardinal.lift_id]
    calc ℵ₀ + #X * (n : Cardinal) ≤ κ + κ * ℵ₀ :=
          add_le_add hκ (mul_le_mul' hXκ (Cardinal.natCast_lt_aleph0 (n := n)).le)
      _ = κ := by
          rw [Cardinal.mul_eq_max hκ le_rfl, max_eq_left hκ, Cardinal.add_eq_self hκ]
  obtain ⟨S, hsS, hScard⟩ := exists_elementarySubstructure_card_eq L s κ hκ
    (by simpa using hscard) (by simpa using hLκ) (by simp [hN₁])
  have hmemb : ∀ m : ℕ, e (b m) ∈ S := fun m => hsS ⟨Sum.inl m, rfl⟩
  have hmemw : ∀ (x : X) (i : Fin n), e (w x i) ∈ S := fun x i => hsS ⟨Sum.inr (x, i), rfl⟩
  haveI : Nonempty S := ⟨⟨e (b 0), hmemb 0⟩⟩
  haveI : S ⊨ T := (S.subtype.theory_model_iff T).2 inferInstance
  set b' : ℕ → ↥S := fun m => ⟨e (b m), hmemb m⟩ with hb'
  set w' : X → Fin n → ↥S := fun x i => ⟨e (w x i), hmemw x i⟩ with hw'
  have hkey : ∀ x : X, tpSeq L (↥S) n b' (w' x) = tpSeq L N n b (w x) := by
    intro x
    rw [← tpSeq_comp S.subtype n b' (w' x), ← tpSeq_comp e n b (w x)]
    rfl
  have hinj' : Function.Injective (fun x => tpSeq L (↥S) n b' (w' x)) := by
    intro x y hxy
    refine hinj ?_
    simp only at hxy
    rw [hkey x, hkey y] at hxy
    exact hxy
  exact ⟨Theory.ModelType.of T ↥S, b', w', by simpa using hScard, hinj'⟩

/-- **An uncountable space of `n`-types over a countable parameter set produces, in every
uncountable cardinal, a model with uncountably many `n`-types over a countable parameter
sequence.**  This is one of the two halves of the proof that categoricity implies ω-stability; the
other half is the Ehrenfeucht–Mostowski bound `Submission.Morley.EMTypeBound`. -/
theorem exists_modelType_card_eq_not_fewSeqTypesAt {T : L.Theory} (hL : L.card ≤ ℵ₀)
    (hInf : ∀ N : T.ModelType.{0, 0, 0}, Infinite N) (M : T.ModelType.{0, 0, 0}) (A : Set M)
    (hAc : #A ≤ ℵ₀) {n : ℕ} (hn : ℵ₀ < #(CompleteTypeOver L A (Fin n)))
    {κ : Cardinal.{0}} (hκ : ℵ₀ < κ) :
    ∃ N : T.ModelType.{0, 0, 0}, #N = κ ∧ ¬ FewSeqTypesAt L N n := by
  classical
  obtain ⟨Y, hY⟩ :=
    Cardinal.le_mk_iff_exists_set.1 (min_le_left #(CompleteTypeOver L A (Fin n)) κ)
  have hYcard : ℵ₀ < #Y := by rw [hY]; exact lt_min hn hκ
  obtain ⟨N, b, w, hinj⟩ := exists_modelType_witnesses M A hAc
    (fun x : Y => (x : CompleteTypeOver L A (Fin n))) Subtype.val_injective
  obtain ⟨N', b', w', hcard, hinj'⟩ :=
    exists_modelType_card_eq_witnesses hL hInf N b w hinj hκ.le
      (by rw [hY]; exact min_le_right _ _)
  refine ⟨N', hcard, fun hfew => ?_⟩
  have hle : #Y ≤ #(Set.range (tpSeq L N' n b')) :=
    Cardinal.mk_le_of_injective (f := fun x : Y =>
      (⟨tpSeq L N' n b' (w' x), ⟨w' x, rfl⟩⟩ : Set.range (tpSeq L N' n b')))
      fun x y hxy => hinj' (congrArg Subtype.val hxy)
  exact absurd (hle.trans (hfew b')) (not_le.2 hYcard)

end Realizing

/-! ## Categoricity implies ω-stability -/

section Categoricity

variable {L : FirstOrder.Language.{0, 0}}

variable (L) in
/-- **The Ehrenfeucht–Mostowski type-counting bound in `n` variables**, taken here as a hypothesis.

It says that a satisfiable theory with only infinite models, in a countable language, has, in every
infinite cardinality `κ`, a model of size `κ` in which only countably many complete `n`-types over a
countable parameter set are *realised*.  This is exactly what an Ehrenfeucht–Mostowski model built
on a linearly ordered set of indiscernibles provides: note that the bound is on the number of
*realised* types, not on the size of the type space. -/
def EMTypeBoundAt (L : FirstOrder.Language.{0, 0}) (n : ℕ) : Prop :=
  ∀ (T : L.Theory), L.card ≤ ℵ₀ → T.IsSatisfiable →
    (∀ M : T.ModelType.{0, 0, 0}, Infinite M) → ∀ κ : Cardinal.{0}, ℵ₀ ≤ κ →
      ∃ M : T.ModelType.{0, 0, 0}, #M = κ ∧
        ∀ A : Set M, #A ≤ ℵ₀ → #((paramTheory L A).realizedTypes M (Fin n)) ≤ ℵ₀

variable (L) in
/-- The Ehrenfeucht–Mostowski type-counting bound in every finite number of variables. -/
def EMTypeBound (L : FirstOrder.Language.{0, 0}) : Prop := ∀ n : ℕ, EMTypeBoundAt L n

/-- **A `κ`-categorical theory has countably many `n`-types over countable parameter sets**,
conditionally on the Ehrenfeucht–Mostowski bound `Submission.Morley.EMTypeBoundAt`.

If there were uncountably many `n`-types over some countable parameter set, there would be a model
of size `κ` realising uncountably many `n`-types over a countable parameter sequence
(`Submission.Morley.exists_modelType_card_eq_not_fewSeqTypesAt`), while the Ehrenfeucht–Mostowski
model of size `κ` realises only countably many.  Categoricity makes the two isomorphic, a
contradiction. -/
theorem countable_completeTypeOver_of_categorical {n : ℕ} (hEM : EMTypeBoundAt L n)
    {T : L.Theory} (hL : L.card ≤ ℵ₀) (hT : T.IsComplete)
    (hInf : ∀ M : T.ModelType.{0, 0, 0}, Infinite M) {κ : Cardinal.{0}} (hκ : ℵ₀ < κ)
    (hcat : κ.Categorical T) (M₀ : T.ModelType.{0, 0, 0}) (A : Set M₀) (hAc : #A ≤ ℵ₀) :
    #(CompleteTypeOver L A (Fin n)) ≤ ℵ₀ := by
  by_contra hcon
  obtain ⟨N, hNcard, hNfew⟩ :=
    exists_modelType_card_eq_not_fewSeqTypesAt hL hInf M₀ A hAc (not_le.1 hcon) hκ
  obtain ⟨M, hMcard, hMfew⟩ := hEM T hL hT.1 hInf κ hκ.le
  obtain ⟨f⟩ := hcat N M hNcard hMcard
  exact hNfew ((fewSeqTypesAt_of_mk_realizedTypes_le n hMfew).of_elementaryEmbedding
    f.toElementaryEmbedding)

/-- **A `κ`-categorical theory is ω-stable**, conditionally on the Ehrenfeucht–Mostowski bound
`Submission.Morley.EMTypeBound`. -/
theorem isOmegaStable_of_categorical (hEM : EMTypeBound L) {T : L.Theory} (hL : L.card ≤ ℵ₀)
    (hT : T.IsComplete) (hInf : ∀ M : T.ModelType.{0, 0, 0}, Infinite M)
    {κ : Cardinal.{0}} (hκ : ℵ₀ < κ) (hcat : κ.Categorical T) : IsOmegaStable.{0, 0, 0} T := by
  intro M₀ A hAc n _
  exact Cardinal.mk_le_aleph0_iff.1 (countable_completeTypeOver_of_categorical (hEM n) hL hT hInf
    hκ hcat M₀ A (Cardinal.mk_le_aleph0_iff.2 (Set.countable_coe_iff.2 hAc)))

/-- **A `κ`-categorical theory is ω-stable for `1`-types**, conditionally on the
Ehrenfeucht–Mostowski bound for `1`-types only.  This is the form in which ω-stability is consumed
by `Submission.Morley.stable_of_omegaStable'`. -/
theorem omegaStable_of_categorical (hEM : EMTypeBoundAt L 1) {T : L.Theory} (hL : L.card ≤ ℵ₀)
    (hT : T.IsComplete) (hInf : ∀ M : T.ModelType.{0, 0, 0}, Infinite M)
    {κ : Cardinal.{0}} (hκ : ℵ₀ < κ) (hcat : κ.Categorical T) : OmegaStable.{0, 0, 0} T :=
  fun M₀ A hAc => countable_completeTypeOver_of_categorical hEM hL hT hInf hκ hcat M₀ A hAc

/-- **Morley's stability step**: a `κ`-categorical theory in a countable language is `μ`-stable for
every infinite `μ`, conditionally on the Ehrenfeucht–Mostowski bound for `1`-types. -/
theorem stable_of_categorical (hEM : EMTypeBoundAt L 1) {T : L.Theory} (hL : L.card ≤ ℵ₀)
    (hT : T.IsComplete) (hInf : ∀ M : T.ModelType.{0, 0, 0}, Infinite M)
    {κ : Cardinal.{0}} (hκ : ℵ₀ < κ) (hcat : κ.Categorical T)
    {μ : Cardinal.{0}} (hμ : ℵ₀ ≤ μ) : Stable μ T :=
  stable_of_omegaStable' hL (omegaStable_of_categorical hEM hL hT hInf hκ hcat) hμ

end Categoricity

end Submission.Morley
