import Mathlib

/-!
# Types over parameter sets and ω-stability

This file is the "types and stability" chapter of a formalisation of Morley's categoricity
theorem.  On top of `Mathlib/ModelTheory/Types.lean` (complete types) and
`Mathlib/ModelTheory/Topology/Types.lean` (the Stone topology on the space of complete types)
it develops:

* `Submission.Morley.paramTheory L A` — the theory `Th(M_A)` of a structure `M` in the language
  `L[[A]]` obtained by naming every element of a parameter set `A ⊆ M`;
* `Submission.Morley.CompleteTypeOver L A α` — the space of complete `α`-types over `A`, and its
  one-variable specialisation `Submission.Morley.S₁ L A`;
* `Submission.Morley.IsOmegaStable T` — ω-stability (all arities), `Submission.Morley.OmegaStable`
  (the `1`-type, cardinal-valued form) and `Submission.Morley.Stable κ T` (`κ`-stability);
* `Submission.Morley.BinaryTree T α` — a full binary tree of formulas whose nodes are consistent
  and whose sibling nodes are contradictory;
* the two directions of the **binary-tree characterisation of non-ω-stability**,
  `Submission.Morley.exists_binaryTree_of_not_isOmegaStable` and
  `Submission.Morley.not_isOmegaStable_of_binaryTree`, together with their `1`-type variants
  `Submission.Morley.exists_binaryTree_of_not_omegaStable` and
  `Submission.Morley.not_omegaStable_of_binaryTree`;
* the `κ`-stable generalisation `Submission.Morley.exists_binaryTree_of_not_stable`.

## Outstanding

`ω`-stable → `κ`-stable is *not* proved here.  Both halves of the standard argument that are
model-theoretic are available: `Submission.Morley.exists_binaryTree_of_not_stable` produces a
binary tree over a parameter set of size at most `κ`, and
`Submission.Morley.not_omegaStable_of_binaryTree` turns a binary tree over a *countable* parameter
set into a failure of ω-stability.  What is missing is the purely syntactic step in between: the
countably many formulas of a binary tree only mention countably many parameters, so the tree may
be taken over a countable subset of the parameter set.

## Implementation notes

Following the conventions of `Mathlib/ModelTheory/Types.lean`, a "formula in the variables `α`
with parameters in `A`" is encoded as a *sentence* of `L[[A]][[α]]`; the extra constants indexed
by `α` play the role of the free variables.  `FirstOrder.Language.Formula.equivSentence`
translates between the two views.

The mathematical core is a Cantor-scheme construction: `Submission.Morley.exists_dyadic` builds a
`List Bool`-indexed tree by recursion, using `Classical.choice` at every node, and
`Submission.Morley.not_countable_of_dyadic` extracts a copy of the Cantor space `ℕ → Bool` out of
such a tree in a compact space.  Both are stated for abstract topological spaces and then
transported to the Stone space `T.CompleteType α`.
-/

universe u v w w'

open Cardinal Set FirstOrder Language Theory

namespace Submission.Morley

/-! ## A Cantor scheme -/

section Cantor

variable {ι X : Type*}

/-- **Cantor scheme.**  Suppose `f : ι → Set X` is a family of sets, `P` is a property of indices,
some index satisfies `P`, and every index satisfying `P` can be split into two indices satisfying
`P` whose sets are disjoint subsets of the original one.  Then there is a full binary tree
`g : List Bool → ι` of indices satisfying `P`, in which children refine their parent and the two
children of a node are disjoint.

This is the fiddly recursion at the heart of the binary-tree characterisation of
non-ω-stability; the two children of a node are chosen with `Classical.choice`. -/
theorem exists_dyadic (f : ι → Set X) (P : ι → Prop) (h₀ : ∃ i, P i)
    (hsplit : ∀ i, P i → ∃ j k : ι,
      f j ⊆ f i ∧ f k ⊆ f i ∧ Disjoint (f j) (f k) ∧ P j ∧ P k) :
    ∃ g : List Bool → ι, (∀ s, P (g s)) ∧
      (∀ (b : Bool) (s : List Bool), f (g (b :: s)) ⊆ f (g s)) ∧
      (∀ s : List Bool, Disjoint (f (g (false :: s))) (f (g (true :: s)))) := by
  classical
  obtain ⟨i₀, hi₀⟩ := h₀
  -- Turn the (partial) splitting into a total function `ι → ι × ι`.
  have hsplit' : ∀ i : ι, ∃ jk : ι × ι, P i →
      (f jk.1 ⊆ f i ∧ f jk.2 ⊆ f i ∧ Disjoint (f jk.1) (f jk.2) ∧ P jk.1 ∧ P jk.2) := by
    intro i
    by_cases hi : P i
    · obtain ⟨j, k, hjk⟩ := hsplit i hi
      exact ⟨(j, k), fun _ => hjk⟩
    · exact ⟨(i, i), fun h => absurd h hi⟩
  choose F hF using hsplit'
  refine ⟨fun s => List.rec i₀ (fun b _ ih => cond b (F ih).2 (F ih).1) s, ?_, ?_, ?_⟩
  · intro s
    induction s with
    | nil => exact hi₀
    | cons b s ih => cases b
                     · exact (hF _ ih).2.2.2.1
                     · exact (hF _ ih).2.2.2.2
  · intro b s
    have hs : P (List.rec i₀ (fun b _ ih => cond b (F ih).2 (F ih).1) s) := by
      induction s with
      | nil => exact hi₀
      | cons b s ih => cases b
                       · exact (hF _ ih).2.2.2.1
                       · exact (hF _ ih).2.2.2.2
    cases b
    · exact (hF _ hs).1
    · exact (hF _ hs).2.1
  · intro s
    have hs : P (List.rec i₀ (fun b _ ih => cond b (F ih).2 (F ih).1) s) := by
      induction s with
      | nil => exact hi₀
      | cons b s ih => cases b
                       · exact (hF _ ih).2.2.2.1
                       · exact (hF _ ih).2.2.2.2
    exact (hF _ hs).2.2.1

/-- The node of a `List Bool`-indexed tree reached after following the first `n` steps of the
branch `η`. -/
private def branch (η : ℕ → Bool) : ℕ → List Bool
  | 0 => []
  | n + 1 => η n :: branch η n

private theorem branch_succ (η : ℕ → Bool) (n : ℕ) :
    branch η (n + 1) = η n :: branch η n := rfl

private theorem branch_congr {η η' : ℕ → Bool} {k : ℕ} (h : ∀ j < k, η j = η' j) :
    branch η k = branch η' k := by
  induction k with
  | zero => rfl
  | succ n ih =>
    rw [branch_succ, branch_succ, h n (Nat.lt_succ_self n),
      ih fun j hj => h j (hj.trans (Nat.lt_succ_self n))]

private theorem not_countable_nat_bool : ¬ Countable (ℕ → Bool) := by
  intro h
  have h2 : #(ℕ → Bool) ≤ ℵ₀ := Cardinal.mk_le_aleph0_iff.2 h
  rw [Cardinal.mk_arrow] at h2
  simp only [Cardinal.mk_bool, Cardinal.mk_nat, Cardinal.lift_id] at h2
  exact absurd h2 (not_le.2 (Cardinal.cantor ℵ₀))

/-- A Cantor scheme of nonempty closed sets inside a compact space carries a copy of the Cantor
space `ℕ → Bool`. -/
theorem exists_injective_of_dyadic [TopologicalSpace X] [CompactSpace X]
    (C : List Bool → Set X) (hne : ∀ s, (C s).Nonempty) (hcl : ∀ s, IsClosed (C s))
    (hmono : ∀ (b : Bool) (s : List Bool), C (b :: s) ⊆ C s)
    (hdisj : ∀ s : List Bool, Disjoint (C (false :: s)) (C (true :: s))) :
    ∃ f : (ℕ → Bool) → X, Function.Injective f := by
  classical
  have key : ∀ η : ℕ → Bool, (⋂ n, C (branch η n)).Nonempty := by
    intro η
    refine IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed _
      (fun n => ?_) (fun _ => hne _) (isCompact_univ.of_isClosed_subset (hcl _) (subset_univ _))
      (fun _ => hcl _)
    rw [branch_succ]
    exact hmono _ _
  choose p hp using key
  have hmem : ∀ (η : ℕ → Bool) (n : ℕ), p η ∈ C (branch η n) := fun η n =>
    Set.mem_iInter.1 (hp η) n
  refine ⟨p, fun η η' hpp => ?_⟩
  by_contra hne'
  have hex : ∃ k, η k ≠ η' k := by
    by_contra hc
    push Not at hc
    exact hne' (funext hc)
  have hk1 : η (Nat.find hex) ≠ η' (Nat.find hex) := Nat.find_spec hex
  have hk2 : ∀ j < Nat.find hex, η j = η' j := fun j hj => by
    by_contra hc
    exact absurd (Nat.find_le hc) (not_le.2 hj)
  have hb : branch η' (Nat.find hex) = branch η (Nat.find hex) := branch_congr fun j hj =>
    (hk2 j hj).symm
  have h1 : p η ∈ C (η (Nat.find hex) :: branch η (Nat.find hex)) := by
    have := hmem η (Nat.find hex + 1); rwa [branch_succ] at this
  have h2 : p η' ∈ C (η' (Nat.find hex) :: branch η (Nat.find hex)) := by
    have := hmem η' (Nat.find hex + 1); rwa [branch_succ, hb] at this
  rw [hpp] at h1
  cases hbb : η (Nat.find hex)
  · have hbb' : η' (Nat.find hex) = true := by
      cases hbb' : η' (Nat.find hex)
      · exact absurd (hbb.trans hbb'.symm) hk1
      · rfl
    rw [hbb] at h1
    rw [hbb'] at h2
    exact Set.disjoint_left.1 (hdisj _) h1 h2
  · have hbb' : η' (Nat.find hex) = false := by
      cases hbb' : η' (Nat.find hex)
      · rfl
      · exact absurd (hbb.trans hbb'.symm) hk1
    rw [hbb] at h1
    rw [hbb'] at h2
    exact Set.disjoint_left.1 (hdisj _) h2 h1

/-- A Cantor scheme of nonempty closed sets inside a compact space makes the ambient space
uncountable. -/
theorem not_countable_of_dyadic [TopologicalSpace X] [CompactSpace X]
    (C : List Bool → Set X) (hne : ∀ s, (C s).Nonempty) (hcl : ∀ s, IsClosed (C s))
    (hmono : ∀ (b : Bool) (s : List Bool), C (b :: s) ⊆ C s)
    (hdisj : ∀ s : List Bool, Disjoint (C (false :: s)) (C (true :: s))) :
    ¬ Countable X := by
  obtain ⟨f, hf⟩ := exists_injective_of_dyadic C hne hcl hmono hdisj
  intro _
  exact not_countable_nat_bool hf.countable

end Cantor

/-! ## Binary trees of formulas -/

section BinaryTree

variable {L : FirstOrder.Language.{u, v}} {T : L.Theory} {α : Type w}

/-- A *binary tree of formulas* for the theory `T` in the variables `α`: a family of formulas
indexed by `List Bool` (encoded, as in `Mathlib/ModelTheory/Types.lean`, as sentences of
`L[[α]]`), such that every node is consistent with `T`, the two children of a node both imply it,
and the two children of a node contradict each other.

Consistency and the implications are phrased through the clopen sets `T.typesWith`, which is
equivalent to the syntactic formulation; see `Submission.Morley.typesWith_nonempty_iff`. -/
structure BinaryTree (T : L.Theory) (α : Type w) where
  /-- The formula sitting at the node `s`. -/
  form : List Bool → L[[α]].Sentence
  /-- Every node is consistent with `T`. -/
  consistent : ∀ s, (T.typesWith (form s)).Nonempty
  /-- Each child implies its parent. -/
  mono : ∀ (b : Bool) (s : List Bool), T.typesWith (form (b :: s)) ⊆ T.typesWith (form s)
  /-- The two children of a node are contradictory. -/
  disjoint : ∀ s : List Bool,
    Disjoint (T.typesWith (form (false :: s))) (T.typesWith (form (true :: s)))

/-- A formula is consistent with `T` exactly when the set of complete types containing it is
nonempty.  This is the bridge between the semantic phrasing of `Submission.Morley.BinaryTree`
and the syntactic one. -/
theorem typesWith_nonempty_iff (T : L.Theory) (φ : L[[α]].Sentence) :
    (T.typesWith φ).Nonempty ↔
      ((L.lhomWithConstants α).onTheory T ∪ {φ}).IsSatisfiable := by
  have h : {p : T.CompleteType α | ({φ} : L[[α]].Theory) ⊆ ↑p} = T.typesWith φ := by
    ext p
    exact Set.singleton_subset_iff
  rw [← not_iff_not, Set.not_nonempty_iff_eq_empty, ← h,
    CompleteType.setOf_subset_eq_empty_iff]

/-- Two formulas are contradictory over `T` exactly when the corresponding clopen sets of
complete types are disjoint.  This is the syntactic reading of the `disjoint` field of
`Submission.Morley.BinaryTree`. -/
theorem typesWith_disjoint_iff (T : L.Theory) (φ ψ : L[[α]].Sentence) :
    Disjoint (T.typesWith φ) (T.typesWith ψ) ↔
      ¬ ((L.lhomWithConstants α).onTheory T ∪ {φ, ψ}).IsSatisfiable := by
  have h : {p : T.CompleteType α | ({φ, ψ} : L[[α]].Theory) ⊆ ↑p} =
      T.typesWith φ ∩ T.typesWith ψ := by
    ext p
    exact ⟨fun hp => ⟨hp (Set.mem_insert _ _), hp (Set.mem_insert_of_mem _ rfl)⟩,
      fun hp => Set.insert_subset hp.1 (Set.singleton_subset_iff.2 hp.2)⟩
  rw [Set.disjoint_iff_inter_eq_empty, ← h, CompleteType.setOf_subset_eq_empty_iff]

/-- One formula implies another over `T` exactly when the corresponding clopen sets of complete
types are nested.  This is the syntactic reading of the `mono` field of
`Submission.Morley.BinaryTree`. -/
theorem typesWith_subset_iff (T : L.Theory) (φ ψ : L[[α]].Sentence) :
    T.typesWith φ ⊆ T.typesWith ψ ↔
      ¬ ((L.lhomWithConstants α).onTheory T ∪ {φ, ∼ψ}).IsSatisfiable := by
  rw [← typesWith_disjoint_iff, CompleteType.typesWith_not, Set.disjoint_compl_right_iff_subset]

/-- A binary tree of formulas produces a copy of the Cantor space inside the space of complete
types. -/
theorem BinaryTree.exists_injective_nat_bool (t : BinaryTree T α) :
    ∃ f : (ℕ → Bool) → T.CompleteType α, Function.Injective f :=
  exists_injective_of_dyadic _ t.consistent (fun _ => CompleteType.isClosed_typesWith _) t.mono
    t.disjoint

/-- A binary tree of formulas produces a copy of the Cantor space inside the type space, so the
space of complete types is uncountable. -/
theorem BinaryTree.not_countable (t : BinaryTree T α) : ¬ Countable (T.CompleteType α) :=
  not_countable_of_dyadic _ t.consistent (fun _ => CompleteType.isClosed_typesWith _) t.mono
    t.disjoint

/-- A binary tree of formulas gives uncountably many complete types. -/
theorem BinaryTree.aleph0_lt_mk (t : BinaryTree T α) : ℵ₀ < #(T.CompleteType α) :=
  Cardinal.aleph0_lt_mk_iff.2 ⟨t.not_countable⟩

/-- **If a type space is bigger than `κ` then it contains a binary tree of formulas**, provided
there are at most `κ` formulas to choose from and `κ` is infinite.

The proof is the standard Cantor–Bendixson argument, run inside the Stone space: the union `V` of
all basic clopen sets of size at most `κ` has size at most `κ`, so its complement `D` is nonempty,
and every basic clopen set meeting `D` splits into two disjoint basic clopen sets that still meet
`D`.  The tree is then assembled by `Submission.Morley.exists_dyadic`. -/
theorem exists_binaryTree_of_lt_mk {κ : Cardinal.{max u v w}} (hκ : ℵ₀ ≤ κ)
    (hsent : #(L[[α]].Sentence) ≤ κ) (h : κ < #(T.CompleteType α)) :
    Nonempty (BinaryTree T α) := by
  classical
  set V : Set (T.CompleteType α) :=
    ⋃ φ : {φ : L[[α]].Sentence // #(T.typesWith φ) ≤ κ}, T.typesWith φ.1 with hVdef
  have hVc : #V ≤ κ := by
    refine Cardinal.mk_iUnion_le_sum_mk.trans ?_
    refine (Cardinal.sum_le_sum _ (fun _ => κ) fun φ => φ.2).trans ?_
    rw [Cardinal.sum_const']
    exact (mul_le_mul' ((Cardinal.mk_subtype_le _).trans hsent) le_rfl).trans
      (Cardinal.mul_eq_self hκ).le
  set D : Set (T.CompleteType α) := Vᶜ with hDdef
  have hD : D.Nonempty := by
    rw [hDdef, Set.nonempty_compl]
    intro hVu
    rw [hVu, Cardinal.mk_univ] at hVc
    exact absurd hVc (not_le.2 h)
  -- A basic clopen set meeting `D` has size bigger than `κ`.
  have hnotc : ∀ φ : L[[α]].Sentence, (T.typesWith φ ∩ D).Nonempty →
      ¬ #(T.typesWith φ) ≤ κ := by
    rintro φ ⟨p, hp1, hp2⟩ hcount
    exact hp2 (Set.mem_iUnion.2 ⟨⟨φ, hcount⟩, hp1⟩)
  -- Two points of `T.typesWith φ ∩ D` separated by `χ` give the required splitting.
  have hmain : ∀ (φ χ : L[[α]].Sentence) (p q : T.CompleteType α),
      p ∈ T.typesWith φ ∩ D → q ∈ T.typesWith φ ∩ D → χ ∈ p → χ ∉ q →
      ∃ ψ₁ ψ₂ : L[[α]].Sentence, T.typesWith ψ₁ ⊆ T.typesWith φ ∧
        T.typesWith ψ₂ ⊆ T.typesWith φ ∧ Disjoint (T.typesWith ψ₁) (T.typesWith ψ₂) ∧
        (T.typesWith ψ₁ ∩ D).Nonempty ∧ (T.typesWith ψ₂ ∩ D).Nonempty := by
    intro φ χ p q hp hq hpχ hqχ
    refine ⟨φ ⊓ χ, φ ⊓ ∼χ, ?_, ?_, ?_, ⟨p, ?_, hp.2⟩, ⟨q, ?_, hq.2⟩⟩
    · rw [CompleteType.typesWith_inf]; exact Set.inter_subset_left
    · rw [CompleteType.typesWith_inf]; exact Set.inter_subset_left
    · rw [CompleteType.typesWith_inf, CompleteType.typesWith_inf, CompleteType.typesWith_not]
      exact Set.disjoint_left.2 fun x hx hx' => hx'.2 hx.2
    · rw [CompleteType.typesWith_inf]; exact ⟨hp.1, hpχ⟩
    · rw [CompleteType.typesWith_inf, CompleteType.typesWith_not]; exact ⟨hq.1, hqχ⟩
  have key : ∀ φ : L[[α]].Sentence, (T.typesWith φ ∩ D).Nonempty →
      ∃ ψ₁ ψ₂ : L[[α]].Sentence, T.typesWith ψ₁ ⊆ T.typesWith φ ∧
        T.typesWith ψ₂ ⊆ T.typesWith φ ∧ Disjoint (T.typesWith ψ₁) (T.typesWith ψ₂) ∧
        (T.typesWith ψ₁ ∩ D).Nonempty ∧ (T.typesWith ψ₂ ∩ D).Nonempty := by
    intro φ hφ
    have h1 : ¬ #(T.typesWith φ ∩ D : Set _) ≤ κ := by
      intro hcount
      refine hnotc φ hφ ?_
      have hsplit : T.typesWith φ = (T.typesWith φ ∩ V) ∪ (T.typesWith φ ∩ D) := by
        rw [hDdef, ← Set.inter_union_distrib_left, Set.union_compl_self, Set.inter_univ]
      rw [hsplit]
      refine (Cardinal.mk_union_le _ _).trans ?_
      refine (add_le_add ((Cardinal.mk_le_mk_of_subset Set.inter_subset_right).trans hVc)
        hcount).trans (Cardinal.add_eq_self hκ).le
    have h2 : (T.typesWith φ ∩ D).Nontrivial := by
      refine Set.not_subsingleton_iff.1 fun hs => h1 ?_
      exact (Cardinal.mk_le_one_iff_set_subsingleton.2 hs).trans (one_le_aleph0.trans hκ)
    obtain ⟨p, hp, q, hq, hpq⟩ := h2
    obtain ⟨χ, hχ⟩ : ∃ χ : L[[α]].Sentence, ¬ (χ ∈ p ↔ χ ∈ q) := by
      by_contra hc
      push Not at hc
      exact hpq (SetLike.ext hc)
    by_cases hpχ : χ ∈ p
    · exact hmain φ χ p q hp hq hpχ fun hq' => hχ ⟨fun _ => hq', fun _ => hpχ⟩
    · obtain ⟨ψ₁, ψ₂, h₁, h₂, h₃, h₄, h₅⟩ :=
        hmain φ χ q p hq hp (by tauto) hpχ
      exact ⟨ψ₂, ψ₁, h₂, h₁, h₃.symm, h₅, h₄⟩
  obtain ⟨g, hP, hmono, hdisj⟩ := exists_dyadic T.typesWith
    (fun φ => (T.typesWith φ ∩ D).Nonempty)
    ⟨⊤, by rw [CompleteType.typesWith_top, Set.univ_inter]; exact hD⟩ key
  exact ⟨⟨g, fun s => (hP s).mono Set.inter_subset_left, hmono, hdisj⟩⟩

/-- If the space of complete `α`-types of a countable theory in countably many variables is
uncountable, then there is a binary tree of formulas. -/
theorem exists_binaryTree_of_not_countable [Countable L.Symbols] [Countable α]
    (h : ¬ Countable (T.CompleteType α)) : Nonempty (BinaryTree T α) :=
  exists_binaryTree_of_lt_mk le_rfl (Cardinal.mk_le_aleph0_iff.2 inferInstance)
    (Cardinal.aleph0_lt_mk_iff.2 ⟨h⟩)

end BinaryTree

/-! ## Types over a parameter set -/

section Types

variable (L : FirstOrder.Language.{u, v}) {M : Type w} [L.Structure M]

/-- `paramTheory L A` is the complete theory of the structure `M` in the language `L[[A]]`, in
which every element of the parameter set `A ⊆ M` is named by a constant.  It is the theory
usually written `Th(M_A)`. -/
abbrev paramTheory (A : Set M) : (L[[A]]).Theory := L[[A]].completeTheory M

/-- `CompleteTypeOver L A α` is the space of complete `α`-types over the parameter set `A ⊆ M`,
i.e. the maximal extensions of `Th(M_A)` that are consistent and mention the variables `α`.
It carries the Stone topology of `Mathlib/ModelTheory/Topology/Types.lean` and is a nonempty
compact totally separated space. -/
abbrev CompleteTypeOver (A : Set M) (α : Type w') : Type _ :=
  (paramTheory L A).CompleteType α

/-- `Form1 L A` is the type of formulas in one free variable with parameters in `A ⊆ M`, encoded
as sentences of `L[[A]][[Fin 1]]`. -/
abbrev Form1 (A : Set M) : Type _ := ((L[[A]])[[Fin 1]]).Sentence

/-- `S₁ L A` is the space of complete `1`-types over the parameter set `A ⊆ M`. -/
abbrev S₁ (A : Set M) : Type _ := CompleteTypeOver L A (Fin 1)

end Types

section TypesBasic

variable {L : FirstOrder.Language.{u, v}} {M : Type w} [L.Structure M] {α : Type w'}

@[simp]
theorem mem_paramTheory {A : Set M} {φ : (L[[A]]).Sentence} :
    φ ∈ paramTheory L A ↔ M ⊨ φ := Iff.rfl

theorem paramTheory_isSatisfiable [Nonempty M] (A : Set M) :
    (paramTheory L A).IsSatisfiable :=
  Theory.Model.isSatisfiable M

instance nonempty_completeTypeOver [Nonempty M] (A : Set M) :
    Nonempty (CompleteTypeOver L A α) :=
  CompleteType.nonempty_iff.2 (paramTheory_isSatisfiable A)

/-- The complete type over `A` realised by a tuple `v : α → M` of elements of `M`. -/
abbrev typeOver [Nonempty M] (A : Set M) (v : α → M) : CompleteTypeOver L A α :=
  (paramTheory L A).typeOf v

@[simp]
theorem mem_typeOver [Nonempty M] {A : Set M} {v : α → M}
    {φ : ((L[[A]])[[α]]).Sentence} :
    φ ∈ typeOver A v ↔ (Formula.equivSentence.symm φ).Realize v :=
  CompleteType.mem_typeOf

theorem formula_mem_typeOver [Nonempty M] {A : Set M} {v : α → M}
    {φ : (L[[A]]).Formula α} :
    Formula.equivSentence φ ∈ typeOver A v ↔ φ.Realize v :=
  CompleteType.formula_mem_typeOf

/-- The complete `1`-type over `A` realised by an element `a : M`. -/
abbrev typeOfElem [Nonempty M] (A : Set M) (a : M) : S₁ L A := typeOver A fun _ => a

@[simp]
theorem mem_typeOfElem [Nonempty M] {A : Set M} {a : M} {φ : Form1 L A} :
    φ ∈ typeOfElem A a ↔ (Formula.equivSentence.symm φ).Realize fun _ => a :=
  CompleteType.mem_typeOf

/-- The types over `A` that are realised in `M` itself are exactly the types of tuples of `M`. -/
theorem mem_realizedTypes_iff [Nonempty M] {A : Set M} {p : CompleteTypeOver L A α} :
    p ∈ (paramTheory L A).realizedTypes M α ↔ ∃ v : α → M, typeOver A v = p :=
  Iff.rfl

/-- The `1`-types over `A` realised in `M` itself are exactly the types of elements of `M`. -/
theorem mem_realizedTypes_one_iff [Nonempty M] {A : Set M} {p : S₁ L A} :
    p ∈ (paramTheory L A).realizedTypes M (Fin 1) ↔ ∃ a : M, typeOfElem A a = p := by
  refine ⟨fun ⟨v, hv⟩ => ⟨v 0, ?_⟩, fun ⟨a, ha⟩ => ⟨fun _ => a, ha⟩⟩
  have hv0 : (fun _ : Fin 1 => v 0) = v := by
    funext i
    fin_cases i
    rfl
  rw [← hv]
  exact congrArg _ hv0

/-- **Every complete type over `A` is realised in some model of `Th(M_A)`.**  This is
`FirstOrder.Language.Theory.exists_modelType_is_realized_in`, specialised to types over a
parameter set. -/
theorem exists_modelType_realizes (A : Set M) (p : CompleteTypeOver L A α) :
    ∃ N : (paramTheory L A).ModelType.{max u w, v, max u v w w'},
      p ∈ (paramTheory L A).realizedTypes N α :=
  Theory.exists_modelType_is_realized_in (paramTheory L A) p

/-- A complete type over `A` is realised in a model `N` of `Th(M_A)` exactly when some tuple of
`N` has it as its type. -/
theorem isRealizedIn_iff {A : Set M} (p : CompleteTypeOver L A α)
    (N : Type*) [(L[[A]]).Structure N] [Nonempty N] [N ⊨ paramTheory L A] :
    p ∈ (paramTheory L A).realizedTypes N α ↔ ∃ v : α → N, (paramTheory L A).typeOf v = p :=
  Iff.rfl

end TypesBasic

/-! ### Monotonicity in the parameter set -/

section Mono

variable {L : FirstOrder.Language.{u, v}} {M : Type w} [L.Structure M]

/-- Enlarging the parameter set enlarges the theory: the language map `L[[A]] → L[[B]]` induced by
an inclusion `A ⊆ B` carries `Th(M_A)` into `Th(M_B)`. -/
theorem onTheory_paramTheory_subset {A B : Set M} (hAB : A ⊆ B) :
    (L.lhomWithConstantsMap (Set.inclusion hAB)).onTheory (paramTheory L A) ⊆
      paramTheory L B := by
  rintro _ ⟨φ, hφ, rfl⟩
  simpa [Sentence.Realize] using
    (LHom.realize_onSentence (φ := L.lhomWithConstantsMap (Set.inclusion hAB)) (M := M) φ).2 hφ

end Mono

/-! ## ω-stability -/

section OmegaStable

variable {L : FirstOrder.Language.{u, v}} {T : L.Theory}

/-- A theory is **ω-stable** when, inside every model, over every countable parameter set, there
are only countably many complete `n`-types, for every `n ≥ 1`.

The shape of this definition matches the one used elsewhere in the wider Morley project, so that
the various chapters interoperate; `Submission.Morley.isOmegaStable_iff_mk_le_aleph0` gives the
equivalent formulation in terms of cardinals. -/
def IsOmegaStable (T : L.Theory) : Prop :=
  ∀ (M : T.ModelType.{u, v, w}) (A : Set M), A.Countable →
    ∀ n : ℕ, 1 ≤ n → Countable (CompleteTypeOver L A (Fin n))

/-- ω-stability, phrased with cardinals. -/
theorem isOmegaStable_iff_mk_le_aleph0 :
    IsOmegaStable.{u, v, w} T ↔ ∀ (M : T.ModelType.{u, v, w}) (A : Set M), #A ≤ ℵ₀ →
      ∀ n : ℕ, 1 ≤ n → #(CompleteTypeOver L A (Fin n)) ≤ ℵ₀ := by
  refine forall_congr' fun M => forall_congr' fun A => ?_
  rw [Cardinal.mk_le_aleph0_iff, Set.countable_coe_iff]
  exact imp_congr_right fun _ => forall_congr' fun n => imp_congr_right fun _ =>
    (Cardinal.mk_le_aleph0_iff).symm

/-- ω-stability, restricted to `1`-types and phrased with cardinals.  This is the form in which
ω-stability is used in the proof of Morley's theorem. -/
def OmegaStable (T : L.Theory) : Prop :=
  ∀ (M : T.ModelType.{u, v, w}) (A : Set M), #A ≤ ℵ₀ → #(S₁ L A) ≤ ℵ₀

theorem IsOmegaStable.omegaStable (h : IsOmegaStable.{u, v, w} T) : OmegaStable.{u, v, w} T :=
  fun M A hA => Cardinal.mk_le_aleph0_iff.2
    (h M A (Set.countable_coe_iff.1 (Cardinal.mk_le_aleph0_iff.1 hA)) 1 le_rfl)

/-- A language with at most `ℵ₀` symbols has a countable type of symbols.  This turns the
hypothesis `L.card ≤ ℵ₀` of Morley's theorem into the instance needed by
`Submission.Morley.exists_binaryTree_of_not_isOmegaStable`. -/
theorem countable_symbols_of_card_le_aleph0 (hL : L.card ≤ ℵ₀) : Countable L.Symbols :=
  Cardinal.mk_le_aleph0_iff.1 hL

/-! ### The binary-tree characterisation -/

/-- **A binary tree of formulas over a countable parameter set refutes ω-stability.**
Conversely to `Submission.Morley.exists_binaryTree_of_not_isOmegaStable`. -/
theorem not_isOmegaStable_of_binaryTree (M : T.ModelType.{u, v, w}) (A : Set M)
    (hA : A.Countable) (n : ℕ) (hn : 1 ≤ n) (t : BinaryTree (paramTheory L A) (Fin n)) :
    ¬ IsOmegaStable.{u, v, w} T :=
  fun h => t.not_countable (h M A hA n hn)

/-- **A binary tree of formulas in one free variable over a countable parameter set gives
`2 ^ ℵ₀` complete `1`-types**, and in particular refutes ω-stability. -/
theorem not_omegaStable_of_binaryTree (M : T.ModelType.{u, v, w}) (A : Set M)
    (hA : #A ≤ ℵ₀) (t : BinaryTree (paramTheory L A) (Fin 1)) :
    ¬ OmegaStable.{u, v, w} T :=
  fun h => absurd (h M A hA) (not_le.2 t.aleph0_lt_mk)

/-- **Failure of ω-stability produces a binary tree of formulas.**

If `T` fails to be ω-stable then, inside some model, over some countable parameter set `A`, there
is a full binary tree of formulas (in finitely many free variables, with parameters from `A`) each
of whose nodes is consistent with `Th(M_A)`, whose children imply their parent, and whose sibling
nodes are contradictory. -/
theorem exists_binaryTree_of_not_isOmegaStable [Countable L.Symbols]
    (h : ¬ IsOmegaStable.{u, v, w} T) :
    ∃ (M : T.ModelType.{u, v, w}) (A : Set M) (n : ℕ), A.Countable ∧ 1 ≤ n ∧
      Nonempty (BinaryTree (paramTheory L A) (Fin n)) := by
  rw [IsOmegaStable, not_forall] at h
  obtain ⟨M, hM⟩ := h
  rw [not_forall] at hM
  obtain ⟨A, hA⟩ := hM
  rw [Classical.not_imp] at hA
  obtain ⟨hAc, hA⟩ := hA
  rw [not_forall] at hA
  obtain ⟨n, hn⟩ := hA
  rw [Classical.not_imp] at hn
  obtain ⟨hn1, hn2⟩ := hn
  haveI := hAc.to_subtype
  exact ⟨M, A, n, hAc, hn1, exists_binaryTree_of_not_countable hn2⟩

/-- **Failure of ω-stability for `1`-types produces a binary tree of formulas in one free
variable.** -/
theorem exists_binaryTree_of_not_omegaStable [Countable L.Symbols]
    (h : ¬ OmegaStable.{u, v, w} T) :
    ∃ (M : T.ModelType.{u, v, w}) (A : Set M), #A ≤ ℵ₀ ∧
      Nonempty (BinaryTree (paramTheory L A) (Fin 1)) := by
  rw [OmegaStable, not_forall] at h
  obtain ⟨M, hM⟩ := h
  rw [not_forall] at hM
  obtain ⟨A, hA⟩ := hM
  rw [Classical.not_imp] at hA
  obtain ⟨hAc, hA⟩ := hA
  haveI := (Set.countable_coe_iff.1 (Cardinal.mk_le_aleph0_iff.1 hAc)).to_subtype
  refine ⟨M, A, hAc, exists_binaryTree_of_not_countable ?_⟩
  intro hc
  exact hA (Cardinal.mk_le_aleph0_iff.2 hc)

end OmegaStable

/-! ## The cardinality bound on type spaces -/

section Card

variable {L : FirstOrder.Language.{0, 0}} {M : Type} [L.Structure M]

omit [L.Structure M] in
/-- There are at most `#A + #L + #α + ℵ₀` formulas in the variables `α` with parameters in `A`. -/
theorem mk_sentence_le (A : Set M) (α : Type) :
    #(((L[[A]])[[α]]).Sentence) ≤ #A + L.card + #α + ℵ₀ := by
  have h1 : #(((L[[A]])[[α]]).Sentence) ≤
      #(Σ n, ((L[[A]])[[α]]).BoundedFormula Empty n) := by
    refine Cardinal.mk_le_of_injective (f := fun φ => ⟨0, φ⟩) ?_
    intro φ ψ h
    simpa using h
  refine h1.trans (BoundedFormula.card_le.trans (max_le ?_ ?_))
  · exact le_add_self
  · simp only [Cardinal.mk_eq_zero, Cardinal.lift_id, zero_add, Language.card_withConstants]
    calc L.card + #A + #α ≤ #A + L.card + #α := by rw [add_comm L.card]
      _ ≤ #A + L.card + #α + ℵ₀ := self_le_add_right _ _

/-- There are at most `2 ^ (#A + #L + #α + ℵ₀)` complete `α`-types over `A`: a complete type is a
set of sentences of `L[[A]][[α]]`. -/
theorem mk_completeTypeOver_le (A : Set M) (α : Type) :
    #(CompleteTypeOver L A α) ≤ 2 ^ (#A + L.card + #α + ℵ₀) := by
  have hinj : Function.Injective
      fun p : CompleteTypeOver L A α => (p : Set (((L[[A]])[[α]]).Sentence)) :=
    fun _ _ h => SetLike.coe_injective h
  refine (Cardinal.mk_le_of_injective hinj).trans ?_
  rw [Cardinal.mk_set]
  exact Cardinal.power_le_power_left two_ne_zero (mk_sentence_le A α)

/-- The trivial upper bound `#S₁(A) ≤ 2 ^ (#A + #L + ℵ₀)`. -/
theorem mk_S₁_le (A : Set M) : #(S₁ L A) ≤ 2 ^ (#A + L.card + ℵ₀) := by
  refine (mk_completeTypeOver_le A (Fin 1)).trans (Cardinal.power_le_power_left two_ne_zero ?_)
  simp only [Cardinal.mk_fin, Nat.cast_one]
  calc #A + L.card + 1 + ℵ₀ ≤ #A + L.card + ℵ₀ + ℵ₀ := by
        gcongr
        exact Cardinal.one_le_aleph0
    _ = #A + L.card + ℵ₀ := by rw [add_assoc, Cardinal.aleph0_add_aleph0]

end Card

/-! ## `κ`-stability -/

section Stability

variable {L : FirstOrder.Language.{0, 0}} {T : L.Theory}

/-- `T` is `κ`-**stable** when over any parameter set of size at most `κ` inside a model there are
at most `κ` complete `1`-types.  ω-stability is `ℵ₀`-stability, see
`Submission.Morley.stable_aleph0_iff_omegaStable`. -/
def Stable (κ : Cardinal.{0}) (T : L.Theory) : Prop :=
  ∀ (M : T.ModelType.{0, 0, 0}) (A : Set M), #A ≤ κ → #(S₁ L A) ≤ κ

theorem stable_aleph0_iff_omegaStable : Stable ℵ₀ T ↔ OmegaStable.{0, 0, 0} T := Iff.rfl

/-- **Failure of `κ`-stability produces a binary tree of formulas** over a parameter set of size
at most `κ`.

Together with `Submission.Morley.not_omegaStable_of_binaryTree` this reduces
`ω`-stable → `κ`-stable to the purely syntactic statement that a countable family of formulas only
mentions countably many parameters; that last reduction is *not* formalised here. -/
theorem exists_binaryTree_of_not_stable {κ : Cardinal.{0}} (hκ : ℵ₀ ≤ κ) (hL : L.card ≤ κ)
    (h : ¬ Stable κ T) :
    ∃ (M : T.ModelType.{0, 0, 0}) (A : Set M), #A ≤ κ ∧
      Nonempty (BinaryTree (paramTheory L A) (Fin 1)) := by
  rw [Stable, not_forall] at h
  obtain ⟨M, hM⟩ := h
  rw [not_forall] at hM
  obtain ⟨A, hA⟩ := hM
  rw [Classical.not_imp] at hA
  obtain ⟨hAc, hA⟩ := hA
  refine ⟨M, A, hAc, exists_binaryTree_of_lt_mk hκ ?_ (not_le.1 hA)⟩
  refine (mk_sentence_le A (Fin 1)).trans ?_
  simp only [Cardinal.mk_fin, Nat.cast_one]
  calc #A + L.card + 1 + ℵ₀ ≤ κ + κ + κ + κ := by
        gcongr
        exact Cardinal.one_le_aleph0.trans hκ
    _ = κ := by rw [Cardinal.add_eq_self hκ, Cardinal.add_eq_self hκ, Cardinal.add_eq_self hκ]

end Stability

end Submission.Morley
