import Mathlib
import Submission.Morley.Port.PartialEmbedding

/-!
# Saturated models and their uniqueness

This file defines saturated models and proves the classical uniqueness theorem: two
elementarily equivalent saturated models of the same cardinality are isomorphic.

## Main definitions

* `Submission.Morley.IsSaturated M` : every complete `1`-type over a parameter set `A ⊆ M`
  with `#A < #M` is realised in `M`. Following `Mathlib/ModelTheory/Types.lean`, a type over
  `A` is a `FirstOrder.Language.Theory.CompleteType` of the `L[[A]]`-theory of `M`.
* `Submission.Morley.IsSaturated' M` : the same for complete `n`-types.
* `Submission.Morley.IsPartialElem L G` : a set `G ⊆ M × N` of pairs is a *partial elementary
  map*, i.e. every first-order formula holds of a tuple of left coordinates iff it holds of the
  corresponding tuple of right coordinates. This "graph" presentation is what makes the
  transfinite unions in the back-and-forth argument painless; `graphOf` and
  `IsPartialElem.toPartialElementaryEmbedding` relate it to the bundled
  `FirstOrder.Language.PartialElementaryEmbedding` of `Submission.Morley.Port.PartialEmbedding`.

## Main results

* `Submission.Morley.exists_insert_of_isSaturated` : the extension step, the only place where
  saturation is used.
* `Submission.Morley.exists_total_isPartialElem` : the abstract transfinite back-and-forth.
* `Submission.Morley.nonempty_equiv_of_isSaturated` : **uniqueness of saturated models** — two
  elementarily equivalent saturated models of the same infinite cardinality are isomorphic.
* `Submission.Morley.nonempty_equiv_of_isSaturated_of_isComplete` : the same for two saturated
  models of a complete theory.
* `Submission.Morley.IsSaturated.exists_insert` : a saturated model is `#M`-homogeneous.
* `Submission.Morley.isSaturated_iff_isSaturated'` : for infinite models, saturation for
  `1`-types is equivalent to saturation for `n`-types.

## Implementation notes

The uniqueness theorem assumes `Infinite M`. This is used to keep the domain built up at stage
`i < (#M).ord` of the back-and-forth strictly smaller than `#M`; models of the theories occurring
in Morley's categoricity theorem are infinite anyway.
-/

namespace Submission.Morley

open Cardinal Set
open FirstOrder FirstOrder.Language

universe u v w w'

section PartialElem

variable (L : FirstOrder.Language.{u, v}) {M : Type w} {N : Type w'}
variable [L.Structure M] [L.Structure N]

/-- A set of pairs `G ⊆ M × N` is a *partial elementary map* when for every first-order formula
`φ` and every tuple of elements of `G`, `φ` holds of the tuple of left coordinates exactly when
it holds of the tuple of right coordinates.

Taking `φ` to be an equality this forces `G` to be the graph of an injective partial function.
Note that `IsPartialElem L ∅` says exactly that `M` and `N` are elementarily equivalent. -/
def IsPartialElem (G : Set (M × N)) : Prop :=
  ∀ ⦃k : ℕ⦄ (φ : L.Formula (Fin k)) (x : Fin k → M × N), (∀ i, x i ∈ G) →
    ((φ.Realize fun i => (x i).1) ↔ (φ.Realize fun i => (x i).2))

variable {L}

/-- A formula with an arbitrary type of free variables can be tested by restricting to the
finitely many variables it actually uses. -/
theorem realize_iff_of_forall_fin {ι : Type*} {a : ι → M} {b : ι → N}
    (h : ∀ (k : ℕ) (ψ : L.Formula (Fin k)) (x : Fin k → ι),
      (ψ.Realize (a ∘ x) ↔ ψ.Realize (b ∘ x)))
    (φ : L.Formula ι) : Formula.Realize φ a ↔ Formula.Realize φ b := by
  classical
  let e : (φ.freeVarFinset : Type _) ≃ Fin (Fintype.card (φ.freeVarFinset : Type _)) :=
    Fintype.equivFin _
  let x : Fin (Fintype.card (φ.freeVarFinset : Type _)) → ι := fun i => ((e.symm i : _) : ι)
  have keyM : Formula.Realize (Formula.relabel (⇑e) (φ.restrictFreeVar id)) (a ∘ x) ↔
      Formula.Realize φ a := by
    rw [Formula.realize_relabel]
    exact BoundedFormula.realize_restrictFreeVar a (by intro t; simp [x])
  have keyN : Formula.Realize (Formula.relabel (⇑e) (φ.restrictFreeVar id)) (b ∘ x) ↔
      Formula.Realize φ b := by
    rw [Formula.realize_relabel]
    exact BoundedFormula.realize_restrictFreeVar b (by intro t; simp [x])
  rw [← keyM, ← keyN]
  exact h _ _ x

namespace IsPartialElem

variable {G G' : Set (M × N)}

theorem mono (h : IsPartialElem L G') (hsub : G ⊆ G') : IsPartialElem L G :=
  fun _ φ x hx => h φ x fun i => hsub (hx i)

/-- A partial elementary map is a partial function. -/
theorem functional (h : IsPartialElem L G) {a : M} {b c : N} (hb : (a, b) ∈ G)
    (hc : (a, c) ∈ G) : b = c := by
  have := h ((Term.var (0 : Fin 2)).equal (Term.var (1 : Fin 2))) ![(a, b), (a, c)] (by
    intro i; fin_cases i <;> simpa)
  simpa using this.1 rfl

/-- A partial elementary map is injective. -/
theorem injOn (h : IsPartialElem L G) {a a' : M} {b : N} (hb : (a, b) ∈ G)
    (hb' : (a', b) ∈ G) : a = a' := by
  have := h ((Term.var (0 : Fin 2)).equal (Term.var (1 : Fin 2))) ![(a, b), (a', b)] (by
    intro i; fin_cases i <;> simpa)
  simpa using this.2 rfl

/-- The version of the defining property for an arbitrary type of free variables. -/
theorem realize_iff (h : IsPartialElem L G) {ι : Type*} (y : ι → M × N) (hy : ∀ i, y i ∈ G)
    (φ : L.Formula ι) :
    ((Formula.Realize φ fun i => (y i).1) ↔ (Formula.Realize φ fun i => (y i).2)) :=
  realize_iff_of_forall_fin (a := fun i => (y i).1) (b := fun i => (y i).2)
    (fun _ ψ z => h ψ (y ∘ z) fun i => hy (z i)) φ

theorem swap (h : IsPartialElem L G) : IsPartialElem L (Prod.swap '' G) := by
  intro k φ x hx
  have hx' : ∀ i, ((x i).2, (x i).1) ∈ G := by
    intro i
    obtain ⟨p, hp, hp'⟩ := hx i
    have h1 : (x i).1 = p.2 := by rw [← hp']; rfl
    have h2 : (x i).2 = p.1 := by rw [← hp']; rfl
    rw [h1, h2]
    exact hp
  exact (h φ (fun i => ((x i).2, (x i).1)) hx').symm

end IsPartialElem

/-- A union of a monotone family of partial elementary maps is a partial elementary map. -/
theorem isPartialElem_iUnion {ι : Type*} [LinearOrder ι] {C : ι → Set (M × N)}
    (hmono : Monotone C) (hC : ∀ i, IsPartialElem L (C i))
    (h0 : IsPartialElem L (∅ : Set (M × N))) : IsPartialElem L (⋃ i, C i) := by
  classical
  intro k φ x hx
  rcases isEmpty_or_nonempty (Fin k) with hk | hk
  · exact h0 φ x fun i => (hk.false i).elim
  · choose j hj using fun i => Set.mem_iUnion.1 (hx i)
    set s : Finset ι := Finset.image j Finset.univ with hs
    have hsne : s.Nonempty := ⟨j hk.some, by simp [hs]⟩
    exact hC (s.max' hsne) φ x fun i => hmono (s.le_max' (j i) (by simp [hs])) (hj i)

/-! ### Comparison with `FirstOrder.Language.PartialElementaryEmbedding`

`IsPartialElem` is the "graph" form of the bundled partial elementary embeddings of
`Submission.Morley.Port.PartialEmbedding`; the graph form is what makes transfinite unions
painless. The two notions determine each other. -/

/-- The graph of a partial elementary embedding, as a set of pairs. -/
def graphOf {A : Set M} {B : Set N} (f : A ↪ₚₑ[L] B) : Set (M × N) :=
  Set.range fun a : A => ((a : M), ((f a : N)))

theorem isPartialElem_graphOf {A : Set M} {B : Set N} (f : A ↪ₚₑ[L] B) :
    IsPartialElem L (graphOf f) := by
  intro k φ x hx
  choose a ha using hx
  have h1 : (fun i => (x i).1) = Subtype.val ∘ a := by funext i; rw [← ha i]; rfl
  have h2 : (fun i => (x i).2) = Subtype.val ∘ (f : A → B) ∘ a := by
    funext i; rw [← ha i]; rfl
  rw [h1, h2]
  exact f.map_formula' φ a

/-- Conversely, a partial elementary map is a partial elementary embedding between the
projections of its graph. -/
noncomputable def IsPartialElem.toPartialElementaryEmbedding {G : Set (M × N)}
    (hG : IsPartialElem L G) : (Prod.fst '' G) ↪ₚₑ[L] (Prod.snd '' G) := by
  classical
  have hex : ∀ a : (Prod.fst '' G), ∃ b : (Prod.snd '' G), ((a : M), (b : N)) ∈ G := by
    rintro ⟨a, p, hp, rfl⟩
    exact ⟨⟨p.2, ⟨p, hp, rfl⟩⟩, by simpa using hp⟩
  choose F hF using hex
  exact
    { toFun := F
      surjective' := by
        rintro ⟨b, p, hp, rfl⟩
        refine ⟨⟨p.1, ⟨p, hp, rfl⟩⟩, Subtype.ext ?_⟩
        exact hG.functional (hF ⟨p.1, ⟨p, hp, rfl⟩⟩) (by simpa using hp)
      map_formula' := fun _ φ x =>
        hG.realize_iff (fun i => ((x i : M), (F (x i) : N))) (fun i => hF (x i)) φ }

end PartialElem

section Saturation

variable {L : FirstOrder.Language.{0, 0}} {T : L.Theory}

/-- `M` is *saturated* if every complete `1`-type over a parameter set `A ⊆ M` of size `< #M`
is realised in `M`. Types over `A` are complete types of the theory of `M` in the language
`L[[A]]` with a constant for every element of `A`. -/
def IsSaturated (M : T.ModelType.{0, 0, 0}) : Prop :=
  ∀ A : Set M, #A < #M →
    ∀ p : ((L[[A]]).completeTheory M).CompleteType (Fin 1),
      p ∈ ((L[[A]]).completeTheory M).realizedTypes M (Fin 1)

/-- The `n`-type version of `IsSaturated`: every complete `n`-type over a parameter set of size
`< #M` is realised in `M`. -/
def IsSaturated' (M : T.ModelType.{0, 0, 0}) : Prop :=
  ∀ A : Set M, #A < #M → ∀ (n : ℕ) (p : ((L[[A]]).completeTheory M).CompleteType (Fin n)),
      p ∈ ((L[[A]]).completeTheory M).realizedTypes M (Fin n)

theorem IsSaturated'.isSaturated {M : T.ModelType.{0, 0, 0}} (h : IsSaturated' M) :
    IsSaturated M := fun A hA p => h A hA 1 p

/-- **Extension step.** If `N` is saturated and `G` is a partial elementary map from `M` into `N`
whose image is smaller than `N`, then any element of `M` can be added to the domain of `G`.

This is the only place where saturation is used. -/
theorem exists_insert_of_isSaturated {N : T.ModelType.{0, 0, 0}} (hN : IsSaturated N)
    {M : Type} [L.Structure M] [Nonempty M] {G : Set (M × N)} (hG : IsPartialElem L G)
    (hcard : #(Prod.snd '' G) < #N) (m : M) :
    ∃ n : N, IsPartialElem L (insert (m, n) G) := by
  classical
  set B : Set N := Prod.snd '' G with hBdef
  have hex : ∀ b : B, ∃ a : M, (a, (b : N)) ∈ G := by
    rintro ⟨b, p, hp, rfl⟩
    exact ⟨p.1, by simpa using hp⟩
  choose g hg using hex
  have helem : ∀ φ : L.Formula B,
      Formula.Realize φ g ↔ Formula.Realize φ ((↑) : B → N) :=
    fun φ => hG.realize_iff (fun b : B => (g b, (b : N))) hg φ
  letI : (Language.constantsOn (↥B)).Structure M := Language.constantsOn.structure g
  haveI hmod : M ⊨ (L[[(↥B)]]).completeTheory N := by
    refine ⟨fun ψ hψ => ?_⟩
    rw [← Formula.realize_equivSentence_symm_con (L := L) (α := ↥B) M ψ]
    exact (helem _).2
      ((Formula.realize_equivSentence_symm_con (L := L) (α := ↥B) N ψ).2 hψ)
  obtain ⟨w, hw⟩ :=
    hN B hcard (((L[[(↥B)]]).completeTheory N).typeOf (fun _ : Fin 1 => m))
  have hkey : ∀ χ : (L[[(↥B)]]).Formula (Fin 1),
      Formula.Realize χ w ↔ Formula.Realize χ (fun _ => m) := by
    intro χ
    have h1 : (Formula.equivSentence χ) ∈ ((L[[(↥B)]]).completeTheory N).typeOf w ↔
        (Formula.equivSentence χ) ∈
          (((L[[(↥B)]]).completeTheory N).typeOf (fun _ : Fin 1 => m)) := by
      rw [hw]
    simpa only [Theory.CompleteType.formula_mem_typeOf] using h1
  have hfin : ∀ φ : L.Formula (↥B ⊕ Fin 1),
      Formula.Realize φ (Sum.elim g (fun _ => m)) ↔
        Formula.Realize φ (Sum.elim ((↑) : ↥B → N) w) := by
    intro φ
    have hM := BoundedFormula.realize_constantsVarsEquiv (M := M) (α := ↥B) (β := Fin 1)
      (φ := BoundedFormula.constantsVarsEquiv.symm φ) (v := fun _ => m) (xs := default)
    have hN' := BoundedFormula.realize_constantsVarsEquiv (M := N) (α := ↥B) (β := Fin 1)
      (φ := BoundedFormula.constantsVarsEquiv.symm φ) (v := w) (xs := default)
    rw [Equiv.apply_symm_apply] at hM hN'
    exact (hM.trans (hkey _).symm).trans hN'.symm
  refine ⟨w 0, ?_⟩
  intro k ψ x hx
  set hmap : Fin k → ↥B ⊕ Fin 1 := fun i =>
    if h : x i ∈ G then Sum.inl ⟨(x i).2, ⟨x i, h, rfl⟩⟩ else Sum.inr 0 with hmapdef
  have hxeq : ∀ i, x i ∉ G → x i = (m, w 0) := by
    intro i hi
    rcases hx i with h' | h'
    · exact h'
    · exact absurd h' hi
  have e1 : ∀ i, Sum.elim g (fun _ : Fin 1 => m) (hmap i) = (x i).1 := by
    intro i
    by_cases h : x i ∈ G
    · simp only [hmapdef, dif_pos h, Sum.elim_inl]
      exact hG.injOn (hg ⟨(x i).2, ⟨x i, h, rfl⟩⟩) (by simpa using h)
    · simp [hmapdef, dif_neg h, hxeq i h]
  have e2 : ∀ i, Sum.elim ((↑) : ↥B → N) w (hmap i) = (x i).2 := by
    intro i
    by_cases h : x i ∈ G
    · simp [hmapdef, dif_pos h]
    · simp [hmapdef, dif_neg h, hxeq i h]
  have h1 : (fun i => (x i).1) = (Sum.elim g (fun _ : Fin 1 => m)) ∘ hmap := by
    funext i; exact (e1 i).symm
  have h2 : (fun i => (x i).2) = (Sum.elim ((↑) : ↥B → N) w) ∘ hmap := by
    funext i; exact (e2 i).symm
  have := hfin (Formula.relabel hmap ψ)
  rw [Formula.realize_relabel, Formula.realize_relabel] at this
  rw [h1, h2]
  exact this

/-- **A saturated model is `#M`-homogeneous**: any partial elementary self-map of `M` of size
`< #M` can be extended so that its domain contains a prescribed element. -/
theorem IsSaturated.exists_insert {M : T.ModelType.{0, 0, 0}} (hM : IsSaturated M)
    {G : Set (↥M × ↥M)} (hG : IsPartialElem L G) (hcard : #G < #M) (a : M) :
    ∃ b : M, IsPartialElem L (insert (a, b) G) :=
  exists_insert_of_isSaturated hM hG (lt_of_le_of_lt Cardinal.mk_image_le hcard) a

/-- Homogeneity, phrased with the bundled partial elementary embeddings. -/
theorem IsSaturated.exists_insert_graphOf {M : T.ModelType.{0, 0, 0}} (hM : IsSaturated M)
    {A B : Set (↥M)} (f : A ↪ₚₑ[L] B) (hcard : #A < #M) (a : M) :
    ∃ b : M, IsPartialElem L (insert (a, b) (graphOf f)) :=
  hM.exists_insert (isPartialElem_graphOf f) (lt_of_le_of_lt Cardinal.mk_range_le hcard) a

end Saturation

section BackAndForth

/-- Transfinite recursion producing a family of sets indexed by a well-order: the value at stage
`i` is computed from the union of the values at all earlier stages. -/
noncomputable def transRec {ι : Type*} [LinearOrder ι] [WellFoundedLT ι] {X : Type*}
    (σ : ι → Set X → Set X) (i : ι) : Set X :=
  (IsWellFounded.wf (r := ((· < ·) : ι → ι → Prop))).fix
    (fun i ih => σ i (⋃ j, ⋃ h : j < i, ih j h)) i

theorem transRec_eq {ι : Type*} [LinearOrder ι] [WellFoundedLT ι] {X : Type*}
    (σ : ι → Set X → Set X) (i : ι) :
    transRec σ i = σ i (⋃ j, ⋃ _ : j < i, transRec σ j) :=
  WellFounded.fix_eq _ _ i

variable (L : FirstOrder.Language.{u, v}) {M N : Type w}
variable [L.Structure M] [L.Structure N] [Nonempty M] [Nonempty N]

/-- One step of a back-and-forth construction: given the partial elementary map `P` built so far
and an element to be put into the domain (`Sum.inl`) or the range (`Sum.inr`), choose a pair of
`M × N` extending `P`. -/
noncomputable def bfNext (P : Set (M × N)) (a : M ⊕ N) : M × N :=
  Sum.elim
    (fun m : M => (m, Classical.epsilon fun n : N => IsPartialElem L (insert (m, n) P)))
    (fun n : N => (Classical.epsilon fun m : M => IsPartialElem L (insert (m, n) P), n)) a

theorem bfNext_inl_fst (P : Set (M × N)) (m : M) : (bfNext L P (Sum.inl m)).1 = m := rfl

theorem bfNext_inr_snd (P : Set (M × N)) (n : N) : (bfNext L P (Sum.inr n)).2 = n := rfl

theorem isPartialElem_insert_bfNext_inl {P : Set (M × N)} {m : M}
    (h : ∃ n : N, IsPartialElem L (insert (m, n) P)) :
    IsPartialElem L (insert (bfNext L P (Sum.inl m)) P) :=
  Classical.epsilon_spec h

theorem isPartialElem_insert_bfNext_inr {P : Set (M × N)} {n : N}
    (h : ∃ m : M, IsPartialElem L (insert (m, n) P)) :
    IsPartialElem L (insert (bfNext L P (Sum.inr n)) P) :=
  Classical.epsilon_spec h

variable {ι : Type w} [LinearOrder ι] [WellFoundedLT ι]

/-- The (singleton) set of pairs added at stage `i` of the back-and-forth construction. -/
noncomputable def bfChain (pick : ι → M ⊕ N) : ι → Set (M × N) :=
  transRec fun i P => {bfNext L P (pick i)}

/-- All pairs constructed strictly before stage `i`. -/
noncomputable def bfBelow (pick : ι → M ⊕ N) (i : ι) : Set (M × N) :=
  ⋃ j, ⋃ _ : j < i, bfChain L pick j

/-- All pairs constructed up to and including stage `i`. -/
noncomputable def bfUpto (pick : ι → M ⊕ N) (i : ι) : Set (M × N) :=
  ⋃ j, ⋃ _ : j ≤ i, bfChain L pick j

variable {L}

theorem bfChain_eq (pick : ι → M ⊕ N) (i : ι) :
    bfChain L pick i = {bfNext L (bfBelow L pick i) (pick i)} :=
  transRec_eq _ i

theorem bfUpto_mono (pick : ι → M ⊕ N) : Monotone (bfUpto L pick) := by
  intro i i' hii' p hp
  simp only [bfUpto, Set.mem_iUnion] at hp ⊢
  obtain ⟨j, hj, hp⟩ := hp
  exact ⟨j, hj.trans hii', hp⟩

theorem bfChain_subset_bfUpto (pick : ι → M ⊕ N) (i : ι) :
    bfChain L pick i ⊆ bfUpto L pick i := fun _ hp =>
  Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨le_rfl, hp⟩⟩

theorem bfBelow_subset_bfUpto (pick : ι → M ⊕ N) (i : ι) :
    bfBelow L pick i ⊆ bfUpto L pick i := by
  intro p hp
  simp only [bfBelow, Set.mem_iUnion] at hp
  obtain ⟨j, hj, hp⟩ := hp
  exact Set.mem_iUnion.2 ⟨j, Set.mem_iUnion.2 ⟨hj.le, hp⟩⟩

theorem bfUpto_eq (pick : ι → M ⊕ N) (i : ι) :
    bfUpto L pick i = bfBelow L pick i ∪ bfChain L pick i := by
  apply Set.Subset.antisymm
  · intro p hp
    simp only [bfUpto, Set.mem_iUnion] at hp
    obtain ⟨j, hj, hp⟩ := hp
    rcases lt_or_eq_of_le hj with hj' | rfl
    · exact Or.inl (Set.mem_iUnion.2 ⟨j, Set.mem_iUnion.2 ⟨hj', hp⟩⟩)
    · exact Or.inr hp
  · exact Set.union_subset (bfBelow_subset_bfUpto pick i) (bfChain_subset_bfUpto pick i)

theorem bfBelow_eq_iUnion (pick : ι → M ⊕ N) (i : ι) :
    bfBelow L pick i = ⋃ j : Set.Iio i, bfUpto L pick (j : ι) := by
  apply Set.Subset.antisymm
  · intro p hp
    simp only [bfBelow, Set.mem_iUnion] at hp
    obtain ⟨j, hj, hp⟩ := hp
    exact Set.mem_iUnion.2 ⟨⟨j, hj⟩, bfChain_subset_bfUpto pick j hp⟩
  · intro p hp
    obtain ⟨j, hp⟩ := Set.mem_iUnion.1 hp
    simp only [bfUpto, Set.mem_iUnion] at hp
    obtain ⟨k, hk, hp⟩ := hp
    exact Set.mem_iUnion.2 ⟨k, Set.mem_iUnion.2 ⟨lt_of_le_of_lt hk j.2, hp⟩⟩

theorem mk_bfBelow_le (pick : ι → M ⊕ N) (i : ι) :
    #(bfBelow L pick i) ≤ #(Set.Iio i) := by
  have hsub : bfBelow L pick i ⊆
      Set.range fun j : Set.Iio i => bfNext L (bfBelow L pick (j : ι)) (pick (j : ι)) := by
    intro p hp
    simp only [bfBelow, Set.mem_iUnion] at hp
    obtain ⟨j, hj, hp⟩ := hp
    rw [bfChain_eq] at hp
    exact ⟨⟨j, hj⟩, (Set.mem_singleton_iff.1 hp).symm⟩
  exact (Cardinal.mk_le_mk_of_subset hsub).trans Cardinal.mk_range_le

variable (L)

/-- **Transfinite back-and-forth.** If `M` and `N` both have cardinality `κ ≥ ℵ₀`, if the empty
partial map is elementary, and if any partial elementary map of size `< κ` can be extended
to cover an arbitrary element of `M` (resp. `N`), then there is a partial elementary map which
is defined everywhere and onto. -/
theorem exists_total_isPartialElem {κ : Cardinal.{w}} (hκ : ℵ₀ ≤ κ)
    (hMc : #M = κ) (hNc : #N = κ) (h0 : IsPartialElem L (∅ : Set (M × N)))
    (hfwd : ∀ G : Set (M × N), IsPartialElem L G → #G < κ → ∀ m : M,
      ∃ n : N, IsPartialElem L (insert (m, n) G))
    (hbwd : ∀ G : Set (M × N), IsPartialElem L G → #G < κ → ∀ n : N,
      ∃ m : M, IsPartialElem L (insert (m, n) G)) :
    ∃ F : Set (M × N), IsPartialElem L F ∧
      (∀ m : M, ∃ n : N, (m, n) ∈ F) ∧ (∀ n : N, ∃ m : M, (m, n) ∈ F) := by
  classical
  have hmkι : #(κ.ord.ToType) = κ := Cardinal.mk_ord_toType κ
  have hsum : #(M ⊕ N) = κ := by
    simp only [Cardinal.mk_sum, Cardinal.lift_id]
    rw [hMc, hNc, Cardinal.add_eq_self hκ]
  obtain ⟨pick, hsurj⟩ : ∃ f : κ.ord.ToType → M ⊕ N, Function.Surjective f := by
    obtain ⟨pe⟩ : Nonempty (κ.ord.ToType ≃ (M ⊕ N)) := Cardinal.eq.mp (by rw [hmkι, hsum])
    exact ⟨pe, pe.surjective⟩
  have hIio : ∀ i : κ.ord.ToType, #(Set.Iio i) < κ := by
    intro i
    have h := Cardinal.mk_Iio_lt (α := κ.ord.ToType) i (by rw [hmkι, Ordinal.type_toType])
    rwa [hmkι] at h
  have hDcard : ∀ i, #(bfBelow L pick i) < κ :=
    fun i => lt_of_le_of_lt (mk_bfBelow_le pick i) (hIio i)
  have hDelem : ∀ i, (∀ j, j < i → IsPartialElem L (bfUpto L pick j)) →
      IsPartialElem L (bfBelow L pick i) := by
    intro i IH
    rw [bfBelow_eq_iUnion]
    exact isPartialElem_iUnion (C := fun j : Set.Iio i => bfUpto L pick (j : κ.ord.ToType))
      (fun _ _ hjj' => bfUpto_mono pick hjj') (fun j => IH j.1 j.2) h0
  have hmain : ∀ i, IsPartialElem L (bfUpto L pick i) := by
    intro i
    induction i using WellFoundedLT.induction with
    | ind i IH =>
      have hD := hDelem i IH
      rw [bfUpto_eq, bfChain_eq, Set.union_comm, ← Set.insert_eq]
      obtain ⟨m, hm⟩ | ⟨n, hn⟩ :
          (∃ m, pick i = Sum.inl m) ∨ (∃ n, pick i = Sum.inr n) := by
        cases h : pick i with
        | inl m => exact Or.inl ⟨m, rfl⟩
        | inr n => exact Or.inr ⟨n, rfl⟩
      · rw [hm]
        exact isPartialElem_insert_bfNext_inl L (hfwd _ hD (hDcard i) m)
      · rw [hn]
        exact isPartialElem_insert_bfNext_inr L (hbwd _ hD (hDcard i) n)
  refine ⟨⋃ i, bfUpto L pick i, isPartialElem_iUnion (bfUpto_mono pick) hmain h0, ?_, ?_⟩
  · intro m
    obtain ⟨i, hi⟩ := hsurj (Sum.inl m)
    refine ⟨(bfNext L (bfBelow L pick i) (Sum.inl m)).2,
      Set.mem_iUnion.2 ⟨i, bfChain_subset_bfUpto pick i ?_⟩⟩
    rw [bfChain_eq, hi]
    exact Set.mem_singleton_iff.2 rfl
  · intro n
    obtain ⟨i, hi⟩ := hsurj (Sum.inr n)
    refine ⟨(bfNext L (bfBelow L pick i) (Sum.inr n)).1,
      Set.mem_iUnion.2 ⟨i, bfChain_subset_bfUpto pick i ?_⟩⟩
    rw [bfChain_eq, hi]
    exact Set.mem_singleton_iff.2 rfl

variable {L}

omit [Nonempty M] [Nonempty N] in
/-- A partial elementary map which is defined everywhere and onto is an isomorphism. -/
theorem nonempty_equiv_of_total {F : Set (M × N)} (hF : IsPartialElem L F)
    (hdom : ∀ m : M, ∃ n : N, (m, n) ∈ F) (hcod : ∀ n : N, ∃ m : M, (m, n) ∈ F) :
    Nonempty (M ≃[L] N) := by
  classical
  choose f hf using hdom
  have hemb : ∀ ⦃k : ℕ⦄ (φ : L.Formula (Fin k)) (x : Fin k → M),
      Formula.Realize φ (f ∘ x) ↔ Formula.Realize φ x := fun k φ x =>
    (hF φ (fun i => (x i, f (x i))) fun i => hf (x i)).symm
  let g : M ↪ₑ[L] N := ⟨f, hemb⟩
  have hinj : Function.Injective f := g.injective
  have hsurj : Function.Surjective f := by
    intro n
    obtain ⟨m, hm⟩ := hcod n
    exact ⟨m, hF.functional (hf m) hm⟩
  exact ⟨{ toEquiv := Equiv.ofBijective f ⟨hinj, hsurj⟩
           map_fun' := fun fn x => g.map_fun fn x
           map_rel' := fun r x => g.map_rel r x }⟩

end BackAndForth

section Uniqueness

variable {L : FirstOrder.Language.{0, 0}} {T : L.Theory}

/-- Elementarily equivalent structures are exactly those for which the empty partial map is
elementary. -/
theorem isPartialElem_empty_of_elementarilyEquivalent {M N : Type}
    [L.Structure M] [L.Structure N] (h : M ≅[L] N) :
    IsPartialElem L (∅ : Set (M × N)) := by
  intro k φ x hx
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have hM0 : Formula.Realize φ (fun i => (x i).1) ↔
        Formula.Realize (Formula.relabel Fin.elim0 φ) (default : Empty → M) := by
      rw [Formula.realize_relabel]
      exact iff_of_eq (congrArg (Formula.Realize φ) (funext fun i => i.elim0))
    have hN0 : Formula.Realize φ (fun i => (x i).2) ↔
        Formula.Realize (Formula.relabel Fin.elim0 φ) (default : Empty → N) := by
      rw [Formula.realize_relabel]
      exact iff_of_eq (congrArg (Formula.Realize φ) (funext fun i => i.elim0))
    exact hM0.trans (((elementarilyEquivalent_iff.1 h) _).trans hN0.symm)
  · exact absurd (hx ⟨0, hk⟩) (Set.notMem_empty _)

/-- **Uniqueness of saturated models.** Two elementarily equivalent saturated models of the same
infinite cardinality are isomorphic. -/
theorem nonempty_equiv_of_isSaturated {M N : T.ModelType.{0, 0, 0}} [Infinite M]
    (hM : IsSaturated M) (hN : IsSaturated N) (hcard : (#M : Cardinal) = #N)
    (hMN : (M : Type) ≅[L] (N : Type)) : Nonempty (M ≃[L] N) := by
  classical
  have hκ : ℵ₀ ≤ (#M : Cardinal) := Cardinal.infinite_iff.1 inferInstance
  have h0 := isPartialElem_empty_of_elementarilyEquivalent hMN
  have hfwd : ∀ G : Set (↥M × ↥N), IsPartialElem L G → #G < (#M : Cardinal) →
      ∀ m : ↥M, ∃ n : ↥N, IsPartialElem L (insert (m, n) G) := by
    intro G hG hGc m
    exact exists_insert_of_isSaturated hN hG
      (lt_of_le_of_lt Cardinal.mk_image_le (hGc.trans_eq hcard)) m
  have hbwd : ∀ G : Set (↥M × ↥N), IsPartialElem L G → #G < (#M : Cardinal) →
      ∀ n : ↥N, ∃ m : ↥M, IsPartialElem L (insert (m, n) G) := by
    intro G hG hGc n
    have himg : Prod.snd '' (Prod.swap '' G) = Prod.fst '' G := by
      rw [Set.image_image]; rfl
    have hc' : #(Prod.snd '' (Prod.swap '' G)) < (#M : Cardinal) := by
      rw [himg]
      exact lt_of_le_of_lt Cardinal.mk_image_le hGc
    obtain ⟨m, hm⟩ := exists_insert_of_isSaturated hM hG.swap hc' n
    refine ⟨m, ?_⟩
    have h2 := hm.swap
    rw [Set.image_insert_eq, Set.image_image] at h2
    simpa using h2
  obtain ⟨F, hF, hdom, hcod⟩ := exists_total_isPartialElem L hκ rfl hcard.symm h0 hfwd hbwd
  exact nonempty_equiv_of_total hF hdom hcod

/-- **Uniqueness of saturated models of a complete theory.** For a complete theory, any two
saturated models of the same infinite cardinality are isomorphic. -/
theorem nonempty_equiv_of_isSaturated_of_isComplete {M N : T.ModelType.{0, 0, 0}} [Infinite M]
    (hT : T.IsComplete) (hM : IsSaturated M) (hN : IsSaturated N)
    (hcard : (#M : Cardinal) = #N) : Nonempty (M ≃[L] N) :=
  nonempty_equiv_of_isSaturated hM hN hcard
    ((Theory.IsComplete.isComplete_iff_models_elementarily_equivalent.1 hT).2 M N)

end Uniqueness

section NTypes

variable {L : FirstOrder.Language.{0, 0}} {T : L.Theory}

/-- A saturated model absorbs finitely many new elements at once: any partial elementary map into
a saturated `M` of size `< #M` extends to one whose domain contains a prescribed finite tuple. -/
theorem exists_extend_fin_of_isSaturated {M : T.ModelType.{0, 0, 0}} [Infinite M]
    (hM : IsSaturated M) {M' : Type} [L.Structure M'] [Nonempty M'] :
    ∀ (n : ℕ) (v : Fin n → M') (G : Set (M' × ↥M)), IsPartialElem L G → #G < #M →
      ∃ w : Fin n → M, IsPartialElem L (G ∪ Set.range fun i => (v i, w i)) := by
  have hℵ : ℵ₀ ≤ (#M : Cardinal) := Cardinal.infinite_iff.1 inferInstance
  intro n
  induction n with
  | zero =>
    intro v G hG _
    exact ⟨Fin.elim0, by simpa using hG⟩
  | succ n IH =>
    intro v G hG hcard
    obtain ⟨b, hb⟩ := exists_insert_of_isSaturated hM hG
      (lt_of_le_of_lt Cardinal.mk_image_le hcard) (v 0)
    have hcard' : #(insert (v 0, b) G : Set (M' × ↥M)) < #M :=
      lt_of_le_of_lt Cardinal.mk_insert_le
        (Cardinal.add_lt_of_lt hℵ hcard (lt_of_lt_of_le Cardinal.one_lt_aleph0 hℵ))
    obtain ⟨w', hw'⟩ := IH (fun i => v i.succ) (insert (v 0, b) G) hb hcard'
    refine ⟨Fin.cons b w', ?_⟩
    have hrange :
        (Set.range fun i : Fin (n + 1) => (v i, (Fin.cons b w' : Fin (n + 1) → ↥M) i)) =
          insert ((v 0, b) : M' × ↥M) (Set.range fun i : Fin n => (v i.succ, w' i)) := by
      apply Set.Subset.antisymm
      · rintro _ ⟨i, rfl⟩
        rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
        · exact Or.inl (by simp)
        · exact Or.inr ⟨j, by simp⟩
      · rintro q (rfl | ⟨j, rfl⟩)
        · exact ⟨0, by simp⟩
        · exact ⟨j.succ, by simp⟩
    rw [hrange, Set.union_insert, ← Set.insert_union]
    exact hw'

/-- **Saturation for `n`-types follows from saturation for `1`-types.** -/
theorem IsSaturated.isSaturated' {M : T.ModelType.{0, 0, 0}} [Infinite M] (hM : IsSaturated M) :
    IsSaturated' M := by
  classical
  intro A hA n p
  obtain ⟨M', v, hv⟩ := Theory.exists_modelType_is_realized_in _ p
  letI : L.Structure ↥M' := (L.lhomWithConstants (↥A)).reduct ↥M'
  -- the parameters of `M'`, as named by the constants of `L[[A]]`
  set c : ↥A → ↥M' := fun a => (L.con a : ↥M') with hc
  have key : ∀ φ : L.Formula (↥A),
      Formula.Realize φ c ↔ Formula.Realize φ ((↑) : ↥A → ↥M) := by
    intro φ
    have h1 : (↥M' ⊨ Formula.equivSentence φ) ↔ Formula.Realize φ c :=
      Formula.realize_equivSentence (M := ↥M') (L := L) (α := ↥A) φ
    have h2 : (↥M ⊨ Formula.equivSentence φ) ↔ Formula.Realize φ ((↑) : ↥A → ↥M) :=
      Formula.realize_equivSentence (M := ↥M) (L := L) (α := ↥A) φ
    exact h1.symm.trans
      ((Language.realize_iff_of_model_completeTheory (↥M) ↥M' _).trans h2)
  -- the identity on the parameters is a partial elementary map from `M'` to `M`
  set G₀ : Set (↥M' × ↥M) := Set.range fun a : ↥A => (c a, (a : ↥M)) with hG₀
  have hG₀elem : IsPartialElem L G₀ := by
    intro k ψ x hx
    choose a ha using hx
    have h1 : (fun i => (x i).1) = c ∘ a := by funext i; rw [← ha i]; rfl
    have h2 : (fun i => (x i).2) = ((↑) : ↥A → ↥M) ∘ a := by funext i; rw [← ha i]; rfl
    rw [h1, h2, ← Formula.realize_relabel, ← Formula.realize_relabel]
    exact key _
  have hG₀card : #G₀ < #M := lt_of_le_of_lt Cardinal.mk_range_le hA
  obtain ⟨w, hw⟩ := exists_extend_fin_of_isSaturated hM n v G₀ hG₀elem hG₀card
  refine ⟨w, ?_⟩
  -- read off that `w` realises `p`
  have hraw : ∀ φ : L.Formula (↥A ⊕ Fin n), Formula.Realize φ (Sum.elim c v) ↔
      Formula.Realize φ (Sum.elim ((↑) : ↥A → ↥M) w) := by
    intro φ
    have hy : ∀ z : ↥A ⊕ Fin n,
        (Sum.elim (fun a : ↥A => (c a, (a : ↥M))) (fun i => (v i, w i)) z) ∈
          G₀ ∪ Set.range fun i => (v i, w i) := by
      rintro (a | i)
      · exact Or.inl ⟨a, rfl⟩
      · exact Or.inr ⟨i, rfl⟩
    have h := hw.realize_iff
      (Sum.elim (fun a : ↥A => (c a, (a : ↥M))) fun i => (v i, w i)) hy φ
    have e1 : (fun z => (Sum.elim (fun a : ↥A => (c a, (a : ↥M)))
        (fun i => (v i, w i)) z).1) = Sum.elim c v := by
      funext z; rcases z with a | i <;> rfl
    have e2 : (fun z => (Sum.elim (fun a : ↥A => (c a, (a : ↥M)))
        (fun i => (v i, w i)) z).2) = Sum.elim ((↑) : ↥A → ↥M) w := by
      funext z; rcases z with a | i <;> rfl
    rwa [e1, e2] at h
  have hchi : ∀ χ : (L[[(↥A)]]).Formula (Fin n),
      Formula.Realize χ w ↔ Formula.Realize χ v := by
    intro χ
    have hM'χ := BoundedFormula.realize_constantsVarsEquiv (M := ↥M') (α := ↥A)
      (β := Fin n) (φ := χ) (v := v) (xs := default)
    have hMχ := BoundedFormula.realize_constantsVarsEquiv (M := ↥M) (α := ↥A)
      (β := Fin n) (φ := χ) (v := w) (xs := default)
    exact hMχ.symm.trans ((hraw _).symm.trans hM'χ)
  rw [← hv]
  refine SetLike.ext fun ψ => ?_
  simp only [Theory.CompleteType.mem_typeOf]
  exact hchi _

/-- For infinite models, saturation for `1`-types and for `n`-types agree. -/
theorem isSaturated_iff_isSaturated' {M : T.ModelType.{0, 0, 0}} [Infinite M] :
    IsSaturated M ↔ IsSaturated' M :=
  ⟨IsSaturated.isSaturated', IsSaturated'.isSaturated⟩

end NTypes

end Submission.Morley
