import Mathlib

/-!
# Morleyization, and the back-and-forth isomorphism it enables

Given a language `L`, its **Morleyization** `morleyLang L` is the purely relational language whose
`n`-ary relation symbols are the `L`-formulas in the free variables `Fin n`.  Every `L`-structure
`M` becomes a `morleyLang L`-structure by interpreting the relation symbol `φ` as the set of
tuples satisfying `φ`.

The point of the construction is that in a purely relational language everything about
substructures degenerates:

* `Substructure.closure_eq_of_isRelational` makes substructures literally *sets*;
* `Substructure.fg_iff_finite` makes *finitely generated* mean *finite*;
* embeddings between substructures become exactly *partial elementary maps*.

Consequently Mathlib's `FirstOrder.Language.equiv_between_cg` — which performs a completely
general back-and-forth argument for `PartialEquiv`s of substructures — becomes, when applied in
`morleyLang L`, a back-and-forth argument for partial *elementary* maps.  This is the engine of
the isomorphism step in Vaught's two-cardinal theorem.

## Main definitions

* `Submission.Morley.morleyLang`: the Morleyized language.
* `Submission.Morley.morleyStructure`: the induced structure on any `L`-structure.
* `Submission.Morley.morleyRel`: the atomic `morleyLang L`-formula attached to an `L`-formula.
* `Submission.Morley.morleySub`: an arbitrary subset viewed as a `morleyLang L`-substructure.
* `Submission.Morley.SameType`: two finite tuples (in possibly different structures) satisfy the
  same `L`-formulas.
* `Submission.Morley.IsTypeExtensionPair`: the back-and-forth hypothesis, phrased with types.

## Main results

* `Submission.Morley.realize_morleyRel`: **the transfer lemma**.  An `L`-formula holds in `M` iff
  the corresponding atomic `morleyLang L`-formula does.
* `Submission.Morley.embeddingOfElementary` / `Submission.Morley.realize_iff_of_embedding`:
  `morleyLang L`-embeddings of substructures are exactly the partial elementary `L`-maps.
* `Submission.Morley.toLEquiv`: a `morleyLang L`-isomorphism is in particular an
  `L`-isomorphism.
* `Submission.Morley.sameType_iff_boundedFormula`: `SameType` may equivalently be tested against
  `L.BoundedFormula Empty k`, which is the form in which types of tuples appear in
  `Submission.Morley.TwoCardinal`.
* `Submission.Morley.isExtensionPair_of_isTypeExtensionPair`: a type-extension pair of
  `L`-structures is an extension pair of Morleyized structures, in Mathlib's sense.
* `Submission.Morley.nonempty_equiv_of_same_types_of_countable`: **the payload**.  Two countable
  structures forming a type-extension pair in both directions, with a designated pair of finite
  tuples of the same type, are isomorphic by an isomorphism matching those tuples.
-/

namespace Submission.Morley

open Set FirstOrder FirstOrder.Language

variable {L : FirstOrder.Language.{0, 0}}

/-! ## The Morleyized language -/

/-- The **Morleyization** of `L`: the purely relational language whose `n`-ary relation symbols
are the `L`-formulas in the free variables `Fin n`. -/
def morleyLang (L : FirstOrder.Language.{0, 0}) : FirstOrder.Language.{0, 0} where
  Functions := fun _ => Empty
  Relations := fun n => L.Formula (Fin n)

instance morleyLang_isRelational (L : FirstOrder.Language.{0, 0}) :
    (morleyLang L).IsRelational :=
  fun _ => inferInstanceAs (IsEmpty Empty)

/-- Every `L`-structure is a `morleyLang L`-structure: the relation symbol `φ` is interpreted as
the set of tuples satisfying `φ`. -/
instance morleyStructure (M : Type*) [L.Structure M] : (morleyLang L).Structure M where
  funMap {_} f := isEmptyElim f
  RelMap {n} (φ : L.Formula (Fin n)) x := φ.Realize x

@[simp]
theorem morley_relMap {M : Type*} [L.Structure M] {n : ℕ} (φ : L.Formula (Fin n))
    (x : Fin n → M) :
    @Structure.RelMap (morleyLang L) M _ n φ x ↔ φ.Realize x :=
  Iff.rfl

/-! ## The transfer lemma -/

/-- The atomic `morleyLang L`-formula attached to an `L`-formula `φ` in `n` free variables: the
`n`-ary relation symbol `φ` applied to the variables `x₀, …, xₙ₋₁`. -/
def morleyRel {n : ℕ} (φ : L.Formula (Fin n)) : (morleyLang L).Formula (Fin n) :=
  Relations.formula (L := morleyLang L) (n := n) φ fun i => Term.var i

/-- **Transfer lemma.**  An `L`-formula holds of a tuple in `M` if and only if the corresponding
atomic `morleyLang L`-formula does. -/
@[simp]
theorem realize_morleyRel {M : Type*} [L.Structure M] {n : ℕ} (φ : L.Formula (Fin n))
    (x : Fin n → M) : (morleyRel φ).Realize x ↔ φ.Realize x := by
  rw [morleyRel, Formula.realize_rel]
  simp

/-! ## Substructures of a Morleyized structure are just sets -/

/-- Any subset of `M` is a `morleyLang L`-substructure, since `morleyLang L` has no function
symbols. -/
def morleySub {M : Type*} [L.Structure M] (s : Set M) : (morleyLang L).Substructure M where
  carrier := s
  fun_mem {_} f := isEmptyElim f

@[simp]
theorem coe_morleySub {M : Type*} [L.Structure M] (s : Set M) :
    ((morleySub (L := L) s : (morleyLang L).Substructure M) : Set M) = s := rfl

@[simp]
theorem mem_morleySub {M : Type*} [L.Structure M] {s : Set M} {x : M} :
    x ∈ morleySub (L := L) s ↔ x ∈ s := Iff.rfl

theorem morleySub_coe {M : Type*} [L.Structure M] (A : (morleyLang L).Substructure M) :
    morleySub (L := L) (A : Set M) = A := by
  ext x; rfl

/-- In the Morleyized language, a substructure carried by a finite set is finitely generated. -/
theorem morleySub_fg {M : Type*} [L.Structure M] {s : Set M} (hs : s.Finite) :
    (morleySub (L := L) s).FG := by
  refine ⟨hs.toFinset, ?_⟩
  ext x
  simp [Substructure.mem_closure_iff_of_isRelational]

/-! ## Embeddings are exactly partial elementary maps -/

section Embeddings

variable {M N : Type*} [L.Structure M] [L.Structure N]

/-- A `morleyLang L`-embedding of a substructure of `M` into `N` preserves and reflects every
`L`-formula: it *is* a partial elementary map. -/
theorem realize_iff_of_embedding {A : (morleyLang L).Substructure M}
    (f : A ↪[morleyLang L] N) {n : ℕ} (φ : L.Formula (Fin n)) (x : Fin n → A) :
    φ.Realize (fun i => ((x i : M))) ↔ φ.Realize fun i => f (x i) :=
  (f.map_rel φ x).symm

/-- Conversely, a partial elementary map on a substructure of a Morleyized structure is a
`morleyLang L`-embedding. -/
def embeddingOfElementary (A : (morleyLang L).Substructure M) (f : A → N)
    (hf : ∀ (n : ℕ) (φ : L.Formula (Fin n)) (x : Fin n → A),
      φ.Realize (fun i => ((x i : M))) ↔ φ.Realize fun i => f (x i)) :
    A ↪[morleyLang L] N where
  toFun := f
  inj' := by
    intro u v huv
    have h := hf 2 ((Term.var 0).equal (Term.var 1)) ![u, v]
    simp only [Formula.realize_equal, Term.realize_var, Matrix.cons_val_zero,
      Matrix.cons_val_one] at h
    exact Subtype.ext (h.2 huv)
  map_fun' {_} f _ := isEmptyElim f
  map_rel' {n} φ x := (hf n φ x).symm

@[simp]
theorem embeddingOfElementary_apply (A : (morleyLang L).Substructure M) (f : A → N)
    (hf : ∀ (n : ℕ) (φ : L.Formula (Fin n)) (x : Fin n → A),
      φ.Realize (fun i => ((x i : M))) ↔ φ.Realize fun i => f (x i)) (y : A) :
    embeddingOfElementary A f hf y = f y := rfl

/-- A `morleyLang L`-embedding between (whole) Morleyized structures preserves and reflects every
`L`-formula. -/
theorem realize_iff_of_morleyEmbedding (f : M ↪[morleyLang L] N) {n : ℕ}
    (φ : L.Formula (Fin n)) (x : Fin n → M) :
    φ.Realize x ↔ φ.Realize fun i => f (x i) :=
  (f.map_rel φ x).symm

/-- A `morleyLang L`-isomorphism preserves and reflects every `L`-formula. -/
theorem realize_iff_of_morleyEquiv (e : M ≃[morleyLang L] N) {n : ℕ}
    (φ : L.Formula (Fin n)) (x : Fin n → M) :
    φ.Realize x ↔ φ.Realize fun i => e (x i) :=
  (e.map_rel φ x).symm

/-- The `L`-formula `f (x₀, …, xₙ₋₁) = xₙ`. -/
def funEqF {n : ℕ} (f : L.Functions n) : L.Formula (Fin (n + 1)) :=
  (Term.func f fun i => Term.var i.castSucc).equal (Term.var (Fin.last n))

@[simp]
theorem realize_funEqF {P : Type*} [L.Structure P] {n : ℕ} (f : L.Functions n)
    (x : Fin n → P) (y : P) :
    (funEqF f).Realize (Fin.snoc x y) ↔ Structure.funMap f x = y := by
  simp [funEqF, Formula.realize_equal]

/-- A `morleyLang L`-isomorphism is in particular an `L`-isomorphism.  (It is even elementary,
by `realize_iff_of_morleyEquiv`.) -/
def toLEquiv (e : M ≃[morleyLang L] N) : M ≃[L] N where
  toEquiv := e.toEquiv
  map_fun' {n} f x := by
    have h := realize_iff_of_morleyEquiv e (funEqF f)
      (Fin.snoc x (Structure.funMap f x) : Fin (n + 1) → M)
    have h2 : (fun i => e ((Fin.snoc x (Structure.funMap f x) : Fin (n + 1) → M) i)) =
        (Fin.snoc (fun i => e (x i)) (e (Structure.funMap f x)) : Fin (n + 1) → N) := by
      funext i
      refine Fin.lastCases ?_ ?_ i <;> simp
    rw [h2, realize_funEqF, realize_funEqF] at h
    exact (h.1 rfl).symm
  map_rel' {n} r x := by
    have h := realize_iff_of_morleyEquiv e (Relations.formula r fun i => Term.var i) x
    simp only [Formula.realize_rel, Term.realize_var] at h
    exact h.symm

@[simp]
theorem toLEquiv_apply (e : M ≃[morleyLang L] N) (x : M) : toLEquiv e x = e x := rfl

end Embeddings

/-! ## Types of tuples -/

/-- Two finite tuples, in possibly different `L`-structures, have the **same `L`-type**: they
satisfy exactly the same `L`-formulas. -/
def SameType (L : FirstOrder.Language.{0, 0}) {M N : Type*} [L.Structure M] [L.Structure N]
    {k : ℕ} (a : Fin k → M) (a' : Fin k → N) : Prop :=
  ∀ φ : L.Formula (Fin k), φ.Realize a ↔ φ.Realize a'

namespace SameType

variable {M N : Type*} [L.Structure M] [L.Structure N] {k : ℕ} {a : Fin k → M} {a' : Fin k → N}

theorem refl (a : Fin k → M) : SameType L a a := fun _ => Iff.rfl

theorem symm (h : SameType L a a') : SameType L a' a := fun φ => (h φ).symm

theorem trans {P : Type*} [L.Structure P] {a'' : Fin k → P} (h : SameType L a a')
    (h' : SameType L a' a'') : SameType L a a'' := fun φ => (h φ).trans (h' φ)

/-- Same-typed tuples have the same pattern of equalities among their entries. -/
theorem eq_iff (h : SameType L a a') (i j : Fin k) : a i = a j ↔ a' i = a' j := by
  have := h ((Term.var i).equal (Term.var j))
  simpa only [Formula.realize_equal, Term.realize_var] using this

/-- Same-typed tuples stay same-typed after an arbitrary reindexing. -/
theorem comp (h : SameType L a a') {n : ℕ} (σ : Fin n → Fin k) :
    SameType L (a ∘ σ) (a' ∘ σ) := by
  intro φ
  have := h (φ.relabel σ)
  rwa [Formula.realize_relabel, Formula.realize_relabel] at this

end SameType

/-- An elementary embedding matches same-typed tuples.  (In particular, a tuple from an
elementary substructure has the same type computed inside the substructure as computed in the
ambient structure.) -/
theorem sameType_of_elementaryEmbedding {M N : Type*} [L.Structure M] [L.Structure N]
    (f : M ↪ₑ[L] N) {k : ℕ} (a : Fin k → M) : SameType L a fun i => f (a i) :=
  fun φ => (f.map_formula φ a).symm

/-- `SameType` may equivalently be tested against bounded formulas over the empty parameter
type, which is the form in which types of tuples show up in `Submission.Morley.TwoCardinal`. -/
theorem sameType_iff_boundedFormula {M N : Type*} [L.Structure M] [L.Structure N] {k : ℕ}
    (a : Fin k → M) (a' : Fin k → N) :
    SameType L a a' ↔
      ∀ ψ : L.BoundedFormula Empty k,
        (ψ.Realize (default : Empty → M) a ↔ ψ.Realize (default : Empty → N) a') := by
  constructor
  · intro h ψ
    have hM : ((a ∘ Sum.elim (fun e : Empty => e.elim) id) ∘ Sum.inl) = (default : Empty → M) :=
      funext fun e => e.elim
    have hN : ((a' ∘ Sum.elim (fun e : Empty => e.elim) id) ∘ Sum.inl) = (default : Empty → N) :=
      funext fun e => e.elim
    have h' := h (Formula.relabel (Sum.elim (fun e : Empty => e.elim) id) ψ.toFormula)
    rw [Formula.realize_relabel, Formula.realize_relabel,
      BoundedFormula.realize_toFormula, BoundedFormula.realize_toFormula, hM, hN] at h'
    exact h'
  · intro h φ
    have h' := h (BoundedFormula.relabel Sum.inr φ)
    rwa [Formula.realize_relabel_sumInr, Formula.realize_relabel_sumInr] at h'

/-! ## The back-and-forth hypothesis -/

/-- `IsTypeExtensionPair L M N` says that the types realized in `M` over finite tuples are also
realized in `N` over matching tuples: if `a` and `a'` have the same `L`-type and `m : M`, then
some `n : N` makes `a ⌢ m` and `a' ⌢ n` have the same `L`-type.

This is exactly the "forth" half of a back-and-forth system, phrased with types.  In
`Submission.Morley.nonempty_equiv_of_same_types_of_countable` it is required in both
directions. -/
def IsTypeExtensionPair (L : FirstOrder.Language.{0, 0}) (M N : Type*) [L.Structure M]
    [L.Structure N] : Prop :=
  ∀ (k : ℕ) (a : Fin k → M) (a' : Fin k → N), SameType L a a' → ∀ m : M,
    ∃ n : N, SameType L (Fin.snoc a m) (Fin.snoc a' n)

/-! ## Partial equivalences from same-typed tuples -/

section Tuples

variable {M N : Type*} [L.Structure M] [L.Structure N] {k : ℕ} {a : Fin k → M} {a' : Fin k → N}

/-- An index `i` with `a i = y`, for `y` in the range of `a`. -/
noncomputable def rangeIdx (a : Fin k → M) (y : ↥(morleySub (L := L) (Set.range a))) : Fin k :=
  Classical.choose (show ∃ i, a i = (y : M) from y.2)

theorem rangeIdx_spec (a : Fin k → M) (y : ↥(morleySub (L := L) (Set.range a))) :
    a (rangeIdx a y) = (y : M) :=
  Classical.choose_spec (show ∃ i, a i = (y : M) from y.2)

/-- The map `Set.range a → N` sending `a i` to `a' i`.  It is well defined precisely because `a`
and `a'` have the same type. -/
noncomputable def rangeMap (a : Fin k → M) (a' : Fin k → N)
    (y : ↥(morleySub (L := L) (Set.range a))) : N :=
  a' (rangeIdx a y)

theorem rangeMap_eq (h : SameType L a a') (y : ↥(morleySub (L := L) (Set.range a))) (i : Fin k)
    (hi : a i = (y : M)) : rangeMap a a' y = a' i := by
  show a' (rangeIdx a y) = a' i
  exact (h.eq_iff (rangeIdx a y) i).1 ((rangeIdx_spec a y).trans hi.symm)

/-- `rangeMap` is a partial elementary map. -/
theorem rangeMap_elementary (h : SameType L a a') (n : ℕ) (φ : L.Formula (Fin n))
    (x : Fin n → ↥(morleySub (L := L) (Set.range a))) :
    φ.Realize (fun j => ((x j : M))) ↔ φ.Realize fun j => rangeMap a a' (x j) := by
  have h1 : (fun j => ((x j : M))) = a ∘ fun j => rangeIdx a (x j) :=
    funext fun j => (rangeIdx_spec a (x j)).symm
  have h2 : (fun j => rangeMap a a' (x j)) = a' ∘ fun j => rangeIdx a (x j) := rfl
  rw [h1, h2]
  exact h.comp _ φ

/-- The `morleyLang L`-embedding of `Set.range a` into `N` determined by same-typed tuples. -/
noncomputable def embeddingOfSameType (h : SameType L a a') :
    ↥(morleySub (L := L) (Set.range a)) ↪[morleyLang L] N :=
  embeddingOfElementary _ (rangeMap a a') (rangeMap_elementary h)

/-- The partial equivalence between Morleyized structures determined by same-typed tuples. -/
noncomputable def peqOfSameType (h : SameType L a a') : M ≃ₚ[morleyLang L] N where
  dom := morleySub (Set.range a)
  cod := (embeddingOfSameType h).toHom.range
  toEquiv := (embeddingOfSameType h).equivRange

@[simp]
theorem peqOfSameType_dom (h : SameType L a a') :
    (peqOfSameType h).dom = morleySub (Set.range a) := rfl

theorem peqOfSameType_toEquiv_coe (h : SameType L a a') (y : ↥(peqOfSameType h).dom) :
    (((peqOfSameType h).toEquiv y : N)) = rangeMap (L := L) a a' y :=
  Embedding.equivRange_apply _ _

theorem peqOfSameType_apply (h : SameType L a a') (i : Fin k)
    (hi : a i ∈ (peqOfSameType h).dom) :
    (((peqOfSameType h).toEquiv ⟨a i, hi⟩ : N)) = a' i :=
  (peqOfSameType_toEquiv_coe h _).trans (rangeMap_eq h _ i rfl)

theorem peqOfSameType_dom_fg (h : SameType L a a') : (peqOfSameType h).dom.FG :=
  morleySub_fg (Set.finite_range a)

/-- The finitely generated partial equivalence determined by same-typed tuples. -/
noncomputable def fgEquivOfSameType (h : SameType L a a') : (morleyLang L).FGEquiv M N :=
  ⟨peqOfSameType h, peqOfSameType_dom_fg h⟩

end Tuples

/-! ## Extension pairs -/

section ExtensionPair

variable {M N : Type*} [L.Structure M] [L.Structure N]

/-- A partial equivalence of Morleyized structures matches same-typed tuples. -/
theorem sameType_of_partialEquiv (f : M ≃ₚ[morleyLang L] N) {k : ℕ} (ε : Fin k → ↥f.dom) :
    SameType L (fun i => ((ε i : M))) fun i => ((f.toEquiv (ε i) : N)) :=
  fun φ => realize_iff_of_embedding f.toEmbedding φ ε

/-- A partial equivalence enumerated by a pair of same-typed tuples is below the partial
equivalence those tuples determine. -/
theorem le_peqOfSameType {f : M ≃ₚ[morleyLang L] N} {k : ℕ} {a : Fin k → M} {a' : Fin k → N}
    (h : SameType L a a') (hsurj : ∀ y : ↥f.dom, ∃ i, a i = (y : M))
    (hcompat : ∀ (y : ↥f.dom) (i : Fin k), a i = (y : M) → ((f.toEquiv y : N)) = a' i) :
    f ≤ peqOfSameType h := by
  have hdom : f.dom ≤ (peqOfSameType h).dom := by
    intro y hy
    obtain ⟨i, hi⟩ := hsurj ⟨y, hy⟩
    exact ⟨i, hi⟩
  refine ⟨hdom, ?_⟩
  ext y
  obtain ⟨i, hi⟩ := hsurj y
  have h1 : (((peqOfSameType h).toEquiv (Substructure.inclusion hdom y) : N)) = a' i :=
    (peqOfSameType_toEquiv_coe h _).trans (rangeMap_eq h _ i hi)
  exact h1.trans (hcompat y i hi).symm

/-- The one-step extension of a finitely generated partial equivalence, given an enumeration of
its (finite) domain and a realization in `N` of the type of the new element. -/
theorem exists_fgEquiv_extension {f : M ≃ₚ[morleyLang L] N} {k : ℕ} (ε : Fin k ≃ ↥f.dom)
    (h : IsTypeExtensionPair L M N) (m : M) (hm : m ∉ f.dom) :
    ∃ g : (morleyLang L).FGEquiv M N, m ∈ g.1.dom ∧ f ≤ g.1 := by
  obtain ⟨n, hn⟩ := h k (fun i => ((ε i : M))) (fun i => ((f.toEquiv (ε i) : N)))
    (sameType_of_partialEquiv f fun i => ε i) m
  refine ⟨fgEquivOfSameType hn, ?_, ?_⟩
  · show m ∈ Set.range (Fin.snoc (fun i => ((ε i : M))) m : Fin (k + 1) → M)
    exact ⟨Fin.last k, by simp⟩
  · refine le_peqOfSameType hn (fun y => ⟨(ε.symm y).castSucc, by simp⟩) ?_
    intro y i
    refine Fin.lastCases ?_ ?_ i
    · intro hlast
      simp only [Fin.snoc_last] at hlast
      exact absurd (show m ∈ f.dom by rw [hlast]; exact y.2) hm
    · intro j hj
      simp only [Fin.snoc_castSucc] at hj ⊢
      have : ε j = y := Subtype.ext hj
      rw [this]

/-- A type-extension pair of `L`-structures is an extension pair of Morleyized structures in the
sense of `FirstOrder.Language.IsExtensionPair`. -/
theorem isExtensionPair_of_isTypeExtensionPair (h : IsTypeExtensionPair L M N) :
    (morleyLang L).IsExtensionPair M N := by
  rintro ⟨f, hfg⟩ m
  by_cases hm : m ∈ f.dom
  · exact ⟨⟨f, hfg⟩, hm, le_rfl⟩
  · haveI : Finite ↥f.dom := hfg.finite
    obtain ⟨g, hg1, hg2⟩ := exists_fgEquiv_extension (Finite.equivFin ↥f.dom).symm h m hm
    exact ⟨g, hg1, hg2⟩

end ExtensionPair

/-! ## The payload -/

/-- **Two countable structures realizing the same types, with a designated finite tuple matched,
are isomorphic by an isomorphism fixing that tuple.**

The hypotheses are exactly what Mathlib's `FirstOrder.Language.equiv_between_cg` needs once the
languages are Morleyized: countability gives countable generation, `hb` gives the starting
finitely generated partial equivalence, and the two `IsTypeExtensionPair` hypotheses give the
"forth" and "back" steps. -/
theorem nonempty_equiv_of_same_types_of_countable {M N : Type*} [L.Structure M] [L.Structure N]
    [Countable M] [Countable N] {m : ℕ} (b : Fin m → M) (b' : Fin m → N)
    (hb : SameType L b b') (hMN : IsTypeExtensionPair L M N) (hNM : IsTypeExtensionPair L N M) :
    ∃ e : M ≃[L] N, ∀ i, e (b i) = b' i := by
  obtain ⟨F, hF⟩ := FirstOrder.Language.equiv_between_cg (L := morleyLang L)
    Structure.cg_of_countable Structure.cg_of_countable (fgEquivOfSameType hb)
    (isExtensionPair_of_isTypeExtensionPair hMN) (isExtensionPair_of_isTypeExtensionPair hNM)
  refine ⟨toLEquiv F, fun i => ?_⟩
  have hmem : b i ∈ (peqOfSameType hb).dom := Set.mem_range_self i
  have h2 : F (b i) = (((peqOfSameType hb).toEquiv ⟨b i, hmem⟩ : N)) :=
    congrArg Subtype.val (PartialEquiv.toEquiv_inclusion_apply hF ⟨b i, hmem⟩)
  rw [peqOfSameType_apply hb i hmem] at h2
  exact h2

end Submission.Morley
