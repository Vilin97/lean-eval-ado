import Mathlib.ModelTheory.ElementaryMaps
import Submission.Morley.Port.IsolatedTypes
import Submission.Morley.Port.PartialEmbedding

/-!
# Prime and atomic models over a set

This file is the "prime and atomic models" chapter of a formalisation of Morley's categoricity
theorem.

## Main definitions

* `Submission.Morley.IsElementaryOn` : a map `g : A → N` out of a subset `A` of a structure `M`
  is a *partial elementary map* when it preserves the truth of every formula with parameters
  from `A`.
* `Submission.Morley.IsAtomic` : `M` is *atomic over* `A ⊆ M` when every finite tuple of
  elements of `M` realises an isolated type over `A`.
* `Submission.Morley.IsPrime` : `M` is *prime over* `A ⊆ M` when every partial elementary map
  from `A` into a model of the theory extends to an elementary embedding of `M`.
* `Submission.Morley.IsolatedDense` : the isolated types are dense in every space `S₁(A)`.

## Main results

* `Submission.Morley.isIsolated_iff_isOpen_singleton_over` : the syntactic and the topological
  characterisations of isolation agree.
* `Submission.Morley.exists_realize_of_isIsolated` : an isolated type over `A` is realised in
  every model containing `A` elementarily.
* `Submission.Morley.isPrime_of_isAtomic` : a model that is atomic over `A` and countable is
  prime over `A`.
* `Submission.Morley.exists_realize_isIsolated_of_isolatedDense` : the construction step for
  prime models, extracted from density of the isolated types.

## Note on countability

`isPrime_of_isAtomic` needs the countability hypothesis: an uncountable dense linear order
without endpoints is atomic over `∅` (all its `n`-types over `∅` are isolated) but does not embed
into `ℚ`, so it is not prime.  For uncountable parameter sets the correct hypothesis is
*constructibility* over `A`, not atomicity.

## What is not proved here

The existence of a prime model over `A` from `IsolatedDense` is not proved.  What is proved is
the construction step, `exists_realize_isIsolated_of_isolatedDense`, together with the two
ingredients of the induction showing that a constructible model is atomic: the base case
`isIsolated_typeOf_of_mem` and, from the ambient development,
`Theory.CompleteType.isIsolated_typeOf_trans`.  What remains is the transfinite bookkeeping
(a Tarski--Vaught closure of an increasing chain of parameter sets) and the "mixed tuple"
isolation lemma for a tuple whose entries are parameters except for one new element.
-/

universe u v w w'

open FirstOrder Language Theory Theory.CompleteType

namespace Submission.Morley

variable {L : Language.{u, v}}

/-! ## Isolated types over a parameter set

Isolation of complete types is taken over verbatim from `Theory.CompleteType.IsIsolated`.  The
two characterisations asked for -- "some formula of the type entails, modulo the theory, every
other formula of the type" and "the type is an isolated point of the Stone topology" -- agree.
-/

section Isolated

variable {M : Type w} [L.Structure M] {A : Set M} {α : Type w'}

/-- **Isolated types over a parameter set: the two characterisations agree.**

A complete type `p` over the parameter set `A ⊆ M` is *principal* -- some formula of `p` entails,
modulo the theory `Th(M_A)` of `M` with constants for `A`, every formula of `p` -- exactly when
`p` is an isolated point of the Stone topology on the space of complete types over `A`. -/
theorem isIsolated_iff_isOpen_singleton_over (p : L.CompleteTypeOver A α) :
    (∃ φ : (L[[A]]).Formula α, Formula.equivSentence φ ∈ p ∧
        ∀ ψ ∈ p, ((L[[A]]).lhomWithConstants α).onTheory ((L[[A]]).completeTheory M) ⊨ᵇ
          (Formula.equivSentence φ).imp ψ) ↔
      IsOpen ({p} : Set (L.CompleteTypeOver A α)) := by
  rw [← CompleteType.isIsolated_iff_isOpen_singleton p]
  exact exists_congr fun _ => CompleteType.isolatedBy_iff_models_imp.symm

end Isolated

/-! ## Partial elementary maps -/

/-- A map `g : A → N`, where `A` is a subset of the `L`-structure `M`, is a *partial elementary
map* when it preserves the truth of every `L`-formula with parameters from `A`.

This is the precise form of "`N` is a model containing `A`" used in the definition of a prime
model: it says exactly that `N`, expanded by interpreting a constant for each `a ∈ A` as `g a`,
is a model of the theory of `M` with constants for `A` (see `IsElementaryOn.model`). -/
def IsElementaryOn (L : Language.{u, v}) {M : Type w} [L.Structure M] {N : Type w}
    [L.Structure N] (A : Set M) (g : A → N) : Prop :=
  ∀ φ : L.Formula A, φ.Realize (Subtype.val : A → M) ↔ φ.Realize g

namespace IsElementaryOn

variable {M : Type w} [L.Structure M] {N : Type w} [L.Structure N]
variable {A : Set M} {g : A → N}

/-- A partial elementary map preserves formulas indexed by any variable type, in particular by
`Fin n`; this is the shape in which `Language.PartialElementaryEmbedding` states the
condition. -/
theorem realize_fin (hg : IsElementaryOn L A g) {n : ℕ} (φ : L.Formula (Fin n)) (x : Fin n → A) :
    φ.Realize (Subtype.val ∘ x) ↔ φ.Realize (g ∘ x) := by
  have h := hg (φ.relabel x)
  rwa [Formula.realize_relabel, Formula.realize_relabel] at h

/-- Interpreting the constants of `L[[A]]` in `N` through `g` makes `N` a model of the theory of
`M` with constants for `A`.  This is the semantic content of being a partial elementary map. -/
theorem model (hg : IsElementaryOn L A g) :
    letI : (Language.constantsOn A).Structure N := Language.constantsOn.structure g
    N ⊨ (L[[A]]).completeTheory M := by
  letI : (Language.constantsOn A).Structure N := Language.constantsOn.structure g
  refine (Theory.model_iff _).2 fun σ hσ => ?_
  have h1 : (Formula.equivSentence.symm σ).Realize (Subtype.val : A → M) := by
    rw [Formula.realize_equivSentence_symm]
    exact hσ
  have h2 := (hg _).1 h1
  rwa [Formula.realize_equivSentence_symm] at h2

end IsElementaryOn

section PartialElementary

variable {M : Type w} [L.Structure M] {N : Type w} [L.Structure N] {A : Set M} {g : A → N}

/-- Conversely to `IsElementaryOn.realize_fin`, it suffices to check the defining condition of a
partial elementary map on formulas with variables indexed by `Fin n`. -/
theorem isElementaryOn_of_realize_fin
    (h : ∀ (n : ℕ) (φ : L.Formula (Fin n)) (x : Fin n → A),
      φ.Realize (Subtype.val ∘ x) ↔ φ.Realize (g ∘ x)) :
    IsElementaryOn L A g := by
  classical
  intro φ
  set ε := Fintype.equivFin φ.freeVarFinset with hε
  set ψ : L.Formula (Fin (Fintype.card φ.freeVarFinset)) :=
    Formula.relabel ε (φ.restrictFreeVar id) with hψ
  set x : Fin (Fintype.card φ.freeVarFinset) → A := Subtype.val ∘ ε.symm with hx
  have key : ∀ {K : Type w} [L.Structure K] (v : A → K), ψ.Realize (v ∘ x) ↔ φ.Realize v := by
    intro K _ v
    rw [hψ, Formula.realize_relabel]
    have hvx : (v ∘ x) ∘ (ε : φ.freeVarFinset → _) = v ∘ (Subtype.val : φ.freeVarFinset → A) := by
      funext a
      simp [hx]
    rw [hvx]
    exact BoundedFormula.realize_restrictFreeVar (f := id) v fun _ => rfl
  rw [← key (Subtype.val : A → M), ← key g]
  exact h _ ψ x

/-- A `Language.PartialElementaryEmbedding` between subsets is a partial elementary map. -/
theorem isElementaryOn_partialElementaryEmbedding {B : Set N} (f : A ↪ₚₑ[L] B) :
    IsElementaryOn L A fun a => (f a : N) :=
  isElementaryOn_of_realize_fin fun _ φ x => f.map_formula' φ x

/-- Conversely, a partial elementary map is a `Language.PartialElementaryEmbedding` onto its
range. -/
def IsElementaryOn.toPartialElementaryEmbedding (hg : IsElementaryOn L A g) :
    A ↪ₚₑ[L] Set.range g where
  toFun a := ⟨g a, ⟨a, rfl⟩⟩
  surjective' := by
    rintro ⟨_, a, rfl⟩
    exact ⟨a, rfl⟩
  map_formula' _ φ x := hg.realize_fin φ x

end PartialElementary

/-! ## Atomic and prime models -/

variable {T : L.Theory}

/-- A tuple of elements of `A` realises an isolated type over `A`: it is isolated by the
conjunction of the equations `xᵢ = aᵢ`.  This is the base case of the induction showing that a
model constructible over `A` is atomic over `A`. -/
theorem isIsolated_typeOf_of_mem {M : Type w} [L.Structure M] [Nonempty M] {A : Set M} {n : ℕ}
    (a : Fin n → A) :
    (((L[[A]]).completeTheory M).typeOf fun i => (a i : M)).IsIsolated := by
  classical
  refine ⟨Formula.iInf fun i : Fin n => (Term.var i).equal (Language.con L (a i)).term, ?_⟩
  rw [CompleteType.typeOf_isolatedBy_iff_of_isComplete (completeTheory.isComplete (L[[A]]) M)]
  refine ⟨by simp [Term.realize_constants], fun b hb => ?_⟩
  have hb' : b = fun i => (a i : M) := by
    funext i
    simpa [Term.realize_constants] using Formula.realize_iInf.1 hb i
  rw [hb']

/-- `M` is *atomic over* the subset `A` when every finite tuple of elements of `M` realises an
isolated complete type over `A`. -/
def IsAtomicOn (L : Language.{u, v}) (M : Type w) [L.Structure M] [Nonempty M] (A : Set M) :
    Prop :=
  ∀ (n : ℕ) (x : Fin n → M), (((L[[A]]).completeTheory M).typeOf x).IsIsolated

/-- `M` is *atomic over* the subset `A` when every finite tuple of elements of `M` realises an
isolated complete type over `A`. -/
def IsAtomic (M : T.ModelType.{u, v, w}) (A : Set M) : Prop :=
  IsAtomicOn L M A

/-- `M` is *prime over* the subset `A` when every partial elementary map from `A` into a model
of `T` extends to an elementary embedding of `M` into that model.

The requirement `A ⊆ M` is built into the statement, since `A : Set M`. -/
def IsPrime (M : T.ModelType.{u, v, w}) (A : Set M) : Prop :=
  ∀ (N : T.ModelType.{u, v, w}) (g : A → N), IsElementaryOn L A g →
    ∃ f : M ↪ₑ[L] N, ∀ a : A, f a = g a

/-! ## An isolated type is realised in every model -/

section Realize

variable {M : Type w} [L.Structure M] [Nonempty M] {A : Set M} {α : Type w'}

/-- **An isolated type over `A` is realised in every model containing `A`.**  This is exactly
what isolation buys: a formula isolating `p` is consistent with the complete theory `Th(M_A)`,
hence satisfiable in every model of it, and any of its realisations realises `p`. -/
theorem exists_realize_of_isIsolated {p : L.CompleteTypeOver A α} (hp : p.IsIsolated)
    (N : Type w) [(L[[A]]).Structure N] [Nonempty N] [N ⊨ (L[[A]]).completeTheory M] :
    ∃ y : α → N, ((L[[A]]).completeTheory M).typeOf y = p := by
  obtain ⟨φ, hφ⟩ := hp
  obtain ⟨K, v, hv⟩ := Theory.exists_modelType_is_realized_in _ p
  have hφv : φ.Realize v := (hφ.realize_iff_typeOf_eq v).2 hv
  obtain ⟨y, hy⟩ :=
    (completeTheory.isComplete (L := L[[A]]) M).exists_realize_of_isComplete v φ hφv N
  exact ⟨y, (hφ.realize_iff_typeOf_eq y).1 hy⟩

end Realize

/-! ## Atomic implies prime

The construction is the classical one: enumerate `M`, and extend the given partial elementary
map on `A` one element at a time.  At stage `n` the tuple `(e 0, …, e n)` realises an isolated
type over `A`; its isolating formula, existentially quantified in the last variable, is already
true of the image tuple, and a witness for it is the value of the extended map at `e n`.
-/

section Construction

variable {N : Type w}

/-- Build a sequence from a one-step extension property. -/
private theorem exists_seq_of_snoc (P : ∀ n : ℕ, (Fin n → N) → Prop) (h0 : P 0 Fin.elim0)
    (hstep : ∀ (n : ℕ) (x : Fin n → N), P n x → ∃ b : N, P (n + 1) (Fin.snoc x b)) :
    ∃ c : ℕ → N, ∀ n : ℕ, P n fun i : Fin n => c i := by
  classical
  let F : ∀ n : ℕ, { x : Fin n → N // P n x } := fun n =>
    Nat.rec (motive := fun n => { x : Fin n → N // P n x }) ⟨Fin.elim0, h0⟩
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

variable {M : Type w} [L.Structure M] [Nonempty M] [L.Structure N] [Nonempty N] {A : Set M}
variable [(Language.constantsOn A).Structure N] [N ⊨ (L[[A]]).completeTheory M]

/-- The empty tuples of `M` and of `N` have the same (empty) type over `A`. -/
private theorem typeOf_elim0_eq :
    ((L[[A]]).completeTheory M).typeOf (Fin.elim0 : Fin 0 → M) =
      ((L[[A]]).completeTheory M).typeOf (Fin.elim0 : Fin 0 → N) := by
  refine CompleteType.typeOf_eq_of_realize_imp _ _ fun φ hφ => ?_
  have h1 : M ⊨ φ.relabel (Fin.elim0 : Fin 0 → Empty) := by
    rw [Sentence.Realize, Formula.realize_relabel]
    rwa [Subsingleton.elim ((default : Empty → M) ∘ (Fin.elim0 : Fin 0 → Empty)) Fin.elim0]
  have h2 : N ⊨ φ.relabel (Fin.elim0 : Fin 0 → Empty) :=
    Theory.realize_sentence_of_mem _ (Language.mem_completeTheory.2 h1)
  rw [Sentence.Realize, Formula.realize_relabel] at h2
  rwa [Subsingleton.elim ((default : Empty → N) ∘ (Fin.elim0 : Fin 0 → Empty)) Fin.elim0] at h2

/-- The key step: a partial elementary map defined on `A` together with an `n`-tuple extends to
one more element, because the type of the longer tuple over `A` is isolated. -/
private theorem exists_snoc (hat : IsAtomicOn L M A) (e : ℕ → M) (n : ℕ) (y : Fin n → N)
    (hy : ((L[[A]]).completeTheory M).typeOf (fun i : Fin n => e (i : ℕ)) =
      ((L[[A]]).completeTheory M).typeOf y) :
    ∃ b : N, ((L[[A]]).completeTheory M).typeOf (fun i : Fin (n + 1) => e (i : ℕ)) =
      ((L[[A]]).completeTheory M).typeOf (Fin.snoc y b) := by
  obtain ⟨φ, hφ⟩ := hat (n + 1) fun i : Fin (n + 1) => e (i : ℕ)
  -- move the last variable into the right-hand summand so that it can be quantified away
  set r : Fin (n + 1) → Fin n ⊕ Fin 1 := Fin.lastCases (Sum.inr 0) Sum.inl with hr
  set φ' : (L[[A]]).Formula (Fin n ⊕ Fin 1) := φ.relabel r with hφ'
  have hcomp : ∀ {K : Type w} (v : Fin n → K) (u : Fin 1 → K),
      Sum.elim v u ∘ r = Fin.snoc v (u 0) := by
    intro K v u
    funext i
    induction i using Fin.lastCases with
    | last => simp [hr]
    | cast j => simp [hr]
  have hsnoc : Fin.snoc (fun i : Fin n => e (i : ℕ)) (e n) = fun i : Fin (n + 1) => e (i : ℕ) := by
    funext i
    induction i using Fin.lastCases with
    | last => simp
    | cast j => simp
  have hM : (φ'.existsRight).Realize fun i : Fin n => e (i : ℕ) := by
    rw [Formula.realize_existsRight]
    refine ⟨fun _ => e n, ?_⟩
    rw [hφ', Formula.realize_relabel, hcomp, hsnoc]
    exact (hφ.realize_iff_typeOf_eq _).2 rfl
  have hN : (φ'.existsRight).Realize y :=
    (CompleteType.realize_iff_of_typeOf_eq _ _ hy _).1 hM
  rw [Formula.realize_existsRight] at hN
  obtain ⟨x, hx⟩ := hN
  refine ⟨x 0, ?_⟩
  rw [hφ', Formula.realize_relabel, hcomp] at hx
  exact ((hφ.realize_iff_typeOf_eq _).1 hx).symm

/-- Iterating `exists_snoc` produces an infinite sequence in `N` matching an enumeration of `M`
type by type over `A`. -/
private theorem exists_seq_typeOf_eq (hat : IsAtomicOn L M A) (e : ℕ → M) :
    ∃ c : ℕ → N, ∀ n : ℕ,
      ((L[[A]]).completeTheory M).typeOf (fun i : Fin n => e (i : ℕ)) =
        ((L[[A]]).completeTheory M).typeOf fun i : Fin n => c (i : ℕ) := by
  refine exists_seq_of_snoc
    (fun n y => ((L[[A]]).completeTheory M).typeOf (fun i : Fin n => e (i : ℕ)) =
      ((L[[A]]).completeTheory M).typeOf y) ?_ fun n y hy => exists_snoc hat e n y hy
  have : (fun i : Fin 0 => e (i : ℕ)) = (Fin.elim0 : Fin 0 → M) := funext fun i => i.elim0
  rw [this]
  exact typeOf_elim0_eq

end Construction

/-! ### The main theorem -/

section Main

variable {M : Type w} [L.Structure M] [Nonempty M] {N : Type w} [L.Structure N] [Nonempty N]
variable {A : Set M}

/-- **Atomic implies prime.**  If `M` is atomic over `A` and can be enumerated by `ℕ`, then every
partial elementary map from `A` into a structure `N` extends to an elementary embedding of `M`
into `N`.

Countability of `M` is genuinely needed: an uncountable dense linear order without endpoints is
atomic over `∅` but does not embed into `ℚ`. -/
theorem exists_elementaryEmbedding_of_isAtomicOn (hat : IsAtomicOn L M A) (e : ℕ → M)
    (he : Function.Surjective e) {g : A → N} (hg : IsElementaryOn L A g) :
    ∃ f : M ↪ₑ[L] N, ∀ a : A, f a = g a := by
  classical
  letI : (Language.constantsOn A).Structure N := Language.constantsOn.structure g
  haveI := hg.model
  obtain ⟨c, hc⟩ := exists_seq_typeOf_eq (N := N) hat e
  set idx : M → ℕ := Function.invFun e with hidx
  have hidxe : ∀ m : M, e (idx m) = m := fun m => Function.invFun_eq (he m)
  set F : M → N := fun m => c (idx m) with hF
  -- transfer of formulas along `F`
  have key : ∀ {k : ℕ} (φ : L.Formula (Fin k)) (x : Fin k → M),
      φ.Realize x ↔ φ.Realize (F ∘ x) := by
    intro k φ x
    set n : ℕ := (Finset.univ.sup fun i : Fin k => idx (x i)) + 1 with hn
    have hlt : ∀ i : Fin k, idx (x i) < n :=
      fun i => Nat.lt_succ_of_le (Finset.le_sup (f := fun i : Fin k => idx (x i))
        (Finset.mem_univ i))
    set J : Fin k → Fin n := fun i => ⟨idx (x i), hlt i⟩ with hJ
    set Φ : (L[[A]]).Formula (Fin n) := ((L.lhomWithConstants A).onFormula φ).relabel J with hΦ
    have hMside : Φ.Realize (fun i : Fin n => e (i : ℕ)) ↔ φ.Realize x := by
      rw [hΦ, Formula.realize_relabel, LHom.realize_onFormula]
      have : (fun i : Fin n => e (i : ℕ)) ∘ J = x := by
        funext i; simp [hJ, hidxe]
      rw [this]
    have hNside : Φ.Realize (fun i : Fin n => c (i : ℕ)) ↔ φ.Realize (F ∘ x) := by
      rw [hΦ, Formula.realize_relabel, LHom.realize_onFormula]
      have : (fun i : Fin n => c (i : ℕ)) ∘ J = F ∘ x := by
        funext i; simp [hJ, hF]
      rw [this]
    rw [← hMside, ← hNside]
    exact CompleteType.realize_iff_of_typeOf_eq _ _ (hc n) Φ
  refine ⟨⟨F, fun k φ x => (key φ x).symm⟩, fun a => ?_⟩
  -- `F` agrees with `g` on `A`
  set k : ℕ := idx (a : M) with hk
  have hek : e k = (a : M) := hidxe _
  set Ψ : (L[[A]]).Formula (Fin (k + 1)) :=
    (Term.var (⟨k, Nat.lt_succ_self k⟩ : Fin (k + 1))).equal (Language.con L a).term with hΨ
  have hMΨ : Ψ.Realize fun i : Fin (k + 1) => e (i : ℕ) := by
    rw [hΨ, Formula.realize_equal, Term.realize_var, Term.realize_constants]
    exact hek
  have hNΨ : Ψ.Realize fun i : Fin (k + 1) => c (i : ℕ) :=
    (CompleteType.realize_iff_of_typeOf_eq _ _ (hc (k + 1)) Ψ).1 hMΨ
  rw [hΨ, Formula.realize_equal, Term.realize_var, Term.realize_constants] at hNΨ
  exact hNΨ

/-- **Atomic implies prime**, for a countable model.  Countability is necessary. -/
theorem isPrime_of_isAtomic {T : L.Theory} {M : T.ModelType.{u, v, w}} [Countable M] {A : Set M}
    (hat : IsAtomic M A) : IsPrime M A := by
  obtain ⟨e, he⟩ := exists_surjective_nat (α := M)
  exact fun N g hg => exists_elementaryEmbedding_of_isAtomicOn hat e he hg

end Main

/-! ## Density of isolated types

The existence of prime models over an arbitrary parameter set follows, in an `ω`-stable theory,
from the density of the isolated types in every space of `1`-types.  Density itself is proved
elsewhere (from the absence of a binary tree of consistent conditions); here it is taken as a
hypothesis and turned into the form in which a construction of a prime model consumes it.
-/

section Density

/-- The isolated types are dense in the Stone space `S₁(A)` of complete `1`-types over the
parameter set `A ⊆ M`. -/
def IsolatedDenseOn (L : Language.{u, v}) (M : Type w) [L.Structure M] (A : Set M) : Prop :=
  Dense {p : L.CompleteTypeOver A (Fin 1) | p.IsIsolated}

/-- **The isolated types are dense.**  For every model `M` of `T` and every parameter set
`A ⊆ M`, the isolated types form a dense subset of the Stone space `S₁(A)` of complete
`1`-types over `A`.

This is the hypothesis under which prime models over an arbitrary parameter set exist; in an
`ω`-stable theory it follows from the absence of a binary tree of consistent conditions. -/
def IsolatedDense (T : L.Theory) : Prop :=
  ∀ (M : T.ModelType.{u, v, w}) (A : Set M), IsolatedDenseOn L M A

variable {M : Type w} [L.Structure M] [Nonempty M] {A : Set M}

/-- Density, in usable form: every consistent formula over `A` in one free variable belongs to
some isolated complete type over `A`. -/
theorem exists_isIsolated_mem_of_isolatedDenseOn (h : IsolatedDenseOn L M A)
    (φ : (L[[A]]).Formula (Fin 1)) (x : Fin 1 → M) (hx : φ.Realize x) :
    ∃ p : L.CompleteTypeOver A (Fin 1), p.IsIsolated ∧ Formula.equivSentence φ ∈ p :=
  h.exists_mem_open (CompleteType.isOpen_typesWith _)
    ⟨((L[[A]]).completeTheory M).typeOf x, CompleteType.formula_mem_typeOf.2 hx⟩

/-- **The construction step for a prime model.**  Assuming the isolated types are dense, every
consistent formula over `A` in one free variable is realised inside `M` by an element whose type
over `A` is isolated.  Iterating this, with a Tarski--Vaught bookkeeping, is what produces a
model that is constructible -- hence atomic -- over `A`. -/
theorem exists_realize_isIsolated_of_isolatedDense (h : IsolatedDenseOn L M A)
    (φ : (L[[A]]).Formula (Fin 1)) (x : Fin 1 → M) (hx : φ.Realize x) :
    ∃ b : M, φ.Realize (fun _ => b) ∧
      (((L[[A]]).completeTheory M).typeOf fun _ : Fin 1 => b).IsIsolated := by
  obtain ⟨p, hp, hmem⟩ := exists_isIsolated_mem_of_isolatedDenseOn h φ x hx
  obtain ⟨y, hy⟩ := exists_realize_of_isIsolated hp M
  have hy0 : (fun _ : Fin 1 => y 0) = y := funext fun i => by rw [Subsingleton.elim i 0]
  refine ⟨y 0, ?_, ?_⟩
  · rw [hy0]
    exact CompleteType.formula_mem_typeOf.1 (hy ▸ hmem)
  · rw [hy0, hy]
    exact hp

end Density

end Submission.Morley
