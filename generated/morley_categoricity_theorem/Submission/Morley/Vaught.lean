import Mathlib
import Submission.Morley.Omitting
import Submission.Morley.Port.DefinablyFull

/-!
# Vaughtian pairs and Vaught's two-cardinal theorem

This file is the "Vaughtian pairs" chapter of the formalisation of Morley's categoricity
theorem.  Everything happens in a fixed countable language `L : FirstOrder.Language.{0, 0}` and
all structures live in `Type 0`.

## Main definitions

* `Submission.Morley.HasVaughtianPair`: `T` has a Vaughtian pair.
* `Submission.Morley.HasTwoCardinalModel`: `T` has a `(κ, λ)`-model.
* `Submission.Morley.VaughtTwoCardinal`, `Submission.Morley.TwoCardinalTransfer`: the statements
  of Vaught's two-cardinal theorem, packaged as hypotheses.

## Main results

* `Submission.Morley.hasVaughtianPair_of_hasTwoCardinalModel`: a `(κ, λ)`-model with
  `ℵ₀ ≤ λ < κ` yields a Vaughtian pair.
* `Submission.Morley.definablyFull_of_not_hasVaughtianPair`: if `T` has no Vaughtian pair then
  every model of `T` is *definably full* — every infinite parameter-definable set is as large as
  the model.
* `Submission.Morley.not_hasVaughtianPair_of_categorical`: an uncountably categorical complete
  theory in a countable language has no Vaughtian pair, given two-cardinal transfer to the
  cardinal of categoricity.

## Status

Vaught's two-cardinal theorem itself (a Vaughtian pair produces an `(ℵ₁, ℵ₀)`-model) is **not**
proved here; it is only stated, as `VaughtTwoCardinal`.  See the section
"Vaught's two-cardinal theorem" below for what the missing argument requires.

The omitting types theorem is imported from `Submission.Morley.Omitting`
(`Submission.Morley.exists_model_omitting`).
-/

namespace Submission.Morley

open Cardinal Set
open FirstOrder FirstOrder.Language

variable {L : FirstOrder.Language.{0, 0}}

/-! ## Auxiliary material on unary definable sets -/

/-- Evaluation at the unique index identifies the `Fin 1`-indexed version of a subset of `M`
with the subset itself. -/
def finOneSetEquiv {M : Type*} (X : Set M) : {x : Fin 1 → M | x 0 ∈ X} ≃ X :=
  (Equiv.funUnique (Fin 1) M).subtypeEquiv fun _ => Iff.rfl

theorem mk_finOneSet {M : Type} (X : Set M) : #{x : Fin 1 → M | x 0 ∈ X} = #X :=
  Cardinal.mk_congr (finOneSetEquiv X)

theorem infinite_finOneSet {M : Type} {X : Set M} (h : X.Infinite) :
    {x : Fin 1 → M | x 0 ∈ X}.Infinite := by
  rw [← Set.infinite_coe_iff] at h ⊢
  exact Infinite.of_injective _ (finOneSetEquiv X).symm.injective

/-- A unary formula with finitely many parameters defines a set over the range of the
parameters. -/
theorem definable₁_of_formula {M : Type} [L.Structure M] {m : ℕ}
    (φ : L.Formula (Fin m ⊕ Fin 1)) (b : Fin m → M) :
    (Set.range b).Definable₁ L {a : M | φ.Realize (Sum.elim b fun _ => a)} := by
  classical
  rw [Set.Definable₁, Set.definable_iff_exists_formula_sum]
  refine ⟨φ.relabel (Sum.map (fun i => (⟨b i, Set.mem_range_self i⟩ : Set.range b)) id), ?_⟩
  ext v
  simp only [Set.mem_setOf_eq, Formula.realize_relabel]
  congr! 1
  ext (i | i)
  · simp
  · exact congrArg v (Subsingleton.elim _ _)

/-- Definable sets are carried to definable sets by an isomorphism of structures. -/
theorem definable_image_equiv {M N : Type} [L.Structure M] [L.Structure N] (f : M ≃[L] N)
    {α : Type} {A : Set M} {S : Set (α → M)} (h : A.Definable L S) :
    (f '' A).Definable L ((fun v : α → M => (f : M → N) ∘ v) '' S) := by
  rw [Set.definable_iff_exists_formula_sum] at h ⊢
  obtain ⟨φ, rfl⟩ := h
  refine ⟨φ.relabel (Sum.map (fun a : A => (⟨f a, ⟨a, a.2, rfl⟩⟩ : (f '' A : Set N))) id), ?_⟩
  have hcomp : ∀ w : α → N,
      (Sum.elim (Subtype.val : (f '' A : Set N) → N) w) ∘
          Sum.map (fun a : A => (⟨f a, ⟨a, a.2, rfl⟩⟩ : (f '' A : Set N))) id
        = Sum.elim (fun a : A => (f a : N)) w := by
    intro w; ext (a | i) <;> simp
  have key : ∀ w : α → N,
      φ.Realize (Sum.elim (fun a : A => (f a : N)) w) ↔
        φ.Realize (Sum.elim (Subtype.val : A → M) ((f.symm : N → M) ∘ w)) := by
    intro w
    rw [← f.toElementaryEmbedding.map_formula φ
      (Sum.elim (Subtype.val : A → M) ((f.symm : N → M) ∘ w))]
    congr! 1
    ext (a | i) <;> simp
  ext w
  simp only [Set.mem_setOf_eq, Formula.realize_relabel, hcomp, key, Set.mem_image]
  constructor
  · rintro ⟨v, hv, rfl⟩
    have hv' : (f.symm : N → M) ∘ ((f : M → N) ∘ v) = v := by ext i; simp
    rw [hv']
    exact hv
  · intro hw
    exact ⟨(f.symm : N → M) ∘ w, hw, by ext i; simp⟩

/-! ## Vaughtian pairs -/

/-- `T` has a **Vaughtian pair** when there are models `N ≺ M` of `T` with `N ≠ M`, and a
subset `X ⊆ M` which

* is definable in `M` with parameters from `N`,
* is infinite,
* is contained in `N`.

The last condition says exactly that `X = φ(M, b̄) = φ(N, b̄)`: since `N ≺ M`, the trace of `X`
on `N` is the set defined by the same formula inside `N`, and `X ⊆ N` makes the two agree. -/
def HasVaughtianPair (T : L.Theory) : Prop :=
  ∃ (M : T.ModelType.{0, 0, 0}) (N : L.ElementarySubstructure M) (X : Set M),
    (N : Set M) ≠ Set.univ ∧ (N : Set M).Definable₁ L X ∧ X.Infinite ∧ X ⊆ (N : Set M)

/-- Convenient constructor for `HasVaughtianPair` from an explicit formula and parameter
tuple. -/
theorem hasVaughtianPair_of_formula {T : L.Theory} (M : T.ModelType.{0, 0, 0})
    (N : L.ElementarySubstructure M) {m : ℕ} (φ : L.Formula (Fin m ⊕ Fin 1)) (b : Fin m → M)
    (hb : ∀ i, b i ∈ N) (hne : (N : Set M) ≠ Set.univ)
    (hinf : {a : M | φ.Realize (Sum.elim b fun _ => a)}.Infinite)
    (hsub : {a : M | φ.Realize (Sum.elim b fun _ => a)} ⊆ (N : Set M)) :
    HasVaughtianPair T :=
  ⟨M, N, _, hne,
    (definable₁_of_formula φ b).mono (Set.range_subset_iff.2 hb), hinf, hsub⟩

/-- Absence of a Vaughtian pair, in the form in which it gets applied: if `N ≼ M` and some
infinite subset of `M` definable over `N` is contained in `N`, then `N = M`. -/
theorem eq_univ_of_not_hasVaughtianPair {T : L.Theory} (h : ¬HasVaughtianPair T)
    (M : T.ModelType.{0, 0, 0}) (N : L.ElementarySubstructure M) (X : Set M)
    (hdef : (N : Set M).Definable₁ L X) (hinf : X.Infinite) (hsub : X ⊆ (N : Set M)) :
    (N : Set M) = Set.univ := by
  by_contra hne
  exact h ⟨M, N, X, hne, hdef, hinf, hsub⟩

/-- Absence of a Vaughtian pair, stated with an explicit formula and parameter tuple. -/
theorem eq_univ_of_not_hasVaughtianPair_formula {T : L.Theory} (h : ¬HasVaughtianPair T)
    (M : T.ModelType.{0, 0, 0}) (N : L.ElementarySubstructure M) {m : ℕ}
    (φ : L.Formula (Fin m ⊕ Fin 1)) (b : Fin m → M) (hb : ∀ i, b i ∈ N)
    (hinf : {a : M | φ.Realize (Sum.elim b fun _ => a)}.Infinite)
    (hsub : {a : M | φ.Realize (Sum.elim b fun _ => a)} ⊆ (N : Set M)) :
    (N : Set M) = Set.univ := by
  by_contra hne
  exact h (hasVaughtianPair_of_formula M N φ b hb hne hinf hsub)

/-- Realization of a formula with parameters from an elementary substructure is the same
computed in the substructure and in the ambient structure.

Consequently `φ(N, b̄) = φ(M, b̄) ∩ N` for `b̄` in `N`, so the condition `X ⊆ N` appearing in
`HasVaughtianPair` says exactly that `φ(N, b̄) = φ(M, b̄)`, which is the classical formulation of
a Vaughtian pair. -/
theorem elementarySubstructure_realize_iff {M : Type} [L.Structure M]
    (N : L.ElementarySubstructure M) {m : ℕ} (φ : L.Formula (Fin m ⊕ Fin 1)) (b : Fin m → N)
    (a : N) :
    φ.Realize (Sum.elim b fun _ => a) ↔
      φ.Realize (Sum.elim (fun i => (b i : M)) fun _ => (a : M)) := by
  have h := N.subtype.map_formula φ (Sum.elim b fun _ => a)
  rw [← h]
  congr! 1
  ext (i | i) <;> simp

/-! ## `(κ, λ)`-models -/

/-- `T` has a `(κ, lam)`-model when some model of `T` of cardinality `κ` has a
parameter-definable unary subset of cardinality `lam`. -/
def HasTwoCardinalModel (T : L.Theory) (κ lam : Cardinal.{0}) : Prop :=
  ∃ (M : T.ModelType.{0, 0, 0}) (A X : Set M),
    A.Definable₁ L X ∧ #M = κ ∧ #X = lam

/-- A `(κ, lam)`-model with `ℵ₀ ≤ lam < κ` produces a Vaughtian pair: shrink the model down to
an elementary substructure of size `lam` containing the definable set and its parameters. -/
theorem hasVaughtianPair_of_hasTwoCardinalModel (hL : L.card ≤ ℵ₀) {T : L.Theory}
    {κ lam : Cardinal.{0}} (hlam : ℵ₀ ≤ lam) (hlt : lam < κ)
    (h : HasTwoCardinalModel T κ lam) : HasVaughtianPair T := by
  obtain ⟨M, A, X, hdef, hMκ, hXlam⟩ := h
  classical
  obtain ⟨A₀, -, hdef₀⟩ := Set.definable_iff_finitely_definable.1 hdef
  -- shrink `M` to an elementary substructure of size `lam` containing `X ∪ A₀`
  obtain ⟨N, hsub, hNcard⟩ :=
    exists_elementarySubstructure_card_eq L (X ∪ (A₀ : Set M)) lam hlam
      (by
        simp only [Cardinal.lift_id]
        refine (Cardinal.mk_union_le _ _).trans ?_
        exact Cardinal.add_le_of_le hlam (le_of_eq hXlam)
          ((A₀.finite_toSet.lt_aleph0).le.trans hlam))
      (by simpa using hL.trans hlam)
      (by
        simp only [Cardinal.lift_id]
        exact hMκ ▸ hlt.le)
  simp only [Cardinal.lift_id] at hNcard
  refine ⟨M, N, X, ?_, hdef₀.mono ((Set.subset_union_right).trans hsub), ?_, ?_⟩
  · intro hcontra
    have hMle : #(M : Type) ≤ #N :=
      Cardinal.mk_le_of_injective
        (f := fun x : M => (⟨x, by rw [← SetLike.mem_coe, hcontra]; trivial⟩ : N))
        (fun x y hxy => by simpa using hxy)
    rw [hNcard, hMκ] at hMle
    exact absurd hMle (not_le.2 hlt)
  · rw [← Set.infinite_coe_iff, Cardinal.infinite_iff, hXlam]
    exact hlam
  · exact (Set.subset_union_left).trans hsub

/-! ## Absence of Vaughtian pairs makes every model definably full -/

/-- If `T` has no Vaughtian pair, then in every model of `T` every infinite parameter-definable
unary set is as large as the model. -/
theorem unaryDefinablyFull_of_not_hasVaughtianPair (hL : L.card ≤ ℵ₀) {T : L.Theory}
    (h : ¬HasVaughtianPair T) (M : T.ModelType.{0, 0, 0}) : L.UnaryDefinablyFull M := by
  intro A X hdef hinf
  refine le_antisymm (Cardinal.mk_set_le X) ?_
  by_contra hcon
  rw [not_le] at hcon
  refine h (hasVaughtianPair_of_hasTwoCardinalModel hL (lam := #X) ?_ hcon
    ⟨M, A, X, hdef, rfl, rfl⟩)
  rw [← Cardinal.infinite_iff, Set.infinite_coe_iff]
  exact hinf

/-- If `T` has no Vaughtian pair, then every model of `T` is definably full: every infinite
parameter-definable set (of any arity) is as large as the model. -/
theorem definablyFull_of_not_hasVaughtianPair (hL : L.card ≤ ℵ₀) {T : L.Theory}
    (h : ¬HasVaughtianPair T) (M : T.ModelType.{0, 0, 0}) : L.DefinablyFull M := by
  rcases finite_or_infinite (M : Type) with hfin | hinf
  · intro A n S _ hS
    have : Finite (M : Type) := hfin
    exact absurd (Set.toFinite S) hS
  · exact definablyFull_of_unary (unaryDefinablyFull_of_not_hasVaughtianPair hL h M)

/-! ## Vaught's two-cardinal theorem

The theorem itself — a Vaughtian pair produces an `(ℵ₁, ℵ₀)`-model — is *not* proved here.  It
is packaged as the predicate `VaughtTwoCardinal` (and its transfer to a prescribed larger
cardinal as `TwoCardinalTransfer`) so that the downstream development can take it as an explicit
hypothesis.

What the missing argument needs.  Write `L₀ = L ∪ {U}` for the *pair language*, `U` a new unary
predicate naming the smaller model, so that an elementary pair `N ≼ M` becomes a single
`L₀`-structure.  One then builds an elementary chain `(M_α)_{α < ω₁}` of copies of a countable
pair, in which the witnessing definable set never grows, and takes the union.

The step that keeps the definable set from growing is *not* a bare application of the omitting
types theorem to the elementary diagram of the pair: the naive statement "every countable model
of the pair theory has a proper elementary pair-extension with `U` unchanged" is false.  (Take
`L = {R}`, `M = ℕ` with `R` the even numbers, `N = ℕ \ {1}`; this is a Vaughtian pair, and
`|M \ N| = 1` is preserved by every elementary extension of the pair.)  The classical repair, and
the one the blueprint of this development follows, first produces a countable Vaughtian pair
whose two sides are *homogeneous and realize the same types over the empty set*, so that a
back-and-forth argument makes them isomorphic; the successor step of the `ω₁`-chain is then a
copy of that fixed isomorphism, and the definable set is transported bijectively at each stage.

So the missing ingredients are: the pair language and relativization, a countable homogeneous
Vaughtian pair, back-and-forth for countable homogeneous structures, and the `ω₁`-length chain.
Transfer from `ℵ₁` to a larger `κ` (`TwoCardinalTransfer`) is a further theorem which genuinely
needs `ω`-stability — it is not available in ZFC for a general theory.
-/

/-- **Vaught's two-cardinal theorem**, as a hypothesis: a complete theory in a countable
language with a Vaughtian pair has a model of cardinality `ℵ₁` in which some formula with
parameters defines a countably infinite set. -/
def VaughtTwoCardinal (L : FirstOrder.Language.{0, 0}) : Prop :=
  ∀ T : L.Theory, L.card ≤ ℵ₀ → T.IsComplete → HasVaughtianPair T →
    HasTwoCardinalModel T ℵ₁ ℵ₀

/-- Two-cardinal transfer to a prescribed uncountable cardinal `κ`, as a hypothesis: a complete
theory in a countable language with a Vaughtian pair has a model of cardinality `κ` in which
some formula with parameters defines a countably infinite set. -/
def TwoCardinalTransfer (L : FirstOrder.Language.{0, 0}) (κ : Cardinal.{0}) : Prop :=
  ∀ T : L.Theory, L.card ≤ ℵ₀ → T.IsComplete → HasVaughtianPair T →
    HasTwoCardinalModel T κ ℵ₀

/-- At `κ = ℵ₁` the two notions coincide. -/
theorem twoCardinalTransfer_aleph1_iff (L : FirstOrder.Language.{0, 0}) :
    TwoCardinalTransfer L ℵ₁ ↔ VaughtTwoCardinal L := Iff.rfl

/-- **Vaught's two-cardinal theorem**, unfolded into the shape the categoricity chapter asks
for: a Vaughtian pair yields a model of cardinality `ℵ₁` in which some formula with parameters
defines a countably infinite set.  This is a restatement of the hypothesis `VaughtTwoCardinal`;
the theorem itself is not proved in this file. -/
theorem exists_model_of_hasVaughtianPair (hVTC : VaughtTwoCardinal L) (hL : L.card ≤ ℵ₀)
    (T : L.Theory) (hT : T.IsComplete) (h : HasVaughtianPair T) :
    ∃ (M : T.ModelType.{0, 0, 0}) (A X : Set M), A.Definable₁ L X ∧ #M = ℵ₁ ∧ #X = ℵ₀ :=
  hVTC T hL hT h

/-! ## Uncountable categoricity rules out Vaughtian pairs -/

/-- A Vaughtian pair in particular provides an infinite model. -/
theorem exists_infinite_model_of_hasVaughtianPair {T : L.Theory} (h : HasVaughtianPair T) :
    ∃ M : T.ModelType.{0, 0, 0}, Infinite M := by
  obtain ⟨M, -, X, -, -, hXinf, -⟩ := h
  exact ⟨M, Set.infinite_univ_iff.1 (hXinf.mono (Set.subset_univ X))⟩

/-- Definable unary sets are carried to definable unary sets by an isomorphism. -/
theorem definable₁_image_equiv {M N : Type} [L.Structure M] [L.Structure N] (f : M ≃[L] N)
    {A X : Set M} (h : A.Definable₁ L X) :
    ((f : M → N) '' A).Definable₁ L ((f : M → N) '' X) := by
  have hd := definable_image_equiv f (α := Fin 1) (S := {x : Fin 1 → M | x 0 ∈ X}) h
  have hset : (fun v : Fin 1 → M => (f : M → N) ∘ v) '' {x : Fin 1 → M | x 0 ∈ X}
      = {x : Fin 1 → N | x 0 ∈ (f : M → N) '' X} := by
    ext w
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact ⟨v 0, hv, rfl⟩
    · rintro ⟨x, hx, hfx⟩
      refine ⟨fun _ => x, hx, ?_⟩
      funext i
      rw [Subsingleton.elim i (0 : Fin 1)]
      exact hfx
  rw [Set.Definable₁, ← hset]
  exact hd

/-- **Uncountable categoricity rules out Vaughtian pairs.**

If `T` is a complete theory in a countable language which is `κ`-categorical for some
uncountable `κ`, and two-cardinal transfer to `κ` is available, then `T` has no Vaughtian pair.

The "saturation" input of the classical argument is not needed as a hypothesis: the existence of
a model of cardinality `κ` in which *every* infinite definable set has cardinality `κ` is
supplied by `Theory.exists_model_of_card_definably_full`, and `κ`-categoricity then forces
*every* model of cardinality `κ` to have that property. -/
theorem not_hasVaughtianPair_of_categorical (hL : L.card ≤ ℵ₀) {T : L.Theory}
    (hT : T.IsComplete) {κ : Cardinal.{0}} (hκ : ℵ₀ < κ) (hcat : κ.Categorical T)
    (hTC : TwoCardinalTransfer L κ) : ¬HasVaughtianPair T := by
  intro hVP
  obtain ⟨M₂, A, X, hdef, hM₂, hX⟩ := hTC T hL hT hVP
  obtain ⟨M₁, hM₁, hfull⟩ :=
    Theory.exists_model_of_card_definably_full T hL
      (exists_infinite_model_of_hasVaughtianPair hVP) hκ.le
  obtain ⟨f⟩ := hcat M₂ M₁ hM₂ hM₁
  have hXinf : X.Infinite := by
    rw [← Set.infinite_coe_iff, Cardinal.infinite_iff, hX]
  have hfinj : Function.Injective (⇑f) := EquivLike.injective f
  have himg : ((⇑f) '' X).Infinite := hXinf.image hfinj.injOn
  have hfull' := hfull ((⇑f) '' A)
    (n := 1) {x : Fin 1 → M₁ | x 0 ∈ (⇑f) '' X}
    (definable₁_image_equiv f hdef) (infinite_finOneSet himg)
  rw [mk_finOneSet, Cardinal.mk_image_eq hfinj, hX, hM₁] at hfull'
  exact absurd hfull' hκ.ne

/-- The same statement in the form used by the categoricity chapter: with the two-cardinal
theorem at `ℵ₁` available, an `ℵ₁`-categorical complete theory in a countable language has no
Vaughtian pair. -/
theorem not_hasVaughtianPair_of_categorical_aleph1 (hL : L.card ≤ ℵ₀) {T : L.Theory}
    (hT : T.IsComplete) (hcat : (ℵ₁ : Cardinal.{0}).Categorical T) (hVTC : VaughtTwoCardinal L) :
    ¬HasVaughtianPair T :=
  not_hasVaughtianPair_of_categorical hL hT (aleph0_lt_aleph_one) hcat hVTC

end Submission.Morley
