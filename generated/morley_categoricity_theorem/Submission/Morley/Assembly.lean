import Mathlib
import Submission.Morley.Saturated
import Submission.Morley.Transfer
import Submission.Morley.Bridge
import Submission.Morley.Chains

/-!
# Final assembly of Morley's categoricity theorem

This file puts together the chapters of the development into Morley's categoricity theorem,
`Submission.Morley.morley_categoricity`, and isolates precisely what is still missing.

## The shape of the argument

Let `T` be a complete theory with only infinite models, in a countable language, and suppose `T`
is `κ`-categorical for some uncountable `κ`.

1. `Submission.Morley.isOmegaStable_of_categorical` (with the Ehrenfeucht–Mostowski bound
   discharged by `Submission.Morley.emTypeBound`) makes `T` ω-stable, and
   `Submission.Morley.stable_of_omegaStable` makes it `λ`-stable for every infinite `λ`.
2. `Submission.Morley.not_hasVaughtianPair_of_categorical'` rules out Vaughtian pairs.  It uses
   that every model of cardinality `κ` of a `κ`-categorical theory is definably full
   (`Submission.Morley.definablyFull_of_categorical`, proved here), so that `T` cannot have a
   model of cardinality `κ` with a small infinite definable subset — *given* that a Vaughtian pair
   produces one, `Submission.Morley.OmegaStableTwoCardinal`.
3. ω-stability together with the absence of Vaughtian pairs makes **every model of uncountable
   cardinality saturated**.  This is `Submission.Morley.SaturationPrinciple`, and it is the piece
   that is *not* proved (see "What is missing" below).
4. Two models of the same uncountable cardinality `μ` are then both saturated, and elementarily
   equivalent because `T` is complete, so `Submission.Morley.nonempty_equiv_of_isSaturated`
   makes them isomorphic.  This is `Submission.Morley.categorical_of_forall_isSaturated`, proved
   here unconditionally.

## Main definitions

* `Submission.Morley.SaturationPrinciple`: ω-stable + no Vaughtian pair implies every uncountable
  model is saturated.
* `Submission.Morley.DefinablyFullSaturation`: the same with the absence of Vaughtian pairs
  replaced by the property it is used through, definable fullness of the model at hand.  This is
  the form in which the missing argument should be attacked;
  `Submission.Morley.saturationPrinciple_of_definablyFullSaturation` shows it is enough.
* `Submission.Morley.OmegaStableTwoCardinal`: an ω-stable theory with a Vaughtian pair has, in
  every uncountable `κ`, a model of cardinality `κ` with an infinite definable subset of
  cardinality `< κ`.

## Main results

* `Submission.Morley.infinite_setOf_mem_typeOfElem`: every formula of an omitted `1`-type defines
  an infinite subset of the model.  Unconditional; the first step of (3).
* `Submission.Morley.definablyFull_of_equiv`: definable fullness transports along an isomorphism.
* `Submission.Morley.definablyFull_of_categorical`: in a `κ`-categorical theory **every** model of
  cardinality `κ` is definably full.  Unconditional.
* `Submission.Morley.not_hasTwoCardinalModel_of_categorical`: a `κ`-categorical theory has no
  `(κ, lam)`-model with `ℵ₀ ≤ lam < κ`.  Unconditional.
* `Submission.Morley.categorical_of_forall_isSaturated`: if all models of cardinality `μ` are
  saturated then `T` is `μ`-categorical.  Unconditional.
* `Submission.Morley.morley_categoricity`: **Morley's categoricity theorem**, modulo
  `SaturationPrinciple L` and `OmegaStableTwoCardinal L`.
* `Submission.Morley.morley_categoricity_aleph1`: the `ℵ₁`-categorical case, where two-cardinal
  transfer is available (`Submission.Morley.vaughtTwoCardinal`), so that
  `SaturationPrinciple L` is the *only* remaining hypothesis.

## What is missing

Two statements are used as hypotheses.  Both are true theorems; neither is proved here.

**(1) `SaturationPrinciple L`.**  "`T` ω-stable with no Vaughtian pairs ⟹ every model of
uncountable cardinality is saturated."  What the absence of Vaughtian pairs supplies is exactly
definable fullness (`Submission.Morley.definablyFull_of_not_hasVaughtianPair`): in a model `M`,
every infinite set definable with parameters from a set of size `< #M` has size `#M`.  Together
with `λ`-stability this is *not* enough on its own.  Given `A ⊆ M` with `#A < #M` and an omitted
`p ∈ S₁(A)`, one gets (by `Submission.Morley.infinite_setOf_mem_typeOfElem` and definable
fullness) that every formula of `p` defines a subset of `M` of size `#M`, and that there are at
most `#A + ℵ₀` types over `A`; but a decreasing family of definable sets of full size can have
empty intersection, so the counting stops there.  The classical proofs supply the missing
structure by Morley rank: pick `φ ∈ p` of least Morley rank and Morley degree one, so that every
element of `φ(M)` has strictly smaller rank over `A`, and use additivity of rank in fibrations to
see that `≤ #A + ℵ₀` sets of smaller rank cannot cover `φ(M)`.  (The Baldwin–Lachlan route
replaces this by a strongly minimal formula and a dimension theory for algebraic closure.)  Either
way the missing input is a theory of Morley rank, which this development does not have.

**(2) `OmegaStableTwoCardinal L`.**  `Submission.Morley.Chains` proves Vaught's two-cardinal
theorem, `Submission.Morley.TwoCardinalTransfer L ℵ₁`, and `ℵ₁` there is *sharp*: the `ω₁`-chain
of copies of a countable homogeneous pair cannot be continued past `ω₁`, because at a limit stage
of uncountable cofinality the union is no longer countable and can no longer be re-coordinatised
as a copy of the countable pair.  For `κ > ℵ₁`, `TwoCardinalTransfer L κ` is *not* a consequence
of the `ℵ₁` case in ZFC — this is the classical two-cardinal transfer problem — which is why the
hypothesis used here, `OmegaStableTwoCardinal L`, carries ω-stability: the chain has then to be
run over homogeneous pairs of larger cardinality, whose existence comes from `λ`-stability.
Consequently `Submission.Morley.morley_categoricity_aleph1` — categoricity at `ℵ₁` — needs only
hypothesis (1).
-/

universe u v w

namespace Submission.Morley

open Cardinal Set FirstOrder FirstOrder.Language

/-! ## Omitted types

A first step of the missing saturation argument, and the point at which definable fullness gets
applied: every formula of an omitted type defines an infinite subset of the model. -/

section Omitted

variable {L : FirstOrder.Language.{u, v}} {M : Type w} [L.Structure M] [Nonempty M] {A : Set M}

/-- A formula with parameters in `A ⊆ M` which belongs to some complete type over `A` is realised
in `M` itself: consistency with `Th(M_A)` is realisability in `M`. -/
theorem exists_mem_typeOfElem_of_mem {p : S₁ L A} {φ : Form1 L A} (hφ : φ ∈ p) :
    ∃ a : M, φ ∈ typeOfElem A a := by
  classical
  obtain ⟨v, hv⟩ :=
    (typesWith_nonempty_iff_exists_realize L A φ).1
      ⟨p, (Theory.CompleteType.mem_typesWith_iff φ p).2 hφ⟩
  refine ⟨v 0, ?_⟩
  rw [mem_typeOfElem]
  have hv0 : (fun _ : Fin 1 => v 0) = v := funext fun i => by
    rw [Subsingleton.elim i (0 : Fin 1)]
  rw [hv0]
  exact hv

/-- **Every formula of an omitted type defines an infinite set.**

If a complete `1`-type `p` over a parameter set `A ⊆ M` is *not* realised in `M`, then every
formula of `p` is satisfied by infinitely many elements of `M`: a formula of `p` satisfied by only
finitely many elements can be cut down, using one separating formula of `p` for each of them, to a
formula of `p` satisfied by none — contradicting consistency.

Together with `FirstOrder.Language.DefinablyFull` this gives that every formula of an omitted type
defines a subset of `M` of cardinality `#M`, which is the starting point of the argument that an
ω-stable theory without Vaughtian pairs has saturated uncountable models. -/
theorem infinite_setOf_mem_typeOfElem {p : S₁ L A}
    (hp : p ∉ (paramTheory L A).realizedTypes M (Fin 1)) {φ : Form1 L A} (hφ : φ ∈ p) :
    {a : M | φ ∈ typeOfElem A a}.Infinite := by
  classical
  -- since `p` is omitted, every element of `M` is separated from `p` by a formula of `p`
  have hsep : ∀ b : M, ∃ ψ : Form1 L A, ψ ∈ p ∧ ψ ∉ typeOfElem A b := by
    intro b
    by_contra hcon
    push Not at hcon
    exact hp (mem_realizedTypes_one_iff.2
      ⟨b, (Theory.CompleteType.eq_of_le (p := p) (q := typeOfElem A b)
        fun ψ hψ => hcon ψ hψ).symm⟩)
  -- hence every formula of `p` is realised outside any prescribed finite set
  have key : ∀ (F : Finset M) (ψ : Form1 L A), ψ ∈ p → ∃ a : M, a ∉ F ∧ ψ ∈ typeOfElem A a := by
    intro F
    induction F using Finset.induction with
    | empty =>
      intro ψ hψ
      obtain ⟨a, ha⟩ := exists_mem_typeOfElem_of_mem hψ
      exact ⟨a, by simp, ha⟩
    | @insert b F _ IH =>
      intro ψ hψ
      obtain ⟨χ, hχp, hχb⟩ := hsep b
      obtain ⟨a, haF, ha⟩ := IH (ψ ⊓ χ) ((Theory.CompleteType.inf_mem_iff _ _ _).2 ⟨hψ, hχp⟩)
      rw [Theory.CompleteType.inf_mem_iff] at ha
      refine ⟨a, ?_, ha.1⟩
      simp only [Finset.mem_insert, not_or]
      exact ⟨fun h => hχb (h ▸ ha.2), haF⟩
  intro hfin
  obtain ⟨a, haF, ha⟩ := key hfin.toFinset φ hφ
  exact haF ((Set.Finite.mem_toFinset hfin).2 ha)

end Omitted

variable {L : FirstOrder.Language.{0, 0}}

/-! ## Definable fullness -/

/-- **Definable fullness transports along an isomorphism of structures.** -/
theorem definablyFull_of_equiv {M N : Type} [L.Structure M] [L.Structure N] (f : M ≃[L] N)
    (hN : L.DefinablyFull N) : L.DefinablyFull M := by
  intro A n S hS hSinf
  have hinj : Function.Injective fun v : Fin n → M => (f : M → N) ∘ v := fun v w h =>
    funext fun i => EquivLike.injective f (congrFun h i)
  have himg := hN ((f : M → N) '' A) ((fun v : Fin n → M => (f : M → N) ∘ v) '' S)
    (definable_image_equiv f hS) (hSinf.image hinj.injOn)
  rw [Cardinal.mk_image_eq hinj] at himg
  rw [himg]
  exact (Cardinal.mk_congr f.toEquiv).symm

/-- **In a `κ`-categorical theory every model of cardinality `κ` is definably full**: every
infinite parameter-definable set has cardinality `κ`.

`Submission.Morley.Port.DefinablyFull` produces *one* model of cardinality `κ` with that property,
and categoricity spreads it to all of them. -/
theorem definablyFull_of_categorical (hL : L.card ≤ ℵ₀) {T : L.Theory}
    (hInf : ∃ M : T.ModelType.{0, 0, 0}, Infinite M) {κ : Cardinal.{0}} (hκ : ℵ₀ ≤ κ)
    (hcat : κ.Categorical T) (M : T.ModelType.{0, 0, 0}) (hM : #M = κ) :
    L.DefinablyFull (M : Type) := by
  obtain ⟨M₁, hM₁, hfull⟩ := Theory.exists_model_of_card_definably_full T hL hInf hκ
  obtain ⟨f⟩ := hcat M M₁ hM hM₁
  exact definablyFull_of_equiv f hfull

/-! ## From saturation to categoricity -/

/-- **Saturation gives categoricity.**  If every model of `T` of cardinality `μ` is saturated then
`T` is `μ`-categorical: two saturated models of the same cardinality of a complete theory are
isomorphic. -/
theorem categorical_of_forall_isSaturated {T : L.Theory} (hT : T.IsComplete)
    (hInf : ∀ M : T.ModelType.{0, 0, 0}, Infinite M) {μ : Cardinal.{0}}
    (h : ∀ M : T.ModelType.{0, 0, 0}, #M = μ → IsSaturated M) : μ.Categorical T := by
  intro M N hM hN
  haveI := hInf M
  exact nonempty_equiv_of_isSaturated_of_isComplete hT (h M hM) (h N hN) (by rw [hM, hN])

/-! ## The saturation principle -/

/-- **The saturation principle**, as a hypothesis: an ω-stable theory without Vaughtian pairs, in
a countable language, has all its uncountable models saturated.

This is the one genuinely model-theoretic statement of Morley's theorem that this development does
not prove; see the module documentation. -/
def SaturationPrinciple (L : FirstOrder.Language.{0, 0}) : Prop :=
  ∀ T : L.Theory, L.card ≤ ℵ₀ → T.IsComplete → IsOmegaStable.{0, 0, 0} T → ¬HasVaughtianPair T →
    ∀ M : T.ModelType.{0, 0, 0}, ℵ₀ < #M → IsSaturated M

/-- The saturation principle in the form in which the absence of Vaughtian pairs is actually
consumed: what is used about a model `M` is that it is *definably full*, i.e. that every infinite
set definable with parameters from a set of size `< #M` already has size `#M`. -/
def DefinablyFullSaturation (L : FirstOrder.Language.{0, 0}) : Prop :=
  ∀ T : L.Theory, L.card ≤ ℵ₀ → T.IsComplete → IsOmegaStable.{0, 0, 0} T →
    ∀ M : T.ModelType.{0, 0, 0}, ℵ₀ < #M → L.DefinablyFull (M : Type) → IsSaturated M

/-- The definably-full form of the saturation principle implies the Vaughtian-pair form, because
a theory without Vaughtian pairs has all of its models definably full
(`Submission.Morley.definablyFull_of_not_hasVaughtianPair`). -/
theorem saturationPrinciple_of_definablyFullSaturation (h : DefinablyFullSaturation L) :
    SaturationPrinciple L := fun T hL hT hos hvp M hM =>
  h T hL hT hos M hM (definablyFull_of_not_hasVaughtianPair hL hvp M)

/-- **The engine of the theorem.**  For an ω-stable theory, categoricity in an uncountable `μ`
follows from definable fullness of the models of cardinality `μ` alone: those models are then
saturated, hence isomorphic.

This isolates what the cardinal `μ` has to satisfy, and is the form in which the two remaining
hypotheses are consumed below. -/
theorem categorical_of_definablyFull (hSat : DefinablyFullSaturation L) (hL : L.card ≤ ℵ₀)
    {T : L.Theory} (hT : T.IsComplete) (hInf : ∀ M : T.ModelType.{0, 0, 0}, Infinite M)
    (hos : IsOmegaStable.{0, 0, 0} T) {μ : Cardinal.{0}} (hμ : ℵ₀ < μ)
    (hdf : ∀ M : T.ModelType.{0, 0, 0}, #M = μ → L.DefinablyFull (M : Type)) :
    μ.Categorical T :=
  categorical_of_forall_isSaturated hT hInf fun M hM =>
    hSat T hL hT hos M (by rw [hM]; exact hμ) (hdf M hM)

/-- **At the cardinal of categoricity no two-cardinal transfer is needed**: every model of a
`κ`-categorical theory of cardinality `κ` is definably full
(`Submission.Morley.definablyFull_of_categorical`), hence saturated.

The whole difficulty of Morley's theorem is to move this from `κ` to another uncountable
cardinal. -/
theorem isSaturated_of_categorical (hSat : DefinablyFullSaturation L) (hL : L.card ≤ ℵ₀)
    {T : L.Theory} (hT : T.IsComplete) (hInf : ∀ M : T.ModelType.{0, 0, 0}, Infinite M)
    {κ : Cardinal.{0}} (hκ : ℵ₀ < κ) (hcat : κ.Categorical T) (M : T.ModelType.{0, 0, 0})
    (hM : #M = κ) : IsSaturated M :=
  hSat T hL hT (isOmegaStable_of_categorical (emTypeBound L hL) hL hT hInf hκ hcat) M
    (by rw [hM]; exact hκ)
    (definablyFull_of_categorical hL ⟨M, hInf M⟩ hκ.le hcat M hM)

/-! ## Ruling out Vaughtian pairs -/

/-- **A `κ`-categorical theory has no two-cardinal model at `κ`**: no model of cardinality `κ` has
an infinite parameter-definable subset of cardinality `< κ`.  Immediate from
`Submission.Morley.definablyFull_of_categorical`. -/
theorem not_hasTwoCardinalModel_of_categorical (hL : L.card ≤ ℵ₀) {T : L.Theory}
    (hInf : ∀ M : T.ModelType.{0, 0, 0}, Infinite M) {κ : Cardinal.{0}} (hκ : ℵ₀ ≤ κ)
    (hcat : κ.Categorical T) {lam : Cardinal.{0}} (hlam : ℵ₀ ≤ lam) (hlt : lam < κ) :
    ¬HasTwoCardinalModel T κ lam := by
  rintro ⟨M, A, X, hdef, hMκ, hXlam⟩
  have hXinf : X.Infinite := by
    rw [← Set.infinite_coe_iff, Cardinal.infinite_iff, hXlam]
    exact hlam
  have hfull := definablyFull_of_categorical hL ⟨M, hInf M⟩ hκ hcat M hMκ
    A (n := 1) {x : Fin 1 → M | x 0 ∈ X} hdef (infinite_finOneSet hXinf)
  rw [mk_finOneSet, hXlam, hMκ] at hfull
  exact absurd hfull hlt.ne

/-- **Two-cardinal transfer for ω-stable theories**, as a hypothesis: an ω-stable complete theory
in a countable language which has a Vaughtian pair has, in *every* uncountable cardinal `κ`, a
model of cardinality `κ` containing an infinite parameter-definable subset of cardinality `< κ`.

Unlike `Submission.Morley.TwoCardinalTransfer L κ` — which for `κ > ℵ₁` is not a consequence of
ZFC — this is a genuine theorem, but its proof needs ω-stability; see the module documentation.
At `κ = ℵ₁` it is Vaught's two-cardinal theorem, proved in `Submission.Morley.Chains`. -/
def OmegaStableTwoCardinal (L : FirstOrder.Language.{0, 0}) : Prop :=
  ∀ T : L.Theory, L.card ≤ ℵ₀ → T.IsComplete → IsOmegaStable.{0, 0, 0} T → HasVaughtianPair T →
    ∀ κ : Cardinal.{0}, ℵ₀ < κ →
      ∃ lam : Cardinal.{0}, ℵ₀ ≤ lam ∧ lam < κ ∧ HasTwoCardinalModel T κ lam

/-- **Uncountable categoricity rules out Vaughtian pairs**, given two-cardinal transfer for
ω-stable theories. -/
theorem not_hasVaughtianPair_of_categorical' (hTC : OmegaStableTwoCardinal L) (hL : L.card ≤ ℵ₀)
    {T : L.Theory} (hT : T.IsComplete) (hInf : ∀ M : T.ModelType.{0, 0, 0}, Infinite M)
    (hos : IsOmegaStable.{0, 0, 0} T) {κ : Cardinal.{0}} (hκ : ℵ₀ < κ) (hcat : κ.Categorical T) :
    ¬HasVaughtianPair T := fun hVP => by
  obtain ⟨lam, hlam, hlt, hmodel⟩ := hTC T hL hT hos hVP κ hκ
  exact not_hasTwoCardinalModel_of_categorical hL hInf hκ.le hcat hlam hlt hmodel

/-! ## Morley's categoricity theorem -/

/-- **Morley's categoricity theorem, given the absence of Vaughtian pairs.**  Everything in this
statement except the saturation principle is proved in this development. -/
theorem morley_categoricity_of_not_hasVaughtianPair (hSat : SaturationPrinciple L)
    (hL : L.card ≤ ℵ₀) {T : L.Theory} (hT : T.IsComplete)
    (hInf : ∀ M : T.ModelType.{0, 0, 0}, Infinite M) (hos : IsOmegaStable.{0, 0, 0} T)
    (hvp : ¬HasVaughtianPair T) {μ : Cardinal.{0}} (hμ : ℵ₀ < μ) : μ.Categorical T :=
  categorical_of_forall_isSaturated hT hInf fun M hM =>
    hSat T hL hT hos hvp M (by rw [hM]; exact hμ)

/-- **Morley's categoricity theorem.**  A complete theory with only infinite models, in a
countable language, which is categorical in one uncountable cardinal `κ`, is categorical in every
uncountable cardinal.

Two inputs are taken as hypotheses, both of them true theorems that this development does not
prove: the saturation principle `Submission.Morley.SaturationPrinciple`, and two-cardinal transfer
for ω-stable theories `Submission.Morley.OmegaStableTwoCardinal`.  Everything else — ω-stability
from categoricity, the passage from two-cardinal transfer to the absence of Vaughtian pairs, and
the uniqueness of saturated models — is proved here.  See
`Submission.Morley.morley_categoricity_aleph1` for the case `κ = ℵ₁`, where the second hypothesis
is discharged by Vaught's two-cardinal theorem. -/
theorem morley_categoricity (hSat : SaturationPrinciple L) (hTC : OmegaStableTwoCardinal L)
    (hL : L.card ≤ ℵ₀) {T : L.Theory} (hT : T.IsComplete)
    (hInf : ∀ M : T.ModelType.{0, 0, 0}, Infinite M) {κ : Cardinal.{0}} (hκ : ℵ₀ < κ)
    (hcat : κ.Categorical T) {μ : Cardinal.{0}} (hμ : ℵ₀ < μ) : μ.Categorical T :=
  have hos : IsOmegaStable.{0, 0, 0} T :=
    isOmegaStable_of_categorical (emTypeBound L hL) hL hT hInf hκ hcat
  morley_categoricity_of_not_hasVaughtianPair hSat hL hT hInf hos
    (not_hasVaughtianPair_of_categorical' hTC hL hT hInf hos hκ hcat) hμ

/-- **Morley's categoricity theorem at `ℵ₁`.**  For a theory categorical in `ℵ₁`, two-cardinal
transfer is Vaught's two-cardinal theorem (`Submission.Morley.vaughtTwoCardinal`), which *is*
proved in this development; so the saturation principle is the only hypothesis left. -/
theorem morley_categoricity_aleph1 (hSat : SaturationPrinciple L) (hL : L.card ≤ ℵ₀)
    {T : L.Theory} (hT : T.IsComplete) (hInf : ∀ M : T.ModelType.{0, 0, 0}, Infinite M)
    (hcat : (ℵ₁ : Cardinal.{0}).Categorical T) {μ : Cardinal.{0}} (hμ : ℵ₀ < μ) :
    μ.Categorical T :=
  morley_categoricity_of_not_hasVaughtianPair hSat hL hT hInf
    (isOmegaStable_of_categorical (emTypeBound L hL) hL hT hInf aleph0_lt_aleph_one hcat)
    (not_hasVaughtianPair_of_categorical_aleph1 hL hT hcat (vaughtTwoCardinal L)) hμ

end Submission.Morley
