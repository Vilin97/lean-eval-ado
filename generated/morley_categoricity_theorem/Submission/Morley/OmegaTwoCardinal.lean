import Mathlib
import Submission.Morley.Chains
import Submission.Morley.Assembly
import Submission.Morley.PrimeExists

/-!
# Two-cardinal transfer for `ω`-stable theories

This file works towards `Submission.Morley.OmegaStableTwoCardinal`: an `ω`-stable complete theory
in a countable language with a Vaughtian pair has, for every uncountable `κ`, a model of
cardinality `κ` carrying an infinite definable set of cardinality `< κ`.

## The classical proof

`Submission.Morley.Chains.vaughtTwoCardinal` supplies the base case: a Vaughtian pair yields an
`(ℵ₁, ℵ₀)`-model, and its `ω₁`-tower of copies of a *countable* homogeneous pair is sharp — at a
limit stage of uncountable cofinality the colimit is no longer countable and cannot be
re-coordinatised as a copy of the pair.  (The same obstruction reappears one level up: a
`λ`-homogeneous pair of size `λ` would push the tower to `λ⁺`, but `λ`-homogeneity is *not*
inherited by unions of chains of cofinality `< λ`, whereas `ω`-homogeneity is inherited by unions
of chains of every length because finite tuples always live in a single stage.  So towers of
copies of a fixed pair cannot reach limit cardinals at all.)

The classical route past `ℵ₁` is not a tower but a **chain of prime model extensions**, and it
uses `ω`-stability twice:

1. *(`Submission.Morley.exists_omega1Minimal`, proved here.)*  In an uncountable model `M` of an
   `ω`-stable theory some definable set is `ℵ₁`-**minimal**: uncountable, with every definable
   subset countable or co-countable in it.  Otherwise one splits an uncountable definable set into
   two uncountable definable pieces over and over, producing a binary tree of formulas which
   descends to a countable parameter set and contradicts `ω`-stability.
2. *(`Submission.Morley.exists_genericType`, proved here.)*  The formulas that hold on all but
   countably many points of an `ℵ₁`-minimal set form a complete type `p` over `M` **every
   countable subset of which has uncountably many realisations in `M` itself**.
3. *(Not proved here.)*  Let `c` realise `p` in an elementary extension of `M` — since `p` is a
   complete type over the whole of `M` it contains `v ≠ a` for every `a : M`, so `c ∉ M` — and let
   `N` be a model containing `M ∪ {c}` in which every element realises an **isolated** type over
   `M ∪ {c}`; that is, a prime model over `M ∪ {c}`.  Then every countable type over `M` realised
   in `N` is already realised in `M`: if `b ∈ N` realises the countable type `Γ` and `θ(w, c)`
   isolates `tp(b / M ∪ {c})`, then `Δ = {∃w θ(w, v)} ∪ {∀w (θ(w, v) → γ(w)) | γ ∈ Γ}` is a
   countable subset of `p`, hence is realised by some `c' ∈ M` by (2), and any `b'` with
   `θ(b', c')` realises `Γ` inside `M`.
4. *(Not proved here.)*  Apply (3) to `Γ(v) = {χ(v)} ∪ {v ≠ m | m ∈ χ(M)}`, which is countable
   when `χ(M)` is and is omitted in `M`: the extension `N ⊋ M` has `χ(N) = χ(M)`.  Iterating this
   along a continuous elementary chain of length `κ`, with unions at limits (where the definable
   set does not grow either, since every element of a union of a chain lies in a stage), produces
   a model of cardinality `κ` whose `χ`-definable set is still countable.
5. *(`Submission.Morley.hasTwoCardinalModel_of_le` and
   `Submission.Morley.omegaStableTwoCardinal_of_largeTwoCardinalModels`, proved here.)*  Downward
   Löwenheim–Skolem pins the cardinality of the big side to `κ` exactly, keeping the whole
   definable set inside the substructure so that the small side is untouched.

## What is proved here

* `Submission.Morley.hasTwoCardinalModel_of_le`: a `(μ, lam)`-model with `lam ≤ κ ≤ μ` yields a
  `(κ, lam)`-model.  This is step (5), and it is what makes step (4) only have to produce models
  of cardinality *at least* `κ`.
* `Submission.Morley.omegaStableTwoCardinal_of_largeTwoCardinalModels`:
  `Submission.Morley.OmegaStableTwoCardinal` follows from `Submission.Morley.LargeTwoCardinalModels`,
  the supply of two-cardinal models of arbitrarily large size.
* `Submission.Morley.exists_hasTwoCardinalModel_of_le_aleph1`: the conclusion of
  `Submission.Morley.OmegaStableTwoCardinal` for `ℵ₀ < κ ≤ ℵ₁`, from Vaught's two-cardinal
  theorem; no `ω`-stability needed.
* `Submission.Morley.exists_omega1Minimal` and `Submission.Morley.exists_genericType`: steps (1)
  and (2), the whole `ω`-stability input to the argument.
* `Submission.Morley.exists_prime_defSet_mk_eq`: the prime-model step over a *countable*
  parameter set, from `Submission.Morley.exists_prime_of_isOmegaStable`.

## What is missing

Steps (3) and (4).  Step (3) needs a **prime model over `M ∪ {c}` for an uncountable `M`**;
`Submission.Morley.exists_prime_of_isOmegaStable` only provides prime models over *countable*
parameter sets, and the parameter set here is a whole uncountable model.  The transfinite
bookkeeping is the missing piece: a maximal `A`-constructible subset of an elementary extension
(one new element at a time, each realising an isolated type over the parameters accumulated so
far, Tarski–Vaught closure by maximality, atomicity by `isIsolated_typeOf_trans` along the
construction order).  Alternatively, inside an ambient `#M⁺`-saturated and `#M⁺`-homogeneous
elementary extension, the set of elements realising an isolated type over `M ∪ {c}` is already an
elementary substructure, and only 1-types are needed for step (3).

Step (4) is the transfinite elementary chain, which the cardinality bookkeeping of step (5)
reduces to producing models of size *at least* `κ`.
-/

namespace Submission.Morley

open Cardinal Set FirstOrder FirstOrder.Language

variable {L : FirstOrder.Language.{0, 0}}

/-! ## Shrinking the big side of a two-cardinal model -/

/-- **Downward Löwenheim–Skolem for two-cardinal models.** -/
theorem hasTwoCardinalModel_of_le (hL : L.card ≤ ℵ₀) {T : L.Theory} {κ lam μ : Cardinal.{0}}
    (hlam : ℵ₀ ≤ lam) (hlamκ : lam ≤ κ) (hκμ : κ ≤ μ) (h : HasTwoCardinalModel T μ lam) :
    HasTwoCardinalModel T κ lam := by
  classical
  obtain ⟨M, A, X, hdef, hMμ, hXlam⟩ := h
  obtain ⟨β, hβ, χ, b, -, hXchar⟩ := exists_boundedFormula_of_definable₁ hdef
  haveI : Finite β := hβ
  have hκ : ℵ₀ ≤ κ := hlam.trans hlamκ
  obtain ⟨N, hsub, hNcard⟩ :=
    exists_elementarySubstructure_card_eq L (X ∪ Set.range b) κ hκ
      (by
        simp only [Cardinal.lift_id]
        refine (Cardinal.mk_union_le _ _).trans ?_
        exact Cardinal.add_le_of_le hκ (hXlam ▸ hlamκ)
          ((Set.finite_range b).lt_aleph0.le.trans hκ))
      (by simpa using hL.trans hκ)
      (by
        simp only [Cardinal.lift_id]
        exact hMμ ▸ hκμ)
  simp only [Cardinal.lift_id] at hNcard
  haveI : Nonempty ↥N :=
    Cardinal.mk_ne_zero_iff.1 (by rw [hNcard]; exact (aleph0_pos.trans_le hκ).ne')
  set b' : β → ↥N := fun i => ⟨b i, hsub (Set.mem_union_right _ ⟨i, rfl⟩)⟩
  have hreal : ∀ a : ↥N,
      χ.Realize b' (fun _ => a) ↔ (a : M) ∈ X := by
    intro a
    have h := N.subtype.map_boundedFormula χ b' (fun _ : Fin 1 => a)
    have e1 : (N.subtype : ↥N → M) ∘ b' = b := rfl
    have e2 : (N.subtype : ↥N → M) ∘ (fun _ : Fin 1 => a) = fun _ => (a : M) := rfl
    rw [e1, e2] at h
    rw [← h, ← hXchar]
  have hset : {a : ↥N | χ.Realize b' fun _ => a}
      = (Subtype.val : ↥N → M) ⁻¹' X := by
    ext a
    simpa using hreal a
  have hcard : #{a : ↥N | χ.Realize b' fun _ => a} = lam := by
    have himg : (Subtype.val : ↥N → M) '' ((Subtype.val : ↥N → M) ⁻¹' X) = X := by
      rw [Set.image_preimage_eq_inter_range]
      refine Set.inter_eq_self_of_subset_left ?_
      intro x hx
      exact ⟨⟨x, hsub (Set.mem_union_left _ hx)⟩, rfl⟩
    have h2 : #↥((Subtype.val : ↥N → M) '' ((Subtype.val : ↥N → M) ⁻¹' X))
        = #↥((Subtype.val : ↥N → M) ⁻¹' X) := Cardinal.mk_image_eq Subtype.val_injective
    rw [hset, ← h2, himg, hXlam]
  exact hasTwoCardinalModel_of_boundedFormula (T := T) ↥N χ b' hNcard hcard

/-! ## Solution sets of formulas with parameters -/

section SolSet

variable {M : Type} [L.Structure M]

/-- The subset of `M` defined by a formula in one free variable with parameters in `A ⊆ M`. -/
def solSet (A : Set M) (φ : Form1 L A) : Set M :=
  {a : M | (Formula.equivSentence.symm φ).Realize (fun _ : Fin 1 => a)}

theorem mem_solSet {A : Set M} {φ : Form1 L A} {a : M} :
    a ∈ solSet A φ ↔ (Formula.equivSentence.symm φ).Realize (fun _ : Fin 1 => a) := Iff.rfl

@[simp]
theorem solSet_inf (A : Set M) (φ ψ : Form1 L A) :
    solSet A (φ ⊓ ψ) = solSet A φ ∩ solSet A ψ := by
  ext a
  simp only [mem_solSet, equivSentence_symm_inf, Formula.realize_inf, Set.mem_inter_iff]

@[simp]
theorem solSet_not (A : Set M) (φ : Form1 L A) : solSet A (∼φ) = (solSet A φ)ᶜ := by
  ext a
  simp only [mem_solSet, equivSentence_symm_not, Formula.realize_not, Set.mem_compl_iff]

variable (L) in
/-- The tautology, as a formula in one free variable with parameters in `A`. -/
def topForm1 (A : Set M) : Form1 L A :=
  Formula.equivSentence (⊤ : (L[[A]]).Formula (Fin 1))

@[simp]
theorem solSet_topForm1 (A : Set M) : solSet A (topForm1 L A) = Set.univ := by
  ext a
  simp [mem_solSet, topForm1]

/-- Consistency of a formula with parameters in `A` with `Th(M_A)` is nonemptiness of the set it
defines in `M`. -/
theorem typesWith_nonempty_iff_solSet_nonempty [Nonempty M] (A : Set M) (φ : Form1 L A) :
    ((paramTheory L A).typesWith φ).Nonempty ↔ (solSet A φ).Nonempty := by
  rw [typesWith_nonempty_iff_exists_realize]
  constructor
  · rintro ⟨v, hv⟩
    refine ⟨v 0, ?_⟩
    have hv0 : (fun _ : Fin 1 => v 0) = v :=
      funext fun i => by rw [Subsingleton.elim i (0 : Fin 1)]
    rw [mem_solSet, hv0]
    exact hv
  · rintro ⟨a, ha⟩
    exact ⟨fun _ => a, ha⟩

theorem not_nonempty_typesWith_of_solSet_eq_empty [Nonempty M] {A : Set M} {φ : Form1 L A}
    (h : solSet A φ = ∅) : ¬ ((paramTheory L A).typesWith φ).Nonempty := by
  rw [typesWith_nonempty_iff_solSet_nonempty, h]
  exact Set.not_nonempty_empty

end SolSet

/-! ## The `ℵ₁`-minimal definable set of an `ω`-stable theory

This is the point at which `ω`-stability enters the classical proof of two-cardinal transfer
(Morley; see also Vaught).  In an uncountable model of an `ω`-stable theory some definable set is
*`ℵ₁`-minimal*: it is uncountable, and every definable subset of it is countable or has countable
complement in it.  Otherwise one splits an uncountable definable set into two uncountable pieces
over and over, producing a binary tree of formulas over a countable parameter set and hence
continuum-many types over it. -/

/-- **An uncountable model of an `ω`-stable theory has an `ℵ₁`-minimal definable set.** -/
theorem exists_omega1Minimal {T : L.Theory} (hst : OmegaStable.{0, 0, 0} T)
    (M : T.ModelType.{0, 0, 0}) (hM : ¬ Countable (M : Type)) :
    ∃ φ₀ : Form1 L (Set.univ : Set M), ¬ (solSet Set.univ φ₀).Countable ∧
      ∀ ψ : Form1 L (Set.univ : Set M),
        (solSet Set.univ (φ₀ ⊓ ψ)).Countable ∨ (solSet Set.univ (φ₀ ⊓ ∼ψ)).Countable := by
  classical
  by_contra hcon
  push Not at hcon
  -- every uncountable definable set splits into two uncountable definable pieces
  have hstep : ∀ φ : Form1 L (Set.univ : Set M), ∃ ψ : Form1 L (Set.univ : Set M),
      ¬ (solSet Set.univ φ).Countable →
        (¬ (solSet Set.univ (φ ⊓ ψ)).Countable ∧ ¬ (solSet Set.univ (φ ⊓ ∼ψ)).Countable) := by
    intro φ
    by_cases h : (solSet Set.univ φ).Countable
    · exact ⟨φ, fun h' => absurd h h'⟩
    · obtain ⟨ψ, h1, h2⟩ := hcon φ h
      exact ⟨ψ, fun _ => ⟨h1, h2⟩⟩
  choose split hsplit using hstep
  -- the tree of formulas
  obtain ⟨F, hF0, hFcons⟩ : ∃ F : List Bool → Form1 L (Set.univ : Set M),
      F [] = topForm1 L (Set.univ : Set M) ∧
        ∀ (b : Bool) (s : List Bool),
          F (b :: s) = if b then F s ⊓ split (F s) else F s ⊓ ∼(split (F s)) :=
    ⟨fun s => s.rec (topForm1 L (Set.univ : Set M))
      (fun b _ ih => if b then ih ⊓ split ih else ih ⊓ ∼(split ih)), rfl,
      fun b s => by cases b <;> rfl⟩
  have hFsub : ∀ (b : Bool) (s : List Bool), solSet Set.univ (F (b :: s)) ⊆
      solSet Set.univ (F s) := by
    intro b s
    rw [hFcons]
    cases b <;> simp
  have hFbig : ∀ s : List Bool, ¬ (solSet Set.univ (F s)).Countable := by
    intro s
    induction s with
    | nil =>
      rw [hF0, solSet_topForm1]
      intro hc
      exact hM (Set.countable_univ_iff.1 hc)
    | cons b s ih =>
      rw [hFcons]
      cases b
      · exact ((hsplit (F s)) ih).2
      · exact ((hsplit (F s)) ih).1
  have hFne : ∀ s : List Bool, (solSet Set.univ (F s)).Nonempty := by
    intro s
    rw [Set.nonempty_iff_ne_empty]
    intro hc
    exact hFbig s (hc ▸ Set.countable_empty)
  -- and hence a binary tree of formulas over the full parameter set
  have tree : BinaryTree (paramTheory L (Set.univ : Set M)) (Fin 1) :=
    { form := F
      consistent := fun s => (typesWith_nonempty_iff_solSet_nonempty _ _).2 (hFne s)
      mono := fun b s => by
        rw [typesWith_subset_iff_not_nonempty]
        refine not_nonempty_typesWith_of_solSet_eq_empty ?_
        rw [solSet_inf, solSet_not]
        exact Set.eq_empty_of_forall_notMem fun a ha => ha.2 (hFsub b s ha.1)
      disjoint := fun s => by
        rw [typesWith_disjoint_iff_not_nonempty]
        refine not_nonempty_typesWith_of_solSet_eq_empty ?_
        rw [solSet_inf, hFcons false s, hFcons true s]
        simp only [Bool.false_eq_true, if_false, if_true, solSet_inf, solSet_not]
        exact Set.eq_empty_of_forall_notMem fun a ha => ha.1.2 ha.2.2 }
  obtain ⟨A₀, -, hcount, ⟨t₀⟩⟩ := exists_countable_binaryTree tree
  exact not_omegaStable_of_binaryTree M A₀
    (Cardinal.mk_le_aleph0_iff.2 (Set.countable_coe_iff.2 hcount)) t₀ hst

/-- **The generic type of an `ℵ₁`-minimal definable set.**

In an uncountable model `M` of an `ω`-stable theory there is a *complete* set `p` of formulas in
one free variable with parameters in `M` — the set of formulas holding on all but countably many
points of an `ℵ₁`-minimal definable set — with the property that **every countable subset of `p`
has uncountably many realisations in `M` itself**.

This is the second half of the `ω`-stability input to two-cardinal transfer.  `p` is a complete
`1`-type over `M`, so it is omitted in `M` (it contains `v ≠ a` for every `a : M`); a realisation
`c` of `p` in an elementary extension therefore gives a proper extension, while the countable
approximation property is what forces a prime model over `M ∪ {c}` to realise no *new* countable
type over `M`, in particular to add no new element to a countable definable set. -/
theorem exists_genericType {T : L.Theory} (hst : OmegaStable.{0, 0, 0} T)
    (M : T.ModelType.{0, 0, 0}) (hM : ¬ Countable (M : Type)) :
    ∃ p : Set (Form1 L (Set.univ : Set M)),
      (∀ ψ, ψ ∈ p ∨ ∼ψ ∈ p) ∧ (∀ ψ, ψ ∈ p → ∼ψ ∉ p) ∧
        ∀ u : ℕ → Form1 L (Set.univ : Set M), (∀ n, u n ∈ p) →
          ¬ (⋂ n, solSet Set.univ (u n)).Countable := by
  classical
  obtain ⟨φ₀, hbig, hmin⟩ := exists_omega1Minimal hst M hM
  have hsplit : ∀ ψ : Form1 L (Set.univ : Set M),
      solSet Set.univ (φ₀ ⊓ ψ) ∪ solSet Set.univ (φ₀ ⊓ ∼ψ) = solSet Set.univ φ₀ := by
    intro ψ
    simp only [solSet_inf, solSet_not, ← Set.sdiff_eq]
    exact Set.inter_union_sdiff _ _
  refine ⟨{ψ | ¬ (solSet Set.univ (φ₀ ⊓ ψ)).Countable}, fun ψ => ?_, fun ψ h1 h2 => ?_,
    fun u hu hc => ?_⟩
  · by_contra hcon
    push Not at hcon
    simp only [Set.mem_setOf_eq, not_not] at hcon
    exact hbig (hsplit ψ ▸ hcon.1.union hcon.2)
  · simp only [Set.mem_setOf_eq] at h1 h2
    exact (hmin ψ).elim h1 h2
  · simp only [Set.mem_setOf_eq] at hu
    refine hbig ?_
    have hsmall : ∀ n, (solSet Set.univ φ₀ \ solSet Set.univ (u n)).Countable := by
      intro n
      rcases hmin (u n) with h | h
      · exact absurd h (hu n)
      · rwa [solSet_inf, solSet_not, ← Set.sdiff_eq] at h
    have hdiff : (solSet Set.univ φ₀ \ ⋂ n, solSet Set.univ (u n)).Countable := by
      rw [Set.sdiff_iInter]
      exact Set.countable_iUnion hsmall
    refine Set.Countable.mono (fun a ha => ?_) (hc.union hdiff)
    by_cases h : a ∈ ⋂ n, solSet Set.univ (u n)
    · exact Or.inl h
    · exact Or.inr ⟨ha, h⟩

/-! ## The prime-model step

The step the classical proof iterates: pass from a model `M` to a *small* elementary submodel
containing prescribed data, without changing the distinguished definable set.  In an `ω`-stable
theory `Submission.Morley.exists_prime_of_isOmegaStable` produces such a submodel which is
moreover **prime** over the prescribed data, hence embeds elementarily into *every* model
containing them. -/

/-- **The prime model over a countable parameter set carries the same definable set.**

Let `M` be a model of an `ω`-stable theory, let `χ(b̄, ·)` define `X ⊆ M`, and let `B ⊆ M` be a
countable set containing `X` and the parameters `b̄` (this is the Vaughtian situation: `X` is
small, so it fits into a countable parameter set together with any prescribed countable amount of
extra data).  Then the prime model `N` over `B` is countable, sits elementarily in `M` over `B`,
and its `χ`-definable set is carried by the embedding *bijectively* onto `X`.

Primality is the point: `N` embeds elementarily, over `B`, into every model of `T` containing
`B`, so this is the smallest extension of `B` to a model, and the one that a chain construction
should use at each step. -/
theorem exists_prime_defSet_mk_eq (hL : L.card ≤ ℵ₀) {T : L.Theory}
    (hst : IsOmegaStable.{0, 0, 0} T) (M : T.ModelType.{0, 0, 0}) {β : Type} [Finite β]
    (χ : L.BoundedFormula β 1) (b : β → M) (B : Set M) (hB : B.Countable) (hbB : ∀ i, b i ∈ B)
    (hXB : {a : M | χ.Realize b fun _ => a} ⊆ B) :
    ∃ (N : T.ModelType.{0, 0, 0}) (f : N ↪ₑ[L] M) (B' : Set N) (b' : β → N),
      Countable N ∧ IsPrime N B' ∧ (fun x : N => (f x : M)) '' B' = B ∧
        (∀ i, b' i ∈ B') ∧ (∀ i, f (b' i) = b i) ∧
        (fun x : N => (f x : M)) '' {a : N | χ.Realize b' fun _ => a}
          = {a : M | χ.Realize b fun _ => a} ∧
        #{a : N | χ.Realize b' fun _ => a} = #{a : M | χ.Realize b fun _ => a} := by
  classical
  obtain ⟨N, f, B', himg, hcount, hprime⟩ := exists_prime_of_isOmegaStable hL hst M B hB
  have hchoice : ∀ i : β, ∃ x : N, x ∈ B' ∧ f x = b i := by
    intro i
    have : b i ∈ (fun x : N => (f x : M)) '' B' := by rw [himg]; exact hbB i
    obtain ⟨x, hx, hfx⟩ := this
    exact ⟨x, hx, hfx⟩
  choose b' hb'mem hb'eq using hchoice
  have hpre : {a : N | χ.Realize b' fun _ => a}
      = (fun x : N => (f x : M)) ⁻¹' {a : M | χ.Realize b fun _ => a} := by
    ext a
    have h := f.map_boundedFormula χ b' (fun _ : Fin 1 => a)
    have e1 : (f : N → M) ∘ b' = b := funext hb'eq
    have e2 : (f : N → M) ∘ (fun _ : Fin 1 => a) = fun _ => f a := rfl
    rw [e1, e2] at h
    simpa using h.symm
  have hrange : {a : M | χ.Realize b fun _ => a} ⊆ Set.range (fun x : N => (f x : M)) := by
    intro x hx
    have : x ∈ (fun y : N => (f y : M)) '' B' := by rw [himg]; exact hXB hx
    obtain ⟨y, -, hy⟩ := this
    exact ⟨y, hy⟩
  have himg2 : (fun x : N => (f x : M)) '' {a : N | χ.Realize b' fun _ => a}
      = {a : M | χ.Realize b fun _ => a} := by
    rw [hpre, Set.image_preimage_eq_inter_range]
    exact Set.inter_eq_self_of_subset_left hrange
  refine ⟨N, f, B', b', hcount, hprime, himg, hb'mem, hb'eq, himg2, ?_⟩
  rw [← himg2, Cardinal.mk_image_eq f.injective]

/-! ## The reduction to arbitrarily large two-cardinal models -/

/-- The supply of two-cardinal models that `Submission.Morley.OmegaStableTwoCardinal` needs,
stated without the requirement that the big side have *exactly* the prescribed cardinality: an
`ω`-stable theory with a Vaughtian pair has, for every uncountable `κ`, a model of cardinality at
least `κ` carrying an infinite parameter-definable set of cardinality `< κ`. -/
def LargeTwoCardinalModels (L : FirstOrder.Language.{0, 0}) : Prop :=
  ∀ T : L.Theory, L.card ≤ ℵ₀ → T.IsComplete → IsOmegaStable.{0, 0, 0} T → HasVaughtianPair T →
    ∀ κ : Cardinal.{0}, ℵ₀ < κ →
      ∃ μ lam : Cardinal.{0}, κ ≤ μ ∧ ℵ₀ ≤ lam ∧ lam < κ ∧ HasTwoCardinalModel T μ lam

/-- **The cardinality bookkeeping of two-cardinal transfer.**  Once two-cardinal models of
*arbitrarily large* size are available, downward Löwenheim–Skolem pins the big side to the
prescribed cardinal `κ` without moving the small side. -/
theorem omegaStableTwoCardinal_of_largeTwoCardinalModels
    (h : LargeTwoCardinalModels L) : OmegaStableTwoCardinal L := by
  intro T hL hT hst hVP κ hκ
  obtain ⟨μ, lam, hκμ, hlam, hlt, hmodel⟩ := h T hL hT hst hVP κ hκ
  exact ⟨lam, hlam, hlt, hasTwoCardinalModel_of_le hL hlam hlt.le hκμ hmodel⟩

/-! ## The case `κ ≤ ℵ₁` -/

/-- **Two-cardinal transfer at `ℵ₁`**, and below: Vaught's two-cardinal theorem already gives the
conclusion of `Submission.Morley.OmegaStableTwoCardinal` for every `κ` with `ℵ₀ < κ ≤ ℵ₁`
(so, in fact, for `κ = ℵ₁`), with no use of `ω`-stability. -/
theorem exists_hasTwoCardinalModel_of_le_aleph1 (hL : L.card ≤ ℵ₀) {T : L.Theory}
    (hT : T.IsComplete) (hVP : HasVaughtianPair T) {κ : Cardinal.{0}} (hκ : ℵ₀ < κ)
    (hκ' : κ ≤ ℵ₁) :
    ∃ lam : Cardinal.{0}, ℵ₀ ≤ lam ∧ lam < κ ∧ HasTwoCardinalModel T κ lam :=
  ⟨ℵ₀, le_rfl, hκ,
    hasTwoCardinalModel_of_le hL le_rfl hκ.le hκ' (vaughtTwoCardinal L T hL hT hVP)⟩

end Submission.Morley
