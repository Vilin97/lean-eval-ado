import Mathlib
import Submission.Morley.Rank

/-!
# Minimal sets, algebraic closure, exchange, and dimension

This file is the **Baldwin–Lachlan chapter** of the formalisation of Morley's categoricity
theorem.  It develops, inside a fixed model `M` of an ω-stable theory in a countable language:

1. minimal (equivalently, strongly minimal) definable sets and their existence,
2. the algebraic closure operator `Alg`,
3. the **exchange principle** — the crux of the chapter — making `Alg` a pregeometry on a minimal
   set,
4. bases and the **dimension** of a minimal set, which in a theory without Vaughtian pairs is the
   cardinality of the model,
5. the **generic type** of a minimal set, and the fact that it is realised over every small
   parameter set.

Everything happens in a fixed countable language `L : FirstOrder.Language.{0, 0}` with all
structures in `Type 0`, matching the conventions of `Submission/Morley/Rank.lean`.

## Why this route

`Submission/Morley/Assembly.lean` reduces Morley's theorem to `SaturationPrinciple L`: an ω-stable
theory without Vaughtian pairs has all its uncountable models saturated.  `Rank.lean` proves this
when the Morley rank of the model is at most one.  For higher rank a purely rank-theoretic
argument is impossible: the definably-full form `Assembly.DefinablyFullSaturation` of the
principle is **false** (the theory of an equivalence relation with infinitely many infinite
classes is ω-stable, and its model with `ℵ₀` classes each of size `ℵ₁` is definably full and
uncountable but omits the type "in no class meeting `A`" for a countable `A` meeting every class).
So the absence of Vaughtian pairs has to be used in its *strong* form — no proper elementary
submodel contains an infinite definable set — which is exactly what
`Submission.Morley.eq_univ_of_maximal_indep_subset` does below.

## Main definitions

* `Submission.Morley.IsMinimalSet L D`: `D ⊆ M` is infinite, and every subset of `M` definable
  with parameters from `M` meets `D` in a finite or a cofinite (in `D`) set.  By
  `Submission.Morley.mrank_le_one_of_isMinimalSet` this is exactly "Morley rank one and Morley
  degree one" in the sense of `Submission/Morley/Rank.lean`.
* `Submission.Morley.Alg L C`: the algebraic closure of `C ⊆ M`, the elements lying in a finite
  `C`-definable subset of `M`.
* `Submission.Morley.Indep L C B`: `B` is independent over `C`, i.e. no `b ∈ B` is algebraic over
  `C` together with `B \ {b}`.
* `Submission.Morley.fewLeft`, `Submission.Morley.fewRight`: the sets of points whose fibre under
  a definable binary relation admits no injective `(n+1)`-tuple.  These replace the counting
  quantifiers `∃^{≤n}` of the informal proof, and are definable by
  `Submission.Morley.definable₁_fewLeft` and `Submission.Morley.definable₁_fewRight`.

## Main results

* `Submission.Morley.exists_definable_subst`: a substitution principle for definable sets, of
  which the two directions used throughout are
  `Submission.Morley.definable₁_fiber_left`/`Submission.Morley.definable₁_fiber_right` (a fibre of
  a `C`-definable binary relation is definable over `C` together with the base point) and
  `Submission.Morley.exists_definable_of_definable₁_insert` (**pulling a parameter out**: a set
  definable over `insert b C` is a fibre of a relation definable over `C`).
* `Submission.Morley.exists_isMinimalSet`: **a minimal set exists** in every model of an ω-stable
  theory.  Choose a definable set of least Morley rank among the infinite ones, and among those
  one of least Morley degree; `Submission.Morley.DegGE.append` shows a further split would exceed
  that degree.
* `Submission.Morley.alg_subset_of_elementarySubstructure`: `Alg L C ⊆ N` for every elementary
  substructure `N` containing `C`; the proof is an induction on the size of a finite definable
  set, using `Submission.Morley.exists_mem_of_definable₁_nonempty`.
* `Submission.Morley.exchange`: **the exchange principle**.
* `Submission.Morley.exists_maximal_indep` and `Submission.Morley.subset_alg_of_maximal_indep`:
  a maximal independent subset of a minimal set exists and spans it.
* `Submission.Morley.eq_univ_of_maximal_indep_subset`: **a model without Vaughtian pairs is
  minimal over a minimal set together with a basis of it**.  This is where `¬HasVaughtianPair`
  enters in its strong form.
* `Submission.Morley.mk_maximal_indep_eq`: **the dimension of a minimal set is the cardinality of
  the model**, and `Submission.Morley.exists_minimalSet_basis` packages the whole construction.
* `Submission.Morley.typeOfElem_eq_of_notMem_alg`: **uniqueness of the generic type**;
  `Submission.Morley.mk_alg_le`: the algebraic closure of a small set is small; and
  `Submission.Morley.exists_isMinimalSet_generic_realized`: the generic type of the minimal set
  is realised over every parameter set of cardinality `< #M`.

## What is *not* proved

`Submission.Morley.SaturationPrinciple` in general.  What is missing, on top of this chapter, is
exactly the two remaining Baldwin–Lachlan ingredients:

1. **Prime models over arbitrary parameter sets.**  `Submission/Morley/Prime.lean` proves
   `isPrime_of_isAtomic` only for *countable* models — and necessarily so, since an uncountable
   dense linear order is atomic over `∅` but does not embed into `ℚ`.  Over an uncountable set the
   right notion is *constructibility*, whose theory (a transfinite construction sequence, and the
   proof that a constructible model is prime) is not developed anywhere in this project.
2. **Indiscernibility of bases**: two independent `n`-tuples from a minimal set realise the same
   type over the parameters.  The `n = 1` case is `typeOfElem_eq_of_notMem_alg` above; the
   inductive step needs the `n`-variable analogue of `fewRight`.

With those two, the classical argument closes: given `A` with `#A < #M`, take `M₁ ≼ M` containing
`A` with `#M₁ < #M` and `q ∈ S₁(M₁)`; realise `q` in some `N ≽ M₁` of size `#M₁ + ℵ₀`;
`eq_univ_of_maximal_indep_subset` applied inside `N` makes `N` minimal, hence (by 1) prime, over
`M₁` together with a basis `B_N` of the minimal set of `N`; by (2) any injection of `B_N` into a
basis `B` of the minimal set of `M` is elementary over `M₁`; primality extends it to an
elementary embedding `N → M` over `M₁`, which carries a realisation of `q` into `M`.
-/

open Cardinal Set FirstOrder Language Theory

namespace Submission.Morley

/-! ## A toolkit for definable sets -/

section Toolkit

variable {L : FirstOrder.Language.{0, 0}} {M : Type} [L.Structure M]

/-- **Substitution in definable sets.**  Let `s` be definable over `A`, and let `p` describe, for
each parameter of `A`, either a parameter of `B` or one of a new block `β` of variables, and `q`
likewise for the variables `α` of `s`.  Then the substituted set is definable over `B`, on the
locus where the substitution respects the parameters. -/
theorem exists_definable_subst {A B : Set M} {α β : Type} {s : Set (α → M)}
    (h : A.Definable L s) (p : A → B ⊕ β) (q : α → B ⊕ β) :
    ∃ t : Set (β → M), B.Definable L t ∧
      ∀ u : β → M, (∀ a : A, Sum.elim (fun c : B => (c : M)) u (p a) = (a : M)) →
        (u ∈ t ↔ (fun i => Sum.elim (fun c : B => (c : M)) u (q i)) ∈ s) := by
  rw [Set.definable_iff_exists_formula_sum] at h
  obtain ⟨φ, rfl⟩ := h
  refine ⟨{u : β → M | (φ.relabel (Sum.elim p q)).Realize (Sum.elim (fun c : B => (c : M)) u)},
    Set.definable_iff_exists_formula_sum.2 ⟨φ.relabel (Sum.elim p q), rfl⟩, fun u hu => ?_⟩
  have hcomp : (Sum.elim (fun c : B => (c : M)) u) ∘ (Sum.elim p q)
      = Sum.elim (fun a : A => (a : M))
        (fun i => Sum.elim (fun c : B => (c : M)) u (q i)) := by
    funext x
    rcases x with a | i
    · simpa using hu a
    · rfl
  rw [Set.mem_setOf_eq, Formula.realize_relabel, hcomp]
  exact Iff.rfl

/-- Membership of a coordinate in a definable subset of `M` is a definable condition. -/
theorem definable_apply_mem {A : Set M} {α : Type} {S : Set M} (hS : A.Definable₁ L S) (i : α) :
    A.Definable L {v : α → M | v i ∈ S} := by
  have h := hS.preimage_comp (fun _ : Fin 1 => i)
  have heq : (fun g : α → M => g ∘ (fun _ : Fin 1 => i)) ⁻¹' {x : Fin 1 → M | x 0 ∈ S}
      = {v : α → M | v i ∈ S} := by
    ext v; simp
  rwa [heq] at h

/-- Composition with a tuple of coordinates preserves definability. -/
theorem comp_pair_eq {α : Type} (v : α → M) (i j : α) : (v ∘ ![i, j]) = ![v i, v j] := by
  funext k; fin_cases k <;> simp

/-- A definable binary relation applied to two coordinates is a definable condition. -/
theorem definable_comp_pair {A : Set M} {α : Type} {R : Set (Fin 2 → M)} (hR : A.Definable L R)
    (i j : α) : A.Definable L {v : α → M | ![v i, v j] ∈ R} := by
  have h := hR.preimage_comp (![i, j] : Fin 2 → α)
  have heq : (fun g : α → M => g ∘ (![i, j] : Fin 2 → α)) ⁻¹' R
      = {v : α → M | ![v i, v j] ∈ R} := by
    ext v; simp only [Set.mem_preimage, Set.mem_setOf_eq, comp_pair_eq]
  rwa [heq] at h

/-- Equality of two coordinates is a definable condition. -/
theorem definable_apply_eq {A : Set M} {α : Type} (i j : α) :
    A.Definable L {v : α → M | v i = v j} := by
  have h0 := Set.Definable.diagonal (L := L) A
  rw [Set.Definable₂] at h0
  have hd : A.Definable L {x : Fin 2 → M | x 0 = x 1} := by
    have heq : {x : Fin 2 → M | (x 0, x 1) ∈ Set.diagonal M} = {x : Fin 2 → M | x 0 = x 1} := by
      ext x; simp [Set.mem_diagonal_iff]
    rwa [heq] at h0
  have h := hd.preimage_comp (![i, j] : Fin 2 → α)
  have heq : (fun g : α → M => g ∘ (![i, j] : Fin 2 → α)) ⁻¹' {x : Fin 2 → M | x 0 = x 1}
      = {v : α → M | v i = v j} := by
    ext v; simp only [Set.mem_preimage, Set.mem_setOf_eq, comp_pair_eq]; simp
  rwa [heq] at h

/-- The transpose of a definable binary relation is definable. -/
theorem definable_swap {A : Set M} {R : Set (Fin 2 → M)} (hR : A.Definable L R) :
    A.Definable L {v : Fin 2 → M | ![v 1, v 0] ∈ R} :=
  definable_comp_pair hR 1 0

/-! ### Fibres of definable binary relations -/

/-- The left fibre of a definable binary relation is definable over the parameters together with
the point at which the fibre is taken. -/
theorem definable₁_fiber_left {C : Set M} {R : Set (Fin 2 → M)} (hR : C.Definable L R) (b : M) :
    (insert b C).Definable₁ L {x : M | ![x, b] ∈ R} := by
  obtain ⟨t, ht, hmem⟩ := exists_definable_subst hR
    (fun c : C => Sum.inl ⟨(c : M), Set.mem_insert_of_mem b c.2⟩)
    (![Sum.inr 0, Sum.inl ⟨b, Set.mem_insert b C⟩] : Fin 2 → (insert b C : Set M) ⊕ Fin 1)
  have hset : t = {u : Fin 1 → M | u 0 ∈ {x : M | ![x, b] ∈ R}} := by
    ext u
    rw [hmem u (fun _ => rfl)]
    have : (fun i : Fin 2 => Sum.elim (fun c : (insert b C : Set M) => (c : M)) u
        ((![Sum.inr 0, Sum.inl ⟨b, Set.mem_insert b C⟩] :
          Fin 2 → (insert b C : Set M) ⊕ Fin 1) i)) = ![u 0, b] := by
      funext k; fin_cases k <;> simp
    rw [this]
    exact Iff.rfl
  rw [Set.Definable₁, ← hset]
  exact ht

/-- The right fibre of a definable binary relation is definable over the parameters together with
the point at which the fibre is taken. -/
theorem definable₁_fiber_right {C : Set M} {R : Set (Fin 2 → M)} (hR : C.Definable L R) (a : M) :
    (insert a C).Definable₁ L {y : M | ![a, y] ∈ R} := by
  have h := definable₁_fiber_left (definable_swap hR) a
  have : {x : M | ![x, a] ∈ {v : Fin 2 → M | ![v 1, v 0] ∈ R}} = {y : M | ![a, y] ∈ R} := by
    ext x; simp
  rwa [this] at h

/-- **Pulling a parameter out of a definable set.**  A set definable over `insert b C` is a fibre
of a binary relation definable over `C`. -/
theorem exists_definable_of_definable₁_insert {C : Set M} {b : M} {S : Set M}
    (h : (insert b C).Definable₁ L S) :
    ∃ R : Set (Fin 2 → M), C.Definable L R ∧ ∀ x : M, (x ∈ S ↔ ![x, b] ∈ R) := by
  classical
  obtain ⟨t, ht, hmem⟩ := exists_definable_subst (α := Fin 1) (β := Fin 2) h
    (fun a : (insert b C : Set M) =>
      if hc : (a : M) ∈ C then Sum.inl ⟨(a : M), hc⟩ else Sum.inr 1)
    (fun _ : Fin 1 => Sum.inr 0)
  refine ⟨t, ht, fun x => ?_⟩
  have hcond : ∀ a : (insert b C : Set M), Sum.elim (fun c : C => (c : M)) ![x, b]
      ((fun a : (insert b C : Set M) =>
        if hc : (a : M) ∈ C then Sum.inl (⟨(a : M), hc⟩ : C) else Sum.inr 1) a) = (a : M) := by
    intro a
    by_cases hc : (a : M) ∈ C
    · simp [hc]
    · have hab : (a : M) = b := by
        rcases a.2 with h' | h'
        · exact h'
        · exact absurd h' hc
      have hbC : b ∉ C := hab ▸ hc
      simp [hbC, hab]
  have hx := hmem ![x, b] hcond
  simpa using hx.symm

/-! ### Counting -/

/-- `fewLeft R n` is the set of points `y` whose left fibre `{x | (x, y) ∈ R}` contains no
injective `(n+1)`-tuple, i.e. has at most `n` elements. -/
def fewLeft (R : Set (Fin 2 → M)) (n : ℕ) : Set M :=
  {y : M | ¬ ∃ v : Fin (n + 1) → M, Function.Injective v ∧ ∀ i, ![v i, y] ∈ R}

/-- `fewRight R n` is the set of points `x` whose right fibre `{y | (x, y) ∈ R}` contains no
injective `(n+1)`-tuple, i.e. has at most `n` elements. -/
def fewRight (R : Set (Fin 2 → M)) (n : ℕ) : Set M :=
  {x : M | ¬ ∃ v : Fin (n + 1) → M, Function.Injective v ∧ ∀ i, ![x, v i] ∈ R}

theorem definable₁_fewLeft {A : Set M} {R : Set (Fin 2 → M)} (hR : A.Definable L R) (n : ℕ) :
    A.Definable₁ L (fewLeft R n) := by
  classical
  set ι : Type := Fin 1 ⊕ Fin (n + 1) with hι
  have h1 : ∀ ij : {p : Fin (n + 1) × Fin (n + 1) // p.1 ≠ p.2},
      A.Definable L {u : ι → M | u (Sum.inr ij.1.1) ≠ u (Sum.inr ij.1.2)} := fun ij =>
    (definable_apply_eq (L := L) (A := A) (Sum.inr ij.1.1 : ι) (Sum.inr ij.1.2)).compl
  have h2 : ∀ i : Fin (n + 1),
      A.Definable L {u : ι → M | ![u (Sum.inr i), u (Sum.inl 0)] ∈ R} := fun i =>
    definable_comp_pair hR (Sum.inr i : ι) (Sum.inl 0)
  have hW : A.Definable L
      ((⋂ ij : {p : Fin (n + 1) × Fin (n + 1) // p.1 ≠ p.2},
          {u : ι → M | u (Sum.inr ij.1.1) ≠ u (Sum.inr ij.1.2)}) ∩
        ⋂ i : Fin (n + 1), {u : ι → M | ![u (Sum.inr i), u (Sum.inl 0)] ∈ R}) :=
    (Set.definable_iInter_of_finite h1).inter (Set.definable_iInter_of_finite h2)
  have hex := hW.exists_of_finite (α := Fin 1) (β := Fin (n + 1))
  rw [Set.Definable₁]
  have hset : {x : Fin 1 → M | x 0 ∈ fewLeft R n} =
      {v : Fin 1 → M | ∃ u : Fin (n + 1) → M, Sum.elim v u ∈
        ((⋂ ij : {p : Fin (n + 1) × Fin (n + 1) // p.1 ≠ p.2},
            {u : ι → M | u (Sum.inr ij.1.1) ≠ u (Sum.inr ij.1.2)}) ∩
          ⋂ i : Fin (n + 1), {u : ι → M | ![u (Sum.inr i), u (Sum.inl 0)] ∈ R})}ᶜ := by
    ext v
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, fewLeft, Set.mem_inter_iff, Set.mem_iInter]
    constructor
    · rintro hno ⟨u, hu1, hu2⟩
      exact hno ⟨u, fun i j hij => by
        by_contra hne
        exact (hu1 ⟨(i, j), hne⟩) hij, fun i => hu2 i⟩
    · rintro hno ⟨u, hu1, hu2⟩
      exact hno ⟨u, fun ij => fun hc => ij.2 (hu1 hc), fun i => hu2 i⟩
  rw [hset]
  exact hex.compl

theorem definable₁_fewRight {A : Set M} {R : Set (Fin 2 → M)} (hR : A.Definable L R) (n : ℕ) :
    A.Definable₁ L (fewRight R n) := by
  have h := definable₁_fewLeft (definable_swap hR) n
  have : fewLeft {v : Fin 2 → M | ![v 1, v 0] ∈ R} n = fewRight R n := by
    ext x; simp [fewLeft, fewRight]
  rwa [this] at h

/-! ### Small sets -/

/-- A set with no injective `(n+1)`-tuple is finite with at most `n` elements. -/
theorem finite_ncard_le_of_no_injective {s : Set M} {n : ℕ}
    (h : ¬ ∃ v : Fin (n + 1) → M, Function.Injective v ∧ ∀ i, v i ∈ s) :
    s.Finite ∧ s.ncard ≤ n := by
  classical
  have hfin : s.Finite := by
    by_contra hinf
    obtain ⟨t, hts, htc⟩ := (Set.not_finite.1 hinf).exists_subset_card_eq (n + 1)
    refine h ⟨fun i => ((t.equivFin.symm (Fin.cast htc.symm i) : M)), ?_, ?_⟩
    · intro i j hij
      have := t.equivFin.symm.injective (Subtype.ext hij)
      simpa using this
    · exact fun i => hts (t.equivFin.symm _).2
  refine ⟨hfin, ?_⟩
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨t, hts, htc⟩ := Finset.exists_subset_card_eq (n := n + 1)
    (s := hfin.toFinset) (by rwa [← Set.ncard_eq_toFinset_card s hfin])
  refine h ⟨fun i => ((t.equivFin.symm (Fin.cast htc.symm i) : M)), ?_, ?_⟩
  · intro i j hij
    have := t.equivFin.symm.injective (Subtype.ext hij)
    simpa using this
  · intro i
    have := hts (t.equivFin.symm (Fin.cast htc.symm i)).2
    simpa using this

/-- A finite set with at most `n` elements has no injective `(n+1)`-tuple. -/
theorem no_injective_of_ncard_le {s : Set M} {n : ℕ} (hfin : s.Finite) (hcard : s.ncard ≤ n) :
    ¬ ∃ v : Fin (n + 1) → M, Function.Injective v ∧ ∀ i, v i ∈ s := by
  rintro ⟨v, hv, hvs⟩
  have hsub : Set.range v ⊆ s := by
    rintro _ ⟨i, rfl⟩; exact hvs i
  have h1 : (Set.range v).ncard = n + 1 := by
    rw [← Nat.card_coe_set_eq, Nat.card_range_of_injective hv, Nat.card_eq_fintype_card,
      Fintype.card_fin]
  have h2 : (Set.range v).ncard ≤ s.ncard := Set.ncard_le_ncard hsub hfin
  omega

end Toolkit

/-! ## Minimal definable sets -/

section MinimalSet

variable {L : FirstOrder.Language.{0, 0}} {M : Type} [L.Structure M]

/-- A subset `D` of a structure `M` is a **minimal set** when it is infinite and every subset of
`M` definable with parameters from `M` meets `D` in a finite or cofinite (in `D`) set.

Together with `Submission.Morley.definable₁_realSet` this says exactly that `D` is defined by a
formula of Morley rank one and Morley degree one, which is
`Submission.Morley.isMinimalSet_iff_forall_finite_or_finite`.  In an ω-stable theory such a set
always exists (`Submission.Morley.exists_isMinimalSet`), and on it algebraic closure satisfies
the exchange principle (`Submission.Morley.exchange`). -/
def IsMinimalSet (L : FirstOrder.Language.{0, 0}) {M : Type} [L.Structure M] (D : Set M) : Prop :=
  D.Infinite ∧ ∀ X : Set M, (Set.univ : Set M).Definable₁ L X → (D ∩ X).Finite ∨ (D \ X).Finite

theorem IsMinimalSet.infinite {D : Set M} (h : IsMinimalSet L D) : D.Infinite := h.1

/-- A definable subset of a minimal set which is infinite is cofinite in it. -/
theorem IsMinimalSet.finite_sdiff {D X : Set M} (h : IsMinimalSet L D)
    (hX : (Set.univ : Set M).Definable₁ L X) (hinf : (D ∩ X).Infinite) : (D \ X).Finite :=
  (h.2 X hX).resolve_left hinf.not_finite

end MinimalSet

/-! ### Minimal sets have Morley rank one -/

section RankOne

variable {L : FirstOrder.Language.{0, 0}} {M : Type} [L.Structure M] [Nonempty M]

/-- **A minimal set has Morley rank one.**  It is infinite, hence of rank at least one
(`Submission.Morley.rankGE_one_iff_infinite`), and it cannot be split into two infinite definable
pieces, hence is not of rank two.

Together with `Submission.Morley.exists_isMinimalSet` this identifies `IsMinimalSet` with the
classical "Morley rank one and Morley degree one". -/
theorem mrank_le_one_of_isMinimalSet {D : Set M} (hD : IsMinimalSet L D)
    (φ : Form1 L (Set.univ : Set M)) (hφ : realSet Set.univ φ = D) :
    MRank (paramTheory L (Set.univ : Set M)) φ ≤ 1 := by
  refine csInf_le' (a := (1 : Ordinal.{0})) ?_
  intro hr
  obtain ⟨ψ, hsub, hdisj, hrank⟩ := rankGE_succ_iff.1 hr
  have hinf : ∀ i, (realSet Set.univ (ψ i)).Infinite := fun i =>
    (rankGE_one_iff_infinite (ψ i)).1 (hrank i)
  have hsub' : ∀ i, realSet Set.univ (ψ i) ⊆ D := fun i => by
    rw [← hφ]
    exact (typesWith_subset_iff_realSet _ _).1 (hsub i)
  have hdisj' : Disjoint (realSet Set.univ (ψ 0)) (realSet Set.univ (ψ 1)) :=
    (typesWith_disjoint_iff_realSet _ _).1 (hdisj 0 1 (by decide))
  have hcof : (D \ realSet Set.univ (ψ 0)).Finite :=
    hD.finite_sdiff (definable₁_realSet _ _)
      (by rw [Set.inter_eq_self_of_subset_right (hsub' 0)]; exact hinf 0)
  exact (hinf 1).not_finite
    (hcof.subset fun x hx => ⟨hsub' 1 hx, Set.disjoint_right.1 hdisj' hx⟩)

/-- If the whole model is a minimal set — that is, if every parameter-definable subset is finite
or cofinite — then the formula `x = x` has Morley rank one, so
`Submission.Morley.categorical_of_mrank_top_le_one` applies. -/
theorem mrank_top_le_one_of_isMinimalSet_univ (h : IsMinimalSet L (Set.univ : Set M)) :
    MRank (paramTheory L (Set.univ : Set M)) (⊤ : Form1 L (Set.univ : Set M)) ≤ 1 :=
  mrank_le_one_of_isMinimalSet h ⊤ realSet_top

end RankOne

/-! ## Existence of a minimal set in an ω-stable theory -/

section Existence

variable {L : FirstOrder.Language.{0, 0}} {T : L.Theory}

/-- Two families of pairwise contradictory formulas of rank at least `o` inside two contradictory
parts of `φ` combine into one family, so Morley degrees add along a binary split. -/
theorem DegGE.append {K : FirstOrder.Language.{0, 0}} {V : Type} {S : K.Theory} {o : Ordinal.{0}}
    {φ ψ χ : K[[V]].Sentence} {m n : ℕ}
    (hψ : S.typesWith ψ ⊆ S.typesWith φ) (hχ : S.typesWith χ ⊆ S.typesWith φ)
    (hd : Disjoint (S.typesWith ψ) (S.typesWith χ))
    (h1 : DegGE S o ψ m) (h2 : DegGE S o χ n) : DegGE S o φ (m + n) := by
  obtain ⟨a, ha1, ha2, ha3⟩ := h1
  obtain ⟨b, hb1, hb2, hb3⟩ := h2
  refine ⟨Fin.append a b, ?_, ?_, ?_⟩
  · intro k
    induction k using Fin.addCases with
    | left i => rw [Fin.append_left]; exact (ha1 i).trans hψ
    | right i => rw [Fin.append_right]; exact (hb1 i).trans hχ
  · have hmixed : ∀ (i : Fin m) (j : Fin n),
        Disjoint (S.typesWith (a i)) (S.typesWith (b j)) := fun i j =>
      Set.disjoint_of_subset (ha1 i) (hb1 j) hd
    intro k l hkl
    induction k using Fin.addCases with
    | left i =>
      induction l using Fin.addCases with
      | left j =>
        rw [Fin.append_left, Fin.append_left]
        exact ha2 i j fun h => hkl (congrArg _ h)
      | right j => rw [Fin.append_left, Fin.append_right]; exact hmixed i j
    | right i =>
      induction l using Fin.addCases with
      | left j => rw [Fin.append_right, Fin.append_left]; exact (hmixed j i).symm
      | right j =>
        rw [Fin.append_right, Fin.append_right]
        exact hb2 i j fun h => hkl (congrArg _ h)
  · intro k
    induction k using Fin.addCases with
    | left i => rw [Fin.append_left]; exact ha3 i
    | right i => rw [Fin.append_right]; exact hb3 i

/-- **Existence of a minimal set.**  In a model of an ω-stable theory there is a minimal
parameter-definable subset: choose a definable set whose Morley rank is least among the infinite
ones, and among those one of least Morley degree.  A binary split of such a set into two infinite
halves would produce two halves of the same rank and of degree at least the chosen one, hence a
splitting of the chosen set into more pieces of full rank than its degree allows. -/
theorem exists_isMinimalSet (hos : OmegaStable.{0, 0, 0} T) (M : T.ModelType.{0, 0, 0})
    (hMinf : Infinite (M : Type)) :
    ∃ D : Set M, IsMinimalSet L D ∧ (Set.univ : Set M).Definable₁ L D := by
  classical
  haveI := hMinf
  haveI : Nonempty (M : Type) := inferInstance
  set K : (L[[(Set.univ : Set M)]]).Theory := paramTheory L (Set.univ : Set M) with hK
  have hb : ∀ φ : Form1 L (Set.univ : Set M), ∃ o : Ordinal.{0}, ¬ RankGE K o φ :=
    fun φ => exists_not_rankGE_of_omegaStable hos M Set.univ φ
  set P : Set Ordinal.{0} :=
    {o | ∃ φ : Form1 L (Set.univ : Set M), (realSet Set.univ φ).Infinite ∧ MRank K φ = o} with hP
  have hPne : P.Nonempty :=
    ⟨MRank K (⊤ : Form1 L (Set.univ : Set M)),
      ⟨⊤, by rw [realSet_top]; exact Set.infinite_univ, rfl⟩⟩
  obtain ⟨φ₀, hφ₀inf, hφ₀rank⟩ := csInf_mem hPne
  set α : Ordinal.{0} := sInf P with hα
  have hαle : ∀ φ : Form1 L (Set.univ : Set M), (realSet Set.univ φ).Infinite →
      α ≤ MRank K φ := fun φ hφ => csInf_le' ⟨φ, hφ, rfl⟩
  set Q : Set ℕ := {d | ∃ φ : Form1 L (Set.univ : Set M), (realSet Set.univ φ).Infinite ∧
      MRank K φ = α ∧ MDegree K φ = d} with hQ
  have hQne : Q.Nonempty := ⟨MDegree K φ₀, φ₀, hφ₀inf, hφ₀rank, rfl⟩
  obtain ⟨φ₁, h1inf, h1rank, h1deg⟩ := Nat.sInf_mem hQne
  set d : ℕ := sInf Q with hd
  have hdle : ∀ φ : Form1 L (Set.univ : Set M), (realSet Set.univ φ).Infinite →
      MRank K φ = α → d ≤ MDegree K φ := fun φ h1 h2 => Nat.sInf_le ⟨φ, h1, h2, rfl⟩
  refine ⟨realSet Set.univ φ₁, ⟨h1inf, fun X hX => ?_⟩, definable₁_realSet _ _⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨hXinf, hXcoinf⟩ := hcon
  obtain ⟨ψ, hψ⟩ := exists_realSet_eq_of_definable₁ (Set.univ : Set M) hX
  -- the two halves of the split
  have hleft : realSet Set.univ (φ₁ ⊓ ψ) = realSet Set.univ φ₁ ∩ X := by
    rw [realSet_inf, hψ]
  have hright : realSet Set.univ (φ₁ ⊓ ∼ψ) = realSet Set.univ φ₁ \ X := by
    rw [realSet_inf, realSet_not, hψ, ← Set.sdiff_eq]
  have hlinf : (realSet Set.univ (φ₁ ⊓ ψ)).Infinite := by rw [hleft]; exact hXinf
  have hrinf : (realSet Set.univ (φ₁ ⊓ ∼ψ)).Infinite := by rw [hright]; exact hXcoinf
  have hlne : (K.typesWith (φ₁ ⊓ ψ)).Nonempty :=
    (nonempty_typesWith_iff_realSet _).2 hlinf.nonempty
  have hrne : (K.typesWith (φ₁ ⊓ ∼ψ)).Nonempty :=
    (nonempty_typesWith_iff_realSet _).2 hrinf.nonempty
  have hlsub : K.typesWith (φ₁ ⊓ ψ) ⊆ K.typesWith φ₁ :=
    (typesWith_subset_iff_realSet _ _).2 (by rw [hleft]; exact Set.inter_subset_left)
  have hrsub : K.typesWith (φ₁ ⊓ ∼ψ) ⊆ K.typesWith φ₁ :=
    (typesWith_subset_iff_realSet _ _).2 (by rw [hright]; exact Set.sdiff_subset)
  have hdisj : Disjoint (K.typesWith (φ₁ ⊓ ψ)) (K.typesWith (φ₁ ⊓ ∼ψ)) :=
    (typesWith_disjoint_iff_realSet _ _).2 (by
      rw [hleft, hright]
      exact Set.disjoint_sdiff_right.mono_left Set.inter_subset_right)
  -- both halves have the minimal rank
  have hlrank : MRank K (φ₁ ⊓ ψ) = α :=
    le_antisymm (h1rank ▸ mrank_mono hlne hlsub (hb φ₁)) (hαle _ hlinf)
  have hrrank : MRank K (φ₁ ⊓ ∼ψ) = α :=
    le_antisymm (h1rank ▸ mrank_mono hrne hrsub (hb φ₁)) (hαle _ hrinf)
  -- the left half splits into `d` pieces of full rank, the right one into one more
  have hldeg : DegGE K α (φ₁ ⊓ ψ) d :=
    (hlrank ▸ degGE_mdegree (T := K) (φ := φ₁ ⊓ ψ)).mono (hdle _ hlinf hlrank)
  have hrdeg : DegGE K α (φ₁ ⊓ ∼ψ) 1 := degGE_one (hrrank ▸ rankGE_mrank hrne)
  have hfinal : DegGE K α φ₁ (d + 1) :=
    DegGE.append hlsub hrsub hdisj hldeg hrdeg
  have hne1 : (K.typesWith φ₁).Nonempty := (nonempty_typesWith_iff_realSet _).2 h1inf.nonempty
  exact not_degGE_mdegree_succ hne1 (hb φ₁) (by rw [h1rank, h1deg]; exact hfinal)

end Existence

/-! ## Algebraic closure -/

section Alg

variable {L : FirstOrder.Language.{0, 0}} {M : Type} [L.Structure M]

/-- The **algebraic closure** of a parameter set `C ⊆ M`: the elements of `M` lying in some finite
subset of `M` definable with parameters from `C`. -/
def Alg (L : FirstOrder.Language.{0, 0}) {M : Type} [L.Structure M] (C : Set M) : Set M :=
  {a : M | ∃ S : Set M, C.Definable₁ L S ∧ S.Finite ∧ a ∈ S}

theorem mem_alg_iff {C : Set M} {a : M} :
    a ∈ Alg L C ↔ ∃ S : Set M, C.Definable₁ L S ∧ S.Finite ∧ a ∈ S := Iff.rfl

/-- A parameter is algebraic over itself. -/
theorem subset_alg (C : Set M) : C ⊆ Alg L C := fun _ ha =>
  ⟨_, Set.Definable.singleton_of_mem L ha, Set.finite_singleton _, rfl⟩

theorem alg_mono {C C' : Set M} (h : C ⊆ C') : Alg L C ⊆ Alg L C' := by
  rintro a ⟨S, hS, hfin, ha⟩
  exact ⟨S, hS.mono h, hfin, ha⟩

/-- **Algebraic closure has finite character**: only finitely many parameters are needed. -/
theorem exists_finset_of_mem_alg {C : Set M} {a : M} (h : a ∈ Alg L C) :
    ∃ C₀ : Finset M, (C₀ : Set M) ⊆ C ∧ a ∈ Alg L (C₀ : Set M) := by
  obtain ⟨S, hS, hfin, ha⟩ := h
  rw [Set.Definable₁, Set.definable_iff_finitely_definable] at hS
  obtain ⟨C₀, hC₀, hdef⟩ := hS
  exact ⟨C₀, hC₀, S, hdef, hfin, ha⟩

/-! ### Algebraic closure inside an elementary substructure -/

/-- A nonempty set definable with parameters from an elementary substructure meets it. -/
theorem exists_mem_of_definable₁_nonempty {N : L.ElementarySubstructure M} {C : Set M}
    (hC : C ⊆ (N : Set M)) {S : Set M} (hS : C.Definable₁ L S) (hne : S.Nonempty) :
    ∃ a ∈ S, a ∈ (N : Set M) := by
  rw [Set.Definable₁, Set.definable_iff_exists_formula_sum] at hS
  obtain ⟨φ, hφ⟩ := hS
  set x : C → N := fun c => ⟨(c : M), hC c.2⟩ with hx
  obtain ⟨a, ha⟩ := hne
  have hreal : (φ.iExs (Fin 1)).Realize (fun c : C => (c : M)) := by
    rw [Formula.realize_iExs]
    refine ⟨fun _ => a, ?_⟩
    have hmem : (fun _ : Fin 1 => a) ∈ {v : Fin 1 → M | v 0 ∈ S} := ha
    rw [hφ] at hmem
    exact hmem
  have h2 : (φ.iExs (Fin 1)).Realize x :=
    (N.subtype.map_formula (φ.iExs (Fin 1)) x).1 hreal
  rw [Formula.realize_iExs] at h2
  obtain ⟨u, hu⟩ := h2
  have h3 : φ.Realize (fun c => ((Sum.elim x u c : N) : M)) :=
    (N.subtype.map_formula φ (Sum.elim x u)).2 hu
  have h4 : (fun c => ((Sum.elim x u c : N) : M))
      = Sum.elim (fun c : C => (c : M)) (fun i => ((u i : N) : M)) := by
    funext c; rcases c with c | i <;> rfl
  rw [h4] at h3
  have h5 : (fun i => ((u i : N) : M)) ∈ {v : Fin 1 → M | v 0 ∈ S} := by rw [hφ]; exact h3
  exact ⟨((u 0 : N) : M), h5, (u 0).2⟩

theorem definable₁_sdiff {A S S' : Set M} (hS : A.Definable₁ L S) (hS' : A.Definable₁ L S') :
    A.Definable₁ L (S \ S') := by
  rw [Set.Definable₁] at hS hS' ⊢
  have heq : {x : Fin 1 → M | x 0 ∈ S \ S'}
      = {x : Fin 1 → M | x 0 ∈ S} \ {x : Fin 1 → M | x 0 ∈ S'} := by
    ext x; simp
  rw [heq]
  exact hS.sdiff hS'

theorem definable₁_inter {A S S' : Set M} (hS : A.Definable₁ L S) (hS' : A.Definable₁ L S') :
    A.Definable₁ L (S ∩ S') := by
  rw [Set.Definable₁] at hS hS' ⊢
  have heq : {x : Fin 1 → M | x 0 ∈ S ∩ S'}
      = {x : Fin 1 → M | x 0 ∈ S} ∩ {x : Fin 1 → M | x 0 ∈ S'} := by
    ext x; simp
  rw [heq]
  exact hS.inter hS'

/-- **The algebraic closure of a subset of an elementary substructure stays inside it.**

A finite set definable over the substructure meets it, and removing the point found leaves a
smaller finite set definable over the substructure; the induction is on the number of elements. -/
theorem alg_subset_of_elementarySubstructure {N : L.ElementarySubstructure M} {C : Set M}
    (hC : C ⊆ (N : Set M)) : Alg L C ⊆ (N : Set M) := by
  have key : ∀ n : ℕ, ∀ C' : Set M, C' ⊆ (N : Set M) → ∀ S : Set M, C'.Definable₁ L S →
      S.Finite → S.ncard ≤ n → S ⊆ (N : Set M) := by
    intro n
    induction n with
    | zero =>
      intro C' _ S _ hfin hcard
      rw [Nat.le_zero, Set.ncard_eq_zero hfin] at hcard
      rw [hcard]
      exact Set.empty_subset _
    | succ n IH =>
      intro C' hC' S hS hfin hcard
      rcases Set.eq_empty_or_nonempty S with rfl | hne
      · exact Set.empty_subset _
      obtain ⟨a, haS, haN⟩ := exists_mem_of_definable₁_nonempty hC' hS hne
      have hins : insert a C' ⊆ (N : Set M) := Set.insert_subset haN hC'
      have hsub : (S \ {a}) ⊆ (N : Set M) := by
        refine IH (insert a C') hins (S \ {a})
          (definable₁_sdiff (hS.mono (Set.subset_insert a C'))
            (Set.Definable.singleton_of_mem L (Set.mem_insert a C')))
          (hfin.sdiff) ?_
        have := Set.ncard_sdiff_singleton_of_mem (s := S) haS
        have hpos : 0 < S.ncard := (Set.ncard_pos hfin).2 hne
        omega
      intro y hy
      by_cases hya : y = a
      · rw [hya]; exact haN
      · exact hsub ⟨hy, hya⟩
  rintro a ⟨S, hS, hfin, ha⟩
  exact key S.ncard C hC S hS hfin le_rfl ha

end Alg

/-! ## The exchange principle -/

section Exchange

variable {L : FirstOrder.Language.{0, 0}} {M : Type} [L.Structure M]

/-- **The exchange principle.**  On a minimal set `D` definable over `C`, algebraic closure
satisfies exchange: if `a ∈ acl(C ∪ {b}) \ acl(C)` with `a, b ∈ D`, then `b ∈ acl(C ∪ {a})`.

The proof is the classical double count.  A binary relation `R` over `C`, contained in `D × D`,
with `R(a, b)` and with `R(·, b)` of size `n`, is cut down to `Θ`, the part of `R` all of whose
left fibres have at most `n` elements; `Θ(a, b)` still holds.  If `b ∉ acl(C ∪ {a})` then the
right fibre `Θ(a, ·)` is infinite, so cofinite in `D`, missing say `k` points; the set `S` of
`x ∈ D` whose right fibre misses at most `k` points of `D` is definable over `C` and contains
`a`, so is infinite by `a ∉ acl(C)`.  Taking `k + 1` points of `D` and `n(k+1) + 1` points of `S`,
every chosen `x` is `Θ`-related to one of the `k + 1` points, while every point has at most `n`
elements of `S` above it — a contradiction. -/
theorem exchange {D : Set M} (hD : IsMinimalSet L D) {C : Set M} (hDC : C.Definable₁ L D)
    {a b : M} (ha : a ∈ D) (hb : b ∈ D)
    (halg : a ∈ Alg L (insert b C)) (hnalg : a ∉ Alg L C) : b ∈ Alg L (insert a C) := by
  classical
  obtain ⟨S, hSdef, hSfin, hSa⟩ := halg
  obtain ⟨R₀, hR₀, hR₀mem⟩ := exists_definable_of_definable₁_insert hSdef
  -- cut `R₀` down to `D × D`
  set R : Set (Fin 2 → M) :=
    (R₀ ∩ {v : Fin 2 → M | v 0 ∈ D}) ∩ {v : Fin 2 → M | v 1 ∈ D} with hRdef
  have hRdef' : C.Definable L R :=
    (hR₀.inter (definable_apply_mem hDC (0 : Fin 2))).inter (definable_apply_mem hDC (1 : Fin 2))
  have hmemR : ∀ v : Fin 2 → M, v ∈ R ↔ (v ∈ R₀ ∧ v 0 ∈ D ∧ v 1 ∈ D) := by
    intro v
    simp only [hRdef, Set.mem_inter_iff, Set.mem_setOf_eq, and_assoc]
  have hfibb : {x : M | ![x, b] ∈ R} = S ∩ D := by
    ext x
    rw [Set.mem_setOf_eq, hmemR]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Set.mem_inter_iff, ← hR₀mem x]
    exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, hb⟩⟩
  set n : ℕ := (S ∩ D).ncard with hn
  have hfibbfin : (S ∩ D).Finite := hSfin.inter_of_left D
  have hbfew : b ∈ fewLeft R n :=
    no_injective_of_ncard_le (s := {x : M | ![x, b] ∈ R}) (by rw [hfibb]; exact hfibbfin)
      (by rw [hfibb])
  -- the part of `R` with uniformly small left fibres
  set Θ : Set (Fin 2 → M) := R ∩ {v : Fin 2 → M | v 1 ∈ fewLeft R n} with hΘdef
  have hΘdef' : C.Definable L Θ :=
    hRdef'.inter (definable_apply_mem (definable₁_fewLeft hRdef' n) (1 : Fin 2))
  have hΘab : ![a, b] ∈ Θ := by
    refine ⟨(hmemR _).2 ⟨(hR₀mem a).1 hSa, ?_, ?_⟩, ?_⟩
    · simpa using ha
    · simpa using hb
    · simpa using hbfew
  have hfibΘ : ∀ y : M,
      ({x : M | ![x, y] ∈ Θ}).Finite ∧ ({x : M | ![x, y] ∈ Θ}).ncard ≤ n := by
    intro y
    rcases Set.eq_empty_or_nonempty {x : M | ![x, y] ∈ Θ} with he | ⟨x₀, hx₀⟩
    · rw [he]; exact ⟨Set.finite_empty, by simp⟩
    · have hy : y ∈ fewLeft R n := by
        have h2 := hx₀.2
        simpa using h2
      obtain ⟨hf, hc⟩ := finite_ncard_le_of_no_injective (s := {x : M | ![x, y] ∈ R}) hy
      have hsub : {x : M | ![x, y] ∈ Θ} ⊆ {x : M | ![x, y] ∈ R} := fun x hx => hx.1
      exact ⟨hf.subset hsub, le_trans (Set.ncard_le_ncard hsub hf) hc⟩
  -- the right fibre of `Θ` over `a`
  set Θa : Set M := {y : M | ![a, y] ∈ Θ} with hΘa
  have hΘadef : (insert a C).Definable₁ L Θa := definable₁_fiber_right hΘdef' a
  by_cases hfinΘa : Θa.Finite
  · exact ⟨Θa, hΘadef, hfinΘa, hΘab⟩
  rw [Set.not_finite] at hfinΘa
  have hΘaD : Θa ⊆ D := by
    intro y hy
    have h2 := ((hmemR _).1 hy.1).2.2
    simpa using h2
  have hcof : (D \ Θa).Finite :=
    hD.finite_sdiff (hΘadef.mono (Set.subset_univ _))
      (by rw [Set.inter_eq_self_of_subset_right hΘaD]; exact hfinΘa)
  set k : ℕ := (D \ Θa).ncard with hk
  -- the points of `D` whose right fibre misses at most `k` points of `D`
  set Θ' : Set (Fin 2 → M) := {v : Fin 2 → M | v 1 ∈ D} \ Θ with hΘ'
  have hΘ'def : C.Definable L Θ' := (definable_apply_mem hDC (1 : Fin 2)).sdiff hΘdef'
  have hfib' : ∀ x : M, {y : M | ![x, y] ∈ Θ'} = D \ {y : M | ![x, y] ∈ Θ} := by
    intro x
    ext y
    simp [hΘ']
  set S' : Set M := D ∩ fewRight Θ' k with hS'
  have hS'def : C.Definable₁ L S' := definable₁_inter hDC (definable₁_fewRight hΘ'def k)
  have haS' : a ∈ S' := by
    refine ⟨ha, ?_⟩
    have h1 : {y : M | ![a, y] ∈ Θ'} = D \ Θa := by rw [hfib' a]
    exact no_injective_of_ncard_le (s := {y : M | ![a, y] ∈ Θ'}) (by rw [h1]; exact hcof)
      (by rw [h1])
  by_cases hfinS' : S'.Finite
  · exact absurd ⟨S', hS'def, hfinS', haS'⟩ hnalg
  rw [Set.not_finite] at hfinS'
  -- the double count
  obtain ⟨D₀, hD₀sub, hD₀card⟩ := hD.infinite.exists_subset_card_eq (k + 1)
  obtain ⟨S₀, hS₀sub, hS₀card⟩ := hfinS'.exists_subset_card_eq (n * (k + 1) + 1)
  have hchoice : ∀ x : M, ∃ y : M, x ∈ S₀ → (y ∈ D₀ ∧ ![x, y] ∈ Θ) := by
    intro x
    by_cases hx : x ∈ S₀
    · have hxfew : x ∈ fewRight Θ' k := (hS₀sub hx).2
      obtain ⟨hfn, hc⟩ := finite_ncard_le_of_no_injective (s := {y : M | ![x, y] ∈ Θ'}) hxfew
      rw [hfib' x] at hfn hc
      have hex : ∃ y ∈ D₀, ![x, y] ∈ Θ := by
        by_contra hcon
        push Not at hcon
        have hsub : (D₀ : Set M) ⊆ D \ {y : M | ![x, y] ∈ Θ} :=
          fun y hy => ⟨hD₀sub hy, hcon y (Finset.mem_coe.1 hy)⟩
        have hle := Set.ncard_le_ncard hsub hfn
        rw [Set.ncard_coe_finset, hD₀card] at hle
        omega
      obtain ⟨y, hy1, hy2⟩ := hex
      exact ⟨y, fun _ => ⟨hy1, hy2⟩⟩
    · exact ⟨a, fun h => absurd h hx⟩
  choose f hf using hchoice
  have hmaps : ∀ x ∈ S₀, f x ∈ D₀ := fun x hx => (hf x hx).1
  have hfibcard : ∀ y ∈ D₀, (S₀.filter fun x => f x = y).card ≤ n := by
    intro y _
    have hsub : ((S₀.filter fun x => f x = y : Finset M) : Set M) ⊆ {x : M | ![x, y] ∈ Θ} := by
      intro x hx
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hx
      have := (hf x hx.1).2
      rw [hx.2] at this
      exact this
    have := Set.ncard_le_ncard hsub (hfibΘ y).1
    rw [Set.ncard_coe_finset] at this
    exact le_trans this (hfibΘ y).2
  have hcount := Finset.card_le_mul_card_image_of_maps_to hmaps n hfibcard
  rw [hS₀card, hD₀card] at hcount
  omega

end Exchange

/-! ## Independence and bases -/

section Basis

variable {L : FirstOrder.Language.{0, 0}} {M : Type} [L.Structure M]

/-- A subset `B` of `M` is **independent over** `C` when no element of `B` is algebraic over `C`
together with the remaining elements of `B`. -/
def Indep (L : FirstOrder.Language.{0, 0}) {M : Type} [L.Structure M] (C B : Set M) : Prop :=
  ∀ b ∈ B, b ∉ Alg L (C ∪ (B \ {b}))

theorem indep_empty (C : Set M) : Indep L C (∅ : Set M) := by
  intro b hb
  exact absurd hb (Set.notMem_empty b)

theorem Indep.mono {C B B' : Set M} (h : Indep L C B) (hB : B' ⊆ B) : Indep L C B' := by
  intro b hb hmem
  exact h b (hB hb) (alg_mono (Set.union_subset_union_right _
    (Set.sdiff_subset_sdiff_left hB)) hmem)

/-- A finite subset of the union of a nonempty chain of sets is contained in one member. -/
theorem exists_mem_of_finset_subset_sUnion {α : Type} {𝒞 : Set (Set α)}
    (h𝒞 : IsChain (· ⊆ ·) 𝒞) (hne : 𝒞.Nonempty) {F : Finset α} (hF : (F : Set α) ⊆ ⋃₀ 𝒞) :
    ∃ B ∈ 𝒞, (F : Set α) ⊆ B := by
  classical
  induction F using Finset.induction with
  | empty =>
    obtain ⟨B, hB⟩ := hne
    exact ⟨B, hB, by simp⟩
  | @insert a F _ IH =>
    have hFsub : (F : Set α) ⊆ ⋃₀ 𝒞 := by
      refine subset_trans ?_ hF
      simp only [Finset.coe_insert]
      exact Set.subset_insert a _
    obtain ⟨B, hB, hFB⟩ := IH hFsub
    have haU : a ∈ ⋃₀ 𝒞 := hF (by simp)
    obtain ⟨B', hB', haB'⟩ := haU
    rcases eq_or_ne B B' with rfl | hne'
    · exact ⟨B, hB, by simp only [Finset.coe_insert]; exact Set.insert_subset haB' hFB⟩
    rcases h𝒞 hB hB' hne' with hle | hle
    · exact ⟨B', hB', by
        simp only [Finset.coe_insert]
        exact Set.insert_subset haB' (hFB.trans hle)⟩
    · exact ⟨B, hB, by
        simp only [Finset.coe_insert]
        exact Set.insert_subset (hle haB') hFB⟩

/-- **A maximal independent subset of a definable set exists.** -/
theorem exists_maximal_indep (L : FirstOrder.Language.{0, 0}) {M : Type} [L.Structure M]
    (C D : Set M) :
    ∃ B : Set M, B ⊆ D ∧ Indep L C B ∧
      ∀ B' : Set M, B' ⊆ D → Indep L C B' → B ⊆ B' → B' = B := by
  classical
  obtain ⟨B, -, hmax⟩ := zorn_subset_nonempty {B : Set M | B ⊆ D ∧ Indep L C B}
    (fun 𝒞 h𝒞S h𝒞 hne => by
      refine ⟨⋃₀ 𝒞, ⟨?_, ?_⟩, fun s hs => Set.subset_sUnion_of_mem hs⟩
      · rintro x ⟨B, hB, hxB⟩
        exact (h𝒞S hB).1 hxB
      · intro b hb hmem
        obtain ⟨F, hFsub, hFalg⟩ := exists_finset_of_mem_alg hmem
        obtain ⟨B₀, hB₀, hbB₀⟩ := hb
        set F' : Finset M := F.filter (fun x => x ∈ ⋃₀ 𝒞 ∧ x ≠ b) with hF'
        have hF'sub : (F' : Set M) ⊆ ⋃₀ 𝒞 := by
          intro x hx
          simp only [hF', Finset.coe_filter, Set.mem_setOf_eq] at hx
          exact hx.2.1
        obtain ⟨B₁, hB₁, hFB₁⟩ := exists_mem_of_finset_subset_sUnion h𝒞 hne hF'sub
        rcases h𝒞.total hB₀ hB₁ with hle | hle
        · refine (h𝒞S hB₁).2 b (hle hbB₀) (alg_mono ?_ hFalg)
          intro x hx
          rcases hFsub hx with hxC | hxU
          · exact Set.mem_union_left _ hxC
          · refine Set.mem_union_right _ ⟨hFB₁ ?_, hxU.2⟩
            simp only [hF', Finset.coe_filter, Set.mem_setOf_eq]
            exact ⟨hx, hxU.1, hxU.2⟩
        · refine (h𝒞S hB₀).2 b hbB₀ (alg_mono ?_ hFalg)
          intro x hx
          rcases hFsub hx with hxC | hxU
          · exact Set.mem_union_left _ hxC
          · refine Set.mem_union_right _ ⟨hle (hFB₁ ?_), hxU.2⟩
            simp only [hF', Finset.coe_filter, Set.mem_setOf_eq]
            exact ⟨hx, hxU.1, hxU.2⟩)
    ∅ ⟨Set.empty_subset D, indep_empty C⟩
  exact ⟨B, hmax.1.1, hmax.1.2, fun B' hB'D hB' hBB' =>
    Set.Subset.antisymm (hmax.2 ⟨hB'D, hB'⟩ hBB') hBB'⟩

/-- **A maximal independent subset spans**: every element of a minimal set is algebraic over the
parameters together with a maximal independent subset.

This is the point at which the exchange principle is used: adding a non-algebraic element to a
maximal independent set keeps it independent. -/
theorem subset_alg_of_maximal_indep {D : Set M} (hD : IsMinimalSet L D) {C : Set M}
    (hDC : C.Definable₁ L D) {B : Set M} (hBD : B ⊆ D) (hB : Indep L C B)
    (hmax : ∀ B' : Set M, B' ⊆ D → Indep L C B' → B ⊆ B' → B' = B) : D ⊆ Alg L (C ∪ B) := by
  intro c hc
  by_contra hcalg
  have hcB : c ∉ B := fun h => hcalg (subset_alg _ (Set.mem_union_right _ h))
  have hins : Indep L C (insert c B) := by
    intro x hx hxalg
    rcases hx with rfl | hxB
    · refine hcalg (alg_mono ?_ hxalg)
      have : (insert x B) \ {x} = B := by
        rw [Set.insert_sdiff_of_mem _ (Set.mem_singleton x), Set.sdiff_singleton_eq_self hcB]
      rw [this]
    · -- `x ∈ B`; use exchange to move `c` into the algebraic closure of `C ∪ B`
      have hxc : x ≠ c := fun h => hcB (h ▸ hxB)
      have hset : (insert c B) \ {x} = insert c (B \ {x}) := by
        rw [Set.insert_sdiff_of_notMem _ (by simpa using Ne.symm hxc)]
      rw [hset, Set.union_insert] at hxalg
      have hxnot : x ∉ Alg L (C ∪ (B \ {x})) := hB x hxB
      have hxD : x ∈ D := hBD hxB
      have hcalg' := exchange hD (hDC.mono Set.subset_union_left) hxD hc hxalg hxnot
      refine hcalg (alg_mono ?_ hcalg')
      intro y hy
      rcases hy with rfl | hy
      · exact Set.mem_union_right _ hxB
      · rcases hy with hy | hy
        · exact Set.mem_union_left _ hy
        · exact Set.mem_union_right _ hy.1
  have := hmax (insert c B) (Set.insert_subset hc hBD) hins (Set.subset_insert c B)
  exact hcB (this ▸ Set.mem_insert c B)

end Basis

/-! ## Dimension -/

section Dimension

variable {L : FirstOrder.Language.{0, 0}} {T : L.Theory}

/-- **A model without Vaughtian pairs is minimal over a minimal set together with a basis.**

If `N ≼ M` contains the parameters `C` of a minimal set `D` and a maximal `C`-independent subset
`B` of `D`, then `D ⊆ acl(C ∪ B) ⊆ N`; as `D` is infinite and definable over `N`, the absence of
Vaughtian pairs forces `N = M`.

This is the point at which `¬HasVaughtianPair` is used in its strong form — not merely through
definable fullness. -/
theorem eq_univ_of_maximal_indep_subset (hvp : ¬HasVaughtianPair T) (M : T.ModelType.{0, 0, 0})
    {D : Set M} (hD : IsMinimalSet L D) {C : Set M} (hDC : C.Definable₁ L D) {B : Set M}
    (hBD : B ⊆ D) (hB : Indep L C B)
    (hmax : ∀ B' : Set M, B' ⊆ D → Indep L C B' → B ⊆ B' → B' = B)
    (N : L.ElementarySubstructure M) (hCN : C ⊆ (N : Set M)) (hBN : B ⊆ (N : Set M)) :
    (N : Set M) = Set.univ :=
  eq_univ_of_not_hasVaughtianPair hvp M N D (hDC.mono hCN) hD.infinite
    ((subset_alg_of_maximal_indep hD hDC hBD hB hmax).trans
      (alg_subset_of_elementarySubstructure (Set.union_subset hCN hBN)))

/-- **A model without Vaughtian pairs is spanned by a minimal set together with its parameters**:
its cardinality is at most that of `C ∪ B`, up to `ℵ₀`.

The elementary substructure of size `#(C ∪ B) + ℵ₀` produced by downward Löwenheim–Skolem
contains `C ∪ B`, hence is all of `M`. -/
theorem mk_le_of_maximal_indep (hL : L.card ≤ ℵ₀) (hvp : ¬HasVaughtianPair T)
    (M : T.ModelType.{0, 0, 0}) {D : Set M} (hD : IsMinimalSet L D) {C : Set M}
    (hDC : C.Definable₁ L D) {B : Set M} (hBD : B ⊆ D) (hB : Indep L C B)
    (hmax : ∀ B' : Set M, B' ⊆ D → Indep L C B' → B ⊆ B' → B' = B) :
    #(M : Type) ≤ #(C ∪ B : Set M) + ℵ₀ := by
  by_contra hcon
  rw [not_le] at hcon
  set κ : Cardinal.{0} := #(C ∪ B : Set M) + ℵ₀ with hκ
  obtain ⟨N, hNsub, hNcard⟩ :=
    exists_elementarySubstructure_card_eq L (C ∪ B : Set M) κ le_add_self
      (by simp only [Cardinal.lift_id]; exact le_add_right le_rfl)
      (by simpa using hL.trans le_add_self)
      (by simp only [Cardinal.lift_id]; exact hcon.le)
  simp only [Cardinal.lift_id] at hNcard
  have hCN : C ⊆ (N : Set M) := Set.subset_union_left.trans hNsub
  have hBN : B ⊆ (N : Set M) := Set.subset_union_right.trans hNsub
  have huniv := eq_univ_of_maximal_indep_subset hvp M hD hDC hBD hB hmax N hCN hBN
  have hMN : #(M : Type) ≤ #(N : Type) :=
    Cardinal.mk_le_of_injective (f := fun x : M => (⟨x, by rw [← SetLike.mem_coe, huniv]; trivial⟩ : N))
      (fun x y hxy => by simpa using hxy)
  rw [hNcard] at hMN
  exact absurd hMN (not_le.2 hcon)

/-- **The dimension of a minimal set is the cardinality of the model.**

In a model of uncountable cardinality of a theory without Vaughtian pairs, a maximal independent
subset of a minimal set defined over a small parameter set is as large as the model itself. -/
theorem mk_maximal_indep_eq (hL : L.card ≤ ℵ₀) (hvp : ¬HasVaughtianPair T)
    (M : T.ModelType.{0, 0, 0}) (hM : ℵ₀ < #(M : Type)) {D : Set M} (hD : IsMinimalSet L D)
    {C : Set M} (hDC : C.Definable₁ L D) (hC : #C < #(M : Type)) {B : Set M} (hBD : B ⊆ D)
    (hB : Indep L C B) (hmax : ∀ B' : Set M, B' ⊆ D → Indep L C B' → B ⊆ B' → B' = B) :
    #B = #(M : Type) := by
  refine le_antisymm (Cardinal.mk_set_le B) ?_
  by_contra hcon
  rw [not_le] at hcon
  have h1 := mk_le_of_maximal_indep hL hvp M hD hDC hBD hB hmax
  have h2 : #(C ∪ B : Set M) + ℵ₀ < #(M : Type) := by
    refine Cardinal.add_lt_of_lt hM.le ?_ hM
    exact lt_of_le_of_lt (Cardinal.mk_union_le C B) (Cardinal.add_lt_of_lt hM.le hC hcon)
  exact absurd h1 (not_le.2 h2)

/-- **Existence of a minimal set with a basis of full dimension.**

For an ω-stable theory in a countable language without Vaughtian pairs, every model of
uncountable cardinality contains a minimal set `D`, defined over a finite parameter set `C`, with
a maximal `C`-independent subset `B ⊆ D` which spans `D` (in the sense that `D ⊆ acl(C ∪ B)`) and
which has the cardinality of the model.

This is the Baldwin–Lachlan dimension of an uncountably categorical theory. -/
theorem exists_minimalSet_basis (hL : L.card ≤ ℵ₀) (hos : OmegaStable.{0, 0, 0} T)
    (hvp : ¬HasVaughtianPair T) (M : T.ModelType.{0, 0, 0}) (hM : ℵ₀ < #(M : Type)) :
    ∃ (D C B : Set M), C.Finite ∧ IsMinimalSet L D ∧ C.Definable₁ L D ∧ B ⊆ D ∧
      Indep L C B ∧ D ⊆ Alg L (C ∪ B) ∧ #B = #(M : Type) ∧ #D = #(M : Type) := by
  haveI : Infinite (M : Type) := Cardinal.infinite_iff.2 hM.le
  obtain ⟨D, hD, hDdef⟩ := exists_isMinimalSet hos M inferInstance
  rw [Set.Definable₁, Set.definable_iff_finitely_definable] at hDdef
  obtain ⟨C₀, -, hC₀⟩ := hDdef
  have hDC : (C₀ : Set M).Definable₁ L D := hC₀
  obtain ⟨B, hBD, hB, hmax⟩ := exists_maximal_indep L (C₀ : Set M) D
  have hBcard : #B = #(M : Type) := by
    refine mk_maximal_indep_eq hL hvp M hM hD hDC ?_ hBD hB hmax
    exact lt_of_lt_of_le (Cardinal.lt_aleph0_iff_set_finite.2 C₀.finite_toSet) hM.le
  refine ⟨D, (C₀ : Set M), B, C₀.finite_toSet, hD, hDC, hBD, hB,
    subset_alg_of_maximal_indep hD hDC hBD hB hmax, hBcard, ?_⟩
  exact le_antisymm (Cardinal.mk_set_le D)
    (hBcard ▸ Cardinal.mk_le_mk_of_subset hBD)

end Dimension

/-! ## The generic type of a minimal set -/

section Generic

variable {L : FirstOrder.Language.{0, 0}} {M : Type} [L.Structure M]

/-- **The algebraic closure of a set is no bigger than the set.**  Every element of `Alg L A` lies
in one of the at most `#A + ℵ₀` finite subsets of `M` definable over `A`. -/
theorem mk_alg_le [Nonempty M] (hL : L.card ≤ ℵ₀) (A : Set M) :
    #(Alg L A : Set M) ≤ #A + ℵ₀ := by
  classical
  have hcov : (Alg L A) ⊆
      ⋃ φ : {φ : Form1 L A // (realSet A φ).Finite}, realSet A (φ : Form1 L A) := by
    rintro a ⟨S, hS, hfin, ha⟩
    obtain ⟨φ, hφ⟩ := exists_realSet_eq_of_definable₁ A hS
    exact Set.mem_iUnion.2 ⟨⟨φ, by rw [hφ]; exact hfin⟩, by rw [hφ]; exact ha⟩
  refine (Cardinal.mk_le_mk_of_subset hcov).trans ?_
  refine Cardinal.mk_iUnion_le_sum_mk.trans ?_
  refine (Cardinal.sum_le_sum _ (fun _ => ℵ₀) fun φ => ?_).trans ?_
  · exact (Cardinal.lt_aleph0_iff_set_finite.2 φ.2).le
  · rw [Cardinal.sum_const']
    have hform : #{φ : Form1 L A // (realSet A φ).Finite} ≤ #A + ℵ₀ := by
      refine (Cardinal.mk_subtype_le _).trans ?_
      refine (mk_sentence_le A (Fin 1)).trans ?_
      simp only [Cardinal.mk_fin, Nat.cast_one]
      calc #A + L.card + 1 + ℵ₀ ≤ #A + ℵ₀ + ℵ₀ + ℵ₀ := by
            gcongr
            exact Cardinal.one_le_aleph0
        _ = #A + ℵ₀ := by
            rw [add_assoc, add_assoc, Cardinal.aleph0_add_aleph0, Cardinal.aleph0_add_aleph0]
    refine (mul_le_mul' hform le_rfl).trans ?_
    rw [Cardinal.mul_eq_max le_add_self le_rfl]
    exact max_le le_rfl le_add_self

/-- **Uniqueness of the generic type.**  Two elements of a minimal set `D`, neither of them
algebraic over a parameter set `C` over which `D` is defined, realise the same type over `C`:
a `C`-definable set either meets `D` in a finite set — which then avoids both — or contains all
but finitely many points of `D` — and then contains both. -/
theorem typeOfElem_eq_of_notMem_alg [Nonempty M] {D : Set M} (hD : IsMinimalSet L D) {C : Set M}
    (hDC : C.Definable₁ L D) {a b : M} (ha : a ∈ D) (hna : a ∉ Alg L C) (hb : b ∈ D)
    (hnb : b ∉ Alg L C) : (typeOfElem C a : S₁ L C) = typeOfElem C b := by
  have key : ∀ φ : Form1 L C, ∀ x : M, x ∈ D → x ∉ Alg L C →
      (x ∈ realSet C φ ↔ (D \ realSet C φ).Finite) := by
    intro φ x hx hxa
    have hXdef : C.Definable₁ L (realSet C φ) := definable₁_realSet C φ
    rcases hD.2 (realSet C φ) (hXdef.mono (Set.subset_univ C)) with hfin | hcofin
    · constructor
      · intro hmem
        exact absurd ⟨D ∩ realSet C φ, definable₁_inter hDC hXdef, hfin, hx, hmem⟩ hxa
      · intro hcofin
        exact absurd (Set.Finite.union hfin hcofin |>.subset
          (fun y hy => by
            by_cases hy' : y ∈ realSet C φ
            · exact Or.inl ⟨hy, hy'⟩
            · exact Or.inr ⟨hy, hy'⟩)) hD.infinite.not_finite
    · exact ⟨fun _ => hcofin, fun _ => by
        by_contra hmem
        exact hxa ⟨D \ realSet C φ, definable₁_sdiff hDC hXdef, hcofin, hx, hmem⟩⟩
  refine Theory.CompleteType.eq_of_le fun φ hφ => ?_
  have h1 : a ∈ realSet C φ := hφ
  have h2 : (D \ realSet C φ).Finite := (key φ a ha hna).1 h1
  exact (key φ b hb hnb).2 h2

/-- **The generic type is realised.**  In a model of uncountable cardinality of an ω-stable theory
without Vaughtian pairs, a minimal set has an element outside the algebraic closure of any
parameter set of cardinality `< #M`. -/
theorem exists_mem_sdiff_alg {T : L.Theory} (hL : L.card ≤ ℵ₀) (M : T.ModelType.{0, 0, 0})
    (hM : ℵ₀ < #(M : Type)) {D : Set M} (hDM : #D = #(M : Type)) {A : Set M}
    (hA : #A < #(M : Type)) : (D \ Alg L A).Nonempty := by
  haveI : Infinite (M : Type) := Cardinal.infinite_iff.2 hM.le
  rw [Set.nonempty_iff_ne_empty]
  intro hempty
  rw [Set.sdiff_eq_empty] at hempty
  have h1 : #D ≤ #A + ℵ₀ := (Cardinal.mk_le_mk_of_subset hempty).trans (mk_alg_le hL A)
  rw [hDM] at h1
  exact absurd h1 (not_le.2 (Cardinal.add_lt_of_lt hM.le hA hM))

/-- **The saturation principle, restricted to the generic type of a minimal set.**

In a model `M` of uncountable cardinality of an ω-stable theory in a countable language without
Vaughtian pairs there is a minimal set `D`, definable over a finite parameter set `C`, of the
cardinality of `M`, such that for every parameter set `A ⊇ C` of cardinality `< #M` there is an
element of `D` not algebraic over `A`, and all such elements realise one and the same complete
`1`-type over `A` — the generic type of `D` over `A`.

So the generic types are realised in `M`; `Submission.Morley.SaturationPrinciple` asks for *all*
types, which needs a prime model over `C` together with a basis of `D`. -/
theorem exists_isMinimalSet_generic_realized {T : L.Theory} (hL : L.card ≤ ℵ₀)
    (hos : OmegaStable.{0, 0, 0} T) (hvp : ¬HasVaughtianPair T) (M : T.ModelType.{0, 0, 0})
    (hM : ℵ₀ < #(M : Type)) :
    ∃ D C : Set M, C.Finite ∧ IsMinimalSet L D ∧ C.Definable₁ L D ∧ #D = #(M : Type) ∧
      ∀ A : Set M, C ⊆ A → #A < #(M : Type) →
        ∃ a ∈ D, a ∉ Alg L A ∧
          ∀ b ∈ D, b ∉ Alg L A → (typeOfElem A a : S₁ L A) = typeOfElem A b := by
  haveI : Infinite (M : Type) := Cardinal.infinite_iff.2 hM.le
  obtain ⟨D, C, B, hCfin, hD, hDC, -, -, -, -, hDcard⟩ :=
    exists_minimalSet_basis hL hos hvp M hM
  refine ⟨D, C, hCfin, hD, hDC, hDcard, fun A hCA hA => ?_⟩
  obtain ⟨a, haD, hana⟩ := exists_mem_sdiff_alg hL M hM hDcard hA
  exact ⟨a, haD, hana, fun b hbD hbna =>
    typeOfElem_eq_of_notMem_alg hD (hDC.mono hCA) haD hana hbD hbna⟩

end Generic

end Submission.Morley
