import Mathlib
import Submission.Morley.PrimeExists
import Submission.Morley.Saturated

/-!
# Prime and atomic models over an arbitrary parameter set

`Submission/Morley/PrimeExists.lean` builds a prime model over a *countable* parameter set, by a
construction of length `ω` with a Tarski–Vaught bookkeeping; countability is used twice, once to
enumerate the tasks of the bookkeeping and once through
`Submission.Morley.isPrime_of_isAtomic`, which needs `[Countable M]`.  This file removes the
countability hypothesis altogether.

## Main results

* `Submission.Morley.exists_prime_of_isolatedDense'` and
  `Submission.Morley.exists_prime_of_isOmegaStable'`: over **every** subset `A` of a model `M` of
  an `ω`-stable theory there is a prime model — a model `N` of `T`, an elementary embedding
  `f : N ↪ₑ[L] M` and a subset `A'` of `N` carried by `f` onto `A`, with `IsPrime N A'` and
  `IsAtomic N A'`.  These are `Submission.Morley.exists_prime_of_isolatedDense` and
  `Submission.Morley.exists_prime_of_isOmegaStable` with `A.Countable` (and `Countable N`)
  dropped.
* `Submission.Morley.exists_prime_defSet_mk_eq'`: the same statement in the form the successor
  step of two-cardinal transfer consumes it, generalising
  `Submission.Morley.exists_prime_defSet_mk_eq`.
* `Submission.Morley.exists_atomic_elementarySubstructure_of_isolatedDense`: an independent, much
  shorter route to the *atomic* half — a **maximal** subset atomic over `A` is automatically an
  elementary substructure — which suffices whenever only atomicity, not primality, is needed.
* `Submission.Morley.mem_of_isIsolated_of_countable`: step (3) of the two-cardinal transfer
  argument documented in `Submission/Morley/OmegaTwoCardinal.lean` — an extension of `S` by an
  element of isolated type over `S ∪ {c}`, with `c` generic over `S`, realises no new countable
  type over `S`, and in particular adds no element to a definable set that is countable in `S`.

## What is still missing for two-cardinal transfer

Step (4) of `Submission/Morley/OmegaTwoCardinal.lean`, the length-`κ` elementary chain, is *not*
proved.  Running the chain inside a fixed ambient model `𝔐` requires `𝔐` to realise the generic
type over each of its stages, i.e. to be `κ⁺`-saturated; and neither Mathlib nor this development
contains any construction of a saturated elementary extension (see
`Submission.Morley.SaturationPrinciple`, which is likewise left as a hypothesis).  Building one
needs a transfinite elementary chain of *structures*, whereas every transfinite construction
available here — `Submission.Morley.transRec`, the tower of `Submission/Morley/Chains.lean`, and
the two constructions of this file — is a recursion inside a *fixed* structure.

## The two constructions

**Atomicity by maximality.**  `Submission.Morley.AtomicOn L M A C` says every finite tuple from
`C` realises an isolated type over `A`.  This is a condition on finite tuples, so it passes to
unions of chains, and Zorn's lemma gives a *maximal* `C ⊇ A` atomic over `A`
(`Submission.Morley.exists_maximal_atomicOn`).  Maximality *is* the Tarski–Vaught condition: a
nonempty set definable over `C` contains, by density of the isolated types, an element of isolated
type over `C`, and adjoining it keeps the set atomic over `A`
(`Submission.Morley.AtomicOn.insert`), so it was in `C` already
(`Submission.Morley.meetsDefinable_of_maximal_atomicOn`).  No bookkeeping and no ambient saturated
model are needed.

**Primality by constructibility.**  Atomicity does not imply primality over an uncountable
parameter set, so the prime model is instead built *constructibly*: elements of isolated type over
the parameters gathered so far are adjoined one at a time along the well-order
`Submission.Morley.ConstrIdx M`, which is too long to inject into `M`
(`Submission.Morley.constrSet`, `Submission.Morley.exists_stable_stage`).  The process must
therefore stabilise, and stabilisation is again the Tarski–Vaught condition
(`Submission.Morley.exists_stage_meetsDefinable`); every stage is atomic over `A`
(`Submission.Morley.atomicOn_constrSet`).  A partial elementary map from `A` into any model of `T`
is then extended along the *same* well-order, one element at a time
(`Submission.Morley.mapSet_isPartialElem_and_dom`), each step being possible because the newly
adjoined element has isolated type over the current domain, not merely over `A`
(`Submission.Morley.exists_isPartialElem_insert`).  Partial maps are carried as graphs
(`Submission.Morley.IsPartialElem`), which makes the transfinite unions painless.
-/

universe u v w w' w''

open Cardinal Set FirstOrder Language Theory Theory.CompleteType

namespace Submission.Morley

/-! ## Atomic subsets -/

section AtomicOn

variable {L : FirstOrder.Language.{u, v}} {M : Type w} [L.Structure M] [Nonempty M]

/-- A subset `C` of `M` is *atomic over* `A ⊆ M` when every finite tuple of elements of `C`
realises an isolated complete type over `A`.

Unlike `Submission.Morley.IsAtomic`, which speaks about a whole structure, this is a property of a
*subset* of a fixed ambient structure, and the types involved are computed in that ambient
structure.  It is the form in which atomicity is carried through the Zorn argument below. -/
def AtomicOn (L : FirstOrder.Language.{u, v}) (M : Type w) [L.Structure M] [Nonempty M]
    (A C : Set M) : Prop :=
  ∀ (n : ℕ) (x : Fin n → M), (∀ i, x i ∈ C) →
    (((L[[A]]).completeTheory M).typeOf x).IsIsolated

/-- The parameter set is atomic over itself: a tuple of parameters is isolated by the conjunction
of the equations naming its entries. -/
theorem atomicOn_self (A : Set M) : AtomicOn L M A A := fun _ x hx =>
  isIsolated_typeOf_of_mem (L := L) (M := M) (A := A) fun i => ⟨x i, hx i⟩

theorem AtomicOn.mono {A C D : Set M} (h : AtomicOn L M A C) (hDC : D ⊆ C) :
    AtomicOn L M A D := fun n x hx => h n x fun i => hDC (hx i)

end AtomicOn

/-! ## A finite tuple in a union of a chain lies in one member -/

section Chain

/-- A finite tuple of elements of the union of a nonempty chain of sets lies in one member of the
chain. -/
theorem exists_mem_of_forall_mem_sUnion {α : Type*} {c : Set (Set α)}
    (hc : IsChain (· ⊆ ·) c) (hne : c.Nonempty) {n : ℕ} (x : Fin n → α)
    (hx : ∀ i, x i ∈ ⋃₀ c) : ∃ s ∈ c, ∀ i, x i ∈ s := by
  induction n with
  | zero => obtain ⟨s, hs⟩ := hne; exact ⟨s, hs, fun i => i.elim0⟩
  | succ k ih =>
    obtain ⟨s, hs, hxs⟩ := ih (fun i => x i.castSucc) fun i => hx _
    obtain ⟨t, ht, hxt⟩ := hx (Fin.last k)
    rcases hc.total hs ht with h | h
    · refine ⟨t, ht, fun i => ?_⟩
      induction i using Fin.lastCases with
      | last => exact hxt
      | cast j => exact h (hxs j)
    · refine ⟨s, hs, fun i => ?_⟩
      induction i using Fin.lastCases with
      | last => exact h hxt
      | cast j => exact hxs j

end Chain

/-! ## Adding one element of isolated type keeps a set atomic -/

section Insert

variable {L : FirstOrder.Language.{u, v}} {M : Type w} [L.Structure M] [Nonempty M]
variable {A C : Set M}

/-- **The one-step atomicity lemma.**  If `C` is atomic over `A ⊇ ∅` and `b` realises an isolated
type over `C`, then `insert b C` is still atomic over `A`.

A finite tuple from `insert b C` is, after reindexing, a tuple of elements of `C` followed by the
single element `b`; the mixed-tuple lemma `Submission.Morley.isIsolated_typeOf_sum_of_mem` makes
its type over `C` isolated, transitivity of isolation
(`FirstOrder.Language.Theory.CompleteType.isIsolated_typeOf_trans`) brings it down to `A`, and
`Submission.Morley.isIsolated_typeOf_comp` undoes the reindexing. -/
theorem AtomicOn.insert (hAC : A ⊆ C) (hC : AtomicOn L M A C) {b : M}
    (hb : (((L[[C]]).completeTheory M).typeOf fun _ : Fin 1 => b).IsIsolated) :
    AtomicOn L M A (insert b C) := by
  classical
  intro k x hx
  set S : Finset (Fin k) := Finset.univ.filter (fun i => x i ∈ C) with hS
  have hmemS : ∀ i : Fin k, i ∈ S ↔ x i ∈ C := by intro i; simp [hS]
  set d : Fin S.card → ↥C :=
    fun r => ⟨x (S.equivFin.symm r), (hmemS _).1 (S.equivFin.symm r).2⟩ with hd'
  set y : (Fin S.card ⊕ Fin 1) → M :=
    Sum.elim (fun r => ((d r : M))) (fun _ => b) with hy
  set f : Fin k → Fin S.card ⊕ Fin 1 :=
    fun i => if h : x i ∈ C then Sum.inl (S.equivFin ⟨i, (hmemS i).2 h⟩) else Sum.inr 0 with hf
  have hyf : y ∘ f = x := by
    funext i
    by_cases h : x i ∈ C
    · simp only [Function.comp_apply, hf, dif_pos h, hy, Sum.elim_inl, hd',
        Equiv.symm_apply_apply]
    · rcases hx i with h' | h'
      · simp only [Function.comp_apply, hf, dif_neg h, hy, Sum.elim_inr]
        exact h'.symm
      · exact absurd h' h
  have hyC : (((L[[C]]).completeTheory M).typeOf y).IsIsolated :=
    isIsolated_typeOf_sum_of_mem d hb
  have hyA : (((L[[A]]).completeTheory M).typeOf y).IsIsolated := by
    refine CompleteType.isIsolated_typeOf_trans hAC y ?_ hyC
    intro nn bb
    exact hC nn (fun i => ((bb i : M))) fun i => (bb i).2
  rw [← hyf]
  exact isIsolated_typeOf_comp (completeTheory.isComplete (L := L[[A]]) M) y f hyA

end Insert

/-! ## A maximal atomic set is an elementary substructure -/

section Maximal

variable {L : FirstOrder.Language.{u, v}} {M : Type w} [L.Structure M] [Nonempty M]

/-- **A maximal atomic set exists.**  The subsets of `M` that contain `A` and are atomic over `A`
are closed under unions of chains, because a finite tuple from such a union already lies in one
member of the chain; and `A` itself is one of them. -/
theorem exists_maximal_atomicOn (A : Set M) :
    ∃ C : Set M, A ⊆ C ∧ AtomicOn L M A C ∧
      ∀ D : Set M, A ⊆ D → AtomicOn L M A D → C ⊆ D → D ⊆ C := by
  obtain ⟨C, -, hCmem, hCmax⟩ :=
    zorn_subset_nonempty {C : Set M | A ⊆ C ∧ AtomicOn L M A C}
      (by
        rintro c hcS hchain hne
        refine ⟨⋃₀ c, ⟨?_, ?_⟩, fun s hs => Set.subset_sUnion_of_mem hs⟩
        · obtain ⟨s, hs⟩ := hne
          exact (hcS hs).1.trans (Set.subset_sUnion_of_mem hs)
        · intro n x hx
          obtain ⟨s, hs, hxs⟩ := exists_mem_of_forall_mem_sUnion hchain hne x hx
          exact (hcS hs).2 n x hxs)
      A ⟨Set.Subset.rfl, atomicOn_self A⟩
  exact ⟨C, hCmem.1, hCmem.2, fun D hAD hD hCD => hCmax ⟨hAD, hD⟩ hCD⟩

/-- **A maximal atomic set meets every nonempty definable set.**  Given a nonempty set definable
with parameters from a maximal atomic set `C`, density of the isolated types produces an element
of it whose type over `C` is isolated; adjoining that element keeps the set atomic over `A`, so by
maximality the element already belongs to `C`. -/
theorem meetsDefinable_of_maximal_atomicOn (hd : ∀ B : Set M, IsolatedDenseOn L M B)
    {A C : Set M} (hAC : A ⊆ C) (hC : AtomicOn L M A C)
    (hmax : ∀ D : Set M, A ⊆ D → AtomicOn L M A D → C ⊆ D → D ⊆ C) :
    L.MeetsDefinable C := by
  rintro D hDne ⟨φ, hφ⟩
  obtain ⟨x₀, hx₀⟩ := hDne
  have hx₀φ : φ.Realize (fun _ : Fin 1 => x₀) := by
    have hmem : (fun _ : Fin 1 => x₀) ∈ {x : Fin 1 → M | x 0 ∈ D} := hx₀
    rw [hφ] at hmem
    exact hmem
  obtain ⟨b, hb1, hb2⟩ :=
    exists_realize_isIsolated_of_isolatedDense (hd C) φ (fun _ => x₀) hx₀φ
  have hbC : b ∈ C :=
    hmax (insert b C) (hAC.trans (Set.subset_insert b C)) (hC.insert hAC hb2)
      (Set.subset_insert b C) (Set.mem_insert b C)
  refine ⟨b, ?_, hbC⟩
  have hmem : (fun _ : Fin 1 => b) ∈ setOf φ.Realize := hb1
  rw [← hφ] at hmem
  exact hmem

/-- **The atomic elementary substructure over an arbitrary parameter set.**

If the isolated types are dense in every space of complete `1`-types over a subset of `M`, then
every subset `A ⊆ M` is contained in an elementary substructure `S ≼ M` every finite tuple of
which realises an isolated type over `A`.

This is `Submission.Morley.exists_atomic_elementarySubstructure` with the countability hypothesis
on `A` removed.  The proof is different: instead of a construction of length `ω` with a
Tarski–Vaught bookkeeping, it takes a **maximal** subset atomic over `A`, which exists by Zorn's
lemma because atomicity is a condition on finite tuples and therefore passes to unions of chains.
Maximality replaces the bookkeeping: it *is* the Tarski–Vaught condition, by density of the
isolated types. -/
theorem exists_atomic_elementarySubstructure_of_isolatedDense
    (hd : ∀ B : Set M, IsolatedDenseOn L M B) (A : Set M) :
    ∃ S : L.ElementarySubstructure M, A ⊆ (S : Set M) ∧ AtomicOn L M A (S : Set M) := by
  obtain ⟨C, hAC, hC, hmax⟩ := exists_maximal_atomicOn (L := L) A
  have hmeets : L.MeetsDefinable C := meetsDefinable_of_maximal_atomicOn hd hAC hC hmax
  have hcoe : ((hmeets.toElementarySubstructure : L.ElementarySubstructure M) : Set M) = C :=
    hmeets.closure_eq_self
  exact ⟨hmeets.toElementarySubstructure, by rw [hcoe]; exact hAC, by rw [hcoe]; exact hC⟩

end Maximal

/-! ## The transfinite construction -/

section Construction

/-- A well-ordered index type long enough that no injection into `M` exists: the order type of
`2 ^ #M`. -/
abbrev ConstrIdx (M : Type w) : Type w := (((2 : Cardinal.{w}) ^ (#M)).ord).ToType

theorem not_injective_constrIdx {M : Type w} (f : ConstrIdx M → M) :
    ¬ Function.Injective f := by
  intro hf
  have h1 : #(ConstrIdx M) ≤ #M := Cardinal.mk_le_of_injective hf
  rw [Cardinal.mk_ord_toType] at h1
  exact absurd h1 (not_le.2 (Cardinal.cantor _))

variable (L : FirstOrder.Language.{u, v}) {M : Type w} [L.Structure M] [Nonempty M]

open Classical in
/-- Adjoin to `D`, if there is one, an element outside `D` whose type over `D` is isolated. -/
noncomputable def stepOn (D : Set M) : Set M :=
  if h : ∃ b : M, b ∉ D ∧
      (((L[[↥D]]).completeTheory M).typeOf fun _ : Fin 1 => b).IsIsolated then
    insert h.choose D
  else D

theorem stepOn_spec (D : Set M) :
    (stepOn L D = D ∧ ∀ b : M, b ∉ D →
        ¬ (((L[[↥D]]).completeTheory M).typeOf fun _ : Fin 1 => b).IsIsolated) ∨
    ∃ b : M, b ∉ D ∧ (((L[[↥D]]).completeTheory M).typeOf fun _ : Fin 1 => b).IsIsolated ∧
      stepOn L D = insert b D := by
  classical
  unfold stepOn
  by_cases h : ∃ b : M, b ∉ D ∧
      (((L[[↥D]]).completeTheory M).typeOf fun _ : Fin 1 => b).IsIsolated
  · rw [dif_pos h]
    exact Or.inr ⟨h.choose, h.choose_spec.1, h.choose_spec.2, rfl⟩
  · rw [dif_neg h]
    push Not at h
    exact Or.inl ⟨rfl, h⟩

theorem subset_stepOn (D : Set M) : D ⊆ stepOn L D := by
  rcases stepOn_spec L D with ⟨h, -⟩ | ⟨b, -, -, h⟩
  · exact h.ge
  · exact h ▸ Set.subset_insert b D

/-- One step of the construction: the parameters gathered so far, together with a new element of
isolated type over them if there is one. -/
noncomputable def constrStep (A : Set M) (_o : ConstrIdx M) (D : Set M) : Set M :=
  stepOn L (A ∪ D)

/-- The stages of the construction over `A`. -/
noncomputable def constrSet (A : Set M) (o : ConstrIdx M) : Set M :=
  transRec (constrStep L A) o

/-- The parameters available at stage `o` of the construction over `A`. -/
noncomputable def constrBelow (A : Set M) (o : ConstrIdx M) : Set M :=
  A ∪ ⋃ j, ⋃ _ : j < o, constrSet L A j

theorem constrSet_eq (A : Set M) (o : ConstrIdx M) :
    constrSet L A o = stepOn L (constrBelow L A o) :=
  transRec_eq _ _

/-- At each stage the construction either adjoins a new element of isolated type, or has run out
of such elements. -/
theorem constrSet_spec (A : Set M) (o : ConstrIdx M) :
    (constrSet L A o = constrBelow L A o ∧
      ∀ b : M, b ∉ constrBelow L A o →
        ¬ (((L[[↥(constrBelow L A o)]]).completeTheory M).typeOf fun _ : Fin 1 => b).IsIsolated) ∨
    ∃ b : M, b ∉ constrBelow L A o ∧
      (((L[[↥(constrBelow L A o)]]).completeTheory M).typeOf fun _ : Fin 1 => b).IsIsolated ∧
      constrSet L A o = insert b (constrBelow L A o) := by
  rw [constrSet_eq]
  exact stepOn_spec L _

theorem constrBelow_subset_constrSet (A : Set M) (o : ConstrIdx M) :
    constrBelow L A o ⊆ constrSet L A o := by
  rcases constrSet_spec L A o with ⟨h, -⟩ | ⟨b, -, -, h⟩
  · exact h.ge
  · exact h ▸ Set.subset_insert b _

theorem subset_constrBelow (A : Set M) (o : ConstrIdx M) : A ⊆ constrBelow L A o :=
  Set.subset_union_left

theorem subset_constrSet (A : Set M) (o : ConstrIdx M) : A ⊆ constrSet L A o :=
  (subset_constrBelow L A o).trans (constrBelow_subset_constrSet L A o)

theorem constrSet_subset_constrBelow (A : Set M) {j o : ConstrIdx M} (h : j < o) :
    constrSet L A j ⊆ constrBelow L A o := fun _ hx =>
  Set.mem_union_right _ (Set.mem_iUnion.2 ⟨j, Set.mem_iUnion.2 ⟨h, hx⟩⟩)

theorem constrSet_mono (A : Set M) : Monotone (constrSet L A) := by
  intro j o hjo
  rcases eq_or_lt_of_le hjo with rfl | h
  · exact le_rfl
  · exact (constrSet_subset_constrBelow L A h).trans (constrBelow_subset_constrSet L A o)

/-- Every finite tuple from the parameters available at stage `o` already lies in a single earlier
stage, or entirely in `A`. -/
theorem exists_stage_of_forall_mem_constrBelow (A : Set M) (o : ConstrIdx M) {n : ℕ}
    (x : Fin n → M) (hx : ∀ i, x i ∈ constrBelow L A o) :
    (∀ i, x i ∈ A) ∨ ∃ j : ConstrIdx M, j < o ∧ ∀ i, x i ∈ constrSet L A j := by
  classical
  by_cases hA : ∀ i, x i ∈ A
  · exact Or.inl hA
  · refine Or.inr ?_
    push Not at hA
    obtain ⟨i₀, hi₀⟩ := hA
    obtain ⟨j₀, hj₀, hxj₀⟩ : ∃ j : ConstrIdx M, j < o ∧ x i₀ ∈ constrSet L A j := by
      rcases hx i₀ with h | h
      · exact absurd h hi₀
      · obtain ⟨-, ⟨j, rfl⟩, hj⟩ := h
        obtain ⟨-, ⟨hjo, rfl⟩, hj'⟩ := hj
        exact ⟨j, hjo, hj'⟩
    have hpick : ∀ i : Fin n, ∃ j : ConstrIdx M, j < o ∧ x i ∈ constrSet L A j := by
      intro i
      rcases hx i with h | h
      · exact ⟨j₀, hj₀, subset_constrSet L A j₀ h⟩
      · obtain ⟨-, ⟨j, rfl⟩, hj⟩ := h
        obtain ⟨-, ⟨hjo, rfl⟩, hj'⟩ := hj
        exact ⟨j, hjo, hj'⟩
    choose jj hjjo hjjx using hpick
    have hne : (Finset.univ.image jj).Nonempty := ⟨jj i₀, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩
    set J := (Finset.univ.image jj).max' hne with hJ
    have hJlt : J < o := by
      obtain ⟨i, -, hi⟩ := Finset.mem_image.1 ((Finset.univ.image jj).max'_mem hne)
      rw [hJ, ← hi]
      exact hjjo i
    refine ⟨J, hJlt, fun i => ?_⟩
    exact constrSet_mono L A ((Finset.univ.image jj).le_max' _
      (Finset.mem_image_of_mem _ (Finset.mem_univ i))) (hjjx i)

/-- **Every stage of the construction is atomic over `A`.** -/
theorem atomicOn_constrSet (A : Set M) (o : ConstrIdx M) : AtomicOn L M A (constrSet L A o) := by
  induction o using WellFoundedLT.induction with
  | _ o ih =>
    have hbelow : AtomicOn L M A (constrBelow L A o) := by
      intro n x hx
      rcases exists_stage_of_forall_mem_constrBelow L A o x hx with hA | ⟨j, hjo, hxj⟩
      · exact atomicOn_self A n x hA
      · exact ih j hjo n x hxj
    rcases constrSet_spec L A o with ⟨h, -⟩ | ⟨b, -, hb, h⟩
    · rw [h]; exact hbelow
    · rw [h]; exact hbelow.insert (subset_constrBelow L A o) hb

/-- **The construction stabilises.**  If a new element were adjoined at every stage, the map
sending a stage to the element adjoined there would be an injection of the index type into `M`. -/
theorem exists_stable_stage (A : Set M) :
    ∃ o : ConstrIdx M, ∀ b : M, b ∉ constrBelow L A o →
      ¬ (((L[[↥(constrBelow L A o)]]).completeTheory M).typeOf fun _ : Fin 1 => b).IsIsolated := by
  by_contra hcon
  push Not at hcon
  have hstep : ∀ o : ConstrIdx M, ∃ b : M, b ∉ constrBelow L A o ∧
      constrSet L A o = insert b (constrBelow L A o) := by
    intro o
    rcases constrSet_spec L A o with ⟨-, h⟩ | ⟨b, hb1, -, hb3⟩
    · obtain ⟨b, hb, hb'⟩ := hcon o
      exact absurd hb' (h b hb)
    · exact ⟨b, hb1, hb3⟩
  choose e he1 he2 using hstep
  refine not_injective_constrIdx e ?_
  intro j o hjo
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · exact he1 o (hjo ▸ (constrSet_subset_constrBelow L A h)
      (he2 j ▸ Set.mem_insert (e j) _))
  · exact he1 j (hjo ▸ (constrSet_subset_constrBelow L A h)
      (he2 o ▸ Set.mem_insert (e o) _) : e j ∈ constrBelow L A j)

end Construction

/-! ## Substituting constants for parameters -/

section Subst

variable {L : FirstOrder.Language.{u, v}}

/-- Substituting constants from `α` for the second block of variables of a formula in
`Fin 1 ⊕ Fin m` free variables. -/
def substParams {α : Type w} {β : Type w'} {m : ℕ} (θ : L.Formula (β ⊕ Fin m)) (c : Fin m → α) :
    (L[[α]]).Formula β :=
  BoundedFormula.constantsVarsEquiv.symm (θ.relabel (Sum.elim Sum.inr fun i => Sum.inl (c i)))

/-- `substParams` realises, in *any* structure interpreting the constants, exactly as the original
formula does at the interpreted parameters. -/
theorem realize_substParams {α : Type w} {β : Type w'} {m : ℕ} (θ : L.Formula (β ⊕ Fin m))
    (c : Fin m → α) {K : Type w''} [L.Structure K] [(L[[α]]).Structure K]
    [(L.lhomWithConstants α).IsExpansionOn K] (v : β → K) :
    (substParams θ c).Realize v ↔ θ.Realize (Sum.elim v fun i => ((L.con (c i) : K))) := by
  have h := BoundedFormula.realize_constantsVarsEquiv (M := K) (L := L) (α := α)
    (β := β) (n := 0) (φ := substParams θ c) (v := v) (xs := default)
  rw [substParams, Equiv.apply_symm_apply] at h
  refine h.symm.trans ?_
  show Formula.Realize (θ.relabel (Sum.elim Sum.inr fun i => Sum.inl (c i)))
    (Sum.elim (fun a : α => ((L.con a : K))) v) ↔ _
  rw [Formula.realize_relabel,
    show (Sum.elim (fun a : α => ((L.con a : K))) v) ∘ (Sum.elim Sum.inr fun i => Sum.inl (c i)) =
      Sum.elim v fun i => ((L.con (c i) : K)) from by funext x; rcases x with j | i <;> rfl]

end Subst

/-! ## Extending a partial elementary map by one element of isolated type -/

section OneStep

variable {L : FirstOrder.Language.{u, v}} {M : Type w} [L.Structure M]
variable {N : Type w} [L.Structure N]

/-- The graph of a map defined on a subset. -/
def graphOfMap {A : Set M} (g : A → N) : Set (M × N) := Set.range fun a : A => ((a : M), g a)

theorem fst_image_graphOfMap {A : Set M} (g : A → N) : Prod.fst '' (graphOfMap g) = A := by
  ext x
  constructor
  · rintro ⟨-, ⟨a, rfl⟩, rfl⟩
    exact a.2
  · intro hx
    exact ⟨((⟨x, hx⟩ : A), g ⟨x, hx⟩), ⟨⟨x, hx⟩, rfl⟩, rfl⟩

theorem isPartialElem_graphOfMap {A : Set M} {g : A → N} (hg : IsElementaryOn L A g) :
    IsPartialElem L (graphOfMap g) := by
  intro k φ x hx
  choose a ha using hx
  have h1 : (fun i => (x i).1) = Subtype.val ∘ a := by funext i; rw [← ha i]; rfl
  have h2 : (fun i => (x i).2) = g ∘ a := by funext i; rw [← ha i]; rfl
  rw [h1, h2]
  exact hg.realize_fin φ a

/-- A partial elementary map with domain `D` is a partial elementary map in the sense of
`Submission.Morley.IsElementaryOn`. -/
theorem exists_isElementaryOn_of_isPartialElem {G : Set (M × N)} (hG : IsPartialElem L G)
    {D : Set M} (hdom : Prod.fst '' G = D) :
    ∃ h : D → N, (∀ a : D, ((a : M), h a) ∈ G) ∧ IsElementaryOn L D h := by
  classical
  have hex : ∀ a : D, ∃ n : N, ((a : M), n) ∈ G := by
    intro a
    have : (a : M) ∈ Prod.fst '' G := by rw [hdom]; exact a.2
    obtain ⟨p, hp, hp'⟩ := this
    exact ⟨p.2, by rwa [← hp']⟩
  choose h hh using hex
  refine ⟨h, hh, isElementaryOn_of_realize_fin fun k φ x => ?_⟩
  exact hG φ (fun i => ((x i : M), h (x i))) fun i => hh (x i)

variable [Nonempty M] [Nonempty N]

/-- **The one-step extension of a partial elementary map.**  A partial elementary map with domain
`D` extends to `insert b D` whenever the type of `b` over `D` is isolated: the isolating formula
determines a complete type over `D`, which is realised in the target because the target is a model
of the theory of `M` with constants for `D`. -/
theorem exists_isPartialElem_insert {G : Set (M × N)} (hG : IsPartialElem L G) {D : Set M}
    (hdom : Prod.fst '' G = D) {b : M}
    (hb : (((L[[↥D]]).completeTheory M).typeOf fun _ : Fin 1 => b).IsIsolated) :
    ∃ b' : N, IsPartialElem L (insert (b, b') G) := by
  classical
  obtain ⟨h, hmem, hel⟩ := exists_isElementaryOn_of_isPartialElem hG hdom
  letI : (Language.constantsOn ↥D).Structure N := Language.constantsOn.structure h
  haveI := hel.model
  obtain ⟨y, hy⟩ := exists_realize_of_isIsolated hb N
  refine ⟨y 0, ?_⟩
  have hy0 : (fun _ : Fin 1 => y 0) = y := funext fun i => by rw [Subsingleton.elim i 0]
  intro k φ x hx
  -- separate the indices whose value already lies in `G` from those equal to `(b, y 0)`
  set S : Finset (Fin k) := Finset.univ.filter (fun i => x i ∈ G) with hS
  have hmemS : ∀ i : Fin k, i ∈ S ↔ x i ∈ G := by intro i; simp [hS]
  set c : Fin S.card → ↥D := fun r =>
    ⟨(x (S.equivFin.symm r)).1, by
      rw [← hdom]; exact ⟨x (S.equivFin.symm r), (hmemS _).1 (S.equivFin.symm r).2, rfl⟩⟩
    with hc
  have hcsnd : ∀ r, h (c r) = (x (S.equivFin.symm r)).2 := fun r =>
    hG.functional (hmem (c r)) ((hmemS _).1 (S.equivFin.symm r).2)
  set ρ : Fin k → Fin 1 ⊕ Fin S.card :=
    fun i => if hi : x i ∈ G then Sum.inr (S.equivFin ⟨i, (hmemS i).2 hi⟩) else Sum.inl 0 with hρ
  set θ : L.Formula (Fin 1 ⊕ Fin S.card) := φ.relabel ρ with hθ
  have hleft : (Sum.elim (fun _ : Fin 1 => b) fun r => ((c r : M))) ∘ ρ = fun i => (x i).1 := by
    funext i
    by_cases hi : x i ∈ G
    · simp only [Function.comp_apply, hρ, dif_pos hi, Sum.elim_inr, hc, Equiv.symm_apply_apply]
    · rcases hx i with hxi | hxi
      · simp only [Function.comp_apply, hρ, dif_neg hi, Sum.elim_inl]
        rw [hxi]
      · exact absurd hxi hi
  have hright : (Sum.elim (fun _ : Fin 1 => y 0) fun r => h (c r)) ∘ ρ = fun i => (x i).2 := by
    funext i
    by_cases hi : x i ∈ G
    · simp only [Function.comp_apply, hρ, dif_pos hi, Sum.elim_inr]
      rw [hcsnd, Equiv.symm_apply_apply]
    · rcases hx i with hxi | hxi
      · simp only [Function.comp_apply, hρ, dif_neg hi, Sum.elim_inl]
        rw [hxi]
      · exact absurd hxi hi
  have hM : φ.Realize (fun i => (x i).1) ↔
      (substParams θ c).Realize (fun _ : Fin 1 => b) := by
    rw [realize_substParams θ c (K := M), ← hleft, hθ, Formula.realize_relabel]
    rfl
  have hN : φ.Realize (fun i => (x i).2) ↔ (substParams θ c).Realize y := by
    rw [realize_substParams θ c (K := N), ← hy0, ← hright, hθ, Formula.realize_relabel]
    rfl
  rw [hM, hN]
  exact CompleteType.realize_iff_of_typeOf_eq _ _ hy.symm _

end OneStep

/-! ## Extending a partial elementary map along the construction -/

section MapConstruction

variable (L : FirstOrder.Language.{u, v}) {M : Type w} [L.Structure M]
variable {N : Type w} [L.Structure N]

open Classical in
/-- Extend a partial elementary map `H` by one pair so as to cover the set `C`, if possible. -/
noncomputable def extendOn (C : Set M) (H : Set (M × N)) : Set (M × N) :=
  if h : ∃ q : M × N, IsPartialElem L (insert q H) ∧ q.1 ∈ C ∧
      C ⊆ insert q.1 (Prod.fst '' H) then insert h.choose H else H

theorem extendOn_spec (C : Set M) (H : Set (M × N)) :
    (∃ q : M × N, IsPartialElem L (insert q H) ∧ q.1 ∈ C ∧ C ⊆ insert q.1 (Prod.fst '' H) ∧
        extendOn L C H = insert q H) ∨
      (extendOn L C H = H ∧ ¬ ∃ q : M × N, IsPartialElem L (insert q H) ∧ q.1 ∈ C ∧
        C ⊆ insert q.1 (Prod.fst '' H)) := by
  classical
  unfold extendOn
  by_cases h : ∃ q : M × N, IsPartialElem L (insert q H) ∧ q.1 ∈ C ∧
      C ⊆ insert q.1 (Prod.fst '' H)
  · rw [dif_pos h]
    exact Or.inl ⟨h.choose, h.choose_spec.1, h.choose_spec.2.1, h.choose_spec.2.2, rfl⟩
  · rw [dif_neg h]
    exact Or.inr ⟨rfl, h⟩

theorem subset_extendOn (C : Set M) (H : Set (M × N)) : H ⊆ extendOn L C H := by
  rcases extendOn_spec L C H with ⟨q, -, -, -, h⟩ | ⟨h, -⟩
  · exact h ▸ Set.subset_insert q H
  · exact h.ge

variable [Nonempty M]

/-- One step of the extension of a partial elementary map along the construction over `A`. -/
noncomputable def mapStep (A : Set M) (GA : Set (M × N)) (o : ConstrIdx M) (G : Set (M × N)) :
    Set (M × N) := extendOn L (constrSet L A o) (G ∪ GA)

/-- The stages of the extension of a partial elementary map along the construction over `A`. -/
noncomputable def mapSet (A : Set M) (GA : Set (M × N)) (o : ConstrIdx M) : Set (M × N) :=
  transRec (mapStep L A GA) o

/-- The partial map available at stage `o`. -/
noncomputable def mapBelow (A : Set M) (GA : Set (M × N)) (o : ConstrIdx M) : Set (M × N) :=
  (⋃ j, ⋃ _ : j < o, mapSet L A GA j) ∪ GA

theorem mapSet_eq (A : Set M) (GA : Set (M × N)) (o : ConstrIdx M) :
    mapSet L A GA o = extendOn L (constrSet L A o) (mapBelow L A GA o) :=
  transRec_eq _ _

theorem mapBelow_subset_mapSet (A : Set M) (GA : Set (M × N)) (o : ConstrIdx M) :
    mapBelow L A GA o ⊆ mapSet L A GA o := by
  rw [mapSet_eq]; exact subset_extendOn L _ _

theorem graph_subset_mapBelow (A : Set M) (GA : Set (M × N)) (o : ConstrIdx M) :
    GA ⊆ mapBelow L A GA o := Set.subset_union_right

theorem mapSet_subset_mapBelow (A : Set M) (GA : Set (M × N)) {j o : ConstrIdx M} (h : j < o) :
    mapSet L A GA j ⊆ mapBelow L A GA o := fun _ hx =>
  Set.mem_union_left _ (Set.mem_iUnion.2 ⟨j, Set.mem_iUnion.2 ⟨h, hx⟩⟩)

theorem mapSet_mono (A : Set M) (GA : Set (M × N)) : Monotone (mapSet L A GA) := by
  intro j o hjo
  rcases eq_or_lt_of_le hjo with rfl | h
  · exact le_rfl
  · exact (mapSet_subset_mapBelow L A GA h).trans (mapBelow_subset_mapSet L A GA o)

variable [Nonempty N]

/-- **The extension of a partial elementary map along the construction.**  At every stage the
partial map is elementary and its domain is exactly the stage of the construction: at a stage
where a new element of isolated type is adjoined, the one-step extension lemma supplies a value
for it. -/
theorem mapSet_isPartialElem_and_dom {A : Set M} {GA : Set (M × N)} (hGA : IsPartialElem L GA)
    (hdomGA : Prod.fst '' GA = A) (o : ConstrIdx M) :
    IsPartialElem L (mapSet L A GA o) ∧ Prod.fst '' (mapSet L A GA o) = constrSet L A o := by
  classical
  induction o using WellFoundedLT.induction with
  | _ o ih =>
    have hunion : Prod.fst '' (mapBelow L A GA o) = constrBelow L A o := by
      rw [mapBelow, Set.image_union, hdomGA, constrBelow, Set.union_comm A]
      congr 1
      simp only [Set.image_iUnion]
      exact Set.iUnion_congr fun j => Set.iUnion_congr fun hj => (ih j hj).2
    have hbelow : IsPartialElem L (mapBelow L A GA o) := by
      by_cases hex : ∃ j : ConstrIdx M, j < o
      · obtain ⟨j₀, hj₀⟩ := hex
        have hsub : GA ⊆ ⋃ j, ⋃ _ : j < o, mapSet L A GA j := fun p hp =>
          Set.mem_iUnion.2 ⟨j₀, Set.mem_iUnion.2 ⟨hj₀,
            mapBelow_subset_mapSet L A GA j₀ (graph_subset_mapBelow L A GA j₀ hp)⟩⟩
        have heq : mapBelow L A GA o = ⋃ j, ⋃ _ : j < o, mapSet L A GA j := by
          rw [mapBelow, Set.union_eq_self_of_subset_right hsub]
        have hsubtype : (⋃ j, ⋃ _ : j < o, mapSet L A GA j)
            = ⋃ j : {j : ConstrIdx M // j < o}, mapSet L A GA j.1 := by
          rw [Set.iUnion_subtype]
        rw [heq, hsubtype]
        exact isPartialElem_iUnion (fun j j' hjj' => mapSet_mono L A GA hjj')
          (fun j => (ih j.1 j.2).1) (hGA.mono (Set.empty_subset _))
      · push Not at hex
        have : (⋃ j, ⋃ _ : j < o, mapSet L A GA j) = (∅ : Set (M × N)) := by
          apply Set.eq_empty_of_forall_notMem
          intro p hp
          obtain ⟨-, ⟨j, rfl⟩, hj⟩ := hp
          obtain ⟨-, ⟨hjo, rfl⟩, -⟩ := hj
          exact absurd hjo (not_lt.2 (hex j))
        rw [mapBelow, this, Set.empty_union]
        exact hGA
    rcases constrSet_spec L A o with ⟨heq, -⟩ | ⟨b, hb1, hb2, hb3⟩
    · rcases extendOn_spec L (constrSet L A o) (mapBelow L A GA o) with
        ⟨q, hq1, hq2, hq3, hq4⟩ | ⟨hq, -⟩
      · rw [mapSet_eq, hq4]
        refine ⟨hq1, ?_⟩
        rw [Set.image_insert_eq, hunion, ← heq]
        exact Set.insert_eq_self.2 hq2
      · rw [mapSet_eq, hq]
        exact ⟨hbelow, by rw [hunion, heq]⟩
    · have hex : ∃ q : M × N, IsPartialElem L (insert q (mapBelow L A GA o)) ∧
          q.1 ∈ constrSet L A o ∧
          constrSet L A o ⊆ insert q.1 (Prod.fst '' (mapBelow L A GA o)) := by
        obtain ⟨b', hb'⟩ := exists_isPartialElem_insert hbelow hunion hb2
        exact ⟨(b, b'), hb', by rw [hb3]; exact Set.mem_insert b _,
          by rw [hb3, hunion]⟩
      rcases extendOn_spec L (constrSet L A o) (mapBelow L A GA o) with
        ⟨q, hq1, hq2, hq3, hq4⟩ | ⟨-, hq⟩
      · rw [hunion] at hq3
        rw [mapSet_eq, hq4]
        refine ⟨hq1, ?_⟩
        rw [Set.image_insert_eq, hunion]
        exact Set.Subset.antisymm
          (Set.insert_subset hq2 (constrBelow_subset_constrSet L A o)) hq3
      · exact absurd hex hq

end MapConstruction

/-! ## The constructed set is an elementary substructure -/

section Closure

variable (L : FirstOrder.Language.{u, v}) {M : Type w} [L.Structure M] [Nonempty M]

/-- **The construction closes off.**  At a stage where the construction has stabilised, the set of
parameters gathered meets every nonempty definable set with parameters in it — by density of the
isolated types, a definable set missing it would supply a further element to adjoin. -/
theorem exists_stage_meetsDefinable (hd : ∀ B : Set M, IsolatedDenseOn L M B) (A : Set M) :
    ∃ o : ConstrIdx M, L.MeetsDefinable (constrSet L A o) := by
  obtain ⟨o, ho⟩ := exists_stable_stage L A
  have heq : constrSet L A o = constrBelow L A o := by
    rcases constrSet_spec L A o with ⟨h, -⟩ | ⟨b, hb1, hb2, -⟩
    · exact h
    · exact absurd hb2 (ho b hb1)
  refine ⟨o, ?_⟩
  rw [heq]
  rintro D hDne ⟨φ, hφ⟩
  obtain ⟨x₀, hx₀⟩ := hDne
  have hx₀φ : φ.Realize (fun _ : Fin 1 => x₀) := by
    have hmem : (fun _ : Fin 1 => x₀) ∈ {x : Fin 1 → M | x 0 ∈ D} := hx₀
    rw [hφ] at hmem
    exact hmem
  obtain ⟨b, hb1, hb2⟩ :=
    exists_realize_isIsolated_of_isolatedDense (hd (constrBelow L A o)) φ (fun _ => x₀) hx₀φ
  refine ⟨b, ?_, by by_contra hb; exact ho b hb hb2⟩
  have hmem : (fun _ : Fin 1 => b) ∈ setOf φ.Realize := hb1
  rw [← hφ] at hmem
  exact hmem

variable {N : Type w} [L.Structure N]

omit [Nonempty M] in
/-- A partial elementary map whose domain is an elementary substructure is an elementary
embedding of that substructure. -/
theorem exists_elementaryEmbedding_of_isPartialElem {G : Set (M × N)} (hG : IsPartialElem L G)
    {S : L.ElementarySubstructure M} (hdom : Prod.fst '' G = (S : Set M)) :
    ∃ f : (S : Type w) ↪ₑ[L] N, ∀ a : (S : Type w), ((a : M), f a) ∈ G := by
  obtain ⟨h, hmem, -⟩ := exists_isElementaryOn_of_isPartialElem hG hdom
  refine ⟨⟨h, fun k φ x => ?_⟩, hmem⟩
  rw [← S.subtype.map_formula φ x]
  exact (hG φ (fun i => (((x i : M)), h (x i))) fun i => hmem (x i)).symm

end Closure

/-! ## Existence of a prime model over an arbitrary parameter set -/

section PrimeModel

variable {L : FirstOrder.Language.{0, 0}}

/-- **Prime models exist over every parameter set.**

If the isolated types are dense in every space of complete `1`-types — which, by
`Submission.Morley.isolatedDense_of_isOmegaStable`, holds in an `ω`-stable theory — then over
*every* subset `A` of a model `M` of `T` there is a prime model: a model `N` of `T`, an elementary
embedding `f : N ↪ₑ[L] M`, and a subset `A'` of `N` carried by `f` onto `A`, such that `N` is
prime over `A'`, and moreover atomic over `A'`.

This is `Submission.Morley.exists_prime_of_isolatedDense` with the countability hypothesis on `A`
removed (and with it the countability of `N`).  The construction is transfinite: elements of
isolated type over the parameters gathered so far are adjoined one at a time along a well-order
long enough that the process must stabilise, and stabilisation is exactly the Tarski–Vaught
condition.  Primality does *not* follow from atomicity here — over an uncountable parameter set
atomic models need not be prime — but from *constructibility*: a partial elementary map is
extended along the very same well-order, one element at a time, each step being possible because
the new element has isolated type over the current domain. -/
theorem exists_prime_of_isolatedDense' {T : L.Theory} (hID : IsolatedDense.{0, 0, 0} T)
    (M : T.ModelType.{0, 0, 0}) (A : Set M) :
    ∃ (N : T.ModelType.{0, 0, 0}) (f : N ↪ₑ[L] M) (A' : Set N),
      (fun x : N => (f x : M)) '' A' = A ∧ IsPrime N A' ∧ IsAtomic N A' := by
  classical
  obtain ⟨o, hmeets⟩ := exists_stage_meetsDefinable L (M := (M : Type)) (fun B => hID M B) A
  set S : L.ElementarySubstructure (M : Type) := hmeets.toElementarySubstructure with hS
  have hcoe : ((S : L.ElementarySubstructure (M : Type)) : Set M) = constrSet L A o :=
    hmeets.closure_eq_self
  have hAC : A ⊆ ((S : L.ElementarySubstructure (M : Type)) : Set M) := by
    rw [hcoe]; exact subset_constrSet L A o
  have hatom : AtomicOn L (M : Type) A (constrSet L A o) := atomicOn_constrSet L A o
  set A' : Set ↥S := Subtype.val ⁻¹' A with hA'
  let e : ↥A' ≃ ↥A :=
    { toFun := fun a => ⟨((a : ↥S) : M), a.2⟩
      invFun := fun b => ⟨⟨(b : M), hAC b.2⟩, b.2⟩
      left_inv := fun a => Subtype.ext (Subtype.ext rfl)
      right_inv := fun b => Subtype.ext rfl }
  have he : ∀ a : ↥A', ((a : ↥S) : M) = ((e a : M)) := fun _ => rfl
  refine ⟨S.toModel T, S.subtype, A', ?_, ?_, ?_⟩
  · show (Subtype.val : ↥S → ↥M) '' (Subtype.val ⁻¹' A) = A
    exact Set.image_preimage_eq_of_subset (by rw [Subtype.range_coe]; exact hAC)
  · -- primality
    intro K g hg
    -- transport the partial elementary map to the copy of `A` inside `M`
    set g' : ↥A → K := fun a => g ⟨⟨(a : M), hAC a.2⟩, a.2⟩ with hg'
    have hgel : IsElementaryOn L A g' := by
      refine isElementaryOn_of_realize_fin fun k φ x => ?_
      have h1 := S.subtype.map_formula φ fun i => (⟨((x i : M)), hAC (x i).2⟩ : ↥S)
      have h2 := hg.realize_fin φ fun i => (⟨⟨((x i : M)), hAC (x i).2⟩, (x i).2⟩ : ↥A')
      exact h1.trans h2
    obtain ⟨hP, hD⟩ := mapSet_isPartialElem_and_dom L (isPartialElem_graphOfMap hgel)
      (fst_image_graphOfMap g') o
    obtain ⟨f, hf⟩ := exists_elementaryEmbedding_of_isPartialElem L hP
      (S := S) (hD.trans hcoe.symm)
    refine ⟨f, fun a => ?_⟩
    have hmemGA' : (S.subtype a.1, g' (e a)) ∈ mapSet L A (graphOfMap g') o :=
      mapBelow_subset_mapSet L A (graphOfMap g') o
        (graph_subset_mapBelow L A (graphOfMap g') o ⟨e a, rfl⟩)
    have := hP.functional (hf a.1) hmemGA'
    refine this.trans ?_
    rw [hg']
    exact congrArg g (Subtype.ext (Subtype.ext rfl))
  · -- atomicity
    intro k x
    let x' : Fin k → ↥S := x
    refine isIsolated_typeOf_of_elementarySubstructure S e he x' ?_
    refine hatom k (fun i => ((x' i : ↥M))) fun i => ?_
    have h2 : ((x' i : ↥S) : M) ∈ ((S : L.ElementarySubstructure (M : Type)) : Set M) :=
      SetLike.mem_coe.2 (x' i).2
    rwa [hcoe] at h2

/-- **Prime models exist over every parameter set in an `ω`-stable theory.**

This is the lift of `Submission.Morley.exists_prime_of_isOmegaStable` to an arbitrary — in
particular uncountable — parameter set: the countability hypothesis on `A` is gone, and with it
the countability of `N`. -/
theorem exists_prime_of_isOmegaStable' {T : L.Theory} (hL : L.card ≤ ℵ₀)
    (hst : IsOmegaStable.{0, 0, 0} T) (M : T.ModelType.{0, 0, 0}) (A : Set M) :
    ∃ (N : T.ModelType.{0, 0, 0}) (f : N ↪ₑ[L] M) (A' : Set N),
      (fun x : N => (f x : M)) '' A' = A ∧ IsPrime N A' ∧ IsAtomic N A' :=
  exists_prime_of_isolatedDense' (isolatedDense_of_isOmegaStable hL hst) M A

end PrimeModel

/-! ## Existence of an atomic model over an arbitrary parameter set -/

section AtomicModel

variable {L : FirstOrder.Language.{0, 0}}

/-- **Atomic models exist over every parameter set.**

If the isolated types are dense in every space of complete `1`-types — which, by
`Submission.Morley.isolatedDense_of_isOmegaStable`, holds in an `ω`-stable theory — then over
*every* subset `A` of a model `M` of `T` there is a model `N` of `T`, an elementary embedding
`f : N ↪ₑ[L] M`, and a subset `A'` of `N` carried by `f` onto `A`, such that `N` is atomic
over `A'`.

This is `Submission.Morley.exists_prime_of_isolatedDense` with the countability hypothesis on `A`
removed.  What is lost is primality: over an uncountable parameter set atomicity no longer implies
primality (`Submission.Morley.isPrime_of_isAtomic` genuinely needs `[Countable M]`), and the
correct hypothesis there is constructibility.  Atomicity is what the two-cardinal transfer
argument consumes. -/
theorem exists_atomic_of_isolatedDense {T : L.Theory} (h : IsolatedDense.{0, 0, 0} T)
    (M : T.ModelType.{0, 0, 0}) (A : Set M) :
    ∃ (N : T.ModelType.{0, 0, 0}) (f : N ↪ₑ[L] M) (A' : Set N),
      (fun x : N => (f x : M)) '' A' = A ∧ IsAtomic N A' := by
  classical
  obtain ⟨S, hAS, hatom⟩ :=
    exists_atomic_elementarySubstructure_of_isolatedDense (M := (M : Type)) (fun B => h M B) A
  set A' : Set ↥S := Subtype.val ⁻¹' A with hA'
  let e : ↥A' ≃ ↥A :=
    { toFun := fun a => ⟨((a : ↥S) : M), a.2⟩
      invFun := fun b => ⟨⟨(b : M), hAS b.2⟩, b.2⟩
      left_inv := fun a => Subtype.ext (Subtype.ext rfl)
      right_inv := fun b => Subtype.ext rfl }
  have he : ∀ a : ↥A', ((a : ↥S) : M) = ((e a : M)) := fun _ => rfl
  refine ⟨S.toModel T, S.subtype, A', ?_, ?_⟩
  · show (Subtype.val : ↥S → ↥M) '' (Subtype.val ⁻¹' A) = A
    exact Set.image_preimage_eq_of_subset (by rw [Subtype.range_coe]; exact hAS)
  · intro k x
    let x' : Fin k → ↥S := x
    exact isIsolated_typeOf_of_elementarySubstructure S e he x'
      (hatom k (fun i => ((x' i : ↥M))) fun i => (x' i).2)

/-- **Atomic models exist over every parameter set in an `ω`-stable theory.**

This is the lift of `Submission.Morley.exists_prime_of_isOmegaStable` to an arbitrary — in
particular uncountable — parameter set: the countability hypothesis on `A` is gone, and with it
the countability of `N` and the primality of `N` over `A'`, which is replaced by atomicity. -/
theorem exists_atomic_of_isOmegaStable {T : L.Theory} (hL : L.card ≤ ℵ₀)
    (hst : IsOmegaStable.{0, 0, 0} T) (M : T.ModelType.{0, 0, 0}) (A : Set M) :
    ∃ (N : T.ModelType.{0, 0, 0}) (f : N ↪ₑ[L] M) (A' : Set N),
      (fun x : N => (f x : M)) '' A' = A ∧ IsAtomic N A' :=
  exists_atomic_of_isolatedDense (isolatedDense_of_isOmegaStable hL hst) M A

/-- **The atomic elementary substructure over an arbitrary parameter set, in an `ω`-stable
theory.**  The form in which two-cardinal transfer uses it: an elementary substructure of a fixed
ambient model, containing the prescribed parameter set, all of whose finite tuples realise
isolated types over that parameter set. -/
theorem exists_atomic_elementarySubstructure_of_isOmegaStable {T : L.Theory} (hL : L.card ≤ ℵ₀)
    (hst : IsOmegaStable.{0, 0, 0} T) (M : T.ModelType.{0, 0, 0}) (A : Set M) :
    ∃ S : L.ElementarySubstructure (M : Type), A ⊆ (S : Set M) ∧
      AtomicOn L (M : Type) A (S : Set M) :=
  exists_atomic_elementarySubstructure_of_isolatedDense (M := (M : Type))
    (fun B => isolatedDense_of_isOmegaStable hL hst M B) A

end AtomicModel

/-! ## The prime-model step of two-cardinal transfer, over an arbitrary parameter set -/

section DefSet

variable {L : FirstOrder.Language.{0, 0}}

/-- **The prime model over an arbitrary parameter set carries the same definable set.**

This is `Submission.Morley.exists_prime_defSet_mk_eq` with the countability hypothesis on the
parameter set `B` removed (and with it the countability of `N`): if `B ⊆ M` contains the
parameters `b̄` of `χ` together with the whole set `χ(M)` that they define, then the prime model
over `B` has its `χ`-definable set carried bijectively onto `χ(M)`.

This is the shape in which the successor step of the length-`κ` elementary chain of two-cardinal
transfer consumes a prime model, and it is exactly the shape that was unavailable while prime
models existed only over countable parameter sets. -/
theorem exists_prime_defSet_mk_eq' (hL : L.card ≤ ℵ₀) {T : L.Theory}
    (hst : IsOmegaStable.{0, 0, 0} T) (M : T.ModelType.{0, 0, 0}) {β : Type} [Finite β]
    (χ : L.BoundedFormula β 1) (b : β → M) (B : Set M) (hbB : ∀ i, b i ∈ B)
    (hXB : {a : M | χ.Realize b fun _ => a} ⊆ B) :
    ∃ (N : T.ModelType.{0, 0, 0}) (f : N ↪ₑ[L] M) (B' : Set N) (b' : β → N),
      IsPrime N B' ∧ IsAtomic N B' ∧ (fun x : N => (f x : M)) '' B' = B ∧
        (∀ i, b' i ∈ B') ∧ (∀ i, f (b' i) = b i) ∧
        (fun x : N => (f x : M)) '' {a : N | χ.Realize b' fun _ => a}
          = {a : M | χ.Realize b fun _ => a} ∧
        #{a : N | χ.Realize b' fun _ => a} = #{a : M | χ.Realize b fun _ => a} := by
  classical
  obtain ⟨N, f, B', himg, hprime, hatomic⟩ := exists_prime_of_isOmegaStable' hL hst M B
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
  refine ⟨N, f, B', b', hprime, hatomic, himg, hb'mem, hb'eq, himg2, ?_⟩
  rw [← himg2, Cardinal.mk_image_eq f.injective]

end DefSet

/-! ## An atomic extension realises no new countable type -/

section NoNewTypes

/-- A map out of `Fin 1` is determined by its value at `0`. -/
theorem funext_fin_one {X : Sort*} (u : Fin 1 → X) : (fun _ : Fin 1 => u 0) = u :=
  funext fun i => by rw [Subsingleton.elim i 0]

variable {L : FirstOrder.Language.{u, v}} {𝔐 : Type w} [L.Structure 𝔐] [Nonempty 𝔐]

/-- **Step (3) of two-cardinal transfer.**

Let `S` be an elementary substructure of `𝔐` (in the form `L.MeetsDefinable S`) and let `c ∈ 𝔐`
have the *generic* property that every countable set of formulas over `S` satisfied by `c` is
already satisfied by an element of `S`.  If `b ∈ 𝔐` realises an **isolated** type over `S ∪ {c}`
— which is what a prime, or merely atomic, model over `S ∪ {c}` provides, by
`Submission.Morley.exists_prime_of_isOmegaStable'` — and `b` satisfies a formula `ψ` over `S` whose
solution set inside `S` is countable, then `b ∈ S`.

In particular the extension adds no new element to a countable definable set: this is exactly what
makes the successor step of the length-`κ` elementary chain preserve the small side of a
two-cardinal model.

The proof is the classical one.  Let `θ(w, c, s̄)` isolate `tp(b / S ∪ {c})` and let
`Γ = {ψ(w)} ∪ {w ≠ a | a ∈ ψ(S)}`, a countable set of formulas over `S` realised by `b`.  Then
`Δ = {∃w θ(w, v, s̄)} ∪ {∀w (θ(w, v, s̄) → γ(w)) | γ ∈ Γ}` is a countable set of formulas over `S`
satisfied by `c`, so some `c' ∈ S` satisfies it; a witness `b' ∈ S` for `∃w θ(w, c', s̄)` then
realises `Γ` inside `S`, which is absurd. -/
theorem mem_of_isIsolated_of_countable {S : Set 𝔐} (hS : L.MeetsDefinable S) (hSne : S.Nonempty)
    (c : 𝔐)
    (hgen : ∀ u : ℕ → (L[[↥S]]).Formula (Fin 1), (∀ n, (u n).Realize fun _ => c) →
      ∃ a : ↥S, ∀ n, (u n).Realize fun _ => ((a : 𝔐)))
    (ψ : (L[[↥S]]).Formula (Fin 1))
    (hY : {a : ↥S | ψ.Realize fun _ => ((a : 𝔐))}.Countable) {b : 𝔐}
    (hb : (((L[[↥(insert c S)]]).completeTheory 𝔐).typeOf fun _ : Fin 1 => b).IsIsolated)
    (hψb : ψ.Realize fun _ => b) : b ∈ S := by
  classical
  haveI : Nonempty ↥S := hSne.to_subtype
  by_contra hbS
  obtain ⟨enum, henum⟩ := Set.countable_iff_exists_subset_range.1 hY
  -- the countable set `Γ` of formulas over `S`, realised by `b` and omitted in `S`
  obtain ⟨Γ, hΓ0, hΓsucc⟩ : ∃ Γ : ℕ → (L[[↥S]]).Formula (Fin 1), Γ 0 = ψ ∧
      ∀ k, Γ (k + 1) = ∼((Term.var 0).equal (L.con (enum k)).term) :=
    ⟨fun n => Nat.casesOn n ψ fun k => ∼((Term.var 0).equal (L.con (enum k)).term), rfl,
      fun _ => rfl⟩
  have hΓne : ∀ (k : ℕ) (z : 𝔐), (Γ (k + 1)).Realize (fun _ : Fin 1 => z) ↔ z ≠ ((enum k : 𝔐)) := by
    intro k z
    rw [hΓsucc]
    simp [Formula.realize_not, Formula.realize_equal, Term.realize_constants]
  have hΓb : ∀ n, (Γ n).Realize fun _ : Fin 1 => b := by
    intro n
    cases n with
    | zero => rw [hΓ0]; exact hψb
    | succ k => exact (hΓne k b).2 fun hcon => hbS (hcon ▸ (enum k).2)
  -- an isolating formula for the type of `b` over `S ∪ {c}`
  rw [CompleteType.isIsolated_typeOf_iff_of_isComplete
    (completeTheory.isComplete (L := L[[↥(insert c S)]]) 𝔐)] at hb
  obtain ⟨θ, hθb, hθu⟩ := hb
  have hθΓ : ∀ z : Fin 1 → 𝔐, θ.Realize z → ∀ n, (Γ n).Realize z := by
    intro z hz n
    exact (CompleteType.realize_iff_of_typeOf_eq z (fun _ => b)
      (CompleteType.typeOf_eq_of_typeOf_eq_of_subset (Set.subset_insert c S) z (fun _ => b)
        (hθu z hz)) (Γ n)).2 (hΓb n)
  -- separate the parameter `c` from the parameters in `S`
  obtain ⟨n, d, ψ₀, hψ₀⟩ := Formula.exists_fin_params θ
  set Sidx : Finset (Fin n) := Finset.univ.filter (fun i => ((d i : 𝔐)) ∈ S) with hSidx
  have hmemSidx : ∀ i : Fin n, i ∈ Sidx ↔ ((d i : 𝔐)) ∈ S := by intro i; simp [hSidx]
  set sp : Fin Sidx.card → ↥S := fun r =>
    ⟨((d (Sidx.equivFin.symm r) : 𝔐)), (hmemSidx _).1 (Sidx.equivFin.symm r).2⟩ with hsp
  set ρ : Fin n → Fin 1 ⊕ Fin Sidx.card := fun i =>
    if h : ((d i : 𝔐)) ∈ S then Sum.inr (Sidx.equivFin ⟨i, (hmemSidx i).2 h⟩) else Sum.inl 0
    with hρ
  set τ : Fin 1 ⊕ Fin n → (Fin 1 ⊕ Fin 1) ⊕ Fin Sidx.card :=
    Sum.elim (fun w => Sum.inl (Sum.inl w))
      (fun i => Sum.elim (fun v : Fin 1 => Sum.inl (Sum.inr v)) (fun j => Sum.inr j) (ρ i))
    with hτ
  set Θ : (L[[↥S]]).Formula (Fin 1 ⊕ Fin 1) := substParams (ψ₀.relabel τ) sp with hΘdef
  have hΘ : ∀ w y : 𝔐, Θ.Realize (Sum.elim (fun _ : Fin 1 => w) fun _ : Fin 1 => y) ↔
      ψ₀.Realize (Sum.elim (fun _ : Fin 1 => w)
        fun i => if ((d i : 𝔐)) ∈ S then ((d i : 𝔐)) else y) := by
    intro w y
    rw [hΘdef, realize_substParams (ψ₀.relabel τ) sp (K := 𝔐), Formula.realize_relabel]
    have hcomp : (Sum.elim (Sum.elim (fun _ : Fin 1 => w) fun _ : Fin 1 => y)
        fun j => ((L.con (sp j) : 𝔐))) ∘ τ =
        Sum.elim (fun _ : Fin 1 => w)
          (fun i => if ((d i : 𝔐)) ∈ S then ((d i : 𝔐)) else y) := by
      funext z
      rcases z with w' | i
      · rfl
      · by_cases h : ((d i : 𝔐)) ∈ S
        · simp only [Function.comp_apply, hτ, Sum.elim_inr, hρ, dif_pos h, if_pos h, hsp,
            Equiv.symm_apply_apply]
          rfl
        · simp only [Function.comp_apply, hτ, Sum.elim_inr, hρ, dif_neg h, Sum.elim_inl,
            Sum.elim_inr, if_neg h]
    rw [hcomp]
  have hdc : (fun i : Fin n => if ((d i : 𝔐)) ∈ S then ((d i : 𝔐)) else c) =
      fun i => ((d i : 𝔐)) := by
    funext i
    by_cases h : ((d i : 𝔐)) ∈ S
    · rw [if_pos h]
    · rw [if_neg h]
      rcases (d i).2 with h' | h'
      · exact h'.symm
      · exact absurd h' h
  have hΘc : ∀ w : 𝔐, Θ.Realize (Sum.elim (fun _ : Fin 1 => w) fun _ : Fin 1 => c) ↔
      θ.Realize fun _ : Fin 1 => w := by
    intro w
    rw [hΘ w c, hdc]
    exact (hψ₀ _).symm
  -- the countable set `Δ` of formulas over `S`, satisfied by `c`
  set Θ' : (L[[↥S]]).Formula (Fin 1 ⊕ Fin 1) := Θ.relabel Sum.swap with hΘ'def
  have hΘ' : ∀ y w : 𝔐, Θ'.Realize (Sum.elim (fun _ : Fin 1 => y) fun _ : Fin 1 => w) ↔
      Θ.Realize (Sum.elim (fun _ : Fin 1 => w) fun _ : Fin 1 => y) := by
    intro y w
    rw [hΘ'def, Formula.realize_relabel]
    have : (Sum.elim (fun _ : Fin 1 => y) fun _ : Fin 1 => w) ∘ Sum.swap =
        Sum.elim (fun _ : Fin 1 => w) fun _ : Fin 1 => y := by
      funext z; rcases z with j | j <;> rfl
    rw [this]
  obtain ⟨δ, hδ0def, hδsuccdef⟩ : ∃ δ : ℕ → (L[[↥S]]).Formula (Fin 1),
      δ 0 = Θ'.existsRight ∧
      ∀ k, δ (k + 1) = ∼((Θ' ⊓ ∼((Γ k).relabel Sum.inr)).existsRight) :=
    ⟨fun n => Nat.casesOn n Θ'.existsRight
      fun k => ∼((Θ' ⊓ ∼((Γ k).relabel Sum.inr)).existsRight), rfl, fun _ => rfl⟩
  have hδ0 : ∀ y : 𝔐, (δ 0).Realize (fun _ : Fin 1 => y) ↔
      ∃ w : 𝔐, Θ.Realize (Sum.elim (fun _ : Fin 1 => w) fun _ : Fin 1 => y) := by
    intro y
    rw [hδ0def, Formula.realize_existsRight]
    constructor
    · rintro ⟨u, hu⟩
      refine ⟨u 0, ?_⟩
      rw [← hΘ' y (u 0), funext_fin_one u]
      exact hu
    · rintro ⟨w, hw⟩
      exact ⟨fun _ => w, (hΘ' y w).2 hw⟩
  have hδsucc : ∀ (k : ℕ) (y : 𝔐), (δ (k + 1)).Realize (fun _ : Fin 1 => y) ↔
      ∀ w : 𝔐, Θ.Realize (Sum.elim (fun _ : Fin 1 => w) fun _ : Fin 1 => y) →
        (Γ k).Realize fun _ : Fin 1 => w := by
    intro k y
    rw [hδsuccdef, Formula.realize_not, Formula.realize_existsRight]
    constructor
    · intro hno w hw
      by_contra hγ
      refine hno ⟨fun _ => w, ?_⟩
      rw [Formula.realize_inf]
      refine ⟨(hΘ' y w).2 hw, ?_⟩
      rw [Formula.realize_not, Formula.realize_relabel]
      exact hγ
    · rintro hall ⟨u, hu⟩
      rw [Formula.realize_inf] at hu
      obtain ⟨hu1, hu2⟩ := hu
      rw [Formula.realize_not, Formula.realize_relabel] at hu2
      refine hu2 ?_
      have h1 : Θ.Realize (Sum.elim (fun _ : Fin 1 => u 0) fun _ : Fin 1 => y) := by
        rw [← hΘ' y (u 0), funext_fin_one u]
        exact hu1
      have h2 := hall (u 0) h1
      rwa [funext_fin_one u] at h2
  have hδc : ∀ m, (δ m).Realize fun _ : Fin 1 => c := by
    intro m
    cases m with
    | zero => exact (hδ0 c).2 ⟨b, (hΘc b).2 hθb⟩
    | succ k => exact (hδsucc k c).2 fun w hw => hθΓ (fun _ => w) ((hΘc w).1 hw) k
  -- the generic property of `c` produces a realisation of `Δ` inside `S`
  obtain ⟨c', hc'⟩ := hgen δ hδc
  obtain ⟨w₀, hw₀⟩ := (hδ0 ((c' : 𝔐))).1 (hc' 0)
  set φD : (L[[↥S]]).Formula (Fin 1) :=
    Θ.subst (Sum.elim (fun w : Fin 1 => Term.var w) fun _ : Fin 1 => (L.con c').term) with hφDdef
  have hφD : ∀ z : 𝔐, φD.Realize (fun _ : Fin 1 => z) ↔
      Θ.Realize (Sum.elim (fun _ : Fin 1 => z) fun _ : Fin 1 => ((c' : 𝔐))) := by
    intro z
    have hfun : (fun a : Fin 1 ⊕ Fin 1 => Term.realize (fun _ : Fin 1 => z)
        (Sum.elim (fun w : Fin 1 => Term.var w) (fun _ : Fin 1 => (L.con c').term) a)) =
        Sum.elim (fun _ : Fin 1 => z) fun _ : Fin 1 => ((c' : 𝔐)) := by
      funext x
      rcases x with j | j
      · rfl
      · simp [Term.realize_constants]
    rw [hφDdef]
    simp only [Formula.Realize, BoundedFormula.realize_subst, hfun]
  -- the definable set it defines is nonempty, so it meets `S`
  obtain ⟨b', hb'D, hb'S⟩ := hS
    {z : 𝔐 | Θ.Realize (Sum.elim (fun _ : Fin 1 => z) fun _ : Fin 1 => ((c' : 𝔐)))}
    ⟨w₀, hw₀⟩
    ⟨φD, by
      ext x
      simp only [Set.mem_setOf_eq]
      rw [← hφD (x 0), funext_fin_one x]⟩
  -- but then `b'` realises `Γ` inside `S`
  have hΓb' : ∀ k, (Γ k).Realize fun _ : Fin 1 => b' := fun k =>
    (hδsucc k ((c' : 𝔐))).1 (hc' (k + 1)) b' hb'D
  have hψb' : ψ.Realize fun _ : Fin 1 => b' := hΓ0 ▸ hΓb' 0
  obtain ⟨k, hk⟩ := henum (show (⟨b', hb'S⟩ : ↥S) ∈ {a : ↥S | ψ.Realize fun _ => ((a : 𝔐))} from
    hψb')
  exact (hΓne k b').1 (hΓb' (k + 1)) (by rw [hk])

end NoNewTypes

end Submission.Morley
