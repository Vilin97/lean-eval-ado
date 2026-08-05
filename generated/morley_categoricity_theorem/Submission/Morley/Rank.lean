import Mathlib
import Submission.Morley.Stable
import Submission.Morley.Transfer
import Submission.Morley.Vaught
import Submission.Morley.Saturated
import Submission.Morley.Assembly

/-!
# Morley rank and Morley degree

This file develops Morley rank for the formalisation of Morley's categoricity theorem, and uses it
to prove the saturation principle `Submission.Morley.SaturationPrinciple` of
`Submission/Morley/Assembly.lean` **in Morley rank one**, i.e. for strongly minimal theories.

## Main definitions

* `Submission.Morley.RankGE T o φ`: the formula `φ` has Morley rank at least the ordinal `o`,
  relative to a theory `T`.  This is the standard recursion — rank `≥ 0` means consistent, rank
  `≥ o` means that for every `q < o` there are infinitely many pairwise contradictory
  consequences of `φ` of rank `≥ q` — carried out by well-founded recursion on `o`.  Phrasing the
  recursion with `∀ q < o` rather than by cases on successors and limits makes antitonicity in `o`
  and closure under suprema immediate, and the successor form is recovered in
  `Submission.Morley.rankGE_succ_iff`.
* `Submission.Morley.MRank T φ`: the Morley rank of `φ`, an `Ordinal`.
* `Submission.Morley.DegGE T o φ n` and `Submission.Morley.MDegree T φ`: the Morley degree, the
  greatest number of pairwise contradictory formulas of full rank into which `φ` splits.
* `Submission.Morley.realSet A φ`: the subset of `M` defined by a formula with parameters in
  `A ⊆ M`, and `Submission.Morley.up φ` a formula with parameters in all of `M` defining the same
  set.
* `Submission.Morley.typeRank p`: the Morley rank of a complete `1`-type, the least rank of one of
  its formulas.

**Ordinals, not `ℕ∞`.**  `ℕ∞` is not enough: the rank of an ω-stable theory is an arbitrary
ordinal (`ℕ∞`-valued rank is *finite* Morley rank, a strictly stronger hypothesis than
ω-stability, and Morley's theorem is proved for all ω-stable theories).  Using `Ordinal` costs
almost nothing here because the recursion is by well-founded recursion either way.

**Parameters from the whole model.**  Morley rank is taken relative to `paramTheory L Set.univ`,
i.e. formulas may use *every* element of `M` as a parameter.  This is essential: with parameters
restricted to a small set `A`, rank `0` would not mean "finitely many realisations" (over `A = ∅`
in the theory of an infinite set, `x = x` would have rank `0`).  Formulas with parameters in a
small `A` are transported by `Submission.Morley.up`, which goes through
`FirstOrder.Language.Set.Definable₁` and so needs no syntactic relabelling.

## Main results

* `Submission.Morley.exists_rankGE_stable`: the rank hierarchy stabilises (a counting argument).
* `Submission.Morley.exists_binaryTree_of_rankGE`: a formula of unbounded rank produces a binary
  tree of formulas, and hence
* `Submission.Morley.exists_not_rankGE_of_omegaStable`: **in an ω-stable theory every formula has
  an ordinal Morley rank**, over an arbitrary parameter set.  The descent of a binary tree to a
  countable parameter set is `Submission.Morley.exists_countable_binaryTree`.
* `Submission.Morley.rankGE_zero_iff_nonempty`, `Submission.Morley.rankGE_one_iff_infinite`:
  rank `≥ 0` is consistency and rank `≥ 1` is infiniteness of the defined set.
* `Submission.Morley.rankGE_inf_or_rankGE_inf_not`: the rank of a formula is the maximum of the
  ranks of the two halves of a binary split of it.
* `Submission.Morley.rankGE_succ_of_forall_degGE`, `Submission.Morley.exists_not_degGE`,
  `Submission.Morley.one_le_mdegree`: **the Morley degree is finite and at least one**.
* `Submission.Morley.exists_mem_forall_not_rankGE_typeRank`: **a formula of least rank and least
  degree in a type**: every complete type `p` contains a formula `φ` such that `φ ∧ ¬ψ` has rank
  `< RM(p)` for every `ψ ∈ p`.  This is the classical "least rank, then least degree" choice; the
  degree is bypassed by a direct descent.
* `Submission.Morley.mem_realizedTypes_of_typeRank_le_one`: **a type of Morley rank at most one
  over a small parameter set is realised** in a definably full model of uncountable cardinality.
* `Submission.Morley.isSaturated_of_mrank_top_le_one` and
  `Submission.Morley.isSaturated_of_not_hasVaughtianPair_of_mrank_top_le_one`: **the saturation
  principle in Morley rank one**, in the definably-full and in the Vaughtian-pair form.
* `Submission.Morley.mrank_top_le_one_of_forall_finite_or_compl_finite`: a minimal structure — one
  in which every parameter-definable set is finite or cofinite — has Morley rank at most one, so
  the hypothesis of the previous item is exactly strong minimality.

## What is *not* proved

`Submission.Morley.SaturationPrinciple` in general.  The argument here is the classical one:
with `φ ∈ p` of least rank `α` and least degree, an omitted `p` makes the sets `φ ∧ ¬ψ`, `ψ ∈ p`,
cover `φ(M)`, and these have rank `< α`.  For `α ≤ 1` the pieces have rank `0`, hence are
**finite**, and `≤ #A + ℵ₀ < #M` finite sets cannot cover `φ(M)`, which is of size `#M` by
definable fullness.  For `α ≥ 2` the pieces can be infinite, and definable fullness then makes
them of size `#M` as well, so the counting genuinely stops: ω-stability together with definable
fullness does **not** suffice.  (Witness: the theory of an equivalence relation with infinitely
many infinite classes is ω-stable, and a model with `ℵ₀` classes each of size `ℵ₁` is definably
full but omits the type "in no class meeting `A`" for a countable `A` meeting every class; it has
Vaughtian pairs.)  Closing the gap for `α ≥ 2` requires the absence of Vaughtian pairs in its
strong form — no proper elementary submodel contains an infinite definable set — through the
Baldwin–Lachlan analysis: a strongly minimal formula, algebraic closure as a pregeometry, and
primality and minimality of a model over a strongly minimal set.  None of that is developed here.
-/

universe u

open Cardinal Set FirstOrder Language Theory

namespace Submission.Morley

section AbstractRank

variable {K : FirstOrder.Language.{u, u}} {V : Type u}

/-- `RankGE T o φ` says that the Morley rank of the formula `φ` relative to the theory `T` is at
least the ordinal `o`. -/
def RankGE (T : K.Theory) (o : Ordinal.{u}) (φ : K[[V]].Sentence) : Prop :=
  (T.typesWith φ).Nonempty ∧
    ∀ q < o, ∃ ψ : ℕ → K[[V]].Sentence,
      (∀ i, T.typesWith (ψ i) ⊆ T.typesWith φ) ∧
      (∀ i j, i ≠ j → Disjoint (T.typesWith (ψ i)) (T.typesWith (ψ j))) ∧
      (∀ i, RankGE T q (ψ i))
  termination_by o

theorem rankGE_def (T : K.Theory) (o : Ordinal.{u}) (φ : K[[V]].Sentence) :
    RankGE T o φ ↔ (T.typesWith φ).Nonempty ∧
      ∀ q < o, ∃ ψ : ℕ → K[[V]].Sentence,
        (∀ i, T.typesWith (ψ i) ⊆ T.typesWith φ) ∧
        (∀ i j, i ≠ j → Disjoint (T.typesWith (ψ i)) (T.typesWith (ψ j))) ∧
        (∀ i, RankGE T q (ψ i)) := by
  rw [RankGE]

theorem RankGE.nonempty {T : K.Theory} {o : Ordinal.{u}} {φ : K[[V]].Sentence}
    (h : RankGE T o φ) : (T.typesWith φ).Nonempty := ((rankGE_def T o φ).1 h).1

theorem rankGE_zero_iff {T : K.Theory} {φ : K[[V]].Sentence} :
    RankGE T 0 φ ↔ (T.typesWith φ).Nonempty := by
  rw [rankGE_def]
  exact ⟨And.left, fun h => ⟨h, fun q hq => absurd hq (by simp)⟩⟩

/-- Morley rank is antitone in the ordinal: rank at least `o` implies rank at least `o'` for
`o' ≤ o`. -/
theorem RankGE.mono_ord {T : K.Theory} {o o' : Ordinal.{u}} {φ : K[[V]].Sentence} (hoo : o' ≤ o)
    (h : RankGE T o φ) : RankGE T o' φ := by
  rw [rankGE_def] at h ⊢
  exact ⟨h.1, fun q hq => h.2 q (hq.trans_le hoo)⟩

/-- Morley rank is monotone in the formula. -/
theorem RankGE.mono {T : K.Theory} {o : Ordinal.{u}} {φ φ' : K[[V]].Sentence}
    (hsub : T.typesWith φ ⊆ T.typesWith φ') (h : RankGE T o φ) : RankGE T o φ' := by
  rw [rankGE_def] at h ⊢
  refine ⟨h.1.mono hsub, fun q hq => ?_⟩
  obtain ⟨ψ, h1, h2, h3⟩ := h.2 q hq
  exact ⟨ψ, fun i => (h1 i).trans hsub, h2, h3⟩

theorem rankGE_succ_iff {T : K.Theory} {o : Ordinal.{u}} {φ : K[[V]].Sentence} :
    RankGE T (o + 1) φ ↔ ∃ ψ : ℕ → K[[V]].Sentence,
      (∀ i, T.typesWith (ψ i) ⊆ T.typesWith φ) ∧
      (∀ i j, i ≠ j → Disjoint (T.typesWith (ψ i)) (T.typesWith (ψ j))) ∧
      (∀ i, RankGE T o (ψ i)) := by
  constructor
  · intro h
    exact ((rankGE_def T (o + 1) φ).1 h).2 o (Order.lt_succ_of_le le_rfl)
  · rintro ⟨ψ, h1, h2, h3⟩
    rw [rankGE_def]
    refine ⟨(h3 0).nonempty.mono (h1 0), fun q hq => ⟨ψ, h1, h2, fun i => ?_⟩⟩
    exact (h3 i).mono_ord (Order.lt_succ_iff.1 hq)

/-- Morley rank is closed under suprema: if a formula has rank at least every `q < o` then it has
rank at least `o`.  Together with `Submission.Morley.RankGE.mono_ord` this says that the ordinals
`o` with `RankGE T o φ` form a (possibly unbounded) closed initial segment. -/
theorem rankGE_of_forall_lt {T : K.Theory} {o : Ordinal.{u}} {φ : K[[V]].Sentence}
    (hne : (T.typesWith φ).Nonempty) (h : ∀ q < o, RankGE T (q + 1) φ) : RankGE T o φ := by
  rw [rankGE_def]
  refine ⟨hne, fun q hq => ?_⟩
  exact rankGE_succ_iff.1 (h q hq)

/-! ### The rank stabilises -/

/-- **The Morley rank hierarchy stabilises.**  There is an ordinal `o` at which the family of
formulas of rank at least `o` stops shrinking.  The proof is a counting argument: a strictly
decreasing family would inject the ordinals into the (small) type of formulas. -/
theorem exists_rankGE_stable (T : K.Theory) :
    ∃ o : Ordinal.{u}, ∀ φ : K[[V]].Sentence, RankGE T o φ → RankGE T (o + 1) φ := by
  classical
  by_contra hcon
  push Not at hcon
  choose f hf1 hf2 using hcon
  have hinj : Function.Injective f := by
    intro o o' h
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact hf2 o (h ▸ (hf1 o').mono_ord (Order.succ_le_of_lt hlt))
    · exact hf2 o' (h ▸ (hf1 o).mono_ord (Order.succ_le_of_lt hlt))
  set c : Cardinal.{u} := #(K[[V]].Sentence) with hc
  have hle : #((Order.succ c).ord.ToType) ≤ c :=
    Cardinal.mk_le_of_injective
      (f := fun x => f (Ordinal.typein (α := (Order.succ c).ord.ToType) (· < ·) x))
      (hinj.comp (Ordinal.typein_injective _))
  rw [Cardinal.mk_toType, Cardinal.card_ord] at hle
  exact absurd hle (not_le.2 (Order.lt_succ c))

/-- **A formula of unboundedly large Morley rank produces a binary tree of formulas.**  At the
stabilisation ordinal every formula of rank at least `o` splits into two contradictory formulas of
rank at least `o`, which is exactly the splitting condition of a Cantor scheme. -/
theorem exists_binaryTree_of_rankGE {T : K.Theory} {o : Ordinal.{u}}
    (hstab : ∀ χ : K[[V]].Sentence, RankGE T o χ → RankGE T (o + 1) χ)
    {φ : K[[V]].Sentence} (hφ : RankGE T o φ) : Nonempty (BinaryTree T V) := by
  obtain ⟨g, hP, hmono, hdisj⟩ :=
    exists_dyadic T.typesWith (fun χ => RankGE T o χ) ⟨φ, hφ⟩ (fun χ hχ => by
      obtain ⟨ψ, h1, h2, h3⟩ := rankGE_succ_iff.1 (hstab χ hχ)
      exact ⟨ψ 0, ψ 1, h1 0, h1 1, h2 0 1 (by decide), h3 0, h3 1⟩)
  exact ⟨⟨g, fun s => (hP s).nonempty, hmono, hdisj⟩⟩

/-- If there is no binary tree of formulas then every formula has *bounded* Morley rank. -/
theorem exists_not_rankGE_of_isEmpty_binaryTree {T : K.Theory} (h : IsEmpty (BinaryTree T V))
    (φ : K[[V]].Sentence) : ∃ o : Ordinal.{u}, ¬ RankGE T o φ := by
  obtain ⟨o, ho⟩ := exists_rankGE_stable (V := V) T
  exact ⟨o, fun hφ => h.elim' (exists_binaryTree_of_rankGE ho hφ).some⟩

/-! ### The Morley rank of a formula -/

/-- The **Morley rank** of a formula `φ` relative to a theory `T`: the largest ordinal `o` with
`RankGE T o φ`, when there is one.  If `φ` is inconsistent this is `0`, and if `φ` has unbounded
rank the definition returns the junk value `0` as well; both degenerate cases are excluded by the
hypotheses of the lemmas below. -/
noncomputable def MRank (T : K.Theory) (φ : K[[V]].Sentence) : Ordinal.{u} :=
  sInf {o : Ordinal.{u} | ¬ RankGE T (o + 1) φ}

theorem not_rankGE_mrank_succ {T : K.Theory} {φ : K[[V]].Sentence}
    (hb : ∃ o : Ordinal.{u}, ¬ RankGE T o φ) : ¬ RankGE T (MRank T φ + 1) φ := by
  obtain ⟨o, ho⟩ := hb
  exact csInf_mem (s := {o : Ordinal.{u} | ¬ RankGE T (o + 1) φ})
    ⟨o, fun h => ho (h.mono_ord (Order.le_succ o))⟩

theorem rankGE_mrank {T : K.Theory} {φ : K[[V]].Sentence} (hne : (T.typesWith φ).Nonempty) :
    RankGE T (MRank T φ) φ := by
  refine rankGE_of_forall_lt hne fun q hq => ?_
  by_contra hq'
  exact absurd (csInf_le' (s := {o : Ordinal.{u} | ¬ RankGE T (o + 1) φ}) hq') (not_le.2 hq)

theorem mrank_le_iff {T : K.Theory} {φ : K[[V]].Sentence} {o : Ordinal.{u}}
    (hb : ∃ o : Ordinal.{u}, ¬ RankGE T o φ) : MRank T φ ≤ o ↔ ¬ RankGE T (o + 1) φ := by
  refine ⟨fun h hr => not_rankGE_mrank_succ hb (hr.mono_ord (Order.succ_le_succ h)),
    fun h => csInf_le' h⟩

theorem le_mrank_iff {T : K.Theory} {φ : K[[V]].Sentence} {o : Ordinal.{u}}
    (hne : (T.typesWith φ).Nonempty) (hb : ∃ o : Ordinal.{u}, ¬ RankGE T o φ) :
    o ≤ MRank T φ ↔ RankGE T o φ :=
  ⟨fun h => (rankGE_mrank hne).mono_ord h, fun h => by
    by_contra hlt
    exact not_rankGE_mrank_succ hb
      (h.mono_ord (Order.succ_le_of_lt (not_le.1 hlt)))⟩

/-- Morley rank is monotone in the formula. -/
theorem mrank_mono {T : K.Theory} {φ φ' : K[[V]].Sentence}
    (hne : (T.typesWith φ).Nonempty) (hsub : T.typesWith φ ⊆ T.typesWith φ')
    (hb' : ∃ o : Ordinal.{u}, ¬ RankGE T o φ') :
    MRank T φ ≤ MRank T φ' :=
  (le_mrank_iff (hne.mono hsub) hb').2 ((rankGE_mrank hne).mono hsub)

end AbstractRank

/-! ### Rank of a binary split -/

section Split

variable {K : FirstOrder.Language.{u, u}} {V : Type u} {T : K.Theory}

theorem typesWith_eq_union_inf (φ ψ : K[[V]].Sentence) :
    T.typesWith φ = T.typesWith (φ ⊓ ψ) ∪ T.typesWith (φ ⊓ ∼ψ) := by
  rw [Theory.CompleteType.typesWith_inf, Theory.CompleteType.typesWith_inf,
    Theory.CompleteType.typesWith_not, ← Set.inter_union_distrib_left, Set.union_compl_self,
    Set.inter_univ]

/-- **The Morley rank of a formula is the maximum of the ranks of the two halves of any binary
split of it.**  One half of a split of a formula of rank at least `o` again has rank at least
`o`.

The proof is a transfinite induction: at a successor stage the infinitely many contradictory
pieces witnessing the rank are split individually, and infinitely many of them fall on the same
side. -/
theorem rankGE_inf_or_rankGE_inf_not (ψ : K[[V]].Sentence) (o : Ordinal.{u})
    (φ : K[[V]].Sentence) (hφ : RankGE T o φ) :
    RankGE T o (φ ⊓ ψ) ∨ RankGE T o (φ ⊓ ∼ψ) := by
  classical
  induction o using WellFoundedLT.induction generalizing φ with
  | _ o IH =>
    by_contra hcon
    push Not at hcon
    obtain ⟨h1, h2⟩ := hcon
    have hsplit := typesWith_eq_union_inf (T := T) φ ψ
    rcases Set.eq_empty_or_nonempty (T.typesWith (φ ⊓ ψ)) with he | hne1
    · exact h2 (hφ.mono (by rw [hsplit, he, Set.empty_union]))
    rcases Set.eq_empty_or_nonempty (T.typesWith (φ ⊓ ∼ψ)) with he | hne2
    · exact h1 (hφ.mono (by rw [hsplit, he, Set.union_empty]))
    obtain ⟨q₁, hq₁, hq₁'⟩ : ∃ q < o, ¬ RankGE T (q + 1) (φ ⊓ ψ) := by
      by_contra hc
      push Not at hc
      exact h1 (rankGE_of_forall_lt hne1 hc)
    obtain ⟨q₂, hq₂, hq₂'⟩ : ∃ q < o, ¬ RankGE T (q + 1) (φ ⊓ ∼ψ) := by
      by_contra hc
      push Not at hc
      exact h2 (rankGE_of_forall_lt hne2 hc)
    obtain ⟨θ, hθ1, hθ2, hθ3⟩ :=
      rankGE_succ_iff.1 (hφ.mono_ord (Order.succ_le_of_lt (max_lt hq₁ hq₂)))
    have hpiece : ∀ i, RankGE T (max q₁ q₂) (θ i ⊓ ψ) ∨ RankGE T (max q₁ q₂) (θ i ⊓ ∼ψ) :=
      fun i => IH _ (max_lt hq₁ hq₂) _ (hθ3 i)
    -- infinitely many pieces fall on the same side
    have key : ∀ (χ : K[[V]].Sentence) (S : Set ℕ), S.Infinite →
        (∀ i ∈ S, RankGE T (max q₁ q₂) (θ i ⊓ χ)) →
        RankGE T (max q₁ q₂ + 1) (φ ⊓ χ) := by
      intro χ S hS hSrank
      have hemb : ℕ ↪ (S : Set ℕ) := hS.natEmbedding
      refine rankGE_succ_iff.2 ⟨fun k => θ ((hemb k : (S : Set ℕ)) : ℕ) ⊓ χ, fun k => ?_,
        fun k l hkl => ?_, fun k => hSrank _ (hemb k).2⟩
      · rw [Theory.CompleteType.typesWith_inf, Theory.CompleteType.typesWith_inf]
        exact Set.inter_subset_inter_left _ (hθ1 _)
      · rw [Theory.CompleteType.typesWith_inf, Theory.CompleteType.typesWith_inf]
        refine Set.disjoint_of_subset Set.inter_subset_left Set.inter_subset_left
          (hθ2 _ _ fun hij => hkl (hemb.injective (Subtype.ext hij)))
    by_cases hfin : {i : ℕ | RankGE T (max q₁ q₂) (θ i ⊓ ψ)}.Finite
    · refine hq₂' ((key (∼ψ) {i : ℕ | RankGE T (max q₁ q₂) (θ i ⊓ ψ)}ᶜ hfin.infinite_compl
        fun i hi => (hpiece i).resolve_left hi).mono_ord ?_)
      exact Order.succ_le_succ (le_max_right q₁ q₂)
    · refine hq₁' ((key ψ {i : ℕ | RankGE T (max q₁ q₂) (θ i ⊓ ψ)} (Set.not_finite.1 hfin)
        fun _ hi => hi).mono_ord ?_)
      exact Order.succ_le_succ (le_max_left q₁ q₂)

/-! ### Morley degree -/

/-- `DegGE T o φ n` says that `φ` can be split into `n` pairwise contradictory formulas of Morley
rank at least `o`. -/
def DegGE (T : K.Theory) (o : Ordinal.{u}) (φ : K[[V]].Sentence) (n : ℕ) : Prop :=
  ∃ ψ : Fin n → K[[V]].Sentence, (∀ i, T.typesWith (ψ i) ⊆ T.typesWith φ) ∧
    (∀ i j, i ≠ j → Disjoint (T.typesWith (ψ i)) (T.typesWith (ψ j))) ∧
    (∀ i, RankGE T o (ψ i))

theorem DegGE.mono {o : Ordinal.{u}} {φ : K[[V]].Sentence} {m n : ℕ} (hmn : m ≤ n)
    (h : DegGE T o φ n) : DegGE T o φ m := by
  obtain ⟨ψ, h1, h2, h3⟩ := h
  refine ⟨fun i => ψ (Fin.castLE hmn i), fun i => h1 _, fun i j hij => h2 _ _ ?_, fun i => h3 _⟩
  exact fun h => hij (Fin.castLE_injective hmn h)

theorem degGE_one {o : Ordinal.{u}} {φ : K[[V]].Sentence} (h : RankGE T o φ) : DegGE T o φ 1 :=
  ⟨fun _ => φ, fun _ => le_rfl, fun i j hij => absurd (Subsingleton.elim i j) hij, fun _ => h⟩

/-- A formula which can be split into `n` pieces of rank at least `o` for **every** `n` has rank
at least `o + 1`.  This is the finiteness of the Morley degree.

The chain is built by repeatedly splitting off a piece: by
`Submission.Morley.rankGE_inf_or_rankGE_inf_not` one of the two halves of a split again admits
arbitrarily large families, and the discarded halves are pairwise contradictory. -/
theorem rankGE_succ_of_forall_degGE {o : Ordinal.{u}} {φ : K[[V]].Sentence}
    (hφ : RankGE T o φ) (h : ∀ n, DegGE T o φ n) : RankGE T (o + 1) φ := by
  classical
  -- a formula which admits arbitrarily large splittings splits off a piece and keeps the property
  have hstep : ∀ χ : K[[V]].Sentence, RankGE T o χ → (∀ n, DegGE T o χ n) →
      ∃ χ' π : K[[V]].Sentence, T.typesWith χ' ⊆ T.typesWith χ ∧
        T.typesWith π ⊆ T.typesWith χ ∧ Disjoint (T.typesWith π) (T.typesWith χ') ∧
        RankGE T o π ∧ RankGE T o χ' ∧ (∀ n, DegGE T o χ' n) := by
    intro χ hχ hunb
    obtain ⟨ψ, hψ1, hψ2, hψ3⟩ := hunb 2
    -- the two halves of the split by `ψ 0`
    have hleft : RankGE T o (χ ⊓ ψ 0) := (hψ3 0).mono (by
      rw [Theory.CompleteType.typesWith_inf]
      exact Set.subset_inter (hψ1 0) le_rfl)
    have hright : RankGE T o (χ ⊓ ∼(ψ 0)) := (hψ3 1).mono (by
      rw [Theory.CompleteType.typesWith_inf, Theory.CompleteType.typesWith_not]
      exact Set.subset_inter (hψ1 1) (Set.subset_compl_iff_disjoint_left.2
        (hψ2 0 1 (by decide))))
    have hdisj : Disjoint (T.typesWith (χ ⊓ ψ 0)) (T.typesWith (χ ⊓ ∼(ψ 0))) := by
      rw [Theory.CompleteType.typesWith_inf, Theory.CompleteType.typesWith_inf,
        Theory.CompleteType.typesWith_not]
      exact Set.disjoint_of_subset Set.inter_subset_right Set.inter_subset_right
        disjoint_compl_right
    have hsubl : T.typesWith (χ ⊓ ψ 0) ⊆ T.typesWith χ := by
      rw [Theory.CompleteType.typesWith_inf]; exact Set.inter_subset_left
    have hsubr : T.typesWith (χ ⊓ ∼(ψ 0)) ⊆ T.typesWith χ := by
      rw [Theory.CompleteType.typesWith_inf]; exact Set.inter_subset_left
    -- one of the halves still admits arbitrarily large splittings
    by_cases hcase : ∀ n, DegGE T o (χ ⊓ ψ 0) n
    · exact ⟨χ ⊓ ψ 0, χ ⊓ ∼(ψ 0), hsubl, hsubr, hdisj.symm, hright, hleft, hcase⟩
    push Not at hcase
    obtain ⟨N₁, hN₁⟩ := hcase
    refine ⟨χ ⊓ ∼(ψ 0), χ ⊓ ψ 0, hsubr, hsubl, hdisj, hleft, hright, fun n => ?_⟩
    by_contra hn
    -- otherwise both halves are bounded, and so is `χ`
    obtain ⟨θ, hθ1, hθ2, hθ3⟩ := hunb (N₁ + n + 1)
    set S : Finset (Fin (N₁ + n + 1)) :=
      {i | RankGE T o (θ i ⊓ ψ 0)} with hS
    have hmemS : ∀ i, i ∈ S ↔ RankGE T o (θ i ⊓ ψ 0) := by
      intro i; rw [hS]; simp
    -- the pieces landing in each half give splittings of that half
    have hsub : ∀ (χ₀ : K[[V]].Sentence) (t : Finset (Fin (N₁ + n + 1))),
        (∀ i ∈ t, RankGE T o (θ i ⊓ χ₀)) → DegGE T o (χ ⊓ χ₀) t.card := by
      intro χ₀ t ht
      refine ⟨fun k => θ (t.orderIsoOfFin rfl k) ⊓ χ₀, fun k => ?_, fun k l hkl => ?_,
        fun k => ht _ (t.orderIsoOfFin rfl k).2⟩
      · rw [Theory.CompleteType.typesWith_inf, Theory.CompleteType.typesWith_inf]
        exact Set.inter_subset_inter_left _ (hθ1 _)
      · rw [Theory.CompleteType.typesWith_inf, Theory.CompleteType.typesWith_inf]
        refine Set.disjoint_of_subset Set.inter_subset_left Set.inter_subset_left
          (hθ2 _ _ fun hij => hkl ?_)
        exact (t.orderIsoOfFin rfl).injective (Subtype.ext hij)
    have hcard1 : S.card ≤ N₁ := by
      by_contra hlt
      exact hN₁ ((hsub (ψ 0) S fun i hi => (hmemS i).1 hi).mono (not_le.1 hlt).le)
    have hcard2 : Sᶜ.card ≤ n := by
      by_contra hlt
      refine hn (((hsub (∼(ψ 0)) Sᶜ fun i hi => ?_).mono (not_le.1 hlt).le))
      exact (rankGE_inf_or_rankGE_inf_not (ψ 0) o (θ i) (hθ3 i)).resolve_left
        (fun hc => (Finset.mem_compl.1 hi) ((hmemS i).2 hc))
    have hcards : S.card + Sᶜ.card = N₁ + n + 1 := by
      rw [Finset.card_add_card_compl, Fintype.card_fin]
    omega
  -- iterate the splitting
  choose! F G hF1 hF2 hF3 hF4 hF5 hF6 using hstep
  set C : ℕ → K[[V]].Sentence := fun k => Nat.rec φ (fun _ ih => F ih) k with hC
  have hC0 : C 0 = φ := rfl
  have hCs : ∀ k, C (k + 1) = F (C k) := fun _ => rfl
  have hCok : ∀ k, RankGE T o (C k) ∧ (∀ n, DegGE T o (C k) n) := by
    intro k
    induction k with
    | zero => exact ⟨hφ, h⟩
    | succ k ih => exact ⟨hF5 _ ih.1 ih.2, hF6 _ ih.1 ih.2⟩
  have hCsub : ∀ k, T.typesWith (C (k + 1)) ⊆ T.typesWith (C k) := fun k =>
    hF1 _ (hCok k).1 (hCok k).2
  have hCmono : ∀ k l, k ≤ l → T.typesWith (C l) ⊆ T.typesWith (C k) := by
    intro k l hkl
    induction l with
    | zero => rw [Nat.le_zero.1 hkl]
    | succ l ih =>
      rcases Nat.lt_or_ge k (l + 1) with hlt | hge
      · exact (hCsub l).trans (ih (Nat.lt_succ_iff.1 hlt))
      · rw [Nat.le_antisymm hkl hge]
  refine rankGE_succ_iff.2 ⟨fun k => G (C k), fun k => ?_, fun k l hkl => ?_,
    fun k => hF4 _ (hCok k).1 (hCok k).2⟩
  · exact ((hF2 _ (hCok k).1 (hCok k).2).trans (hCmono 0 k (Nat.zero_le k))).trans_eq (by rw [hC0])
  · have hgen : ∀ k l : ℕ, k < l →
        Disjoint (T.typesWith (G (C k))) (T.typesWith (G (C l))) := by
      intro k l hkl
      refine Set.disjoint_of_subset le_rfl
        (((hF2 _ (hCok l).1 (hCok l).2).trans (hCmono (k + 1) l hkl)).trans_eq rfl) ?_
      exact hF3 _ (hCok k).1 (hCok k).2
    rcases Nat.lt_or_ge k l with hlt | hge
    · exact hgen k l hlt
    · exact (hgen l k (lt_of_le_of_ne hge (Ne.symm hkl))).symm

theorem degGE_zero {o : Ordinal.{u}} {φ : K[[V]].Sentence} : DegGE T o φ 0 :=
  ⟨Fin.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩

/-- The **Morley degree** of a formula: the largest number of pairwise contradictory formulas of
the same Morley rank into which it can be split. -/
noncomputable def MDegree (T : K.Theory) (φ : K[[V]].Sentence) : ℕ :=
  sInf {n : ℕ | ¬ DegGE T (MRank T φ) φ (n + 1)}

/-- **The Morley degree is finite.** -/
theorem exists_not_degGE {φ : K[[V]].Sentence} (hne : (T.typesWith φ).Nonempty)
    (hb : ∃ o : Ordinal.{u}, ¬ RankGE T o φ) : ∃ n : ℕ, ¬ DegGE T (MRank T φ) φ n := by
  by_contra hc
  push Not at hc
  exact not_rankGE_mrank_succ hb (rankGE_succ_of_forall_degGE (rankGE_mrank hne) hc)

theorem not_degGE_mdegree_succ {φ : K[[V]].Sentence} (hne : (T.typesWith φ).Nonempty)
    (hb : ∃ o : Ordinal.{u}, ¬ RankGE T o φ) :
    ¬ DegGE T (MRank T φ) φ (MDegree T φ + 1) := by
  obtain ⟨n, hn⟩ := exists_not_degGE hne hb
  exact Nat.sInf_mem (s := {n : ℕ | ¬ DegGE T (MRank T φ) φ (n + 1)})
    ⟨n, fun h => hn (h.mono (Nat.le_succ n))⟩

theorem degGE_mdegree {φ : K[[V]].Sentence} : DegGE T (MRank T φ) φ (MDegree T φ) := by
  rcases Nat.eq_zero_or_pos (MDegree T φ) with h0 | hpos
  · rw [h0]; exact degGE_zero
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
  rw [hm]
  by_contra hc
  have hlt : m < MDegree T φ := by rw [hm]; exact Nat.lt_succ_self m
  exact absurd (Nat.sInf_le (s := {n : ℕ | ¬ DegGE T (MRank T φ) φ (n + 1)}) hc) (not_le.2 hlt)

/-- A consistent formula has Morley degree at least one. -/
theorem one_le_mdegree {φ : K[[V]].Sentence} (hne : (T.typesWith φ).Nonempty)
    (hb : ∃ o : Ordinal.{u}, ¬ RankGE T o φ) : 1 ≤ MDegree T φ := by
  by_contra hc
  rw [not_le, Nat.lt_one_iff] at hc
  exact not_degGE_mdegree_succ hne hb (by rw [hc]; exact degGE_one (rankGE_mrank hne))

end Split

/-! ## Formulas and the sets they define

From now on we work inside a fixed structure `M` and identify a formula with parameters in
`A ⊆ M` with the subset of `M` it defines. -/

section RealSet

variable {L : FirstOrder.Language.{0, 0}} {M : Type} [L.Structure M] [Nonempty M]

/-- The set of elements of `M` satisfying a formula with parameters in `A ⊆ M`. -/
def realSet (A : Set M) (φ : Form1 L A) : Set M := {a : M | φ ∈ typeOfElem A a}

theorem mem_realSet {A : Set M} {φ : Form1 L A} {a : M} :
    a ∈ realSet A φ ↔ φ ∈ typeOfElem A a := Iff.rfl

@[simp] theorem realSet_inf {A : Set M} (φ ψ : Form1 L A) :
    realSet A (φ ⊓ ψ) = realSet A φ ∩ realSet A ψ := by
  ext a
  simp only [mem_realSet, Set.mem_inter_iff]
  exact Theory.CompleteType.inf_mem_iff _ _ _

@[simp] theorem realSet_not {A : Set M} (φ : Form1 L A) :
    realSet A (∼φ) = (realSet A φ)ᶜ := by
  ext a
  simp only [mem_realSet, Set.mem_compl_iff]
  exact Theory.CompleteType.not_mem_iff _ _

@[simp] theorem realSet_top {A : Set M} : realSet A (⊤ : Form1 L A) = Set.univ := by
  ext a
  simp only [mem_realSet, Set.mem_univ, iff_true]
  exact (Theory.CompleteType.mem_typesWith_iff (⊤ : Form1 L A) (typeOfElem A a)).1
    (by rw [Theory.CompleteType.typesWith_top]; trivial)

/-- Consistency of a formula with parameters in `A` is exactly nonemptiness of the set it
defines in `M`; the point is that `Th(M_A)` is the theory of `M` itself. -/
theorem nonempty_typesWith_iff_realSet {A : Set M} (φ : Form1 L A) :
    ((paramTheory L A).typesWith φ).Nonempty ↔ (realSet A φ).Nonempty := by
  rw [typesWith_nonempty_iff_exists_realize L A φ]
  constructor
  · rintro ⟨v, hv⟩
    refine ⟨v 0, ?_⟩
    rw [mem_realSet, mem_typeOfElem]
    have hv0 : (fun _ : Fin 1 => v 0) = v := funext fun i => by
      rw [Subsingleton.elim i (0 : Fin 1)]
    rw [hv0]
    exact hv
  · rintro ⟨a, ha⟩
    exact ⟨fun _ => a, mem_typeOfElem.1 ha⟩

theorem typesWith_subset_iff_realSet {A : Set M} (φ ψ : Form1 L A) :
    (paramTheory L A).typesWith φ ⊆ (paramTheory L A).typesWith ψ ↔
      realSet A φ ⊆ realSet A ψ := by
  rw [typesWith_subset_iff_not_nonempty, nonempty_typesWith_iff_realSet, realSet_inf, realSet_not,
    ← Set.sdiff_eq, Set.not_nonempty_iff_eq_empty, Set.sdiff_eq_empty]

theorem typesWith_disjoint_iff_realSet {A : Set M} (φ ψ : Form1 L A) :
    Disjoint ((paramTheory L A).typesWith φ) ((paramTheory L A).typesWith ψ) ↔
      Disjoint (realSet A φ) (realSet A ψ) := by
  rw [typesWith_disjoint_iff_not_nonempty, nonempty_typesWith_iff_realSet, realSet_inf,
    Set.not_nonempty_iff_eq_empty, Set.disjoint_iff_inter_eq_empty]

/-- The set defined by a formula with parameters in `A` is definable over `A`. -/
theorem definable₁_realSet (A : Set M) (φ : Form1 L A) : A.Definable₁ L (realSet A φ) := by
  refine ⟨Formula.equivSentence.symm φ, ?_⟩
  ext x
  have hx : (fun _ : Fin 1 => x 0) = x := funext fun i => by
    rw [Subsingleton.elim i (0 : Fin 1)]
  simp only [Set.mem_setOf_eq, mem_realSet, mem_typeOfElem, hx]

/-- Conversely, every set definable over `B` is defined by a formula with parameters in `B`. -/
theorem exists_realSet_eq_of_definable₁ (B : Set M) {X : Set M} (h : B.Definable₁ L X) :
    ∃ φ : Form1 L B, realSet B φ = X := by
  obtain ⟨ψ, hψ⟩ := h
  refine ⟨Formula.equivSentence ψ, ?_⟩
  ext a
  rw [mem_realSet, mem_typeOfElem, Equiv.symm_apply_apply]
  exact (Set.ext_iff.1 hψ fun _ => a).symm

/-- Every formula with parameters in `A ⊆ M` defines the same set as some formula with parameters
in all of `M`.  This is what lets Morley rank be computed with parameters from the whole model,
which is what makes rank `0` mean *finite*. -/
theorem exists_realSet_univ_eq {A : Set M} (φ : Form1 L A) :
    ∃ φ' : Form1 L (Set.univ : Set M), realSet Set.univ φ' = realSet A φ :=
  exists_realSet_eq_of_definable₁ _ ((definable₁_realSet A φ).mono (Set.subset_univ A))

/-- A formula with parameters in `A ⊆ M`, viewed as a formula with parameters in all of `M`. -/
noncomputable def up {A : Set M} (φ : Form1 L A) : Form1 L (Set.univ : Set M) :=
  (exists_realSet_univ_eq φ).choose

@[simp] theorem realSet_up {A : Set M} (φ : Form1 L A) :
    realSet Set.univ (up φ) = realSet A φ :=
  (exists_realSet_univ_eq φ).choose_spec

end RealSet

/-! ## Morley rank inside a model

The Morley rank of a formula is computed with parameters from the *whole* model.  This is what
makes rank `0` mean "finitely many realisations": a formula with parameters in a small set `A` can
be split by formulas naming arbitrary elements of `M`. -/

section UnivRank

variable {L : FirstOrder.Language.{0, 0}} {M : Type} [L.Structure M] [Nonempty M]

/-- Morley rank only depends on the set a formula defines. -/
theorem rankGE_congr {o : Ordinal.{0}} {φ ψ : Form1 L (Set.univ : Set M)}
    (h : realSet Set.univ φ = realSet Set.univ ψ) :
    RankGE (paramTheory L (Set.univ : Set M)) o φ ↔
      RankGE (paramTheory L (Set.univ : Set M)) o ψ :=
  ⟨fun hr => hr.mono ((typesWith_subset_iff_realSet _ _).2 h.subset),
    fun hr => hr.mono ((typesWith_subset_iff_realSet _ _).2 h.symm.subset)⟩

theorem mrank_congr {φ ψ : Form1 L (Set.univ : Set M)}
    (h : realSet Set.univ φ = realSet Set.univ ψ) :
    MRank (paramTheory L (Set.univ : Set M)) φ = MRank (paramTheory L (Set.univ : Set M)) ψ := by
  unfold MRank
  exact congrArg _ (Set.ext fun o => not_congr (rankGE_congr h))

theorem rankGE_zero_iff_nonempty (φ : Form1 L (Set.univ : Set M)) :
    RankGE (paramTheory L (Set.univ : Set M)) 0 φ ↔ (realSet Set.univ φ).Nonempty := by
  rw [rankGE_zero_iff, nonempty_typesWith_iff_realSet]

/-- **Morley rank at least one means infinitely many realisations.**  Since parameters from the
whole model are allowed, a formula with infinitely many realisations is split by the formulas
naming those realisations. -/
theorem rankGE_one_iff_infinite (φ : Form1 L (Set.univ : Set M)) :
    RankGE (paramTheory L (Set.univ : Set M)) 1 φ ↔ (realSet Set.univ φ).Infinite := by
  classical
  rw [show (1 : Ordinal.{0}) = 0 + 1 from (zero_add 1).symm, rankGE_succ_iff]
  constructor
  · rintro ⟨ψ, h1, h2, h3⟩
    choose a ha using fun i =>
      (nonempty_typesWith_iff_realSet (ψ i)).1 (rankGE_zero_iff.1 (h3 i))
    have hdisj : ∀ i j, i ≠ j → Disjoint (realSet Set.univ (ψ i)) (realSet Set.univ (ψ j)) :=
      fun i j hij => (typesWith_disjoint_iff_realSet _ _).1 (h2 i j hij)
    refine Set.infinite_of_injective_forall_mem (f := a) (fun i j hij => ?_) fun i => ?_
    · by_contra hne
      exact Set.disjoint_left.1 (hdisj i j hne) (ha i) (hij ▸ ha j)
    · exact (typesWith_subset_iff_realSet _ _).1 (h1 i) (ha i)
  · intro hinf
    have hemb : ℕ ↪ (realSet Set.univ φ : Set M) := hinf.natEmbedding
    set a : ℕ → M := fun i => ((hemb i : (realSet Set.univ φ : Set M)) : M) with hadef
    have hainj : Function.Injective a := fun i j hij =>
      hemb.injective (Subtype.ext hij)
    have hamem : ∀ i, a i ∈ realSet Set.univ φ := fun i => (hemb i).2
    have hsing : ∀ i, ∃ χ : Form1 L (Set.univ : Set M),
        realSet Set.univ χ = {a i} := fun i =>
      exists_realSet_eq_of_definable₁ _ (Set.Definable.singleton_of_mem L (Set.mem_univ (a i)))
    choose χ hχ using hsing
    refine ⟨χ, fun i => ?_, fun i j hij => ?_, fun i => ?_⟩
    · rw [typesWith_subset_iff_realSet, hχ i, Set.singleton_subset_iff]
      exact hamem i
    · rw [typesWith_disjoint_iff_realSet, hχ i, hχ j, Set.disjoint_singleton]
      exact fun h => hij (hainj h)
    · rw [rankGE_zero_iff, nonempty_typesWith_iff_realSet, hχ i]
      exact Set.singleton_nonempty _

/-- A formula of Morley rank `0` has only finitely many realisations. -/
theorem finite_realSet_of_not_rankGE_one {φ : Form1 L (Set.univ : Set M)}
    (h : ¬ RankGE (paramTheory L (Set.univ : Set M)) 1 φ) : (realSet Set.univ φ).Finite := by
  rw [rankGE_one_iff_infinite] at h
  exact Set.not_infinite.1 h

/-- **A minimal structure has Morley rank at most one.**  If every parameter-definable subset of
`M` is finite or cofinite then the formula `x = x` has Morley rank at most `1`: two disjoint
infinite definable sets cannot both be cofinite. -/
theorem mrank_top_le_one_of_forall_finite_or_compl_finite
    (h : ∀ φ : Form1 L (Set.univ : Set M),
      (realSet Set.univ φ).Finite ∨ (realSet Set.univ φ)ᶜ.Finite) :
    MRank (paramTheory L (Set.univ : Set M)) (⊤ : Form1 L (Set.univ : Set M)) ≤ 1 := by
  refine csInf_le' (a := (1 : Ordinal.{0})) ?_
  intro hr
  obtain ⟨ψ, -, hdisj, hrank⟩ := rankGE_succ_iff.1 hr
  have hinf : ∀ i, (realSet Set.univ (ψ i)).Infinite := fun i =>
    (rankGE_one_iff_infinite (ψ i)).1 (hrank i)
  have hcof : (realSet Set.univ (ψ 0))ᶜ.Finite := (h (ψ 0)).resolve_left (hinf 0).not_finite
  refine (hinf 1).not_finite (hcof.subset ?_)
  exact Set.subset_compl_iff_disjoint_left.2
    ((typesWith_disjoint_iff_realSet _ _).1 (hdisj 0 1 (by decide)))

end UnivRank

/-! ## ω-stability makes Morley rank ordinal-valued -/

section OmegaStableRank

variable {L : FirstOrder.Language.{0, 0}} {T : L.Theory}

/-- An ω-stable theory admits no binary tree of formulas over any parameter set: a binary tree
descends to a countable parameter set (`Submission.Morley.exists_countable_binaryTree`), where it
contradicts ω-stability. -/
theorem isEmpty_binaryTree_of_omegaStable (hos : OmegaStable.{0, 0, 0} T)
    (M : T.ModelType.{0, 0, 0}) (A : Set M) :
    IsEmpty (BinaryTree (paramTheory L A) (Fin 1)) := by
  refine ⟨fun t => ?_⟩
  obtain ⟨A₀, -, hcount, ⟨t₀⟩⟩ := exists_countable_binaryTree t
  exact not_omegaStable_of_binaryTree M A₀
    (Cardinal.mk_le_aleph0_iff.2 (Set.countable_coe_iff.2 hcount)) t₀ hos

/-- **Every formula has an ordinal Morley rank in an ω-stable theory.**  This is the first place
where ω-stability is used: unbounded rank produces a binary tree of formulas. -/
theorem exists_not_rankGE_of_omegaStable (hos : OmegaStable.{0, 0, 0} T)
    (M : T.ModelType.{0, 0, 0}) (A : Set M) (φ : Form1 L A) :
    ∃ o : Ordinal.{0}, ¬ RankGE (paramTheory L A) o φ :=
  exists_not_rankGE_of_isEmpty_binaryTree (isEmpty_binaryTree_of_omegaStable hos M A) φ

end OmegaStableRank

/-! ## The Morley rank of a type -/

section TypeRank

variable {L : FirstOrder.Language.{0, 0}} {T : L.Theory}

theorem top_mem_completeType {K : FirstOrder.Language.{u, u}} {S : K.Theory} {V : Type u}
    (p : S.CompleteType V) : (⊤ : K[[V]].Sentence) ∈ p :=
  (Theory.CompleteType.mem_typesWith_iff ⊤ p).1
    (by rw [Theory.CompleteType.typesWith_top]; trivial)

/-- The **Morley rank of a complete `1`-type** over a parameter set `A ⊆ M`: the least Morley rank
of a formula belonging to it. -/
noncomputable def typeRank {M : T.ModelType.{0, 0, 0}} {A : Set M} (p : S₁ L A) : Ordinal.{0} :=
  sInf ((fun ψ : Form1 L A => MRank (paramTheory L (Set.univ : Set M)) (up ψ)) ''
    (p : Set (Form1 L A)))

theorem typeRank_le {M : T.ModelType.{0, 0, 0}} {A : Set M} {p : S₁ L A} {ψ : Form1 L A}
    (hψ : ψ ∈ p) : typeRank p ≤ MRank (paramTheory L (Set.univ : Set M)) (up ψ) :=
  csInf_le' ⟨ψ, hψ, rfl⟩

/-- **A formula of least Morley rank in a type exists.** -/
theorem exists_mem_mrank_eq_typeRank {M : T.ModelType.{0, 0, 0}} {A : Set M} (p : S₁ L A) :
    ∃ ψ : Form1 L A, ψ ∈ p ∧ MRank (paramTheory L (Set.univ : Set M)) (up ψ) = typeRank p := by
  have hne : ((fun ψ : Form1 L A => MRank (paramTheory L (Set.univ : Set M)) (up ψ)) ''
      (p : Set (Form1 L A))).Nonempty := ⟨_, ⟨⊤, top_mem_completeType p, rfl⟩⟩
  obtain ⟨ψ, hψ, hmem⟩ := csInf_mem hne
  exact ⟨ψ, hψ, hmem⟩

/-- **A formula of least rank and least degree in a type.**

If `p` is a complete `1`-type over `A ⊆ M` and `T` is ω-stable, then `p` contains a formula `φ`
which cannot be cut down inside `p` without dropping the rank: for every `ψ ∈ p` the difference
`φ ∧ ¬ψ` has Morley rank *strictly smaller* than the rank of `p`.

This is the classical "least rank, then least degree" choice; here the degree is avoided by a
direct descent: a failure produces an infinite decreasing chain inside `p` whose successive
differences are pairwise contradictory formulas of rank `RM(p)`, which would make the rank of the
first formula at least `RM(p) + 1`. -/
theorem exists_mem_forall_not_rankGE_typeRank (hos : OmegaStable.{0, 0, 0} T)
    (M : T.ModelType.{0, 0, 0}) (A : Set M) (p : S₁ L A) :
    ∃ φ : Form1 L A, φ ∈ p ∧ ∀ ψ ∈ p,
      ¬ RankGE (paramTheory L (Set.univ : Set M)) (typeRank p) (up φ ⊓ ∼(up ψ)) := by
  classical
  by_contra hcon
  push Not at hcon
  -- make the choice of a cutting-down formula total
  have hcon' : ∀ φ : Form1 L A, ∃ ψ : Form1 L A, φ ∈ p →
      (ψ ∈ p ∧ RankGE (paramTheory L (Set.univ : Set M)) (typeRank p) (up φ ⊓ ∼(up ψ))) := by
    intro φ
    by_cases hφ : φ ∈ p
    · obtain ⟨ψ, hψ1, hψ2⟩ := hcon φ hφ
      exact ⟨ψ, fun _ => ⟨hψ1, hψ2⟩⟩
    · exact ⟨⊤, fun h => absurd h hφ⟩
  choose g hg using hcon'
  obtain ⟨φ₀, hφ₀p, hφ₀r⟩ := exists_mem_mrank_eq_typeRank p
  -- the decreasing chain inside `p`
  set F : ℕ → Form1 L A := fun k => Nat.rec φ₀ (fun _ ih => ih ⊓ g ih) k with hFdef
  have hF0 : F 0 = φ₀ := rfl
  have hFs : ∀ k, F (k + 1) = F k ⊓ g (F k) := fun _ => rfl
  have hFp : ∀ k, F k ∈ p := by
    intro k
    induction k with
    | zero => exact hF0 ▸ hφ₀p
    | succ k ih =>
      rw [hFs k]
      exact (Theory.CompleteType.inf_mem_iff _ _ _).2 ⟨ih, (hg (F k) ih).1⟩
  have hFsub : ∀ k, realSet A (F (k + 1)) ⊆ realSet A (F k) := by
    intro k
    rw [hFs k, realSet_inf]
    exact Set.inter_subset_left
  have hFmono : ∀ k l, k ≤ l → realSet A (F l) ⊆ realSet A (F k) := by
    intro k l hkl
    induction l with
    | zero => rw [Nat.le_zero.1 hkl]
    | succ l ih =>
      rcases Nat.lt_or_ge k (l + 1) with h | h
      · exact (hFsub l).trans (ih (Nat.lt_succ_iff.1 h))
      · rw [Nat.le_antisymm hkl h]
  -- the pairwise contradictory pieces of rank `typeRank p`
  set π : ℕ → Form1 L (Set.univ : Set M) := fun k => up (F k) ⊓ ∼(up (g (F k))) with hπdef
  have hπreal : ∀ k, realSet Set.univ (π k) = realSet A (F k) \ realSet A (g (F k)) := by
    intro k
    rw [hπdef]
    simp only [realSet_inf, realSet_not, realSet_up, Set.sdiff_eq]
  have hπrank : ∀ k, RankGE (paramTheory L (Set.univ : Set M)) (typeRank p) (π k) := fun k =>
    (hg (F k) (hFp k)).2
  have hπsub : ∀ k, realSet Set.univ (π k) ⊆ realSet Set.univ (up φ₀) := by
    intro k
    rw [hπreal k, realSet_up, ← hF0]
    exact (Set.sdiff_subset).trans (hFmono 0 k (Nat.zero_le k))
  have hπdisj : ∀ k l, k < l → Disjoint (realSet Set.univ (π k)) (realSet Set.univ (π l)) := by
    intro k l hkl
    rw [Set.disjoint_left]
    intro x hx hx'
    rw [hπreal k] at hx
    rw [hπreal l] at hx'
    refine hx.2 ?_
    have : realSet A (F l) ⊆ realSet A (g (F k)) := by
      refine (hFmono (k + 1) l hkl).trans ?_
      rw [hFs k, realSet_inf]
      exact Set.inter_subset_right
    exact this hx'.1
  -- hence the least-rank formula has rank at least `typeRank p + 1`
  refine not_rankGE_mrank_succ (exists_not_rankGE_of_omegaStable hos M Set.univ (up φ₀)) ?_
  rw [hφ₀r]
  refine rankGE_succ_iff.2 ⟨π, fun k => ?_, fun k l hkl => ?_, hπrank⟩
  · exact (typesWith_subset_iff_realSet _ _).2 (hπsub k)
  · rcases Nat.lt_or_ge k l with h | h
    · exact (typesWith_disjoint_iff_realSet _ _).2 (hπdisj k l h)
    · exact ((typesWith_disjoint_iff_realSet _ _).2
        (hπdisj l k (lt_of_le_of_ne h (Ne.symm hkl)))).symm

end TypeRank

/-! ## Rank and saturation -/

section Saturation

variable {L : FirstOrder.Language.{0, 0}} {T : L.Theory}

/-- In a definably full model an infinite parameter-definable set has full cardinality. -/
theorem mk_realSet_eq (M : T.ModelType.{0, 0, 0}) (hfull : L.DefinablyFull (M : Type))
    (A : Set M) (φ : Form1 L A) (hinf : (realSet A φ).Infinite) : #(realSet A φ) = #M := by
  have h := hfull A (n := 1) {x : Fin 1 → M | x 0 ∈ realSet A φ}
    (definable₁_realSet A φ) (infinite_finOneSet hinf)
  rwa [mk_finOneSet] at h

/-- If a complete `1`-type over `A` is omitted then every element of `M` is separated from it by
one of its formulas. -/
theorem exists_mem_notMem_realSet {M : T.ModelType.{0, 0, 0}} {A : Set M} {p : S₁ L A}
    (hp : p ∉ (paramTheory L A).realizedTypes M (Fin 1)) (a : M) :
    ∃ ψ : Form1 L A, ψ ∈ p ∧ a ∉ realSet A ψ := by
  by_contra hcon
  push Not at hcon
  exact hp (mem_realizedTypes_one_iff.2
    ⟨a, (Theory.CompleteType.eq_of_le (p := p) (q := typeOfElem A a)
      fun ψ hψ => hcon ψ hψ).symm⟩)

/-- **Types of Morley rank at most one are realised.**

Let `T` be ω-stable in a countable language, let `M` be a definably full model of uncountable
cardinality and let `A ⊆ M` be a parameter set of size `< #M`.  Then every complete `1`-type over
`A` of Morley rank at most `1` is realised in `M`.

This is the rank-theoretic core of the saturation principle.  A formula `φ` of least rank in `p`
which cannot be cut down inside `p` without dropping the rank
(`Submission.Morley.exists_mem_forall_not_rankGE_typeRank`) has all its "wrong" pieces
`φ ∧ ¬ψ`, `ψ ∈ p`, of rank `0`, hence *finite*; if `p` were omitted these `≤ #A + ℵ₀` finite sets
would cover `φ(M)`, which has cardinality `#M` by definable fullness. -/
theorem mem_realizedTypes_of_typeRank_le_one (hL : L.card ≤ ℵ₀) (hos : OmegaStable.{0, 0, 0} T)
    (M : T.ModelType.{0, 0, 0}) (hfull : L.DefinablyFull (M : Type)) (hM : ℵ₀ < #M)
    (A : Set M) (hA : #A < #M) (p : S₁ L A) (hp1 : typeRank p ≤ 1) :
    p ∈ (paramTheory L A).realizedTypes M (Fin 1) := by
  classical
  by_contra hp
  obtain ⟨φ, hφp, hφ⟩ := exists_mem_forall_not_rankGE_typeRank hos M A p
  -- every piece cut off by a formula of `p` is finite, because it has Morley rank `0`
  have hfin : ∀ ψ : Form1 L A, ψ ∈ p → (realSet A φ \ realSet A ψ).Finite := by
    intro ψ hψ
    have h1 : ¬ RankGE (paramTheory L (Set.univ : Set M)) 1 (up φ ⊓ ∼(up ψ)) := fun h =>
      hφ ψ hψ (h.mono_ord hp1)
    have h2 := finite_realSet_of_not_rankGE_one h1
    rwa [realSet_inf, realSet_not, realSet_up, realSet_up, ← Set.sdiff_eq] at h2
  -- an omitted type makes these pieces cover `φ(M)`
  have hcov : realSet A φ ⊆
      ⋃ ψ : (p : Set (Form1 L A)), (realSet A φ \ realSet A (ψ : Form1 L A)) := by
    intro a ha
    obtain ⟨ψ, hψp, hψa⟩ := exists_mem_notMem_realSet hp a
    exact Set.mem_iUnion.2 ⟨⟨ψ, hψp⟩, ha, hψa⟩
  -- so `φ(M)` is small
  have hcard : #(realSet A φ) ≤ #A + ℵ₀ := by
    refine (Cardinal.mk_le_mk_of_subset hcov).trans ?_
    refine Cardinal.mk_iUnion_le_sum_mk.trans ?_
    refine (Cardinal.sum_le_sum _ (fun _ => ℵ₀) fun ψ => ?_).trans ?_
    · exact (Cardinal.lt_aleph0_iff_set_finite.2 (hfin ψ.1 ψ.2)).le
    · rw [Cardinal.sum_const']
      have hform : #(p : Set (Form1 L A)) ≤ #A + ℵ₀ := by
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
  -- but definable fullness makes it big
  have hinf : (realSet A φ).Infinite := infinite_setOf_mem_typeOfElem hp hφp
  rw [mk_realSet_eq M hfull A φ hinf] at hcard
  exact absurd hcard (not_le.2 (Cardinal.add_lt_of_lt hM.le hA hM))

/-- The Morley rank of a type is at most the Morley rank of the model. -/
theorem typeRank_le_mrank_top {M : T.ModelType.{0, 0, 0}} {A : Set M} (p : S₁ L A) :
    typeRank p ≤ MRank (paramTheory L (Set.univ : Set M)) (⊤ : Form1 L (Set.univ : Set M)) := by
  refine (typeRank_le (top_mem_completeType p)).trans (le_of_eq ?_)
  refine mrank_congr ?_
  rw [realSet_up, realSet_top, realSet_top]

/-- **The saturation principle for models of Morley rank one.**

If `T` is ω-stable in a countable language and the formula `x = x` has Morley rank at most `1` in
`M` — i.e. every parameter-definable subset of `M` is finite or cofinite, so that `T` is
*strongly minimal* — then every definably full model of uncountable cardinality is saturated.

By `Submission.Morley.definablyFull_of_not_hasVaughtianPair` the definable fullness hypothesis is
supplied by the absence of Vaughtian pairs, so this is the `RM = 1` case of
`Submission.Morley.SaturationPrinciple`. -/
theorem isSaturated_of_mrank_top_le_one (hL : L.card ≤ ℵ₀) (hos : OmegaStable.{0, 0, 0} T)
    (M : T.ModelType.{0, 0, 0}) (hfull : L.DefinablyFull (M : Type)) (hM : ℵ₀ < #M)
    (h1 : MRank (paramTheory L (Set.univ : Set M)) (⊤ : Form1 L (Set.univ : Set M)) ≤ 1) :
    IsSaturated M := fun A hA p =>
  mem_realizedTypes_of_typeRank_le_one hL hos M hfull hM A hA p
    ((typeRank_le_mrank_top p).trans h1)

/-- **The saturation principle for theories of Morley rank one**, in the shape of
`Submission.Morley.SaturationPrinciple`: an ω-stable theory without Vaughtian pairs whose models
have Morley rank one has all its uncountable models saturated.

The absence of Vaughtian pairs is consumed exactly as in the general statement, through
`Submission.Morley.definablyFull_of_not_hasVaughtianPair`. -/
theorem isSaturated_of_not_hasVaughtianPair_of_mrank_top_le_one (hL : L.card ≤ ℵ₀)
    (hos : IsOmegaStable.{0, 0, 0} T) (hvp : ¬HasVaughtianPair T) (M : T.ModelType.{0, 0, 0})
    (hM : ℵ₀ < #M)
    (h1 : MRank (paramTheory L (Set.univ : Set M)) (⊤ : Form1 L (Set.univ : Set M)) ≤ 1) :
    IsSaturated M :=
  isSaturated_of_mrank_top_le_one hL hos.omegaStable M
    (definablyFull_of_not_hasVaughtianPair hL hvp M) hM h1

/-- **Morley's categoricity theorem in Morley rank one.**

A complete theory with only infinite models, in a countable language, which is ω-stable, has no
Vaughtian pairs, and all of whose models have Morley rank one (equivalently, is strongly minimal),
is categorical in every uncountable cardinal.

This is `Submission.Morley.morley_categoricity_of_not_hasVaughtianPair` with its hypothesis
`Submission.Morley.SaturationPrinciple` discharged, in Morley rank one. -/
theorem categorical_of_mrank_top_le_one (hL : L.card ≤ ℵ₀) (hT : T.IsComplete)
    (hInf : ∀ M : T.ModelType.{0, 0, 0}, Infinite M) (hos : IsOmegaStable.{0, 0, 0} T)
    (hvp : ¬HasVaughtianPair T)
    (h1 : ∀ M : T.ModelType.{0, 0, 0},
      MRank (paramTheory L (Set.univ : Set M)) (⊤ : Form1 L (Set.univ : Set M)) ≤ 1)
    {μ : Cardinal.{0}} (hμ : ℵ₀ < μ) : μ.Categorical T :=
  categorical_of_forall_isSaturated hT hInf fun M hM =>
    isSaturated_of_not_hasVaughtianPair_of_mrank_top_le_one hL hos hvp M
      (by rw [hM]; exact hμ) (h1 M)

end Saturation

end Submission.Morley
