import Submission.Ado.PBW.Pow

/-!
# Words in the central `p`-polynomials do not depend on their order

`Submission/Ado/PBW/Pow.lean` builds the operators `Cⱼ` and their word products
`bigCword l` without assuming anything about the coefficients, so in particular
without assuming that the underlying elements `cⱼ` of `U(L)` are central. This
file adds the consequences of centrality, which is what
`Submission.Ado.central_pPolynomial` supplies in the intended application:

* a word product depends only on the multiset of its letters
  (`cWord_of_perm`, `bigCword_of_perm`);
* hence `bigCword l = C^(wordWeight l)` (`bigCword_eq_bigCpow`);
* hence the multi-index powers compose additively
  (`bigCpow_add`, `bigC_mul_bigCpow`).

The last one is what the characteristic-`p` argument needs: applying `Cⱼ` to
`C^m` lands in `C^(m + eⱼ)`, so the span of the `m ≠ 0` part of the restricted
basis absorbs every `Cⱼ`.
-/

universe u

namespace Submission.Ado.PBW

open UniversalEnvelopingAlgebra

variable {K : Type u} [Field K] {L : Type u} [LieRing L] [LieAlgebra K L] {n : ℕ}
variable (bas : Module.Basis (Fin n) K L) (q : ℕ) (mu : Fin n → ℕ → K)

/-- Centrality of the `p`-polynomials, as a hypothesis. In the application this is
supplied by `Submission.Ado.central_pPolynomial`. -/
def CentralElts : Prop :=
  ∀ (j : Fin n) (u : UniversalEnvelopingAlgebra K L),
    cElt bas q mu j * u = u * cElt bas q mu j

/-! ### The weight of a word counts its letters -/

/-- The `j`-th coordinate of the weight of a word is the number of `j`s in it. -/
theorem wordWeight_apply (l : List (Fin n)) (j : Fin n) :
    wordWeight l j = l.count j := by
  induction l with
  | nil => simp [wordWeight]
  | cons k l ih =>
      rw [wordWeight_cons, Finsupp.add_apply, ih, List.count_cons]
      by_cases h : k = j
      · subst h; simp [e_apply_self, Nat.add_comm]
      · simp [e_apply_of_ne h, beq_iff_eq, h]

/-- Two words of equal weight are permutations of each other. -/
theorem perm_of_wordWeight_eq {l l' : List (Fin n)} (h : wordWeight l = wordWeight l') :
    l.Perm l' := by
  rw [List.perm_iff_count]
  intro j
  rw [← wordWeight_apply, ← wordWeight_apply, h]

/-- Every word is a permutation of the canonical word of its weight. -/
theorem perm_monList_wordWeight (l : List (Fin n)) : l.Perm (monList (wordWeight l)) :=
  perm_of_wordWeight_eq (by rw [wordWeight_monList])

/-! ### Order-independence -/

theorem cWord_of_perm (hc : CentralElts bas q mu) {l l' : List (Fin n)}
    (h : l.Perm l') : cWord bas q mu l = cWord bas q mu l' :=
  List.Perm.prod_eq' (h.map _)
    (List.pairwise_map.mpr (List.pairwise_of_forall fun a _ => hc a _))

theorem bigCword_of_perm (hc : CentralElts bas q mu) {l l' : List (Fin n)}
    (h : l.Perm l') : bigCword bas q mu l = bigCword bas q mu l' := by
  rw [bigCword, bigCword, cWord_of_perm bas q mu hc h]

/-- A word product is the multi-index power of its weight. -/
theorem bigCword_eq_bigCpow (hc : CentralElts bas q mu) (l : List (Fin n)) :
    bigCword bas q mu l = bigCpow bas q mu (wordWeight l) :=
  bigCword_of_perm bas q mu hc (perm_monList_wordWeight l)

/-! ### Additivity of the multi-index powers -/

theorem cWord_append (l l' : List (Fin n)) :
    cWord bas q mu (l ++ l') = cWord bas q mu l * cWord bas q mu l' := by
  rw [cWord, cWord, cWord, List.map_append, List.prod_append]

theorem bigCword_append (l l' : List (Fin n)) :
    bigCword bas q mu (l ++ l') = bigCword bas q mu l * bigCword bas q mu l' := by
  rw [bigCword, bigCword, bigCword, cWord_append, map_mul]

/-- `C^(m + m') = C^m ∘ C^(m')`. -/
theorem bigCpow_add (hc : CentralElts bas q mu) (m m' : Mon n) :
    bigCpow bas q mu (m + m') = bigCpow bas q mu m * bigCpow bas q mu m' := by
  rw [bigCpow, bigCpow, bigCpow, ← bigCword_append]
  refine bigCword_of_perm bas q mu hc (perm_of_wordWeight_eq ?_)
  rw [wordWeight_monList, wordWeight_append, wordWeight_monList, wordWeight_monList]

/-- `bigC j` is the word product of the one-letter word `[j]`. -/
theorem bigCword_singleton (j : Fin n) : bigCword bas q mu [j] = bigC bas q mu j := by
  rw [bigCword_cons, bigCword_nil, mul_one]

/-- **Applying `Cⱼ` to `C^m` gives `C^(m + eⱼ)`.** -/
theorem bigC_mul_bigCpow (hc : CentralElts bas q mu) (j : Fin n) (m : Mon n) :
    bigC bas q mu j * bigCpow bas q mu m = bigCpow bas q mu (m + e j) := by
  rw [← bigCword_singleton bas q mu j, bigCpow, ← bigCword_append, List.singleton_append,
    bigCword_eq_bigCpow bas q mu hc, wordWeight_cons, wordWeight_monList, add_comm]

end Submission.Ado.PBW
