import Mathlib
import Submission.Morley.TwoCardinal

/-!
# Realizing countably many types in a countable elementary extension

This file supplies the compactness step that the `ω`-chain construction in Vaught's two-cardinal
theorem needs (see `Submission.Morley.TwoCardinal`): given a countable structure `A` and a
countable family of `1`-types over `A`, each of them *finitely satisfiable in `A`*, there is a
**countable** elementary extension of `A` realizing all of them simultaneously.

## The construction

Work in `L[[A]][[ι]]`: the language `L` with a constant naming every element of `A`, plus one
further constant `c i` for every index `i` of the family.  The theory `typeTheory L A p` consists
of

* the elementary diagram of `A`, pushed forward along `L[[A]] →ᴸ L[[A]][[ι]]`;
* for every `i` and every `φ ∈ p i`, the sentence `typeSentence L A i φ` obtained from `φ` by
  naming its parameters with their own constants and substituting `c i` for the free variable.

The theory is presented as the union of the diagram with the *range* of a map out of
`typeIndex p = Σ i, {φ // φ ∈ p i}`, so that membership of one of the new sentences carries the
index it came from; this is what makes the finite-satisfiability argument painless.  Writing that
range as a directed union over `Finset (typeIndex p)` reduces satisfiability to
`isSatisfiable_typeTheoryFin`, where only finitely many formulas occur and `A` itself is a model:
for each `i`, finite satisfiability of `p i` supplies an element of `A` to interpret `c i`.

A model of `typeTheory L A p` is an elementary extension of `A` (via
`ElementaryEmbedding.ofModelsElementaryDiagram`) in which `c i` realizes `p i`.  Downward
Löwenheim–Skolem, seeded with the image of `A` together with the interpretations of the `c i`,
cuts it down to a countable one.

## Main results

* `Submission.Morley.isSatisfiable_typeTheory`: the combined theory is satisfiable.
* `Submission.Morley.exists_elementaryExtension_realizing`: an elementary extension realizing
  every `p i`, of unrestricted size.
* `Submission.Morley.exists_countable_elementaryExtension_realizing`: the same, with the extension
  countable.
-/

namespace Submission.Morley

open Cardinal Set FirstOrder FirstOrder.Language

variable {L : FirstOrder.Language.{0, 0}} {A : Type} [L.Structure A] {ι : Type}

/-- The sentence of `L[[A]][[ι]]` obtained from a formula `φ` in the parameters `A` and a single
free variable, by naming the parameters with their own constants and substituting the new
constant `c i` for the free variable. -/
def typeSentence (L : FirstOrder.Language.{0, 0}) (A : Type) [L.Structure A] {ι : Type} (i : ι)
    (φ : L.Formula (A ⊕ Fin 1)) : (L[[A]][[ι]]).Sentence :=
  (((L[[A]]).lhomWithConstants ι).onFormula
      (BoundedFormula.constantsVarsEquiv.symm φ)).subst fun _ => ((L[[A]]).con i).term

/-- `typeSentence L A i φ` says exactly that `φ` holds of the interpretations of the constants:
the parameters are read off from `L[[A]]` and the free variable is `c i`. -/
theorem realize_typeSentence {M : Type} [L.Structure M] [(L[[A]]).Structure M]
    [(L[[A]][[ι]]).Structure M] [(L.lhomWithConstants A).IsExpansionOn M]
    [((L[[A]]).lhomWithConstants ι).IsExpansionOn M]
    (i : ι) (φ : L.Formula (A ⊕ Fin 1)) :
    M ⊨ typeSentence L A i φ ↔
      φ.Realize (Sum.elim (fun a => (L.con a : M)) fun _ => ((L[[A]]).con i : M)) := by
  rw [Sentence.Realize, typeSentence, Formula.Realize, BoundedFormula.realize_subst]
  simp only [Term.realize_constants]
  rw [show ∀ (χ : (L[[A]][[ι]]).Formula (Fin 1)),
      BoundedFormula.Realize χ (fun _ => ((L[[A]]).con i : M)) default =
        Formula.Realize χ (fun _ => ((L[[A]]).con i : M)) from fun _ => rfl]
  rw [LHom.realize_onFormula]
  have key := BoundedFormula.realize_constantsVarsEquiv (M := M) (L := L) (α := A) (β := Fin 1)
    (n := 0) (φ := BoundedFormula.constantsVarsEquiv.symm φ)
    (v := fun _ => ((L[[A]]).con i : M)) (xs := default)
  rw [Equiv.apply_symm_apply] at key
  exact key.symm

/-- The index type carrying, along with a formula, the type it belongs to. -/
abbrev typeIndex (p : ι → Set (L.Formula (A ⊕ Fin 1))) : Type :=
  Σ i : ι, {φ : L.Formula (A ⊕ Fin 1) // φ ∈ p i}

/-- The sentence attached to an element of `typeIndex p`. -/
abbrev typeIndexSentence (L : FirstOrder.Language.{0, 0}) (A : Type) [L.Structure A] {ι : Type}
    (p : ι → Set (L.Formula (A ⊕ Fin 1))) (q : typeIndex p) : (L[[A]][[ι]]).Sentence :=
  typeSentence L A q.1 q.2.1

/-- The theory in `L[[A]][[ι]]` consisting of the elementary diagram of `A` together with, for
each index `i`, all the formulas of `p i` with the constant `c i` substituted for the free
variable.  A model of it is an elementary extension of `A` realizing every `p i`. -/
def typeTheory (L : FirstOrder.Language.{0, 0}) (A : Type) [L.Structure A] {ι : Type}
    (p : ι → Set (L.Formula (A ⊕ Fin 1))) : (L[[A]][[ι]]).Theory :=
  ((L[[A]]).lhomWithConstants ι).onTheory (L.elementaryDiagram A) ∪
    Set.range (typeIndexSentence L A p)

/-- The approximations of `typeTheory` by finitely many of the new sentences. -/
def typeTheoryFin (L : FirstOrder.Language.{0, 0}) (A : Type) [L.Structure A] {ι : Type}
    (p : ι → Set (L.Formula (A ⊕ Fin 1))) (s : Finset (typeIndex p)) : (L[[A]][[ι]]).Theory :=
  ((L[[A]]).lhomWithConstants ι).onTheory (L.elementaryDiagram A) ∪
    typeIndexSentence L A p '' (s : Set (typeIndex p))

/-- The full theory is the directed union of its finite approximations. -/
theorem typeTheory_eq_iUnion (p : ι → Set (L.Formula (A ⊕ Fin 1))) :
    typeTheory L A p = ⋃ s : Finset (typeIndex p), typeTheoryFin L A p s := by
  apply Set.Subset.antisymm
  · rintro σ (hσ | ⟨q, rfl⟩)
    · exact Set.mem_iUnion.2 ⟨∅, Or.inl hσ⟩
    · exact Set.mem_iUnion.2 ⟨{q}, Or.inr ⟨q, by simp, rfl⟩⟩
  · refine Set.iUnion_subset fun s => Set.union_subset_union_right _ ?_
    rintro σ ⟨q, -, rfl⟩
    exact ⟨q, rfl⟩

/-- Each finite approximation is satisfied by `A` itself, interpreting the constant `c i` by a
witness for the finitely many formulas of `p i` that occur. -/
theorem isSatisfiable_typeTheoryFin [Nonempty A] (p : ι → Set (L.Formula (A ⊕ Fin 1)))
    (hfin : ∀ i, ∀ t : Finset (L.Formula (A ⊕ Fin 1)), ↑t ⊆ p i →
      ∃ a : A, ∀ φ ∈ t, φ.Realize (Sum.elim id fun _ => a))
    (s : Finset (typeIndex p)) : (typeTheoryFin L A p s).IsSatisfiable := by
  classical
  set si : ι → Finset (L.Formula (A ⊕ Fin 1)) :=
    fun i => (s.filter fun q => q.1 = i).image fun q => q.2.1 with hsi
  have hsub : ∀ i, ↑(si i) ⊆ p i := by
    intro i φ hφ
    simp only [hsi, Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_filter] at hφ
    obtain ⟨q, ⟨-, hqi⟩, rfl⟩ := hφ
    subst hqi
    exact q.2.2
  have hmem : ∀ q ∈ s, q.2.1 ∈ si q.1 := fun q hq =>
    Finset.mem_image.2 ⟨q, Finset.mem_filter.2 ⟨hq, rfl⟩, rfl⟩
  choose val hval using fun i => hfin i (si i) (hsub i)
  letI : (constantsOn ι).Structure A := constantsOn.structure val
  have hdiag : A ⊨ ((L[[A]]).lhomWithConstants ι).onTheory (L.elementaryDiagram A) :=
    (LHom.onTheory_model _ _).2 inferInstance
  have himg : A ⊨ typeIndexSentence L A p '' (s : Set (typeIndex p)) := by
    rw [Theory.model_iff]
    rintro σ ⟨q, hq, rfl⟩
    rw [realize_typeSentence]
    exact hval q.1 q.2.1 (hmem q hq)
  haveI : A ⊨ typeTheoryFin L A p s := hdiag.union himg
  exact Theory.Model.isSatisfiable A

/-- The finite approximations are monotone in the finite set, hence directed. -/
theorem directed_typeTheoryFin (p : ι → Set (L.Formula (A ⊕ Fin 1))) :
    Directed (· ⊆ ·) (typeTheoryFin L A p) :=
  Monotone.directed_le fun _ _ hst =>
    Set.union_subset_union_right _ (Set.image_mono (Finset.coe_subset.2 hst))

/-- **Compactness**: the whole theory is satisfiable. -/
theorem isSatisfiable_typeTheory [Nonempty A] (p : ι → Set (L.Formula (A ⊕ Fin 1)))
    (hfin : ∀ i, ∀ t : Finset (L.Formula (A ⊕ Fin 1)), ↑t ⊆ p i →
      ∃ a : A, ∀ φ ∈ t, φ.Realize (Sum.elim id fun _ => a)) :
    (typeTheory L A p).IsSatisfiable := by
  rw [typeTheory_eq_iUnion, Theory.isSatisfiable_directed_union_iff (directed_typeTheoryFin p)]
  exact isSatisfiable_typeTheoryFin p hfin

/-- **Realization of countably many types in an elementary extension**, before cutting the
extension down to countable size: a model of `typeTheory L A p` is exactly an elementary extension
of `A` equipped with a realization of each `p i`. -/
theorem exists_elementaryExtension_realizing
    [Nonempty A] (p : ι → Set (L.Formula (A ⊕ Fin 1)))
    (hfin : ∀ i, ∀ t : Finset (L.Formula (A ⊕ Fin 1)), ↑t ⊆ p i →
      ∃ a : A, ∀ φ ∈ t, φ.Realize (Sum.elim id fun _ => a)) :
    ∃ (B : Type) (_ : L.Structure B) (f : A ↪ₑ[L] B) (b : ι → B),
      (∀ i, ∀ φ ∈ p i, φ.Realize (Sum.elim (f ·) fun _ => b i)) := by
  obtain ⟨N⟩ := isSatisfiable_typeTheory p hfin
  letI : (L[[A]]).Structure N := ((L[[A]]).lhomWithConstants ι).reduct N
  haveI : ((L[[A]]).lhomWithConstants ι).IsExpansionOn N := LHom.isExpansionOn_reduct _ _
  letI : L.Structure N := (L.lhomWithConstants A).reduct N
  haveI : (L.lhomWithConstants A).IsExpansionOn N := LHom.isExpansionOn_reduct _ _
  haveI hNdiag : N ⊨ L.elementaryDiagram A :=
    (LHom.onTheory_model _ _).1 (Theory.Model.mono N.is_model Set.subset_union_left)
  refine ⟨N, inferInstance, ElementaryEmbedding.ofModelsElementaryDiagram L A N,
    fun i => ((L[[A]]).con i : N), fun i φ hφ => ?_⟩
  have hmem : typeSentence L A i φ ∈ typeTheory L A p := Or.inr ⟨⟨i, ⟨φ, hφ⟩⟩, rfl⟩
  have h := N.is_model.realize_of_mem _ hmem
  rw [realize_typeSentence] at h
  exact h

/-- **Downward Löwenheim–Skolem**, in the shape needed here: an elementary extension `N` of a
countable `A` together with countably many distinguished elements can be cut down to a countable
elementary substructure containing them all, without changing which formulas they satisfy. -/
theorem exists_countable_of_elementaryEmbedding (hL : L.card ≤ ℵ₀) [Countable A]
    {N : Type} [L.Structure N] (f : A ↪ₑ[L] N) [Countable ι] (b : ι → N) :
    ∃ (B : Type) (_ : L.Structure B) (_ : Countable B) (g : A ↪ₑ[L] B) (c : ι → B),
      ∀ (i : ι) (φ : L.Formula (A ⊕ Fin 1)),
        φ.Realize (Sum.elim (f ·) fun _ => b i) → φ.Realize (Sum.elim (g ·) fun _ => c i) := by
  classical
  rcases finite_or_infinite N with hN | hN
  · haveI := hN
    exact ⟨N, inferInstance, inferInstance, f, b, fun _ _ h => h⟩
  · haveI := hN
    have hcount : ((Set.range fun a => f a) ∪ Set.range b : Set N).Countable :=
      (Set.countable_range _).union (Set.countable_range _)
    obtain ⟨S, hSsub, hScard⟩ := exists_elementarySubstructure_card_eq L
      ((Set.range fun a => f a) ∪ Set.range b) (ℵ₀ : Cardinal.{0}) le_rfl
      (by simpa using Cardinal.mk_le_aleph0_iff.2 (Set.countable_coe_iff.2 hcount))
      (by simpa using hL) (by simp [Cardinal.aleph0_le_mk N])
    have hScard' : #(S : Type) = ℵ₀ := by simpa using hScard
    haveI : Countable (S : Type) := Cardinal.mk_le_aleph0_iff.1 hScard'.le
    have hfS : ∀ a : A, f a ∈ S := fun a => hSsub (Or.inl ⟨a, rfl⟩)
    have hbS : ∀ i : ι, b i ∈ S := fun i => hSsub (Or.inr ⟨i, rfl⟩)
    refine ⟨(S : Type), inferInstance, inferInstance,
      ⟨fun a => ⟨f a, hfS a⟩, fun n χ x => ?_⟩, fun i => ⟨b i, hbS i⟩, fun i φ h => ?_⟩
    · rw [← S.subtype.map_formula χ ((fun a : A => (⟨f a, hfS a⟩ : S)) ∘ x)]
      exact f.map_formula χ x
    · refine (S.subtype.map_formula φ
        (Sum.elim (fun a : A => (⟨f a, hfS a⟩ : S)) fun _ => (⟨b i, hbS i⟩ : S))).1 ?_
      rwa [show ((S.subtype : S → N) ∘
          Sum.elim (fun a : A => (⟨f a, hfS a⟩ : S)) fun _ => (⟨b i, hbS i⟩ : S)) =
          Sum.elim (fun a => f a) fun _ => b i from by
        funext z; rcases z with a | j <;> rfl]

/-- **Realization of countably many types in a countable elementary extension.**

Let `A` be a countable, nonempty structure for a language `L` with at most countably many symbols,
and let `p : ι → Set (L.Formula (A ⊕ Fin 1))` be a countable family of `1`-types over `A` (formulas
with parameters from `A` in a single free variable).  If each `p i` is *finitely satisfiable* in
`A`, then there is a countable elementary extension `B` of `A` in which every `p i` is realized. -/
theorem exists_countable_elementaryExtension_realizing (hL : L.card ≤ ℵ₀)
    [Countable A] [Nonempty A] [Countable ι] (p : ι → Set (L.Formula (A ⊕ Fin 1)))
    (hfin : ∀ i, ∀ t : Finset (L.Formula (A ⊕ Fin 1)), ↑t ⊆ p i →
      ∃ a : A, ∀ φ ∈ t, φ.Realize (Sum.elim id fun _ => a)) :
    ∃ (B : Type) (_ : L.Structure B) (_ : Countable B) (f : A ↪ₑ[L] B),
      ∀ i, ∃ b : B, ∀ φ ∈ p i, φ.Realize (Sum.elim (f ·) fun _ => b) := by
  obtain ⟨N, instN, f, b, hb⟩ := exists_elementaryExtension_realizing p hfin
  obtain ⟨B, instB, hcB, g, c, hgc⟩ := exists_countable_of_elementaryEmbedding hL f b
  exact ⟨B, instB, hcB, g, fun i => ⟨c i, fun φ hφ => hgc i φ (hb i φ hφ)⟩⟩

end Submission.Morley
