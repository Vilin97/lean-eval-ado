import Submission.Morley.Ramsey

/-!
# Order indiscernibles

This file defines order indiscernible sequences in a first-order structure and proves the
existence of such sequences using the infinite Ramsey theorem together with the compactness
theorem.
-/

universe u v w w'

namespace Submission.Morley

open FirstOrder FirstOrder.Language

/-- A tuple-indexed form of the infinite Ramsey theorem: a finite colouring of the strictly
increasing `n`-tuples drawn from an infinite set of naturals is constant on the strictly
increasing `n`-tuples drawn from some infinite subset. -/
theorem exists_infinite_subset_monochromatic_tuple {S : Set ℕ} (hS : S.Infinite) (n : ℕ)
    {β : Type v} [Finite β] (c : (Fin n → ℕ) → β) :
    ∃ S' : Set ℕ, S' ⊆ S ∧ S'.Infinite ∧ ∃ b : β,
      ∀ i : Fin n → ℕ, StrictMono i → (∀ k, i k ∈ S') → c i = b := by
  classical
  have : Infinite S := hS.to_subtype
  obtain ⟨S'', hS''inf, b, hb⟩ :=
    exists_infinite_monochromatic (α := S) n
      (fun s => c fun k => ((s.1.orderEmbOfFin s.2 k : S) : ℕ))
  refine ⟨Subtype.val '' S'', ?_, ?_, b, ?_⟩
  · rintro x ⟨y, -, rfl⟩
    exact y.2
  · exact hS''inf.image (Set.injOn_of_injective Subtype.val_injective)
  · intro i hi hiS'
    have hiS : ∀ k, i k ∈ S := fun k => by
      obtain ⟨y, -, hy⟩ := hiS' k
      exact hy ▸ y.2
    set j : Fin n → S := fun k => ⟨i k, hiS k⟩
    have hjmono : StrictMono j := fun k l hkl => Subtype.coe_lt_coe.mp (hi hkl)
    have hjmem : ∀ k, j k ∈ S'' := by
      intro k
      obtain ⟨y, hy, hy'⟩ := hiS' k
      exact (Subtype.ext hy' : y = j k) ▸ hy
    have hcard : (Finset.image j Finset.univ).card = n := by
      rw [Finset.card_image_of_injective _ hjmono.injective, Finset.card_univ, Fintype.card_fin]
    have hmemim : ∀ k, j k ∈ Finset.image j Finset.univ := fun k =>
      Finset.mem_image_of_mem _ (Finset.mem_univ k)
    have heq : j = (Finset.image j Finset.univ).orderEmbOfFin hcard :=
      Finset.orderEmbOfFin_unique hcard hmemim hjmono
    have := hb ⟨Finset.image j Finset.univ, hcard⟩ (by
      intro x hx
      simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at hx
      obtain ⟨k, rfl⟩ := hx
      exact hjmem k)
    have hconv : (fun k => (((Finset.image j Finset.univ).orderEmbOfFin hcard) k : ℕ)) = i := by
      funext k
      rw [← heq]
    rwa [hconv] at this

/-- A sequence `a : I → M` indexed by a linear order `I` is *order indiscernible* if any two
strictly increasing tuples drawn from it satisfy exactly the same formulas. -/
def IsOrderIndiscernible {L : FirstOrder.Language.{u, v}} {M : Type w} [L.Structure M]
    {I : Type*} [LinearOrder I] (a : I → M) : Prop :=
  ∀ (n : ℕ) (φ : L.Formula (Fin n)) (i j : Fin n → I),
    StrictMono i → StrictMono j → (φ.Realize (a ∘ i) ↔ φ.Realize (a ∘ j))

/-- Ramsey's theorem applied to a first-order structure: given a sequence `b : ℕ → M` in an
`L`-structure `M` and finitely many formulas, there is an infinite set of indices on which all
of those formulas are indiscernible. -/
theorem exists_infinite_indiscernible_of_finite {L : FirstOrder.Language.{u, v}} {M : Type w}
    [L.Structure M] (b : ℕ → M) (Δ : Set (Σ n, L.Formula (Fin n))) (hΔ : Δ.Finite)
    {S : Set ℕ} (hS : S.Infinite) :
    ∃ S' : Set ℕ, S' ⊆ S ∧ S'.Infinite ∧
      ∀ p ∈ Δ, ∀ i j : Fin p.1 → ℕ, StrictMono i → StrictMono j →
        (∀ k, i k ∈ S') → (∀ k, j k ∈ S') → (p.2.Realize (b ∘ i) ↔ p.2.Realize (b ∘ j)) := by
  induction Δ, hΔ using Set.Finite.induction_on with
  | empty => exact ⟨S, subset_rfl, hS, by simp⟩
  | @insert p Δ _ _ ih =>
    obtain ⟨S₁, hS₁sub, hS₁inf, hS₁⟩ := ih
    obtain ⟨S₂, hS₂sub, hS₂inf, t, ht⟩ :=
      exists_infinite_subset_monochromatic_tuple hS₁inf p.1 fun i => p.2.Realize (b ∘ i)
    refine ⟨S₂, hS₂sub.trans hS₁sub, hS₂inf, ?_⟩
    rintro q (rfl | hq) i j hi hj hiS hjS
    · rw [ht i hi hiS, ht j hj hjS]
    · exact hS₁ q hq i j hi hj (fun k => hS₂sub (hiS k)) fun k => hS₂sub (hjS k)

section Existence

variable {L : FirstOrder.Language.{u, v}}

/-- The data determining an indiscernibility axiom: an arity, a formula, and two tuples of
indices. -/
abbrev IndisData (L : FirstOrder.Language.{u, v}) (I : Type w') : Type (max u v w') :=
  Σ n : ℕ, L.Formula (Fin n) × (Fin n → I) × (Fin n → I)

/-- The `L[[I]]`-sentence saying that the two tuples of new constants satisfy the same instance
of the given formula. -/
def indisSentence {I : Type w'} (d : IndisData L I) : L[[I]].Sentence :=
  Formula.equivSentence ((d.2.1.relabel d.2.2.1).iff (d.2.1.relabel d.2.2.2))

/-- The `L[[I]]`-theory saying that the new constants form an order indiscernible sequence. -/
def indiscernibleTheory (L : FirstOrder.Language.{u, v}) (I : Type w') [LinearOrder I] :
    L[[I]].Theory :=
  indisSentence '' {d : IndisData L I | StrictMono d.2.2.1 ∧ StrictMono d.2.2.2}

/-- The `L[[I]]`-theory whose models are exactly the models of `T` equipped with an injective
order indiscernible sequence indexed by `I`. -/
def indiscernibleExtension (T : L.Theory) (I : Type w') [LinearOrder I] : L[[I]].Theory :=
  ((L.lhomWithConstants I).onTheory T ∪ L.distinctConstantsTheory (Set.univ : Set I)) ∪
    indiscernibleTheory L I

/-- **Finite satisfiability of the indiscernible extension.** This is where Ramsey's theorem is
used: a finite fragment of the theory mentions only finitely many formulas and finitely many new
constants, and Ramsey's theorem produces an infinite set of elements of `M` on which all of those
formulas are indiscernible. -/
theorem isSatisfiable_indiscernibleExtension (T : L.Theory) (M : Type w) [L.Structure M]
    [M ⊨ T] [Infinite M] (I : Type w') [LinearOrder I] :
    (indiscernibleExtension T I).IsSatisfiable := by
  classical
  rw [Theory.isSatisfiable_iff_isFinitelySatisfiable]
  intro T0 hT0
  -- Witnesses for the indiscernibility axioms occurring in `T0`.
  have hAfin : ((T0 : Set (L[[I]].Sentence)) ∩ indiscernibleTheory L I).Finite :=
    T0.finite_toSet.inter_of_left _
  haveI : Finite ↥((T0 : Set (L[[I]].Sentence)) ∩ indiscernibleTheory L I) := hAfin.to_subtype
  have hwitA : ∀ σ : ↥((T0 : Set (L[[I]].Sentence)) ∩ indiscernibleTheory L I),
      ∃ d : IndisData L I, (StrictMono d.2.2.1 ∧ StrictMono d.2.2.2) ∧
        indisSentence d = (σ : L[[I]].Sentence) := fun σ => σ.2.2
  choose D hDmono hDeq using hwitA
  -- Witnesses for the distinctness axioms occurring in `T0`.
  have hBfin : ((T0 : Set (L[[I]].Sentence)) ∩
      L.distinctConstantsTheory (Set.univ : Set I)).Finite := T0.finite_toSet.inter_of_left _
  haveI : Finite ↥((T0 : Set (L[[I]].Sentence)) ∩
      L.distinctConstantsTheory (Set.univ : Set I)) := hBfin.to_subtype
  have hwitB : ∀ σ : ↥((T0 : Set (L[[I]].Sentence)) ∩
      L.distinctConstantsTheory (Set.univ : Set I)), ∃ p : I × I, p.1 ≠ p.2 ∧
        ((L.con p.1).term.equal (L.con p.2).term).not = (σ : L[[I]].Sentence) := by
    intro σ
    obtain ⟨p, hp, hpe⟩ := σ.2.2
    exact ⟨p, by simpa using hp.2, hpe⟩
  choose P hPne hPeq using hwitB
  -- The finite set of indices mentioned in `T0`.
  set F : Set I := (⋃ σ, Set.range (D σ).2.2.1 ∪ Set.range (D σ).2.2.2) ∪
    ⋃ σ, ({(P σ).1, (P σ).2} : Set I) with hFdef
  have hFfin : F.Finite :=
    (Set.finite_iUnion fun _ => (Set.finite_range _).union (Set.finite_range _)).union
      (Set.finite_iUnion fun _ => (Set.finite_singleton _).insert _)
  -- The finite set of formulas mentioned in `T0`.
  have hΔfin : (Set.range fun σ => (⟨(D σ).1, (D σ).2.1⟩ : Σ n, L.Formula (Fin n))).Finite :=
    Set.finite_range _
  -- Ramsey's theorem applied to an injective sequence in `M`.
  obtain ⟨b, hbinj⟩ : ∃ b : ℕ → M, Function.Injective b :=
    ⟨Infinite.natEmbedding M, (Infinite.natEmbedding M).injective⟩
  obtain ⟨S, -, hSinf, hSind⟩ := exists_infinite_indiscernible_of_finite (M := M) b _ hΔfin
    (S := Set.univ) Set.infinite_univ
  obtain ⟨N, hN⟩ : ∃ N, hFfin.toFinset.card = N := ⟨_, rfl⟩
  obtain ⟨t, htS, htcard⟩ := hSinf.exists_subset_card_eq N
  set u : Fin N ↪o ℕ := t.orderEmbOfFin htcard with hu
  set ρ : Fin N ≃o hFfin.toFinset := hFfin.toFinset.orderIsoOfFin hN with hρ
  set e : I → M := fun x => if h : x ∈ hFfin.toFinset then b (u (ρ.symm ⟨x, h⟩)) else b 0 with he
  have hmemF : ∀ x ∈ F, x ∈ hFfin.toFinset := fun x hx => hFfin.mem_toFinset.mpr hx
  have heF : ∀ (x : I) (hx : x ∈ F), e x = b (u (ρ.symm ⟨x, hmemF x hx⟩)) := by
    intro x hx
    rw [he]
    exact dif_pos (hmemF x hx)
  -- `e` is injective on `F`.
  have heinj : Set.InjOn e F := by
    intro x hx y hy hxy
    rw [heF x hx, heF y hy] at hxy
    have := ρ.symm.injective (u.injective (hbinj hxy))
    exact congrArg Subtype.val this
  -- Transporting increasing tuples from `F` into `S`.
  have key : ∀ (n : ℕ) (i : Fin n → I), StrictMono i → (∀ k, i k ∈ F) →
      ∃ i' : Fin n → ℕ, StrictMono i' ∧ (∀ k, i' k ∈ S) ∧ ∀ k, e (i k) = b (i' k) := by
    intro n i hi hiF
    refine ⟨fun k => u (ρ.symm ⟨i k, hmemF _ (hiF k)⟩), fun k l hkl => ?_, fun k => ?_,
      fun k => heF _ (hiF k)⟩
    · exact u.strictMono (ρ.symm.strictMono (Subtype.mk_lt_mk.mpr (hi hkl)))
    · exact htS (Finset.mem_coe.mpr (t.orderEmbOfFin_mem htcard _))
  -- Interpret the new constants by `e`.
  letI : (constantsOn I).Structure M := constantsOn.structure e
  have hcon : ∀ x : I, (L.con x : M) = e x := fun _ => rfl
  haveI : M ⊨ (L.lhomWithConstants I).onTheory T := (LHom.onTheory_model _ T).mpr inferInstance
  haveI : M ⊨ L.distinctConstantsTheory F := by
    rw [L.model_distinctConstantsTheory F]
    intro x hx y hy hxy
    exact heinj hx hy (by simpa only [hcon] using hxy)
  haveI : M ⊨ (T0 : L[[I]].Theory) := by
    refine Theory.model_iff _ |>.mpr fun σ hσ => ?_
    rcases hT0 hσ with (hcase | hcase) | hcase
    · exact Theory.realize_sentence_of_mem _ hcase
    · -- a distinctness axiom
      have hmem : σ ∈ ((T0 : Set (L[[I]].Sentence)) ∩
          L.distinctConstantsTheory (Set.univ : Set I)) := ⟨hσ, hcase⟩
      have hp1 : (P ⟨σ, hmem⟩).1 ∈ F :=
        Set.mem_union_right _ (Set.mem_iUnion.mpr ⟨⟨σ, hmem⟩, Set.mem_insert _ _⟩)
      have hp2 : (P ⟨σ, hmem⟩).2 ∈ F :=
        Set.mem_union_right _
          (Set.mem_iUnion.mpr ⟨⟨σ, hmem⟩, Set.mem_insert_of_mem _ rfl⟩)
      refine Theory.realize_sentence_of_mem (L.distinctConstantsTheory F) ?_
      exact ⟨P ⟨σ, hmem⟩, ⟨⟨hp1, hp2⟩, hPne ⟨σ, hmem⟩⟩, hPeq ⟨σ, hmem⟩⟩
    · -- an indiscernibility axiom
      have hmem : σ ∈ ((T0 : Set (L[[I]].Sentence)) ∩ indiscernibleTheory L I) := ⟨hσ, hcase⟩
      have hd : indisSentence (D ⟨σ, hmem⟩) = σ := hDeq ⟨σ, hmem⟩
      have hm := hDmono ⟨σ, hmem⟩
      have hiF : ∀ k, (D ⟨σ, hmem⟩).2.2.1 k ∈ F := fun k =>
        Set.mem_union_left _ (Set.mem_iUnion.mpr ⟨⟨σ, hmem⟩, Set.mem_union_left _ ⟨k, rfl⟩⟩)
      have hjF : ∀ k, (D ⟨σ, hmem⟩).2.2.2 k ∈ F := fun k =>
        Set.mem_union_left _ (Set.mem_iUnion.mpr ⟨⟨σ, hmem⟩, Set.mem_union_right _ ⟨k, rfl⟩⟩)
      obtain ⟨i', hi'mono, hi'S, hi'e⟩ := key _ _ hm.1 hiF
      obtain ⟨j', hj'mono, hj'S, hj'e⟩ := key _ _ hm.2 hjF
      have hres := hSind _ ⟨⟨σ, hmem⟩, rfl⟩ i' j' hi'mono hj'mono hi'S hj'S
      rw [← hd]
      simp only [indisSentence]
      rw [Formula.realize_equivSentence, Formula.realize_iff, Formula.realize_relabel,
        Formula.realize_relabel]
      have hc1 : (fun x : I => (L.con x : M)) ∘ (D ⟨σ, hmem⟩).2.2.1 = b ∘ i' := by
        funext k
        simp only [Function.comp_apply, hcon]
        exact hi'e k
      have hc2 : (fun x : I => (L.con x : M)) ∘ (D ⟨σ, hmem⟩).2.2.2 = b ∘ j' := by
        funext k
        simp only [Function.comp_apply, hcon]
        exact hj'e k
      rw [hc1, hc2]
      exact hres
  exact Theory.Model.isSatisfiable M

theorem exists_orderIndiscernible_of_isSatisfiable (T : L.Theory) (I : Type w') [LinearOrder I]
    (h : (indiscernibleExtension T I).IsSatisfiable) :
    ∃ (N : T.ModelType.{u, v, max u v w'}) (a : I → N),
      Function.Injective a ∧ IsOrderIndiscernible (L := L) a := by
  obtain ⟨N⟩ := h
  letI : L.Structure N := (L.lhomWithConstants I).reduct N
  have hT : N ⊨ (L.lhomWithConstants I).onTheory T :=
    N.is_model.mono (Set.subset_union_left.trans Set.subset_union_left)
  have hD : N ⊨ L.distinctConstantsTheory (Set.univ : Set I) :=
    N.is_model.mono (Set.subset_union_right.trans Set.subset_union_left)
  have hI : N ⊨ indiscernibleTheory L I := N.is_model.mono Set.subset_union_right
  haveI : N ⊨ T := (LHom.onTheory_model _ _).mp hT
  set a : I → (N : Type (max u v w')) := fun i => (L.con i : N) with ha
  have hinj : Function.Injective a := by
    rw [ha, ← Set.injOn_univ]
    exact (L.model_distinctConstantsTheory (Set.univ : Set I)).mp hD
  have hind : IsOrderIndiscernible (L := L) a := by
    intro n φ i j hi hj
    have hmem : indisSentence (⟨n, φ, i, j⟩ : IndisData L I) ∈ indiscernibleTheory L I :=
      ⟨⟨n, φ, i, j⟩, ⟨hi, hj⟩, rfl⟩
    have hreal := hI.realize_of_mem _ hmem
    rw [indisSentence, Formula.realize_equivSentence, Formula.realize_iff,
      Formula.realize_relabel, Formula.realize_relabel] at hreal
    exact hreal
  exact ⟨Theory.ModelType.of T N, a, hinj, hind⟩

/-- **Existence of order indiscernibles.** If the `L`-theory `T` has an infinite model, then for
every linear order `I` there is a model of `T` containing an injective order indiscernible
sequence indexed by `I`.

The proof combines the infinite Ramsey theorem with the compactness theorem. -/
theorem exists_orderIndiscernible (T : L.Theory) (M : Type w) [L.Structure M] [M ⊨ T]
    [Infinite M] (I : Type w') [LinearOrder I] :
    ∃ (N : T.ModelType.{u, v, max u v w'}) (a : I → N),
      Function.Injective a ∧ IsOrderIndiscernible (L := L) a :=
  exists_orderIndiscernible_of_isSatisfiable T I (isSatisfiable_indiscernibleExtension T M I)

end Existence

end Submission.Morley
