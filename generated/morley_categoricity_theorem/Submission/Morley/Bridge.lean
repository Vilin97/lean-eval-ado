/-
# Bridging the Ehrenfeucht–Mostowski chapter to the stability transfer chapter

`Submission/Morley/Transfer.lean` proves that categoricity implies ω-stability *conditionally* on
the Ehrenfeucht–Mostowski type-counting bound `Submission.Morley.EMTypeBoundAt`.
`Submission/Morley/EM.lean` proves that bound for Ehrenfeucht–Mostowski models, but

* only for the sequence-of-indiscernibles hypothesis `Submission.Morley.IndiscerniblesExist`
  taken as an assumption,
* only in the "raw" encoding `Submission.Morley.emTypeOver` of the type of an element over a
  parameter set, and
* with the types computed in the *ambient* model rather than in `EM(I)` itself.

This file closes all three gaps and proves `Submission.Morley.emTypeBound`, which discharges the
hypothesis of `Submission.Morley.isOmegaStable_of_categorical`.

## Main results

* `Submission.Morley.indiscerniblesExist` — the Ramsey chapter discharges
  `Submission.Morley.IndiscerniblesExist`.
* `Submission.Morley.exists_emData_injective` — Ehrenfeucht–Mostowski data whose indiscernible
  sequence is injective, so that `#EM(I) = #I + ℵ₀` exactly.
* `Submission.Morley.typeOverN_eq_of_emTypeOverN_eq` — the reconciliation of the two encodings of
  "the type of a tuple over a parameter set", including the transfer along the elementary
  embedding `EM(I) ≼ M`.
* `Submission.Morley.emTypeBound` — the Ehrenfeucht–Mostowski type-counting bound, in every
  finite number of variables.

The type counting of `Submission/Morley/EM.lean` is stated for single elements; the argument is
re-run here for tuples (`Submission.Morley.emTypeOverN`), which needs the observation
`Submission.Morley.exists_common_index` that a tuple from a Skolem hull can be written using a
*single* strictly increasing tuple of indices.
-/
import Mathlib
import Submission.Morley.EM
import Submission.Morley.Transfer

universe u v w

namespace Submission.Morley

open Cardinal FirstOrder FirstOrder.Language

/-! ## Existence of order indiscernibles -/

/-- The Ramsey chapter's `Submission.Morley.exists_orderIndiscernible` discharges the hypothesis
`Submission.Morley.IndiscerniblesExist` used by the Ehrenfeucht–Mostowski chapter. -/
theorem indiscerniblesExist (L : FirstOrder.Language.{0, 0}) : IndiscerniblesExist L := by
  intro T hT hInf I _
  obtain ⟨M⟩ := hT
  haveI : Infinite (M : Type) := hInf M
  obtain ⟨N, a, -, ha⟩ := exists_orderIndiscernible T (M : Type) I
  exact ⟨N, a, ha⟩

/-! ## Ehrenfeucht–Mostowski data with an injective indiscernible sequence -/

section Existence

variable {L : FirstOrder.Language.{0, 0}}

/-- A refinement of `Submission.Morley.nonempty_EMData`: the indiscernible sequence can be taken
injective, which is what pins down the cardinality of `EM(I)`.  (An order indiscernible sequence
that is not injective is constant, and then `EM(I)` can be countable.) -/
theorem exists_emData_injective (T : L.Theory) (hT : T.IsSatisfiable)
    (hInf : ∀ N : FirstOrder.Language.Theory.ModelType.{0, 0, 0} T, Infinite N)
    (I : Type) [LinearOrder I] : ∃ d : EMData L T I, Function.Injective d.seq := by
  have hsat : (emTheory L T).IsSatisfiable := by
    obtain ⟨M⟩ := hT
    have h1 : (M : Type) ⊨ FirstOrder.Language.LHom.sumInl.onTheory T :=
      (LHom.onTheory_model (FirstOrder.Language.LHom.sumInl : L →ᴸ L.sum L.skolem₁) T).2
        inferInstance
    have h2 : (M : Type) ⊨ skolemTheory L := model_skolemTheory L (M : Type)
    haveI h3 : (M : Type) ⊨ emTheory L T := Theory.model_union_iff.2 ⟨h1, h2⟩
    exact Theory.Model.isSatisfiable (M : Type)
  have hinf : ∀ N : FirstOrder.Language.Theory.ModelType.{0, 0, 0} (emTheory L T),
      Infinite N := by
    intro N
    letI : L.Structure (N : Type) :=
      (FirstOrder.Language.LHom.sumInl : L →ᴸ L.sum L.skolem₁).reduct (N : Type)
    have hN : (N : Type) ⊨ emTheory L T := inferInstance
    haveI : (N : Type) ⊨ T :=
      (LHom.onTheory_model (FirstOrder.Language.LHom.sumInl : L →ᴸ L.sum L.skolem₁) T).1
        (Theory.model_union_iff.1 hN).1
    exact hInf (FirstOrder.Language.Theory.ModelType.of T (N : Type))
  obtain ⟨M₀⟩ := hsat
  haveI : Infinite (M₀ : Type) := hinf M₀
  obtain ⟨N, a, hinj, ha⟩ := exists_orderIndiscernible (emTheory L T) (M₀ : Type) I
  letI : L.Structure (N : Type) :=
      (FirstOrder.Language.LHom.sumInl : L →ᴸ L.sum L.skolem₁).reduct (N : Type)
  have hN : (N : Type) ⊨ emTheory L T := inferInstance
  haveI : (N : Type) ⊨ T :=
    (LHom.onTheory_model (FirstOrder.Language.LHom.sumInl : L →ᴸ L.sum L.skolem₁) T).1
      (Theory.model_union_iff.1 hN).1
  exact ⟨{ Carrier := (N : Type)
           skolem := (Theory.model_union_iff.1 hN).2
           seq := a
           indiscernible := ha }, hinj⟩

/-- If the indiscernible sequence is injective then `EM(I)` has at least `#I` elements. -/
theorem EMData.card_le_card_toEM {T : L.Theory} {I : Type} [LinearOrder I] (d : EMData L T I)
    (hinj : Function.Injective d.seq) : #I ≤ #(d.toEM) := by
  rw [← Cardinal.mk_range_eq d.seq hinj]
  exact Cardinal.mk_le_mk_of_subset (range_subset_EMSub d.seq)

end Existence

/-! ## Types of tuples in the Ehrenfeucht–Mostowski encoding -/

/-- The type of the `n`-tuple `b` over the parameter set `A ⊆ M`, in the encoding used by the
Ehrenfeucht–Mostowski chapter: the set of all pairs consisting of a formula
`φ(x₀,…,x_{m-1}, y₀,…,y_{n-1})` and a tuple of parameters from `A` that `b` satisfies.  For
`n = 1` this is `Submission.Morley.emTypeOver`. -/
def emTypeOverN (L : FirstOrder.Language.{u, v}) {M : Type w} [L.Structure M] (n : ℕ)
    (A : Set M) (b : Fin n → M) :
    Set ((m : ℕ) × L.Formula (Fin m ⊕ Fin n) × (Fin m → A)) :=
  {p | p.2.1.Realize (Sum.elim (fun r => ((p.2.2 r : M))) b)}

theorem emTypeOverN_one (L : FirstOrder.Language.{u, v}) {M : Type w} [L.Structure M]
    (A : Set M) (b : M) : emTypeOverN L 1 A (fun _ => b) = emTypeOver L A b := rfl

section Tuples

variable {L : FirstOrder.Language.{0, 0}} {M : Type} [(L.sum L.skolem₁).Structure M]
variable {I : Type} [LinearOrder I]

/-- **A tuple from a Skolem hull uses a single increasing tuple of indices.**  Every element of
`EMSub L a` is a Skolem term evaluated at some strictly increasing tuple of indices; merging the
(finitely many) index tuples of the coordinates of an `n`-tuple gives one strictly increasing
tuple of indices that works for all coordinates simultaneously. -/
theorem exists_common_index {a : I → M} {n : ℕ} {x : Fin n → M}
    (hx : ∀ k, x k ∈ EMSub L a) :
    ∃ (N : ℕ) (t : Fin n → (L.sum L.skolem₁).Term (Fin N)) (i : Fin N → I),
      StrictMono i ∧ ∀ k, (t k).realize (a ∘ i) = x k := by
  classical
  choose Nk tk ik _hik hxk using fun k => mem_EMSub_iff.mp (hx k)
  set F : Finset I := Finset.univ.biUnion fun k : Fin n => Finset.image (ik k) Finset.univ with hF
  have hmemF : ∀ (k : Fin n) (q : Fin (Nk k)), ik k q ∈ F := by
    intro k q
    rw [hF, Finset.mem_biUnion]
    exact ⟨k, Finset.mem_univ k, Finset.mem_image_of_mem _ (Finset.mem_univ q)⟩
  set e : Fin F.card ≃o F := F.orderIsoOfFin rfl with he
  refine ⟨F.card, fun k => (tk k).relabel fun q => e.symm ⟨ik k q, hmemF k q⟩,
    fun p => ((e p : I)), fun p q hpq => e.lt_iff_lt.mpr hpq, fun k => ?_⟩
  rw [Term.realize_relabel, ← hxk k]
  congr 1
  funext q
  simp only [Function.comp_apply]
  exact congrArg a (congrArg Subtype.val (e.apply_symm_apply ⟨ik k q, hmemF k q⟩))

/-- The set of indices needed to name a subset `A` of a Skolem hull by Skolem terms. -/
theorem exists_index_set {a : I → M} {A : Set M} (hA : A ⊆ (EMSub L a : Set M))
    {μ : Cardinal.{0}} (hAμ : #A ≤ μ) (hμ : ℵ₀ ≤ μ) :
    ∃ J : Set I, #J ≤ μ ∧ ∀ c : A, ∃ (m : ℕ) (s : (L.sum L.skolem₁).Term (Fin m))
      (p : Fin m → I), (∀ k, p k ∈ J) ∧ s.realize (a ∘ p) = (c : M) := by
  classical
  have hmem : ∀ c : A, ∃ (m : ℕ) (t : (L.sum L.skolem₁).Term (Fin m)) (p : Fin m → I),
      StrictMono p ∧ t.realize (a ∘ p) = (c : M) := fun c => mem_EMSub_iff.mp (hA c.2)
  choose mA sA pA _hpA hsA using hmem
  refine ⟨⋃ c : A, Set.range (pA c), ?_,
    fun c => ⟨mA c, sA c, pA c, fun k => Set.mem_iUnion.mpr ⟨c, ⟨k, rfl⟩⟩, hsA c⟩⟩
  have hJsub : (⋃ c : A, Set.range (pA c)) ⊆
      Set.range fun q : (Σ c : A, Fin (mA c)) => pA q.1 q.2 := by
    rintro x hx
    rw [Set.mem_iUnion] at hx
    obtain ⟨c, k, rfl⟩ := hx
    exact ⟨⟨c, k⟩, rfl⟩
  refine (Cardinal.mk_le_mk_of_subset hJsub).trans (Cardinal.mk_range_le.trans ?_)
  rw [Cardinal.mk_sigma]
  refine (Cardinal.sum_le_sum _ (fun _ => μ) ?_).trans ?_
  · intro c
    calc #(Fin (mA c)) = (mA c : Cardinal) := Cardinal.mk_fin _
      _ ≤ ℵ₀ := Cardinal.natCast_lt_aleph0.le
      _ ≤ μ := hμ
  · rw [Cardinal.sum_const']
    exact (mul_le_mul' hAμ le_rfl).trans (le_of_eq (Cardinal.mul_eq_self hμ))

end Tuples

/-! ## The type-counting property for tuples -/

section CountingN

variable {L : FirstOrder.Language.{0, 0}} {M : Type} [L.Structure M]
  [(L.sum L.skolem₁).Structure M]
  [(FirstOrder.Language.LHom.sumInl : L →ᴸ L.sum L.skolem₁).IsExpansionOn M]
variable {I : Type} [LinearOrder I] [WellFoundedLT I]

/-- **Key lemma, tuple version.**  If a tuple of Skolem terms is evaluated at two strictly
increasing index tuples with the same index codes relative to `J`, the two resulting tuples
realize the same type over any parameter set `A` all of whose elements are values of Skolem terms
at indices from `J`.  This is `Submission.Morley.typeOver_eq_of_idxCode_eq` for tuples. -/
theorem emTypeOverN_eq_of_idxCode_eq {a : I → M}
    (ha : IsOrderIndiscernible (L.sum L.skolem₁) a) {A : Set M} {J : Set I}
    (hAJ : ∀ c : A, ∃ (m : ℕ) (s : (L.sum L.skolem₁).Term (Fin m)) (p : Fin m → I),
      (∀ k, p k ∈ J) ∧ s.realize (a ∘ p) = (c : M))
    {n N : ℕ} (t : Fin n → (L.sum L.skolem₁).Term (Fin N)) {i i' : Fin N → I}
    (hi : StrictMono i) (hi' : StrictMono i')
    (hkey : ∀ k, idxCode J (i k) = idxCode J (i' k)) :
    emTypeOverN L n A (fun k => (t k).realize (a ∘ i)) =
      emTypeOverN L n A (fun k => (t k).realize (a ∘ i')) := by
  classical
  choose mA sA pA hpA hsA using hAJ
  set g : I → I := fun x => if h : ∃ k, i k = x then i' h.choose else x with hgdef
  have hg2 : ∀ k, g (i k) = i' k := by
    intro k
    have h : ∃ k', i k' = i k := ⟨k, rfl⟩
    simp only [hgdef, dif_pos h]
    exact congrArg i' (hi.injective h.choose_spec)
  have hgJ : ∀ x ∈ J, g x = x := by
    intro x hx
    by_cases h : ∃ k, i k = x
    · obtain ⟨k, hk⟩ := h
      subst hk
      rw [hg2 k]
      exact eq_of_idxCode_eq (hkey k) hx
    · simp only [hgdef, dif_neg h]
  have hval : ∀ x ∈ J ∪ Set.range i, (x ∈ J ∧ g x = x) ∨ ∃ k, x = i k ∧ g x = i' k := by
    rintro x (hx | ⟨k, rfl⟩)
    · exact Or.inl ⟨hx, hgJ x hx⟩
    · exact Or.inr ⟨k, rfl, hg2 k⟩
  have hgs : StrictMonoOn g (J ∪ Set.range i) := by
    rintro x hx y hy hxy
    rcases hval x hx with ⟨hxJ, hgx⟩ | ⟨k, rfl, hgx⟩ <;>
      rcases hval y hy with ⟨hyJ, hgy⟩ | ⟨l, rfl, hgy⟩
    · rw [hgx, hgy]; exact hxy
    · rw [hgx, hgy]; exact (lt_iff_of_idxCode_eq (hkey l) hxJ).mp hxy
    · rw [hgx, hgy]; exact (gt_iff_of_idxCode_eq (hkey k) hyJ).mp hxy
    · rw [hgx, hgy]; exact hi' (hi.lt_iff_lt.mp hxy)
  ext p
  obtain ⟨m, φ, c⟩ := p
  simp only [emTypeOverN, Set.mem_setOf_eq]
  set σ : (Fin m ⊕ Fin n) → (L.sum L.skolem₁).Term ↥(J ∪ Set.range i) :=
    Sum.elim
      (fun r => (sA (c r)).relabel fun q =>
        (⟨pA (c r) q, Or.inl (hpA (c r) q)⟩ : ↥(J ∪ Set.range i)))
      (fun k => (t k).relabel fun q => (⟨i q, Or.inr ⟨q, rfl⟩⟩ : ↥(J ∪ Set.range i))) with hσ
  set ψ : (L.sum L.skolem₁).Formula ↥(J ∪ Set.range i) :=
    ((FirstOrder.Language.LHom.sumInl : L →ᴸ L.sum L.skolem₁).onFormula φ).subst σ with hψ
  have key : ∀ v : ↥(J ∪ Set.range i) → M,
      (Formula.Realize ψ v ↔ φ.Realize fun x => (σ x).realize v) := by
    intro v
    rw [hψ]
    exact BoundedFormula.realize_subst.trans (LHom.realize_onFormula _ φ)
  have v1 : (fun x => (σ x).realize fun y : ↥(J ∪ Set.range i) => a (y : I)) =
      Sum.elim (fun r => ((c r : M))) fun k => (t k).realize (a ∘ i) := by
    funext x
    rcases x with r | r
    · simp only [hσ, Sum.elim_inl, Term.realize_relabel]
      exact hsA (c r)
    · simp only [hσ, Sum.elim_inr, Term.realize_relabel]
      rfl
  have v2 : (fun x => (σ x).realize fun y : ↥(J ∪ Set.range i) => a (g (y : I))) =
      Sum.elim (fun r => ((c r : M))) fun k => (t k).realize (a ∘ i') := by
    funext x
    rcases x with r | r
    · simp only [hσ, Sum.elim_inl, Term.realize_relabel]
      rw [← hsA (c r)]
      congr 1
      funext q
      exact congrArg a (hgJ _ (hpA (c r) q))
    · simp only [hσ, Sum.elim_inr, Term.realize_relabel]
      congr 1
      funext q
      exact congrArg a (hg2 q)
  have E1 := key fun y : ↥(J ∪ Set.range i) => a (y : I)
  have E2 := key fun y : ↥(J ∪ Set.range i) => a (g (y : I))
  rw [v1] at E1
  rw [v2] at E2
  rw [← E1, ← E2]
  exact ha.realize_comp g hgs ψ

/-- **The type-counting property for tuples** (version with an explicit index set `J`). -/
theorem card_emTypeOverN_image_le_of_index {a : I → M}
    (hL : L.card ≤ ℵ₀) (ha : IsOrderIndiscernible (L.sum L.skolem₁) a)
    {A : Set M} {J : Set I}
    (hAJ : ∀ c : A, ∃ (m : ℕ) (s : (L.sum L.skolem₁).Term (Fin m)) (p : Fin m → I),
      (∀ k, p k ∈ J) ∧ s.realize (a ∘ p) = (c : M))
    {μ : Cardinal.{0}} (hJ : #J ≤ μ) (hμ : ℵ₀ ≤ μ) (n : ℕ) :
    #(emTypeOverN L n A '' {x : Fin n → M | ∀ k, x k ∈ (EMSub L a : Set M)}) ≤ μ := by
  classical
  haveI : Countable (Σ N, (L.sum L.skolem₁).Functions N) :=
    Cardinal.mk_le_aleph0_iff.mp (card_functions_skolem_le hL)
  set f : ((N : ℕ) × ((Fin n → (L.sum L.skolem₁).Term (Fin N)) ×
      (Fin N → Option J × Option J))) →
      Set ((m : ℕ) × L.Formula (Fin m ⊕ Fin n) × (Fin m → A)) := fun d =>
    if h : ∃ i : Fin d.1 → I, StrictMono i ∧ ∀ k, idxCode J (i k) = d.2.2 k then
      emTypeOverN L n A fun k => (d.2.1 k).realize (a ∘ h.choose)
    else ∅ with hf
  have hsub : emTypeOverN L n A '' {x : Fin n → M | ∀ k, x k ∈ (EMSub L a : Set M)} ⊆
      Set.range f := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨N, t, i, hi, hti⟩ := exists_common_index fun k => hx k
    have hex : ∃ i' : Fin N → I, StrictMono i' ∧ ∀ k, idxCode J (i' k) = idxCode J (i k) :=
      ⟨i, hi, fun _ => rfl⟩
    refine ⟨⟨N, t, fun k => idxCode J (i k)⟩, ?_⟩
    rw [hf]
    simp only [dif_pos hex]
    exact (emTypeOverN_eq_of_idxCode_eq ha hAJ t hex.choose_spec.1 hi
      fun k => hex.choose_spec.2 k).trans (congrArg _ (funext hti))
  refine (Cardinal.mk_le_mk_of_subset hsub).trans (Cardinal.mk_range_le.trans ?_)
  have hOpt : #(Option J) ≤ μ := by
    rw [Cardinal.mk_option]
    exact (add_le_add hJ (Cardinal.one_le_aleph0.trans hμ)).trans
      (le_of_eq (Cardinal.add_eq_self hμ))
  have hK : #(Option J × Option J) ≤ μ := by
    calc #(Option J × Option J) = #(Option J) * #(Option J) := by
          rw [Cardinal.mk_prod]
          simp
      _ ≤ μ * μ := mul_le_mul' hOpt hOpt
      _ = μ := Cardinal.mul_eq_self hμ
  rw [Cardinal.mk_sigma]
  refine (Cardinal.sum_le_sum _ (fun _ => μ) ?_).trans ?_
  · intro N
    have h1 : #(Fin n → (L.sum L.skolem₁).Term (Fin N)) ≤ μ := Cardinal.mk_le_aleph0.trans hμ
    have h2 : #(Fin N → Option J × Option J) ≤ μ :=
      (Cardinal.mk_le_of_injective List.ofFn_injective).trans
        ((Cardinal.mk_list_le_max _).trans (max_le hμ hK))
    calc #((Fin n → (L.sum L.skolem₁).Term (Fin N)) × (Fin N → Option J × Option J))
        = #(Fin n → (L.sum L.skolem₁).Term (Fin N)) * #(Fin N → Option J × Option J) := by
          rw [Cardinal.mk_prod]
          simp
      _ ≤ μ * μ := mul_le_mul' h1 h2
      _ = μ := Cardinal.mul_eq_self hμ
  · rw [Cardinal.sum_const']
    simpa using (Cardinal.mul_eq_max le_rfl hμ).trans_le (le_of_eq (max_eq_right hμ))

/-- **The type-counting property of Ehrenfeucht–Mostowski models, for tuples.**  If `A` is a
subset of the Skolem hull of size at most an infinite cardinal `μ`, then at most `μ` types of
`n`-tuples from the Skolem hull over `A` are realised. -/
theorem card_emTypeOverN_le {a : I → M}
    (hL : L.card ≤ ℵ₀) (ha : IsOrderIndiscernible (L.sum L.skolem₁) a)
    {A : Set M} (hA : A ⊆ (EMSub L a : Set M)) {μ : Cardinal.{0}} (hAμ : #A ≤ μ) (hμ : ℵ₀ ≤ μ)
    (n : ℕ) : #(emTypeOverN L n A '' {x : Fin n → M | ∀ k, x k ∈ (EMSub L a : Set M)}) ≤ μ := by
  obtain ⟨J, hJ, hAJ⟩ := exists_index_set hA hAμ hμ
  exact card_emTypeOverN_image_le_of_index hL ha hAJ hJ hμ n

end CountingN

section EMDataCounting

variable {L : FirstOrder.Language.{0, 0}} {T : L.Theory} {I : Type} [LinearOrder I]
  [WellFoundedLT I]

/-- The tuple type-counting property of `EM(I)`. -/
theorem EMData.card_emTypeOverN_le (d : EMData L T I) (hL : L.card ≤ ℵ₀) {A : Set d.Carrier}
    (hA : A ⊆ (d.toEM : Set d.Carrier)) {μ : Cardinal.{0}} (hAμ : #A ≤ μ) (hμ : ℵ₀ ≤ μ) (n : ℕ) :
    #(emTypeOverN L n A ''
      {x : Fin n → d.Carrier | ∀ k, x k ∈ (d.toEM : Set d.Carrier)}) ≤ μ :=
  Submission.Morley.card_emTypeOverN_le hL d.indiscernible hA hAμ hμ n

end EMDataCounting

/-! ## Reconciling the two encodings of a type over a parameter set -/

section Encoding

variable {L : FirstOrder.Language.{0, 0}} {C : Type} [L.Structure C] [Nonempty C]

/-- **The reconciliation lemma.**  If two `n`-tuples from an elementary substructure `S ≼ C`
satisfy the same `L`-formulas with parameters from `A ⊆ S` *computed in the ambient structure
`C`* — this is `Submission.Morley.emTypeOverN`, the encoding used by the Ehrenfeucht–Mostowski
chapter — then they have the same complete `n`-type over `A` *computed in `S`*, which is the
encoding used by the stability chapter.

Two things happen here: the finitely many parameters occurring in a formula of `L[[A]]` are
extracted into a tuple `Fin m → A` (this is `BoundedFormula.restrictFreeVar`), and realization is
transferred between `S` and `C` along the elementary embedding `S ↪ₑ[L] C`. -/
theorem typeOverN_eq_of_emTypeOverN_eq (S : L.ElementarySubstructure C) (A : Set S) {n : ℕ}
    {b b' : Fin n → S}
    (h : emTypeOverN L n (Subtype.val '' A) (fun k => ((b k : C))) =
      emTypeOverN L n (Subtype.val '' A) fun k => ((b' k : C))) :
    (typeOver A b : CompleteTypeOver L A (Fin n)) = typeOver A b' := by
  classical
  set A' : Set C := Subtype.val '' A with hA'
  set j : A → A' := fun q => ⟨((q : S) : C), ⟨(q : S), q.2, rfl⟩⟩ with hj
  -- Step 1: the ambient-realization statement for arbitrary `L`-formulas with parameters in `A`.
  have key : ∀ χ : L.Formula (A ⊕ Fin n),
      (χ.Realize (Sum.elim (fun q : A => ((j q : C))) fun k => ((b k : C))) ↔
        χ.Realize (Sum.elim (fun q : A => ((j q : C))) fun k => ((b' k : C)))) := by
    intro χ
    set s : Finset A := χ.freeVarFinset.toLeft with hs
    set c : Fin s.card → A' := fun k => j (s.equivFin.symm k) with hc
    set g : χ.freeVarFinset → (Fin s.card ⊕ Fin n) := fun z =>
      match hz : (z : A ⊕ Fin n) with
      | Sum.inl p => Sum.inl (s.equivFin ⟨p, Finset.mem_toLeft.2 (hz ▸ z.2)⟩)
      | Sum.inr w => Sum.inr w with hg
    have hres : ∀ y : Fin n → C,
        (Formula.Realize (χ.restrictFreeVar g)
            (Sum.elim (fun r : Fin s.card => ((c r : C))) y) ↔
          χ.Realize (Sum.elim (fun q : A => ((j q : C))) y)) := by
      intro y
      refine BoundedFormula.realize_restrictFreeVar _ ?_
      rintro ⟨z, hz⟩
      cases z <;> simp [hg, hc, hj]
    have hmem : (⟨s.card, χ.restrictFreeVar g, c⟩ :
        (m : ℕ) × L.Formula (Fin m ⊕ Fin n) × (Fin m → A')) ∈
          emTypeOverN L n A' (fun k => ((b k : C))) ↔
        (⟨s.card, χ.restrictFreeVar g, c⟩ :
        (m : ℕ) × L.Formula (Fin m ⊕ Fin n) × (Fin m → A')) ∈
          emTypeOverN L n A' fun k => ((b' k : C)) := by
      rw [h]
    simp only [emTypeOverN, Set.mem_setOf_eq] at hmem
    rw [hres, hres] at hmem
    exact hmem
  -- Step 2: transfer the realization from `C` down to `S`, and repackage as a complete type.
  refine SetLike.ext fun φ => ?_
  rw [mem_typeOver, mem_typeOver]
  set ψ : (L[[A]]).Formula (Fin n) := Formula.equivSentence.symm φ with hψ
  have hcv : ∀ y : Fin n → S, (Formula.Realize ψ y ↔
      Formula.Realize (BoundedFormula.constantsVarsEquiv ψ)
        (Sum.elim (fun q : A => ((q : S))) y)) := fun y =>
    (BoundedFormula.realize_constantsVarsEquiv (M := S) (L := L) (α := (A : Set S))
      (φ := ψ) (v := y) (xs := default)).symm
  have helem : ∀ (χ : L.Formula (A ⊕ Fin n)) (y : Fin n → S),
      (Formula.Realize χ (Sum.elim (fun q : A => ((q : S))) y) ↔
        Formula.Realize χ
          (Sum.elim (fun q : A => ((j q : C))) fun k => ((y k : C)))) := by
    intro χ y
    have hmap := S.subtype.map_formula χ (Sum.elim (fun q : A => ((q : S))) y)
    rw [Sum.comp_elim] at hmap
    exact hmap.symm
  rw [hcv b, hcv b', helem _ b, helem _ b']
  exact key _

end Encoding

/-! ## The Ehrenfeucht–Mostowski type-counting bound -/

section Bound

variable {L : FirstOrder.Language.{0, 0}}

/-- Only countably many complete `n`-types over a countable parameter set of an
Ehrenfeucht–Mostowski model are realised in it. -/
theorem card_realizedTypes_toEM_le {T : L.Theory} {I : Type} [LinearOrder I] [WellFoundedLT I]
    (hL : L.card ≤ ℵ₀) (d : EMData L T I) (n : ℕ) (A : Set d.toEM) (hA : #A ≤ ℵ₀) :
    #((paramTheory L A).realizedTypes d.toEM (Fin n)) ≤ ℵ₀ := by
  classical
  set A' : Set d.Carrier := Subtype.val '' A with hA'
  have hA'sub : A' ⊆ (d.toEM : Set d.Carrier) := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hA'card : #A' ≤ ℵ₀ := by
    rw [hA', Cardinal.mk_image_eq Subtype.val_injective]
    exact hA
  have hbound := d.card_emTypeOverN_le hL hA'sub hA'card le_rfl n
  have hchoice : ∀ p : ((paramTheory L A).realizedTypes d.toEM (Fin n)),
      ∃ x : Fin n → d.toEM, (typeOver A x : CompleteTypeOver L A (Fin n)) =
        (p : CompleteTypeOver L A (Fin n)) := fun p => mem_realizedTypes_iff.1 p.2
  choose w hw using hchoice
  refine le_trans (Cardinal.mk_le_of_injective
    (f := fun p => (⟨emTypeOverN L n A' fun k => ((w p k : d.Carrier)),
      ⟨fun k => ((w p k : d.Carrier)), fun k => (w p k).2, rfl⟩⟩ :
        ↥(emTypeOverN L n A' ''
          {x : Fin n → d.Carrier | ∀ k, x k ∈ (d.toEM : Set d.Carrier)}))) ?_) hbound
  intro p q hpq
  have h1 : emTypeOverN L n A' (fun k => ((w p k : d.Carrier))) =
      emTypeOverN L n A' fun k => ((w q k : d.Carrier)) := congrArg Subtype.val hpq
  exact Subtype.ext (by rw [← hw p, ← hw q]; exact typeOverN_eq_of_emTypeOverN_eq d.toEM A h1)

/-- **The Ehrenfeucht–Mostowski type-counting bound**, discharging the hypothesis
`Submission.Morley.EMTypeBound` of `Submission.Morley.isOmegaStable_of_categorical`.

Given a satisfiable theory with only infinite models in a countable language and an infinite
cardinal `κ`, build the Ehrenfeucht–Mostowski model over the well-ordered index set `κ.ord.ToType`
(`Submission.Morley.exists_emData_injective`).  It is a model of `T` of size exactly `κ`, and by
`Submission.Morley.card_realizedTypes_toEM_le` it realises only countably many `n`-types over any
countable parameter set. -/
theorem emTypeBound (L : FirstOrder.Language.{0, 0}) (hL : L.card ≤ ℵ₀) : EMTypeBound L := by
  intro n T _ hT hInf κ hκ
  obtain ⟨d, hinj⟩ := exists_emData_injective T hT hInf (Cardinal.ord κ).ToType
  have hI : #((Cardinal.ord κ).ToType) = κ := Cardinal.mk_ord_toType κ
  have hcard : #(d.toEM) = κ := by
    refine le_antisymm ?_ ?_
    · refine (d.card_toEM_le hL).trans ?_
      rw [hI]
      exact max_le hκ le_rfl
    · calc κ = #((Cardinal.ord κ).ToType) := hI.symm
        _ ≤ #(d.toEM) := d.card_le_card_toEM hinj
  exact ⟨FirstOrder.Language.Theory.ModelType.of T d.toEM, hcard,
    fun A hA => card_realizedTypes_toEM_le hL d n A hA⟩

/-- The Ehrenfeucht–Mostowski type-counting bound for `1`-types, which is the form consumed by
`Submission.Morley.omegaStable_of_categorical` and `Submission.Morley.stable_of_categorical`. -/
theorem emTypeBoundAt_one (L : FirstOrder.Language.{0, 0}) (hL : L.card ≤ ℵ₀) :
    EMTypeBoundAt L 1 := emTypeBound L hL 1

end Bound

end Submission.Morley
