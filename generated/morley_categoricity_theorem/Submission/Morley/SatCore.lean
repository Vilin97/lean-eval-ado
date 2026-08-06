import Mathlib
import Submission.Morley.UniformFinite
import Submission.Morley.IndepIndisc
import Submission.Morley.PrimeBig

/-!
# The saturation principle: passing between a model and an elementary extension

`Submission/Morley/StronglyMinimal.lean` and `Submission/Morley/IndepIndisc.lean` develop the
Baldwin–Lachlan analysis of a minimal set *inside one fixed structure*, in the language of
`FirstOrder.Language.Set.Definable`.  The proof of `Submission.Morley.SaturationPrinciple`
however has to compare three structures — the model `M`, an elementary extension `Ω` of it
realising the given type, and a small `N ≼ Ω` — and definability is not a notion that transports
between them.  This file supplies the transport, which has to happen at the level of *formulas*.

## Main definitions

* `Submission.Morley.splitBound φ ψ k`: the formula, in the parameters of `φ`, saying that for
  *every* choice of parameters for `ψ` one of the two halves into which `ψ` cuts the fibre of `φ`
  has fewer than `k` elements.
* `Submission.Morley.UnifMinimal φ c`: the fibre of `φ` over `c` is infinite and every `ψ` cuts
  it with a uniform bound.  Being a conjunction of first-order conditions on `c`, this transports
  along elementary embeddings in *both* directions, which `Submission.Morley.IsMinimalSet` does
  not.
* `Submission.Morley.UnifFinite L M`: every formula has a uniform bound on the size of its finite
  fibres.  This is what the absence of Vaughtian pairs supplies, by
  `Submission.Morley.exists_bound_ncard_fiber`.
* `Submission.Morley.elemRange f`: the range of an elementary embedding, as an elementary
  substructure.

## Main results

* `Submission.Morley.exists_formula_fiber`: a set definable over a finite parameter set is the
  fibre of a formula — the passage from `Set.Definable` to syntax.
* `Submission.Morley.isMinimalSet_of_unifMinimal`, `Submission.Morley.unifMinimal_map_iff` and
  `Submission.Morley.unifMinimal_of_isMinimalSet`: **a minimal set stays minimal in every
  elementary extension**, once the fibres of every formula are uniformly bounded.  This is the
  step for which `Submission/Morley/UniformFinite.lean` was needed; a minimal set of an arbitrary
  model is *not* minimal in an elementary extension without it.
* `Submission.Morley.mem_alg_of_elementaryEmbedding` and
  `Submission.Morley.indep_image_of_elementaryEmbedding`: algebraic closure and independence
  reflect along elementary embeddings.
* `Submission.Morley.typeOver_eq_of_restrict`: a type is determined by the entries of the tuple
  that are not already parameters.  This is what reduces the elementarity of the map
  `M₁ ∪ B_N → M` to indiscernibility of the two bases.
* `Submission.Morley.exists_extension_realizing_type`: a complete `1`-type over a subset of `M`
  is realised in an elementary extension of `M`, with each of its formulas presented by an
  `L`-formula whose parameters are indexed by the parameter set.
-/

namespace Submission.Morley

open Cardinal Set FirstOrder Language Theory

variable {L : FirstOrder.Language.{0, 0}}

/-! ## Definable sets as fibres of formulas -/

section Conversion

variable {M : Type} [L.Structure M]

/-- **A set definable over a finite parameter set is the fibre of a formula.** -/
theorem exists_formula_fiber {A : Set M} {X : Set M} (h : A.Definable₁ L X) :
    ∃ (r : ℕ) (ψ : L.Formula (Fin r ⊕ Fin 1)) (d : Fin r → M),
      (∀ i, d i ∈ A) ∧ X = fiber ψ d := by
  classical
  rw [Set.Definable₁, Set.definable_iff_finitely_definable] at h
  obtain ⟨A₀, hA₀, hdef⟩ := h
  rw [Set.definable_iff_exists_formula_sum] at hdef
  obtain ⟨χ, hχ⟩ := hdef
  set e : ((A₀ : Set M) : Type) ≃ Fin A₀.card := (A₀.equivFin.trans (Equiv.refl _)) with he
  refine ⟨A₀.card, χ.relabel (Sum.map e id), fun i => ((e.symm i : M)), fun i => hA₀ (e.symm i).2,
    ?_⟩
  ext x
  have hx : x ∈ X ↔ (fun _ : Fin 1 => x) ∈ {v : Fin 1 → M | v 0 ∈ X} := by simp
  rw [hx, hχ]
  simp only [Set.mem_setOf_eq, mem_fiber_iff, Formula.realize_relabel]
  congr! 1
  ext (a | i)
  · simp
  · simp

end Conversion

/-! ## Uniform minimality -/

section UnifMinimal

/-- The formula, in the parameters of `φ`, saying that for every choice of parameters for `ψ` one
of the two halves into which `ψ` cuts the fibre of `φ` has fewer than `k` elements. -/
noncomputable def splitBound {m r : ℕ} (φ : L.Formula (Fin m ⊕ Fin 1))
    (ψ : L.Formula (Fin r ⊕ Fin 1)) (k : ℕ) : L.Formula (Fin m) :=
  Formula.iAlls (Fin r)
    (Formula.not (atLeastF
        ((φ.relabel (Sum.map Sum.inl id)) ⊓ (ψ.relabel (Sum.map Sum.inr id))) k) ⊔
      Formula.not (atLeastF
        ((φ.relabel (Sum.map Sum.inl id)) ⊓ Formula.not (ψ.relabel (Sum.map Sum.inr id))) k))

variable {M : Type} [L.Structure M]

/-- The left half of the split, as a fibre. -/
theorem fiber_splitL {m r : ℕ} (φ : L.Formula (Fin m ⊕ Fin 1)) (ψ : L.Formula (Fin r ⊕ Fin 1))
    (c : Fin m → M) (d : Fin r → M) :
    fiber ((φ.relabel (Sum.map Sum.inl id)) ⊓ (ψ.relabel (Sum.map Sum.inr id)))
        (Sum.elim c d) = fiber φ c ∩ fiber ψ d := by
  ext x
  simp only [mem_fiber_iff, Formula.realize_inf, Formula.realize_relabel, Set.mem_inter_iff]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · convert h1 using 2
      ext (i | i) <;> simp
    · convert h2 using 2
      ext (i | i) <;> simp
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · convert h1 using 2
      ext (i | i) <;> simp
    · convert h2 using 2
      ext (i | i) <;> simp

/-- The right half of the split, as a fibre. -/
theorem fiber_splitR {m r : ℕ} (φ : L.Formula (Fin m ⊕ Fin 1)) (ψ : L.Formula (Fin r ⊕ Fin 1))
    (c : Fin m → M) (d : Fin r → M) :
    fiber ((φ.relabel (Sum.map Sum.inl id)) ⊓ Formula.not (ψ.relabel (Sum.map Sum.inr id)))
        (Sum.elim c d) = fiber φ c \ fiber ψ d := by
  ext x
  simp only [mem_fiber_iff, Formula.realize_inf, Formula.realize_not, Formula.realize_relabel,
    Set.mem_sdiff]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · convert h1 using 2
      ext (i | i) <;> simp
    · intro hc
      refine h2 ?_
      convert hc using 2
      ext (i | i) <;> simp
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · convert h1 using 2
      ext (i | i) <;> simp
    · intro hc
      refine h2 ?_
      convert hc using 2
      ext (i | i) <;> simp

/-- `UnifMinimal φ c` says that the fibre of `φ` over `c` is infinite and that, for every formula
`ψ`, the two halves into which `ψ` cuts it are *uniformly* small on one side.  This is the
first-order — hence elementarily transferable — form of minimality. -/
def UnifMinimal {m : ℕ} (φ : L.Formula (Fin m ⊕ Fin 1)) (c : Fin m → M) : Prop :=
  (fiber φ c).Infinite ∧
    ∀ (r : ℕ) (ψ : L.Formula (Fin r ⊕ Fin 1)), ∃ n : ℕ, (splitBound φ ψ (n + 1)).Realize c

/-- **Uniform minimality implies minimality.** -/
theorem isMinimalSet_of_unifMinimal {m : ℕ} {φ : L.Formula (Fin m ⊕ Fin 1)} {c : Fin m → M}
    (h : UnifMinimal φ c) : IsMinimalSet L (fiber φ c) := by
  refine ⟨h.1, fun X hX => ?_⟩
  obtain ⟨r, ψ, d, -, rfl⟩ := exists_formula_fiber hX
  obtain ⟨n, hn⟩ := h.2 r ψ
  rw [splitBound, Formula.realize_iAlls] at hn
  have hd := hn d
  rw [Formula.realize_sup, Formula.realize_not, Formula.realize_not] at hd
  have hce : (fun a => Sum.elim c d a) = Sum.elim c d := rfl
  rw [hce] at hd
  rcases hd with hd | hd
  · exact Or.inl (by
      rw [← fiber_splitL φ ψ c d]
      exact (finite_ncard_le_of_not_realize_atLeastF hd).1)
  · exact Or.inr (by
      rw [← fiber_splitR φ ψ c d]
      exact (finite_ncard_le_of_not_realize_atLeastF hd).1)

/-- **Uniform minimality transfers along elementary embeddings**, in both directions. -/
theorem unifMinimal_map_iff {Ω : Type} [L.Structure Ω] (f : M ↪ₑ[L] Ω) {m : ℕ}
    {φ : L.Formula (Fin m ⊕ Fin 1)} {c : Fin m → M} :
    UnifMinimal φ (fun i => f (c i)) ↔ UnifMinimal φ c := by
  have hinf : (fiber φ fun i => f (c i)).Infinite ↔ (fiber φ c).Infinite := by
    rw [infinite_fiber_iff_forall_realize_atLeastF, infinite_fiber_iff_forall_realize_atLeastF]
    exact forall_congr' fun k => f.map_formula (atLeastF φ k) c
  refine and_congr hinf (forall_congr' fun r => forall_congr' fun ψ => exists_congr fun n => ?_)
  exact f.map_formula (splitBound φ ψ (n + 1)) c

/-- Uniform finiteness of the fibres of every formula: for each formula there is a bound on the
size of its *finite* fibres.  This is what the absence of Vaughtian pairs supplies. -/
def UnifFinite (L : FirstOrder.Language.{0, 0}) (M : Type) [L.Structure M] : Prop :=
  ∀ (α : Type) (χ : L.Formula (α ⊕ Fin 1)), ∃ k : ℕ, ∀ z : α → M,
    (fiber χ z).Finite → (fiber χ z).ncard ≤ k

/-- **Minimality plus uniform finiteness gives uniform minimality.** -/
theorem unifMinimal_of_isMinimalSet (huf : UnifFinite L M) {m : ℕ}
    {φ : L.Formula (Fin m ⊕ Fin 1)} {c : Fin m → M} (h : IsMinimalSet L (fiber φ c)) :
    UnifMinimal φ c := by
  refine ⟨h.1, fun r ψ => ?_⟩
  obtain ⟨k₁, hk₁⟩ := huf (Fin m ⊕ Fin r)
    ((φ.relabel (Sum.map Sum.inl id)) ⊓ (ψ.relabel (Sum.map Sum.inr id)))
  obtain ⟨k₂, hk₂⟩ := huf (Fin m ⊕ Fin r)
    ((φ.relabel (Sum.map Sum.inl id)) ⊓ Formula.not (ψ.relabel (Sum.map Sum.inr id)))
  refine ⟨max k₁ k₂, ?_⟩
  rw [splitBound, Formula.realize_iAlls]
  intro d
  show (Formula.not _ ⊔ Formula.not _).Realize (Sum.elim c d)
  rw [Formula.realize_sup, Formula.realize_not, Formula.realize_not]
  rcases h.2 (fiber ψ d) ((definable₁_fiber ψ d).mono (Set.subset_univ _)) with hfin | hfin
  · refine Or.inl (not_realize_atLeastF_of_ncard_le ?_ ?_)
    · rw [fiber_splitL]; exact hfin
    · exact le_trans (hk₁ _ (by rw [fiber_splitL]; exact hfin)) (le_max_left _ _)
  · refine Or.inr (not_realize_atLeastF_of_ncard_le ?_ ?_)
    · rw [fiber_splitR]; exact hfin
    · exact le_trans (hk₂ _ (by rw [fiber_splitR]; exact hfin)) (le_max_right _ _)

end UnifMinimal

/-! ## Algebraic closure along an elementary embedding -/

section AlgTransfer

variable {M Ω : Type} [L.Structure M] [L.Structure Ω]

/-- The preimage of a set definable over the image of `X` is definable over `X`. -/
theorem definable₁_preimage_of_elementaryEmbedding (f : M ↪ₑ[L] Ω) {X : Set M} {S : Set Ω}
    (h : ((fun x => f x) '' X).Definable₁ L S) :
    X.Definable₁ L ((fun x : M => f x) ⁻¹' S) := by
  classical
  obtain ⟨r, ψ, d, hd, rfl⟩ := exists_formula_fiber h
  choose d' hd' using fun i => hd i
  have hset : (fun x : M => f x) ⁻¹' fiber ψ d = fiber ψ (fun i => d' i) := by
    ext x
    simp only [Set.mem_preimage, mem_fiber_iff]
    rw [← f.map_formula ψ (Sum.elim (fun i => d' i) fun _ => x)]
    congr! 1
    ext (i | i)
    · simpa using (hd' i).2.symm
    · rfl
  rw [hset]
  refine (definable₁_fiber ψ (fun i => d' i)).mono ?_
  rintro _ ⟨i, rfl⟩
  exact (hd' i).1

/-- **Algebraic closure reflects along an elementary embedding.** -/
theorem mem_alg_of_elementaryEmbedding (f : M ↪ₑ[L] Ω) {X : Set M} {x : M}
    (h : f x ∈ Alg L ((fun y => f y) '' X)) : x ∈ Alg L X := by
  obtain ⟨S, hS, hfin, hmem⟩ := h
  refine ⟨(fun y : M => f y) ⁻¹' S, definable₁_preimage_of_elementaryEmbedding f hS, ?_, hmem⟩
  exact hfin.preimage (f.injective.injOn)

/-- **Independence is preserved by elementary embeddings.** -/
theorem indep_image_of_elementaryEmbedding (f : M ↪ₑ[L] Ω) {C B : Set M} (h : Indep L C B) :
    Indep L ((fun y => f y) '' C) ((fun y => f y) '' B) := by
  rintro _ ⟨b, hb, rfl⟩ hmem
  refine h b hb (mem_alg_of_elementaryEmbedding f (alg_mono ?_ hmem))
  rintro y (⟨z, hz, rfl⟩ | ⟨⟨z, hz, rfl⟩, hne⟩)
  · exact ⟨z, Set.mem_union_left _ hz, rfl⟩
  · refine ⟨z, Set.mem_union_right _ ⟨hz, fun hcon => hne ?_⟩, rfl⟩
    rw [Set.mem_singleton_iff] at hcon ⊢
    rw [hcon]

/-- Fibres are preserved and reflected by elementary embeddings. -/
theorem mem_fiber_map_iff (f : M ↪ₑ[L] Ω) {α : Type} (χ : L.Formula (α ⊕ Fin 1)) (z : α → M)
    (x : M) : f x ∈ fiber χ (fun i => f (z i)) ↔ x ∈ fiber χ z := by
  have hcomp : (Sum.elim (fun i => f (z i)) fun _ : Fin 1 => f x)
      = (f : M → Ω) ∘ Sum.elim z fun _ : Fin 1 => x := by
    funext w
    rcases w with i | i <;> rfl
  rw [mem_fiber_iff, mem_fiber_iff, hcomp, f.map_formula]

/-- **The range of an elementary embedding is an elementary substructure.** -/
def elemRange (f : M ↪ₑ[L] Ω) : L.ElementarySubstructure Ω where
  toSubstructure := f.toEmbedding.toHom.range
  isElementary' := by
    intro n ψ x
    have hval : ((Subtype.val : ↥(f.toEmbedding.toHom.range) → Ω) ∘ x)
        = (f : M → Ω) ∘ fun i => f.toEmbedding.equivRange.symm (x i) := by
      funext i
      have h1 := Embedding.equivRange_apply f.toEmbedding
        (f.toEmbedding.equivRange.symm (x i))
      rw [FirstOrder.Language.Equiv.apply_symm_apply] at h1
      simpa using h1
    have h3 : (⇑f.toEmbedding.equivRange ∘ fun i => f.toEmbedding.equivRange.symm (x i)) = x := by
      funext i
      exact FirstOrder.Language.Equiv.apply_symm_apply _ _
    rw [hval, f.map_formula ψ fun i => f.toEmbedding.equivRange.symm (x i),
      ← StrongHomClass.realize_formula (g := f.toEmbedding.equivRange) ψ
        (v := fun i => f.toEmbedding.equivRange.symm (x i)), h3]

@[simp]
theorem coe_elemRange (f : M ↪ₑ[L] Ω) :
    ((elemRange f : L.ElementarySubstructure Ω) : Set Ω) = Set.range (f : M → Ω) := by
  ext y
  exact ⟨fun ⟨x, hx⟩ => ⟨x, hx⟩, fun ⟨x, hx⟩ => ⟨x, hx⟩⟩

end AlgTransfer

/-! ## Gluing types along a splitting of the variables -/

section Glue

variable {Ω : Type} [L.Structure Ω] [Nonempty Ω]

/-- **Types are determined by the entries that are not parameters.**  If two tuples agree outside
a set `S` of indices, and take values in `C` there, then they realise the same type over `C` as
soon as their restrictions to `S` do. -/
theorem typeOver_eq_of_restrict {C : Set Ω} {k : ℕ} {w w' : Fin k → Ω} (S : Set (Fin k))
    (hout : ∀ i, i ∉ S → w i = w' i) (houtC : ∀ i, i ∉ S → w i ∈ C)
    (hin : (typeOver C (fun i : ↥S => w (i : Fin k)) : CompleteTypeOver L C ↥S)
      = typeOver C fun i : ↥S => w' (i : Fin k)) :
    (typeOver C w : CompleteTypeOver L C (Fin k)) = typeOver C w' := by
  classical
  rw [typeOver_eq_iff_forall_definable] at hin ⊢
  intro s hs
  rw [Set.definable_iff_exists_formula_sum] at hs
  obtain ⟨ψ, rfl⟩ := hs
  set g : ↥C ⊕ Fin k → ↥C ⊕ ↥S := fun z =>
    match z with
    | Sum.inl cc => Sum.inl cc
    | Sum.inr i => if h : i ∈ S then Sum.inr ⟨i, h⟩ else Sum.inl ⟨w i, houtC i h⟩ with hg
  have hdef : C.Definable L {y : ↥S → Ω | (ψ.relabel g).Realize (Sum.elim Subtype.val y)} :=
    Set.definable_iff_exists_formula_sum.2 ⟨ψ.relabel g, rfl⟩
  have hkey : ∀ v : Fin k → Ω, (∀ i, i ∉ S → v i = w i) →
      (v ∈ {u : Fin k → Ω | ψ.Realize (Sum.elim Subtype.val u)} ↔
        (fun i : ↥S => v (i : Fin k)) ∈
          {y : ↥S → Ω | (ψ.relabel g).Realize (Sum.elim Subtype.val y)}) := by
    intro v hv
    simp only [Set.mem_setOf_eq, Formula.realize_relabel]
    congr! 1
    funext z
    rcases z with cc | i
    · rfl
    · by_cases hi : i ∈ S
      · simp [hg, hi]
      · simp [hg, hi, hv i hi]
  rw [hkey w fun _ _ => rfl, hkey w' fun i hi => (hout i hi).symm]
  exact hin _ hdef

end Glue

/-! ## Realising a type in an elementary extension -/

section Realizing

variable {M : Type} [L.Structure M]

omit [L.Structure M] in
/-- Reading a formula with parameters indexed by `A` as one with parameters indexed by `M`. -/
theorem fiber_relabel_val {A : Set M} (χ : L.Formula (↥A ⊕ Fin 1)) {Ω : Type} [L.Structure Ω]
    (g : M → Ω) :
    fiber (χ.relabel (Sum.map (Subtype.val : ↥A → M) id)) g
      = fiber χ fun x : ↥A => g (x : M) := by
  ext y
  simp only [mem_fiber_iff, Formula.realize_relabel]
  congr! 1
  ext (i | i)
  · rfl
  · rfl

/-- **Finite satisfiability of a complete type in the model it lives over.** -/
theorem exists_mem_forall_realSet [Nonempty M] {A : Set M} (p : S₁ L A)
    (t : Finset (Form1 L A)) (ht : ∀ φ ∈ t, φ ∈ p) :
    ∃ a : M, ∀ φ ∈ t, a ∈ realSet A φ := by
  classical
  have key : ∀ s : Finset (Form1 L A), (∀ φ ∈ s, φ ∈ p) →
      ∃ χ : Form1 L A, χ ∈ p ∧ ∀ φ ∈ s, realSet A χ ⊆ realSet A φ := by
    intro s
    induction s using Finset.induction with
    | empty => exact fun _ => ⟨⊤, top_mem_completeType p, by simp⟩
    | @insert ψ s _ IH =>
      intro hall
      obtain ⟨χ, hχ, hsub⟩ := IH fun φ hφ => hall φ (Finset.mem_insert_of_mem hφ)
      refine ⟨χ ⊓ ψ, (Theory.CompleteType.inf_mem_iff _ _ _).2
        ⟨hχ, hall ψ (Finset.mem_insert_self ψ s)⟩, fun φ hφ => ?_⟩
      rw [realSet_inf]
      rcases Finset.mem_insert.1 hφ with rfl | hφ'
      · exact Set.inter_subset_right
      · exact Set.inter_subset_left.trans (hsub φ hφ')
  obtain ⟨χ, hχ, hsub⟩ := key t ht
  obtain ⟨a, ha⟩ := exists_mem_typeOfElem_of_mem hχ
  exact ⟨a, fun φ hφ => hsub φ hφ (mem_realSet.2 ha)⟩

/-- **A complete `1`-type over a subset of `M` is realised in an elementary extension of `M`.**

The type is presented through a choice of `L`-formula, with parameters indexed by `A`, for each of
its formulas; this is what makes the realisation transportable to the elementary extension. -/
theorem exists_extension_realizing_type {T : L.Theory} (M : T.ModelType.{0, 0, 0}) (A : Set M)
    (p : S₁ L A) :
    ∃ (Ω : T.ModelType.{0, 0, 0}) (F : (M : Type) ↪ₑ[L] Ω) (a : Ω)
      (rep : Form1 L A → L.Formula (↥A ⊕ Fin 1)),
      (∀ φ : Form1 L A, realSet A φ = fiber (rep φ) (Subtype.val : ↥A → M)) ∧
        ∀ φ ∈ p, a ∈ fiber (rep φ) fun x : ↥A => F (x : M) := by
  classical
  have hch : ∀ φ : Form1 L A, ∃ χ : L.Formula (↥A ⊕ Fin 1),
      realSet A φ = fiber χ (Subtype.val : ↥A → M) := by
    intro φ
    have hd := definable₁_realSet A φ
    rw [Set.Definable₁, Set.definable_iff_exists_formula_sum] at hd
    obtain ⟨χ, hχ⟩ := hd
    refine ⟨χ, ?_⟩
    ext x
    have hx : x ∈ realSet A φ ↔ (fun _ : Fin 1 => x) ∈ {v : Fin 1 → M | v 0 ∈ realSet A φ} := by
      simp
    rw [hx, hχ]
    exact Iff.rfl
  choose rep hrep using hch
  obtain ⟨B, instB, F, b, hb⟩ :=
    exists_elementaryExtension_realizing (A := (M : Type)) (ι := Unit)
      (fun _ => (fun φ : Form1 L A => (rep φ).relabel (Sum.map (Subtype.val : ↥A → M) id)) ''
        {φ : Form1 L A | φ ∈ p})
      (by
        rintro - t htP
        have hpick : ∀ χ : L.Formula ((M : Type) ⊕ Fin 1), χ ∈ t →
            ∃ φ : Form1 L A, φ ∈ p ∧
              (rep φ).relabel (Sum.map (Subtype.val : ↥A → M) id) = χ := by
          intro χ hχ
          obtain ⟨φ, hφ, hEq⟩ := htP (Finset.mem_coe.2 hχ)
          exact ⟨φ, hφ, hEq⟩
        choose pick hpick1 hpick2 using hpick
        have hex := exists_mem_forall_realSet p (t.attach.image fun x => pick x.1 x.2)
          (by
            intro φ hφ
            simp only [Finset.mem_image, Finset.mem_attach, true_and] at hφ
            obtain ⟨x, rfl⟩ := hφ
            exact hpick1 x.1 x.2)
        obtain ⟨a, ha⟩ := hex
        refine ⟨a, fun χ hχ => ?_⟩
        have hmem : pick χ hχ ∈ t.attach.image fun x => pick x.1 x.2 :=
          Finset.mem_image.2 ⟨⟨χ, hχ⟩, Finset.mem_attach _ _, rfl⟩
        have hax := ha _ hmem
        rw [hrep (pick χ hχ), mem_fiber_iff] at hax
        rw [← hpick2 χ hχ, Formula.realize_relabel]
        convert hax using 2
        ext (i | i) <;> rfl)
  letI := instB
  haveI : Nonempty B := ⟨F (Classical.arbitrary (M : Type))⟩
  haveI : B ⊨ T := F.elementarilyEquivalent.theory_model
  refine ⟨⟨B⟩, F, b (), rep, hrep, fun φ hφ => ?_⟩
  have h1 := hb () _ ⟨φ, hφ, rfl⟩
  rw [Formula.realize_relabel] at h1
  rw [mem_fiber_iff]
  convert h1 using 2
  ext (i | i) <;> rfl

end Realizing

end Submission.Morley
