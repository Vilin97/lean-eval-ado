import Mathlib
import Submission.Morley.SatCore

/-!
# The saturation principle

This file proves `Submission.Morley.SaturationPrinciple`: an `ω`-stable theory in a countable
language without Vaughtian pairs has all its models of uncountable cardinality saturated.  It is
the last input that `Submission/Morley/Assembly.lean` leaves as a hypothesis, so
`Submission.Morley.morley_categoricity_aleph1'` — Morley's categoricity theorem at `ℵ₁` — becomes
unconditional.

## The argument

Let `M ⊨ T` with `ℵ₀ < #M`, let `A ⊆ M` with `#A < #M`, and let `p ∈ S₁(A)`.

1. `Submission.Morley.exists_isMinimalSet` produces a minimal set of `M`; written as the fibre of
   a formula `φ` over a tuple `c` of parameters.  Because `T` has no Vaughtian pairs, the fibres
   of every formula are uniformly bounded (`Submission.Morley.exists_bound_ncard_fiber`), so `φ`
   is *uniformly* minimal and therefore stays minimal in every elementary extension
   (`Submission.Morley.unifMinimal_map_iff`).  This is the point at which a bare minimal set is
   not enough: minimality of a definable set is not an elementary property.
2. `Submission.Morley.exists_extension_realizing_type` realises `p` by an element `a` of an
   elementary extension `Ω` of `M`.
3. Downward Löwenheim–Skolem gives `M₁ ≼ M` containing `A` and `c` with `#M₁ = #A + ℵ₀ < #M`,
   and `Ns ≼ Ω` of the same size containing the image of `M₁` and the point `a`.
4. Inside `M`, a maximal `M₁`-independent subset `BM` of the minimal set has `#BM = #M`
   (`Submission.Morley.mk_maximal_indep_eq`).  Inside `Ns`, a maximal independent subset `BN` of
   the minimal set spans it, so by `Submission.Morley.eq_univ_of_maximal_indep_subset` — the
   *strong* form of the absence of Vaughtian pairs — no proper elementary substructure of `Ns`
   contains it.  Hence the prime model over it, which exists by
   `Submission.Morley.exists_prime_of_isOmegaStable'`, is the whole of `Ns`.
5. Since `#BN ≤ #Ns < #M = #BM`, the set `BN` injects into `BM`.  By
   `Submission.Morley.typeOver_eq_of_indep_of_injOn`, applied inside `Ω`, that injection together
   with the identity of `M₁` is a partial elementary map, and primality extends it to an
   elementary embedding of `Ns` into `M` fixing `M₁`.  The image of `a` realises `p` in `M`.

## Main results

* `Submission.Morley.isSaturated_of_not_hasVaughtianPair`: the saturation principle.
* `Submission.Morley.saturationPrinciple`: the same, packaged as
  `Submission.Morley.SaturationPrinciple`.
* `Submission.Morley.morley_categoricity_aleph1'`: **Morley's categoricity theorem at `ℵ₁`**,
  unconditionally.
* `Submission.Morley.morley_categoricity'`: Morley's categoricity theorem, with two-cardinal
  transfer for `ω`-stable theories as the only remaining hypothesis.
-/

namespace Submission.Morley

open Cardinal Set FirstOrder Language Theory

section Main

variable {L : FirstOrder.Language.{0, 0}}

/-- **The saturation principle.**

An `ω`-stable theory in a countable language without Vaughtian pairs has all its models of
uncountable cardinality saturated. -/
theorem isSaturated_of_not_hasVaughtianPair (hL : L.card ≤ ℵ₀) {T : L.Theory}
    (hos : IsOmegaStable.{0, 0, 0} T) (hvp : ¬HasVaughtianPair T)
    (M : T.ModelType.{0, 0, 0}) (hM : ℵ₀ < #(M : Type)) : IsSaturated M := by
  classical
  haveI : Infinite (M : Type) := Cardinal.infinite_iff.2 hM.le
  obtain ⟨D, hDmin, hDdef⟩ := exists_isMinimalSet hos.omegaStable M inferInstance
  obtain ⟨mc, φ, c, -, rfl⟩ := exists_formula_fiber hDdef
  have huf : UnifFinite L (M : Type) := fun α χ => exists_bound_ncard_fiber hL hvp M χ
  have hUM : UnifMinimal φ c := unifMinimal_of_isMinimalSet huf hDmin
  intro A hA p
  -- an elementary extension of `M` realising `p`
  obtain ⟨Ω, F, a, rep, hrep, ha⟩ := exists_extension_realizing_type M A p
  have hUMΩ : UnifMinimal φ (fun i => F (c i)) := (unifMinimal_map_iff F).2 hUM
  have hminΩ : IsMinimalSet L (fiber φ fun i => F (c i)) := isMinimalSet_of_unifMinimal hUMΩ
  have hMΩ : #(M : Type) ≤ #(Ω : Type) := Cardinal.mk_le_of_injective F.injective
  -- a small elementary substructure of `M` containing `A` and the parameters of the minimal set
  have hlamM : #A + ℵ₀ < #(M : Type) := Cardinal.add_lt_of_lt hM.le hA hM
  have hunion : #(A ∪ Set.range c : Set (M : Type)) ≤ #A + ℵ₀ := by
    refine (Cardinal.mk_union_le _ _).trans (add_le_add le_rfl ?_)
    exact (Cardinal.lt_aleph0_iff_set_finite.2 (Set.finite_range c)).le
  obtain ⟨M₁, hM₁sub, hM₁card⟩ := exists_elementarySubstructure_card_eq L
    (A ∪ Set.range c) (#A + ℵ₀) le_add_self
    (by simpa using hunion) (by simpa using hL.trans le_add_self)
    (by simpa using hlamM.le)
  simp only [Cardinal.lift_id] at hM₁card
  have hAM₁ : A ⊆ (M₁ : Set (M : Type)) := Set.subset_union_left.trans hM₁sub
  have hcM₁ : ∀ i, c i ∈ (M₁ : Set (M : Type)) := fun i => hM₁sub (Or.inr ⟨i, rfl⟩)
  have hM₁mk : #((M₁ : Set (M : Type)) : Type) = #A + ℵ₀ := by
    rw [← hM₁card]
    exact Cardinal.mk_congr (Equiv.refl _)
  have hM₁lt : #((M₁ : Set (M : Type)) : Type) < #(M : Type) := by rw [hM₁mk]; exact hlamM
  -- a basis of the minimal set of `M` over `M₁`
  have hDCM₁ : (M₁ : Set (M : Type)).Definable₁ L (fiber φ c) :=
    (definable₁_fiber φ c).mono (by rintro _ ⟨i, rfl⟩; exact hcM₁ i)
  obtain ⟨BM, hBMD, hBMindep, hBMmax⟩ := exists_maximal_indep L (M₁ : Set (M : Type)) (fiber φ c)
  have hBMcard : #BM = #(M : Type) :=
    mk_maximal_indep_eq hL hvp M hM hDmin hDCM₁ hM₁lt hBMD hBMindep hBMmax
  -- a small elementary substructure of `Ω` containing the image of `M₁` and the realisation `a`
  have hFMsub : #((fun x : (M : Type) => F x) '' (M₁ : Set (M : Type)) ∪ {a} : Set (Ω : Type))
      ≤ #A + ℵ₀ := by
    refine (Cardinal.mk_union_le _ _).trans ?_
    have h1 : #(((fun x : (M : Type) => F x) '' (M₁ : Set (M : Type))) : Set (Ω : Type))
        ≤ #A + ℵ₀ := by
      rw [Cardinal.mk_image_eq F.injective]
      exact le_of_eq hM₁mk
    have h2 : #(({a} : Set (Ω : Type))) ≤ ℵ₀ := by
      rw [Cardinal.mk_singleton]
      exact Cardinal.one_le_aleph0
    calc #(((fun x : (M : Type) => F x) '' (M₁ : Set (M : Type))) : Set (Ω : Type))
          + #(({a} : Set (Ω : Type))) ≤ (#A + ℵ₀) + ℵ₀ := add_le_add h1 h2
      _ = #A + ℵ₀ := by rw [add_assoc, Cardinal.aleph0_add_aleph0]
  obtain ⟨Ns, hNs, hNscard⟩ := exists_elementarySubstructure_card_eq L
    ((fun x : (M : Type) => F x) '' (M₁ : Set (M : Type)) ∪ {a}) (#A + ℵ₀) le_add_self
    (by simpa using hFMsub) (by simpa using hL.trans le_add_self)
    (by simpa using hlamM.le.trans hMΩ)
  simp only [Cardinal.lift_id] at hNscard
  set FM : Set (Ω : Type) := (fun x : (M : Type) => F x) '' (M₁ : Set (M : Type)) with hFM
  have hFMNs : FM ⊆ (Ns : Set (Ω : Type)) := Set.subset_union_left.trans hNs
  have haNs : a ∈ (Ns : Set (Ω : Type)) := hNs (Or.inr rfl)
  -- the small model
  set cN : Fin mc → (Ns : Type) := fun i => ⟨F (c i), hFMNs ⟨c i, hcM₁ i, rfl⟩⟩ with hcN
  set CN : Set (Ns : Type) := Subtype.val ⁻¹' FM with hCN
  have hUMN : UnifMinimal φ cN := (unifMinimal_map_iff Ns.subtype).1 hUMΩ
  have hminN : IsMinimalSet L (fiber φ cN) := isMinimalSet_of_unifMinimal hUMN
  have hcNCN : ∀ i, cN i ∈ CN := fun i => ⟨c i, hcM₁ i, rfl⟩
  have hDCN : CN.Definable₁ L (fiber φ cN) :=
    (definable₁_fiber φ cN).mono (by rintro _ ⟨i, rfl⟩; exact hcNCN i)
  obtain ⟨BN, hBND, hBNindep, hBNmax⟩ := exists_maximal_indep L CN (fiber φ cN)
  -- `BN` is disjoint from `CN`
  have hBNCN : ∀ b ∈ BN, b ∉ CN := by
    intro b hb hbc
    exact hBNindep b hb (subset_alg _ (Set.mem_union_left _ hbc))
  -- the prime model over `CN ∪ BN` is all of `N`
  obtain ⟨N₀, gemb, A'', hA''img, hprime, -⟩ :=
    exists_prime_of_isOmegaStable' hL hos (Ns.toModel T) (CN ∪ BN)
  have hrange : ∀ y : (Ns : Type), y ∈ CN ∪ BN → ∃ z : ↥A'', (gemb (z : N₀) : (Ns : Type)) = y := by
    intro y hy
    have hy' : y ∈ (fun x : N₀ => (gemb x : (Ns : Type))) '' A'' := by
      rw [hA''img]
      exact hy
    obtain ⟨z, hz, hzy⟩ := hy'
    exact ⟨⟨z, hz⟩, hzy⟩
  have hsurj : Function.Surjective (gemb : N₀ → (Ns : Type)) := by
    have huniv := eq_univ_of_maximal_indep_subset hvp (Ns.toModel T) hminN hDCN hBND hBNindep
      hBNmax (elemRange gemb)
      (fun y hy => by
        obtain ⟨z, hz⟩ := hrange y (Or.inl hy)
        exact ⟨(z : N₀), hz⟩)
      (fun y hy => by
        obtain ⟨z, hz⟩ := hrange y (Or.inr hy)
        exact ⟨(z : N₀), hz⟩)
    rw [coe_elemRange] at huniv
    intro y
    have : y ∈ Set.range (gemb : N₀ → (Ns : Type)) := by rw [huniv]; trivial
    exact this
  -- an injection of the basis of `N` into the basis of `M`
  have hBNle : #(BN : Set (Ns : Type)) ≤ #(BM : Set (M : Type)) := by
    refine (Cardinal.mk_set_le BN).trans ?_
    rw [hBMcard, hNscard]
    exact hlamM.le
  obtain ⟨j⟩ := (Cardinal.le_def _ _).1 hBNle
  -- the inverse of `F` on the copy of `M₁`
  have hCNpre : ∀ y : (Ns : Type), y ∈ CN →
      ∃ x : (M : Type), x ∈ (M₁ : Set (M : Type)) ∧ F x = (y : (Ω : Type)) := by
    rintro y ⟨x, hx, hFx⟩
    exact ⟨x, hx, hFx⟩
  choose finv hfinv1 hfinv2 using hCNpre
  -- the partial map into `M`
  set hmap : ↥(CN ∪ BN) → (M : Type) := fun y =>
    if hy : (y : (Ns : Type)) ∈ BN then (j ⟨(y : (Ns : Type)), hy⟩ : (M : Type))
    else finv (y : (Ns : Type)) (by
      rcases y.2 with h | h
      · exact h
      · exact absurd h hy) with hhmap
  have hmap_BN : ∀ (y : ↥(CN ∪ BN)) (hy : (y : (Ns : Type)) ∈ BN),
      hmap y = (j ⟨(y : (Ns : Type)), hy⟩ : (M : Type)) := by
    intro y hy
    simp only [hhmap, dif_pos hy]
  have hmap_CN : ∀ y : ↥(CN ∪ BN), (y : (Ns : Type)) ∈ CN →
      F (hmap y) = ((y : (Ns : Type)) : (Ω : Type)) := by
    intro y hy
    have hnb : (y : (Ns : Type)) ∉ BN := fun hb => hBNCN _ hb hy
    simp only [hhmap, dif_neg hnb]
    exact hfinv2 _ _
  -- the ingredients of indiscernibility, inside `Ω`
  have hFMdef : FM.Definable₁ L (fiber φ fun i => F (c i)) :=
    (definable₁_fiber φ _).mono (by rintro _ ⟨i, rfl⟩; exact ⟨c i, hcM₁ i, rfl⟩)
  have hvalCN : (fun y : (Ns : Type) => Ns.subtype y) '' CN = FM := by
    refine Set.image_preimage_eq_of_subset ?_
    intro z hz
    exact ⟨⟨z, hFMNs hz⟩, rfl⟩
  have hindepBN : Indep L FM ((fun y : (Ns : Type) => Ns.subtype y) '' BN) := by
    have h := indep_image_of_elementaryEmbedding Ns.subtype hBNindep
    rwa [hvalCN] at h
  have hindepBM : Indep L FM ((fun x : (M : Type) => F x) '' BM) :=
    indep_image_of_elementaryEmbedding F hBMindep
  have hBNΩ : ((fun y : (Ns : Type) => Ns.subtype y) '' BN) ⊆ fiber φ fun i => F (c i) := by
    rintro _ ⟨y, hy, rfl⟩
    exact (mem_fiber_map_iff Ns.subtype φ cN y).2 (hBND hy)
  have hBMΩ : ((fun x : (M : Type) => F x) '' BM) ⊆ fiber φ fun i => F (c i) := by
    rintro _ ⟨y, hy, rfl⟩
    exact (mem_fiber_map_iff F φ c y).2 (hBMD hy)
  -- the partial map is elementary
  have helem : IsElementaryOn L (CN ∪ BN) hmap := by
    refine isElementaryOn_of_realize_fin fun n ψ x => ?_
    rw [← Ns.subtype.map_formula ψ (Subtype.val ∘ x), ← F.map_formula ψ (hmap ∘ x)]
    set w : Fin n → (Ω : Type) := ⇑Ns.subtype ∘ Subtype.val ∘ x with hw
    set w' : Fin n → (Ω : Type) := ⇑F ∘ hmap ∘ x with hw'
    have htype : (typeOver FM w : CompleteTypeOver L FM (Fin n)) = typeOver FM w' := by
      refine typeOver_eq_of_restrict {i : Fin n | (x i : (Ns : Type)) ∈ BN} ?_ ?_ ?_
      · intro i hi
        have hCNi : (x i : (Ns : Type)) ∈ CN := by
          rcases (x i).2 with h | h
          · exact h
          · exact absurd h hi
        exact (hmap_CN (x i) hCNi).symm
      · intro i hi
        have hCNi : (x i : (Ns : Type)) ∈ CN := by
          rcases (x i).2 with h | h
          · exact h
          · exact absurd h hi
        exact hCNi
      · -- the entries lying in the bases
        set S : Set (Fin n) := {i : Fin n | (x i : (Ns : Type)) ∈ BN} with hS
        set V : Set (Ns : Type) := Set.range fun i : ↥S => (x (i : Fin n) : (Ns : Type)) with hV
        haveI : Finite ↥V := Set.finite_coe_iff.2 (Set.finite_range _)
        haveI : Fintype ↥V := Fintype.ofFinite _
        have hVBN : ∀ v : ↥V, (v : (Ns : Type)) ∈ BN := by
          rintro ⟨-, ⟨i, rfl⟩⟩
          exact i.2
        set e : Fin (Fintype.card ↥V) ≃ ↥V := (Fintype.equivFin ↥V).symm with he
        set abar : Fin (Fintype.card ↥V) → (Ω : Type) :=
          fun t => ((e t : (Ns : Type)) : (Ω : Type)) with habar
        set bbar : Fin (Fintype.card ↥V) → (Ω : Type) :=
          fun t => F (j ⟨(e t : (Ns : Type)), hVBN (e t)⟩) with hbbar
        set σ : ↥S → Fin (Fintype.card ↥V) :=
          fun i => e.symm ⟨(x (i : Fin n) : (Ns : Type)), ⟨i, rfl⟩⟩ with hσ
        have hea : ∀ i : ↥S,
            (e (σ i) : (Ns : Type)) = (x (i : Fin n) : (Ns : Type)) := by
          intro i
          rw [hσ, Equiv.apply_symm_apply]
        have hVinj : Function.Injective fun v : ↥V => ((v : (Ns : Type)) : (Ω : Type)) := by
          intro u v huv
          exact Subtype.ext (Subtype.ext huv)
        have hainj : Function.Injective abar := fun s t hst =>
          e.injective (hVinj (by simpa only [habar] using hst))
        have hbinj : Function.Injective bbar := by
          intro s t hst
          simp only [hbbar] at hst
          have h1 := F.injective hst
          have h2 : (⟨(e s : (Ns : Type)), hVBN (e s)⟩ : ↥BN)
              = ⟨(e t : (Ns : Type)), hVBN (e t)⟩ := j.injective (Subtype.ext (by exact_mod_cast h1))
          exact e.injective (Subtype.ext (congrArg (fun z : ↥BN => (z : (Ns : Type))) h2))
        have hindisc := typeOver_eq_of_indep_of_injOn hminΩ hFMdef hBNΩ hBMΩ hindepBN hindepBM
          (a := abar) (b := bbar)
          (fun t => ⟨(e t : (Ns : Type)), hVBN (e t), rfl⟩)
          (fun t => ⟨(j ⟨(e t : (Ns : Type)), hVBN (e t)⟩ : (M : Type)),
            (j ⟨(e t : (Ns : Type)), hVBN (e t)⟩).2, rfl⟩)
          hainj hbinj
        have hcomp := typeOver_comp_eq hindisc σ
        have hA : (abar ∘ σ) = fun i : ↥S => w (i : Fin n) := by
          funext i
          simp only [Function.comp_apply, habar, hw, hea i]
          rfl
        have hB : (bbar ∘ σ) = fun i : ↥S => w' (i : Fin n) := by
          funext i
          have hxi : (x (i : Fin n) : (Ns : Type)) ∈ BN := i.2
          have hsub : (⟨(e (σ i) : (Ns : Type)), hVBN (e (σ i))⟩ : ↥BN)
              = ⟨(x (i : Fin n) : (Ns : Type)), hxi⟩ := Subtype.ext (hea i)
          simp only [Function.comp_apply, hbbar, hw', Function.comp_apply]
          rw [hsub, hmap_BN (x (i : Fin n)) hxi]
        rw [hA, hB] at hcomp
        exact hcomp
    rw [typeOver_eq_iff_forall_definable] at htype
    exact htype {v : Fin n → (Ω : Type) | ψ.Realize v}
      (Set.definable_iff_exists_formula_sum.2
        ⟨ψ.relabel Sum.inr, by ext v; simp [Formula.realize_relabel]⟩)
  -- transport the map to the prime model
  have hA''mem : ∀ z : ↥A'', (gemb (z : N₀) : (Ns : Type)) ∈ CN ∪ BN := by
    intro z
    have : (gemb (z : N₀) : (Ns : Type)) ∈ (fun x : N₀ => (gemb x : (Ns : Type))) '' A'' :=
      ⟨(z : N₀), z.2, rfl⟩
    rwa [hA''img] at this
  set gmap : ↥A'' → (M : Type) :=
    fun z => hmap ⟨(gemb (z : N₀) : (Ns : Type)), hA''mem z⟩ with hgmap
  have hgmapelem : IsElementaryOn L A'' gmap := by
    refine isElementaryOn_of_realize_fin fun n ψ y => ?_
    have h2 := helem.realize_fin ψ
      fun i => (⟨(gemb (y i : N₀) : (Ns : Type)), hA''mem (y i)⟩ : ↥(CN ∪ BN))
    show ψ.Realize (fun i => ((y i : N₀))) ↔ ψ.Realize fun i => gmap (y i)
    rw [← gemb.map_formula ψ fun i => ((y i : N₀))]
    exact h2
  obtain ⟨H, hH⟩ := hprime M gmap hgmapelem
  -- the realisation of `p` in `M`
  obtain ⟨a₀, ha₀⟩ := hsurj ⟨a, haNs⟩
  have hApre : ∀ y : ↥A, ∃ z : ↥A'',
      (gemb (z : N₀) : (Ns : Type)) = ⟨F (y : (M : Type)), hFMNs ⟨(y : (M : Type)),
        hAM₁ y.2, rfl⟩⟩ := by
    intro y
    exact hrange _ (Or.inl ⟨(y : (M : Type)), hAM₁ y.2, rfl⟩)
  choose pre hpre using hApre
  have hHpre : ∀ y : ↥A, H (pre y : N₀) = (y : (M : Type)) := by
    intro y
    have hq : ((⟨(gemb (pre y : N₀) : (Ns : Type)), hA''mem (pre y)⟩ :
        ↥(CN ∪ BN)) : (Ns : Type)) ∈ CN := by
      show (gemb (pre y : N₀) : (Ns : Type)) ∈ CN
      rw [hpre y]
      exact ⟨(y : (M : Type)), hAM₁ y.2, rfl⟩
    have hc := hmap_CN ⟨(gemb (pre y : N₀) : (Ns : Type)), hA''mem (pre y)⟩ hq
    have hq2 : (((⟨(gemb (pre y : N₀) : (Ns : Type)), hA''mem (pre y)⟩ : ↥(CN ∪ BN)) :
        (Ns : Type)) : (Ω : Type)) = F (y : (M : Type)) := by
      have hval : ((⟨(gemb (pre y : N₀) : (Ns : Type)), hA''mem (pre y)⟩ : ↥(CN ∪ BN)) :
          (Ns : Type)) = ⟨F (y : (M : Type)), hFMNs ⟨(y : (M : Type)), hAM₁ y.2, rfl⟩⟩ := hpre y
      rw [hval]
    rw [hH (pre y)]
    exact F.injective (hc.trans hq2)
  refine mem_realizedTypes_one_iff.2 ⟨H a₀, ?_⟩
  refine (Theory.CompleteType.eq_of_le (p := p) (q := typeOfElem A (H a₀)) fun ψ hψ => ?_).symm
  have h0 : a ∈ fiber (rep ψ) fun y : ↥A => F (y : (M : Type)) := ha ψ hψ
  have h1 : (⟨a, haNs⟩ : (Ns : Type)) ∈ fiber (rep ψ)
      fun y : ↥A => (⟨F (y : (M : Type)), hFMNs ⟨(y : (M : Type)), hAM₁ y.2, rfl⟩⟩ :
        (Ns : Type)) :=
    (mem_fiber_map_iff Ns.subtype (rep ψ) _ ⟨a, haNs⟩).1 h0
  have h2 : a₀ ∈ fiber (rep ψ) fun y : ↥A => (pre y : N₀) := by
    refine (mem_fiber_map_iff gemb (rep ψ) (fun y : ↥A => (pre y : N₀)) a₀).1 ?_
    rw [ha₀]
    have hfun : (fun y : ↥A => (gemb (pre y : N₀) : (Ns : Type)))
        = fun y : ↥A => (⟨F (y : (M : Type)), hFMNs ⟨(y : (M : Type)), hAM₁ y.2, rfl⟩⟩ :
          (Ns : Type)) := funext fun y => hpre y
    rw [hfun]
    exact h1
  have h3 : H a₀ ∈ fiber (rep ψ) fun y : ↥A => H (pre y : N₀) :=
    (mem_fiber_map_iff H (rep ψ) (fun y : ↥A => (pre y : N₀)) a₀).2 h2
  have h4 : (fun y : ↥A => H (pre y : N₀)) = (Subtype.val : ↥A → (M : Type)) :=
    funext hHpre
  rw [h4] at h3
  rw [← hrep ψ] at h3
  exact h3

end Main

/-- **The saturation principle**, in the form `Submission/Morley/Assembly.lean` asks for: an
`ω`-stable complete theory in a countable language without Vaughtian pairs has all its models of
uncountable cardinality saturated. -/
theorem saturationPrinciple (L : FirstOrder.Language.{0, 0}) : SaturationPrinciple L :=
  fun _ hL _ hos hvp M hM => isSaturated_of_not_hasVaughtianPair hL hos hvp M hM

/-- **Morley's categoricity theorem at `ℵ₁`, unconditionally.**

A complete theory with only infinite models, in a countable language, which is categorical in
`ℵ₁`, is categorical in every uncountable cardinal.  This is
`Submission.Morley.morley_categoricity_aleph1` with its hypothesis discharged. -/
theorem morley_categoricity_aleph1' {L : FirstOrder.Language.{0, 0}} (hL : L.card ≤ ℵ₀)
    {T : L.Theory} (hT : T.IsComplete) (hInf : ∀ M : T.ModelType.{0, 0, 0}, Infinite M)
    (hcat : (ℵ₁ : Cardinal.{0}).Categorical T) {μ : Cardinal.{0}} (hμ : ℵ₀ < μ) :
    μ.Categorical T :=
  morley_categoricity_aleph1 (saturationPrinciple L) hL hT hInf hcat hμ

/-- **Morley's categoricity theorem**, with the saturation principle discharged: only
two-cardinal transfer for `ω`-stable theories remains as a hypothesis. -/
theorem morley_categoricity' {L : FirstOrder.Language.{0, 0}} (hTC : OmegaStableTwoCardinal L)
    (hL : L.card ≤ ℵ₀) {T : L.Theory} (hT : T.IsComplete)
    (hInf : ∀ M : T.ModelType.{0, 0, 0}, Infinite M) {κ : Cardinal.{0}} (hκ : ℵ₀ < κ)
    (hcat : κ.Categorical T) {μ : Cardinal.{0}} (hμ : ℵ₀ < μ) : μ.Categorical T :=
  morley_categoricity (saturationPrinciple L) hTC hL hT hInf hκ hcat hμ

end Submission.Morley
