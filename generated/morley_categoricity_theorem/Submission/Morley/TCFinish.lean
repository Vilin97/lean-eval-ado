import Mathlib
import Submission.Morley.OmegaTwoCardinal
import Submission.Morley.PrimeBig
import Submission.Morley.Rank
import Submission.Morley.SatExists

/-!
# Two-cardinal transfer for `ω`-stable theories: the chain of prime extensions

This file completes `Submission.Morley.OmegaStableTwoCardinal`, the last of the two hypotheses of
`Submission.Morley.morley_categoricity` coming from the two-cardinal side: an `ω`-stable complete
theory in a countable language with a Vaughtian pair has, for **every** uncountable `κ`, a model of
cardinality `κ` carrying an infinite definable set of cardinality `< κ`.

## What was missing, and how it is supplied

`Submission/Morley/OmegaTwoCardinal.lean` reduces the statement to steps (3) and (4) of the
classical proof.  Step (3) is `Submission.Morley.mem_of_isIsolated_of_countable`: an extension of a
set `S` by elements of isolated type over `S ∪ {c}`, with `c` *generic* over `S`, adds nothing to a
set definable over `S` that is countable in `S`.  Step (4) — the length-`κ` elementary chain — is
proved here.

Two changes to the classical bookkeeping make it short.

* **Everything happens inside one ambient model.**  `Submission.Morley.exists_saturated_elementaryExtension`
  supplies a model `𝔐` realizing every complete `1`-type over every parameter set of size at most
  `κ`, so all the stages of the chain can be taken to be *subsets* of `𝔐`.  There is then no
  chain of structures to build and no colimit to form.
* **Zorn instead of a recursion.**  The stages are exactly the members of
  `{S | S₀ ⊆ S, L.MeetsDefinable S, D ∩ S ⊆ D ∩ S₀}`, a family closed under unions of chains
  (`Submission.Morley.meetsDefinable_sUnion`: a set definable over a union of a chain is definable
  over one member, because a formula mentions only finitely many parameters).  A maximal member has
  cardinality at least `κ`, since otherwise the successor step applies to it and enlarges it.

## Main results

* `Submission.Morley.meetsDefinable_sUnion`: `FirstOrder.Language.MeetsDefinable` passes to unions
  of chains.
* `Submission.Morley.meetsDefinable_range`: the range of an elementary embedding meets definable
  sets.
* `Submission.Morley.exists_omega1Minimal_inter`: an *uncountable subset* `S` of a model of an
  `ω`-stable theory carries an `ℵ₁`-minimal definable set, minimality being measured inside `S`.
  This is `Submission.Morley.exists_omega1Minimal` relativised to a subset.
* `Submission.Morley.exists_generic_elem`: inside a model realizing all `1`-types over `S`, an
  element `c ∉ S` **generic** over `S`, i.e. such that every countable set of formulas over `S`
  satisfied by `c` is already satisfied inside `S`.  This is the hypothesis `hgen` of
  `Submission.Morley.mem_of_isIsolated_of_countable`.
* `Submission.Morley.exists_meetsDefinable_large`: the Zorn argument — a subset of size at least
  `κ` which is an elementary substructure and does not enlarge the distinguished definable set.
* `Submission.Morley.largeTwoCardinalModels` and `Submission.Morley.omegaStableTwoCardinal`:
  **two-cardinal transfer for `ω`-stable theories**.
-/

namespace Submission.Morley

open Cardinal Set FirstOrder FirstOrder.Language

/-! ## Meeting definable sets -/

section MeetsDefinable

variable {L : FirstOrder.Language.{0, 0}} {M : Type} [L.Structure M]

/-- **`MeetsDefinable` passes to unions of chains.**  A set definable over the union of a chain is
definable over a single member of the chain, because a formula mentions only finitely many
parameters and a finite tuple from a union of a chain lies in one member. -/
theorem meetsDefinable_sUnion {c : Set (Set M)} (hchain : IsChain (· ⊆ ·) c) (hne : c.Nonempty)
    (h : ∀ s ∈ c, L.MeetsDefinable s) : L.MeetsDefinable (⋃₀ c) := by
  classical
  intro Dset hDne hdef
  obtain ⟨γ, hγ, θ, d, hdmem, hθ⟩ := exists_boundedFormula_of_definable₁ hdef
  haveI : Finite γ := hγ
  obtain ⟨m, ⟨e⟩⟩ := Finite.exists_equiv_fin γ
  obtain ⟨s, hs, hds⟩ := exists_mem_of_forall_mem_sUnion hchain hne
    (fun i : Fin m => d (e.symm i)) fun i => hdmem (e.symm i)
  have hrange : Set.range d ⊆ s := by
    rintro z ⟨i, rfl⟩
    have h1 := hds (e i)
    rwa [Equiv.symm_apply_apply] at h1
  have hdefs : s.Definable₁ L Dset := by
    have h1 := (definable₁_of_boundedFormula θ d).mono hrange
    have heq : {a : M | θ.Realize d fun _ => a} = Dset := by
      ext a
      exact (hθ a).symm
    rwa [heq] at h1
  obtain ⟨z, hzD, hzs⟩ := h s hs Dset hDne hdefs
  exact ⟨z, hzD, ⟨s, hs, hzs⟩⟩

/-- **The range of an elementary embedding meets definable sets**, hence is an elementary
substructure of the target. -/
theorem meetsDefinable_range {N : Type} [L.Structure N] (f : M ↪ₑ[L] N) :
    L.MeetsDefinable (Set.range (f : M → N)) := by
  classical
  intro Dset hDne hdef
  obtain ⟨γ, hγ, θ, d, hdmem, hθ⟩ := exists_boundedFormula_of_definable₁ hdef
  haveI : Finite γ := hγ
  choose d' hd' using hdmem
  have hd'f : (f : M → N) ∘ d' = d := funext hd'
  have hsnocN : ∀ x : N, (Fin.snoc (default : Fin 0 → N) x : Fin 1 → N) = fun _ => x := by
    intro x
    funext i
    refine Fin.lastCases ?_ (fun j => j.elim0) i
    rw [Fin.snoc_last]
  have hsnocM : ∀ x : M, (Fin.snoc (default : Fin 0 → M) x : Fin 1 → M) = fun _ => x := by
    intro x
    funext i
    refine Fin.lastCases ?_ (fun j => j.elim0) i
    rw [Fin.snoc_last]
  have hdefault : ((f : M → N) ∘ (default : Fin 0 → M)) = (default : Fin 0 → N) := by
    funext i
    exact i.elim0
  obtain ⟨z, hz⟩ := hDne
  have hex : θ.ex.Realize d (default : Fin 0 → N) := by
    refine BoundedFormula.realize_ex.2 ⟨z, ?_⟩
    rw [hsnocN]
    exact (hθ z).1 hz
  have hmapex := f.map_boundedFormula θ.ex d' (default : Fin 0 → M)
  rw [hd'f, hdefault] at hmapex
  obtain ⟨y, hy⟩ := BoundedFormula.realize_ex.1 (hmapex.1 hex)
  rw [hsnocM] at hy
  refine ⟨f y, ?_, ⟨y, rfl⟩⟩
  rw [hθ (f y)]
  have h3 := (f.map_boundedFormula θ d' (fun _ : Fin 1 => y)).2 hy
  rw [hd'f] at h3
  exact h3

end MeetsDefinable

/-! ## The `ℵ₁`-minimal definable set of an uncountable subset -/

section Minimal

variable {L : FirstOrder.Language.{0, 0}}

/-- **An uncountable subset carries an `ℵ₁`-minimal definable set.**

This is `Submission.Morley.exists_omega1Minimal` with the model replaced by an arbitrary
uncountable *subset* `S` of a model: some formula with parameters in `S` has uncountably many
realizations in `S`, and every formula cuts that set into a piece which is countable in `S` and a
complement which is countable in `S`. -/
theorem exists_omega1Minimal_inter {T : L.Theory} (hst : OmegaStable.{0, 0, 0} T)
    (M : T.ModelType.{0, 0, 0}) (S : Set M) (hS : ¬ S.Countable) :
    ∃ φ₀ : Form1 L S, ¬ (realSet S φ₀ ∩ S).Countable ∧
      ∀ ψ : Form1 L S,
        (realSet S (φ₀ ⊓ ψ) ∩ S).Countable ∨ (realSet S (φ₀ ⊓ ∼ψ) ∩ S).Countable := by
  classical
  by_contra hcon
  push Not at hcon
  have hstep : ∀ φ : Form1 L S, ∃ ψ : Form1 L S,
      ¬ (realSet S φ ∩ S).Countable →
        (¬ (realSet S (φ ⊓ ψ) ∩ S).Countable ∧ ¬ (realSet S (φ ⊓ ∼ψ) ∩ S).Countable) := by
    intro φ
    by_cases h : (realSet S φ ∩ S).Countable
    · exact ⟨φ, fun h' => absurd h h'⟩
    · obtain ⟨ψ, h1, h2⟩ := hcon φ h
      exact ⟨ψ, fun _ => ⟨h1, h2⟩⟩
  choose split hsplit using hstep
  obtain ⟨F, hF0, hFcons⟩ : ∃ F : List Bool → Form1 L S, F [] = ⊤ ∧
      ∀ (b : Bool) (s : List Bool),
        F (b :: s) = if b then F s ⊓ split (F s) else F s ⊓ ∼(split (F s)) :=
    ⟨fun s => s.rec (⊤ : Form1 L S)
      (fun b _ ih => if b then ih ⊓ split ih else ih ⊓ ∼(split ih)), rfl,
      fun b s => by cases b <;> rfl⟩
  have hFsub : ∀ (b : Bool) (s : List Bool),
      realSet S (F (b :: s)) ⊆ realSet S (F s) := by
    intro b s
    rw [hFcons]
    cases b <;> simp
  have hFbig : ∀ s : List Bool, ¬ (realSet S (F s) ∩ S).Countable := by
    intro s
    induction s with
    | nil =>
      rw [hF0, realSet_top, Set.univ_inter]
      exact hS
    | cons b s ih =>
      rw [hFcons]
      cases b
      · exact ((hsplit (F s)) ih).2
      · exact ((hsplit (F s)) ih).1
  have hFne : ∀ s : List Bool, (realSet S (F s)).Nonempty := by
    intro s
    rw [Set.nonempty_iff_ne_empty]
    intro hc
    exact hFbig s (by rw [hc, Set.empty_inter]; exact Set.countable_empty)
  have tree : BinaryTree (paramTheory L S) (Fin 1) :=
    { form := F
      consistent := fun s => (nonempty_typesWith_iff_realSet _).2 (hFne s)
      mono := fun b s => (typesWith_subset_iff_realSet _ _).2 (hFsub b s)
      disjoint := fun s => (typesWith_disjoint_iff_realSet _ _).2 (by
        rw [hFcons false s, hFcons true s]
        simp only [Bool.false_eq_true, if_false, if_true, realSet_inf, realSet_not]
        rw [Set.disjoint_iff_inter_eq_empty]
        exact Set.eq_empty_of_forall_notMem fun a ha => ha.1.2 ha.2.2) }
  obtain ⟨A₀, -, hcount, ⟨t₀⟩⟩ := exists_countable_binaryTree tree
  exact not_omegaStable_of_binaryTree M A₀
    (Cardinal.mk_le_aleph0_iff.2 (Set.countable_coe_iff.2 hcount)) t₀ hst

end Minimal

/-! ## The generic element over an uncountable subset -/

section Generic

variable {L : FirstOrder.Language.{0, 0}}

/-- **A generic element over an uncountable subset.**

Let `S` be an uncountable subset of a model `M` of an `ω`-stable theory, and suppose every complete
`1`-type over `S` is realized in `M` (which `Submission.Morley.exists_saturated_elementaryExtension`
guarantees when `#S ≤ κ`).  Then there is `c ∈ M \ S` such that every countable set of formulas over
`S` satisfied by `c` is already satisfied by an element of `S`.

This is exactly the hypothesis `hgen` of `Submission.Morley.mem_of_isIsolated_of_countable`.  The
element `c` realizes the *generic type* of an `ℵ₁`-minimal definable set of `S`: the formulas whose
solution set in `S` is uncountable form a directed family of nonempty closed subsets of the
(compact) space of complete `1`-types over `S`, hence lie in a common complete type. -/
theorem exists_generic_elem {T : L.Theory} (hst : OmegaStable.{0, 0, 0} T)
    (M : T.ModelType.{0, 0, 0}) (S : Set M) (hS : ¬ S.Countable)
    (hsat : ∀ p : S₁ L S, ∃ a : M, typeOfElem S a = p) :
    ∃ c : M, c ∉ S ∧
      ∀ u : ℕ → (L[[↥S]]).Formula (Fin 1), (∀ n, (u n).Realize fun _ => c) →
        ∃ a : ↥S, ∀ n, (u n).Realize fun _ => ((a : M)) := by
  classical
  obtain ⟨φ₀, hbig, hmin⟩ := exists_omega1Minimal_inter hst M S hS
  obtain ⟨p, hmem⟩ : ∃ p : Set (Form1 L S),
      ∀ ψ, ψ ∈ p ↔ ¬ (realSet S (φ₀ ⊓ ψ) ∩ S).Countable :=
    ⟨{ψ | ¬ (realSet S (φ₀ ⊓ ψ) ∩ S).Countable}, fun _ => Iff.rfl⟩
  -- the complementary piece of a formula of `p` is countable in `S`
  have hsmall : ∀ ψ : Form1 L S, ψ ∈ p → (realSet S (φ₀ ⊓ ∼ψ) ∩ S).Countable := fun ψ hψ =>
    (hmin ψ).resolve_left ((hmem ψ).1 hψ)
  -- `p` is complete
  have hsplit : ∀ ψ : Form1 L S, realSet S φ₀ ∩ S =
      (realSet S (φ₀ ⊓ ψ) ∩ S) ∪ (realSet S (φ₀ ⊓ ∼ψ) ∩ S) := by
    intro ψ
    simp only [realSet_inf, realSet_not]
    ext z
    simp only [Set.mem_inter_iff, Set.mem_union, Set.mem_compl_iff]
    tauto
  have hcompl : ∀ ψ : Form1 L S, ψ ∈ p ∨ ∼ψ ∈ p := by
    intro ψ
    by_contra hcon
    push Not at hcon
    obtain ⟨h1, h2⟩ := hcon
    rw [hmem, not_not] at h1
    rw [hmem, not_not] at h2
    exact hbig (by rw [hsplit ψ]; exact h1.union h2)
  -- `p` contains `⊤` and is closed under conjunction
  have htop : (⊤ : Form1 L S) ∈ p := by
    rw [hmem]
    simpa using hbig
  have hinf : ∀ ψ₁ ψ₂ : Form1 L S, ψ₁ ∈ p → ψ₂ ∈ p → ψ₁ ⊓ ψ₂ ∈ p := by
    intro ψ₁ ψ₂ h1 h2
    rw [hmem]
    intro hc
    refine hbig (Set.Countable.mono ?_ ((hc.union (hsmall ψ₁ h1)).union (hsmall ψ₂ h2)))
    rintro z ⟨hz0, hzS⟩
    by_cases h1' : z ∈ realSet S ψ₁
    · by_cases h2' : z ∈ realSet S ψ₂
      · exact Or.inl (Or.inl ⟨by simp only [realSet_inf]; exact ⟨hz0, h1', h2'⟩, hzS⟩)
      · exact Or.inr ⟨by simp only [realSet_inf, realSet_not]; exact ⟨hz0, h2'⟩, hzS⟩
    · exact Or.inl (Or.inr ⟨by simp only [realSet_inf, realSet_not]; exact ⟨hz0, h1'⟩, hzS⟩)
  -- every countable subfamily of `p` is realized in `S`
  have hseq : ∀ u : ℕ → Form1 L S, (∀ n, u n ∈ p) →
      ((⋂ n, realSet S (u n)) ∩ S).Nonempty := by
    intro u hu
    have hcover : realSet S φ₀ ∩ S ⊆
        ((⋂ n, realSet S (u n)) ∩ S) ∪ ⋃ n, (realSet S (φ₀ ⊓ ∼(u n)) ∩ S) := by
      rintro z ⟨hz0, hzS⟩
      by_cases hz : ∀ n, z ∈ realSet S (u n)
      · exact Or.inl ⟨Set.mem_iInter.2 hz, hzS⟩
      · push Not at hz
        obtain ⟨n, hn⟩ := hz
        refine Or.inr (Set.mem_iUnion.2 ⟨n, ?_, hzS⟩)
        simp only [realSet_inf, realSet_not]
        exact ⟨hz0, hn⟩
    rw [Set.nonempty_iff_ne_empty]
    intro hemp
    refine hbig (Set.Countable.mono hcover ?_)
    rw [hemp]
    exact Set.countable_empty.union
      (Set.countable_iUnion fun n => hsmall (u n) (hu n))
  -- every formula of `p` is consistent
  have hpne : ∀ ψ : Form1 L S, ψ ∈ p → (realSet S ψ).Nonempty := by
    intro ψ hψ
    have h1 : (realSet S (φ₀ ⊓ ψ) ∩ S).Nonempty := by
      rw [Set.nonempty_iff_ne_empty]
      intro hemp
      exact (hmem ψ).1 hψ (by rw [hemp]; exact Set.countable_empty)
    obtain ⟨z, hz, -⟩ := h1
    rw [realSet_inf] at hz
    exact ⟨z, hz.2⟩
  -- compactness of the space of types: `p` extends to a complete type
  haveI : Nonempty ↥p := ⟨⟨⊤, htop⟩⟩
  have hdir : Directed (· ⊇ ·) (fun ψ : ↥p => (paramTheory L S).typesWith (ψ : Form1 L S)) := by
    intro ψ₁ ψ₂
    refine ⟨⟨(ψ₁ : Form1 L S) ⊓ (ψ₂ : Form1 L S), hinf _ _ ψ₁.2 ψ₂.2⟩, ?_, ?_⟩
    · simp only [Theory.CompleteType.typesWith_inf]
      exact Set.inter_subset_left
    · simp only [Theory.CompleteType.typesWith_inf]
      exact Set.inter_subset_right
  obtain ⟨q, hq⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
    (fun ψ : ↥p => (paramTheory L S).typesWith (ψ : Form1 L S)) hdir
    (fun ψ => (nonempty_typesWith_iff_realSet _).2 (hpne _ ψ.2))
    (fun _ => (_root_.CompleteType.isClosed_typesWith _).isCompact)
    (fun _ => _root_.CompleteType.isClosed_typesWith _)
  have hqmem : ∀ ψ : Form1 L S, ψ ∈ p → ψ ∈ q := fun ψ hψ =>
    (Theory.CompleteType.mem_typesWith_iff _ _).1 (Set.mem_iInter.1 hq ⟨ψ, hψ⟩)
  obtain ⟨c, hc⟩ := hsat q
  have hcreal : ∀ ψ : Form1 L S, ψ ∈ p → c ∈ realSet S ψ := by
    intro ψ hψ
    rw [mem_realSet, hc]
    exact hqmem ψ hψ
  -- `c` lies outside `S`
  have hcnotmem : c ∉ S := by
    intro hcS
    have hreal : realSet S (Formula.equivSentence
        (∼((Term.var 0).equal (L.con (⟨c, hcS⟩ : ↥S)).term))) = {z : M | z ≠ c} := by
      ext z
      rw [mem_realSet, mem_typeOfElem, Equiv.symm_apply_apply]
      simp [Formula.realize_not, Formula.realize_equal, Term.realize_constants]
    have hmemp : Formula.equivSentence
        (∼((Term.var 0).equal (L.con (⟨c, hcS⟩ : ↥S)).term)) ∈ p := by
      rw [hmem]
      intro hcnt
      refine hbig (Set.Countable.mono ?_ (hcnt.union (Set.countable_singleton c)))
      rintro z ⟨hz0, hzS⟩
      by_cases hzc : z = c
      · exact Or.inr hzc
      · refine Or.inl ⟨?_, hzS⟩
        rw [realSet_inf, hreal]
        exact ⟨hz0, hzc⟩
    have := hcreal _ hmemp
    rw [hreal] at this
    exact this rfl
  refine ⟨c, hcnotmem, ?_⟩
  intro u hu
  have hup : ∀ n, Formula.equivSentence (u n) ∈ p := by
    intro n
    rcases hcompl (Formula.equivSentence (u n)) with h | h
    · exact h
    · exfalso
      have h1 : c ∈ realSet S (∼(Formula.equivSentence (u n))) := hcreal _ h
      rw [realSet_not] at h1
      exact h1 (by rw [mem_realSet, mem_typeOfElem, Equiv.symm_apply_apply]; exact hu n)
  obtain ⟨a, ha, haS⟩ := hseq (fun n => Formula.equivSentence (u n)) hup
  refine ⟨⟨a, haS⟩, fun n => ?_⟩
  have h1 := Set.mem_iInter.1 ha n
  rw [mem_realSet, mem_typeOfElem, Equiv.symm_apply_apply] at h1
  exact h1

end Generic

/-! ## The chain of prime extensions, as a Zorn argument -/

section Chain

variable {L : FirstOrder.Language.{0, 0}}

/-- **Step (4) of two-cardinal transfer.**

Inside a model `M` of an `ω`-stable theory realizing every complete `1`-type over every parameter
set of size at most `κ`, let `D` be a set definable over an uncountable elementary substructure
`S₀`, with `D ∩ S₀` countable.  Then there is an elementary substructure `S ⊇ S₀` of cardinality at
least `κ` with `D ∩ S = D ∩ S₀`.

The family of candidates is closed under unions of chains, so Zorn's lemma provides a maximal one;
if it had cardinality `< κ` then `Submission.Morley.exists_generic_elem` would supply a generic
`c ∉ S`, an atomic elementary substructure over `S ∪ {c}` would enlarge it, and
`Submission.Morley.mem_of_isIsolated_of_countable` would keep `D ∩ S` unchanged. -/
theorem exists_meetsDefinable_large {T : L.Theory} (hL : L.card ≤ ℵ₀)
    (hst : IsOmegaStable.{0, 0, 0} T) (M : T.ModelType.{0, 0, 0}) {κ : Cardinal.{0}}
    (hsat : ∀ A : Set M, #A ≤ κ → ∀ p : S₁ L A, ∃ a : M, typeOfElem A a = p)
    {D S₀ : Set M} (hDdef : S₀.Definable₁ L D) (hS₀ : L.MeetsDefinable S₀)
    (hS₀u : ¬ S₀.Countable) (hDc : (D ∩ S₀).Countable) :
    ∃ S : Set M, S₀ ⊆ S ∧ L.MeetsDefinable S ∧ D ∩ S = D ∩ S₀ ∧ κ ≤ #S := by
  classical
  obtain ⟨P, hPmem⟩ : ∃ P : Set (Set M),
      ∀ S, S ∈ P ↔ (S₀ ⊆ S ∧ L.MeetsDefinable S ∧ D ∩ S ⊆ D ∩ S₀) :=
    ⟨{S | S₀ ⊆ S ∧ L.MeetsDefinable S ∧ D ∩ S ⊆ D ∩ S₀}, fun _ => Iff.rfl⟩
  have hS₀P : S₀ ∈ P := (hPmem _).2 ⟨subset_rfl, hS₀, subset_rfl⟩
  have hchainub : ∀ c ⊆ P, IsChain (· ⊆ ·) c → c.Nonempty → ∃ ub ∈ P, ∀ s ∈ c, s ⊆ ub := by
    intro c hcP hchain hcne
    refine ⟨⋃₀ c, (hPmem _).2 ⟨?_, ?_, ?_⟩, fun s hs => Set.subset_sUnion_of_mem hs⟩
    · obtain ⟨s, hs⟩ := hcne
      exact ((hPmem _).1 (hcP hs)).1.trans (Set.subset_sUnion_of_mem hs)
    · exact meetsDefinable_sUnion hchain hcne fun s hs => ((hPmem _).1 (hcP hs)).2.1
    · rintro z ⟨hzD, s, hs, hzs⟩
      exact ((hPmem _).1 (hcP hs)).2.2 ⟨hzD, hzs⟩
  obtain ⟨S, hS₀S, hSmax⟩ := zorn_subset_nonempty P hchainub S₀ hS₀P
  obtain ⟨-, hSmd, hSD⟩ := (hPmem _).1 hSmax.1
  have hSu : ¬ S.Countable := fun h => hS₀u (Set.Countable.mono hS₀S h)
  have hDS : D ∩ S = D ∩ S₀ :=
    Set.Subset.antisymm hSD fun z hz => ⟨hz.1, hS₀S hz.2⟩
  refine ⟨S, hS₀S, hSmd, hDS, ?_⟩
  by_contra hcard
  push Not at hcard
  have hSne : S.Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro h
    exact hSu (h ▸ Set.countable_empty)
  obtain ⟨c, hcS, hgen⟩ :=
    exists_generic_elem hst.omegaStable M S hSu (hsat S hcard.le)
  obtain ⟨S', hS'sub, hS'atom⟩ :=
    exists_atomic_elementarySubstructure_of_isOmegaStable hL hst M (insert c S)
  obtain ⟨φS, hφS⟩ := exists_realSet_eq_of_definable₁ S (hDdef.mono hS₀S)
  have hψ : ∀ z : M, (Formula.equivSentence.symm φS).Realize (fun _ : Fin 1 => z) ↔ z ∈ D := by
    intro z
    rw [← hφS, mem_realSet, mem_typeOfElem]
  have hY : {a : ↥S | (Formula.equivSentence.symm φS).Realize fun _ => ((a : M))}.Countable := by
    have heq : {a : ↥S | (Formula.equivSentence.symm φS).Realize fun _ => ((a : M))}
        = Subtype.val ⁻¹' (D ∩ S) := by
      ext a
      simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_inter_iff]
      exact ⟨fun h => ⟨(hψ _).1 h, a.2⟩, fun h => (hψ _).2 h.1⟩
    rw [heq]
    exact (show (D ∩ S).Countable by rw [hDS]; exact hDc).preimage Subtype.val_injective
  have hnew : D ∩ (S' : Set M) ⊆ D ∩ S₀ := by
    rintro z ⟨hzD, hzS'⟩
    have hzS : z ∈ S :=
      mem_of_isIsolated_of_countable hSmd hSne c hgen (Formula.equivSentence.symm φS) hY
        (hS'atom 1 (fun _ => z) fun _ => hzS') ((hψ z).2 hzD)
    exact hSD ⟨hzD, hzS⟩
  have hSS' : S ⊆ (S' : Set M) := (Set.subset_insert c S).trans hS'sub
  have hS'P : (S' : Set M) ∈ P :=
    (hPmem _).2 ⟨hS₀S.trans hSS', S'.meetsDefinable, hnew⟩
  exact hcS (hSmax.2 hS'P hSS' (hS'sub (Set.mem_insert c S)))

end Chain

/-! ## Two-cardinal transfer for `ω`-stable theories -/

section Main

/-- **Arbitrarily large two-cardinal models.**  An `ω`-stable complete theory in a countable
language with a Vaughtian pair has, for every uncountable `κ`, a model of cardinality at least `κ`
with a countably infinite parameter-definable set.

The base of the construction is Vaught's two-cardinal theorem, which supplies an `(ℵ₁, ℵ₀)`-model
`M₀`; the model is embedded elementarily into an ambient model `𝔐` realizing all `1`-types over
parameter sets of size at most `κ`, and `Submission.Morley.exists_meetsDefinable_large` grows the
image of `M₀` inside `𝔐` to size at least `κ` without adding a point to the definable set. -/
theorem largeTwoCardinalModels (L : FirstOrder.Language.{0, 0}) : LargeTwoCardinalModels L := by
  classical
  intro T hL hT hst hVP κ hκ
  -- the base `(ℵ₁, ℵ₀)`-model
  obtain ⟨M₀, A₀, X, hdef, hM₀, hX⟩ := vaughtTwoCardinal L T hL hT hVP
  obtain ⟨β, hβ, χ, b₀, -, hXchar⟩ := exists_boundedFormula_of_definable₁ hdef
  haveI : Finite β := hβ
  -- an ambient model realizing all `1`-types over parameter sets of size at most `κ`
  obtain ⟨𝔐, f, hsat, -⟩ := exists_saturated_elementaryExtension hL M₀ hκ.le
  obtain ⟨b, hb⟩ : ∃ b : β → 𝔐, (f : M₀ → 𝔐) ∘ b₀ = b := ⟨_, rfl⟩
  have hmapb : ∀ y : M₀, (χ.Realize b fun _ : Fin 1 => (f y : 𝔐)) ↔ χ.Realize b₀ fun _ => y := by
    intro y
    have h := f.map_boundedFormula χ b₀ (fun _ : Fin 1 => y)
    rw [hb] at h
    exact h
  -- the distinguished definable set and the base subset
  have hDS₀ : {a : 𝔐 | χ.Realize b fun _ => a} ∩ Set.range (f : M₀ → 𝔐)
      = (f : M₀ → 𝔐) '' X := by
    ext z
    constructor
    · rintro ⟨hzD, y, rfl⟩
      exact ⟨y, (hXchar y).2 ((hmapb y).1 hzD), rfl⟩
    · rintro ⟨y, hyX, rfl⟩
      exact ⟨(hmapb y).2 ((hXchar y).1 hyX), ⟨y, rfl⟩⟩
  have hXc : X.Countable := Set.countable_coe_iff.1 (Cardinal.mk_le_aleph0_iff.1 hX.le)
  have hinjf : Function.Injective (f : M₀ → 𝔐) := f.injective
  have hDc : ({a : 𝔐 | χ.Realize b fun _ => a}
      ∩ Set.range (f : M₀ → 𝔐)).Countable := by
    rw [hDS₀]
    exact hXc.image _
  have hS₀u : ¬ (Set.range (f : M₀ → 𝔐)).Countable := by
    intro hc
    have h1 : #(Set.range (f : M₀ → 𝔐)) ≤ ℵ₀ :=
      Cardinal.mk_le_aleph0_iff.2 (Set.countable_coe_iff.2 hc)
    rw [Cardinal.mk_range_eq _ hinjf, hM₀] at h1
    exact absurd h1 (not_le.2 aleph0_lt_aleph_one)
  have hbrange : Set.range b ⊆ Set.range (f : M₀ → 𝔐) := by
    rintro z ⟨i, rfl⟩
    exact ⟨b₀ i, by rw [← hb]; rfl⟩
  have hDdef : (Set.range (f : M₀ → 𝔐)).Definable₁ L
      {a : 𝔐 | χ.Realize b fun _ => a} := (definable₁_of_boundedFormula χ b).mono hbrange
  -- grow the base subset to size at least `κ`
  obtain ⟨S, hS₀S, hSmd, hDS, hcard⟩ :=
    exists_meetsDefinable_large hL hst 𝔐 hsat hDdef (meetsDefinable_range f) hS₀u hDc
  -- package the result as a two-cardinal model
  obtain ⟨Sub, hSubcoe⟩ : ∃ Sub : L.ElementarySubstructure (𝔐 : Type), (Sub : Set 𝔐) = S :=
    ⟨hSmd.toElementarySubstructure, hSmd.closure_eq_self⟩
  have hmemSub : ∀ z : 𝔐, z ∈ Sub ↔ z ∈ S := fun z => by rw [← hSubcoe, SetLike.mem_coe]
  haveI : Nonempty ↥Sub :=
    ⟨⟨(f (Classical.arbitrary M₀) : 𝔐),
      (hmemSub _).2 (hS₀S ⟨Classical.arbitrary M₀, rfl⟩)⟩⟩
  haveI : (↥Sub) ⊨ T := (Sub.toModel T).is_model
  obtain ⟨b', hb'⟩ : ∃ b' : β → ↥Sub, ∀ i, ((b' i : 𝔐)) = b i :=
    ⟨fun i => ⟨b i, (hmemSub _).2 (hS₀S (hbrange ⟨i, rfl⟩))⟩, fun _ => rfl⟩
  have hsubtypeb : (Sub.subtype : ↥Sub → 𝔐) ∘ b' = b := funext hb'
  have hpre : {a : ↥Sub | χ.Realize b' fun _ => a}
      = Subtype.val ⁻¹' {a : 𝔐 | χ.Realize b fun _ => a} := by
    ext a
    have h := Sub.subtype.map_boundedFormula χ b' (fun _ : Fin 1 => a)
    rw [hsubtypeb] at h
    exact h.symm
  have hrangeval : Set.range (Subtype.val : ↥Sub → 𝔐) = S := by
    rw [← hSubcoe]
    ext z
    simp
  have himg : (Subtype.val : ↥Sub → 𝔐) '' (Subtype.val ⁻¹' {a : 𝔐 | χ.Realize b fun _ => a})
      = {a : 𝔐 | χ.Realize b fun _ => a} ∩ S := by
    rw [Set.image_preimage_eq_inter_range, hrangeval]
  have hlam : #{a : ↥Sub | χ.Realize b' fun _ => a} = ℵ₀ := by
    have h1 := Cardinal.mk_image_eq (f := (Subtype.val : ↥Sub → 𝔐))
      (s := Subtype.val ⁻¹' {a : 𝔐 | χ.Realize b fun _ => a}) Subtype.val_injective
    rw [himg, hDS, hDS₀, Cardinal.mk_image_eq hinjf, hX] at h1
    rw [hpre]
    exact h1.symm
  refine ⟨#(↥Sub), ℵ₀, ?_, le_rfl, hκ,
    hasTwoCardinalModel_of_boundedFormula (T := T) (↥Sub) χ b' rfl hlam⟩
  have hmk : #(↥Sub) = #(↥S) := Cardinal.mk_congr (Equiv.setCongr hSubcoe)
  rw [hmk]
  exact hcard

/-- **Two-cardinal transfer for `ω`-stable theories.**  An `ω`-stable complete theory in a
countable language which has a Vaughtian pair has, in *every* uncountable cardinal `κ`, a model of
cardinality `κ` containing an infinite parameter-definable subset of cardinality `< κ`.

This discharges the hypothesis `Submission.Morley.OmegaStableTwoCardinal` of
`Submission.Morley.morley_categoricity`. -/
theorem omegaStableTwoCardinal (L : FirstOrder.Language.{0, 0}) : OmegaStableTwoCardinal L :=
  omegaStableTwoCardinal_of_largeTwoCardinalModels (largeTwoCardinalModels L)

/-- **Morley's categoricity theorem, modulo the saturation principle alone.**  With
`Submission.Morley.omegaStableTwoCardinal` in hand, the only hypothesis left in
`Submission.Morley.morley_categoricity` is `Submission.Morley.SaturationPrinciple`. -/
theorem morley_categoricity_of_saturationPrinciple {L : FirstOrder.Language.{0, 0}}
    (hSat : SaturationPrinciple L) (hL : L.card ≤ ℵ₀) {T : L.Theory} (hT : T.IsComplete)
    (hInf : ∀ M : T.ModelType.{0, 0, 0}, Infinite M) {κ : Cardinal.{0}} (hκ : ℵ₀ < κ)
    (hcat : κ.Categorical T) {μ : Cardinal.{0}} (hμ : ℵ₀ < μ) : μ.Categorical T :=
  morley_categoricity hSat (omegaStableTwoCardinal L) hL hT hInf hκ hcat hμ

end Main

end Submission.Morley

