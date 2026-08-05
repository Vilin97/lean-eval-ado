import Mathlib
import Submission.Morley.StronglyMinimal

/-!
# Indiscernibility of independent tuples in a minimal set

This file supplies the second of the two ingredients that
`Submission/Morley/StronglyMinimal.lean` lists as missing from
`Submission.Morley.SaturationPrinciple`:

> two `C`-independent `n`-tuples from a minimal set `D` realise the same type over `C`.

The `n = 1` case is `Submission.Morley.typeOfElem_eq_of_notMem_alg`; the inductive step needs the
`n`-variable analogue of `Submission.Morley.fewRight`, which is `Submission.Morley.fewFiber`
below.

## Main definitions

* `Submission.Morley.fewFiber R n`: for a relation `R ⊆ (α ⊕ Fin 1) → M`, the set of tuples
  `x : α → M` whose fibre `{y | Sum.elim x (fun _ => y) ∈ R}` contains no injective
  `(n + 1)`-tuple, i.e. has at most `n` elements.  This is the `α`-variable analogue of
  `Submission.Morley.fewRight`, and it is definable over the parameters of `R` by
  `Submission.Morley.definable_fewFiber`.

## Main results

* `Submission.Morley.typeOver_eq_iff_forall_definable`: two tuples realise the same type over `C`
  exactly when they belong to the same `C`-definable sets.  This is the bridge between the
  syntactic `Submission.Morley.typeOver` and the definable-sets toolkit of
  `Submission/Morley/StronglyMinimal.lean`.
* `Submission.Morley.definable_fewFiber`: the `n`-variable analogue of
  `Submission.Morley.definable₁_fewRight`.
* `Submission.Morley.definable₁_fiber_sum`: the fibre of a `C`-definable relation over a tuple
  `x` is definable over `C` together with the entries of `x`; the `n`-variable analogue of
  `Submission.Morley.definable₁_fiber_right`.
* `Submission.Morley.typeOver_sumElim_eq`: **the inductive step.**  If `a` and `b` realise the
  same type over `C` and `u`, `v` are points of `D` generic over `C` together with `a`,
  respectively `b`, then `a ⌢ u` and `b ⌢ v` realise the same type over `C`.
* `Submission.Morley.typeOver_eq_of_indep`: **indiscernibility of independent tuples.**
* `Submission.Morley.typeOver_eq_of_indep_of_injOn`: the same statement for two injective
  enumerations of parts of `C`-independent subsets of `D`, which is the form in which the
  Baldwin–Lachlan argument uses it (a bijection between bases of the minimal sets of two models
  is elementary over the parameters).
* `Submission.Morley.typeOfElem_eq_of_indep_one`: the `n = 1` instance, which is
  `Submission.Morley.typeOfElem_eq_of_notMem_alg` again.

## The proof

Induction on `n`.  Write `a = a' ⌢ u` and `b = b' ⌢ v`.  By induction `a'` and `b'` realise the
same type over `C`.  Let `R` be a `C`-definable set of `(n+1)`-tuples containing `a`, and let
`Y_{a'} = {y | a' ⌢ y ∈ R}` be the fibre of `R` over `a'`; it is definable over `C` together with
the entries of `a'`, so by minimality of `D` either `D ∩ Y_{a'}` is finite — impossible, since it
would exhibit `u` as algebraic over `C` together with `a'` — or `D \ Y_{a'}` is finite, of size
`k` say.  The set of tuples `x` with `D \ Y_x` of size at most `k` is `fewFiber Θ k` for the
`C`-definable relation `Θ` of pairs `(x, y)` with `y ∈ D` and `x ⌢ y ∉ R`, hence is `C`-definable;
it contains `a'`, hence also `b'`.  So `D \ Y_{b'}` is finite and definable over `C` together with
the entries of `b'`; as `v ∈ D` is not algebraic over that set, `v ∈ Y_{b'}`, that is, `b ∈ R`.

Note that no automorphism, and no monster model, is needed: the transport of `a'` to `b'` happens
entirely inside the definable set `fewFiber Θ k`.
-/

open Cardinal Set FirstOrder Language Theory

namespace Submission.Morley

/-! ## Types of tuples and definable sets -/

section TypesOfTuples

variable {L : FirstOrder.Language.{0, 0}} {M : Type} [L.Structure M] [Nonempty M]

/-- **Two tuples realise the same type over `C` exactly when they lie in the same `C`-definable
sets.**  This is the tuple analogue of the identification of `Submission.Morley.S₁` with the
Boolean algebra of definable subsets of `M`, and it is what lets the whole argument be run with
the definable-sets toolkit rather than with formulas. -/
theorem typeOver_eq_iff_forall_definable {C : Set M} {α : Type} {a b : α → M} :
    (typeOver C a : CompleteTypeOver L C α) = typeOver C b ↔
      ∀ s : Set (α → M), C.Definable L s → (a ∈ s ↔ b ∈ s) := by
  constructor
  · rintro h s ⟨φ, rfl⟩
    have ha : (Formula.equivSentence φ ∈ (typeOver C a : CompleteTypeOver L C α))
        ↔ φ.Realize a := Theory.CompleteType.formula_mem_typeOf
    have hb : (Formula.equivSentence φ ∈ (typeOver C b : CompleteTypeOver L C α))
        ↔ φ.Realize b := Theory.CompleteType.formula_mem_typeOf
    rw [Set.mem_setOf_eq, Set.mem_setOf_eq, ← ha, ← hb, h]
  · intro h
    refine Theory.CompleteType.eq_of_le fun ψ hψ => ?_
    have hd : C.Definable L {v : α → M | (Formula.equivSentence.symm ψ).Realize v} :=
      ⟨Formula.equivSentence.symm ψ, rfl⟩
    have hab := h _ hd
    have hψ' : ψ ∈ (typeOver C a : CompleteTypeOver L C α) := hψ
    show ψ ∈ (typeOver C b : CompleteTypeOver L C α)
    rw [Theory.CompleteType.mem_typeOf] at hψ' ⊢
    exact hab.1 hψ'

/-- Reindexing two tuples along a common map preserves equality of their types. -/
theorem typeOver_comp_eq {C : Set M} {α β : Type} {a b : α → M}
    (h : (typeOver C a : CompleteTypeOver L C α) = typeOver C b) (e : β → α) :
    (typeOver C (a ∘ e) : CompleteTypeOver L C β) = typeOver C (b ∘ e) := by
  rw [typeOver_eq_iff_forall_definable] at h ⊢
  intro s hs
  exact h _ (hs.preimage_comp e)

end TypesOfTuples

/-! ## Counting in several variables -/

section Counting

variable {L : FirstOrder.Language.{0, 0}} {M : Type} [L.Structure M]

/-- `fewFiber R n` is the set of tuples `x : α → M` whose fibre
`{y : M | Sum.elim x (fun _ => y) ∈ R}` contains no injective `(n + 1)`-tuple, i.e. has at most
`n` elements.  For `α = Fin 1` this is `Submission.Morley.fewRight` up to reindexing. -/
def fewFiber {α : Type} (R : Set ((α ⊕ Fin 1) → M)) (n : ℕ) : Set (α → M) :=
  {x : α → M | ¬ ∃ v : Fin (n + 1) → M, Function.Injective v ∧
    ∀ i, Sum.elim x (fun _ => v i) ∈ R}

theorem mem_fewFiber_iff {α : Type} {R : Set ((α ⊕ Fin 1) → M)} {n : ℕ} {x : α → M} :
    x ∈ fewFiber R n ↔ ¬ ∃ v : Fin (n + 1) → M, Function.Injective v ∧
      ∀ i, Sum.elim x (fun _ => v i) ∈ R := Iff.rfl

/-- The fibre of `R` over `x`, as a subset of `M`. -/
theorem fewFiber_eq_of_fiber {α : Type} {R : Set ((α ⊕ Fin 1) → M)} {n : ℕ} {x : α → M}
    (s : Set M) (hs : s = {y : M | Sum.elim x (fun _ : Fin 1 => y) ∈ R}) :
    x ∈ fewFiber R n ↔ ¬ ∃ v : Fin (n + 1) → M, Function.Injective v ∧ ∀ i, v i ∈ s := by
  subst hs; exact Iff.rfl

/-- **The `n`-variable analogue of `Submission.Morley.definable₁_fewRight`**: having a small
fibre is a definable condition on the base tuple, uniformly in the tuple. -/
theorem definable_fewFiber {A : Set M} {α : Type} {R : Set ((α ⊕ Fin 1) → M)}
    (hR : A.Definable L R) (n : ℕ) : A.Definable L (fewFiber R n) := by
  classical
  -- the injectivity conditions on the new block of variables
  have h1 : ∀ ij : {p : Fin (n + 1) × Fin (n + 1) // p.1 ≠ p.2},
      A.Definable L {u : (α ⊕ Fin (n + 1)) → M |
        u (Sum.inr ij.1.1) ≠ u (Sum.inr ij.1.2)} := fun ij =>
    (definable_apply_eq (L := L) (A := A)
      (Sum.inr ij.1.1 : α ⊕ Fin (n + 1)) (Sum.inr ij.1.2)).compl
  -- the conditions saying that each new variable lies in the fibre
  have h2 : ∀ i : Fin (n + 1),
      A.Definable L {u : (α ⊕ Fin (n + 1)) → M |
        u ∘ (Sum.elim Sum.inl fun _ : Fin 1 => Sum.inr i) ∈ R} := fun i =>
    hR.preimage_comp (Sum.elim Sum.inl fun _ : Fin 1 => Sum.inr i)
  have hWdef : A.Definable L
      ((⋂ ij : {p : Fin (n + 1) × Fin (n + 1) // p.1 ≠ p.2},
          {u : (α ⊕ Fin (n + 1)) → M | u (Sum.inr ij.1.1) ≠ u (Sum.inr ij.1.2)}) ∩
        ⋂ i : Fin (n + 1), {u : (α ⊕ Fin (n + 1)) → M |
          u ∘ (Sum.elim Sum.inl fun _ : Fin 1 => Sum.inr i) ∈ R}) :=
    (Set.definable_iInter_of_finite h1).inter (Set.definable_iInter_of_finite h2)
  have hex := hWdef.exists_of_finite (α := α) (β := Fin (n + 1))
  have hcomp : ∀ (x : α → M) (u : Fin (n + 1) → M) (i : Fin (n + 1)),
      (Sum.elim x u) ∘ (Sum.elim Sum.inl fun _ : Fin 1 => Sum.inr i)
        = Sum.elim x fun _ : Fin 1 => u i := by
    intro x u i
    funext z
    rcases z with a | j
    · rfl
    · rfl
  have hset : fewFiber R n =
      {v : α → M | ∃ u : Fin (n + 1) → M, Sum.elim v u ∈
        ((⋂ ij : {p : Fin (n + 1) × Fin (n + 1) // p.1 ≠ p.2},
            {u : (α ⊕ Fin (n + 1)) → M | u (Sum.inr ij.1.1) ≠ u (Sum.inr ij.1.2)}) ∩
          ⋂ i : Fin (n + 1), {u : (α ⊕ Fin (n + 1)) → M |
            u ∘ (Sum.elim Sum.inl fun _ : Fin 1 => Sum.inr i) ∈ R})}ᶜ := by
    ext x
    simp only [fewFiber, Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_inter_iff, Set.mem_iInter,
      Sum.elim_inr]
    constructor
    · rintro hno ⟨u, hu1, hu2⟩
      refine hno ⟨u, fun i j hij => by
        by_contra hne
        exact (hu1 ⟨(i, j), hne⟩) hij, fun i => ?_⟩
      have := hu2 i
      rwa [hcomp x u i] at this
    · rintro hno ⟨u, hu1, hu2⟩
      refine hno ⟨u, fun ij => fun hc => ij.2 (hu1 hc), fun i => ?_⟩
      rw [hcomp x u i]
      exact hu2 i
  rw [hset]
  exact hex.compl

/-- **The `n`-variable analogue of `Submission.Morley.definable₁_fiber_right`**: the fibre of a
`C`-definable relation over a tuple `x` is definable over `C` together with the entries of `x`. -/
theorem definable₁_fiber_sum {C : Set M} {α : Type} {R : Set ((α ⊕ Fin 1) → M)}
    (hR : C.Definable L R) (x : α → M) :
    (C ∪ Set.range x).Definable₁ L {y : M | Sum.elim x (fun _ : Fin 1 => y) ∈ R} := by
  have hCB : ∀ c : C, (c : M) ∈ C ∪ Set.range x := fun c => Set.mem_union_left _ c.2
  have hxB : ∀ i : α, x i ∈ C ∪ Set.range x := fun i =>
    Set.mem_union_right _ (Set.mem_range_self i)
  obtain ⟨t, ht, hmem⟩ := exists_definable_subst (α := α ⊕ Fin 1) (β := Fin 1) hR
    (fun c : C => (Sum.inl ⟨(c : M), hCB c⟩ : (C ∪ Set.range x : Set M) ⊕ Fin 1))
    (Sum.elim (fun i : α => (Sum.inl ⟨x i, hxB i⟩ : (C ∪ Set.range x : Set M) ⊕ Fin 1))
      fun _ : Fin 1 => Sum.inr 0)
  have hset : t = {u : Fin 1 → M | u 0 ∈ {y : M | Sum.elim x (fun _ : Fin 1 => y) ∈ R}} := by
    ext u
    rw [hmem u fun _ => rfl]
    exact iff_of_eq (congrArg (fun w : (α ⊕ Fin 1) → M => w ∈ R)
      (funext fun i => by rcases i with a | j <;> rfl))
  rw [Set.Definable₁, ← hset]
  exact ht

end Counting

/-! ## The inductive step -/

section Step

variable {L : FirstOrder.Language.{0, 0}} {M : Type} [L.Structure M] [Nonempty M]

/-- **The inductive step of indiscernibility.**

If the tuples `a` and `b` realise the same type over `C`, and `u`, `v` are points of the minimal
set `D` not algebraic over `C` together with the entries of `a`, respectively of `b`, then the
extended tuples `a ⌢ u` and `b ⌢ v` realise the same type over `C`. -/
theorem typeOver_sumElim_eq {D : Set M} (hD : IsMinimalSet L D) {C : Set M}
    (hDC : C.Definable₁ L D) {α : Type} {a b : α → M}
    (hab : (typeOver C a : CompleteTypeOver L C α) = typeOver C b)
    {u v : M} (hu : u ∈ D) (hv : v ∈ D)
    (hnu : u ∉ Alg L (C ∪ Set.range a)) (hnv : v ∉ Alg L (C ∪ Set.range b)) :
    (typeOver C (Sum.elim a fun _ : Fin 1 => u) : CompleteTypeOver L C (α ⊕ Fin 1))
      = typeOver C (Sum.elim b fun _ : Fin 1 => v) := by
  classical
  -- One direction, applied twice.
  have key : ∀ a b : α → M, ∀ u v : M,
      (typeOver C a : CompleteTypeOver L C α) = typeOver C b →
      u ∈ D → v ∈ D → u ∉ Alg L (C ∪ Set.range a) → v ∉ Alg L (C ∪ Set.range b) →
      ∀ R : Set ((α ⊕ Fin 1) → M), C.Definable L R →
        (Sum.elim a fun _ : Fin 1 => u) ∈ R → (Sum.elim b fun _ : Fin 1 => v) ∈ R := by
    intro a b u v hab hu hv hnu hnv R hR hmem
    by_contra hcon
    -- `Θ` relates `x` to the points of `D` *outside* the fibre of `R` over `x`.
    set Θ : Set ((α ⊕ Fin 1) → M) :=
      {w : (α ⊕ Fin 1) → M | w (Sum.inr 0) ∈ D} \ R with hΘ
    have hΘdef : C.Definable L Θ := (definable_apply_mem hDC (Sum.inr 0)).sdiff hR
    have hfib : ∀ x : α → M, {y : M | Sum.elim x (fun _ : Fin 1 => y) ∈ Θ}
        = D \ {y : M | Sum.elim x (fun _ : Fin 1 => y) ∈ R} := by
      intro x
      ext y
      simp only [hΘ, Set.mem_setOf_eq, Set.mem_sdiff, Sum.elim_inr]
    -- the fibre of `R` over `a`
    have hYadef : (C ∪ Set.range a).Definable₁ L
        {y : M | Sum.elim a (fun _ : Fin 1 => y) ∈ R} := definable₁_fiber_sum hR a
    have hDa : (C ∪ Set.range a).Definable₁ L D := hDC.mono Set.subset_union_left
    have hcof : (D \ {y : M | Sum.elim a (fun _ : Fin 1 => y) ∈ R}).Finite := by
      rcases hD.2 _ (hYadef.mono (Set.subset_univ _)) with hfin | hcofin
      · exact absurd ⟨_, definable₁_inter hDa hYadef, hfin, hu, hmem⟩ hnu
      · exact hcofin
    -- `a` has a small `Θ`-fibre, hence so does `b`
    have hafew : a ∈ fewFiber Θ (D \ {y : M | Sum.elim a (fun _ : Fin 1 => y) ∈ R}).ncard := by
      rw [fewFiber_eq_of_fiber _ (hfib a)]
      exact no_injective_of_ncard_le hcof le_rfl
    have hbfew : b ∈ fewFiber Θ (D \ {y : M | Sum.elim a (fun _ : Fin 1 => y) ∈ R}).ncard := by
      rw [typeOver_eq_iff_forall_definable] at hab
      exact (hab _ (definable_fewFiber hΘdef _)).1 hafew
    have hbfin : (D \ {y : M | Sum.elim b (fun _ : Fin 1 => y) ∈ R}).Finite := by
      rw [fewFiber_eq_of_fiber _ (hfib b)] at hbfew
      exact (finite_ncard_le_of_no_injective hbfew).1
    -- but then `v` is algebraic over `C` together with the entries of `b`
    exact hnv ⟨_, definable₁_sdiff (hDC.mono Set.subset_union_left) (definable₁_fiber_sum hR b),
      hbfin, hv, hcon⟩
  rw [typeOver_eq_iff_forall_definable]
  exact fun R hR => ⟨key a b u v hab hu hv hnu hnv R hR,
    key b a v u hab.symm hv hu hnv hnu R hR⟩

end Step

/-! ## Indiscernibility of independent tuples -/

section Indisc

variable {L : FirstOrder.Language.{0, 0}} {M : Type} [L.Structure M] [Nonempty M]

omit [Nonempty M] in
/-- Splitting a tuple indexed by `Fin (n + 1)` into its first `n` entries and its last one. -/
theorem sumElim_comp_finSumFinEquiv_symm {n : ℕ} (c : Fin (n + 1) → M) :
    (Sum.elim (c ∘ Fin.castSucc) fun _ : Fin 1 => c (Fin.last n))
        ∘ (finSumFinEquiv.symm : Fin (n + 1) → Fin n ⊕ Fin 1) = c := by
  have h : (Sum.elim (c ∘ Fin.castSucc) fun _ : Fin 1 => c (Fin.last n))
      = c ∘ (finSumFinEquiv : Fin n ⊕ Fin 1 → Fin (n + 1)) := by
    funext z
    rcases z with j | j
    · simp [Fin.castSucc, Fin.castAdd, Fin.castLE]
    · have hj : j = 0 := Subsingleton.elim _ _
      subst hj
      simp only [Sum.elim_inr, Function.comp_apply, finSumFinEquiv_apply_right]
      congr 1
  rw [h]
  funext i
  simp

omit [Nonempty M] in
/-- The entries of a tuple other than the last one are exactly the entries of its initial
segment. -/
theorem range_comp_castSucc {n : ℕ} (c : Fin (n + 1) → M) :
    Set.range (c ∘ Fin.castSucc) = c '' {j : Fin (n + 1) | j ≠ Fin.last n} := by
  rw [Set.range_comp]
  congr 1
  ext j
  simp only [Set.mem_range, Set.mem_setOf_eq]
  exact Fin.exists_castSucc_eq

/-- **Indiscernibility of independent tuples in a minimal set.**

Two `n`-tuples of elements of a minimal set `D`, each of them independent over the parameter set
`C` defining `D` — no entry algebraic over `C` together with the other entries — realise one and
the same complete `n`-type over `C`.

For `n = 1` this is `Submission.Morley.typeOfElem_eq_of_notMem_alg`, the uniqueness of the generic
type of `D`; the induction on `n` is `Submission.Morley.typeOver_sumElim_eq`, which rests on the
`n`-variable counting of `Submission.Morley.definable_fewFiber`. -/
theorem typeOver_eq_of_indep {D : Set M} (hD : IsMinimalSet L D) {C : Set M}
    (hDC : C.Definable₁ L D) {n : ℕ} (a b : Fin n → M)
    (ha : ∀ i, a i ∈ D) (hb : ∀ i, b i ∈ D)
    (hai : ∀ i, a i ∉ Alg L (C ∪ a '' {j | j ≠ i}))
    (hbi : ∀ i, b i ∉ Alg L (C ∪ b '' {j | j ≠ i})) :
    (typeOver C a : CompleteTypeOver L C (Fin n)) = typeOver C b := by
  induction n with
  | zero =>
    have hab : a = b := funext fun i => i.elim0
    rw [hab]
  | succ n IH =>
    -- passing to the initial segment preserves independence
    have htail : ∀ c : Fin (n + 1) → M, (∀ i, c i ∉ Alg L (C ∪ c '' {j | j ≠ i})) →
        ∀ i : Fin n, (c ∘ Fin.castSucc) i ∉
          Alg L (C ∪ (c ∘ Fin.castSucc) '' {j : Fin n | j ≠ i}) := by
      intro c hc i hmem
      refine hc i.castSucc (alg_mono ?_ hmem)
      refine Set.union_subset_union_right _ ?_
      rintro _ ⟨j, hj, rfl⟩
      exact ⟨j.castSucc, fun hcon => hj (Fin.castSucc_injective n hcon), rfl⟩
    have hIH := IH (a ∘ Fin.castSucc) (b ∘ Fin.castSucc)
      (fun i => ha _) (fun i => hb _) (htail a hai) (htail b hbi)
    have hstep := typeOver_sumElim_eq hD hDC hIH (ha (Fin.last n)) (hb (Fin.last n))
      (by rw [range_comp_castSucc a]; exact hai (Fin.last n))
      (by rw [range_comp_castSucc b]; exact hbi (Fin.last n))
    have hfin := typeOver_comp_eq hstep (finSumFinEquiv.symm : Fin (n + 1) → Fin n ⊕ Fin 1)
    rwa [sumElim_comp_finSumFinEquiv_symm a, sumElim_comp_finSumFinEquiv_symm b] at hfin

/-- **Indiscernibility of bases.**  Two injective enumerations of the same length, one inside a
`C`-independent subset of the minimal set `D` and the other inside another such subset, realise
the same type over `C`.

This is the form in which the Baldwin–Lachlan argument uses indiscernibility: any injection of a
basis of the minimal set of one model into a basis of the minimal set of another is elementary
over the parameters. -/
theorem typeOver_eq_of_indep_of_injOn {D : Set M} (hD : IsMinimalSet L D) {C : Set M}
    (hDC : C.Definable₁ L D) {A B : Set M} (hAD : A ⊆ D) (hBD : B ⊆ D)
    (hA : Indep L C A) (hB : Indep L C B) {n : ℕ} {a b : Fin n → M}
    (haA : ∀ i, a i ∈ A) (hbB : ∀ i, b i ∈ B)
    (hainj : Function.Injective a) (hbinj : Function.Injective b) :
    (typeOver C a : CompleteTypeOver L C (Fin n)) = typeOver C b := by
  have key : ∀ (E : Set M) (c : Fin n → M), Indep L C E → (∀ i, c i ∈ E) →
      Function.Injective c → ∀ i, c i ∉ Alg L (C ∪ c '' {j | j ≠ i}) := by
    intro E c hE hcE hcinj i hmem
    refine hE (c i) (hcE i) (alg_mono ?_ hmem)
    refine Set.union_subset_union_right _ ?_
    rintro _ ⟨j, hj, rfl⟩
    exact ⟨hcE j, fun hcon => hj (hcinj hcon)⟩
  exact typeOver_eq_of_indep hD hDC a b (fun i => hAD (haA i)) (fun i => hBD (hbB i))
    (key A a hA haA hainj) (key B b hB hbB hbinj)

/-- **Consistency with the `n = 1` case.**  The one-variable instance of
`Submission.Morley.typeOver_eq_of_indep` is exactly
`Submission.Morley.typeOfElem_eq_of_notMem_alg`, the uniqueness of the generic type of a minimal
set: for a `1`-tuple the independence hypothesis says just that the entry is not algebraic
over `C`. -/
theorem typeOfElem_eq_of_indep_one {D : Set M} (hD : IsMinimalSet L D) {C : Set M}
    (hDC : C.Definable₁ L D) {a b : M} (ha : a ∈ D) (hna : a ∉ Alg L C) (hb : b ∈ D)
    (hnb : b ∉ Alg L C) : (typeOfElem C a : S₁ L C) = typeOfElem C b := by
  have hemp : ∀ i : Fin 1, {j : Fin 1 | j ≠ i} = (∅ : Set (Fin 1)) := by
    intro i
    ext j
    simp [Subsingleton.elim j i]
  exact typeOver_eq_of_indep hD hDC (fun _ => a) (fun _ => b) (fun _ => ha) (fun _ => hb)
    (fun i => by rw [hemp i, Set.image_empty, Set.union_empty]; exact hna)
    (fun i => by rw [hemp i, Set.image_empty, Set.union_empty]; exact hnb)

end Indisc

end Submission.Morley
