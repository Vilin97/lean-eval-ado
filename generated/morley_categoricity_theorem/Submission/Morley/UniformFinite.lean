import Mathlib
import Submission.Morley.Counting

/-!
# Uniform finiteness of fibres

If a theory `T` has no Vaughtian pair, then in any model `M` of `T` the finite fibres of a fixed
formula `χ` are uniformly bounded: there is a single `k` with `#χ(M, z̄) ≤ k` for every parameter
tuple `z̄` whose fibre is finite.

The proof is by contraposition.  Given fibres of unbounded finite size, one first passes to a very
large elementary extension `M'` of `M` (upward Löwenheim–Skolem), and then forms the ultrapower of
`M'` along the hyperfilter on `ℕ`.  In the ultrapower the diagonal parameter tuple has an *infinite*
fibre (by Łoś's theorem, since the fibres are unboundedly large), yet that fibre is a quotient of a
product of finite sets, so it has cardinality at most `2 ^ ℵ₀`; the ultrapower itself is at least as
big as `M'`, which was chosen bigger than `2 ^ ℵ₀`.  This is a two-cardinal model, and
`Submission.Morley.hasVaughtianPair_of_hasTwoCardinalModel` turns it into a Vaughtian pair.

## Main results

* `Submission.Morley.hasVaughtianPair_of_unbounded_finite_fiber`
* `Submission.Morley.exists_bound_ncard_fiber`
-/

namespace Submission.Morley

open Cardinal Set FirstOrder Language Theory

variable {L : FirstOrder.Language.{0, 0}}

/-! ## Counting formulas and the size of a fibre -/

/-- A fibre with at least `k` elements satisfies the `k`-th counting formula. -/
theorem realize_atLeastF_of_le_ncard {M : Type} [L.Structure M] {α : Type}
    {χ : L.Formula (α ⊕ Fin 1)} {z : α → M} {k : ℕ} (hk : k ≤ (fiber χ z).ncard) :
    (atLeastF χ k).Realize z := by
  rcases k with _ | m
  · rw [realize_atLeastF]
    exact ⟨Fin.elim0, fun i => i.elim0, fun i => i.elim0⟩
  · by_contra hcon
    have := (finite_ncard_le_of_not_realize_atLeastF hcon).2
    omega

/-- A finite fibre satisfying the `k`-th counting formula has at least `k` elements. -/
theorem le_ncard_of_realize_atLeastF {M : Type} [L.Structure M] {α : Type}
    {χ : L.Formula (α ⊕ Fin 1)} {z : α → M} {k : ℕ} (hfin : (fiber χ z).Finite)
    (hk : (atLeastF χ k).Realize z) : k ≤ (fiber χ z).ncard := by
  by_contra hcon
  rw [Nat.not_le] at hcon
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  exact not_realize_atLeastF_of_ncard_le hfin (by omega) hk

/-- An elementary embedding preserves finiteness of a fibre and does not shrink it. -/
theorem finite_and_ncard_le_map_of_elementaryEmbedding {M N : Type} [L.Structure M]
    [L.Structure N] (g : M ↪ₑ[L] N) {α : Type} {χ : L.Formula (α ⊕ Fin 1)} {z : α → M}
    (hfin : (fiber χ z).Finite) :
    (fiber χ fun i => g (z i)).Finite ∧
      (fiber χ z).ncard ≤ (fiber χ fun i => g (z i)).ncard := by
  have hmap : ∀ k : ℕ, (atLeastF χ k).Realize (fun i => g (z i)) ↔ (atLeastF χ k).Realize z := by
    intro k
    simpa [Function.comp_def] using g.map_formula (atLeastF χ k) z
  have h1 : ¬ (atLeastF χ ((fiber χ z).ncard + 1)).Realize fun i => g (z i) := by
    rw [hmap]
    exact not_realize_atLeastF_of_ncard_le hfin le_rfl
  have h2 := finite_ncard_le_of_not_realize_atLeastF h1
  exact ⟨h2.1,
    le_ncard_of_realize_atLeastF h2.1 ((hmap _).2 (realize_atLeastF_of_le_ncard le_rfl))⟩

/-- A unary formula with an arbitrary tuple of parameters defines its fibre over the range of the
parameters.  This is the version of `Submission.Morley.definable₁_of_formula` for an arbitrary
index type. -/
theorem definable₁_fiber {M : Type} [L.Structure M] {α : Type} (χ : L.Formula (α ⊕ Fin 1))
    (z : α → M) : (Set.range z).Definable₁ L (fiber χ z) := by
  classical
  rw [Set.Definable₁, Set.definable_iff_exists_formula_sum]
  refine ⟨χ.relabel (Sum.map (fun i => (⟨z i, Set.mem_range_self i⟩ : Set.range z)) id), ?_⟩
  ext v
  simp only [fiber, Set.mem_setOf_eq, Formula.realize_relabel]
  congr! 1
  ext (i | i)
  · simp
  · exact congrArg v (Subsingleton.elim _ _)

/-! ## The ultrapower construction -/

/-- **Unboundedly large finite fibres give a two-cardinal model.**

If `M'` carries fibres of `χ` which are all finite but of unbounded size, then the ultrapower of
`M'` along the hyperfilter on `ℕ` is a model of `T`, at least as large as `M'`, in which some
parameter-definable set is infinite of cardinality at most `2 ^ ℵ₀`. -/
theorem exists_definable_infinite_le_continuum {T : L.Theory} {M' : Type} [L.Structure M']
    [Nonempty M'] [M' ⊨ T] {α : Type} (χ : L.Formula (α ⊕ Fin 1)) (w : ℕ → α → M')
    (hfin : ∀ n, (fiber χ (w n)).Finite) (hcard : ∀ n, n ≤ (fiber χ (w n)).ncard) :
    ∃ (P : T.ModelType.{0, 0, 0}) (A X : Set P),
      A.Definable₁ L X ∧ X.Infinite ∧ #X ≤ 2 ^ ℵ₀ ∧ #M' ≤ #(P : Type) := by
  classical
  haveI hmod : ((Filter.hyperfilter ℕ : Filter ℕ).Product fun _ : ℕ => M') ⊨ T :=
    (Theory.model_iff T).2 fun φ hφ => by
      rw [Ultraproduct.sentence_realize]
      exact Filter.Eventually.of_forall fun _ => Theory.realize_sentence_of_mem T hφ
  obtain ⟨zs, hzs⟩ : ∃ zs : α → ((Filter.hyperfilter ℕ : Filter ℕ).Product fun _ : ℕ => M'),
      zs = fun i => ((fun n => w n i : ∀ _ : ℕ, M') :
        (Filter.hyperfilter ℕ : Filter ℕ).Product fun _ : ℕ => M') := ⟨_, rfl⟩
  -- Łoś's theorem: the diagonal fibre satisfies every counting formula, so it is infinite.
  have hinf : (fiber χ zs).Infinite := by
    refine infinite_fiber_of_forall_realize_atLeastF fun k => ?_
    rw [hzs]
    refine (Ultraproduct.realize_formula_cast (atLeastF χ k) fun i n => w n i).2 ?_
    have hmem : {n : ℕ | k ≤ n} ∈ (Filter.hyperfilter ℕ : Filter ℕ) := by
      refine Filter.mem_hyperfilter_of_finite_compl
        ((Set.finite_Iio k).subset fun n hn => ?_)
      simpa using hn
    filter_upwards [hmem] with n hn
    exact realize_atLeastF_of_le_ncard (hn.trans (hcard n))
  -- The diagonal fibre is small: it is covered by a product of finite sets.
  obtain ⟨d⟩ := ‹Nonempty M'›
  have hsub : fiber χ zs ⊆
      (fun t : ℕ → M' => ((t : ∀ _ : ℕ, M') :
          (Filter.hyperfilter ℕ : Filter ℕ).Product fun _ : ℕ => M')) ''
        {t : ℕ → M' | ∀ n, t n ∈ insert d (fiber χ (w n))} := by
    intro x hx
    revert hx
    refine Quotient.inductionOn x ?_
    intro t hx
    have heq : (fun j => ((Sum.elim (fun i (n : ℕ) => w n i) (fun _ => t) j : ∀ _ : ℕ, M') :
          (Filter.hyperfilter ℕ : Filter ℕ).Product fun _ : ℕ => M'))
        = Sum.elim zs fun _ : Fin 1 => ((t : ∀ _ : ℕ, M') :
          (Filter.hyperfilter ℕ : Filter ℕ).Product fun _ : ℕ => M') := by
      funext j
      rcases j with i | i <;> simp [hzs]
    have hlos := Ultraproduct.realize_formula_cast (u := Filter.hyperfilter ℕ) χ
      (Sum.elim (fun i (n : ℕ) => w n i) fun _ => t)
    rw [heq] at hlos
    have hmem : ∀ᶠ n : ℕ in (Filter.hyperfilter ℕ : Filter ℕ), t n ∈ fiber χ (w n) := by
      filter_upwards [hlos.1 hx] with n hn
      have hre : (fun j => Sum.elim (fun i (m : ℕ) => w m i) (fun _ => t) j n)
          = Sum.elim (w n) fun _ : Fin 1 => t n := by
        funext j; rcases j with i | i <;> rfl
      rw [hre] at hn
      exact hn
    refine ⟨fun n => if t n ∈ fiber χ (w n) then t n else d, fun n => ?_, ?_⟩
    · by_cases hc : t n ∈ fiber χ (w n) <;> simp [hc]
    · refine Quotient.sound ?_
      filter_upwards [hmem] with n hn
      simp [hn]
  have hsmall : #(fiber χ zs) ≤ 2 ^ ℵ₀ := by
    refine (Cardinal.mk_le_mk_of_subset hsub).trans (Cardinal.mk_image_le.trans ?_)
    have hcount : ∀ n : ℕ, ∃ f : (insert d (fiber χ (w n)) : Set M') → ℕ, Function.Injective f :=
      fun n => Set.countable_iff_exists_injective.1 ((hfin n).insert d).countable
    choose e he using hcount
    have hinj : Function.Injective
        (fun y : {t : ℕ → M' | ∀ n, t n ∈ insert d (fiber χ (w n))} =>
          fun n => e n ⟨y.1 n, y.2 n⟩) := by
      intro y1 y2 hy
      exact Subtype.ext (funext fun n => congrArg Subtype.val (he n (congrFun hy n)))
    refine (Cardinal.mk_le_of_injective hinj).trans ?_
    rw [Cardinal.mk_arrow, Cardinal.lift_id, Cardinal.mk_nat, Cardinal.aleph0_power_aleph0,
      Cardinal.two_power_aleph0]
  -- The ultrapower is at least as large as `M'`, via the diagonal.
  have hbig : #M' ≤ #((Filter.hyperfilter ℕ : Filter ℕ).Product fun _ : ℕ => M') := by
    refine Cardinal.mk_le_of_injective (f := fun a : M' => (((fun _ : ℕ => a) : ∀ _ : ℕ, M') :
      (Filter.hyperfilter ℕ : Filter ℕ).Product fun _ : ℕ => M')) ?_
    intro a b hab
    obtain ⟨n, hn⟩ := (Quotient.exact hab).exists
    exact hn
  exact ⟨Theory.ModelType.of T ((Filter.hyperfilter ℕ : Filter ℕ).Product fun _ : ℕ => M'),
    Set.range zs, fiber χ zs, definable₁_fiber χ zs, hinf, hsmall, hbig⟩

/-! ## The main results -/

/-- **Unboundedly large finite fibres produce a Vaughtian pair.** -/
theorem hasVaughtianPair_of_unbounded_finite_fiber (hL : L.card ≤ ℵ₀) {T : L.Theory}
    (M : T.ModelType.{0, 0, 0}) {α : Type} (χ : L.Formula (α ⊕ Fin 1))
    (h : ∀ k : ℕ, ∃ z : α → M, (fiber χ z).Finite ∧ k ≤ (fiber χ z).ncard) :
    HasVaughtianPair T := by
  classical
  -- `M` has finite fibres of arbitrarily large size, so it is infinite.
  haveI hMinf : Infinite (M : Type) := by
    rw [← not_finite_iff_infinite]
    intro hfin
    obtain ⟨z, -, hle⟩ := h (Nat.card (M : Type) + 1)
    have hb : (fiber χ z).ncard ≤ Nat.card (M : Type) := by
      have hu := Set.ncard_le_ncard (Set.subset_univ (fiber χ z)) Set.finite_univ
      rwa [Set.ncard_univ] at hu
    omega
  -- An elementary extension of `M` of cardinality bigger than `2 ^ ℵ₀`.
  have h1 : Cardinal.lift.{0} L.card ≤
      Cardinal.lift.{0} (max #(M : Type) (2 ^ (2 ^ ℵ₀ : Cardinal.{0}))) := by
    simp only [Cardinal.lift_id]
    exact hL.trans ((Cardinal.aleph0_le_mk (M : Type)).trans (le_max_left _ _))
  have h2 : Cardinal.lift.{0} #(M : Type) ≤
      Cardinal.lift.{0} (max #(M : Type) (2 ^ (2 ^ ℵ₀ : Cardinal.{0}))) := by
    simp only [Cardinal.lift_id]
    exact le_max_left _ _
  obtain ⟨N, ⟨f⟩, hNcard⟩ := exists_elementaryEmbedding_card_eq_of_ge L (M : Type)
    (max #(M : Type) (2 ^ (2 ^ ℵ₀ : Cardinal.{0}))) h1 h2
  haveI : Infinite (N : Type) := Infinite.of_injective f f.injective
  haveI : (N : Type) ⊨ T := (f.theory_model_iff T).1 inferInstance
  -- Transfer the fibres to the extension.
  choose z hz1 hz2 using h
  have hwfin : ∀ n : ℕ, (fiber χ fun i => f (z n i)).Finite := fun n =>
    (finite_and_ncard_le_map_of_elementaryEmbedding f (hz1 n)).1
  have hwcard : ∀ n : ℕ, n ≤ (fiber χ fun i => f (z n i)).ncard := fun n =>
    (hz2 n).trans (finite_and_ncard_le_map_of_elementaryEmbedding f (hz1 n)).2
  obtain ⟨P, A, X, hdef, hXinf, hXsmall, hbig⟩ :=
    exists_definable_infinite_le_continuum (T := T) χ (fun n i => f (z n i)) hwfin hwcard
  refine hasVaughtianPair_of_hasTwoCardinalModel hL (lam := #X) (κ := #(P : Type)) ?_ ?_
    ⟨P, A, X, hdef, rfl, rfl⟩
  · rw [← Cardinal.infinite_iff, Set.infinite_coe_iff]
    exact hXinf
  · calc #X ≤ 2 ^ ℵ₀ := hXsmall
      _ < 2 ^ (2 ^ ℵ₀ : Cardinal.{0}) := Cardinal.cantor _
      _ ≤ #(N : Type) := by rw [hNcard]; exact le_max_right _ _
      _ ≤ #(P : Type) := hbig

/-- **Absence of Vaughtian pairs gives a uniform bound on finite fibres.** -/
theorem exists_bound_ncard_fiber (hL : L.card ≤ ℵ₀) {T : L.Theory}
    (hvp : ¬HasVaughtianPair T) (M : T.ModelType.{0, 0, 0}) {α : Type}
    (χ : L.Formula (α ⊕ Fin 1)) :
    ∃ k : ℕ, ∀ z : α → M, (fiber χ z).Finite → (fiber χ z).ncard ≤ k := by
  by_contra hcon
  simp only [not_exists, not_forall, not_le] at hcon
  refine hvp (hasVaughtianPair_of_unbounded_finite_fiber hL M χ fun k => ?_)
  obtain ⟨z, hz1, hz2⟩ := hcon k
  exact ⟨z, hz1, hz2.le⟩

end Submission.Morley
