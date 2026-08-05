import Submission.Ado.PBW.Env
import Submission.Ado.PBW.Unitriangular
import Submission.Ado.PBW.Sorting

/-!
# The Poincaré–Birkhoff–Witt basis theorem

Let `K` be a field and `L` a Lie algebra over `K` with a basis `bas` indexed by
`Fin n`. Write `y i = ι K (bas i)` for the images of the basis vectors in the
universal enveloping algebra `U(L)`. For an exponent vector `a : Mon n` the
*ordered monomial* is the product

```
pbwMonomial bas a = y 0 ^ a 0 * y 1 ^ a 1 * ⋯ * y (n-1) ^ a (n-1)
```

taken in the canonical order of `Fin n`. The theorem proved here is that these
ordered monomials form a `K`-basis of `U(L)`; see `pbwBasis`.

## Note on the product

`U(L)` is not commutative, so `Finset.prod` is unavailable and the ordered
product has to be spelled as a `List.prod` over `List.finRange n` — this is
exactly "the product over `Finset.univ` in the canonical order of `Fin n`".

## Outline

Both halves are assembled from material proved elsewhere in this development.

*Linear independence* comes from the PBW module `Poly K n` of
`Submission/Ado/PBW/Defs.lean`: the evaluation map
`ev bas : U(L) →ₗ[K] Poly K n` of `Submission/Ado/PBW/Env.lean` sends
`pbwMonomial bas a` to `z^a` plus terms of strictly smaller degree
(`ev_pbwMonomial_sub_mono`), so `ev bas ∘ pbwMonomial bas` is a unitriangular
family in the sense of `Submission/Ado/PBW/Unitriangular.lean` and is therefore
linearly independent; hence so is `pbwMonomial bas` itself.

The triangularity computation rests on the two elementary invariants of the
construction, `act_of_aligned` and `act_sub_mono_degLE`, packaged here as the
power lemma `rho_pow_mono`.

*Spanning* comes from `Submission.Ado.span_sorted_prod_eq_top`: `U(L)` is
spanned by the sorted words `y i₁ ⋯ y i_m`, and every sorted word is an ordered
monomial (`sorted_prod_eq_pbwMonomial`).
-/

universe u

namespace Submission.Ado.PBW

open UniversalEnvelopingAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

variable {K : Type u} [Field K] {n : ℕ}

/-! ### Complements to the `DegLT` calculus -/

/-- The zero polynomial is supported in degrees `< d` for every `d`. -/
theorem DegLT_zero (d : ℕ) : DegLT (0 : Poly K n) d := by
  intro c hc
  simp only [Finsupp.support_zero, Finset.notMem_empty] at hc

/-- `DegLT` is monotone in the degree bound. -/
theorem DegLT_mono {f : Poly K n} {d d' : ℕ} (hf : DegLT f d) (hd : d ≤ d') : DegLT f d' :=
  fun c hc => lt_of_lt_of_le (hf c hc) hd

/-- A sum of two polynomials of degree `< d` has degree `< d`. -/
theorem DegLT_add {f g : Poly K n} {d : ℕ} (hf : DegLT f d) (hg : DegLT g d) :
    DegLT (f + g) d := by
  intro c hc
  rcases Finset.mem_union.mp (Finsupp.support_add hc) with hc | hc
  · exact hf c hc
  · exact hg c hc

/-- A polynomial supported in degrees `≤ d` is supported in degrees `< d + 1`. -/
theorem DegLT_succ_of_degLE {f : Poly K n} {d : ℕ} (h : DegLE f d) : DegLT f (d + 1) :=
  fun c hc => Nat.lt_succ_of_le (h c hc)

/-! ### Degrees of the exponent vectors `a + k • eⱼ` -/

/-- Adding `k` copies of the variable `zⱼ` to a monomial raises its degree by `k`. -/
theorem degree_add_nsmul_e (a : Mon n) (j : Fin n) (k : ℕ) :
    (a + k • e j).degree = a.degree + k := by
  induction k with
  | zero => simp
  | succ k ih => rw [succ_nsmul, ← add_assoc, degree_add_e, ih, Nat.add_assoc]

/-! ### Powers of `rho` -/

section Rho

variable {γ : Fin n → Fin n → Fin n → K}

/-- **The workhorse.** The action of a basis vector raises the degree by at most one. -/
theorem rho_degLE {j : Fin n} {f : Poly K n} {d : ℕ} (hf : DegLE f d) :
    DegLE (rho γ j f) (d + 1) := by
  have hrho : rho γ j f = Finsupp.linearCombination K (act γ j) f := rfl
  rw [hrho]
  exact DegLE_linearCombination fun c hc => DegLE_mono (act_degLE j c)
    (Nat.succ_le_succ (hf c hc))

/-- The strict form of `rho_degLE`. -/
theorem rho_degLT {j : Fin n} {f : Poly K n} {d : ℕ} (hf : DegLT f d) :
    DegLT (rho γ j f) (d + 1) := by
  cases d with
  | zero => rw [DegLT_zero_iff.mp hf, map_zero]; exact DegLT_zero _
  | succ m => exact DegLT_succ_of_degLE (rho_degLE hf.degLE)

/-- Applying a power of `rho` to a polynomial of degree `< d`: the degree grows by
at most the exponent. -/
theorem rho_pow_degLT {j : Fin n} {f : Poly K n} {d : ℕ} (hf : DegLT f d) (k : ℕ) :
    DegLT ((rho γ j ^ k) f) (d + k) := by
  induction k with
  | zero => simpa using hf
  | succ k ih =>
      have hs : ((rho γ j ^ (k + 1)) f) = rho γ j ((rho γ j ^ k) f) := by
        rw [pow_succ']; rfl
      rw [hs]
      exact rho_degLT ih

/-- **The key power lemma.** The `k`-th power of `ρ(xⱼ)` sends the monomial `z^a`
to `z^(a + k eⱼ)` plus terms of strictly smaller degree. -/
theorem rho_pow_mono (j : Fin n) (a : Mon n) (k : ℕ) :
    DegLT ((rho γ j ^ k) (mono a) - mono (a + k • e j)) (a.degree + k) := by
  induction k with
  | zero => simpa using DegLT_zero (K := K) (n := n) (a.degree + 0)
  | succ k ih =>
      have hs : ((rho γ j ^ (k + 1)) (mono a)) = rho γ j ((rho γ j ^ k) (mono a)) := by
        rw [pow_succ']; rfl
      have hsucc : a + (k + 1) • e j = (a + k • e j) + e j := by
        rw [succ_nsmul, ← add_assoc]
      have hsplit : (rho γ j ^ k) (mono a)
          = ((rho γ j ^ k) (mono a) - mono (a + k • e j)) + mono (a + k • e j) := by abel
      have hkey : (rho γ j ^ (k + 1)) (mono a) - mono (a + (k + 1) • e j)
          = rho γ j ((rho γ j ^ k) (mono a) - mono (a + k • e j))
            + (act γ j (a + k • e j) - mono ((a + k • e j) + e j)) := by
        rw [hs, hsucc]
        conv_lhs => rw [hsplit]
        rw [map_add, rho_mono]
        abel
      rw [hkey]
      refine DegLT_add (rho_degLT ih) (DegLT_succ_of_degLE ?_)
      have hd := act_sub_mono_degLE (γ := γ) j (a + k • e j)
      rw [degree_add_nsmul_e] at hd
      exact hd

end Rho

/-! ### The ordered monomials -/

section Monomial

variable {L : Type u} [LieRing L] [LieAlgebra K L]

/-- The **ordered monomial** `y 0 ^ a 0 * ⋯ * y (n-1) ^ a (n-1)` in `U(L)`, where
`y i = ι K (bas i)`. The product is taken over all of `Fin n` in the canonical
order; since `U(L)` is noncommutative this has to be spelled as a `List.prod`. -/
noncomputable def pbwMonomial (bas : Module.Basis (Fin n) K L) (a : Mon n) :
    UniversalEnvelopingAlgebra K L :=
  ((List.finRange n).map fun i => (ι K (bas i) : UniversalEnvelopingAlgebra K L) ^ a i).prod

/-- The ordered monomial with exponent vector `a`, written with `List.ofFn`. -/
theorem pbwMonomial_eq_ofFn (bas : Module.Basis (Fin n) K L) (a : Mon n) :
    pbwMonomial bas a
      = (List.ofFn fun i => (ι K (bas i) : UniversalEnvelopingAlgebra K L) ^ a i).prod := by
  rw [pbwMonomial, List.ofFn_eq_map]

/-- The empty ordered monomial is `1`. -/
@[simp] theorem pbwMonomial_zero (bas : Module.Basis (Fin n) K L) :
    pbwMonomial bas 0 = 1 := by
  simp [pbwMonomial]

/-! #### Multiplying an ordered monomial by a generator on the left -/

/-- **The `List.prod` lemma.** If the exponent vector `c` vanishes below `i`, then
multiplying the ordered product `∏ⱼ y j ^ c j` on the left by `y i` just increments
the exponent of `y i`. The list `l` is required to be strictly increasing and to
contain `i`; the case of interest is `l = List.finRange n`. -/
theorem mul_list_prod_pow {A : Type*} [Monoid A] (y : Fin n → A) {i : Fin n} {c : Mon n}
    (hc : ∀ j, j < i → c j = 0) :
    ∀ {l : List (Fin n)}, l.Pairwise (· < ·) → i ∈ l →
      y i * (l.map fun j => y j ^ c j).prod = (l.map fun j => y j ^ (c + e i) j).prod := by
  intro l
  induction l with
  | nil => intro _ hi; exact (List.not_mem_nil hi).elim
  | cons j t ih =>
      intro hl hi
      obtain ⟨hj, ht⟩ := List.pairwise_cons.mp hl
      by_cases hji : j = i
      · subst hji
        have hnot : ∀ k ∈ t, (c + e j) k = c k := fun k hk => by
          rw [Finsupp.add_apply, e_apply_of_ne (ne_of_lt (hj k hk)), add_zero]
        have hmap : (t.map fun k => y k ^ (c + e j) k) = t.map fun k => y k ^ c k :=
          List.map_congr_left fun k hk => by rw [hnot k hk]
        have hpow : y j ^ ((c + e j) j) = y j * y j ^ c j := by
          rw [Finsupp.add_apply, e_apply_self, pow_succ']
        rw [List.map_cons, List.map_cons, List.prod_cons, List.prod_cons, hmap, hpow,
          mul_assoc]
      · have hit : i ∈ t := by
          rcases List.mem_cons.mp hi with h | h
          · exact absurd h.symm hji
          · exact h
        have h1 : c j = 0 := hc j (hj i hit)
        have h2 : (c + e i) j = 0 := by
          rw [Finsupp.add_apply, h1, e_apply_of_ne (Ne.symm hji), add_zero]
        simp only [List.map_cons, List.prod_cons, h1, h2, pow_zero, one_mul]
        exact ih ht hit

/-! #### The exponent vector of a word -/

/-- The exponent vector of a word in the generators: `monOfList l` counts the
occurrences of each index in `l`. -/
noncomputable def monOfList : List (Fin n) → Mon n
  | [] => 0
  | i :: l => monOfList l + e i

/-- `monOfList l` counts occurrences. -/
theorem monOfList_apply (l : List (Fin n)) (i : Fin n) : monOfList l i = l.count i := by
  induction l with
  | nil => simp [monOfList]
  | cons j t ih =>
      rw [monOfList, Finsupp.add_apply, ih, List.count_cons]
      congr 1
      by_cases h : j = i
      · subst h; simp
      · rw [e_apply_of_ne h, if_neg (by simpa using fun hc => h (by simpa using hc))]

/-- The exponent vector of a sorted word vanishes below the first letter. -/
theorem monOfList_eq_zero_of_lt {l : List (Fin n)} {i : Fin n} (hl : ∀ k ∈ l, i ≤ k)
    {j : Fin n} (hj : j < i) : monOfList l j = 0 := by
  rw [monOfList_apply, List.count_eq_zero]
  exact fun hjl => absurd (hl j hjl) (not_le.mpr hj)

/-- **Every sorted word is an ordered monomial.** -/
theorem sorted_prod_eq_pbwMonomial (bas : Module.Basis (Fin n) K L) :
    ∀ {l : List (Fin n)}, l.Pairwise (· ≤ ·) →
      (l.map fun i => (ι K (bas i) : UniversalEnvelopingAlgebra K L)).prod
        = pbwMonomial bas (monOfList l) := by
  intro l
  induction l with
  | nil => simp [monOfList]
  | cons i t ih =>
      intro hl
      obtain ⟨hi, ht⟩ := List.pairwise_cons.mp hl
      rw [List.map_cons, List.prod_cons, ih ht, monOfList, pbwMonomial, pbwMonomial]
      exact mul_list_prod_pow (fun k => (ι K (bas k) : UniversalEnvelopingAlgebra K L))
        (fun j hj => monOfList_eq_zero_of_lt hi hj)
        (List.pairwise_lt_finRange n) (List.mem_finRange i)

end Monomial

/-! ### Triangularity of the evaluation map -/

section Triangular

variable {L : Type u} [LieRing L] [LieAlgebra K L]

/-- **Triangularity for a word of powers.** Applying the operators
`ρ(x_{i₁})^{a i₁}, …, ρ(x_{i_m})^{a i_m}` in turn to the monomial `z^b` produces
`z^(b + a i₁ e_{i₁} + ⋯ + a i_m e_{i_m})` plus terms of strictly smaller degree. -/
theorem degLT_list_prod_apply {γ : Fin n → Fin n → Fin n → K} (a : Mon n) :
    ∀ (l : List (Fin n)) (b : Mon n),
      DegLT ((l.map fun i => rho γ i ^ a i).prod (mono b)
          - mono (b + (l.map fun i => a i • e i).sum))
        (b + (l.map fun i => a i • e i).sum).degree := by
  intro l
  induction l with
  | nil =>
      intro b
      simpa using DegLT_zero (K := K) (n := n) (b + 0 : Mon n).degree
  | cons i t ih =>
      intro b
      set m : Mon n := (t.map fun i => a i • e i).sum with hm
      have hset : ((i :: t).map fun i => a i • e i).sum = a i • e i + m := by
        rw [List.map_cons, List.sum_cons, hm]
      have hb : b + (a i • e i + m) = (b + m) + a i • e i := by abel
      have hdeg : (b + (a i • e i + m)).degree = (b + m).degree + a i := by
        rw [hb, degree_add_nsmul_e]
      have happ : (((i :: t).map fun i => rho γ i ^ a i).prod) (mono b)
          = (rho γ i ^ a i) (((t.map fun i => rho γ i ^ a i).prod) (mono b)) := by
        rw [List.map_cons, List.prod_cons]; rfl
      rw [hset, happ, hdeg, hb]
      set Y := ((t.map fun i => rho γ i ^ a i).prod) (mono b)
      have hsplit : Y = (Y - mono (b + m)) + mono (b + m) := by abel
      have hkey : (rho γ i ^ a i) Y - mono ((b + m) + a i • e i)
          = (rho γ i ^ a i) (Y - mono (b + m))
            + ((rho γ i ^ a i) (mono (b + m)) - mono ((b + m) + a i • e i)) := by
        conv_lhs => rw [hsplit]
        rw [map_add]
        abel
      rw [hkey]
      exact DegLT_add (rho_pow_degLT (ih b) (a i)) (rho_pow_mono i (b + m) (a i))

/-- The exponent vectors of the variables, weighted by `a` and summed over all of
`Fin n`, reconstruct `a`. -/
theorem sum_map_nsmul_e_finRange (a : Mon n) :
    ((List.finRange n).map fun i => a i • e i).sum = a := by
  have h1 : ((List.finRange n).map fun i => a i • (e i : Mon n)).sum
      = ∑ i : Fin n, a i • (e i : Mon n) := by
    rw [← List.ofFn_eq_map, List.sum_ofFn]
  have h2 : ∀ i : Fin n, a i • (e i : Mon n) = Finsupp.single i (a i) := by
    intro i
    rw [e, Finsupp.smul_single, smul_eq_mul, mul_one]
  have h3 : a.sum Finsupp.single = ∑ i : Fin n, Finsupp.single i (a i) :=
    Finsupp.sum_fintype a _ fun i => Finsupp.single_zero i
  rw [h1, Finset.sum_congr rfl fun i _ => h2 i, ← h3, Finsupp.sum_single]

/-- The image of an ordered monomial under the enveloping action, as a word of
powers of the operators `rho`. -/
theorem envAction_pbwMonomial (bas : Module.Basis (Fin n) K L) (a : Mon n) :
    envAction bas (pbwMonomial bas a)
      = ((List.finRange n).map fun i => rho (gamma bas) i ^ a i).prod := by
  rw [pbwMonomial]
  induction (List.finRange n) with
  | nil => simp
  | cons i t ih =>
      rw [List.map_cons, List.prod_cons, map_mul, map_pow, envAction_ι, rhoL_basis,
        List.map_cons, List.prod_cons, ih]

/-- **Triangularity.** The evaluation map sends the ordered monomial with exponent
vector `a` to `z^a` plus terms of strictly smaller degree. -/
theorem ev_pbwMonomial_sub_mono (bas : Module.Basis (Fin n) K L) (a : Mon n) :
    DegLT (ev bas (pbwMonomial bas a) - mono a) a.degree := by
  have h := degLT_list_prod_apply (γ := gamma bas) a (List.finRange n) 0
  rw [sum_map_nsmul_e_finRange, zero_add] at h
  rwa [ev_apply, envAction_pbwMonomial]

/-- The composite `ev ∘ pbwMonomial` is a unitriangular family indexed by the
identity of `Mon n`. -/
theorem unitriangular_ev_pbwMonomial (bas : Module.Basis (Fin n) K L) :
    Unitriangular (id : Mon n → Mon n) fun a => ev bas (pbwMonomial bas a) :=
  fun a => ev_pbwMonomial_sub_mono bas a

end Triangular

/-! ### The basis theorem -/

section Basis

variable {L : Type u} [LieRing L] [LieAlgebra K L]

/-- **The linear-independence half of the Poincaré–Birkhoff–Witt theorem.** The
ordered monomials in the images of a basis of `L` are linearly independent in
`U(L)`. -/
theorem linearIndependent_pbwMonomial (bas : Module.Basis (Fin n) K L) :
    LinearIndependent K (pbwMonomial bas) := by
  refine LinearIndependent.of_comp (ev bas) ?_
  exact (unitriangular_ev_pbwMonomial bas).linearIndependent Function.injective_id

/-- **The spanning half of the Poincaré–Birkhoff–Witt theorem.** The ordered
monomials in the images of a basis of `L` span `U(L)` over `K`. -/
theorem span_range_pbwMonomial (bas : Module.Basis (Fin n) K L) :
    Submodule.span K (Set.range (pbwMonomial bas)) = ⊤ := by
  refine top_unique ?_
  rw [← span_sorted_prod_eq_top K bas bas.span_eq, Submodule.span_le]
  rintro u ⟨l, hl, rfl⟩
  rw [sorted_prod_eq_pbwMonomial bas hl]
  exact Submodule.subset_span ⟨monOfList l, rfl⟩

/-- **The Poincaré–Birkhoff–Witt basis theorem.** If the Lie algebra `L` has a
basis indexed by `Fin n`, the ordered monomials in the images of the basis
vectors form a `K`-basis of the universal enveloping algebra `U(L)`, indexed by
the exponent vectors `Mon n = Fin n →₀ ℕ`. -/
noncomputable def pbwBasis (bas : Module.Basis (Fin n) K L) :
    Module.Basis (Mon n) K (UniversalEnvelopingAlgebra K L) :=
  Module.Basis.mk (linearIndependent_pbwMonomial bas)
    (le_of_eq (span_range_pbwMonomial bas).symm)

/-- The `a`-th member of the Poincaré–Birkhoff–Witt basis is the ordered monomial
with exponent vector `a`. -/
@[simp] theorem pbwBasis_apply (bas : Module.Basis (Fin n) K L) (a : Mon n) :
    pbwBasis bas a
      = (List.ofFn fun i => (ι K (bas i) : UniversalEnvelopingAlgebra K L) ^ a i).prod := by
  rw [pbwBasis, Module.Basis.mk_apply, pbwMonomial_eq_ofFn]

end Basis

end Submission.Ado.PBW
