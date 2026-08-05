import Submission.Ado.PBW.Sorting

/-!
# Finite-dimensional quotients of `U(L)`

Let `K` be a field, `L` a Lie algebra over `K` and `b : Fin n → L` a family
which *spans* `L`; write `y i = pbwGen K b i = ι K (b i)` for the corresponding
generators of the universal enveloping algebra `U(L)`.

Fix `q : ℕ` and a two-sided ideal `I` of `U(L)` containing, for every index `i`,
an element of the shape

`y i ^ q - ∑ t : Fin q, mu i t • y i ^ (t : ℕ)`.

(In the characteristic `p` half of Ado–Iwasawa these are the central elements
produced by `Submission.Ado.central_pPolynomial`, with `q = p ^ m`; that they
are central is what makes the ideal they generate two-sided, but centrality
plays no role below — only membership in `I` does.)

The main results of this file say that `U(L) ⧸ I` is then a
**finite-dimensional** `K`-vector space:

* `Submission.Ado.finiteDimensional_quotient` — for `I` presented as a
  `K`-submodule of `U(L)` that is stable under left and right multiplication;
* `Submission.Ado.finiteDimensional_quotient_ideal` — for `I` presented as an
  `Ideal (U(L))` with `Ideal.IsTwoSided`, so that `U(L) ⧸ I` is again a
  `K`-algebra (the shape needed by
  `Submission.Ado.hasFaithfulFinRep_of_injective_toAlgebra`);
* `Submission.Ado.finiteDimensional_quotient_of_basis` and
  `Submission.Ado.finiteDimensional_quotient_ideal_of_basis` — the same
  statements for a `Module.Basis (Fin n) K L`, with the generators spelled out
  as `ι K (b i)`;
* `Submission.Ado.finiteDimensional_quotient_ideal_of_pPolynomial` and
  `Submission.Ado.finiteDimensional_quotient_ideal_of_pPolynomial_of_basis` —
  the version in which the elements of `J` are given in the `p`-polynomial
  shape `y i ^ p ^ m - ∑ j : Fin m, lam i j • y i ^ p ^ j` produced by
  `Submission.Ado.central_pPolynomial`; the exponents are reindexed by
  `Submission.Ado.exists_coeff_of_pPow`.

## The argument

Only the *spanning* half of the Poincaré–Birkhoff–Witt theorem is used, in the
form proved in `Submission/Ado/PBW/Sorting.lean`: `U(L)` is spanned over `K` by
the sorted monomials `(l.map (pbwGen K b)).prod`, `l : List (Fin n)` sorted.

Call a sorted monomial **restricted** when every index occurs in `l` fewer than
`q` times; `Submission.Ado.restrictedMonomials` is the set of these, and it is
finite (`Submission.Ado.restrictedMonomials_finite`) because a list over
`Fin n` all of whose multiplicities are `< q` has length at most `n * q`.

The heart of the file is `Submission.Ado.sortedSpanLE_le_restrictedSpan_sup`:
by strong induction on `k`, every sorted monomial of length at most `k` lies in
`restrictedSpan K b q ⊔ I`. Indeed, if some index `i` occurs at least `q` times
in the sorted list `l`, those occurrences are *adjacent*
(`Submission.Ado.exists_eq_append_replicate`), so
`l = l₁ ++ (List.replicate q i ++ l₂)` and the monomial factors as
`A * (y i ^ q * B)`. Replacing `y i ^ q` by `∑ t, mu i t • y i ^ t` changes the
element by a member of `I`, and each resulting word `A * (y i ^ t * B)` is a
product of strictly fewer than `l.length` generators, hence lies in
`gen K L ^ k'` with `k' < k`, hence — by
`Submission.Ado.genPow_le_sortedSpanLE` — in `sortedSpanLE K b k'`, to which
the induction hypothesis applies.

Consequently `restrictedSpan K b q ⊔ I = ⊤`
(`Submission.Ado.restrictedSpan_sup_eq_top`), so the images of the finitely
many restricted monomials span the quotient.

`Mathlib` makes `LieRing.ofAssociativeRing` a *local* instance only, so, as in
`Submission/Ado/PBW/Sorting.lean`, it is re-enabled here for the duration of
the file.
-/

universe u v

namespace Submission.Ado

open UniversalEnvelopingAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

/-! ### Combinatorics of sorted lists -/

section Lists

variable {α : Type u} [LinearOrder α]

/-- In a sorted list all of whose entries are `≥ x`, the entries equal to `x`
form an initial segment: `List.replicate (l.count x) x` is a prefix of `l`. -/
theorem replicate_count_prefix {l : List α} (hl : l.Pairwise (· ≤ ·)) {x : α}
    (hx : ∀ y ∈ l, x ≤ y) : List.replicate (l.count x) x <+: l := by
  induction l with
  | nil => simp
  | cons a t ih =>
      have ht : t.Pairwise (· ≤ ·) := hl.of_cons
      have hat : ∀ y ∈ t, a ≤ y := (List.pairwise_cons.mp hl).1
      by_cases hax : a = x
      · subst hax
        have := ih ht hat
        rw [List.count_cons]
        simp only [beq_self_eq_true, if_true, List.replicate_succ]
        exact List.cons_prefix_cons.mpr ⟨rfl, this⟩
      · have h0 : (a :: t).count x = 0 := by
          refine List.count_eq_zero.mpr ?_
          intro hmem
          rcases List.mem_cons.mp hmem with h | h
          · exact hax h.symm
          · exact hax (le_antisymm (hat x h) (hx a (List.mem_cons_self ..)))
        rw [h0]
        simp

/-- **Adjacency of repeated entries.** If a sorted list `l` contains `x` at
least `q` times, then `q` of those occurrences are adjacent: `l` can be written
as `l₁ ++ (List.replicate q x ++ l₂)`. -/
theorem exists_eq_append_replicate {l : List α} (hl : l.Pairwise (· ≤ ·)) {x : α} {q : ℕ}
    (hq : q ≤ l.count x) : ∃ l₁ l₂ : List α, l = l₁ ++ (List.replicate q x ++ l₂) := by
  induction l with
  | nil =>
      simp only [List.count_nil, Nat.le_zero] at hq
      exact ⟨[], [], by simp [hq]⟩
  | cons a t ih =>
      have ht : t.Pairwise (· ≤ ·) := hl.of_cons
      have hat : ∀ y ∈ t, a ≤ y := (List.pairwise_cons.mp hl).1
      by_cases hax : a = x
      · subst hax
        have hpre : List.replicate ((a :: t).count a) a <+: a :: t :=
          replicate_count_prefix hl (fun y hy => by
            rcases List.mem_cons.mp hy with rfl | h
            · exact le_rfl
            · exact hat y h)
        have hsplit : List.replicate q a <+: List.replicate ((a :: t).count a) a :=
          ⟨List.replicate ((a :: t).count a - q) a, by
            rw [← List.replicate_add, Nat.add_sub_cancel' hq]⟩
        obtain ⟨l₂, hl₂⟩ := hsplit.trans hpre
        exact ⟨[], l₂, by simpa using hl₂.symm⟩
      · have hc : (a :: t).count x = t.count x := by
          rw [List.count_cons]
          simp [hax]
        rw [hc] at hq
        obtain ⟨l₁, l₂, hl₁⟩ := ih ht hq
        exact ⟨a :: l₁, l₂, by rw [hl₁]; simp⟩

end Lists

/-- A list over `Fin n` in which every index occurs fewer than `q` times has
length at most `n * q`; this is what makes the set of restricted monomials
finite. -/
theorem length_le_of_forall_count_lt {n q : ℕ} {l : List (Fin n)} (h : ∀ i, l.count i < q) :
    l.length ≤ n * q := by
  have h1 : ∑ i : Fin n, l.count i = l.length := by
    have := Multiset.sum_count_eq_card (s := (Finset.univ : Finset (Fin n)))
      (m := (l : Multiset (Fin n))) (by simp)
    simpa using this
  calc l.length = ∑ i : Fin n, l.count i := h1.symm
    _ ≤ ∑ _i : Fin n, q := Finset.sum_le_sum fun i _ => (h i).le
    _ = n * q := by simp

section Enveloping

variable (K : Type u) {L : Type u} [Field K] [LieRing L] [LieAlgebra K L] {n : ℕ}
  (b : Fin n → L) (q : ℕ)

/-! ### Restricted monomials -/

/-- The set of **restricted monomials**: the sorted products
`(l.map (pbwGen K b)).prod` for which every index occurs in `l` fewer than `q`
times. -/
def restrictedMonomials : Set (UniversalEnvelopingAlgebra K L) :=
  {u | ∃ l : List (Fin n), l.Pairwise (· ≤ ·) ∧ (∀ i, l.count i < q) ∧
    (l.map (pbwGen K b)).prod = u}

/-- The `K`-submodule of `U(L)` spanned by the restricted monomials. -/
noncomputable def restrictedSpan : Submodule K (UniversalEnvelopingAlgebra K L) :=
  Submodule.span K (restrictedMonomials K b q)

/-- There are only finitely many restricted monomials: the underlying lists
have length at most `n * q`. -/
theorem restrictedMonomials_finite : (restrictedMonomials K b q).Finite := by
  have hfin : {l : List (Fin n) | l.length ≤ n * q}.Finite := List.finite_length_le _ _
  refine Set.Finite.subset (hfin.image fun l => (l.map (pbwGen K b)).prod) ?_
  rintro u ⟨l, -, hr, rfl⟩
  exact ⟨l, length_le_of_forall_count_lt hr, rfl⟩

/-- A restricted monomial lies in `restrictedSpan K b q`. -/
theorem prod_mem_restrictedSpan {l : List (Fin n)} (hl : l.Pairwise (· ≤ ·))
    (hr : ∀ i, l.count i < q) : (l.map (pbwGen K b)).prod ∈ restrictedSpan K b q :=
  Submodule.subset_span ⟨l, hl, hr, rfl⟩

/-! ### Words in the generators and the degree filtration -/

/-- A product of `l.length` generators lies in the `l.length`-th power of
`gen K L`. -/
theorem prod_map_pbwGen_mem_genPow (l : List (Fin n)) :
    (l.map (pbwGen K b)).prod ∈ gen K L ^ l.length := by
  induction l with
  | nil => simpa using Submodule.mem_one.mpr ⟨1, by simp⟩
  | cons a t ih =>
      rw [List.map_cons, List.prod_cons, List.length_cons, pow_succ']
      exact Submodule.mul_mem_mul (ι_mem_gen K L (b a)) ih

/-- The `t`-th power of a generator lies in `gen K L ^ t`. -/
theorem pbwGen_pow_mem_genPow (i : Fin n) (t : ℕ) : pbwGen K b i ^ t ∈ gen K L ^ t := by
  have := prod_map_pbwGen_mem_genPow K b (List.replicate t i)
  simpa [List.map_replicate, List.prod_replicate] using this

/-- Since `b` spans `L`, the submodule `gen K L` is contained in the span of
the generators `pbwGen K b`. -/
theorem gen_le_span_range_pbwGen (hb : Submodule.span K (Set.range b) = ⊤) :
    gen K L ≤ Submodule.span K (Set.range (pbwGen K b)) := by
  rw [gen, Submodule.span_le]
  rintro _ ⟨x, rfl⟩
  exact ι_mem_span_range_pbwGen K b hb x

/-- **A length-bounded form of the spanning half of PBW.** A product of `j`
generators is a `K`-combination of sorted monomials of length at most `j`. -/
theorem genPow_le_sortedSpanLE (hb : Submodule.span K (Set.range b) = ⊤) (j : ℕ) :
    gen K L ^ j ≤ sortedSpanLE K b j := by
  induction j with
  | zero =>
      rw [pow_zero]
      refine Submodule.one_le.mpr ?_
      simpa using prod_mem_sortedSpanLE K b (l := []) (by simp) (by simp)
  | succ j ih =>
      rw [pow_succ']
      refine Submodule.mul_le.mpr fun v hv u hu => ?_
      refine mul_mem_of_left_mem_span K (gen_le_span_range_pbwGen K b hb hv) ?_
      rintro _ ⟨i, rfl⟩
      refine mul_mem_of_right_mem_span K (ih hu) ?_
      rintro _ ⟨l, hl, hlen, rfl⟩
      exact pbwGen_mul_prod_mem_sortedSpanLE K b hb j i l hl hlen

/-! ### Reduction to restricted monomials -/

/-- **The key reduction.** Assume `I` is a `K`-submodule of `U(L)` stable under
left and right multiplication which contains, for every index `i`, the element
`pbwGen K b i ^ q - ∑ t : Fin q, mu i t • pbwGen K b i ^ t`. Then every sorted
monomial of length at most `k` lies in `restrictedSpan K b q ⊔ I`.

The proof is a strong induction on `k`. If the sorted list `l` is already
restricted there is nothing to do. Otherwise some index `i` occurs at least `q`
times, and since `l` is sorted these occurrences are adjacent, so the monomial
reads `A * (y i ^ q * B)`. Modulo `I` one may replace `y i ^ q` by
`∑ t, mu i t • y i ^ t`, and each summand `A * (y i ^ t * B)` is a product of
`l₁.length + t + l₂.length < l.length` generators, hence lies in a
`sortedSpanLE` of strictly smaller index. -/
theorem sortedSpanLE_le_restrictedSpan_sup (hb : Submodule.span K (Set.range b) = ⊤)
    {I : Submodule K (UniversalEnvelopingAlgebra K L)}
    (hIl : ∀ u v : UniversalEnvelopingAlgebra K L, u ∈ I → v * u ∈ I)
    (hIr : ∀ u v : UniversalEnvelopingAlgebra K L, u ∈ I → u * v ∈ I)
    {mu : Fin n → Fin q → K}
    (hI : ∀ i, pbwGen K b i ^ q - ∑ t : Fin q, mu i t • pbwGen K b i ^ (t : ℕ) ∈ I)
    (k : ℕ) : sortedSpanLE K b k ≤ restrictedSpan K b q ⊔ I := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rw [sortedSpanLE, Submodule.span_le]
    rintro u ⟨l, hl, hlen, rfl⟩
    by_cases hr : ∀ i, l.count i < q
    · exact Submodule.mem_sup_left (prod_mem_restrictedSpan K b q hl hr)
    · push Not at hr
      obtain ⟨i, hi⟩ := hr
      obtain ⟨l₁, l₂, rfl⟩ := exists_eq_append_replicate hl hi
      have key : ∀ t : ℕ, ((l₁ ++ (List.replicate t i ++ l₂)).map (pbwGen K b)).prod
          = (l₁.map (pbwGen K b)).prod
            * (pbwGen K b i ^ t * (l₂.map (pbwGen K b)).prod) := by
        intro t
        simp [List.map_append, List.prod_append, List.map_replicate, List.prod_replicate]
      have hlen' : l₁.length + (q + l₂.length) ≤ k := by simpa using hlen
      have hsmall : ∀ t : Fin q, (l₁.map (pbwGen K b)).prod
          * (pbwGen K b i ^ (t : ℕ) * (l₂.map (pbwGen K b)).prod)
            ∈ restrictedSpan K b q ⊔ I := by
        intro t
        have hts : (t : ℕ) < q := t.isLt
        have hk' : l₁.length + ((t : ℕ) + l₂.length) < k := by omega
        have hmem : (l₁.map (pbwGen K b)).prod
            * (pbwGen K b i ^ (t : ℕ) * (l₂.map (pbwGen K b)).prod)
              ∈ gen K L ^ (l₁.length + ((t : ℕ) + l₂.length)) := by
          rw [pow_add]
          refine Submodule.mul_mem_mul (prod_map_pbwGen_mem_genPow K b l₁) ?_
          rw [pow_add]
          exact Submodule.mul_mem_mul (pbwGen_pow_mem_genPow K b i t)
            (prod_map_pbwGen_mem_genPow K b l₂)
        exact ih _ hk' (genPow_le_sortedSpanLE K b hb _ hmem)
      have hIcmem : (l₁.map (pbwGen K b)).prod
          * ((pbwGen K b i ^ q - ∑ t : Fin q, mu i t • pbwGen K b i ^ (t : ℕ))
            * (l₂.map (pbwGen K b)).prod) ∈ I := hIl _ _ (hIr _ _ (hI i))
      have hexp : (l₁.map (pbwGen K b)).prod
          * (pbwGen K b i ^ q * (l₂.map (pbwGen K b)).prod)
          = (l₁.map (pbwGen K b)).prod
              * ((pbwGen K b i ^ q - ∑ t : Fin q, mu i t • pbwGen K b i ^ (t : ℕ))
                * (l₂.map (pbwGen K b)).prod)
            + ∑ t : Fin q, mu i t • ((l₁.map (pbwGen K b)).prod
                * (pbwGen K b i ^ (t : ℕ) * (l₂.map (pbwGen K b)).prod)) := by
        simp only [sub_mul, mul_sub, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc,
          mul_smul_comm]
        abel
      rw [key q, hexp]
      exact add_mem (Submodule.mem_sup_right hIcmem)
        (sum_mem fun t _ => Submodule.smul_mem _ _ (hsmall t))

/-! ### The finite-dimensional quotient -/

/-- **The restricted monomials span `U(L)` modulo `I`.** Under the hypotheses of
`Submission.Ado.sortedSpanLE_le_restrictedSpan_sup` the span of the restricted
monomials together with `I` is all of `U(L)`. -/
theorem restrictedSpan_sup_eq_top (hb : Submodule.span K (Set.range b) = ⊤)
    {I : Submodule K (UniversalEnvelopingAlgebra K L)}
    (hIl : ∀ u v : UniversalEnvelopingAlgebra K L, u ∈ I → v * u ∈ I)
    (hIr : ∀ u v : UniversalEnvelopingAlgebra K L, u ∈ I → u * v ∈ I)
    {mu : Fin n → Fin q → K}
    (hI : ∀ i, pbwGen K b i ^ q - ∑ t : Fin q, mu i t • pbwGen K b i ^ (t : ℕ) ∈ I) :
    restrictedSpan K b q ⊔ I = ⊤ := by
  refine top_unique ?_
  rw [← sortedSpan_eq_top K b hb, sortedSpan, Submodule.span_le]
  rintro u ⟨l, hl, rfl⟩
  exact sortedSpanLE_le_restrictedSpan_sup K b q hb hIl hIr hI l.length
    (prod_mem_sortedSpanLE K b hl le_rfl)

/-- The images of the restricted monomials span the quotient `U(L) ⧸ I`. -/
theorem span_image_mkQ_restrictedMonomials_eq_top (hb : Submodule.span K (Set.range b) = ⊤)
    {I : Submodule K (UniversalEnvelopingAlgebra K L)}
    (hIl : ∀ u v : UniversalEnvelopingAlgebra K L, u ∈ I → v * u ∈ I)
    (hIr : ∀ u v : UniversalEnvelopingAlgebra K L, u ∈ I → u * v ∈ I)
    {mu : Fin n → Fin q → K}
    (hI : ∀ i, pbwGen K b i ^ q - ∑ t : Fin q, mu i t • pbwGen K b i ^ (t : ℕ) ∈ I) :
    Submodule.span K (I.mkQ '' restrictedMonomials K b q) = ⊤ := by
  have h := congrArg (fun N => Submodule.map I.mkQ N)
    (restrictedSpan_sup_eq_top K b q hb hIl hIr hI)
  simpa [restrictedSpan, Submodule.map_sup, Submodule.map_span, Submodule.mkQ_map_self,
    Submodule.range_mkQ] using h

/-- **The quotient of `U(L)` by a `q`-truncating two-sided ideal is
finite-dimensional.** Here the ideal is presented as a `K`-submodule `I` of
`U(L)` stable under left and right multiplication, and `U(L) ⧸ I` is the
quotient `K`-module. -/
theorem finiteDimensional_quotient (hb : Submodule.span K (Set.range b) = ⊤)
    {I : Submodule K (UniversalEnvelopingAlgebra K L)}
    (hIl : ∀ u v : UniversalEnvelopingAlgebra K L, u ∈ I → v * u ∈ I)
    (hIr : ∀ u v : UniversalEnvelopingAlgebra K L, u ∈ I → u * v ∈ I)
    {mu : Fin n → Fin q → K}
    (hI : ∀ i, pbwGen K b i ^ q - ∑ t : Fin q, mu i t • pbwGen K b i ^ (t : ℕ) ∈ I) :
    FiniteDimensional K (UniversalEnvelopingAlgebra K L ⧸ I) :=
  Module.finite_def.mpr <| Submodule.fg_def.mpr
    ⟨I.mkQ '' restrictedMonomials K b q, (restrictedMonomials_finite K b q).image _,
      span_image_mkQ_restrictedMonomials_eq_top K b q hb hIl hIr hI⟩

/-- **The same statement for an honest two-sided ideal.** If `J` is a two-sided
ideal of `U(L)` containing, for each index `i`, an element
`pbwGen K b i ^ q - ∑ t : Fin q, mu i t • pbwGen K b i ^ t`, then the quotient
`K`-algebra `U(L) ⧸ J` is finite-dimensional. -/
theorem finiteDimensional_quotient_ideal (hb : Submodule.span K (Set.range b) = ⊤)
    (J : Ideal (UniversalEnvelopingAlgebra K L)) [J.IsTwoSided] {mu : Fin n → Fin q → K}
    (hJ : ∀ i, pbwGen K b i ^ q - ∑ t : Fin q, mu i t • pbwGen K b i ^ (t : ℕ) ∈ J) :
    FiniteDimensional K (UniversalEnvelopingAlgebra K L ⧸ J) := by
  have htop := restrictedSpan_sup_eq_top K b q hb (I := J.restrictScalars K)
    (fun _ v hu => J.mul_mem_left v hu) (fun _ v hu => J.mul_mem_right v hu) hJ
  set f : UniversalEnvelopingAlgebra K L →ₗ[K] UniversalEnvelopingAlgebra K L ⧸ J :=
    (Ideal.Quotient.mkₐ K J).toLinearMap
  have hmap : Submodule.map f (restrictedSpan K b q ⊔ J.restrictScalars K) = ⊤ := by
    rw [htop, Submodule.map_top, LinearMap.range_eq_top.mpr
      (Ideal.Quotient.mk_surjective (I := J))]
  have hJbot : Submodule.map f (J.restrictScalars K) = ⊥ := by
    refine le_bot_iff.mp ?_
    rintro _ ⟨x, hx, rfl⟩
    exact (Submodule.mem_bot K).mpr (Ideal.Quotient.eq_zero_iff_mem.mpr hx)
  rw [Submodule.map_sup, hJbot, sup_bot_eq, restrictedSpan, Submodule.map_span] at hmap
  exact Module.finite_def.mpr (Submodule.fg_def.mpr
    ⟨f '' restrictedMonomials K b q, (restrictedMonomials_finite K b q).image _, hmap⟩)

end Enveloping

/-! ### The statements for a basis -/

section Basis

variable (K : Type u) {L : Type u} [Field K] [LieRing L] [LieAlgebra K L] {n : ℕ}
  (b : Module.Basis (Fin n) K L) (q : ℕ)

/-- `Submission.Ado.finiteDimensional_quotient` for a basis `b` of `L`, with the
generators of `U(L)` spelled out as `ι K (b i)`. -/
theorem finiteDimensional_quotient_of_basis
    {I : Submodule K (UniversalEnvelopingAlgebra K L)}
    (hIl : ∀ u v : UniversalEnvelopingAlgebra K L, u ∈ I → v * u ∈ I)
    (hIr : ∀ u v : UniversalEnvelopingAlgebra K L, u ∈ I → u * v ∈ I)
    {mu : Fin n → Fin q → K}
    (hI : ∀ i, (ι K (b i) : UniversalEnvelopingAlgebra K L) ^ q
      - ∑ t : Fin q, mu i t • (ι K (b i) : UniversalEnvelopingAlgebra K L) ^ (t : ℕ) ∈ I) :
    FiniteDimensional K (UniversalEnvelopingAlgebra K L ⧸ I) :=
  finiteDimensional_quotient K (⇑b) q b.span_eq hIl hIr hI

/-- `Submission.Ado.finiteDimensional_quotient_ideal` for a basis `b` of `L`,
with the generators of `U(L)` spelled out as `ι K (b i)`. This is the form used
in the characteristic `p` half of Ado–Iwasawa: `U(L) ⧸ J` is then a
finite-dimensional associative `K`-algebra. -/
theorem finiteDimensional_quotient_ideal_of_basis
    (J : Ideal (UniversalEnvelopingAlgebra K L)) [J.IsTwoSided] {mu : Fin n → Fin q → K}
    (hJ : ∀ i, (ι K (b i) : UniversalEnvelopingAlgebra K L) ^ q
      - ∑ t : Fin q, mu i t • (ι K (b i) : UniversalEnvelopingAlgebra K L) ^ (t : ℕ) ∈ J) :
    FiniteDimensional K (UniversalEnvelopingAlgebra K L ⧸ J) :=
  finiteDimensional_quotient_ideal K (⇑b) q b.span_eq J hJ

end Basis

/-! ### The `p`-polynomial shape -/

section PPolynomial

/-- **Reindexing a `p`-polynomial as a truncated polynomial.** A `K`-combination
of the values `f (p ^ j)`, `j < m`, is a `K`-combination of the values `f t` for
`t < p ^ m`: the exponents `p ^ j` are distinct and `< p ^ m`.

This converts the `p`-polynomial relations produced by
`Submission.Ado.central_pPolynomial` into the shape required by
`Submission.Ado.finiteDimensional_quotient_ideal`. -/
theorem exists_coeff_of_pPow (K : Type u) [Field K] {M : Type v} [AddCommMonoid M] [Module K M]
    {p : ℕ} (hp : 2 ≤ p) {m : ℕ} (lam : Fin m → K) (f : ℕ → M) :
    ∃ mu : Fin (p ^ m) → K,
      ∑ t : Fin (p ^ m), mu t • f (t : ℕ) = ∑ j : Fin m, lam j • f (p ^ (j : ℕ)) := by
  have hlt : ∀ j : Fin m, p ^ (j : ℕ) < p ^ m := fun j => (Nat.pow_lt_pow_iff_right hp).mpr j.isLt
  set e : Fin m → Fin (p ^ m) := fun j => ⟨p ^ (j : ℕ), hlt j⟩ with he
  have hinj : Function.Injective e := by
    intro j₁ j₂ h
    have : p ^ (j₁ : ℕ) = p ^ (j₂ : ℕ) := congrArg Fin.val h
    exact Fin.ext (Nat.pow_right_injective hp this)
  refine ⟨Function.extend e lam 0, ?_⟩
  have hzero : ∀ t ∈ (Finset.univ : Finset (Fin (p ^ m))),
      t ∉ Finset.univ.map ⟨e, hinj⟩ →
        Function.extend e lam (0 : Fin (p ^ m) → K) t • f (t : ℕ) = 0 := by
    intro t _ ht
    have hne : ¬∃ j, e j = t := by
      intro hex
      exact ht (Finset.mem_map.mpr ⟨hex.choose, Finset.mem_univ _, hex.choose_spec⟩)
    rw [Function.extend_apply' _ _ _ hne]
    simp
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.map ⟨e, hinj⟩)) hzero,
    Finset.sum_map]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Function.Embedding.coeFn_mk]
  rw [hinj.extend_apply lam 0 j]

variable (K : Type u) {L : Type u} [Field K] [LieRing L] [LieAlgebra K L] {n : ℕ}
  (b : Fin n → L)

/-- **Finite-dimensionality of the quotient by a `p`-polynomial ideal.** If `J`
is a two-sided ideal of `U(L)` containing, for every index `i`, an element

`ι K (b i) ^ p ^ m - ∑ j : Fin m, lam i j • ι K (b i) ^ p ^ j`

(such as the central elements manufactured by
`Submission.Ado.central_pPolynomial`), then `U(L) ⧸ J` is a finite-dimensional
`K`-algebra. -/
theorem finiteDimensional_quotient_ideal_of_pPolynomial
    (hb : Submodule.span K (Set.range b) = ⊤) {p : ℕ} (hp : 2 ≤ p) {m : ℕ}
    (J : Ideal (UniversalEnvelopingAlgebra K L)) [J.IsTwoSided] (lam : Fin n → Fin m → K)
    (hJ : ∀ i, pbwGen K b i ^ p ^ m
      - ∑ j : Fin m, lam i j • pbwGen K b i ^ p ^ (j : ℕ) ∈ J) :
    FiniteDimensional K (UniversalEnvelopingAlgebra K L ⧸ J) := by
  choose mu hmu using fun i : Fin n =>
    exists_coeff_of_pPow K hp (lam i) fun t => pbwGen K b i ^ t
  exact finiteDimensional_quotient_ideal K b (p ^ m) hb J (mu := mu)
    fun i => by rw [hmu i]; exact hJ i

/-- `Submission.Ado.finiteDimensional_quotient_ideal_of_pPolynomial` for a basis
of `L`, with the generators of `U(L)` spelled out as `ι K (bs i)`. -/
theorem finiteDimensional_quotient_ideal_of_pPolynomial_of_basis
    (bs : Module.Basis (Fin n) K L) {p : ℕ} (hp : 2 ≤ p) {m : ℕ}
    (J : Ideal (UniversalEnvelopingAlgebra K L)) [J.IsTwoSided] (lam : Fin n → Fin m → K)
    (hJ : ∀ i, (ι K (bs i) : UniversalEnvelopingAlgebra K L) ^ p ^ m
      - ∑ j : Fin m, lam i j • (ι K (bs i) : UniversalEnvelopingAlgebra K L) ^ p ^ (j : ℕ)
        ∈ J) :
    FiniteDimensional K (UniversalEnvelopingAlgebra K L ⧸ J) :=
  finiteDimensional_quotient_ideal_of_pPolynomial K (⇑bs) bs.span_eq hp J lam hJ

end PPolynomial

end Submission.Ado
