import Submission.Ado.Filtration

/-!
# The spanning half of the Poincaré–Birkhoff–Witt theorem

Let `K` be a field, `L` a Lie algebra over `K` and `b : Fin n → L` a family
which *spans* `L` (no independence is assumed). Write
`y i = ι K (b i) : U(L)` for the images of the members of `b` under the
canonical map into the universal enveloping algebra.

The theorem proved here is the spanning half of the Poincaré–Birkhoff–Witt
theorem: the *sorted* monomials
`y i₁ * y i₂ * ⋯ * y i_m` with `i₁ ≤ i₂ ≤ ⋯ ≤ i_m` already span `U(L)` as a
`K`-module, see `Submission.Ado.span_sorted_prod_eq_top`.

## Outline

`Submission.Ado.adjoin_range_ι_eq_top` (in `Submission/Ado/Filtration.lean`)
says that `ι '' L` generates `U(L)` as a `K`-algebra; concretely,
`Submission.Ado.exists_mem_gen_pow` writes every element of `U(L)` as a sum of
products of elements of `ι '' L`. It therefore suffices to prove that the
submodule `sortedSpan` spanned by the sorted monomials contains `1` and is
stable under left multiplication by each `y i`.

Stability is the "straightening" step. It is proved by a double induction, on
the length `k` of the sorted word that is being multiplied and, for fixed `k`,
on the index `i`. If `y i` meets a word `y j * ⋯` with `j < i`, the commutation
rule

`y i * y j = y j * y i + ι ⁅b i, b j⁆`

replaces it by a word whose leading generator has a smaller index, plus — since
`ι ⁅b i, b j⁆` is a `K`-linear combination of the `y k`, `b` being a spanning
family — a word that is one letter shorter. Keeping track of lengths is what
the auxiliary submodules `Submission.Ado.sortedSpanLE` are for.

`Mathlib` makes `LieRing.ofAssociativeRing` a *local* instance only, so, as in
`Submission/Ado/Filtration.lean`, it is re-enabled here for the duration of the
file.

## Note on `List.Sorted`

The `Mathlib` revision pinned by this workspace no longer has `List.Sorted`;
its definition was `List.Sorted r = List.Pairwise r`, and that is the spelling
used below. The variant phrased with `List.SortedLE` is recorded as
`Submission.Ado.span_sortedLE_prod_eq_top`.
-/

universe u

namespace Submission.Ado

open UniversalEnvelopingAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

variable (K : Type u) {L : Type u} [Field K] [LieRing L] [LieAlgebra K L] {n : ℕ}
  (b : Fin n → L)

/-! ### Generators and the submodules spanned by sorted monomials -/

/-- The image in `U(L)` of the `i`-th member of the family `b : Fin n → L`. -/
noncomputable def pbwGen (i : Fin n) : UniversalEnvelopingAlgebra K L := ι K (b i)

/-- The `K`-submodule of `U(L)` spanned by the sorted monomials in the
generators `pbwGen K b` of length at most `k`. -/
noncomputable def sortedSpanLE (k : ℕ) : Submodule K (UniversalEnvelopingAlgebra K L) :=
  Submodule.span K {u | ∃ l : List (Fin n), l.Pairwise (· ≤ ·) ∧ l.length ≤ k ∧
    (l.map (pbwGen K b)).prod = u}

/-- The `K`-submodule of `U(L)` spanned by all sorted monomials in the
generators `pbwGen K b`. -/
noncomputable def sortedSpan : Submodule K (UniversalEnvelopingAlgebra K L) :=
  Submodule.span K {u | ∃ l : List (Fin n), l.Pairwise (· ≤ ·) ∧ (l.map (pbwGen K b)).prod = u}

/-- A sorted monomial of length at most `k` lies in `sortedSpanLE K b k`. -/
theorem prod_mem_sortedSpanLE {l : List (Fin n)} (hl : l.Pairwise (· ≤ ·)) {k : ℕ}
    (hk : l.length ≤ k) : (l.map (pbwGen K b)).prod ∈ sortedSpanLE K b k :=
  Submodule.subset_span ⟨l, hl, hk, rfl⟩

/-- A sorted monomial lies in `sortedSpan K b`. -/
theorem prod_mem_sortedSpan {l : List (Fin n)} (hl : l.Pairwise (· ≤ ·)) :
    (l.map (pbwGen K b)).prod ∈ sortedSpan K b :=
  Submodule.subset_span ⟨l, hl, rfl⟩

/-- The submodules `sortedSpanLE K b k` increase with `k`. -/
theorem sortedSpanLE_mono {k k' : ℕ} (h : k ≤ k') :
    sortedSpanLE K b k ≤ sortedSpanLE K b k' := by
  refine Submodule.span_mono ?_
  rintro u ⟨l, hl, hlen, rfl⟩
  exact ⟨l, hl, hlen.trans h, rfl⟩

/-- Bounded sorted monomials span a submodule of the span of all of them. -/
theorem sortedSpanLE_le_sortedSpan (k : ℕ) : sortedSpanLE K b k ≤ sortedSpan K b := by
  refine Submodule.span_mono ?_
  rintro u ⟨l, hl, -, rfl⟩
  exact ⟨l, hl, rfl⟩

/-- The empty monomial shows `1 ∈ sortedSpan K b`. -/
theorem one_mem_sortedSpan : (1 : UniversalEnvelopingAlgebra K L) ∈ sortedSpan K b := by
  simpa using prod_mem_sortedSpan K b (l := []) (by simp)

/-! ### Two elementary facts about spans and multiplication -/

/-- If `v` lies in the span of `s` and every element of `s` multiplies `w` into
the submodule `M` from the left, then `v * w ∈ M`. -/
theorem mul_mem_of_left_mem_span {s : Set (UniversalEnvelopingAlgebra K L)}
    {M : Submodule K (UniversalEnvelopingAlgebra K L)}
    {v w : UniversalEnvelopingAlgebra K L} (hv : v ∈ Submodule.span K s)
    (h : ∀ x ∈ s, x * w ∈ M) : v * w ∈ M := by
  induction hv using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero => simp
  | add x y _ _ hx hy => simpa [add_mul] using M.add_mem hx hy
  | smul a x _ hx => simpa [smul_mul_assoc] using M.smul_mem a hx

/-- If `w` lies in the span of `s` and `v` multiplies every element of `s` into
the submodule `M` from the right, then `v * w ∈ M`. -/
theorem mul_mem_of_right_mem_span {s : Set (UniversalEnvelopingAlgebra K L)}
    {M : Submodule K (UniversalEnvelopingAlgebra K L)}
    {v w : UniversalEnvelopingAlgebra K L} (hw : w ∈ Submodule.span K s)
    (h : ∀ x ∈ s, v * x ∈ M) : v * w ∈ M := by
  induction hw using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero => simp
  | add x y _ _ hx hy => simpa [mul_add] using M.add_mem hx hy
  | smul a x _ hx => simpa [mul_smul_comm] using M.smul_mem a hx

/-! ### The straightening lemma -/

/-- Since `b` spans `L`, the image `ι K x` of any `x : L` is a `K`-linear
combination of the generators `pbwGen K b`. -/
theorem ι_mem_span_range_pbwGen (hb : Submodule.span K (Set.range b) = ⊤) (x : L) :
    (ι K x : UniversalEnvelopingAlgebra K L) ∈ Submodule.span K (Set.range (pbwGen K b)) := by
  have h : Set.range (pbwGen K b)
      = (ι K : L →ₗ⁅K⁆ UniversalEnvelopingAlgebra K L).toLinearMap '' Set.range b := by
    rw [← Set.range_comp]
    rfl
  rw [h, ← Submodule.map_span, hb, Submodule.map_top]
  exact LinearMap.mem_range.mpr ⟨x, rfl⟩

/-- The commutation rule for the generators:
`y i * y j = y j * y i + ι ⁅b i, b j⁆`. -/
theorem pbwGen_mul_comm (i j : Fin n) :
    pbwGen K b i * pbwGen K b j
      = pbwGen K b j * pbwGen K b i + ι K ⁅b i, b j⁆ := by
  have h : (ι K ⁅b i, b j⁆ : UniversalEnvelopingAlgebra K L)
      = ι K (b i) * ι K (b j) - ι K (b j) * ι K (b i) := by
    have := (ι K : L →ₗ⁅K⁆ UniversalEnvelopingAlgebra K L).map_lie (b i) (b j)
    rwa [LieRing.of_associative_ring_bracket] at this
  simp only [pbwGen, h]
  abel

/-- **Straightening.** Multiplying a sorted monomial of length at most `k` by a
generator lands in the span of the sorted monomials of length at most `k + 1`.

The proof is a double induction: on `k`, and, for fixed `k`, on the index of
the generator. -/
theorem pbwGen_mul_prod_mem_sortedSpanLE (hb : Submodule.span K (Set.range b) = ⊤) (k : ℕ) :
    ∀ (i : Fin n) (l : List (Fin n)), l.Pairwise (· ≤ ·) → l.length ≤ k →
      pbwGen K b i * (l.map (pbwGen K b)).prod ∈ sortedSpanLE K b (k + 1) := by
  induction k with
  | zero =>
      intro i l hl hlen
      match l, hl, hlen with
      | [], _, _ =>
          simpa using prod_mem_sortedSpanLE K b (l := [i]) (by simp) (by simp)
  | succ k ih =>
      -- Inner induction: the claim for all generators of index `< m`.
      have inner : ∀ (m : ℕ) (i : Fin n), (i : ℕ) < m → ∀ l : List (Fin n),
          l.Pairwise (· ≤ ·) → l.length ≤ k + 1 →
          pbwGen K b i * (l.map (pbwGen K b)).prod ∈ sortedSpanLE K b (k + 1 + 1) := by
        intro m
        induction m with
        | zero => exact fun i hi => absurd hi (Nat.not_lt_zero _)
        | succ m ihm =>
            intro i hi l hl hlen
            match l with
            | [] => simpa using prod_mem_sortedSpanLE K b (l := [i]) (by simp) (by simp)
            | j :: t =>
                have hts : t.Pairwise (· ≤ ·) := hl.of_cons
                have htlen : t.length ≤ k := by
                  simpa using hlen
                rcases le_or_gt i j with hij | hji
                · -- already sorted: just prepend `i`
                  have hsorted : (i :: j :: t).Pairwise (· ≤ ·) := by
                    refine List.pairwise_cons.mpr ⟨?_, hl⟩
                    intro x hx
                    rcases List.mem_cons.mp hx with rfl | hx
                    · exact hij
                    · exact hij.trans ((List.pairwise_cons.mp hl).1 x hx)
                  have hlen' : (i :: j :: t).length ≤ k + 1 + 1 := by
                    simpa using htlen
                  simpa using prod_mem_sortedSpanLE K b hsorted hlen'
                · -- out of order: commute `y i` past `y j`
                  have hjm : (j : ℕ) < m :=
                    lt_of_lt_of_le hji (Nat.lt_succ_iff.mp hi)
                  have hA : pbwGen K b i * (t.map (pbwGen K b)).prod
                      ∈ sortedSpanLE K b (k + 1) := ih i t hts htlen
                  have hB : ∀ v ∈ sortedSpanLE K b (k + 1),
                      pbwGen K b j * v ∈ sortedSpanLE K b (k + 1 + 1) := by
                    intro v hv
                    refine mul_mem_of_right_mem_span K hv ?_
                    rintro x ⟨l', hl', hlen', rfl⟩
                    exact ihm j hjm l' hl' hlen'
                  have hbr : (ι K ⁅b i, b j⁆ : UniversalEnvelopingAlgebra K L)
                      * (t.map (pbwGen K b)).prod ∈ sortedSpanLE K b (k + 1) := by
                    refine mul_mem_of_left_mem_span K
                      (ι_mem_span_range_pbwGen K b hb _) ?_
                    rintro x ⟨i', rfl⟩
                    exact ih i' t hts htlen
                  have hsplit : pbwGen K b i * ((j :: t).map (pbwGen K b)).prod
                      = pbwGen K b j * (pbwGen K b i * (t.map (pbwGen K b)).prod)
                        + ι K ⁅b i, b j⁆ * (t.map (pbwGen K b)).prod := by
                    simp only [List.map_cons, List.prod_cons, ← mul_assoc,
                      pbwGen_mul_comm K b i j, add_mul]
                  rw [hsplit]
                  exact add_mem (hB _ hA) (sortedSpanLE_mono K b (Nat.le_succ _) hbr)
      intro i l hl hlen
      exact inner (i + 1) i (Nat.lt_succ_self _) l hl hlen

/-! ### The spanning theorem -/

/-- `sortedSpan K b` is stable under left multiplication by the generators. -/
theorem pbwGen_mul_mem_sortedSpan (hb : Submodule.span K (Set.range b) = ⊤) (i : Fin n)
    {u : UniversalEnvelopingAlgebra K L} (hu : u ∈ sortedSpan K b) :
    pbwGen K b i * u ∈ sortedSpan K b := by
  refine mul_mem_of_right_mem_span K hu ?_
  rintro x ⟨l, hl, rfl⟩
  exact sortedSpanLE_le_sortedSpan K b _
    (pbwGen_mul_prod_mem_sortedSpanLE K b hb l.length i l hl le_rfl)

/-- `sortedSpan K b` is stable under left multiplication by `gen K L`, the span
of the image of `L` in `U(L)`. -/
theorem gen_mul_mem_sortedSpan (hb : Submodule.span K (Set.range b) = ⊤)
    {v u : UniversalEnvelopingAlgebra K L} (hv : v ∈ gen K L) (hu : u ∈ sortedSpan K b) :
    v * u ∈ sortedSpan K b := by
  have hle : gen K L ≤ Submodule.span K (Set.range (pbwGen K b)) := by
    rw [gen, Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    exact ι_mem_span_range_pbwGen K b hb x
  refine mul_mem_of_left_mem_span K (hle hv) ?_
  rintro _ ⟨i, rfl⟩
  exact pbwGen_mul_mem_sortedSpan K b hb i hu

/-- Every power of `gen K L` is contained in `sortedSpan K b`. -/
theorem genPow_le_sortedSpan (hb : Submodule.span K (Set.range b) = ⊤) (j : ℕ) :
    gen K L ^ j ≤ sortedSpan K b := by
  induction j with
  | zero =>
      rw [pow_zero]
      exact Submodule.one_le.mpr (one_mem_sortedSpan K b)
  | succ j ih =>
      rw [pow_succ']
      exact Submodule.mul_le.mpr fun v hv u hu => gen_mul_mem_sortedSpan K b hb hv (ih hu)

/-- The sorted monomials span the whole universal enveloping algebra. -/
theorem sortedSpan_eq_top (hb : Submodule.span K (Set.range b) = ⊤) :
    sortedSpan K b = ⊤ :=
  top_unique fun u _ =>
    iSup_le (fun j => genPow_le_sortedSpan K b hb j) (exists_mem_gen_pow K L u)

/-- **The spanning half of the Poincaré–Birkhoff–Witt theorem.** If
`b : Fin n → L` spans the Lie algebra `L`, then the universal enveloping
algebra `U(L)` is spanned, as a `K`-module, by the sorted products of the
elements `ι K (b i)`. -/
theorem span_sorted_prod_eq_top (hb : Submodule.span K (Set.range b) = ⊤) :
    Submodule.span K {u | ∃ l : List (Fin n), l.Pairwise (· ≤ ·) ∧
      (l.map fun i => (ι K (b i) : UniversalEnvelopingAlgebra K L)).prod = u} = ⊤ :=
  sortedSpan_eq_top K b hb

/-- The same statement phrased with `List.SortedLE`, the replacement in current
`Mathlib` for `List.Sorted (· ≤ ·)`. -/
theorem span_sortedLE_prod_eq_top (hb : Submodule.span K (Set.range b) = ⊤) :
    Submodule.span K {u | ∃ l : List (Fin n), l.SortedLE ∧
      (l.map fun i => (ι K (b i) : UniversalEnvelopingAlgebra K L)).prod = u} = ⊤ := by
  refine top_unique ?_
  rw [← span_sorted_prod_eq_top K b hb, Submodule.span_le]
  rintro u ⟨l, hl, rfl⟩
  exact Submodule.subset_span ⟨l, hl.sortedLE, rfl⟩

end Submission.Ado
