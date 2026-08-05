import Submission.Ado.PBW.Env
import Submission.Ado.PBW.Unitriangular

/-!
# Iterated actions and the operators `Cⱼ`

This file proves the *triangularity* half of the characteristic-`p` argument.
Everything below is about the abstract structure constants `γ`; no property of
the Lie algebra is used beyond what `Submission/Ado/PBW/Props.lean` already
establishes:

* **(A)** `Aligned i a → act γ i a = mono (a + eᵢ)`;
* **(B)** `act γ i a - mono (a + eᵢ)` is supported in degrees `≤ |a|`.

From (A) and (B) one gets

```
ρ(xⱼ)^k (z^a) = z^(a + k eⱼ) + (terms of degree < |a| + k)
```

(`rho_pow_mono_triangular`).  Fixing an exponent `q` and coefficients `μ`, the
element

```
cⱼ = ι(xⱼ)^q - ∑_{t < q} μⱼₜ ι(xⱼ)^t  ∈ U(L)
```

acts on the polynomial module through an operator `Cⱼ` (`bigC`), and the
subtracted tail only contributes degrees `< |a| + q`, so

```
Cⱼ (z^a) = z^(a + q eⱼ) + (terms of degree < |a| + q)
```

(`bigC_mono_triangular`).  Finally, for a multi-index `m : Mon n` the product
`C^m` (`bigCpow`) satisfies

```
C^m (z^b) = z^(b + q·m) + (terms of degree < |b| + q|m|)
```

(`bigCpow_mono_triangular`).  This is exactly the unitriangularity hypothesis of
`Submission.Ado.PBW.Unitriangular`.

The `cⱼ` are defined *inside* `U(L)` rather than as raw polynomials in `ρ(xⱼ)`,
so that the commutation properties available in `U(L)` (the `cⱼ` are central for
a suitable choice of `q` and `μ`, by `Submission.Ado.central_pPolynomial`) are
inherited for free by the operators. Since `U(L)` is not commutative there is no
`Finset.prod` to form `∏ⱼ cⱼ^(mⱼ)`; we therefore multiply along a *word*
(`cWord`) and take for `C^m` the particular word `monList m` listing each index
`j` with multiplicity `m j` in increasing order (`bigCpow`).
-/

universe u

namespace Submission.Ado.PBW

variable {K : Type u} [Field K] {n : ℕ}

/-! ### Closure properties of `DegLT`

`Submission/Ado/PBW/Props.lean` proves the analogous statements for `DegLE`;
the strict versions are what the inductions below need. -/

/-- The zero polynomial is supported in degrees `< d` for every `d`. -/
theorem DegLT_zero (d : ℕ) : DegLT (0 : Poly K n) d := by
  intro c hc
  simp only [Finsupp.support_zero, Finset.notMem_empty] at hc

/-- `DegLT` is monotone in the degree bound. -/
theorem DegLT_mono {f : Poly K n} {d d' : ℕ} (hf : DegLT f d) (hd : d ≤ d') : DegLT f d' :=
  fun c hc => lt_of_lt_of_le (hf c hc) hd

/-- A degree bound `≤ d` is in particular a strict degree bound `< d + 1`. -/
theorem DegLE.degLT {f : Poly K n} {d : ℕ} (h : DegLE f d) : DegLT f (d + 1) :=
  fun c hc => Nat.lt_succ_of_le (h c hc)

/-- A sum of two polynomials of degree `< d` has degree `< d`. -/
theorem DegLT_add {f g : Poly K n} {d : ℕ} (hf : DegLT f d) (hg : DegLT g d) :
    DegLT (f + g) d := by
  intro c hc
  rcases Finset.mem_union.mp (Finsupp.support_add hc) with hc | hc
  · exact hf c hc
  · exact hg c hc

/-- A difference of two polynomials of degree `< d` has degree `< d`. -/
theorem DegLT_sub {f g : Poly K n} {d : ℕ} (hf : DegLT f d) (hg : DegLT g d) :
    DegLT (f - g) d := by
  intro c hc
  rcases Finset.mem_union.mp (Finsupp.support_sub hc) with hc | hc
  · exact hf c hc
  · exact hg c hc

/-- Scaling does not increase the degree. -/
theorem DegLT_smul {r : K} {f : Poly K n} {d : ℕ} (hf : DegLT f d) : DegLT (r • f) d :=
  fun c hc => hf c (Finsupp.support_smul hc)

/-- A finite sum of polynomials of degree `< d` has degree `< d`. -/
theorem DegLT_sum {ι : Type*} {s : Finset ι} {f : ι → Poly K n} {d : ℕ}
    (hf : ∀ k ∈ s, DegLT (f k) d) : DegLT (∑ k ∈ s, f k) d := by
  classical
  induction s using Finset.induction with
  | empty => simpa using DegLT_zero d
  | insert k s hk ih =>
      rw [Finset.sum_insert hk]
      exact DegLT_add (hf k (Finset.mem_insert_self k s))
        (ih fun l hl => hf l (Finset.mem_insert_of_mem hl))

/-- A linear combination of polynomials of degree `< d` has degree `< d`. -/
theorem DegLT_linearCombination {v : Mon n → Poly K n} {t : Poly K n} {d : ℕ}
    (hv : ∀ c ∈ t.support, DegLT (v c) d) :
    DegLT (Finsupp.linearCombination K v t) d := by
  rw [Finsupp.linearCombination_apply, Finsupp.sum]
  exact DegLT_sum fun c hc => DegLT_smul (hv c hc)

/-! ### Degrees of scalar multiples of exponent vectors -/

/-- The total degree is additive, hence multiplicative under scaling by a natural
number. -/
theorem degree_nsmul (k : ℕ) (a : Mon n) : (k • a).degree = k * a.degree := by
  induction k with
  | zero => simp
  | succ k ih => rw [succ_nsmul, map_add Finsupp.degree, ih]; ring

/-- The degree of the exponent vector `b + q·m`. This is the bound appearing in
`Submission.Ado.PBW.Unitriangular`. -/
theorem degree_add_nsmul (b : Mon n) (q : ℕ) (m : Mon n) :
    (b + q • m : Mon n).degree = b.degree + q * m.degree := by
  rw [map_add Finsupp.degree, degree_nsmul]

/-- `k • eⱼ` is the exponent vector of `zⱼ^k`, of degree `k`. -/
@[simp] theorem degree_nsmul_e (k : ℕ) (j : Fin n) : (k • e j : Mon n).degree = k := by
  rw [degree_nsmul, degree_e, mul_one]

/-- If `j` occurs in `a` then `eⱼ ≤ a`, so `a - eⱼ` recovers `a` after adding
`eⱼ` back. -/
theorem e_le_of_mem_support {a : Mon n} {j : Fin n} (hj : j ∈ a.support) : (e j : Mon n) ≤ a := by
  rw [e, Finsupp.single_le_iff]
  exact Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hj)

/-- Every exponent vector is the sum of its coordinates against the unit vectors. -/
theorem sum_smul_e (m : Mon n) : ∑ j : Fin n, m j • e j = m := by
  refine Finsupp.ext fun k => ?_
  rw [Finsupp.finsetSum_apply, Finset.sum_eq_single k]
  · rw [Finsupp.smul_apply, e_apply_self, smul_eq_mul, mul_one]
  · intro j _ hjk
    rw [Finsupp.smul_apply, e_apply_of_ne hjk, smul_zero]
  · intro hk
    exact absurd (Finset.mem_univ k) hk

/-! ### Iterating `ρ(xⱼ)` -/

section Rho

variable {γ : Fin n → Fin n → Fin n → K}

/-- Applying `ρ(xⱼ)` raises a `≤` degree bound by at most one. -/
theorem rho_degLE (j : Fin n) {f : Poly K n} {d : ℕ} (hf : DegLE f d) :
    DegLE (rho γ j f) (d + 1) := by
  rw [show rho γ j f = Finsupp.linearCombination K (act γ j) f from rfl]
  exact DegLE_linearCombination fun c hc => DegLE_mono (act_degLE j c) (by
    have := hf c hc; omega)

/-- Applying `ρ(xⱼ)` raises a `<` degree bound by at most one. -/
theorem rho_degLT (j : Fin n) {f : Poly K n} {d : ℕ} (hf : DegLT f d) :
    DegLT (rho γ j f) (d + 1) := by
  rw [show rho γ j f = Finsupp.linearCombination K (act γ j) f from rfl]
  exact DegLT_linearCombination fun c hc => DegLT_mono (act_degLE j c).degLT (by
    have := hf c hc; omega)

/-- Applying `ρ(xⱼ)^k` raises a `≤` degree bound by at most `k`. -/
theorem rho_pow_degLE' (j : Fin n) (k : ℕ) {f : Poly K n} {d : ℕ} (hf : DegLE f d) :
    DegLE ((rho γ j ^ k) f) (d + k) := by
  induction k with
  | zero => simpa using hf
  | succ k ih =>
      rw [show ((rho γ j ^ (k + 1)) f) = rho γ j ((rho γ j ^ k) f) by rw [pow_succ']; rfl]
      exact DegLE_mono (rho_degLE j ih) (by omega)

/-- Applying `ρ(xⱼ)^k` raises a `<` degree bound by at most `k`. -/
theorem rho_pow_degLT (j : Fin n) (k : ℕ) {f : Poly K n} {d : ℕ} (hf : DegLT f d) :
    DegLT ((rho γ j ^ k) f) (d + k) := by
  induction k with
  | zero => simpa using hf
  | succ k ih =>
      rw [show ((rho γ j ^ (k + 1)) f) = rho γ j ((rho γ j ^ k) f) by rw [pow_succ']; rfl]
      exact DegLT_mono (rho_degLT j ih) (by omega)

/-- `ρ(xⱼ)^k (z^a)` is supported in degrees `≤ |a| + k`. -/
theorem rho_pow_degLE (j : Fin n) (k : ℕ) (a : Mon n) :
    DegLE ((rho γ j ^ k) (mono a)) (a.degree + k) :=
  rho_pow_degLE' j k (DegLE_mono_single a)

/-- **Triangularity of the iterated action.**
`ρ(xⱼ)^k (z^a) = z^(a + k eⱼ) + (terms of degree < |a| + k)`. -/
theorem rho_pow_mono_triangular (j : Fin n) (k : ℕ) (a : Mon n) :
    DegLT ((rho γ j ^ k) (mono a) - mono (a + k • e j)) (a.degree + k) := by
  induction k with
  | zero =>
      simp only [pow_zero, Module.End.one_apply, zero_smul, add_zero, sub_self]
      exact DegLT_zero _
  | succ k ih =>
      have hdeg : (a + k • e j : Mon n).degree = a.degree + k := by
        rw [map_add Finsupp.degree, degree_nsmul_e]
      have hidx : a + (k + 1) • e j = a + k • e j + e j := by
        rw [succ_nsmul, add_assoc]
      have hsplit : (rho γ j ^ k) (mono a)
          = mono (a + k • e j) + ((rho γ j ^ k) (mono a) - mono (a + k • e j)) := by abel
      have hrw : ∀ x y z : Poly K n, x + y - z = x - z + y := fun x y z => by abel
      rw [show ((rho γ j ^ (k + 1)) (mono a)) = rho γ j ((rho γ j ^ k) (mono a)) by
        rw [pow_succ']; rfl, hsplit, map_add, rho_mono, hidx, hrw]
      refine DegLT_mono (DegLT_add ?_ (rho_degLT j ih)) (by omega)
      exact DegLT_mono (act_sub_mono_degLE j (a + k • e j)).degLT (by omega)

end Rho

/-! ### Words of indices

`U(L)` is not commutative, so a "monomial in the `cⱼ`" is a product along a word
of indices. `wordWeight` records the exponent vector such a word contributes,
and `monList` chooses, for each exponent vector, the word listing each index
with the right multiplicity in increasing order. -/

/-- The exponent vector contributed by a word of indices. -/
noncomputable def wordWeight (l : List (Fin n)) : Mon n := (l.map e).sum

/-- The empty word has weight `0`. -/
@[simp] theorem wordWeight_nil : wordWeight ([] : List (Fin n)) = 0 := rfl

/-- Prepending a letter adds the corresponding unit vector to the weight. -/
@[simp] theorem wordWeight_cons (j : Fin n) (l : List (Fin n)) :
    wordWeight (j :: l) = e j + wordWeight l := by
  simp [wordWeight]

/-- The weight of a concatenation is the sum of the weights. -/
theorem wordWeight_append (l₁ l₂ : List (Fin n)) :
    wordWeight (l₁ ++ l₂) = wordWeight l₁ + wordWeight l₂ := by
  simp [wordWeight]

/-- The weight of a `List.flatMap`. -/
theorem wordWeight_flatMap (f : Fin n → List (Fin n)) (l : List (Fin n)) :
    wordWeight (l.flatMap f) = (l.map fun j => wordWeight (f j)).sum := by
  induction l with
  | nil => simp
  | cons j l ih => rw [List.flatMap_cons, wordWeight_append, ih, List.map_cons, List.sum_cons]

/-- Repeating a single index `k` times contributes `k • eⱼ`. -/
theorem wordWeight_replicate (k : ℕ) (j : Fin n) :
    wordWeight (List.replicate k j) = k • e j := by
  induction k with
  | zero => simp
  | succ k ih => rw [List.replicate_succ, wordWeight_cons, ih, succ_nsmul]; abel

/-- The total degree of a word's weight is its length. -/
theorem degree_wordWeight (l : List (Fin n)) : (wordWeight l).degree = l.length := by
  induction l with
  | nil => simp
  | cons j l ih =>
      rw [wordWeight_cons, map_add Finsupp.degree, degree_e, ih, List.length_cons]
      omega

/-- The canonical word for an exponent vector: each index `j` repeated `m j`
times, in increasing order of `j`. -/
def monList (m : Mon n) : List (Fin n) :=
  (List.finRange n).flatMap fun j => List.replicate (m j) j

/-- The canonical word of `m` has weight `m`. -/
@[simp] theorem wordWeight_monList (m : Mon n) : wordWeight (monList m) = m := by
  rw [monList, wordWeight_flatMap]
  simp only [wordWeight_replicate]
  rw [← Fin.sum_univ_def fun j => m j • e j, sum_smul_e]

/-- The canonical word of `m` has length `|m|`. -/
@[simp] theorem length_monList (m : Mon n) : (monList m).length = m.degree := by
  rw [monList, List.length_flatMap, Finsupp.degree_eq_sum, Fin.sum_univ_def]
  simp

/-- The canonical word of `0` is empty. -/
@[simp] theorem monList_zero : monList (0 : Mon n) = [] := by
  rw [← List.length_eq_zero_iff, length_monList, map_zero]

/-- The canonical word of a nonzero exponent vector is nonempty. -/
theorem monList_ne_nil {m : Mon n} (hm : m ≠ 0) : monList m ≠ [] := by
  intro h
  exact hm (by rw [← wordWeight_monList m, h, wordWeight_nil])

/-! ### The operators `Cⱼ` -/

section Central

open UniversalEnvelopingAlgebra

variable {L : Type u} [LieRing L] [LieAlgebra K L]
  (bas : Module.Basis (Fin n) K L) (q : ℕ) (mu : Fin n → ℕ → K)

/-- The `p`-polynomial `cⱼ = ι(xⱼ)^q - ∑_{t < q} μⱼₜ ι(xⱼ)^t` in the universal
enveloping algebra. For a suitable choice of `q` and `μ` this element is central
(`Submission.Ado.central_pPolynomial`), but nothing in this file depends on
that. -/
noncomputable def cElt (j : Fin n) : UniversalEnvelopingAlgebra K L :=
  (ι K (bas j)) ^ q - ∑ t ∈ Finset.range q, mu j t • (ι K (bas j)) ^ t

/-- The operator by which `cElt bas q mu j` acts on the polynomial module. -/
noncomputable def bigC (j : Fin n) : Module.End K (Poly K n) :=
  envAction bas (cElt bas q mu j)

/-- `bigC` is the expected polynomial in `ρ(xⱼ)`. -/
theorem bigC_eq (j : Fin n) :
    bigC bas q mu j
      = rho (gamma bas) j ^ q - ∑ t ∈ Finset.range q, mu j t • rho (gamma bas) j ^ t := by
  simp only [bigC, cElt, map_sub, map_sum, map_smul, map_pow, envAction_ι, rhoL_basis]

/-- `bigC` raises a `<` degree bound by at most `q`. -/
theorem bigC_degLT (j : Fin n) {f : Poly K n} {d : ℕ} (hf : DegLT f d) :
    DegLT (bigC bas q mu j f) (d + q) := by
  rw [bigC_eq, LinearMap.sub_apply, LinearMap.sum_apply]
  refine DegLT_sub (rho_pow_degLT j q hf) (DegLT_sum fun t ht => ?_)
  rw [LinearMap.smul_apply]
  exact DegLT_smul (DegLT_mono (rho_pow_degLT j t hf)
    (by have := Finset.mem_range.mp ht; omega))

/-- **Triangularity of `Cⱼ`.**
`Cⱼ (z^a) = z^(a + q eⱼ) + (terms of degree < |a| + q)`: the subtracted tail
`∑_{t < q} μⱼₜ ρ(xⱼ)^t` only reaches degree `|a| + t < |a| + q`. -/
theorem bigC_mono_triangular (j : Fin n) (a : Mon n) :
    DegLT (bigC bas q mu j (mono a) - mono (a + q • e j)) (a.degree + q) := by
  rw [bigC_eq, LinearMap.sub_apply, LinearMap.sum_apply,
    show ∀ x y z : Poly K n, x - y - z = x - z - y from fun x y z => sub_right_comm x y z]
  refine DegLT_sub (rho_pow_mono_triangular j q a) (DegLT_sum fun t ht => ?_)
  rw [LinearMap.smul_apply]
  exact DegLT_smul (DegLT_mono (rho_pow_degLE j t a).degLT
    (by have := Finset.mem_range.mp ht; omega))

/-! ### Products along words -/

/-- The product `c_{j₁} ⋯ c_{j_k}` along a word of indices. -/
noncomputable def cWord (l : List (Fin n)) : UniversalEnvelopingAlgebra K L :=
  (l.map (cElt bas q mu)).prod

/-- The operator by which `cWord bas q mu l` acts on the polynomial module. -/
noncomputable def bigCword (l : List (Fin n)) : Module.End K (Poly K n) :=
  envAction bas (cWord bas q mu l)

/-- The empty word is the unit of `U(L)`. -/
@[simp] theorem cWord_nil : cWord bas q mu [] = 1 := by
  rw [cWord, List.map_nil, List.prod_nil]

/-- Peeling the first letter off a word. -/
theorem cWord_cons (j : Fin n) (l : List (Fin n)) :
    cWord bas q mu (j :: l) = cElt bas q mu j * cWord bas q mu l := by
  rw [cWord, cWord, List.map_cons, List.prod_cons]

/-- The empty word acts as the identity. -/
@[simp] theorem bigCword_nil : bigCword bas q mu [] = 1 := by
  rw [bigCword, cWord_nil, map_one]

/-- Peeling the first letter off a word, on the operator side. -/
theorem bigCword_cons (j : Fin n) (l : List (Fin n)) :
    bigCword bas q mu (j :: l) = bigC bas q mu j * bigCword bas q mu l := by
  rw [bigCword, cWord_cons, map_mul, bigC, bigCword]

/-- **Triangularity of a word of `C`'s.** -/
theorem bigCword_mono_triangular (l : List (Fin n)) (b : Mon n) :
    DegLT (bigCword bas q mu l (mono b) - mono (b + q • wordWeight l))
      (b.degree + q * l.length) := by
  induction l generalizing b with
  | nil =>
      simp only [bigCword_nil, wordWeight_nil, smul_zero, add_zero, Module.End.one_apply, sub_self]
      exact DegLT_zero _
  | cons j l ih =>
      have hlen : q * (l.length + 1) = q * l.length + q := by ring
      have hbdeg : (b + q • wordWeight l : Mon n).degree = b.degree + q * l.length := by
        rw [map_add Finsupp.degree, degree_nsmul, degree_wordWeight]
      have hidx : b + q • wordWeight (j :: l) = b + q • wordWeight l + q • e j := by
        rw [wordWeight_cons, smul_add]; abel
      have hIH := ih b
      set w := bigCword bas q mu l (mono b) - mono (b + q • wordWeight l) with hw
      have hval : bigCword bas q mu l (mono b) = mono (b + q • wordWeight l) + w := by
        rw [hw]; abel
      have hrw : ∀ x y z : Poly K n, x + y - z = x - z + y := fun x y z => by abel
      rw [bigCword_cons, Module.End.mul_apply, hval, map_add, hidx, hrw, List.length_cons]
      refine DegLT_add (DegLT_mono
          (bigC_mono_triangular bas q mu j (b + q • wordWeight l)) ?_)
        (DegLT_mono (bigC_degLT bas q mu j hIH) (by omega))
      rw [hbdeg]
      omega

/-! ### Multi-index powers -/

/-- The multi-index power `C^m = ∏ⱼ Cⱼ^(mⱼ)`, formed along the canonical word
`monList m`. -/
noncomputable def bigCpow (m : Mon n) : Module.End K (Poly K n) :=
  bigCword bas q mu (monList m)

/-- `C^0` is the identity. -/
theorem bigCpow_zero : bigCpow bas q mu 0 = LinearMap.id := by
  rw [bigCpow, monList_zero, bigCword_nil]
  exact Module.End.one_eq_id

/-- **Triangularity of the multi-index powers.**
`C^m (z^b) = z^(b + q·m) + (terms of degree < |b| + q|m|)`. -/
theorem bigCpow_mono_triangular (m : Mon n) (b : Mon n) :
    DegLT (bigCpow bas q mu m (mono b) - mono (b + q • m)) (b.degree + q * m.degree) := by
  have h := bigCword_mono_triangular bas q mu (monList m) b
  rwa [wordWeight_monList, length_monList] at h

/-- `bigCpow_mono_triangular` in the shape required by
`Submission.Ado.PBW.Unitriangular`: the correction term is supported strictly
below the degree of the leading exponent vector `b + q·m`. -/
theorem bigCpow_mono_triangular' (m : Mon n) (b : Mon n) :
    DegLT (bigCpow bas q mu m (mono b) - mono (b + q • m)) (b + q • m : Mon n).degree := by
  rw [degree_add_nsmul]
  exact bigCpow_mono_triangular bas q mu m b

/-- For a nonzero multi-index, `C^m` factors through some `Cⱼ`; in particular its
range is contained in the range of that `Cⱼ`. -/
theorem exists_bigC_factor {m : Mon n} (hm : m ≠ 0) :
    ∃ (j : Fin n) (A : Module.End K (Poly K n)), bigCpow bas q mu m = bigC bas q mu j * A := by
  obtain ⟨j, l, hl⟩ := List.exists_cons_of_ne_nil (monList_ne_nil hm)
  exact ⟨j, bigCword bas q mu l, by rw [bigCpow, hl, bigCword_cons]⟩

end Central

end Submission.Ado.PBW
