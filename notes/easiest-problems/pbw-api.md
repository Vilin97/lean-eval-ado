# The PBW development: API reference

Everything listed here is proved, `sorry`-free, zero-warning, and depends only on
`[propext, Classical.choice, Quot.sound]`. Files live under
`generated/adoIwasawa/Submission/Ado/`. Namespace `Submission.Ado.PBW` unless said
otherwise.

Nothing in this development existed in Lean 4 before: Mathlib's
`docs/1000.yaml:2123` lists the Poincaré–Birkhoff–Witt theorem with no `decl:`
field, `Mathlib/Algebra/Lie/Free.lean:44` and
`Mathlib/Algebra/Lie/SerreConstruction.lean:46` both say in prose that they are
blocked on it, and `Mathlib/Algebra/Lie/UniversalEnveloping.lean` (153 lines) stops
at the universal property.

## The polynomial module — `PBW/Defs.lean`

```
Mon n      := Fin n →₀ ℕ                  -- exponent vectors; `Finsupp.degree` is the total degree
Poly K n   := Mon n →₀ K                  -- the free K-module on monomials
mono a     := Finsupp.single a 1          -- the monomial z^a
e i        := Finsupp.single i 1          -- the exponent vector of the variable z_i
Aligned i a := ∀ j ∈ a.support, i ≤ j     -- "i is ≤ every variable occurring in a"
trunc d f  := f.filter (fun a => a.degree ≤ d)
```

The action, by Humphreys' recursion with a fuel parameter making it structural:

```
actAux γ : ℕ → Fin n → Mon n → Poly K n
act γ i a := actAux γ a.degree i a
```

Support lemmas: `aligned_zero`, `support_nonempty_of_not_aligned`, `lead`,
`lead_mem`, `lead_le`, `lead_lt`.

## Basic properties — `PBW/Props.lean`

| name | statement |
| --- | --- |
| `degree_e`, `degree_add_e`, `degree_sub_e`, `degree_lead_lt` | degree bookkeeping |
| `actAux_fuel_irrel`, `act_eq_actAux` | the fuel does not matter |
| `act_of_aligned` | **(A)** `Aligned i a → act γ i a = mono (a + e i)` |
| `act_of_not_aligned` | the recursive branch, in terms of `act` |
| `DegLE f d` | `∀ c ∈ f.support, c.degree ≤ d` |
| `DegLE_zero/_mono/_add/_sub/_smul/_sum/_mono_single/_linearCombination` | the `DegLE` calculus |
| `act_sub_mono_degLE` | **(B)** `DegLE (act γ i a - mono (a + e i)) a.degree` |
| `act_degLE` | `DegLE (act γ i a) (a.degree + 1)` |

## The action as an operator — `PBW/Action.lean`

```
rho γ i : Poly K n →ₗ[K] Poly K n := Finsupp.linearCombination K (act γ i)
rho_mono   : rho γ i (mono a) = act γ i a
rho_single : rho γ i (Finsupp.single a c) = c • act γ i a
```

Truncation: `trunc_add`, `trunc_eq_self`, `trunc_mono_of_lt`, `trunc_act`,
`act_eq_mono_add_trunc`.

**The aligned case of the Lie relation**, true by construction in every degree:

```
lie_rel_aligned : Aligned j a → j < i →
  rho γ i (rho γ j (mono a)) - rho γ j (rho γ i (mono a)) = ∑ k, γ i j k • act γ k a
```

with the supporting `not_aligned_add_e` and `lead_add_e`.

## The Lie module — `PBW/Module.lean`

```
gamma bas i j k := bas.repr ⁅bas i, bas j⁆ k          -- structure constants
rhoL bas        : L →ₗ[K] Module.End K (Poly K n)
rhoL_apply, rhoL_basis, rhoL_lie_basis
rhoL_lie : ∀ x y, ⁅rhoL bas x, rhoL bas y⁆ = rhoL bas ⁅x, y⁆      -- (C)
```

`rhoL_lie` is the theorem that `Poly K n` is a Lie module over `L`. The bracket on
`Module.End` is the commutator (`⁅f, g⁆ = f * g - g * f` holds by `rfl`; see
[`pbw-sanity-checks.lean`](pbw-sanity-checks.lean)).

## The enveloping algebra acts — `PBW/Env.lean`

```
rhoLie bas    : L →ₗ⁅K⁆ Module.End K (Poly K n)
envAction bas : UniversalEnvelopingAlgebra K L →ₐ[K] Module.End K (Poly K n)
envAction_ι   : envAction bas (ι K x) = rhoL bas x
ev bas        : UniversalEnvelopingAlgebra K L →ₗ[K] Poly K n,  ev bas u = envAction bas u (mono 0)
ev_apply, ev_one, ev_ι_basis, ev_ι_mul
```

`envAction` being an *algebra* morphism is what makes central elements of `U(L)`
act by operators commuting with the whole action — the mechanism the
characteristic-`p` argument runs on.

## Injectivity of `ι` — `PBW/Injective.lean`

```
e_injective
ev_ι       : ev bas (ι K x) = ∑ i, bas.repr x i • mono (e i)
ev_ι_coeff : (ev bas (ι K x)) (e j) = bas.repr x j
ι_injective_of_basis (bas) : Function.Injective (ι K : L → UniversalEnvelopingAlgebra K L)
ι_injective [FiniteDimensional K L] : Function.Injective (ι K)
```

## Unitriangular families — `PBW/Unitriangular.lean`

```
DegLT f d          := ∀ c ∈ f.support, c.degree < d
Unitriangular φ f  := ∀ s, DegLT (f s - mono (φ s)) (φ s).degree
```

| name | statement |
| --- | --- |
| `DegLT_zero_iff`, `DegLT.degLE`, `DegLT.apply_eq_zero` | basic |
| `sum_smul_mono` | `∑ c ∈ g.support, g c • mono c = g` |
| `mem_span_of_support` | a polynomial lies in a submodule containing the monomials of its support |
| `Unitriangular.apply_self` | `f s (φ s) = 1` |
| `Unitriangular.apply_of_ne` | `f s c = 0` for `c ≠ φ s` of degree `≥ (φ s).degree` |
| `Unitriangular.linearIndependent` | `φ` injective ⟹ `LinearIndependent K f` |
| `Unitriangular.span_eq_top` | `φ` surjective ⟹ `span K (range f) = ⊤` |

This is the abstract engine behind both the PBW basis of `U(L)` (index map the
identity on `Mon n`) and the restricted basis used in characteristic `p` (index map
`(b, m) ↦ b + q·m`).

## The Poincaré–Birkhoff–Witt theorem — `PBW/Basis2.lean`

```
pbwMonomial bas a := ((List.finRange n).map fun i => (ι K (bas i)) ^ a i).prod
  -- the ordered monomial; `Finset.prod` will not do, since `U(L)` is noncommutative
  -- and `Finset.prod` demands `CommMonoid`

ev_pbwMonomial_sub_mono   : DegLT (ev bas (pbwMonomial bas a) - mono a) a.degree
unitriangular_ev_pbwMonomial : Unitriangular id fun a => ev bas (pbwMonomial bas a)
sorted_prod_eq_pbwMonomial : l.Pairwise (· ≤ ·) →
    (l.map fun i => ι K (bas i)).prod = pbwMonomial bas (monOfList l)

linearIndependent_pbwMonomial : LinearIndependent K (pbwMonomial bas)
span_range_pbwMonomial        : Submodule.span K (Set.range (pbwMonomial bas)) = ⊤
pbwBasis bas : Module.Basis (Mon n) K (UniversalEnvelopingAlgebra K L)
pbwBasis_apply : pbwBasis bas a = (List.ofFn fun i => (ι K (bas i)) ^ a i).prod
```

Non-vacuity, checked in [`pbw-basis-checks.lean`](pbw-basis-checks.lean): for `n ≥ 1`
it follows that `¬ Module.Finite K (U(L))`, since the basis is indexed by the
infinite set `Mon n`.

## Ordered monomials span — `PBW/Sorting.lean`

For `b : Fin n → L` spanning `L`:

```
span_sorted_prod_eq_top :
  Submodule.span K {u | ∃ l : List (Fin n), l.Pairwise (· ≤ ·) ∧
    (l.map fun i => ι K (b i)).prod = u} = ⊤
span_sortedLE_prod_eq_top     -- the same with `List.SortedLE`
```

plus the length-graded machinery `sortedSpanLE`, `sortedSpan`,
`pbwGen_mul_prod_mem_sortedSpanLE` (the straightening lemma),
`gen_mul_mem_sortedSpan`, `genPow_le_sortedSpan`, `sortedSpan_eq_top`.

Note `List.Sorted` does **not** exist at Mathlib `905b9581` — it was removed in
favour of `List.Pairwise` and the `SortedLE`/`SortedLT` family.

## Characteristic `p` — `CharP/`

`AdPow.lean`:

```
ad K a := LinearMap.mulLeft K a - LinearMap.mulRight K a
ad_pow_char     : ad K a ^ p       = ad K (a ^ p)
ad_pow_char_pow : ad K a ^ p ^ i   = ad K (a ^ p ^ i)
```

`Central.lean`:

```
exists_pPolynomial_relation       -- A^(p^m) is a K-combination of the earlier p-powers, some m ≥ 1
exists_pPolynomial_relation_of_le -- the relation persists for every larger exponent
exists_pPolynomial_relation_of_ge -- a single m₀ that works for all m ≥ m₀
ad_isDeriv                        -- ad a is a derivation of the associative algebra
central_pPolynomial               -- ι(x)^(p^m) − ∑ λᵢ ι(x)^(p^i) is CENTRAL in U(L)
central_pPolynomial_mem_center
```

`Dispatch.lean`:

```
hasFaithfulFinRep_of_charP :
  (∀ p, Fact p.Prime → CharP K p → HasFaithfulFinRep K L) → HasFaithfulFinRep K L
```

so Ado–Iwasawa now reduces to the positive-characteristic case alone.
