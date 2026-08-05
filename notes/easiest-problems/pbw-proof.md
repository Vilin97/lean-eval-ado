# The Poincaré–Birkhoff–Witt theorem: the central construction, in full

*A gap-free, formalization-ready write-up of the inductive construction of the `L`-module structure on the polynomial algebra, together with the deduction of the PBW basis.*

---

## 0. Executive summary — read this first

**There is an error in the recursion as stated in the task.** The task proposes

```
x_i · z^a := z_j (x_i · z^b) + [x_i, x_j] · z^b        (j = min supp a, b = a − e_j)
             ^^^^ multiplication by the variable z_j
```

The correct recursion (Humphreys §17.4, Jacobson Ch. V §2, Dixmier 2.1.9, and every
lecture-note treatment I checked) uses the **action of `x_j`**, not multiplication by `z_j`:

```
x_i · z^a := x_j · (x_i · z^b) + [x_i, x_j] · z^b
             ^^^^ the action, already constructed in degree ≤ |a| − 1
```

which unfolds, using `x_i · z^b = z_i z^b + w` with `w ∈ P_{|b|}`, into the explicit formula

```
x_i · z^a := z_i z^a + x_j · w + [x_i, x_j] · z^b,     w := (x_i · z^b) − z_i z^b.
```

Every term on the right of this last line is supplied by the **previous** stage of the
induction, so there is no circularity — this is exactly why the literature phrases it this way.

Your diagnosis of the sticking point ("`x_j · w = z_j w` is false in general") is **correct**,
and the resolution is exactly the one you guessed — `w` is handled by the previous stage of the
induction — but it is applied *inside the definition*, not as a later repair. Once the definition
is correct, the case you were stuck on (`j ≼ a`, `i > j`) becomes **true by definition, term by
term**, with nothing left to prove. Section 6.2 spells this out.

I verified this numerically (§12): with the correct recursion, (C) holds for all monomials up to
degree 4–5 on five different Lie algebras; with the recursion as stated in the task, (C) already
**fails** on a 3-dimensional solvable Lie algebra at `|a| = 1`. An explicit counterexample is in
§6.5.

**Answer to item 4 (char/field):** confirmed, the argument uses **neither** `char K = 0` **nor**
that `K` is a field. It works verbatim over an arbitrary commutative ring `K` provided `L` is
**free** as a `K`-module with a totally ordered basis. Being a field is used *only* to guarantee
such a basis exists. There is no division by any integer anywhere; in particular char 2 is fine,
provided one uses the *alternating* axiom `[x,x] = 0` (as Mathlib's `LieRing` does) rather than
mere antisymmetry. Details and the one place where a naive proof would divide by 2 are in §9.

---

## 1. Setting and notation

Throughout:

* `K` is a commutative ring with `1` (take `K` a field if you like; see §9).
* `L` is a Lie algebra over `K`, **free** as a `K`-module, with a basis `(x_i)_{i ∈ I}` indexed by
  a **totally ordered** set `I`. (Think `I = {1 < 2 < ⋯ < n}`; nothing below needs `I` finite or
  well-ordered — only that every finite nonempty subset of `I` has a minimum, which totality gives.)
* Structure constants: `[x_i, x_j] = Σ_k γ_{ijk} x_k`, a finite sum.
* `Λ := ℕ^{(I)}` is the monoid of **finitely supported** functions `I → ℕ` ("multi-indices"),
  written additively, with `e_i` the `i`-th standard basis vector. `|a| := Σ_i a_i`.
  `supp a := {i : a_i ≠ 0}` is finite.
* `P := K[z_i : i ∈ I]` with `K`-basis the monomials `z^a := ∏_i z_i^{a_i}`, `a ∈ Λ`.
* `P^{(d)} := span_K{z^a : |a| = d}` (homogeneous component of degree `d`), and
  `P_m := ⊕_{d ≤ m} P^{(d)} = span_K{z^a : |a| ≤ m}`, with the convention `P_{-1} := 0`.
  So `P_{-1} ⊆ P_0 ⊆ P_1 ⊆ ⋯` and `P = ⋃_m P_m`.

**Definition 1.1 (the relation `i ≼ a`).** For `i ∈ I` and `a ∈ Λ` write

```
i ≼ a   :⟺   ∀ j ∈ supp a, i ≤ j       (equivalently: ∀ j < i, a_j = 0).
```

This is the task's "`i ≤ a`"; I use `≼` to avoid clashing with the order on `I`.

**Lemma 1.2 (combinatorics of `≼`).** For all `i, k ∈ I`, `a, b ∈ Λ`:

1. `i ≼ 0` for every `i`.
2. If `a ≠ 0` then `min supp a` exists, and `i ≼ a ⟺ i ≤ min supp a`.
3. If `i ≼ a` and `i ≤ k` then `i ≼ a + e_k`.
4. If `a ≠ 0` and `j := min supp a`, then `j ≼ a` and `j ≼ a − e_j`.
5. If `¬(i ≼ a)` then `a ≠ 0` and `min supp a < i`.
6. If `j ≼ a` then `min supp (a + e_j) = j`; consequently `¬(i ≼ a + e_j)` for every `i > j`.
7. If `b ≤ a` pointwise and `i ≼ a` then `i ≼ b`.

*Proof.* All immediate from Definition 1.1 and totality of `≤` on `I`. For (6): `supp(a + e_j) =
supp a ∪ {j}` and every element of `supp a` is `≥ j`. ∎

*(Lean: these are the `Finsupp`/`Finset.min'` lemmas you will want as a preliminary file. The
formulation `∀ j ∈ a.support, i ≤ j` is the friendliest; item (2) is then
`Finset.le_min'_iff` / `Finset.min'_le`.)*

**Notation 1.3.** `z_i z^a = z^{a + e_i}`, so the monomial basis is multiplicative:
`z^a z^b = z^{a+b}`. In particular `z^a = z_j z^{a − e_j}` whenever `a_j ≥ 1`.

---

## 2. The statement to be proved

**Theorem 2.1 (main construction).** There is a unique `K`-bilinear map

```
L × P → P,    (x, f) ↦ x · f
```

such that

* **(A)** `x_i · z^a = z_i z^a` whenever `i ≼ a`;
* **(B)** `x_i · z^a − z_i z^a ∈ P_{|a|}` for all `i, a`;
* **(C)** `x · (y · f) − y · (x · f) = [x, y] · f` for all `x, y ∈ L`, `f ∈ P`.

Note `z_i z^a ∈ P^{(|a|+1)}`, so (B) says the "error term" drops the degree by at least one.

*Remark 2.2 (uniqueness).* (A) + (C) already force the map: see §7. (B) is what makes (C) even
*typecheck* at each finite stage of the induction (it is what confines `x · z^a` to `P_{|a|+1}`),
and it is what powers the final triangularity argument in §10.

---

## 3. The exact inductive scheme

This answers item 1 of the task.

For `m ≥ 0` let

> **`Lem(m)`** : *There is a unique `K`-bilinear map `f_m : L × P_m → P` satisfying*
>
> * **(A_m)** `f_m(x_i, z^a) = z_i z^a`  for all `i ∈ I` and all `a` with `|a| ≤ m` and `i ≼ a`;
> * **(B_m)** `f_m(x_i, z^a) − z_i z^a ∈ P_{|a|}`  for all `i ∈ I` and all `a` with `|a| ≤ m`;
> * **(C_m)** `f_m(x_i, f_m(x_j, z^a)) − f_m(x_j, f_m(x_i, z^a)) = f_m([x_i,x_j], z^a)`
>   for all `i, j ∈ I` and all `a` with `|a| ≤ m − 1`.
>
> *Moreover* `f_m |_{L × P_{m−1}} = f_{m−1}`.

**Three points about the asymmetry `|a| ≤ m` vs. `|a| ≤ m − 1` in (C_m).**

1. **(C_m) would not typecheck for `|a| = m`.** The inner term `f_m(x_j, z^a)` lies in `P_{m+1}`
   by (B_m), which is outside the domain `P_m` of `f_m`; the outer application would be undefined.
   For `|a| ≤ m − 1`, (B_m) gives `f_m(x_j, z^a) ∈ P_{|a|+1} ⊆ P_m` ✓. (Booher makes exactly this
   remark: *"condition `C_n` is actually well defined because `f_n(x_j ⊗ z_J)` is in `P_n` by
   condition `B_n`"*.)
2. **The lag is not a defect, it is the engine.** At stage `m` we get to *define* `f_m` on degree-`m`
   monomials, and we then *verify* (C) one degree lower than we have defined. The definition on
   degree `m` is precisely what makes (C) come out on degree `m − 1`.
3. **This is why the naive induction fails.** If you try to prove (A), (B), (C) all at level `m`
   simultaneously, or (C) at level `m`, you are asserting an identity that involves values of the
   map that have not been defined yet.

**The recursion at stage `m`.** For `m ≥ 1` and `|a| = m`, define

```
(D1)  i ≼ a       ⟹   f_m(x_i, z^a) := z_i z^a
(D2)  ¬(i ≼ a)    ⟹   let j := min supp a  (so j < i by Lemma 1.2(5)),
                       let b := a − e_j    (so |b| = m − 1, j ≼ b by Lemma 1.2(4)),
                       let w := f_{m−1}(x_i, z^b) − z_i z^b   (∈ P_{m−1} by (B_{m−1})),
                       f_m(x_i, z^a) := z_i z^a + f_{m−1}(x_j, w) + f_{m−1}([x_i, x_j], z^b)
```

and on `P_{m−1}` set `f_m := f_{m−1}`. Extend `K`-bilinearly (legitimate: `(x_i)` is a `K`-basis
of `L` and `(z^a)_{|a| ≤ m}` is a `K`-basis of `P_m`).

**This is exactly Humphreys' formula.** Booher's transcription of it reads verbatim:

> `f_n(x_i ⊗ z_j z_{J'}) = z_i z_J + f_{n−1}(x_j ⊗ w) + f_{n−1}([x_i,x_j] ⊗ z_{J'})`

(his `z_J = z_j z_{J'}`, i.e. our `z^a = z_j z^b`, and his `w` is our `w`). Swanson's notes give
the same formula with `y := −w`: `x_λ · z_Σ = z_λ z_Σ − x_μ · y − [x_λ, x_μ] · z_T`.

**Crucially: every term on the right-hand side of (D2) is a value of `f_{m−1}`.** There is *no*
recursive call inside stage `m`. This is the property that makes the whole thing a plain
structural recursion on `m` (see §11).

**Lemma 3.1 (equivalent "conceptual" form of (D2)).** With the notation of (D2),

```
f_m(x_i, z^a) = f_m(x_j, f_{m−1}(x_i, z^b)) + f_{m−1}([x_i, x_j], z^b).
```

*Proof.* `f_{m−1}(x_i, z^b) = z_i z^b + w = z^{b + e_i} + w`, so by bilinearity
`f_m(x_j, f_{m−1}(x_i, z^b)) = f_m(x_j, z^{b+e_i}) + f_m(x_j, w)`.

* First term: `|b + e_i| = m` and `j ≼ b + e_i` (Lemma 1.2(3), since `j ≼ b` and `j < i`), so by
  **(D1)** `f_m(x_j, z^{b+e_i}) = z_j z^{b+e_i} = z_j z_i z^b = z_i z^a` (using `a = b + e_j`).
* Second term: `w ∈ P_{m−1}`, so `f_m(x_j, w) = f_{m−1}(x_j, w)` by the compatibility clause.

Adding gives the claim. ∎

So the "conceptual" recursion `x_i · z^a = x_j · (x_i · z^b) + [x_i, x_j] · z^b` is legitimate, and
the *only* thing that has to be checked to make sense of it is that `x_j ·` can be applied to
`x_i · z^b ∈ P_m`: the leading monomial `z_i z^b` is handled by (D1) (which is legal because
`j ≼ b + e_i`), and the remainder `w` by `f_{m−1}` (which is legal because `deg w ≤ m − 1`).
**That split is the entire content of the "sticking point".**

---

## 4. Base case `m = 0`

`P_0 = K · 1 = K · z^0`.

* (A_0) forces `f_0(x_i, z^0) = z_i z^0 = z_i` (note `i ≼ 0` always, Lemma 1.2(1)). Define it so.
  This also *is* the uniqueness at stage `0`.
* (B_0): `f_0(x_i, z^0) − z_i z^0 = 0 ∈ P_0` ✓.
* (C_0): vacuous — there is no `a` with `|a| ≤ −1`. ✓
* Compatibility clause: vacuous (`P_{-1} = 0`).

∎

---

## 5. Stage `m ≥ 1`: verification of (A_m) and (B_m)

Assume `Lem(m−1)`, and define `f_m` by (D1)/(D2) and `f_m|_{P_{m−1}} := f_{m−1}`.

**(A_m).** For `|a| ≤ m − 1` this is (A_{m−1}). For `|a| = m` and `i ≼ a` it is (D1) verbatim. ✓

**Lemma 5.1 (degree bound, corollary of (B)).** If `Lem(r)` holds and `p ∈ P_r`, then
`f_r(x, p) ∈ P_{r+1}` for every `x ∈ L`. More precisely, if `p ∈ P_s` with `s ≤ r`, then
`f_r(x, p) ∈ P_{s+1}`.

*Proof.* By bilinearity reduce to `x = x_i`, `p = z^a` with `|a| ≤ s`. Then
`f_r(x_i, z^a) = z_i z^a + (\text{elt of } P_{|a|})` by (B_r), and `z_i z^a ∈ P^{(|a|+1)} ⊆ P_{s+1}`,
`P_{|a|} ⊆ P_{s+1}`. ∎

**(B_m).** For `|a| ≤ m − 1` this is (B_{m−1}). For `|a| = m`:

* If `i ≼ a`: `f_m(x_i, z^a) − z_i z^a = 0 ∈ P_m`. ✓
* If `¬(i ≼ a)`: by (D2),
  `f_m(x_i, z^a) − z_i z^a = f_{m−1}(x_j, w) + f_{m−1}([x_i,x_j], z^b)`.
  Now `w ∈ P_{m−1}` by (B_{m−1}), so `f_{m−1}(x_j, w) ∈ P_m` by Lemma 5.1; and `z^b ∈ P_{m−1}`,
  so `f_{m−1}([x_i,x_j], z^b) ∈ P_m` by Lemma 5.1 (applied after expanding `[x_i,x_j]` in the
  basis). Hence the difference lies in `P_m = P_{|a|}`. ✓

**This is why the definition is written as `z_i z^a + …` rather than as
`x_j · (x_i · z^b) + …`:** in the first form (B_m) is immediate by inspection. Booher: *"Property
`A_n` is obviously satisfied, and so is `B_n`, since the second and third terms are in `P_{n−1}` by
`B_{n−1}`."* (He means `P_n`; the terms lie in `P_n`, cf. Lemma 5.1.) Swanson: *"Written this way,
it is evident that `(B_{m+1})` is satisfied."*

---

## 6. Stage `m ≥ 1`: verification of (C_m) — every case

This is item 2 and item 3 of the task. Goal:

> For all `i, j ∈ I` and all `a` with `|a| ≤ m − 1`:
> `f_m(x_i, f_m(x_j, z^a)) − f_m(x_j, f_m(x_i, z^a)) = f_m([x_i,x_j], z^a).`   (★)

All terms are defined: `f_m(x_j, z^a) ∈ P_{|a|+1} ⊆ P_m` by Lemma 5.1.

From now on I drop `f_m` and write `x · p` for `f_m(x, p)`, with the understanding that on
`P_{m−1}` this is `f_{m−1}` (compatibility clause). Define, for `x, y ∈ L` and `p ∈ P_m`,

```
D(x, y; p) := x · (y · p) − y · (x · p) − [x, y] · p ∈ P.
```

(★) says `D(x_i, x_j; z^a) = 0` for `|a| ≤ m − 1`.

### 6.0 Four structural reductions

**(R1) Bilinearity in `(x, y)`.** For fixed `p ∈ P_{m−1}`, the map `(x, y) ↦ D(x, y; p)` is
`K`-bilinear `L × L → P`. Hence if `D(x_i, x_j; p) = 0` for all pairs of *basis* elements, then
`D(x, y; p) = 0` for all `x, y ∈ L`.

*Proof.* `x · q` is `K`-linear in `x` (by construction), `[x, y]` is bilinear, and `p ↦ x · p` is
linear. Composition/subtraction of bilinear things. (Domain check: `p ∈ P_{m−1} ⟹ y·p ∈ P_m ⟹`
`x·(y·p)` defined.) ∎

> *This reduction is used repeatedly below with `x` or `y` a bracket like `[x_i, x_k]`, which is
> not a basis element.* Swanson's notes use it silently ("applied `(C_m)` to commute
> `x_λ · [x_μ, x_ν]`"). In Lean it is one `LinearMap`/`ext` argument and should be a standalone
> lemma.

**(R2) Linearity in `p`.** For fixed `x, y`, `p ↦ D(x, y; p)` is `K`-linear on `P_{m−1}`. Hence it
suffices to prove (★) on monomials, and one may split a polynomial into its parts.

**(R3) Antisymmetry and the diagonal.**

* `D(x, x; p) = x·(x·p) − x·(x·p) − [x,x]·p = −[x,x]·p = 0` since `[x,x] = 0`.
  **(Uses the alternating axiom, not just antisymmetry — see §9.)**
* `D(y, x; p) = −D(x, y; p)`, using `[y,x] = −[x,y]` (which follows from `[·,·]` alternating by
  polarizing `0 = [x+y, x+y]`).

Hence in proving (★) we may assume **`i > j`**.

**(R4) Lower degrees are inherited.** For `|a| ≤ m − 2`, (★) is exactly (C_{m−1}) together with
`f_m|_{P_{m−1}} = f_{m−1}`: all four applications of `f` occur on arguments in `P_{m−1}`
(`z^a ∈ P_{m−2}`, `x_j · z^a ∈ P_{m−1}` by Lemma 5.1).

**Therefore only the following remains:**

> **Prove `D(x_i, x_j; z^a) = 0` for `i > j` and `|a| = m − 1`.**

We split on whether `j ≼ a`.

### 6.1 Data available in the remaining case

* `(A_m)`, `(B_m)` — proved in §5, valid up to degree `m`.
* `(C_{m−1})` — the induction hypothesis: `D(x, y; p) = 0` for all `x, y ∈ L` and all
  `p ∈ P_{m−2}` (using (R1) to upgrade from basis pairs).
* Lemma 5.1 for degree bookkeeping.
* The recursion (D1)/(D2) *as a definitional equation*.

### 6.2 Case 1: `j ≼ a` (with `i > j`, `|a| = m − 1`) — **true by definition**

This is the case the task got stuck on. With the correct recursion it closes with **no work at
all**; I write it out term by term.

Put `a' := a + e_j`, so `|a'| = m`. By Lemma 1.2(6), `min supp a' = j` and `¬(i ≼ a')` (as
`i > j`); also `a' − e_j = a`. So (D2) applies to `(i, a')` with **its** `j` equal to our `j` and
**its** `b` equal to our `a`:

```
x_i · z^{a'} = z_i z^{a'} + x_j · w + [x_i, x_j] · z^a,      where w := x_i · z^a − z_i z^a.   (6.2.1)
```

Now compute the two sides of (★).

**Left side.**

```
x_i · (x_j · z^a)
  = x_i · (z_j z^a)                                  [ (A_{m−1}), since j ≼ a and |a| = m−1 ]
  = x_i · z^{a'}                                     [ z_j z^a = z^{a + e_j} = z^{a'} ]
  = z_i z^{a'} + x_j · w + [x_i, x_j] · z^a.         [ (6.2.1) ]
```

**Right side.**

```
x_j · (x_i · z^a) + [x_i, x_j] · z^a
  = x_j · (z_i z^a + w) + [x_i, x_j] · z^a           [ definition of w ]
  = x_j · z^{a + e_i} + x_j · w + [x_i, x_j] · z^a   [ linearity in the second slot ]
  = z_j z^{a + e_i} + x_j · w + [x_i, x_j] · z^a     [ (A_m): |a + e_i| = m and j ≼ a + e_i
                                                       by Lemma 1.2(3), since j ≼ a and j < i ]
  = z_i z^{a'}     + x_j · w + [x_i, x_j] · z^a.     [ z_j z^{a+e_i} = z^{a + e_i + e_j} = z_i z^{a'} ]
```

The two sides are **syntactically identical**. ∎

**Commentary — exactly how the literature closes your sticking point.**

Your worry was: "one must show `x_j · (x_i · z^a) = z_j · (x_i · z^a)`, but `x_j · w = z_j w` is
false in general." That obligation only arises from the *incorrect* recursion. In the correct
recursion the term `x_j · w` appears **on both sides**, so it cancels without ever being
evaluated. Concretely:

* the summand `z_i z^a` of `x_i · z^a` is handled by **(A_m)**, because `j ≼ a + e_i` — this is the
  step you correctly identified as fine;
* the summand `w` is handled by **`f_{m−1}`** — and *not* by (A), and *not* by (C) either. It is
  simply carried along uninterpreted, because the definition (D2) was built to contain the
  symbol `f_{m−1}(x_j, w)` verbatim.

So your intuition ("`w` is handled by the induction hypothesis in degree `|a|`, not by (A)") is
right, but the mechanism is **the definition**, not a subsequent verification. **No strengthening
of the inductive statement is needed for Case 1.** (A strengthening *is* convenient for Case 2 —
see Lemma 6.3 — but it is a lemma proved inside the stage-`m` step, not an addition to `Lem(m)`.)

Booher's text for this case, with his typos corrected:

> By the way we constructed `f_n`, `C_n` is satisfied if `j < i` and `j ≼ J` since
> `f_n(x_i ⊗ f_{n−1}(x_j ⊗ z_J)) = f_n(x_i ⊗ z_j z_J) = z_i z_j z_J + f_{n−1}(x_j ⊗ w) +
> f_{n−1}([x_i,x_j] ⊗ z_J) = f_n(x_j ⊗ f_{n−1}(x_i ⊗ z_J)) + f_{n−1}([x_i,x_j] ⊗ z_J)`.

Swanson: *"we've declared `(C_{m+1})` to hold when `μ < λ`, `μ ≼ T`."* — "declared", i.e. by fiat
of the definition.

### 6.3 An auxiliary lemma (the one genuine strengthening, local to stage `m`)

Case 2 needs (★) not just for monomials but for certain *polynomials* of degree `m − 1`. Define,
for `k ∈ I`,

```
Q_k := P_{m−2} + span_K { z^d : |d| = m − 1,  k ≼ d }   ⊆ P_{m−1}.
```

**Lemma 6.3 (extended (C) at the pivot index).** Let `k ∈ I` and `i > k`. Then
`D(x_i, x_k; p) = 0` for every `p ∈ Q_k`.

*Proof.* By (R2), `p ↦ D(x_i, x_k; p)` is linear, so check on the two kinds of generators.

* `p ∈ P_{m−2}`: this is (C_{m−1}) (via (R4)). ✓
* `p = z^d` with `|d| = m − 1` and `k ≼ d`: this is **Case 1 (§6.2)** applied to the pair
  `(i, k)` — legitimate because `i > k`, `|d| = m − 1` and `k ≼ d`. ✓  ∎

*(Domain check: `p ∈ P_{m−1} ⟹ x_k · p ∈ P_m ⟹ x_i · (x_k · p)` is defined.)*

This is the statement Booher gestures at with *"Since `i > k` and `k ≼ j, K` and `w ∈ P_{n−2}`,
`C_n` holds for the first term"*, and that Swanson spells out as *"In showing that `(C_{m+1})`
applies to commute `x_λ · x_ν` … we must break `x_μ · z_U` into `z_μ z_U + w` … We then must apply
`(C_m)` to `x_λ · x_ν · w` and `(C_{m+1})` to `x_λ · x_ν · z_μ z_U`, which is valid since
`ν ≼ (μ, U)`."*

**Lemma 6.4 (membership test).** Let `k ≼ c`, `|c| = m − 2`, and let `l ∈ I` with `k ≤ l`. Then
`x_l · z^c ∈ Q_k`.

*Proof.* By (B_{m−1}), `x_l · z^c = z_l z^c + v = z^{c + e_l} + v` with `v ∈ P_{m−2}`. And
`|c + e_l| = m − 1` with `k ≼ c + e_l` by Lemma 1.2(3) (`k ≼ c`, `k ≤ l`). ∎

### 6.4 Case 2: `¬(j ≼ a)` (with `i > j`, `|a| = m − 1`) — reduction to Case 1 + Jacobi

Since `¬(j ≼ a)` we have `a ≠ 0`, hence `m ≥ 2`. Put

```
k := min supp a,      so  k < j < i,        c := a − e_k,   |c| = m − 2,   k ≼ c
```

(Lemma 1.2(4),(5)). Note `z^a = z_k z^c` and, by **(A_{m−2})**, `x_k · z^c = z_k z^c = z^a`.

Throughout, all `f`-applications below have arguments in `P_m` or lower; I record the checks in
brackets.

#### Step 1: unfold `x_i · z^a` and `x_j · z^a` through the pivot `k`

Apply (C_{m−1}) to the pair `(x_i, x_k)` on `z^c ∈ P_{m−2}` and use `x_k · z^c = z^a`:

```
(E1)   x_i · z^a = x_k · (x_i · z^c) + [x_i, x_k] · z^c
(E2)   x_j · z^a = x_k · (x_j · z^c) + [x_j, x_k] · z^c
(E3)   [x_i,x_j] · z^a = x_k · ([x_i,x_j] · z^c) + [[x_i,x_j], x_k] · z^c
```

(E3) is (C_{m−1}) for the pair `([x_i,x_j], x_k)` — legitimate by **(R1)**.

*(These are also literally the definition (D2) at stage `m−1`, by Lemma 3.1. Either justification
is fine; (C_{m−1}) is the uniform one.)*

#### Step 2: apply `x_i` to (E2), and `x_j` to (E1)

`x_j · z^c ∈ P_{m−1}` (Lemma 5.1), so `x_k · (x_j · z^c) ∈ P_m` and `x_i ·` applies. Likewise
`[x_j, x_k] · z^c ∈ P_{m−1}` and `x_i ·` applies.

```
x_i · (x_j · z^a) = x_i · (x_k · (x_j · z^c))  +  x_i · ([x_j, x_k] · z^c)
x_j · (x_i · z^a) = x_j · (x_k · (x_i · z^c))  +  x_j · ([x_i, x_k] · z^c)
```

#### Step 3: commute `x_i` past `x_k` (and `x_j` past `x_k`) — **this is where Lemma 6.3 fires**

By Lemma 6.4 with `l := j` (`k ≤ j` ✓): `x_j · z^c ∈ Q_k`. By Lemma 6.3 with `i > k`:

```
(★1)   x_i · (x_k · (x_j · z^c)) = x_k · (x_i · (x_j · z^c)) + [x_i, x_k] · (x_j · z^c)
```

Symmetrically, by Lemma 6.4 with `l := i` (`k ≤ i` ✓): `x_i · z^c ∈ Q_k`; by Lemma 6.3 with
`j > k`:

```
(★2)   x_j · (x_k · (x_i · z^c)) = x_k · (x_j · (x_i · z^c)) + [x_j, x_k] · (x_i · z^c)
```

Substituting:

```
x_i · (x_j · z^a) = x_k·(x_i·(x_j·z^c)) + [x_i,x_k]·(x_j·z^c) + x_i·([x_j,x_k]·z^c)
x_j · (x_i · z^a) = x_k·(x_j·(x_i·z^c)) + [x_j,x_k]·(x_i·z^c) + x_j·([x_i,x_k]·z^c)
```

#### Step 4: subtract and collect into three commutators

```
Δ := x_i·(x_j·z^a) − x_j·(x_i·z^a)
   = x_k · ( x_i·(x_j·z^c) − x_j·(x_i·z^c) )                        … (T0)
   + ( [x_i,x_k]·(x_j·z^c) − x_j·([x_i,x_k]·z^c) )                  … (T1)
   − ( [x_j,x_k]·(x_i·z^c) − x_i·([x_j,x_k]·z^c) )                  … (T2)
```

(Here (T0) used linearity of `p ↦ x_k · p`.) Each of (T0), (T1), (T2) is an instance of
(C_{m−1}) on `z^c ∈ P_{m−2}`, using (R1) for the bracketed arguments:

```
(T0):  pair (x_i, x_j)          ⟹   x_i·(x_j·z^c) − x_j·(x_i·z^c) = [x_i,x_j]·z^c
(T1):  pair ([x_i,x_k], x_j)    ⟹   (T1) = [[x_i,x_k], x_j] · z^c
(T2):  pair ([x_j,x_k], x_i)    ⟹   (T2) = [[x_j,x_k], x_i] · z^c
```

Hence

```
Δ = x_k · ( [x_i,x_j] · z^c ) + ( [[x_i,x_k], x_j] − [[x_j,x_k], x_i] ) · z^c.        (6.4.1)
```

#### Step 5: the Jacobi identity

**Lemma 6.5.** In any Lie algebra, for all `A, B, C`:
`[[A,C],B] − [[B,C],A] = [[A,B],C]`.

*Proof.* From the Leibniz/Jacobi axiom `[A,[B,C]] = [[A,B],C] + [B,[A,C]]` and antisymmetry one
gets the cyclic form

```
(J)   [[A,B],C] + [[B,C],A] + [[C,A],B] = 0
```

(rewrite `[A,[B,C]] = −[[B,C],A]` and `[B,[A,C]] = −[[A,C],B] = [[C,A],B]`). Then

```
[[A,C],B] − [[B,C],A] = −[[C,A],B] − [[B,C],A] = [[A,B],C]     by (J).
```

∎ **No division by 2 is used** — see §9.2 for why a naive route does divide by 2.

Applying Lemma 6.5 with `A = x_i`, `B = x_j`, `C = x_k`:

```
[[x_i,x_k], x_j] − [[x_j,x_k], x_i] = [[x_i,x_j], x_k].
```

Substituting into (6.4.1) and then comparing with **(E3)**:

```
Δ = x_k · ([x_i,x_j] · z^c) + [[x_i,x_j], x_k] · z^c
  = [x_i,x_j] · z^a                                     by (E3).
```

That is `D(x_i, x_j; z^a) = 0`. ∎

**Case 2 is closed.** Together with §6.2 and reductions (R1)–(R4), **(C_m) is proved**.

*(Cross-check against Booher, who writes the Jacobi step in the "right-bracket" convention:
`[x_k,[x_i,x_j]] + [x_i,[x_j,x_k]] − [x_j,[x_i,x_k]] = 0`. Negating each term turns this into
`[[x_i,x_j],x_k] + [[x_j,x_k],x_i] − [[x_i,x_k],x_j] = 0`, i.e. exactly Lemma 6.5. Swanson's
version is his displayed equation (*) followed by "applied `(C_m)` to collapse two terms into
`[x_λ,x_μ]` along with the Jacobi identity to collapse the other two terms". Same argument.)*

### 6.5 A concrete counterexample to the recursion as stated in the task

Take `I = {1 < 2 < 3}`, `K = ℚ`, and `L` with

```
[x_1, x_2] = x_1,     [x_2, x_3] = x_1,     [x_1, x_3] = 0.
```

(Jacobi holds: `[[x_1,x_2],x_3] + [[x_2,x_3],x_1] + [[x_3,x_1],x_2] = [x_1,x_3] + [x_1,x_1] + 0 = 0`;
triples with a repeated entry are automatic.)

Compute with the **correct** recursion:

| value | derivation | result |
|---|---|---|
| `x_2 · 1` | (A) | `z_2` |
| `x_3 · 1` | (A) | `z_3` |
| `x_2 · z_1` | (D2), `j=1`, `b=0`, `w=0`, `[x_2,x_1] = −x_1` | `z_1 z_2 − z_1` |
| `x_1 · z_2` | (A), `1 ≼ e_2` | `z_1 z_2` |
| `x_3 · z_2` | (D2), `j=2`, `b=0`, `w=0`, `[x_3,x_2] = −x_1` | `z_2 z_3 − z_1` |
| `x_2 · z_2` | (A) | `z_2²` |
| `x_2·(z_2 z_3)` | (A), `2 ≼ e_2+e_3` | `z_2² z_3` |

Now `a = 2e_2` (`z_2²`), `i = 3`: `j = 2`, `b = e_2`,
`w = x_3·z_2 − z_3 z_2 = −z_1`, and `x_2 · w = −(z_1 z_2 − z_1) = −z_1 z_2 + z_1`, whereas
`z_2 · w = −z_1 z_2`. **They differ.** Hence

```
correct:  x_3 · z_2²  = z_2² z_3 + (−z_1 z_2 + z_1) + [x_3,x_2]·z_2
                      = z_2² z_3 − z_1 z_2 + z_1 − z_1 z_2 = z_2² z_3 − 2 z_1 z_2 + z_1
task's:   x_3 · z_2²  = z_2·(z_2 z_3 − z_1) + [x_3,x_2]·z_2
                      = z_2² z_3 − z_1 z_2 − z_1 z_2      = z_2² z_3 − 2 z_1 z_2
```

Test (C) for the pair `(3,2)` on `z^{e_2} = z_2`:

```
x_3·(x_2·z_2) − x_2·(x_3·z_2)  =?  [x_3,x_2]·z_2 = −x_1·z_2 = −z_1 z_2.
x_2·(x_3·z_2) = x_2·(z_2 z_3) − x_2·z_1 = z_2² z_3 − (z_1 z_2 − z_1) = z_2² z_3 − z_1 z_2 + z_1.
```

* Correct value: `(z_2²z_3 − 2z_1z_2 + z_1) − (z_2²z_3 − z_1z_2 + z_1) = −z_1 z_2` ✓
* Task's value: `(z_2²z_3 − 2z_1z_2) − (z_2²z_3 − z_1z_2 + z_1) = −z_1 z_2 − z_1` ✗ (off by `−z_1`)

Machine-checked (§12): the task's recursion violates (C) in 20 of the instances with `|a| ≤ 3` on
this algebra; the correct recursion violates none up to degree 5.

**Why the discrepancy is invisible in small examples:** `x_j · w = z_j w` *does* hold whenever
every monomial `z^c` occurring in `w` satisfies `j ≼ c`. If `j = 1` this is automatic. So any
counterexample needs `n ≥ 3`, needs `[x_j, x_l] ≠ 0` for some `l < j` (to make `x_j · z^c ≠ z_j z^c`),
and needs `w ≠ 0`, i.e. `[x_i, x_j] ≠ 0`. The algebra above is the smallest such.

---

## 7. Uniqueness of `f_m`, and the limit

**Proposition 7.1 (uniqueness).** `f_m` is the unique bilinear map `L × P_m → P` satisfying
(A_m), (B_m), (C_m).

*Proof.* Let `g` be another. Restricting (A_m), (B_m), (C_m) to `P_{m−1}` yields exactly
(A_{m−1}), (B_{m−1}), (C_{m−1}) for `g|_{L × P_{m−1}}` — note (C_m) restricted to `|a| ≤ m − 2` is
(C_{m−1}), and the outer applications stay in `P_{m−1}` by Lemma 5.1 applied to `g`, which is
legitimate since `g` satisfies (B_m). By induction (uniqueness at stage `m−1`),
`g|_{L × P_{m−1}} = f_{m−1}`.

Now let `|a| = m`.

* If `i ≼ a`: (A_m) forces `g(x_i, z^a) = z_i z^a = f_m(x_i, z^a)`.
* If `¬(i ≼ a)`: with `j = min supp a`, `b = a − e_j`, we have `z^a = z_j z^b = g(x_j, z^b)` by
  (A_{m−1}) (`j ≼ b`, `|b| = m−1`). So (C_m) applied to the pair `(x_i, x_j)` at `z^b` (legal:
  `|b| = m − 1`) gives
  `g(x_i, z^a) = g(x_i, g(x_j, z^b)) = g(x_j, g(x_i, z^b)) + g([x_i,x_j], z^b)`.
  All arguments on the right lie in `P_{m−1}` except `g(x_i, z^b) ∈ P_m`; splitting
  `g(x_i, z^b) = z_i z^b + w` with `w ∈ P_{m−1}` (by (B_{m−1}), and `w` equals *our* `w` since
  `g = f_{m−1}` there) and using (A_m) on `z^{b+e_i}` exactly as in Lemma 3.1, we get
  `g(x_i, z^a) = z_i z^a + f_{m−1}(x_j, w) + f_{m−1}([x_i,x_j], z^b) = f_m(x_i, z^a)`.

Bilinearity finishes it. ∎

Base case of this induction: §4.

**Corollary 7.2 (Theorem 2.1).** The `f_m` are compatible, so they glue to a bilinear
`f : L × P → P`. It satisfies (A) and (B) directly. For (C): given `x, y ∈ L` and `f ∈ P`, pick
`m` with `f ∈ P_{m−1}`; then (C_m) plus (R1) gives `x·(y·f) − y·(x·f) = [x,y]·f`. Uniqueness: any
map satisfying (A),(B),(C) restricts to one satisfying (A_m),(B_m),(C_m) for every `m`, hence
equals `f_m` on `P_m` by Prop. 7.1. ∎

**Corollary 7.3.** `ρ : L → End_K(P)`, `ρ(x)(p) := x · p`, is a homomorphism of Lie algebras
`L → 𝔤𝔩(P)`, i.e. `ρ([x,y]) = ρ(x)ρ(y) − ρ(y)ρ(x)`. This is (C) verbatim. So `P` is an
`L`-module. ∎

---

## 8. Summary table of the induction (item 1, condensed)

| stage | assumed | constructed / proved | where |
|---|---|---|---|
| `m = 0` | — | `f_0` on `P_0`; (A_0) forced; (B_0) trivial; (C_0) vacuous | §4 |
| `m ≥ 1` | `Lem(m−1)`: `f_{m−1}` with (A_{m−1}),(B_{m−1}),(C_{m−1}) | **define** `f_m` on `P^{(m)}` by (D1)/(D2), extending `f_{m−1}` | §3 |
| | | (A_m): (D1) + (A_{m−1}) | §5 |
| | | (B_m): inspect (D2); needs (B_{m−1}) + Lemma 5.1 | §5 |
| | | (C_m) for `\|a\| ≤ m−2`: = (C_{m−1}) | (R4) |
| | | (C_m), `\|a\| = m−1`, `i = j`: `[x,x] = 0` | (R3) |
| | | (C_m), `\|a\| = m−1`, `i < j`: antisymmetry | (R3) |
| | | (C_m), `\|a\| = m−1`, `i > j`, `j ≼ a`: **by definition** | §6.2 |
| | | Lemma 6.3 (`(C)` for `(x_i, x_k)` on `Q_k`): §6.2 + (C_{m−1}) | §6.3 |
| | | (C_m), `\|a\| = m−1`, `i > j`, `¬(j ≼ a)`: pivot `k = min supp a`, Lemma 6.3 twice, (C_{m−1}) three times, Jacobi once | §6.4 |
| | | uniqueness | §7 |

**Dependency order inside stage `m` (important for Lean — do not permute):**
`(D1)/(D2)` → `(A_m)` → `(B_m)` → `Lemma 5.1` → `§6.2 (Case 1)` → `Lemma 6.3` → `§6.4 (Case 2)`.
In particular Case 1 must be available **before** Lemma 6.3, and Lemma 6.3 before Case 2.

---

## 9. Where (if anywhere) is `char K = 0` or "`K` is a field" used? (item 4)

**Answer: nowhere.** Here is the audit.

### 9.1 What the construction actually needs

| ingredient | needed? | comment |
|---|---|---|
| `K` commutative ring with `1` | **yes** | for `P = K[z_i]` and bilinearity |
| `L` free as a `K`-module | **yes** | to have `(x_i)` and to define `f_m` on a basis |
| index set `I` totally ordered | **yes** | to have `min supp a` |
| `[x, x] = 0` (alternating) | **yes** | (R3), diagonal case of (C) |
| Jacobi | **yes** | Lemma 6.5 only |
| `K` a field | **no** | only to guarantee `L` free |
| `char K = 0` | **no** | — |
| `K` has no `2`-torsion | **no** | — |
| `I` finite / `L` finite-dimensional | **no** | supports are finite; `P_m` filtration is exhaustive |
| `I` well-ordered | **no** | totality suffices (`supp a` is finite) |

There is **no division by any scalar** anywhere in §§3–7 or §10: every step is a rewriting by
bilinearity, an application of an induction hypothesis, or the Jacobi identity. The scalars that
appear are the structure constants `γ_{ijk} ∈ K`, always multiplied, never inverted.

### 9.2 The one place a careless proof divides by 2

If in §6.4 Step 5 you expand `[[A,C],B]` and `[[B,C],A]` using the *Leibniz* form
`[[X,Y],Z] = [X,[Y,Z]] − [Y,[X,Z]]` and then try to match `[[A,B],C] = −[C,[A,B]]`, you land on

```
[[A,C],B] − [[B,C],A] − [[A,B],C] = −2([A,[B,C]] + [B,[C,A]] + [C,[A,B]])
```

which is `0` by Jacobi but only *after* cancelling a factor `2` — i.e. you have proved
`2 · (goal) = 0`, useless over `ℤ/2`. **Lemma 6.5 as proved above avoids this**: derive the cyclic
form (J) first (a division-free rewrite), then use it once. In Lean, use `lie_jacobi`
(`⁅x,⁅y,z⁆⁆ + ⁅y,⁅z,x⁆⁆ + ⁅z,⁅x,y⁆⁆ = 0`) directly, **not** `lie_lie` twice.

### 9.3 Char 2: alternating vs. antisymmetric

(R3) uses `[x, x] = 0`. Over a ring where `2` is not invertible, `[x,y] = −[y,x]` does **not**
imply `[x,x] = 0`. Mathlib's `LieRing` axiom is `lie_self : ⁅x, x⁆ = 0`, the alternating one, so
this is a non-issue there; but if you ever axiomatize with antisymmetry only, the diagonal case
of (C) breaks in char 2. Flagging it because it is the single genuinely char-sensitive line.

### 9.4 Beyond free modules

If `L` is not free the construction has no starting point, and PBW can genuinely fail for Lie
algebras over commutative rings that are not free (nor flat/projective) as modules. For `L`
**projective** over a commutative `K`, PBW does still hold (Bourbaki I §2.7; the standard route is
to reduce to the free case by localizing at primes, since projective ⟹ locally free, and both
`U(L)` and `Sym(L)` commute with localization). **I have not verified that localization argument
in detail here** — flagged.

---

## 10. Consequences: the PBW basis (item 5)

### 10.1 The evaluation map

By Corollary 7.3, `ρ : L → 𝔤𝔩(P)` is a Lie algebra map. By the universal property of `U(L)` there
is a unique associative `K`-algebra homomorphism

```
ρ̃ : U(L) → End_K(P)      with   ρ̃ ∘ ι = ρ.
```

Define the `K`-linear map

```
ev : U(L) → P,        ev(u) := ρ̃(u)(1).
```

Two immediate properties:

* **(ev1)** `ev(1) = 1 = z^0`.
* **(ev2)** `ev(ι(x) · u) = ρ(x)(ρ̃(u)(1)) = x · ev(u)` for `x ∈ L`, `u ∈ U(L)`.

For `a ∈ Λ` (finite support) write the **ordered monomial**

```
X^a := ι(x_{i_1})^{a_{i_1}} ⋯ ι(x_{i_r})^{a_{i_r}} ∈ U(L),      i_1 < ⋯ < i_r  the support of a
```

(with `X^0 := 1`). Note `X^a = ι(x_j) · X^{a − e_j}` when `j = min supp a`.

### 10.2 Triangularity

**Proposition 10.1.** For every `a ∈ Λ`:  `ev(X^a) − z^a ∈ P_{|a| − 1}`.

*Proof.* Strong induction on `|a|`.

* `|a| = 0`: `ev(X^0) = ev(1) = 1 = z^0`, difference `0 ∈ P_{-1} = 0`. ✓
* `|a| ≥ 1`: let `j := min supp a`, `b := a − e_j`, so `|b| = |a| − 1`, `X^a = ι(x_j) X^b`, and
  `j ≼ b` (Lemma 1.2(4)). By (ev2) and the induction hypothesis `ev(X^b) = z^b + r`,
  `r ∈ P_{|b| − 1}`:

  ```
  ev(X^a) = x_j · ev(X^b) = x_j · z^b + x_j · r.
  ```
  Now `x_j · z^b = z_j z^b = z^a` by **(A)** (this is exactly where `j ≼ b` is used), and
  `x_j · r ∈ P_{|b|} = P_{|a| − 1}` by Lemma 5.1. ∎

*(Note the proof uses (A) and (B) only. It does **not** use (C) — (C) was used earlier, to know
that `ρ̃` exists at all.)*

### 10.3 Ordered monomials span `U(L)`

Let `U_m ⊆ U(L)` be the image of `⊕_{r ≤ m} L^{⊗ r}`, i.e. the span of products
`ι(y_1) ⋯ ι(y_r)` with `y_t ∈ L`, `r ≤ m`. Then `U_0 ⊆ U_1 ⊆ ⋯`, `⋃ U_m = U(L)`, and expanding
each `y_t` in the basis, `U_m = span_K { ι(x_{i_1}) ⋯ ι(x_{i_r}) : r ≤ m }`.

**Proposition 10.2.** `U_m = span_K { X^a : |a| ≤ m }`. Hence `{X^a : a ∈ Λ}` spans `U(L)`.

*Proof.* `⊇` is clear. For `⊆`, induct on `m`. `m = 0`: `U_0 = K·1 = K·X^0`. ✓

For `m ≥ 1`, it suffices to show `y := ι(x_{i_1}) ⋯ ι(x_{i_m}) ∈ span{X^a : |a| ≤ m}` for every
sequence `(i_1, …, i_m)` (shorter products are in `U_{m−1}`, done by the outer hypothesis). Do a
**second, inner induction on the inversion number**

```
inv(i_1, …, i_m) := #{ (p, q) : p < q,  i_p > i_q }.
```

* `inv = 0`: the sequence is nondecreasing, so `y = X^a` with `a = e_{i_1} + ⋯ + e_{i_m}`,
  `|a| = m`. ✓
* `inv > 0`: there is `p` with `i_p > i_{p+1}` (a nondecreasing sequence has `inv = 0`). In `U(L)`,
  `ι(x_{i_p}) ι(x_{i_{p+1}}) = ι(x_{i_{p+1}}) ι(x_{i_p}) + ι([x_{i_p}, x_{i_{p+1}}])`, so

  ```
  y = ι(x_{i_1})⋯ι(x_{i_{p+1}})ι(x_{i_p})⋯ι(x_{i_m})  +  ι(x_{i_1})⋯ι([x_{i_p},x_{i_{p+1}}])⋯ι(x_{i_m}).
  ```
  The first summand is the same product with `i_p, i_{p+1}` transposed, and transposing an
  *adjacent* inversion decreases `inv` by exactly `1`; inner induction applies. The second summand
  is a product of `m − 1` elements of `ι(L)`, hence lies in `U_{m−1}`, hence in
  `span{X^a : |a| ≤ m−1}` by the outer induction. ✓ ∎

*(This is Humphreys §17.3 Corollary C; Booher's Lemma 3; PlanetMath's "spanning" half.)*

### 10.4 Linear independence and the isomorphism

**Proposition 10.3.** `{ ev(X^a) : a ∈ Λ }` is `K`-linearly independent in `P`.

*Proof.* Suppose `Σ_{a ∈ F} c_a ev(X^a) = 0` with `F ⊆ Λ` finite and some `c_a ≠ 0`. Let
`m := max{ |a| : a ∈ F, c_a ≠ 0 }`. By Prop. 10.1, `ev(X^a) = z^a + r_a` with `r_a ∈ P_{|a|−1}`.
Hence

```
0 = Σ_{a ∈ F, c_a ≠ 0} c_a z^a  +  Σ_{a} c_a r_a.
```

Take the degree-`m` homogeneous component. Terms with `|a| < m` contribute nothing; the `r_a` lie
in `P_{|a|−1} ⊆ P_{m−1}` and contribute nothing. What remains is `Σ_{|a| = m} c_a z^a = 0`. Since
`(z^a)_{a ∈ Λ}` is a `K`-basis of `P`, `c_a = 0` for all `|a| = m` — contradicting the choice of
`m`. ∎

**Theorem 10.4 (PBW).**

1. `{ X^a : a ∈ Λ }` is a `K`-basis of `U(L)`.
2. `ev : U(L) → P` is a `K`-linear isomorphism, and `ev(X^a) = z^a + (\text{lower degree})`.
3. `ι : L → U(L)` is injective.
4. `U_m = span{X^a : |a| ≤ m}` is a filtration with `gr U(L) ≅ Sym(L)` as graded `K`-algebras.

*Proof.*

**(1)** Spanning is Prop. 10.2. Independence: if `Σ c_a X^a = 0` then applying the linear map `ev`
gives `Σ c_a ev(X^a) = 0`, so all `c_a = 0` by Prop. 10.3.

**(2)** `ev` maps the basis `{X^a}` to the linearly independent family `{ev(X^a)}`, hence is
injective. Surjective: show `z^a ∈ im(ev)` by strong induction on `|a|` — `z^a = ev(X^a) − r_a`
with `r_a ∈ P_{|a|−1} = span{z^c : |c| < |a|} ⊆ im(ev)` by induction. Since `{z^a}` spans `P`,
`ev` is onto. (Equivalently: `{ev(X^a)}` is a basis of `P`, being unitriangular with respect to
the degree filtration against the basis `{z^a}`.)

**(3)** Let `x = Σ_i c_i x_i ∈ L` with `ι(x) = 0`. Then
`0 = ev(ι(x)) = x · 1 = Σ_i c_i (x_i · z^0) = Σ_i c_i z_i` by **(A)** (`i ≼ 0` always). Since
`{z_i}` is part of a basis of `P`, all `c_i = 0`, so `x = 0`.
*(This step needs only (A) and the existence of `ρ̃` — not the full basis theorem. It is the
cheapest corollary and a good early Lean milestone.)*

**(4)** By (1) and Prop. 10.2, `{X^a : |a| ≤ m}` is a basis of `U_m` (it spans by 10.2 and is
independent by (1)), so `{X^a + U_{m−1} : |a| = m}` is a basis of `U_m / U_{m−1}`. `gr U(L)` is
commutative because `ι(x)ι(y) − ι(y)ι(x) = ι([x,y]) ∈ U_1` has degree drop `1`, so the canonical
map `Sym(L) → gr U(L)` (from the universal property of `Sym`, applied to `L ≅ U_1/U_0 ⊆ gr U(L)`)
is a surjective algebra map sending the monomial basis of `Sym^m(L)` to the basis
`{X^a + U_{m−1} : |a| = m}` of `gr^m U(L)`, hence is an isomorphism. ∎

*Remark 10.5.* `ev` is **not** an algebra map (`P` is commutative, `U(L)` generally is not). It is
a `K`-linear isomorphism `U(L) ≅ P ≅ Sym(L)`; the induced map on associated graded objects is the
canonical algebra isomorphism of (4). Over `char K = 0` one can upgrade `ev^{-1}` to the
symmetrization map, but that **does** need `1/m!` and is not needed for PBW.

---

## 11. Formalization skeleton for Lean 4 / Mathlib

Suggested types:

```lean
variable {K : Type*} [CommRing K]
variable {ι : Type*} [LinearOrder ι]
variable {L : Type*} [LieRing L] [LieAlgebra K L]
variable (b : Basis ι K L)

abbrev P := MvPolynomial ι K
abbrev Λ := ι →₀ ℕ
def preceq (i : ι) (a : Λ) : Prop := ∀ j ∈ a.support, i ≤ j
```

**§1: `preceq` API.** Lemma 1.2, seven lemmas, all `Finsupp.support` manipulation. Decidability of
`preceq` needs `DecidableEq ι` + `Finset` quantifier; use `Finset.min'` for `min supp`.

**§3: the recursion.** The subtlety: (D2) refers to `f_{m−1}(x_j, w)` where `w`'s degree bound is a
*theorem*, not definitional. Two clean options:

*Option A (recommended) — total function with junk, structural recursion on `m`.* Define

```lean
noncomputable def A : ℕ → ι → Λ → P K ι
| 0,     i, a => if a = 0 then X i else 0
| (m+1), i, a =>
    if a.degree ≤ m then A m i a
    else if a.degree ≠ m+1 then 0                      -- junk outside the stage
    else if preceq i a then X i * monomial a 1
    else
      let j := a.support.min' (by …);  let bb := a - single j 1
      X i * monomial a 1
        + lin (A m) (b.repr.symm (single j 1)) (A m i bb - X i * monomial bb 1)
        + lin (A m) ⁅b i, b j⁆ (monomial bb 1)
```

where `lin (A m) : L →ₗ[K] P →ₗ[K] P` is the bilinear extension of `A m` (via `Basis.constr` on
both slots). This is *structural* recursion on `m` — no well-founded machinery, no termination
proof obligations tangled with (B). Then prove, by induction on `m`, the conjunction

```
(A_m) ∧ (B_m) ∧ (C_m) ∧ (∀ a, a.degree ≤ m → A (m+1) i a = A m i a)
```

and finally set `act i a := A a.degree i a`.

*Option B — well-founded recursion on `a.degree`.* Cleaner to read but the recursive call
`lin act x_j w` needs `w`'s monomials to have degree `< |a|`, which is (B) — so the definition and
the proof of (B) become mutually recursive. Avoid unless you want to fight `WellFounded.fix` with
a `Subtype`-valued motive.

**Filtration.** `P_m := Submodule.span K {monomial a 1 | a.degree ≤ m}`. Mathlib has
`MvPolynomial.restrictTotalDegree` (a `Submodule` of polynomials of total degree `≤ m`) — check it
matches. You will want `MvPolynomial.homogeneousComponent` for §10.4's "take the degree-`m` part".

**Key lemma statements to have as named theorems (mirrors of this document):**

| doc | Lean name suggestion |
|---|---|
| Lemma 1.2 | `preceq_zero`, `preceq_iff_le_min`, `preceq_add_single`, … |
| Lemma 3.1 | `act_of_not_preceq'` (conceptual form) |
| Lemma 5.1 | `act_mem_filtration` |
| (R1) | `lie_comm_apply_bilinear` (`D` is bilinear in `(x,y)`) |
| (R3) | `D_self`, `D_swap` |
| §6.2 | `C_case_min` |
| Lemma 6.3 | `C_of_mem_Q` |
| Lemma 6.4 | `act_mem_Q` |
| Lemma 6.5 | `lie_lie_sub_lie_lie` (from `lie_jacobi`) |
| §6.4 | `C_case_general` |
| Prop 10.1 | `ev_orderedMonomial` |
| Prop 10.2 | `orderedMonomial_span` |
| Prop 10.3 | `ev_orderedMonomial_linearIndependent` |
| Thm 10.4(3) | `LieAlgebra.ι_injective` (may already exist in Mathlib as `UniversalEnvelopingAlgebra.ι_injective` under a field hypothesis) |

**Mathlib notes.**
* `UniversalEnvelopingAlgebra K L` and `UniversalEnvelopingAlgebra.ι` exist; the universal property
  is `UniversalEnvelopingAlgebra.lift`.
* Jacobi: use `lie_jacobi : ⁅x, ⁅y, z⁆⁆ + ⁅y, ⁅z, x⁆⁆ + ⁅z, ⁅x, y⁆⁆ = 0`, **not** two applications
  of `lie_lie` (§9.2).
* `LieRing` already gives `lie_self`, so (R3) is `simp [lie_self]`.
* For (R1), the map `L →ₗ[K] L →ₗ[K] P` is built by `LinearMap.mk₂`; vanishing on a basis pair is
  `Basis.ext₂`.

**Estimated shape:** §1 ≈ 60 lines; the recursion + (A),(B) ≈ 150 lines; (C) ≈ 250 lines (Case 2 is
the bulk: 5 rewriting steps, each a `rw`/`linear_combination` on a `Submodule` membership side
goal); §10 ≈ 200 lines.

---

## 12. Machine verification performed

I implemented the recursion over `ℚ` with exact arithmetic and checked (A), (B), (C) exhaustively
on all monomials and all index pairs, for these Lie algebras:

| Lie algebra | max degree | (A) fails | (B) fails | (C) fails |
|---|---|---|---|---|
| `sl₂` (basis `e < h < f`) | 5 | 0 | 0 | 0 |
| Heisenberg (`[x₂,x₃] = x₁`) | 5 | 0 | 0 | 0 |
| `[x₁,x₂] = x₁, [x₂,x₃] = x₁` | 5 | 0 | 0 | 0 |
| abelian, `n = 3` | 4 | 0 | 0 | 0 |
| 4-dim filiform `[x₁,x₂]=x₃, [x₁,x₃]=x₄` | 4 | 0 | 0 | 0 |

With the recursion **as stated in the task** (`z_j (x_i · z^b) + …`), on the third algebra: **20
violations of (C)** already among monomials of degree `≤ 3`, the first being `(i,j) = (2,3)`,
`a = e_2`, with defect `+z_1` (§6.5).

---

## 13. Explicit list of flags

1. **The recursion in the task statement is wrong** (§0, §6.5). Everything else in the task's
   framing — the shape of `Lem(m)`, the degree lag in (C_m), the identification of the hard case,
   and the guess that "`w` is handled by the induction hypothesis in degree `|a|`" — is correct.
2. **No strengthening of `Lem(m)` is required.** What *is* required is the auxiliary Lemma 6.3,
   proved *inside* the stage-`m` step after Case 1 and before Case 2. If you prefer a single
   monolithic statement, you may add to `Lem(m)` the clause
   *"(C'_m): `D(x_i, x_k; p) = 0` for all `i > k` and all `p ∈ P_{m−2} + span{z^d : |d| = m−1, k ≼ d}`"*,
   but it is strictly derivable from (A_m),(B_m),(C_m)-Case-1,(C_{m−1}) and adds nothing.
3. **Ordering of obligations inside stage `m` is not permutable** (§8, last row). Case 2 depends on
   Lemma 6.3 which depends on Case 1 which depends on the definition (D2). A Lean proof that
   attempts Case 2 before Case 1 will not close.
4. **Char / field**: confirmed not used (§9), with the two caveats: (a) `[x,x] = 0` must be the
   axiom (char 2); (b) the Jacobi step must be done via the cyclic identity, not two Leibniz
   rewrites (which introduces a factor 2).
5. **Not fully verified by me**: the extension of PBW from *free* to *projective* `L` over a
   commutative ring via localization (§9.4). Everything else above I checked line by line and, for
   the construction itself, machine-checked (§12).
6. **Source typos I corrected** (so you do not get confused reading them): Booher's page 2 has
   `f_p` for `f_n` and writes `f_n(x_k ⊗ f_n(x_j ⊗ z_J))` where `f_n(x_i ⊗ f_n(x_j ⊗ z_J))` is
   meant, and page 2 line "the second and third terms are in `P_{n−1}`" should read `P_n`;
   his final display drops a `+`. His displayed Jacobi relation is correct.

---

## Sources

* [Jeremy Booher, *PBW Theorem* (lecture notes, 2009)](https://people.clas.ufl.edu/jeremybooher/files/pbw.pdf)
  — the closest published transcription of Humphreys §17.4; source of the verbatim formula in §3.
* [J. P. Swanson, *§17: The PBW Theorem* (notes on Humphreys)](https://www.jpswanson.org/talks/2015_Humphreys_PBW.pdf)
  — Proposition 119; independent confirmation, with the `y = −w` sign convention.
* [K. Igusa, *Proof of PBW Theorem*, Brandeis Math 223a](https://people.brandeis.edu/~igusa/Math223aF11/Notes223a17b.pdf)
  — could not fetch (TLS certificate error); listed for completeness.
* [PlanetMath, *Poincaré–Birkhoff–Witt theorem*](https://planetmath.org/poincarebirkhoffwitttheorem)
  — the spanning half (§10.3) only.
* [P. Garrett, *Poincaré–Birkhoff–Witt theorem*](https://www-users.cse.umn.edu/~garrett/m/algebra/pbw.pdf)
  — Jacobson-style variant (induction on degree, then on "defect").
* [D. Grinberg, *PBW type results for inclusions of Lie algebras*](https://www.cip.ifi.lmu.de/~grinberg/algebra/pbw.pdf)
  — general-base-ring treatment, relevant to §9.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §17.4 (print).
* N. Jacobson, *Lie Algebras*, Ch. V §2; N. Bourbaki, *Groupes et algèbres de Lie* I §2.7;
  J. Dixmier, *Enveloping Algebras* 2.1.9 (print).
