# Lean blueprint: `adoCharZero` and `adoIwasawa`

Companion to [`ado-informal.md`](ado-informal.md). Section numbers `§n.m` refer
to that document.

Workspaces: `generated/adoCharZero/`, `generated/adoIwasawa/`.
Solver-owned files: `Submission.lean` and anything under `Submission/`.
Permitted axioms: `propext`, `Quot.sound`, `Classical.choice` only — so no
`sorry`, no `native_decide`, no added axioms. No `set_option` anywhere.

Both workspaces get an identical `Submission/Ado/` tree; `adoIwasawa`
additionally gets `Submission/Ado/Restricted/`. (Duplicating the tree is
required: comparator reads only `Submission.lean` and `Submission/**` of the
workspace being scored, and workspaces cannot import each other.)

## File layout

```
Submission.lean                         -- the final theorem, 5 lines
Submission/Helpers.lean                 -- re-exports
Submission/Ado/
  Basic.lean                            -- §0  reductions
  PBW/
    Defs.lean                           -- ordered monomials, the filtration
    SymAction.lean                      -- §1  the action on the polynomial ring
    Basis.lean                          -- §1  PBW theorem
    Corollaries.lean                    -- §1  ι injective, L ∩ J² = 0, dim U/Jᵏ
    Noetherian.lean                     -- §1  U(L) is Noetherian
  Nilradical.lean                       -- §2  nilRadical, characteristic-ness
  DerivedRadical.lean                   -- §2  [L,L] ∩ radical is nilpotent
  Birkhoff.lean                         -- §3  nilpotent case
  Extension.lean                        -- §4  the U(a)/Iᵐ machinery
  Solvable.lean                         -- §5  solvable case
  Casimir.lean                          -- §6  Casimir element
  Weyl.lean                             -- §6  complete reducibility
  Whitehead.lean                        -- §6  H¹(s, M) = 0
  Levi.lean                             -- §6  Levi decomposition
  CharZero.lean                         -- §6  Ado in char 0
  Restricted/                           -- adoIwasawa only
    Defs.lean                           -- §7  restricted Lie algebras
    Envelope.lean                       -- §7  u(g), restricted PBW
    PEnvelope.lean                      -- §7  finite-dimensional p-envelope
    CharP.lean                          -- §7  Ado-Iwasawa in char p
```

## Naming conventions

Everything lives in `namespace Submission.Ado`, so nothing can clash with a
future Mathlib `LieAlgebra.*`. Where a declaration is a plausible future Mathlib
contribution the name mirrors the Mathlib style it would have
(`LieAlgebra.nilRadical`, `UniversalEnvelopingAlgebra.pbwBasis`, …) with the
`Submission.Ado` prefix.

---

## §0 `Submission/Ado/Basic.lean`

```lean
namespace Submission.Ado

/-- A packaged finite-dimensional representation, matching the shape the
benchmark statement asks for. -/
structure FinRep (K L : Type u) [Field K] [LieRing L] [LieAlgebra K L] where
  carrier   : Type u
  [addCommGroup : AddCommGroup carrier]
  [module       : Module K carrier]
  [finite       : FiniteDimensional K carrier]
  hom       : L →ₗ⁅K⁆ Module.End K carrier

/-- `FinRep.sum`: the direct sum of two finite representations. -/
def FinRep.sum (V W : FinRep K L) : FinRep K L

theorem FinRep.ker_sum (V W : FinRep K L) :
    LieHom.ker (V.sum W).hom = LieHom.ker V.hom ⊓ LieHom.ker W.hom

/-- §0 the adjoint representation, whose kernel is the centre. -/
def adRep : FinRep K L                       -- needs `FiniteDimensional K L`

theorem ker_adRep : LieHom.ker (adRep (K := K) (L := L)) = LieAlgebra.center K L

/-- §0 Lemma 0.1. -/
theorem exists_injective_of_centre
    (V : FinRep K L) (h : LieHom.ker V.hom ⊓ LieAlgebra.center K L = ⊥) :
    ∃ W : FinRep K L, Function.Injective W.hom
```

Mathlib gives `LieAlgebra.center`, `LieHom.ker`, `LieModule.toEnd`, and
`LieAlgebra.ad`; `ker_adRep` is `LieAlgebra.ker_ad_eq_center` if it exists,
otherwise a three-line unfolding.

The final `Submission.lean` is then

```lean
theorem adoCharZero [CharZero K] [FiniteDimensional K L] :
    ∃ (V : Type u) (_ : AddCommGroup V) (_ : Module K V) (_ : FiniteDimensional K V)
      (ρ : L →ₗ⁅K⁆ Module.End K V), Function.Injective ρ := by
  obtain ⟨W, hW⟩ := Submission.Ado.ado_charZero (K := K) (L := L)
  exact ⟨W.carrier, W.addCommGroup, W.module, W.finite, W.hom, hW⟩
```

**Size estimate: 150 lines. No dependencies beyond Mathlib. Do this first — it
compiles immediately and pins down the interface.**

---

## §1 PBW — `Submission/Ado/PBW/`

This is the single biggest missing brick. Mathlib has
`UniversalEnvelopingAlgebra R L` with `ι`, `lift`, `hom_ext` and nothing else;
`Mathlib/Algebra/Lie/Free.lean:36` and
`Mathlib/Algebra/Lie/SerreConstruction.lean:46` both record that PBW is absent.

### `PBW/Defs.lean`

```lean
variable (R L : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]
variable {n : ℕ} (b : Basis (Fin n) R L)

/-- Nondecreasing index words: the index set of the PBW basis. -/
def Word (n : ℕ) : Type := {l : List (Fin n) // l.Sorted (· ≤ ·)}

/-- The standard monomial `x_{i₁} ⋯ x_{i_m}` in `U(L)`. -/
noncomputable def stdMonomial (w : Word n) : UniversalEnvelopingAlgebra R L

/-- Augmentation ideal: the two-sided ideal generated by `ι '' L`. -/
def augIdeal : TwoSidedIdeal (UniversalEnvelopingAlgebra R L)
```

`Word n` is `List (Fin n)` cut down by `Sorted`; a `DecidableEq`/`Fintype`
instance for `{w : Word n // w.1.length ≤ m}` is what makes `U/Jᵐ` finite.

### `PBW/SymAction.lean` — the heart

Target space `S := MvPolynomial (Fin n) R`, with `S_{≤m}` the span of monomials
of total degree `≤ m` (`MvPolynomial.totalDegree`; Mathlib has
`MvPolynomial.restrictTotalDegree` as a submodule).

The recursion of §1 is best set up in Lean as a **well-founded recursion on
`(|A|, i)` lexicographically**, defining a family

```lean
private noncomputable def act : Fin n → Word n → S
```

with the three properties as separate lemmas:

```lean
theorem act_of_le  (i : Fin n) (w : Word n) (h : ∀ j ∈ w.1, i ≤ j) :
    act b i w = (X i) * monomialOf w
theorem act_sub_lt (i : Fin n) (w : Word n) :
    act b i w - (X i) * monomialOf w ∈ restrictTotalDegree (Fin n) R w.1.length
theorem act_comm (i j : Fin n) (w : Word n) :
    actLin b i (actLin b j (monomialOf w)) - actLin b j (actLin b i (monomialOf w))
      = actLin' b ⁅b i, b j⁆ (monomialOf w)
```

`act_comm` is the only hard proof; the case split is

* `i = j` — trivial;
* `i ≤ w` and `j ≤ w` — both sides reduce by `act_of_le` and a Jacobi-free
  computation;
* WLOG `j < i`, `j ≤ w`, `w = j ::ᵥ w'` — this is the *defining* case of the
  recursion, so it holds by `rfl`-style unfolding;
* the general case reduces to the previous one, and this is where the Jacobi
  identity is used exactly once.

Then

```lean
noncomputable def symAction : L →ₗ⁅R⁆ Module.End R S      -- by `Basis.constr` + act_comm
noncomputable def symLift : UniversalEnvelopingAlgebra R L →ₐ[R] Module.End R S
  := UniversalEnvelopingAlgebra.lift R symAction
```

**This file is the risk concentration of the entire project.** Budget it as
its own milestone; ~800–1200 lines, with the well-founded recursion and the
`act_comm` case analysis taking most of it.

### `PBW/Basis.lean`

```lean
theorem stdMonomial_span : Submodule.span R (Set.range (stdMonomial R b)) = ⊤
theorem stdMonomial_linearIndependent : LinearIndependent R (stdMonomial R b)
noncomputable def pbwBasis : Basis (Word n) R (UniversalEnvelopingAlgebra R L)
```

Spanning is a straightforward induction on the length of an arbitrary word,
using `ι x * ι y = ι y * ι x + ι ⁅x,y⁆` to bubble-sort; the induction measure is
the number of inversions. Independence is `symLift` applied to `1 : S` plus a
triangularity argument on total degree.

### `PBW/Corollaries.lean`

```lean
theorem ι_injective : Function.Injective (UniversalEnvelopingAlgebra.ι R : L → _)
theorem mem_augIdeal_pow_iff (m : ℕ) (u) :
    u ∈ (augIdeal R L) ^ m ↔ u ∈ span R {stdMonomial w | m ≤ w.1.length}
theorem ι_inter_augIdeal_sq : ∀ x : L, ι R x ∈ (augIdeal R L)^2 → x = 0
noncomputable def quotBasis (m : ℕ) :
    Basis {w : Word n // w.1.length < m} R (U ⧸ (augIdeal R L)^m)
instance finiteDimensional_quot (m : ℕ) :
    FiniteDimensional R (U ⧸ (augIdeal R L)^m)
```

### `PBW/Noetherian.lean`

```lean
instance : IsNoetherianRing (UniversalEnvelopingAlgebra K L)
```

via the filtration and `gr U ≃ MvPolynomial`. **Optional** — Lemma 4.3 has an
alternative Cayley–Hamilton proof that avoids it. Skip on the first pass.

**Size estimate for `PBW/`: 2000–2600 lines.**

---

## §2 Structure theory

### `Nilradical.lean`

```lean
/-- Iterated brackets of an ideal land in the lower central series. -/
theorem lcs_bracket_le (I : LieIdeal R L) (p q : ℕ) :
    ⁅lowerCentralSeries R I I p, lowerCentralSeries R I I q⁆ ≤ … (p + q)

/-- Sum of two nilpotent ideals is nilpotent — §2.1. -/
theorem isNilpotent_sup (I J : LieIdeal K L)
    [LieAlgebra.IsNilpotent I] [LieAlgebra.IsNilpotent J] :
    LieAlgebra.IsNilpotent ↥(I ⊔ J)

/-- The nilradical: the `sSup` of all nilpotent ideals. -/
def nilRadical : LieIdeal K L := sSup {I : LieIdeal K L | LieAlgebra.IsNilpotent I}

instance nilRadicalIsNilpotent [FiniteDimensional K L] :
    LieAlgebra.IsNilpotent (nilRadical K L)
theorem le_nilRadical {I} (h : LieAlgebra.IsNilpotent I) : I ≤ nilRadical K L
theorem center_le_nilRadical : LieAlgebra.center K L ≤ nilRadical K L
theorem nilRadical_le_radical : nilRadical K L ≤ LieAlgebra.radical K L
/-- Characteristic: stable under every derivation. §2.1 -/
theorem map_nilRadical_le (D : LieDerivation K L L) :
    (nilRadical K L).map … ≤ nilRadical K L
```

Mathlib's `LieAlgebra.radical` (`Mathlib/Algebra/Lie/Solvable.lean:363`) and its
`radicalIsSolvable` instance are the exact template for the `sSup` pattern, and
`Mathlib/Algebra/Lie/Nilpotent.lean:308` (`instIsNilpotentSup`) is the template
for `isNilpotent_sup` — but note that Mathlib's lemma is about
`LieModule.IsNilpotent L (M₁ ⊔ M₂)` (module nilpotency), which is *strictly
stronger* than what the nilradical needs (`LieAlgebra.IsNilpotent ↥(I ⊔ J)`), so
it cannot be reused directly. The counterexample keeping the two apart: for the
two-dimensional non-abelian `⟨H, x⟩` with `⁅H,x⁆ = x`, `I = K·x` is an abelian
(hence nilpotent) ideal but `⁅L, I⁆ = I`, so `I` is not module-nilpotent.

**Size: 400–600 lines.**

### `DerivedRadical.lean` — §2.2, §2.3

```lean
theorem isNilpotent_derived_inf_radical [CharZero K] [FiniteDimensional K L] :
    LieAlgebra.IsNilpotent ↥(⁅(⊤ : LieIdeal K L), ⊤⁆ ⊓ LieAlgebra.radical K L)
theorem derived_inf_radical_le_nilRadical [CharZero K] [FiniteDimensional K L] :
    ⁅(⊤ : LieIdeal K L), ⊤⁆ ⊓ LieAlgebra.radical K L ≤ nilRadical K L
theorem derivation_radical_le_nilRadical [CharZero K] [FiniteDimensional K L]
    (D : LieDerivation K L L) :
    ∀ x ∈ LieAlgebra.radical K L, D x ∈ nilRadical K L
```

Ingredients already in Mathlib: `LieAlgebra.LieModule.exists_forall_lie_eq_smul`
/ Lie's theorem in `Mathlib/Algebra/Lie/LieTheorem.lean`, Engel in
`Mathlib/Algebra/Lie/Engel.lean`, and `LieAlgebra.isSolvable_of_…` /
Cartan's criterion in `Mathlib/Algebra/Lie/CartanCriterion.lean`. The proof of
§2.2 needs a base change to the algebraic closure (`Mathlib/Algebra/Lie/BaseChange.lean`)
to apply Lie's theorem, then descends.

**Size: 400–600 lines.**

---

## §3 `Birkhoff.lean`

```lean
theorem exists_faithful_nilpotent_of_isNilpotent
    [FiniteDimensional K N] [LieAlgebra.IsNilpotent N] :
    ∃ (V : FinRep K N) (m : ℕ), Function.Injective V.hom ∧
      ∀ x : N, (V.hom x) ^ m = 0
```

Direct from `PBW/Corollaries.lean`: take `V = U(N) ⧸ (augIdeal)^(max (c+1) 2)`
with `N` acting by left multiplication. **Size: 150 lines.**

---

## §4 `Extension.lean`

The reusable engine. Stated over an arbitrary field.

```lean
variable (A : Type u) [LieRing A] [LieAlgebra K A] (N : LieIdeal K A)
variable (ρ₀ : FinRep K A) (hρ₀ : Function.Injective ρ₀.hom)
variable (hN : ∀ x ∈ N, IsNilpotent (ρ₀.hom x))

/-- `π : U(A) →ₐ End V₀`, `q = ker π`, `I = q + ⟨N⟩`. -/
noncomputable def envIdeal : TwoSidedIdeal (UniversalEnvelopingAlgebra K A)

theorem exists_pow_envIdeal_le_ker : ∃ N₀, (envIdeal …) ^ N₀ ≤ ker π       -- 4.2
instance finiteDimensional_quot_envIdeal (m : ℕ) :
    FiniteDimensional K (U ⧸ (envIdeal …) ^ m)                              -- 4.3

/-- Unique extension of a Lie derivation of `A` to an algebra derivation of `U(A)`. -/
noncomputable def envDerivation (D : LieDerivation K A A) :
    Derivation K (UniversalEnvelopingAlgebra K A) (UniversalEnvelopingAlgebra K A)

theorem envDerivation_mem (D) (hD : ∀ a, D a ∈ N) (u) : envDerivation D u ∈ envIdeal -- 4.4
theorem envDerivation_pow_le (D) (hD) (m) :
    (envIdeal)^m ≤ Submodule.comap (envDerivation D) ((envIdeal)^m)          -- 4.4

/-- The key algebraic identity `[D̃, L_a] = L_{D̃ a}`. -/
theorem commutator_derivation_mulLeft (D : Derivation K A' A') (a : A') :
    ⁅(D : Module.End K A'), LinearMap.mulLeft K a⁆ = LinearMap.mulLeft K (D a)

/-- §4.5. -/
noncomputable def extend (D : LieDerivation K A A) (hD) (m) (hm) :
    (A ⋉ K∙D) →ₗ⁅K⁆ Module.End K (U ⧸ (envIdeal)^m)
theorem extend_injective_on … ; theorem extend_nilpotent_on_N …
```

`commutator_derivation_mulLeft` is a two-line `ext`/`simp` proof and is the
single most reused fact in the development. `envDerivation` is built with
`UniversalEnvelopingAlgebra.lift` applied to the Lie morphism
`A → U(A) ⋊ U(A)` (square-zero extension), which is how one gets the Leibniz
rule for free rather than by induction on monomials.

**Size: 700–900 lines.**

---

## §5 `Solvable.lean`

```lean
theorem exists_faithful_nilpotent_on_nilRadical_of_isSolvable
    [CharZero K] [FiniteDimensional K R'] [LieAlgebra.IsSolvable R'] :
    ∃ V : FinRep K R', Function.Injective V.hom ∧
      ∀ x ∈ nilRadical K R', IsNilpotent (V.hom x)
```

Strong induction on `finrank K R' - finrank K (nilRadical K R')`, following §5
verbatim. The two fiddly Lean points:

* the codimension-one ideal `𝔞` is obtained from
  `Submodule.exists_le_of_finrank_lt` applied to `nilRadical ≤ 𝔞 ⊊ R'` — it is
  an ideal because `⁅R',R'⁆ ≤ nilRadical` (`DerivedRadical.lean`);
* `nilRadical K 𝔞 = nilRadical K R'` needs "characteristic ideal of an ideal is
  an ideal", i.e. `map_nilRadical_le` from `Nilradical.lean`.

**Size: 400–500 lines.**

---

## §6 char 0: `Casimir.lean` → `Weyl.lean` → `Whitehead.lean` → `Levi.lean` → `CharZero.lean`

This is the largest remaining block and is essentially "the standard structure
theory of semisimple Lie algebras that Mathlib stops just short of".

```lean
-- Casimir.lean
noncomputable def casimir (ρ : L →ₗ⁅K⁆ Module.End K V) : Module.End K V
theorem casimir_comm (x : L) : ⁅ρ x, casimir ρ⁆ = 0
theorem trace_casimir (h : Function.Injective ρ) :
    LinearMap.trace K V (casimir ρ) = (finrank K L : K)

-- Weyl.lean
theorem isSemisimpleModule_of_isSemisimple [LieAlgebra.IsSemisimple K L]
    [FiniteDimensional K V] : IsSemisimpleModule (UniversalEnvelopingAlgebra K L) V

-- Whitehead.lean
theorem whitehead_one [LieAlgebra.IsSemisimple K L] [FiniteDimensional K M]
    (c : LieModule.Cohomology.oneCochain K L M)
    (hc : isCocycle c) : ∃ m : M, c = d₀ m

-- Levi.lean
theorem exists_levi [CharZero K] [FiniteDimensional K L] :
    ∃ S : LieSubalgebra K L, LieAlgebra.IsSemisimple S ∧
      IsCompl (S.toSubmodule) ((LieAlgebra.radical K L).toSubmodule)
```

Mathlib supplies `LieAlgebra.IsSemisimple`, `killingForm`,
`LieAlgebra.IsKilling`, `InvariantForm.isSemisimple_of_nondegenerate` and the
low-degree cochain scaffolding in `Mathlib/Algebra/Lie/Cochain.lean`
(`oneCochain`, `twoCochain`, `d₁₂`, `twoCocycle`) — but its own `TODO` says
coboundaries and cohomology are not there, so `whitehead_one` has to define the
`H¹ = 0` statement itself.

Levi's proof: induct on `finrank (radical)`; reduce to `radical` abelian and
minimal; then complements correspond to `H¹(L/rad, rad)`, killed by
`whitehead_one`.

`CharZero.lean` then assembles §6.2 in ~200 lines.

**Size: 2500–3500 lines. This is the second risk concentration.**

---

## §7 char p: `Restricted/` (needed only for `adoIwasawa`)

```lean
-- Defs.lean
class IsRestricted (K L) [Field K] [CharP K p] [LieRing L] [LieAlgebra K L] where
  pow : L → L
  pow_smul : ∀ (a : K) x, pow (a • x) = a ^ p • pow x
  ad_pow : ∀ x, LieAlgebra.ad K L (pow x) = (LieAlgebra.ad K L x) ^ p
  pow_add : ∀ x y, pow (x + y) = pow x + pow y + jacobsonSum x y

instance : IsRestricted K (Module.End K V)      -- the model example, `pow A = A ^ p`

-- Envelope.lean
def restrictedEnvelope : Type _ :=
  UniversalEnvelopingAlgebra K L ⧸ TwoSidedIdeal.span {ι x ^ p - ι (pow x) | x}
theorem central_pow_sub (x : L) : ι x ^ p - ι (pow x) ∈ Subring.center _
noncomputable def restrictedBasis (b : Basis (Fin n) K L) :
    Basis (Fin n → Fin p) K (restrictedEnvelope K L)
theorem finrank_restrictedEnvelope : finrank K (restrictedEnvelope K L) = p ^ n
theorem ι_restricted_injective : Function.Injective (ι' : L → restrictedEnvelope K L)

-- PEnvelope.lean
theorem exists_finite_pEnvelope [FiniteDimensional K L] :
    ∃ (Ĝ : Type u) (_ : LieRing Ĝ) (_ : LieAlgebra K Ĝ) (_ : FiniteDimensional K Ĝ)
      (_ : IsRestricted K Ĝ) (f : L →ₗ⁅K⁆ Ĝ), Function.Injective f

-- CharP.lean
theorem ado_charP (p) [Fact p.Prime] [CharP K p] [FiniteDimensional K L] :
    ∃ V : FinRep K L, Function.Injective V.hom
```

`central_pow_sub` is the one genuinely non-formal step: `ad(ιx ^ p) = (ad ιx)^p`
in `U(L)` because `ad` is a derivation and `char = p` makes the binomial
coefficients vanish — this is Jacobson's formula and Mathlib does *not* have it
(`Mathlib/Algebra/Lie/…` has no `p`-map at all). Expect ~300 lines for it alone.
Given PBW, `restrictedBasis` is then a `MvPolynomial`-style quotient argument:
`U(L)` is free over the central subalgebra `K[z₁,…,z_n]`, `z_i = ι x_i ^ p − ι(pow x_i)`.

`exists_finite_pEnvelope` follows Strade–Farnsteiner Thm 2.5.8: put
`H = ` the `p`-closure of `ad L` inside `Module.End K L` (finite-dimensional
because it sits in `End K L`), and build `Ĝ` as the pullback of `L ↠ ad L ↪ H`.

**Size: 1200–1600 lines.**

---

## Total and ordering

| milestone | lines | unlocks |
| --- | --- | --- |
| §0 `Basic.lean` | 150 | interface, compiles day one |
| §1 `PBW/` | 2000–2600 | §3, §4, §7 |
| §7 `Restricted/` | 1200–1600 | **char p half of `adoIwasawa`** |
| §2 `Nilradical`, `DerivedRadical` | 800–1200 | §5, §6 |
| §3 `Birkhoff` | 150 | §5 base case |
| §4 `Extension` | 700–900 | §5, §6 |
| §5 `Solvable` | 400–500 | §6 |
| §6 `Casimir`→`Levi`→`CharZero` | 2500–3500 | `adoCharZero` |
| **total** | **≈ 8000–10500** | |

Build order rationale: §0 first (cheap, fixes the interface); then §1, because
everything downstream is blocked on it and it is where the schedule risk is;
then §7, because it is the only self-contained *complete* result available
early (it finishes the characteristic-`p` half of `adoIwasawa` given only PBW);
then the char-0 chain §2 → §3 → §4 → §5 → §6.

Neither problem is finished until §6 lands, since `adoIwasawa` quantifies over
all fields and so subsumes `adoCharZero`.

## Verification protocol

* `lake build Submission` after every file; treat any warning as an error
  (`AGENTS.md`: "Do not leave linter warnings behind in edited files").
* `#print axioms Submission.adoCharZero` must print exactly
  `propext, Quot.sound, Classical.choice`.
* `lake exe lean-eval validate-submission --file generated/adoCharZero/Submission.lean`
  before submitting.
* `lake test` in the workspace once `landrun`/`lean4export`/`comparator`/`nanoda`
  are installed (see `SECURITY.md` for the pinned commits).
