# Mathlib audit for Ado's theorem (rev `905b95818e`, Lean v4.32.2)

Exhaustive source-level audit. This supersedes the guesses in
[`ado-blueprint.md`](ado-blueprint.md).

## Absent — must be built

| item | evidence |
| --- | --- |
| Poincaré–Birkhoff–Witt | `Mathlib/Algebra/Lie/UniversalEnveloping.lean` is 153 lines and contains only `Rel`, `ringCon`, `UniversalEnvelopingAlgebra`, `mkAlgHom`, `ι`, `lift`, `lift_symm_apply`, `ι_comp_lift`, `lift_ι_apply`, `lift_ι_apply'`, `lift_unique`, `hom_ext`. Nothing else. |
| `ι` injective, UEA basis/filtration/Noetherian | absent |
| Casimir element | `grep -rn "asimir"` over the whole package: **zero hits** |
| Weyl complete reducibility | `grep -rn "IsSemisimpleModule"` in `Algebra/Lie/`: **zero hits**. No bridge from Lie modules to `IsSemisimpleModule`, no "every `LieSubmodule` has a complement" |
| Whitehead's lemmas | `grep -rni "whitehead"` in `Algebra/Lie/`: zero hits. `Cochain.lean` defines cochains, `d₁₂`, `d₂₃`, `twoCocycle` — but **no cohomology group, no coboundaries** (its own TODO says so) |
| Levi decomposition | `grep -rn "Levi"` over all of Mathlib: only author names and Beppo Levi / Hopkins–Levitzki |
| derivation of a **noncommutative** algebra | `Derivation R A M` requires `[CommSemiring A]` — confirmed. Cannot even *state* "derivation of `U(L)`". Must roll our own (we do: `IsDeriv` in `DerivRep.lean`) |

Decisive: Mathlib's own registry `docs/1000.yaml:2122` lists
`Q2270905: Poincaré–Birkhoff–Witt theorem` **with no `decl:` field**, and
`Q2028341: Ado's theorem` likewise at line 1974. Mathlib records both as
unformalized.

## The nilradical trap

`LieAlgebra.maxNilpotentIdeal` **does** exist (`Algebra/Lie/Nilpotent.lean:958`),
with `center_le_maxNilpotentIdeal`, `maxNilpotentIdeal_le_radical`,
`LieIdeal.isNilpotent_iff_le_maxNilpotentIdeal`. **But it is the wrong notion**:
it is the `sSup` of ideals `I` with `LieModule.IsNilpotent L I` (nilpotent as an
`L`-module), not `LieRing.IsNilpotent ↥I` (nilpotent as a Lie algebra).

Concretely, for `L = ⟨H, x⟩` with `⁅H,x⁆ = x`: the classical nilradical is
`K∙x`, but `⁅L, K∙x⁆ = K∙x ≠ ⊥`, so `K∙x` is not module-nilpotent and
`maxNilpotentIdeal K L = ⊥`. Ado's proof needs the classical (Lie-algebra)
nilradical, because §5 requires `⁅𝔯, 𝔯⁆ ≤ nil 𝔯`, and `⁅𝔯,𝔯⁆` is module-nilpotent
only when `𝔯` is already nilpotent. So `nilRadical` must be built.

One direction of the bridge does exist (`Nilpotent.lean:919`):
`[LieModule.IsNilpotent L I] → LieRing.IsNilpotent ↥I`. The converse does not.

## Present and usable

* **Engel** — `LieAlgebra.isNilpotent_iff_forall [IsNoetherian R L] :
  LieRing.IsNilpotent L ↔ ∀ x, IsNilpotent (LieAlgebra.ad R L x)`
  (`Engel.lean:275`); also `LieModule.isNilpotent_iff_forall'` at `:270`.
  Hypotheses are weak: **no field, no char 0, no algebraic closure**, just
  Noetherian.
* **Lie's theorem** — `LieModule.exists_nontrivial_weightSpace_of_isSolvable`
  (`LieTheorem.lean:240`), needing `[Field k] [CharZero k] [IsSolvable L]`
  `[Module.Finite k V] [Nontrivial V] [LieModule.IsTriangularizable k L V]`.
  Algebraic closure is **not** required — it is replaced by
  `IsTriangularizable`.
* **Cartan's criteria** — `isSolvable_of_killingForm_apply_lie_eq_zero`
  (`CartanCriterion.lean:235`), `LieIdeal.isSolvable_of_killingForm_apply_lie_eq_zero`
  (`:207`), `HasTrivialRadical.instIsKilling` (`:258`),
  `hasTrivialRadical_iff_isKilling` (`:261`),
  `isNilpotent_derivedSeries_of_traceForm_eq_zero` (`:176`).
* **`LieDerivation`** (`Algebra/Lie/Derivation/Basic.lean`) — full API:
  `instLieRing`/`instLieAlgebra` on `LieDerivation R L L`,
  `commutator_apply`, `toLinearMapLieHom` (injective),
  `instNoetherian`. Plus `LieDerivation.ad : L →ₗ⁅R⁆ LieDerivation R L L`,
  `ad_ker_eq_center`, `lie_der_ad_eq_ad_der : ⁅D, ad R L x⁆ = ad R L (D x)`
  (`AdjointAction/Derivation.lean`).
* **`LieAlgebra.SemiDirectSum`** (`SemiDirect.lean`, notation `K ⋊⁅ψ⁆ L` for
  `ψ : L →ₗ⁅R⁆ LieDerivation R K K`) with `inl`, `inr`, `projr`, `projl`,
  `inl_injective`, `projr_surjective`, and an `IsExtension` instance. **This is
  exactly the `𝔞 ⋊ 𝔡` of §4** and should be used rather than hand-rolled.
* **`LieAlgebra.radical`**, `radicalIsSolvable`, `LieIdeal.solvable_iff_le_radical`,
  `center_le_radical`, `abelian_radical_of_hasTrivialRadical`.
* `Submodule.fg_iSup` (`Finiteness/Basic.lean:55`), `Submodule.FG.pow`
  (`Finiteness/Subalgebra.lean:57`), `Submodule.iSup_mul` / `Submodule.mul_iSup`
  (`Algebra/Algebra/Operations.lean:297,300` — **not** in the Finiteness files).

## Consequences for the plan

1. `Nilradical.lean` is genuinely required; `maxNilpotentIdeal` cannot be
   substituted.
2. §4's `𝔞 ⋊ 𝔡` should be `LieAlgebra.SemiDirectSum` with
   `ψ = LieDerivation.ad`, not a hand-rolled product.
3. Engel is available with weak hypotheses, which makes `DerivedRadical.lean`'s
   final step cheap once nilpotency of `ad` is established.
4. Nothing upstream can be ported for PBW/Casimir/Weyl/Whitehead/Levi; all five
   are original work.
