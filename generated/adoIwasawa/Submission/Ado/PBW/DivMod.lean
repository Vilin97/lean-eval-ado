import Submission.Ado.PBW.Defs

/-!
# Division with remainder on exponent vectors

Fix a modulus `q : ℕ`. Dividing with remainder in each coordinate splits an
exponent vector `a : Mon n = Fin n →₀ ℕ` as

```
a = b + q • m,      b j < q for every j,
```

and the pair `(b, m)` is uniquely determined by `a`. This file proves that,
in the form of an explicit bijection

```
monDivModEquiv q : Mon n ≃ {b : Mon n // IsRestricted q b} × Mon n
```

together with the injectivity and surjectivity of the reassembly map
`monAdd q (b, m) = b + q • m` as standalone statements, which is the form the
unitriangularity machinery of `Submission/Ado/PBW/Unitriangular.lean` consumes.

The modulus is required to be positive (`0 < q`) exactly where it is needed;
`monMod_add_smul_monDiv` holds for every `q`, since `Nat.mod_add_div` does.

Finally `finite_isRestricted` records that there are only finitely many
restricted exponent vectors — each of the `n` coordinates takes one of `q`
values — which is what makes the representation built downstream
finite-dimensional.
-/

namespace Submission.Ado.PBW

variable {n : ℕ}

/-- The scalar multiple `q • m` of an exponent vector acts componentwise. -/
theorem smul_mon_apply (q : ℕ) (m : Mon n) (j : Fin n) : (q • m) j = q * m j := by
  rw [Finsupp.smul_apply, smul_eq_mul]

/-- The componentwise remainder of an exponent vector on division by `q`. -/
noncomputable def monMod (q : ℕ) (a : Mon n) : Mon n :=
  Finsupp.mapRange (fun k => k % q) (by simp) a

/-- The componentwise quotient of an exponent vector on division by `q`. -/
noncomputable def monDiv (q : ℕ) (a : Mon n) : Mon n :=
  Finsupp.mapRange (fun k => k / q) (by simp) a

/-- An exponent vector is *restricted* when every one of its exponents is `< q`. -/
def IsRestricted (q : ℕ) (b : Mon n) : Prop := ∀ j, b j < q

/-- The remainder is computed componentwise. -/
@[simp]
theorem monMod_apply (q : ℕ) (a : Mon n) (j : Fin n) : monMod q a j = a j % q :=
  Finsupp.mapRange_apply

/-- The quotient is computed componentwise. -/
@[simp]
theorem monDiv_apply (q : ℕ) (a : Mon n) (j : Fin n) : monDiv q a j = a j / q :=
  Finsupp.mapRange_apply

/-- The remainder of an exponent vector is restricted. -/
theorem isRestricted_monMod {q : ℕ} (hq : 0 < q) (a : Mon n) : IsRestricted q (monMod q a) :=
  fun j => by rw [monMod_apply]; exact Nat.mod_lt _ hq

/-- The zero exponent vector is restricted, for any positive modulus. -/
theorem isRestricted_zero {q : ℕ} (hq : 0 < q) : IsRestricted q (0 : Mon n) := by
  intro j
  simpa using hq

/-- The exponent vector of a single variable is restricted as soon as `2 ≤ q`. -/
theorem isRestricted_e {q : ℕ} (hq : 2 ≤ q) (i : Fin n) : IsRestricted q (e i) := by
  intro j
  rw [e, Finsupp.single_apply]
  split <;> omega

/-- Division with remainder, componentwise: `a` is recovered from its remainder
and its quotient. -/
theorem monMod_add_smul_monDiv (q : ℕ) (a : Mon n) : monMod q a + q • monDiv q a = a := by
  refine Finsupp.ext fun j => ?_
  rw [Finsupp.add_apply, monMod_apply, smul_mon_apply, monDiv_apply, Nat.mod_add_div]

/-- The remainder of `b + q • m` is `b`, when `b` is restricted. -/
theorem monMod_of_isRestricted {q : ℕ} {b : Mon n} (hb : IsRestricted q b) (m : Mon n) :
    monMod q (b + q • m) = b := by
  refine Finsupp.ext fun j => ?_
  rw [monMod_apply, Finsupp.add_apply, smul_mon_apply, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt (hb j)]

/-- The quotient of `b + q • m` is `m`, when `b` is restricted. -/
theorem monDiv_of_isRestricted {q : ℕ} (hq : 0 < q) {b : Mon n} (hb : IsRestricted q b)
    (m : Mon n) : monDiv q (b + q • m) = m := by
  refine Finsupp.ext fun j => ?_
  rw [monDiv_apply, Finsupp.add_apply, smul_mon_apply, Nat.add_mul_div_left _ _ hq,
    Nat.div_eq_of_lt (hb j), zero_add]

/-- Reassembling an exponent vector out of a restricted part and a quotient part.
This is the indexing map of the restricted monomial basis built downstream. -/
noncomputable def monAdd (q : ℕ) (bm : {b : Mon n // IsRestricted q b} × Mon n) : Mon n :=
  (bm.1 : Mon n) + q • bm.2

/-- `monAdd` on an explicit pair. -/
@[simp]
theorem monAdd_mk (q : ℕ) (b : {b : Mon n // IsRestricted q b}) (m : Mon n) :
    monAdd q (b, m) = (b : Mon n) + q • m := rfl

/-- A restricted exponent vector is its own reassembly with zero quotient part. -/
@[simp]
theorem monAdd_snd_zero (q : ℕ) (b : {b : Mon n // IsRestricted q b}) :
    monAdd q (b, 0) = (b : Mon n) := by
  rw [monAdd_mk, smul_zero, add_zero]

/-- Reassembly followed by taking the remainder recovers the restricted part. -/
theorem monMod_monAdd {q : ℕ} (bm : {b : Mon n // IsRestricted q b} × Mon n) :
    monMod q (monAdd q bm) = (bm.1 : Mon n) :=
  monMod_of_isRestricted bm.1.2 bm.2

/-- Reassembly followed by taking the quotient recovers the quotient part. -/
theorem monDiv_monAdd {q : ℕ} (hq : 0 < q) (bm : {b : Mon n // IsRestricted q b} × Mon n) :
    monDiv q (monAdd q bm) = bm.2 :=
  monDiv_of_isRestricted hq bm.1.2 bm.2

/-- Distinct pairs (restricted part, quotient part) give distinct exponent vectors. -/
theorem monAdd_injective {q : ℕ} (hq : 0 < q) : Function.Injective (monAdd (n := n) q) := by
  intro bm₁ bm₂ h
  refine Prod.ext (Subtype.ext ?_) ?_
  · rw [← monMod_monAdd bm₁, ← monMod_monAdd bm₂, h]
  · rw [← monDiv_monAdd hq bm₁, ← monDiv_monAdd hq bm₂, h]

/-- Every exponent vector is `b + q • m` for a restricted `b` and some `m`. -/
theorem monAdd_surjective {q : ℕ} (hq : 0 < q) : Function.Surjective (monAdd (n := n) q) :=
  fun a => ⟨(⟨monMod q a, isRestricted_monMod hq a⟩, monDiv q a), monMod_add_smul_monDiv q a⟩

/-- Division with remainder as a bijection: an exponent vector is the same thing
as a restricted exponent vector together with an arbitrary one. -/
noncomputable def monDivModEquiv (q : ℕ) (hq : 0 < q) :
    Mon n ≃ {b : Mon n // IsRestricted q b} × Mon n where
  toFun a := (⟨monMod q a, isRestricted_monMod hq a⟩, monDiv q a)
  invFun bm := monAdd q bm
  left_inv a := monMod_add_smul_monDiv q a
  right_inv bm := monAdd_injective hq (by
    rw [monAdd_mk, monMod_add_smul_monDiv])

/-- The forward direction of `monDivModEquiv` is division with remainder. -/
@[simp]
theorem monDivModEquiv_apply (q : ℕ) (hq : 0 < q) (a : Mon n) :
    monDivModEquiv q hq a = (⟨monMod q a, isRestricted_monMod hq a⟩, monDiv q a) := rfl

/-- The backward direction of `monDivModEquiv` is reassembly. -/
@[simp]
theorem monDivModEquiv_symm_apply (q : ℕ) (hq : 0 < q)
    (bm : {b : Mon n // IsRestricted q b} × Mon n) :
    (monDivModEquiv q hq).symm bm = monAdd q bm := rfl

/-- A restricted exponent vector, read as a function `Fin n → Fin q`. -/
def restrictedToFin (q : ℕ) (b : {b : Mon n // IsRestricted q b}) : Fin n → Fin q :=
  fun j => ⟨(b : Mon n) j, b.2 j⟩

/-- A restricted exponent vector is determined by its associated function
`Fin n → Fin q`. -/
theorem restrictedToFin_injective (q : ℕ) :
    Function.Injective (restrictedToFin (n := n) q) := by
  intro b₁ b₂ h
  refine Subtype.ext (Finsupp.ext fun j => ?_)
  exact congrArg Fin.val (congrFun h j)

/-- There are only finitely many restricted exponent vectors: each of the `n`
coordinates takes one of `q` values. -/
instance instFiniteIsRestricted {q : ℕ} : Finite {b : Mon n // IsRestricted q b} :=
  Finite.of_injective _ (restrictedToFin_injective q)

/-- The set of restricted exponent vectors is finite. -/
theorem finite_isRestricted (q : ℕ) : {b : Mon n | IsRestricted q b}.Finite :=
  Set.finite_coe_iff.mp instFiniteIsRestricted

end Submission.Ado.PBW
