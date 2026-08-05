import Mathlib

/-!
# The Poincaré–Birkhoff–Witt module

This file constructs, for a Lie algebra `L` over a field `K` with an ordered
basis indexed by `Fin n`, the *PBW module*: a Lie-module structure on the free
`K`-module `Poly K n` on monomial exponent vectors `Mon n = Fin n →₀ ℕ`, such
that `x i` acts on `z^a` as multiplication by `z i` whenever `i` is `≤` every
index occurring in `a`.

The construction is Humphreys' (*Introduction to Lie Algebras and
Representation Theory*, §17.4):

```
ρ(xᵢ) zᵃ = zᵢ zᵃ                                  if i ≼ a
ρ(xᵢ) zᵃ = ρ(xⱼ)(ρ(xᵢ) zᵇ) + ρ(⁅xᵢ, xⱼ⁆) zᵇ       otherwise,
                                    where j := min (supp a), b := a - eⱼ
```

Writing `ρ(xⱼ)` — and *not* multiplication by `zⱼ` — in the second branch is
essential: it makes the hard case of the Lie relation true by construction. See
`Submission/Ado/PBW/Props.lean`.

Literally transcribed, the second branch is not a decreasing recursion, since
`ρ(xᵢ) zᵇ` has degree `|b| + 1 = |a|`. We therefore split off its leading term,
which is `z^(b + eᵢ)` and is sent by `ρ(xⱼ)` to `z^(b + eᵢ + eⱼ)` by the first
branch, and apply `ρ(xⱼ)` only to the remainder, which has degree `≤ |b|`. To
keep this a *structural* recursion we carry a fuel parameter `d` bounding the
degree, and prove afterwards (`actAux_fuel_irrel`) that the result does not
depend on the fuel.
-/

universe u

namespace Submission.Ado.PBW

variable {K : Type u} [Field K] {n : ℕ}

/-- Exponent vectors of monomials in `n` variables. -/
abbrev Mon (n : ℕ) : Type := Fin n →₀ ℕ

/-- The free `K`-module on monomials: the "polynomial module" the Lie algebra
will act on. We do not need its ring structure, only the free module. -/
abbrev Poly (K : Type u) (n : ℕ) [Field K] : Type u := Mon n →₀ K

/-- The basis monomial `z^a`. -/
noncomputable def mono (a : Mon n) : Poly K n := Finsupp.single a (1 : K)

/-- `eᵢ`, the exponent vector of the variable `zᵢ`. -/
noncomputable def e (i : Fin n) : Mon n := Finsupp.single i 1

/-- `i ≼ a`: every variable occurring in the monomial `a` has index `≥ i`.
Equivalently `zᵢ z^a` is again an "ordered" monomial with smallest index `i`. -/
def Aligned (i : Fin n) (a : Mon n) : Prop := ∀ j ∈ a.support, i ≤ j

instance (i : Fin n) (a : Mon n) : Decidable (Aligned i a) := by
  unfold Aligned; infer_instance

theorem aligned_zero (i : Fin n) : Aligned i (0 : Mon n) := by
  simp [Aligned]

theorem support_nonempty_of_not_aligned {i : Fin n} {a : Mon n} (h : ¬ Aligned i a) :
    a.support.Nonempty := by
  by_contra hc
  exact h fun j hj => absurd ⟨j, hj⟩ hc

/-- The smallest variable occurring in a monomial that is not aligned with `i`.
This is the index the recursion peels off. -/
noncomputable def lead {i : Fin n} {a : Mon n} (h : ¬ Aligned i a) : Fin n :=
  a.support.min' (support_nonempty_of_not_aligned h)

theorem lead_mem {i : Fin n} {a : Mon n} (h : ¬ Aligned i a) : lead h ∈ a.support :=
  Finset.min'_mem _ _

theorem lead_le {i : Fin n} {a : Mon n} (h : ¬ Aligned i a) {j : Fin n}
    (hj : j ∈ a.support) : lead h ≤ j :=
  Finset.min'_le _ _ hj

/-- The peeled index is strictly below `i` — this is what makes the recursion
produce the *ordered* monomials. -/
theorem lead_lt {i : Fin n} {a : Mon n} (h : ¬ Aligned i a) : lead h < i := by
  by_contra hc
  exact h fun j hj => le_trans (not_lt.mp hc) (lead_le h hj)

/-- Keep only the monomials of degree at most `d`. -/
noncomputable def trunc (d : ℕ) (f : Poly K n) : Poly K n :=
  f.filter (fun a => a.degree ≤ d)

/-- The fuelled action. `actAux d i a` is the intended value of `ρ(xᵢ) z^a`
whenever `a.degree ≤ d`; `γ i j k` are the structure constants,
`⁅xᵢ, xⱼ⁆ = ∑ₖ γ i j k • xₖ`. -/
noncomputable def actAux (γ : Fin n → Fin n → Fin n → K) :
    ℕ → Fin n → Mon n → Poly K n
  | 0, i, a => mono (a + e i)
  | d + 1, i, a =>
      if h : Aligned i a then mono (a + e i)
      else
        mono ((a - e (lead h)) + e i + e (lead h))
          + Finsupp.linearCombination K (actAux γ d (lead h))
              (trunc (a - e (lead h)).degree (actAux γ d i (a - e (lead h))))
          + ∑ k : Fin n, γ i (lead h) k • actAux γ d k (a - e (lead h))

/-- The action of the `i`-th basis vector on the polynomial module. -/
noncomputable def act (γ : Fin n → Fin n → Fin n → K) (i : Fin n) (a : Mon n) :
    Poly K n :=
  actAux γ a.degree i a

end Submission.Ado.PBW
