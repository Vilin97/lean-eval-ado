import Submission.Ado.PBW.Action

/-!
# The PBW module over a Lie algebra with an ordered basis

`Action.lean` works with abstract structure constants `γ`. Here we fix a Lie
algebra `L` with a basis indexed by `Fin n`, take `γ` to be its structure
constants, and package the action as a linear map `L →ₗ[K] Module.End K (Poly K n)`.

The main theorem is `rhoL_lie`: this map is a morphism of Lie algebras, i.e.
`Poly K n` is an `L`-module. This is statement (C) of the construction.
-/

universe u

namespace Submission.Ado.PBW

variable {K : Type u} [Field K] {L : Type u} [LieRing L] [LieAlgebra K L] {n : ℕ}

/-- The structure constants of `L` in the basis `bas`. -/
noncomputable def gamma (bas : Module.Basis (Fin n) K L) (i j k : Fin n) : K :=
  bas.repr ⁅bas i, bas j⁆ k

/-- The action of an arbitrary element of `L` on the PBW module, obtained from
the action of the basis vectors by linearity. -/
noncomputable def rhoL (bas : Module.Basis (Fin n) K L) : L →ₗ[K] Module.End K (Poly K n) :=
  ∑ k : Fin n, (LinearMap.toSpanSingleton K (Module.End K (Poly K n))
      (rho (gamma bas) k)) ∘ₗ (bas.coord k)

theorem rhoL_apply (bas : Module.Basis (Fin n) K L) (x : L) :
    rhoL bas x = ∑ k : Fin n, bas.repr x k • rho (gamma bas) k := by
  simp [rhoL, LinearMap.toSpanSingleton, Module.Basis.coord]

@[simp] theorem rhoL_basis (bas : Module.Basis (Fin n) K L) (i : Fin n) :
    rhoL bas (bas i) = rho (gamma bas) i := by
  rw [rhoL_apply]
  simp [Module.Basis.repr_self, Finsupp.single_apply]

/-- The bracket of two basis vectors acts through the structure constants. -/
theorem rhoL_lie_basis (bas : Module.Basis (Fin n) K L) (i j : Fin n) :
    rhoL bas ⁅bas i, bas j⁆ = ∑ k : Fin n, gamma bas i j k • rho (gamma bas) k := by
  rw [rhoL_apply]; rfl

/-! ### Combinatorial and degree auxiliaries

These only involve the abstract structure constants `γ`; they are the "Lemma 1.2"
and "Lemma 6.4" bookkeeping of the classical proof. -/

section Aux

variable {γ : Fin n → Fin n → Fin n → K}

/-- If `k ≼ c` and `k ≤ l`, then `k ≼ c + eₗ`. (Lemma 1.2(3).) -/
theorem aligned_add_e {k l : Fin n} {c : Mon n} (hc : Aligned k c) (hkl : k ≤ l) :
    Aligned k (c + e l) := by
  intro b hb
  rw [Finsupp.mem_support_iff, Finsupp.add_apply] at hb
  rcases eq_or_ne b l with rfl | hbl
  · exact hkl
  · refine hc _ (Finsupp.mem_support_iff.mpr ?_)
    rwa [e_apply_of_ne (Ne.symm hbl), add_zero] at hb

/-- Peeling off a variable that occurs in `a` and putting it back is the identity. -/
theorem sub_e_add_e {a : Mon n} {j : Fin n} (hj : j ∈ a.support) : a - e j + e j = a := by
  refine tsub_add_cancel_of_le ?_
  rw [e, Finsupp.single_le_iff]
  exact Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hj)

/-- The pivot index `lead h` is `≼` the monomial obtained by peeling it off. -/
theorem aligned_lead_sub {i : Fin n} {a : Mon n} (h : ¬ Aligned i a) :
    Aligned (lead h) (a - e (lead h)) := by
  intro b hb
  refine lead_le h (Finsupp.mem_support_iff.mpr ?_)
  intro hab
  rw [Finsupp.mem_support_iff, Finsupp.tsub_apply, hab, Nat.zero_sub] at hb
  exact hb rfl

/-- **Lemma 6.4.** Every monomial of `act γ l c` is either the leading monomial
`c + eₗ` or has degree at most `|c|`. -/
theorem act_support_cases {l : Fin n} {c b : Mon n} (hb : b ∈ (act γ l c).support) :
    b = c + e l ∨ b.degree ≤ c.degree := by
  by_cases h : b = c + e l
  · exact Or.inl h
  refine Or.inr (act_sub_mono_degLE (γ := γ) l c b ?_)
  rw [Finsupp.mem_support_iff] at hb ⊢
  have hm : (mono (c + e l) : Poly K n) b = 0 := by
    simp only [mono]
    exact Finsupp.single_eq_of_ne h
  rwa [Finsupp.sub_apply, hm, sub_zero]

end Aux

/-! ### The defect of the Lie relation -/

/-- The defect of the Lie relation (C) for the pair `(x, y)`, as a linear
endomorphism of `Poly K n`. Relation (C) at `p` says that all these defects
vanish at `p`. -/
noncomputable def lieDefect (bas : Module.Basis (Fin n) K L) (x y : L) :
    Poly K n →ₗ[K] Poly K n :=
  ⁅rhoL bas x, rhoL bas y⁆ - rhoL bas ⁅x, y⁆

/-- The defect, evaluated at a polynomial. -/
theorem lieDefect_apply (bas : Module.Basis (Fin n) K L) (x y : L) (p : Poly K n) :
    lieDefect bas x y p
      = rhoL bas x (rhoL bas y p) - rhoL bas y (rhoL bas x p) - rhoL bas ⁅x, y⁆ p := rfl

/-- Relation (C) holds at the polynomial `p`, for every pair of elements of `L`. -/
def LieRelOn (bas : Module.Basis (Fin n) K L) (p : Poly K n) : Prop :=
  ∀ x y : L, lieDefect bas x y p = 0

/-- Every polynomial is the sum of its monomials. -/
theorem eq_sum_support (p : Poly K n) : p = ∑ b ∈ p.support, p b • mono b := by
  conv_lhs => rw [← Finsupp.sum_single p]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [mono, Finsupp.smul_single, smul_eq_mul, mul_one]

/-- **(R2), linearity in `p`.** A defect that vanishes on every monomial of `p`
vanishes at `p`. -/
theorem lieDefect_of_support {bas : Module.Basis (Fin n) K L} {x y : L} {p : Poly K n}
    (h : ∀ b ∈ p.support, lieDefect bas x y (mono b) = 0) : lieDefect bas x y p = 0 := by
  conv_lhs => rw [eq_sum_support p]
  rw [map_sum]
  exact Finset.sum_eq_zero fun b hb => by rw [map_smul, h b hb, smul_zero]

/-- The bracket of two basis vectors acts on a polynomial through the structure
constants. -/
theorem rhoL_lie_basis_apply (bas : Module.Basis (Fin n) K L) (i j : Fin n) (p : Poly K n) :
    rhoL bas ⁅bas i, bas j⁆ p = ∑ k : Fin n, gamma bas i j k • rho (gamma bas) k p := by
  rw [rhoL_lie_basis]
  simp

/-- The action of an arbitrary element, expanded over the basis. -/
theorem rhoL_apply_eq_sum (bas : Module.Basis (Fin n) K L) (x : L) (q : Poly K n) :
    rhoL bas x q = ∑ i : Fin n, bas.repr x i • rhoL bas (bas i) q := by
  conv_lhs => rw [← bas.sum_repr x]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]

/-- **(R1), linearity in `x`.** The defect is `K`-linear in its first slot. -/
theorem lieDefect_apply_sum_left (bas : Module.Basis (Fin n) K L) (x y : L) (p : Poly K n) :
    lieDefect bas x y p = ∑ i : Fin n, bas.repr x i • lieDefect bas (bas i) y p := by
  have h1 : rhoL bas x (rhoL bas y p)
      = ∑ i : Fin n, bas.repr x i • rhoL bas (bas i) (rhoL bas y p) :=
    rhoL_apply_eq_sum bas x _
  have h2 : rhoL bas y (rhoL bas x p)
      = ∑ i : Fin n, bas.repr x i • rhoL bas y (rhoL bas (bas i) p) := by
    conv_lhs => rw [rhoL_apply_eq_sum bas x p]
    simp only [map_sum, map_smul]
  have h3 : rhoL bas ⁅x, y⁆ p = ∑ i : Fin n, bas.repr x i • rhoL bas ⁅bas i, y⁆ p := by
    conv_lhs => rw [← bas.sum_repr x]
    simp only [sum_lie, smul_lie, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
  simp only [lieDefect_apply, h1, h2, h3, smul_sub, Finset.sum_sub_distrib]

/-- **(R3), antisymmetry.** -/
theorem lieDefect_swap (bas : Module.Basis (Fin n) K L) (x y : L) (p : Poly K n) :
    lieDefect bas y x p = - lieDefect bas x y p := by
  rw [lieDefect_apply, lieDefect_apply, ← lie_skew x y, map_neg, LinearMap.neg_apply]
  abel

/-- **(R3), the diagonal.** Uses `⁅x, x⁆ = 0`, i.e. that the bracket is
alternating (not merely antisymmetric). -/
theorem lieDefect_self (bas : Module.Basis (Fin n) K L) (x : L) (p : Poly K n) :
    lieDefect bas x x p = 0 := by
  rw [lieDefect_apply, lie_self, map_zero]
  simp

/-- **(R1).** A defect that vanishes at `p` on all pairs of basis vectors
vanishes at `p` on all pairs of elements of `L`. -/
theorem lieRelOn_of_basis {bas : Module.Basis (Fin n) K L} {p : Poly K n}
    (h : ∀ i j : Fin n, lieDefect bas (bas i) (bas j) p = 0) : LieRelOn bas p := by
  intro x y
  rw [lieDefect_apply_sum_left bas x y p]
  refine Finset.sum_eq_zero fun i _ => ?_
  have hi : lieDefect bas (bas i) y p = 0 := by
    rw [lieDefect_swap bas y (bas i) p, lieDefect_apply_sum_left bas y (bas i) p]
    rw [Finset.sum_eq_zero fun l _ => by rw [h l i, smul_zero], neg_zero]
  rw [hi, smul_zero]

/-- **Case 1 (§6.2).** For `j < i` and `j ≼ a` the defect vanishes on `z^a`, in
every degree; this is `lie_rel_aligned`, true by construction. -/
theorem lieDefect_mono_of_aligned (bas : Module.Basis (Fin n) K L) {i j : Fin n} {a : Mon n}
    (haj : Aligned j a) (hji : j < i) : lieDefect bas (bas i) (bas j) (mono a) = 0 := by
  rw [lieDefect_apply, rhoL_basis, rhoL_basis, rhoL_lie_basis_apply, sub_eq_zero]
  simpa using lie_rel_aligned (γ := gamma bas) haj hji

/-! ### The inductive step -/

/-- **Lemma 6.3.** If the relation is known on all monomials of degree `< d`,
then for `k < l` the pair `(x_l, x_k)` satisfies it on every polynomial whose
monomials are either of degree `< d` or aligned with the pivot `k`. -/
theorem lieDefect_pivot (bas : Module.Basis (Fin n) K L) {d : ℕ}
    (IH : ∀ b : Mon n, b.degree < d → LieRelOn bas (mono b))
    {k l : Fin n} (hkl : k < l) {p : Poly K n}
    (hp : ∀ b ∈ p.support, b.degree < d ∨ Aligned k b) :
    lieDefect bas (bas l) (bas k) p = 0 := by
  refine lieDefect_of_support fun b hb => ?_
  rcases hp b hb with h | h
  · exact IH b h _ _
  · exact lieDefect_mono_of_aligned bas h hkl

/-- **Lemma 6.5.** The form of the Jacobi identity used in Case 2. It is derived
from the cyclic identity `lie_jacobi`; expanding with `lie_lie` twice would only
give twice the statement. -/
theorem lie_lie_sub_lie_lie (A B C : L) : ⁅⁅A, C⁆, B⁆ - ⁅⁅B, C⁆, A⁆ = ⁅⁅A, B⁆, C⁆ := by
  have h := lie_jacobi A B C
  rw [← lie_skew C A, lie_neg] at h
  rw [← lie_skew ⁅A, C⁆ B, ← lie_skew ⁅B, C⁆ A, ← lie_skew ⁅A, B⁆ C]
  refine eq_of_sub_eq_zero ?_
  rw [← h]
  abel

/-- **Case 2 (§6.4).** The pair `(x_i, x_j)` with `k < j < i` on the monomial
`z^a = z_k z^c`, where `k ≼ c`: unfold through the pivot `k`, commute `x_i` and
`x_j` past `x_k` using Lemma 6.3, and collect with the Jacobi identity. -/
theorem lieDefect_mono_of_pivot (bas : Module.Basis (Fin n) K L) {d : ℕ}
    (IH : ∀ b : Mon n, b.degree < d → LieRelOn bas (mono b))
    {i j k : Fin n} {a c : Mon n} (hkj : k < j) (hji : j < i)
    (hkc : Aligned k c) (hac : c + e k = a) (hcd : c.degree < d) :
    lieDefect bas (bas i) (bas j) (mono a) = 0 := by
  have hki : k < i := hkj.trans hji
  -- the induction hypothesis at `z^c`, in the form of a commutation rule
  have hrel : ∀ u v : L, rhoL bas u (rhoL bas v (mono c))
      = rhoL bas v (rhoL bas u (mono c)) + rhoL bas ⁅u, v⁆ (mono c) := by
    intro u v
    have h := IH c hcd u v
    rwa [lieDefect_apply, sub_sub, sub_eq_zero] at h
  -- `x_k · z^c = z^a`, by (A)
  have hZc : rhoL bas (bas k) (mono c) = mono a := by
    rw [rhoL_basis, rho_mono, act_of_aligned hkc, hac]
  -- Step 1: unfold through the pivot
  have hE1 : rhoL bas (bas i) (mono a)
      = rhoL bas (bas k) (rhoL bas (bas i) (mono c))
        + rhoL bas ⁅bas i, bas k⁆ (mono c) := by
    have h := hrel (bas i) (bas k); rwa [hZc] at h
  have hE2 : rhoL bas (bas j) (mono a)
      = rhoL bas (bas k) (rhoL bas (bas j) (mono c))
        + rhoL bas ⁅bas j, bas k⁆ (mono c) := by
    have h := hrel (bas j) (bas k); rwa [hZc] at h
  have hE3 : rhoL bas ⁅bas i, bas j⁆ (mono a)
      = rhoL bas (bas k) (rhoL bas ⁅bas i, bas j⁆ (mono c))
        + rhoL bas ⁅⁅bas i, bas j⁆, bas k⁆ (mono c) := by
    have h := hrel ⁅bas i, bas j⁆ (bas k); rwa [hZc] at h
  -- Lemma 6.4: `x_l · z^c` lies in the domain of Lemma 6.3 whenever `k ≤ l`
  have hQ : ∀ l : Fin n, k ≤ l →
      ∀ b ∈ (rhoL bas (bas l) (mono c)).support, b.degree < d ∨ Aligned k b := by
    intro l hkl b hb
    rw [rhoL_basis, rho_mono] at hb
    rcases act_support_cases hb with rfl | hdeg
    · exact Or.inr (aligned_add_e hkc hkl)
    · exact Or.inl (lt_of_le_of_lt hdeg hcd)
  -- Step 3: commute past the pivot
  have h1 : rhoL bas (bas i) (rhoL bas (bas k) (rhoL bas (bas j) (mono c)))
      = rhoL bas (bas k) (rhoL bas (bas i) (rhoL bas (bas j) (mono c)))
        + rhoL bas ⁅bas i, bas k⁆ (rhoL bas (bas j) (mono c)) := by
    have h := lieDefect_pivot bas IH hki (hQ j hkj.le)
    rwa [lieDefect_apply, sub_sub, sub_eq_zero] at h
  have h2 : rhoL bas (bas j) (rhoL bas (bas k) (rhoL bas (bas i) (mono c)))
      = rhoL bas (bas k) (rhoL bas (bas j) (rhoL bas (bas i) (mono c)))
        + rhoL bas ⁅bas j, bas k⁆ (rhoL bas (bas i) (mono c)) := by
    have h := lieDefect_pivot bas IH hkj (hQ i hki.le)
    rwa [lieDefect_apply, sub_sub, sub_eq_zero] at h
  -- Step 5: the Jacobi identity
  have hJ : rhoL bas ⁅⁅bas i, bas k⁆, bas j⁆ (mono c)
      - rhoL bas ⁅⁅bas j, bas k⁆, bas i⁆ (mono c)
      = rhoL bas ⁅⁅bas i, bas j⁆, bas k⁆ (mono c) := by
    have h : ⁅⁅bas i, bas k⁆, bas j⁆
        = ⁅⁅bas i, bas j⁆, bas k⁆ + ⁅⁅bas j, bas k⁆, bas i⁆ := by
      rw [← lie_lie_sub_lie_lie (bas i) (bas j) (bas k)]; abel
    rw [h, map_add, LinearMap.add_apply]
    abel
  -- Steps 2 and 4: assemble
  rw [lieDefect_apply, sub_sub, sub_eq_zero, hE1, hE2, hE3, map_add, map_add, h1, h2,
    hrel (bas i) (bas j), map_add, hrel ⁅bas i, bas k⁆ (bas j), hrel ⁅bas j, bas k⁆ (bas i),
    ← hJ]
  abel

/-- The inductive step for a pair `j < i` of basis indices. -/
theorem lieDefect_mono_step (bas : Module.Basis (Fin n) K L) {d : ℕ}
    (IH : ∀ b : Mon n, b.degree < d → LieRelOn bas (mono b))
    {i j : Fin n} {a : Mon n} (ha : a.degree ≤ d) (hji : j < i) :
    lieDefect bas (bas i) (bas j) (mono a) = 0 := by
  by_cases haj : Aligned j a
  · exact lieDefect_mono_of_aligned bas haj hji
  · exact lieDefect_mono_of_pivot bas IH (lead_lt haj) hji (aligned_lead_sub haj)
      (sub_e_add_e (lead_mem haj)) (by have := degree_sub_e (lead_mem haj); omega)

/-- **(C) on monomials.** Proved by strong induction on a bound for the degree. -/
theorem lieRelOn_mono (bas : Module.Basis (Fin n) K L) :
    ∀ (d : ℕ) (a : Mon n), a.degree ≤ d → LieRelOn bas (mono a) := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d IH =>
    intro a ha
    have IH' : ∀ b : Mon n, b.degree < d → LieRelOn bas (mono b) :=
      fun b hb => IH b.degree hb b le_rfl
    refine lieRelOn_of_basis fun i j => ?_
    rcases lt_trichotomy j i with hji | rfl | hij
    · exact lieDefect_mono_step bas IH' ha hji
    · exact lieDefect_self bas _ _
    · rw [lieDefect_swap bas (bas j) (bas i), lieDefect_mono_step bas IH' ha hij, neg_zero]

/-- **(C) on all of `Poly K n`.** -/
theorem lieRelOn_all (bas : Module.Basis (Fin n) K L) (p : Poly K n) : LieRelOn bas p := by
  intro x y
  exact lieDefect_of_support fun b _ => lieRelOn_mono bas b.degree b le_rfl x y

/-- **(C).** `Poly K n` is a Lie module over `L`: the commutator of the actions of
`x` and `y` is the action of `⁅x, y⁆`.

This is proved by strong induction on the degree of a monomial; the aligned case
`lie_rel_aligned` holds by construction in every degree, and the general case
reduces to it via the Jacobi identity. -/
theorem rhoL_lie (bas : Module.Basis (Fin n) K L) (x y : L) :
    ⁅rhoL bas x, rhoL bas y⁆ = rhoL bas ⁅x, y⁆ := by
  rw [← sub_eq_zero]
  exact LinearMap.ext fun p => lieRelOn_all bas p x y

end Submission.Ado.PBW
