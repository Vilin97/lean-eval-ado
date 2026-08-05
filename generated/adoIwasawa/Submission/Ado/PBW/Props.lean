import Submission.Ado.PBW.Defs

/-!
# Basic properties of the PBW action

Unfolding lemmas, fuel-irrelevance, and the two elementary invariants of the
construction:

* **(A)** `Aligned i a → act γ i a = mono (a + eᵢ)`;
* **(B)** `act γ i a - mono (a + eᵢ)` is supported in degrees `≤ |a|`.

The Lie relation (C) is in `Submission/Ado/PBW/Lie.lean`.
-/

universe u

namespace Submission.Ado.PBW

variable {K : Type u} [Field K] {n : ℕ} {γ : Fin n → Fin n → Fin n → K}

/-! ### Degree bookkeeping -/

@[simp] theorem degree_e (i : Fin n) : (e i : Mon n).degree = 1 := by
  simp [e, Finsupp.degree]

theorem degree_sub_e {a : Mon n} {j : Fin n} (hj : j ∈ a.support) :
    (a - e j).degree + 1 = a.degree := by
  have hle : (e j : Mon n) ≤ a := by
    rw [e, Finsupp.single_le_iff]
    exact Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hj)
  have h1 : a - e j + e j = a := tsub_add_cancel_of_le hle
  calc (a - e j).degree + 1 = (a - e j).degree + (e j : Mon n).degree := by simp
    _ = (a - e j + e j).degree := (map_add Finsupp.degree _ _).symm
    _ = a.degree := by rw [h1]

theorem degree_lead_lt {i : Fin n} {a : Mon n} (h : ¬ Aligned i a) :
    (a - e (lead h)).degree < a.degree := by
  have := degree_sub_e (lead_mem h); omega

/-! ### Unfolding -/

@[simp] theorem actAux_zero (i : Fin n) (a : Mon n) :
    actAux γ 0 i a = mono (a + e i) := rfl

theorem actAux_succ_of_aligned {d : ℕ} {i : Fin n} {a : Mon n} (h : Aligned i a) :
    actAux γ (d + 1) i a = mono (a + e i) := dif_pos h

theorem actAux_succ_of_not_aligned {d : ℕ} {i : Fin n} {a : Mon n} (h : ¬ Aligned i a) :
    actAux γ (d + 1) i a =
      mono ((a - e (lead h)) + e i + e (lead h))
        + Finsupp.linearCombination K (actAux γ d (lead h))
            (trunc (a - e (lead h)).degree (actAux γ d i (a - e (lead h))))
        + ∑ k : Fin n, γ i (lead h) k • actAux γ d k (a - e (lead h)) := dif_neg h

/-! ### Fuel irrelevance -/

theorem actAux_fuel_irrel :
    ∀ (d : ℕ) (d' : ℕ) (i : Fin n) (a : Mon n), a.degree ≤ d → a.degree ≤ d' →
      actAux γ d i a = actAux γ d' i a := by
  intro d
  induction d with
  | zero =>
      intro d' i a hd _
      have ha : a = 0 := (Finsupp.degree_eq_zero_iff a).mp (Nat.le_zero.mp hd)
      subst ha
      cases d' with
      | zero => rfl
      | succ d' => rw [actAux_zero, actAux_succ_of_aligned (aligned_zero i)]
  | succ d ih =>
      intro d' i a hd hd'
      by_cases h : Aligned i a
      · cases d' with
        | zero => rw [actAux_succ_of_aligned h, actAux_zero]
        | succ d' => rw [actAux_succ_of_aligned h, actAux_succ_of_aligned h]
      · cases d' with
        | zero =>
            exfalso
            refine h ?_
            rw [(Finsupp.degree_eq_zero_iff a).mp (Nat.le_zero.mp hd')]
            exact aligned_zero i
        | succ d' =>
            rw [actAux_succ_of_not_aligned h, actAux_succ_of_not_aligned h]
            have hdeg : (a - e (lead h)).degree + 1 = a.degree := degree_sub_e (lead_mem h)
            have hb : (a - e (lead h)).degree ≤ d := by omega
            have hb' : (a - e (lead h)).degree ≤ d' := by omega
            have hi : actAux γ d i (a - e (lead h)) = actAux γ d' i (a - e (lead h)) :=
              ih d' i _ hb hb'
            have hsum : (∑ k : Fin n, γ i (lead h) k • actAux γ d k (a - e (lead h)))
                = ∑ k : Fin n, γ i (lead h) k • actAux γ d' k (a - e (lead h)) :=
              Finset.sum_congr rfl fun k _ => by rw [ih d' k _ hb hb']
            have hlc : Finsupp.linearCombination K (actAux γ d (lead h))
                  (trunc (a - e (lead h)).degree (actAux γ d' i (a - e (lead h))))
                = Finsupp.linearCombination K (actAux γ d' (lead h))
                  (trunc (a - e (lead h)).degree (actAux γ d' i (a - e (lead h)))) := by
              rw [Finsupp.linearCombination_apply, Finsupp.linearCombination_apply]
              refine Finsupp.sum_congr fun c hc => ?_
              have hcd : c.degree ≤ (a - e (lead h)).degree := by
                simp only [trunc, Finsupp.support_filter, Finset.mem_filter] at hc
                exact hc.2
              rw [ih d' (lead h) c (hcd.trans hb) (hcd.trans hb')]
            rw [hi, hsum, hlc]

/-- `act` computed with any sufficient fuel. -/
theorem act_eq_actAux {d : ℕ} (i : Fin n) (a : Mon n) (hd : a.degree ≤ d) :
    act γ i a = actAux γ d i a :=
  actAux_fuel_irrel _ _ _ _ le_rfl hd

/-! ### (A) and the unfolded form of `act` -/

theorem act_of_aligned {i : Fin n} {a : Mon n} (h : Aligned i a) :
    act γ i a = mono (a + e i) := by
  rw [act_eq_actAux (d := a.degree + 1) i a (Nat.le_succ _), actAux_succ_of_aligned h]

theorem act_of_not_aligned {i : Fin n} {a : Mon n} (h : ¬ Aligned i a) :
    act γ i a =
      mono ((a - e (lead h)) + e i + e (lead h))
        + Finsupp.linearCombination K (act γ (lead h))
            (trunc (a - e (lead h)).degree (act γ i (a - e (lead h))))
        + ∑ k : Fin n, γ i (lead h) k • act γ k (a - e (lead h)) := by
  have hdeg : (a - e (lead h)).degree + 1 = a.degree := degree_sub_e (lead_mem h)
  have hb : (a - e (lead h)).degree ≤ (a - e (lead h)).degree := le_rfl
  rw [act_eq_actAux (d := (a - e (lead h)).degree + 1) i a (le_of_eq hdeg.symm),
    actAux_succ_of_not_aligned h]
  have hi : actAux γ (a - e (lead h)).degree i (a - e (lead h)) = act γ i (a - e (lead h)) :=
    (act_eq_actAux i _ hb).symm
  have hsum : (∑ k : Fin n, γ i (lead h) k • actAux γ (a - e (lead h)).degree k (a - e (lead h)))
      = ∑ k : Fin n, γ i (lead h) k • act γ k (a - e (lead h)) :=
    Finset.sum_congr rfl fun k _ => by rw [act_eq_actAux k _ hb]
  have hlc : Finsupp.linearCombination K (actAux γ (a - e (lead h)).degree (lead h))
        (trunc (a - e (lead h)).degree (act γ i (a - e (lead h))))
      = Finsupp.linearCombination K (act γ (lead h))
        (trunc (a - e (lead h)).degree (act γ i (a - e (lead h)))) := by
    rw [Finsupp.linearCombination_apply, Finsupp.linearCombination_apply]
    refine Finsupp.sum_congr fun c hc => ?_
    have hcd : c.degree ≤ (a - e (lead h)).degree := by
      simp only [trunc, Finsupp.support_filter, Finset.mem_filter] at hc
      exact hc.2
    rw [act_eq_actAux (lead h) c hcd]
  rw [hi, hsum, hlc]

/-! ### (B) -/

/-- `f` is supported in degrees `≤ d`. -/
def DegLE (f : Poly K n) (d : ℕ) : Prop := ∀ c ∈ f.support, c.degree ≤ d

/-- The degree of `a + eᵢ` is one more than the degree of `a`. -/
theorem degree_add_e (a : Mon n) (i : Fin n) : (a + e i).degree = a.degree + 1 := by
  rw [map_add Finsupp.degree, degree_e]

/-- The zero polynomial is supported in degrees `≤ d` for every `d`. -/
theorem DegLE_zero (d : ℕ) : DegLE (0 : Poly K n) d := by
  intro c hc
  simp only [Finsupp.support_zero, Finset.notMem_empty] at hc

/-- `DegLE` is monotone in the degree bound. -/
theorem DegLE_mono {f : Poly K n} {d d' : ℕ} (hf : DegLE f d) (hd : d ≤ d') : DegLE f d' :=
  fun c hc => (hf c hc).trans hd

/-- A sum of two polynomials of degree `≤ d` has degree `≤ d`. -/
theorem DegLE_add {f g : Poly K n} {d : ℕ} (hf : DegLE f d) (hg : DegLE g d) :
    DegLE (f + g) d := by
  intro c hc
  rcases Finset.mem_union.mp (Finsupp.support_add hc) with hc | hc
  · exact hf c hc
  · exact hg c hc

/-- A difference of two polynomials of degree `≤ d` has degree `≤ d`. -/
theorem DegLE_sub {f g : Poly K n} {d : ℕ} (hf : DegLE f d) (hg : DegLE g d) :
    DegLE (f - g) d := by
  intro c hc
  rcases Finset.mem_union.mp (Finsupp.support_sub hc) with hc | hc
  · exact hf c hc
  · exact hg c hc

/-- Scaling does not increase the degree. -/
theorem DegLE_smul {r : K} {f : Poly K n} {d : ℕ} (hf : DegLE f d) : DegLE (r • f) d :=
  fun c hc => hf c (Finsupp.support_smul hc)

/-- A finite sum of polynomials of degree `≤ d` has degree `≤ d`. -/
theorem DegLE_sum {ι : Type*} {s : Finset ι} {f : ι → Poly K n} {d : ℕ}
    (hf : ∀ k ∈ s, DegLE (f k) d) : DegLE (∑ k ∈ s, f k) d := by
  classical
  induction s using Finset.induction with
  | empty => simpa using DegLE_zero d
  | insert k s hk ih =>
      rw [Finset.sum_insert hk]
      exact DegLE_add (hf k (Finset.mem_insert_self k s))
        (ih fun l hl => hf l (Finset.mem_insert_of_mem hl))

/-- The monomial `z^a` is supported in degrees `≤ |a|`. -/
theorem DegLE_mono_single (a : Mon n) : DegLE (mono a : Poly K n) a.degree := by
  intro c hc
  rw [mono] at hc
  rw [Finset.mem_singleton.mp (Finsupp.support_single_subset hc)]

/-- A linear combination of polynomials of degree `≤ d` has degree `≤ d`. -/
theorem DegLE_linearCombination {v : Mon n → Poly K n} {t : Poly K n} {d : ℕ}
    (hv : ∀ c ∈ t.support, DegLE (v c) d) :
    DegLE (Finsupp.linearCombination K v t) d := by
  rw [Finsupp.linearCombination_apply, Finsupp.sum]
  exact DegLE_sum fun c hc => DegLE_smul (hv c hc)

theorem act_sub_mono_degLE (i : Fin n) (a : Mon n) :
    DegLE (act γ i a - mono (a + e i)) a.degree := by
  suffices H : ∀ N : ℕ, ∀ (i : Fin n) (a : Mon n), a.degree ≤ N →
      DegLE (act γ i a - mono (a + e i)) a.degree from H a.degree i a le_rfl
  intro N
  induction N with
  | zero =>
      intro i a ha
      have h : Aligned i a := by
        rw [(Finsupp.degree_eq_zero_iff a).mp (Nat.le_zero.mp ha)]
        exact aligned_zero i
      rw [act_of_aligned h, sub_self]
      exact DegLE_zero _
  | succ N ih =>
      intro i a ha
      by_cases h : Aligned i a
      · rw [act_of_aligned h, sub_self]
        exact DegLE_zero _
      · -- Every action on a monomial of degree `≤ N` raises the degree by at most one.
        have key : ∀ (k : Fin n) (b : Mon n), b.degree ≤ N → DegLE (act γ k b) (b.degree + 1) := by
          intro k b hb
          have hsplit : act γ k b = (act γ k b - mono (b + e k)) + mono (b + e k) := by abel
          rw [hsplit]
          refine DegLE_add (DegLE_mono (ih k b hb) (Nat.le_succ _)) ?_
          have := DegLE_mono_single (K := K) (b + e k)
          rwa [degree_add_e] at this
        have hdeg : (a - e (lead h)).degree + 1 = a.degree := degree_sub_e (lead_mem h)
        have hbN : (a - e (lead h)).degree ≤ N := by omega
        have hle : (e (lead h) : Mon n) ≤ a := by
          rw [e, Finsupp.single_le_iff]
          exact Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp (lead_mem h))
        have hcancel : a - e (lead h) + e i + e (lead h) = a + e i := by
          rw [add_right_comm, tsub_add_cancel_of_le hle]
        have hcollapse : ∀ f g : Poly K n, mono (a + e i) + f + g - mono (a + e i) = f + g := by
          intro f g; abel
        rw [act_of_not_aligned h, hcancel, hcollapse]
        refine DegLE_add ?_ ?_
        · refine DegLE_linearCombination fun c hc => ?_
          have hcd : c.degree ≤ (a - e (lead h)).degree := by
            simp only [trunc, Finsupp.support_filter, Finset.mem_filter] at hc
            exact hc.2
          exact DegLE_mono (key (lead h) c (hcd.trans hbN)) (by omega)
        · exact DegLE_sum fun k _ =>
            DegLE_smul (DegLE_mono (key k _ hbN) (le_of_eq hdeg))

theorem act_degLE (i : Fin n) (a : Mon n) : DegLE (act γ i a) (a.degree + 1) := by
  have hsplit : act γ i a = (act γ i a - mono (a + e i)) + mono (a + e i) := by abel
  rw [hsplit]
  refine DegLE_add (DegLE_mono (act_sub_mono_degLE i a) (Nat.le_succ _)) ?_
  have := DegLE_mono_single (K := K) (a + e i)
  rwa [degree_add_e] at this

end Submission.Ado.PBW
