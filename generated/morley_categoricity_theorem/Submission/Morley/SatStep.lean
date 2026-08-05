import Mathlib
import Submission.Morley.Realize

/-!
# One saturation step

This file provides the two ingredients needed to build a saturated (or `κ`-saturated) elementary
extension one step at a time.

* `Submission.Morley.exists_elementaryExtension_realizing_card_le` is
  `Submission.Morley.exists_countable_elementaryExtension_realizing` with `ℵ₀` replaced by an
  arbitrary infinite cardinal `κ`: given a structure `A` of size at most `κ` and a family of
  `1`-types over `A` indexed by a set of size at most `κ`, each finitely satisfiable in `A`, there
  is an elementary extension of `A` of size at most `κ` realizing all of them.  The proof runs the
  compactness argument of `Submission.Morley.exists_elementaryExtension_realizing` and then cuts
  the resulting model down with downward Löwenheim–Skolem.

* `Submission.Morley.exists_realize_finset_iff` says that an elementary embedding preserves and
  reflects finite satisfiability of a *finite* set of formulas with parameters, since such a set can
  be packaged into the single formula `⋀ φ ∈ t, φ` prefixed by an existential quantifier.
-/

namespace Submission.Morley

open Cardinal Set FirstOrder FirstOrder.Language

/-- **Realization of `≤ κ` many types in an elementary extension of size `≤ κ`.**

Let `A` be a nonempty structure of size at most `κ` for a language `L` with at most countably many
symbols, `κ` infinite, and let `p : ι → Set (L.Formula (A ⊕ Fin 1))` be a family, indexed by a type
of size at most `κ`, of `1`-types over `A`.  If each `p i` is finitely satisfiable in `A`, then
there is an elementary extension `B` of `A` with `#B ≤ κ` in which every `p i` is realized. -/
theorem exists_elementaryExtension_realizing_card_le
    {L : FirstOrder.Language.{0, 0}} {A : Type} [L.Structure A] [Nonempty A] {ι : Type}
    (hL : L.card ≤ ℵ₀) {κ : Cardinal.{0}} (hκ : ℵ₀ ≤ κ) (hA : #A ≤ κ) (hι : #ι ≤ κ)
    (p : ι → Set (L.Formula (A ⊕ Fin 1)))
    (hfin : ∀ i, ∀ t : Finset (L.Formula (A ⊕ Fin 1)), ↑t ⊆ p i →
      ∃ a : A, ∀ φ ∈ t, φ.Realize (Sum.elim id fun _ => a)) :
    ∃ (B : Type) (_ : L.Structure B) (f : A ↪ₑ[L] B), #B ≤ κ ∧
      ∀ i, ∃ b : B, ∀ φ ∈ p i, φ.Realize (Sum.elim (f ·) fun _ => b) := by
  classical
  obtain ⟨N, instN, f, b, hb⟩ := exists_elementaryExtension_realizing p hfin
  rcases le_or_gt (#N) κ with hN | hN
  · exact ⟨N, instN, f, hN, fun i => ⟨b i, fun φ hφ => hb i φ hφ⟩⟩
  · have hset : #(((Set.range fun a => f a) ∪ Set.range b : Set N)) ≤ κ := by
      refine (Cardinal.mk_union_le _ _).trans ?_
      calc #(Set.range fun a => f a) + #(Set.range b)
          ≤ κ + κ := add_le_add (Cardinal.mk_range_le.trans hA) (Cardinal.mk_range_le.trans hι)
        _ = κ := Cardinal.add_eq_self hκ
    obtain ⟨S, hSsub, hScard⟩ := exists_elementarySubstructure_card_eq L
      ((Set.range fun a => f a) ∪ Set.range b) κ hκ (by simpa using hset)
      (by simpa using hL.trans hκ) (by simpa using hN.le)
    have hScard' : #(S : Type) = κ := by simpa using hScard
    have hfS : ∀ a : A, f a ∈ S := fun a => hSsub (Or.inl ⟨a, rfl⟩)
    have hbS : ∀ i : ι, b i ∈ S := fun i => hSsub (Or.inr ⟨i, rfl⟩)
    refine ⟨(S : Type), inferInstance, ⟨fun a => ⟨f a, hfS a⟩, fun n χ x => ?_⟩, hScard'.le,
      fun i => ⟨⟨b i, hbS i⟩, fun φ hφ => ?_⟩⟩
    · rw [← S.subtype.map_formula χ ((fun a : A => (⟨f a, hfS a⟩ : S)) ∘ x)]
      exact f.map_formula χ x
    · refine (S.subtype.map_formula φ
        (Sum.elim (fun a : A => (⟨f a, hfS a⟩ : S)) fun _ => (⟨b i, hbS i⟩ : S))).1 ?_
      rw [show ((S.subtype : S → N) ∘
          Sum.elim (fun a : A => (⟨f a, hfS a⟩ : S)) fun _ => (⟨b i, hbS i⟩ : S)) =
          Sum.elim (fun a => f a) fun _ => b i from by
        funext z; rcases z with a | j <;> rfl]
      exact hb i φ hφ

/-- The formula `∃ x, ⋀ φ ∈ t, φ(·, x)` attached to a finite set `t` of formulas in the parameters
`γ` and one further free variable, together with the computation of its meaning: it holds of a
valuation `w` exactly when some single element of the structure satisfies every member of `t`. -/
private theorem realize_finsetExs {L : FirstOrder.Language.{0, 0}} {γ : Type} {M : Type}
    [L.Structure M] (t : Finset (L.Formula (γ ⊕ Fin 1))) (w : γ → M) :
    (Formula.iExs (Fin 1)
        (Formula.iInf fun φ : {x // x ∈ t} => (φ : L.Formula (γ ⊕ Fin 1)))).Realize w ↔
      ∃ a : M, ∀ φ ∈ t, φ.Realize (Sum.elim w fun _ => a) := by
  rw [Formula.realize_iExs]
  simp only [Formula.realize_iInf, Subtype.forall]
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨i 0, fun φ hφ => ?_⟩
    have hi0 : (fun _ : Fin 1 => i 0) = i := funext fun j => by
      rw [Subsingleton.elim (0 : Fin 1) j]
    rw [hi0]
    exact hi φ hφ
  · rintro ⟨a, ha⟩
    exact ⟨fun _ => a, ha⟩

/-- **Finite satisfiability with parameters is preserved and reflected by elementary embeddings.**

If `g : X ↪ₑ[L] N` is an elementary embedding and `t` is a *finite* set of formulas with parameters
indexed by `γ` (interpreted in `X` via `v`) and one free variable, then `t` is realized by a single
element of `X` if and only if it is realized by a single element of `N`. -/
theorem exists_realize_finset_iff {L : FirstOrder.Language.{0, 0}} {γ : Type}
    {X N : Type} [L.Structure X] [L.Structure N] (g : X ↪ₑ[L] N) (v : γ → X)
    (t : Finset (L.Formula (γ ⊕ Fin 1))) :
    (∃ a : X, ∀ φ ∈ t, φ.Realize (Sum.elim v fun _ => a)) ↔
      ∃ b : N, ∀ φ ∈ t, φ.Realize (Sum.elim (fun i => g (v i)) fun _ => b) := by
  rw [← realize_finsetExs t v, ← realize_finsetExs (M := N) t fun i => g (v i)]
  exact (g.map_formula _ v).symm

end Submission.Morley
