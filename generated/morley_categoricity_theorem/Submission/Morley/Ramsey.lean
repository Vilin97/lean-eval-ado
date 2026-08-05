import Mathlib

/-!
# Infinite Ramsey theory

The main result of this file is `Submission.Morley.exists_infinite_monochromatic`: any finite
colouring of the `n`-element subsets of an infinite set admits an infinite monochromatic subset.

The proof follows the classical ultrafilter argument.  Fix a non-principal ultrafilter `U` on the
(infinite) index type `α` — concretely, `Filter.hyperfilter α`.  Since the set of colours is finite,
every map `α → β` has a well-defined `U`-limit.  Starting from the given colouring (extended to a
total function on `Finset α`) we build a family of derived colourings `E k` by
`E (k+1) s = U-lim_x (E k (insert x s))`, and then greedily construct a sequence of points, each of
which is "generic" for all the previously constructed finite configurations.  Any `n`-element subset
of the resulting set then peels off one point at a time, showing its colour equals `E n ∅`.
-/

universe u v

namespace Submission.Morley

open Filter

/-- **Infinite Ramsey.** Any finite colouring of the `n`-element subsets of an infinite
set admits an infinite monochromatic subset. -/
theorem exists_infinite_monochromatic {α : Type u} [Infinite α] (n : ℕ)
    {β : Type v} [Finite β] (c : {s : Finset α // s.card = n} → β) :
    ∃ S : Set α, S.Infinite ∧ ∃ b : β,
      ∀ s : {s : Finset α // s.card = n}, ↑(s : Finset α) ⊆ S → c s = b := by
  classical
  -- Since `α` is infinite it has `n`-element subsets, so the colour type is nonempty.
  obtain ⟨s₀, hs₀⟩ := Infinite.exists_subset_card_eq α n
  have hβ : Nonempty β := ⟨c ⟨s₀, hs₀⟩⟩
  -- Extend `c` to a total colouring of all finite subsets.
  obtain ⟨C, hCn⟩ : ∃ C : Finset α → β, ∀ (s : Finset α) (h : s.card = n), C s = c ⟨s, h⟩ :=
    ⟨fun s => if h : s.card = n then c ⟨s, h⟩ else Classical.arbitrary β, fun _ h => dif_pos h⟩
  -- A non-principal ultrafilter on `α`.
  have hU : (hyperfilter α : Filter α) ≤ Filter.cofinite := hyperfilter_le_cofinite
  -- Ultrafilter limits of maps into the finite type `β`.
  have hlim : ∀ f : α → β, ∃ b : β, ∀ᶠ x in (hyperfilter α : Filter α), f x = b := fun f =>
    Ultrafilter.eventually_exists_iff.mp (Filter.Eventually.of_forall fun x => ⟨f x, rfl⟩)
  choose L hL using hlim
  -- The derived colourings: `E k` is used to colour `k`-codimensional configurations.
  obtain ⟨E, hE0, hEs⟩ : ∃ E : ℕ → Finset α → β, E 0 = C ∧
      ∀ (k : ℕ) (s : Finset α), E (k + 1) s = L fun x => E k (insert x s) :=
    ⟨fun k => Nat.rec (motive := fun _ => Finset α → β) C
      (fun _ e s => L fun x => e (insert x s)) k, rfl, fun _ _ => rfl⟩
  -- Given a finite set `t`, almost every point is generic over every subset of `t`.
  have hgood : ∀ t : Finset α, ∃ x : α, x ∉ t ∧
      ∀ s ∈ t.powerset, ∀ k ∈ Finset.range (n + 1), E k (insert x s) = E (k + 1) s := by
    intro t
    have h1 : ∀ᶠ x in (hyperfilter α : Filter α), x ∉ t := hU t.finite_toSet.compl_mem_cofinite
    have h2 : ∀ᶠ x in (hyperfilter α : Filter α), ∀ s ∈ t.powerset, ∀ k ∈ Finset.range (n + 1),
        E k (insert x s) = E (k + 1) s := by
      rw [Filter.eventually_all_finset]
      intro s _
      rw [Filter.eventually_all_finset]
      intro k _
      simpa only [hEs k s] using hL fun x => E k (insert x s)
    exact (h1.and h2).exists
  choose g hg1 hg2 using hgood
  -- The nested sequence of finite sets; the `j`-th chosen point is `g (T j)`.
  obtain ⟨T, hT0, hTs⟩ : ∃ T : ℕ → Finset α, T 0 = ∅ ∧ ∀ j, T (j + 1) = insert (g (T j)) (T j) :=
    ⟨fun j => Nat.rec (motive := fun _ => Finset α) ∅ (fun _ t => insert (g t) t) j, rfl, fun _ =>
      rfl⟩
  have hmono : Monotone T := by
    apply monotone_nat_of_le_succ
    intro j
    rw [hTs j]
    exact Finset.subset_insert _ _
  have hmem : ∀ j, g (T j) ∈ T (j + 1) := fun j => by rw [hTs j]; exact Finset.mem_insert_self _ _
  -- Every subset of some `T j` of size at most `n` has the same derived colour as `∅`.
  have main : ∀ j : ℕ, ∀ s : Finset α, s ⊆ T j → s.card ≤ n → E (n - s.card) s = E n ∅ := by
    intro j
    induction j with
    | zero =>
      intro s hs _
      rw [hT0, Finset.subset_empty] at hs
      subst hs
      simp
    | succ j ih =>
      intro s hs hcard
      rw [hTs j, Finset.subset_insert_iff] at hs
      by_cases hgj : g (T j) ∈ s
      · have hpos : 1 ≤ s.card := Finset.card_pos.mpr ⟨_, hgj⟩
        have hcard' : (s.erase (g (T j))).card = s.card - 1 := Finset.card_erase_of_mem hgj
        have key := hg2 (T j) (s.erase (g (T j))) (Finset.mem_powerset.mpr hs) (n - s.card)
          (Finset.mem_range.mpr (by omega))
        rw [Finset.insert_erase hgj] at key
        have hih := ih (s.erase (g (T j))) hs (by omega)
        rw [hcard'] at hih
        rw [key, show n - s.card + 1 = n - (s.card - 1) by omega, hih]
      · rw [Finset.erase_eq_of_notMem hgj] at hs
        exact ih s hs hcard
  -- The sequence of chosen points is injective, so its range is infinite.
  obtain ⟨a, haT⟩ : ∃ a : ℕ → α, ∀ j, a j = g (T j) := ⟨fun j => g (T j), fun _ => rfl⟩
  have hmem' : ∀ j, a j ∈ T (j + 1) := fun j => by rw [haT j]; exact hmem j
  have hnot : ∀ j, a j ∉ T j := fun j => by rw [haT j]; exact hg1 (T j)
  have hinj : Function.Injective a := by
    intro i j hij
    rcases lt_trichotomy i j with h | h | h
    · exact absurd (by rw [← hij]; exact hmono (by omega) (hmem' i)) (hnot j)
    · exact h
    · exact absurd (by rw [hij]; exact hmono (by omega) (hmem' j)) (hnot i)
  -- Every finite subset of the range is contained in some `T j`.
  have hcover : ∀ s : Finset α, (↑s : Set α) ⊆ Set.range a → ∃ j, s ⊆ T j := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact fun _ => ⟨0, by simp⟩
    | @insert x s _ ih =>
      intro hsub
      have hxr : x ∈ Set.range a := hsub (show x ∈ (↑(insert x s) : Set α) by simp)
      have hsr : (↑s : Set α) ⊆ Set.range a :=
        (Finset.coe_subset.mpr (Finset.subset_insert x s)).trans hsub
      obtain ⟨j, hj⟩ := ih hsr
      obtain ⟨i, hi⟩ := hxr
      refine ⟨max j (i + 1), fun y hy => ?_⟩
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact hmono (le_max_right _ _) (by rw [← hi]; exact hmem' i)
      · exact hmono (le_max_left _ _) (hj hy)
  refine ⟨Set.range a, Set.infinite_range_of_injective hinj, E n ∅, ?_⟩
  rintro ⟨s, hsn⟩ hsub
  obtain ⟨j, hj⟩ := hcover s hsub
  have h := main j s hj hsn.le
  rwa [hsn, Nat.sub_self, hE0, hCn s hsn] at h

end Submission.Morley
