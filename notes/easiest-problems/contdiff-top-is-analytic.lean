import Mathlib
open scoped ContDiff
-- The bare `⊤` in `ContDiff ℝ ⊤ f` is `ω` (analytic), not `C^∞`.
example : (⊤ : ℕ∞ω) = ω := rfl
example (f : ℝ → ℝ) : ContDiff ℝ ⊤ f ↔ ContDiff ℝ ω f := Iff.rfl
-- `ω` is strictly stronger than the ascribed `(⊤ : ℕ∞)` = `C^∞`.
example (f : ℝ → ℝ) (h : ContDiff ℝ ⊤ f) : ContDiff ℝ (⊤ : ℕ∞) f := h.of_le (by simp)
example : ((⊤ : ℕ∞) : ℕ∞ω) ≠ (⊤ : ℕ∞ω) := by decide
-- and analytic really does imply analyticity, so the knot files quantify over analytic curves:
example (f : ℝ → ℝ) (h : ContDiff ℝ ⊤ f) : AnalyticOnNhd ℝ f Set.univ := h.analyticOnNhd
