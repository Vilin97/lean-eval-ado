import Mathlib
import Submission.Helpers
import Submission.Morley.Port.All
import Submission.Morley.Indiscernibles
import Submission.Morley.Omitting
import Submission.Morley.Stable
import Submission.Morley.Prime
import Submission.Morley.Ramsey

open Cardinal

namespace Submission

theorem morley_categoricity_theorem (L : FirstOrder.Language.{0, 0}) (hL : L.card ≤ ℵ₀)
    (T : L.Theory) (hT : T.IsComplete)
    (hInf : ∀ M : FirstOrder.Language.Theory.ModelType.{0, 0, 0} T, Infinite M)
    {κ : Cardinal.{0}} (hκ : ℵ₀ < κ) (hcat : κ.Categorical T)
    {μ : Cardinal.{0}} (hμ : ℵ₀ < μ) :
    μ.Categorical T := by
  sorry

end Submission
