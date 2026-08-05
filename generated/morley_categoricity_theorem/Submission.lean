import Mathlib
import Submission.Helpers
import Submission.Morley.Port.All
import Submission.Morley.Indiscernibles
import Submission.Morley.Omitting
import Submission.Morley.Stable
import Submission.Morley.Prime
import Submission.Morley.Vaught
import Submission.Morley.Saturated
import Submission.Morley.EM
import Submission.Morley.TwoCardinal
import Submission.Morley.Transfer
import Submission.Morley.Realize
import Submission.Morley.Morleyization
import Submission.Morley.Bridge
import Submission.Morley.Chains
import Submission.Morley.Assembly
import Submission.Morley.PrimeExists
import Submission.Morley.OmegaTwoCardinal
import Submission.Morley.Rank
import Submission.Morley.StronglyMinimal
import Submission.Morley.PrimeBig
import Submission.Morley.IndepIndisc
import Submission.Morley.SatExists
import Submission.Morley.SatTypes
import Submission.Morley.SatStep
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
