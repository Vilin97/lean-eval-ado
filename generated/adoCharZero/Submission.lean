import ChallengeDeps
import Submission.Helpers
import Submission.Ado.Basic
import Submission.Ado.DerivRep
import Submission.Ado.Easy
import Submission.Ado.Embed
import Submission.Ado.Closure
import Submission.Ado.Filtration
import Submission.Ado.Truncation
import Submission.Ado.AugIdeal
import Submission.Ado.EnvDeriv
import Submission.Ado.DerivedRadical
import Submission.Ado.PBW.Basis
import Submission.Ado.Nilradical
import Submission.Ado.Casimir
import Submission.Ado.Weyl
import Submission.Ado.Levi
import Submission.Ado.Solvable
import Submission.Ado.Main

open LeanEval.RepresentationTheory.AdoIwasawa

universe u v

variable {K L : Type u} [Field K] [LieRing L] [LieAlgebra K L]

namespace Submission

theorem adoCharZero [CharZero K] [FiniteDimensional K L] :
    ∃ (V : Type u) (_ : AddCommGroup V) (_ : Module K V) (_ : FiniteDimensional K V)
      (ρ : L →ₗ⁅K⁆ Module.End K V), Function.Injective ρ :=
  Submission.Ado.hasFaithfulFinRep_charZero

end Submission
