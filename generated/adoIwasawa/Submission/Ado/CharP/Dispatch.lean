import Submission.Ado.Main

/-!
# Reducing Ado–Iwasawa to the two characteristics

Every field has characteristic `0` or a prime characteristic `p`. The
characteristic-zero case of Ado's theorem is
`Submission.Ado.hasFaithfulFinRep_charZero` (proved, and accepted by comparator as
the benchmark problem `adoCharZero`). This file packages the case split, so that
finishing `adoIwasawa` requires only the positive-characteristic case.
-/

universe u

namespace Submission.Ado

variable {K L : Type u} [Field K] [LieRing L] [LieAlgebra K L]

/-- **Top-level dispatch for Ado–Iwasawa.** Given the theorem in every positive
characteristic, it follows in every characteristic: the characteristic-zero case is
`hasFaithfulFinRep_charZero`. -/
theorem hasFaithfulFinRep_of_charP [FiniteDimensional K L]
    (hp : ∀ (p : ℕ) (_ : Fact p.Prime) (_ : CharP K p), HasFaithfulFinRep K L) :
    HasFaithfulFinRep K L := by
  haveI hc : CharP K (ringChar K) := ringChar.charP K
  rcases CharP.char_is_prime_or_zero K (ringChar K) with h | h
  · exact hp _ ⟨h⟩ hc
  · haveI : CharP K 0 := h ▸ hc
    haveI : CharZero K := CharP.charP_to_charZero K
    exact hasFaithfulFinRep_charZero

end Submission.Ado
