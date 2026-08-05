/-
Ported from https://github.com/NoneMore/MorleyCategoricityTheorem
(`MorleyCategoricityTheorem/ModelTheory/OmegaStable.lean`), an ongoing formalisation of
Morley's categoricity theorem, released under the Apache 2.0 licence.  Pinned to
the same Lean v4.32.2 / Mathlib `905b95818e` as this workspace, so this is a
verbatim copy with only the import paths rewritten; the mathematics and the
proofs are the original author's, not ours.
-/
import Mathlib.Data.Set.Countable
import Submission.Morley.Port.Types

/-!
# Omega-stable theories

This file defines omega-stability using complete types over countable parameter sets.
-/

universe u v w

namespace FirstOrder

namespace Language

namespace Theory

variable {L : Language.{u, v}} (T : L.Theory)

/-- A theory is omega-stable if every space of complete positive finite-arity types over a
countable parameter set in a model of the theory is countable. -/
def IsOmegaStable : Prop :=
  ∀ (M : ModelType.{u, v, w} T) (A : Set M), A.Countable →
    ∀ n : ℕ, 1 ≤ n → Countable (L.CompleteTypeOver A (Fin n))

end Theory

end Language

end FirstOrder
