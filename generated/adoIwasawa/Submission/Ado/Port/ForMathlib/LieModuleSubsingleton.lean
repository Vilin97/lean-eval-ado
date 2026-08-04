/-
Ported from https://github.com/Komyyy/ado (`Ado/ForMathlib/LieModuleSubsingleton.lean`),
an ongoing human-written formalisation of Ado's theorem by Miyahara Kō,
released under the Apache 2.0 licence.  This file is a mechanical port of that
work to the Mathlib revision used by this workspace; the mathematics and the
proofs are the original author's, not ours.
-/
/-
Copyright (c) 2026 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō
-/
module
public import Mathlib.Algebra.Lie.OfAssociative

public section

variable {R L M : Type*}

variable [CommRing R] [LieRing L] [LieAlgebra R L]
variable [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

namespace LieModule

instance [Subsingleton L] : IsFaithful R L M where
  injective_toEnd := Function.injective_of_subsingleton _

end LieModule
