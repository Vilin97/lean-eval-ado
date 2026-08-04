/-
Ported from https://github.com/Komyyy/ado (`Ado/ForMathlib/LieIdealCoe.lean`),
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
public import Mathlib.Algebra.Lie.Ideal

public section

namespace LieIdeal

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

lemma coe_bracket (I : LieIdeal R L) (x y : I) : (↑⁅x, y⁆ : L) = ⁅(↑x : L), (↑y : L)⁆ := by
  simp

end LieIdeal
