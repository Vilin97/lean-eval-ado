/-
Ported from https://github.com/Komyyy/ado (`Ado/ForMathlib/LieModulePUnit.lean`),
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
public import Mathlib.Algebra.Lie.Basic

@[expose] public section

variable {R L : Type*}

namespace PUnit

instance : Bracket L PUnit where
  bracket _ _ := unit

-- Lie 代数でも Lie 加群でも変わらないので `lie_module_bracket` とは書かない
@[simp]
lemma bracket_eq (x : L) (m : PUnit) : ⁅x, m⁆ = unit :=
  rfl

instance [LieRing L] : LieRingModule L PUnit where
  add_lie _ _ _ := by subsingleton
  lie_add _ _ _ := by subsingleton
  leibniz_lie _ _ _ := by subsingleton

instance [CommRing R] [LieRing L] [LieAlgebra R L] : LieModule R L PUnit where
  smul_lie _ _ _ := by subsingleton
  lie_smul _ _ _ := by subsingleton

end PUnit
