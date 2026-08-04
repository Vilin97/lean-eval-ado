/-
Ported from https://github.com/Komyyy/ado (`Ado/ForMathlib/ModuleRank.lean`),
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
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

public section

open Module

namespace Submodule

@[congr]
lemma finrank_congr {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    {p q : Submodule R M} (h : p = q) : finrank R p = finrank R q :=
  (LinearEquiv.ofEq p q h).finrank_eq

lemma finrank_lt_iff {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {s : Submodule K V} : finrank K s < finrank K V ↔ s < ⊤ where
  mp := lt_top_of_finrank_lt_finrank
  mpr := finrank_lt ∘ ne_top_of_lt

end Submodule
