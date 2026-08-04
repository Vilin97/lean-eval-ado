/-
Ported from https://github.com/Komyyy/ado (`Ado/ForMathlib/LieHom.lean`),
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
public import Submission.Ado.Port.ForMathlib.LieIdealOf

@[expose] public section

open Function LieIdeal

namespace LieHom

def lieIdealComap {R L L₂ : Type*} [CommRing R]
    [LieRing L] [LieAlgebra R L] [LieRing L₂] [LieAlgebra R L₂]
    (f : L →ₗ⁅R⁆ L₂) (q : LieIdeal R L₂) : comap f q →ₗ⁅R⁆ q where
  toLinearMap := LinearMap.submoduleComap f.toLinearMap q
  map_lie' {_ _} := Subtype.ext f.map_lie'

@[simp]
lemma lieIdealComap_apply_coe {R L L₂ : Type*} [CommRing R]
    [LieRing L] [LieAlgebra R L] [LieRing L₂] [LieAlgebra R L₂]
    (f : L →ₗ⁅R⁆ L₂) (q : LieIdeal R L₂) (x : comap f q) :
    (lieIdealComap f q x : L₂) = f x :=
  rfl

@[simp]
lemma lieIdealComap_surjective_of_surjective {R L L₂ : Type*} [CommRing R]
    [LieRing L] [LieAlgebra R L] [LieRing L₂] [LieAlgebra R L₂]
    (f : L →ₗ⁅R⁆ L₂) (q : LieIdeal R L₂) (hf : Surjective f) : Surjective (lieIdealComap f q) :=
  LinearMap.submoduleComap_surjective_of_surjective f.toLinearMap q hf

@[simp]
lemma lieIdealComap_ker {R L L₂ : Type*} [CommRing R]
    [LieRing L] [LieAlgebra R L] [LieRing L₂] [LieAlgebra R L₂]
    (f : L →ₗ⁅R⁆ L₂) (q : LieIdeal R L₂) :
    ker (lieIdealComap f q) = lieIdealOf (ker f) (comap f q) := by
  ext; simp [Subtype.ext_iff]

end LieHom
