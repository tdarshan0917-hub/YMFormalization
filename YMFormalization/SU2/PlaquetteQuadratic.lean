/-
Copyright (c) 2026 Travis Darshan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Travis Darshan
-/

import YMFormalization.SU2.PlaquetteKernel
import Mathlib

/-!
# Exact Quadratic Form of the Twisted SU(2) Plaquette Operator

The certified operator identity

`Lstar L = 8 P_perp`

is converted here into the corresponding Euclidean quadratic-form
identity.

We deliberately use the explicit finite-dimensional pairings defined
in `PlaquetteAdjoint.lean`, rather than Lean's default function norm.

The main result is

`<L X, L X> = 8 <X, P_perp X>`.

On the physical slice `P_perp X = X`, this becomes

`<L X, L X> = 8 <X, X>`.
-/

set_option autoImplicit false

namespace YMFormalization
namespace SU2

/--
Euclidean quadratic form on the four-link cell tangent space.
-/
def cellQuadratic (X : CellTangent) : ℝ :=
  cellPairing X X

/--
Euclidean quadratic form on the six plaquette components.
-/
def plaquetteQuadratic (Y : PlaquetteTangent) : ℝ :=
  plaquettePairing Y Y

/--
The cell pairing is homogeneous in its second argument.
-/
theorem cellPairing_smul_right
    (c : ℝ) (X Y : CellTangent) :
    cellPairing X (c • Y) =
      c * cellPairing X Y := by
  simp [cellPairing, vecPairing]
  ring

/--
**Exact quadratic form identity.**

For every cell tangent vector,

`<L X, L X> = 8 <X, P_perp X>`.
-/
theorem plaquetteQuadratic_linearization_eq_eight_physical
    (X : CellTangent) :
    plaquetteQuadratic (plaquetteLinearization X) =
      (8 : ℝ) * cellPairing X (physicalProjection X) := by
  unfold plaquetteQuadratic
  rw [plaquetteAdjoint_spec]
  rw [plaquetteAdjoint_linearization_eq_eight_physicalProjection]
  rw [cellPairing_smul_right]

/--
**Exact physical-slice quadratic identity.**

If `X` is already physical, then

`<L X, L X> = 8 <X, X>`.
-/
theorem plaquetteQuadratic_linearization_of_physical
    (X : CellTangent)
    (hX : physicalProjection X = X) :
    plaquetteQuadratic (plaquetteLinearization X) =
      (8 : ℝ) * cellQuadratic X := by
  rw [plaquetteQuadratic_linearization_eq_eight_physical]
  rw [hX]
  rfl

/--
Gauge directions have zero plaquette quadratic form.
-/
theorem plaquetteQuadratic_linearization_K
    (η : Vec3) :
    plaquetteQuadratic (plaquetteLinearization (K η)) = 0 := by
  rw [plaquetteLinearization_K]
  simp [plaquetteQuadratic, plaquettePairing, vecPairing]

#print axioms cellPairing_smul_right
#print axioms plaquetteQuadratic_linearization_eq_eight_physical
#print axioms plaquetteQuadratic_linearization_of_physical
#print axioms plaquetteQuadratic_linearization_K

end SU2
end YMFormalization
