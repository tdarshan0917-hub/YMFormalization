/-
Copyright (c) 2026 Travis Darshan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Travis Darshan
-/

import YMFormalization.SU2.PlaquetteQuadratic
import Mathlib

/-!
# Linearized Wilson Quadratic Operator

The twisted-cell plaquette linearization satisfies

`Lstar L = 8 P_perp`

and

`<L X, L X> = 8 <X, P_perp X>`.

For a real coupling `β`, this file defines the operator and quadratic
form obtained by multiplying those certified plaquette expressions by
`β`.

Importantly, this file does **not** yet identify these objects with the
second derivative of the nonlinear Wilson action.  That Hessian bridge
will be proved separately.

The principal operator identity here is

`β Lstar L = 8 β P_perp`.
-/

set_option autoImplicit false

namespace YMFormalization
namespace SU2

/--
The linearized Wilson quadratic operator at coupling `β`:

`β Lstar L`.
-/
def linearizedWilsonOperator
    (β : ℝ) (X : CellTangent) : CellTangent :=
  β • plaquetteAdjoint (plaquetteLinearization X)

/--
The associated scalar quadratic form:

`β <L X, L X>`.
-/
def linearizedWilsonQuadratic
    (β : ℝ) (X : CellTangent) : ℝ :=
  β * plaquetteQuadratic (plaquetteLinearization X)

/--
**Exact linearized Wilson operator identity.**

`β Lstar L = 8 β P_perp`.
-/
theorem linearizedWilsonOperator_eq_eight_beta_physical
    (β : ℝ) (X : CellTangent) :
    linearizedWilsonOperator β X =
      (8 * β : ℝ) • physicalProjection X := by
  unfold linearizedWilsonOperator
  rw [plaquetteAdjoint_linearization_eq_eight_physicalProjection]
  simp [smul_smul, mul_comm]

/--
On the physical slice, the linearized Wilson operator acts as
multiplication by `8β`.
-/
theorem linearizedWilsonOperator_of_physical
    (β : ℝ) (X : CellTangent)
    (hX : physicalProjection X = X) :
    linearizedWilsonOperator β X =
      (8 * β : ℝ) • X := by
  rw [linearizedWilsonOperator_eq_eight_beta_physical, hX]

/--
Gauge directions are zero modes of the linearized Wilson operator.
-/
theorem linearizedWilsonOperator_K
    (β : ℝ) (η : Vec3) :
    linearizedWilsonOperator β (K η) = 0 := by
  rw [linearizedWilsonOperator_eq_eight_beta_physical]
  rw [physicalProjection_K]
  simp

/--
**Exact linearized Wilson quadratic identity.**

`β <L X,L X> = 8β <X,P_perp X>`.
-/
theorem linearizedWilsonQuadratic_eq_eight_beta_physical
    (β : ℝ) (X : CellTangent) :
    linearizedWilsonQuadratic β X =
      (8 * β) * cellPairing X (physicalProjection X) := by
  unfold linearizedWilsonQuadratic
  rw [plaquetteQuadratic_linearization_eq_eight_physical]
  ring

/--
On the physical slice,

`β <L X,L X> = 8β <X,X>`.
-/
theorem linearizedWilsonQuadratic_of_physical
    (β : ℝ) (X : CellTangent)
    (hX : physicalProjection X = X) :
    linearizedWilsonQuadratic β X =
      (8 * β) * cellQuadratic X := by
  rw [linearizedWilsonQuadratic_eq_eight_beta_physical, hX]
  simp [cellQuadratic]

/--
Gauge directions have zero linearized Wilson quadratic form.
-/
theorem linearizedWilsonQuadratic_K
    (β : ℝ) (η : Vec3) :
    linearizedWilsonQuadratic β (K η) = 0 := by
  unfold linearizedWilsonQuadratic
  rw [plaquetteQuadratic_linearization_K]
  ring

#print axioms linearizedWilsonOperator_eq_eight_beta_physical
#print axioms linearizedWilsonOperator_of_physical
#print axioms linearizedWilsonOperator_K
#print axioms linearizedWilsonQuadratic_eq_eight_beta_physical
#print axioms linearizedWilsonQuadratic_of_physical
#print axioms linearizedWilsonQuadratic_K

end SU2
end YMFormalization
