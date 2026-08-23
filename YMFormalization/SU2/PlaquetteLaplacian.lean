/-
Copyright (c) 2026 Travis Darshan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Travis Darshan
-/

import YMFormalization.SU2.PlaquetteAdjoint
import Mathlib

/-!
# Twisted SU(2) Plaquette Laplacian

This file proves the central finite-dimensional structural identity
for the twisted SU(2) root cell.

With

`L_{μν}(X) = A_ν X_μ - A_μ X_ν`

and `Lstar` the explicit Euclidean adjoint constructed in
`PlaquetteAdjoint.lean`, we prove

`Lstar (L X) = 8 • P_perp X`.

Equivalently,

`Lstar L = 8 P_perp`.

Thus the plaquette quadratic form vanishes exactly along infinitesimal
gauge directions and acts with eigenvalue `8` on the complementary
physical slice.
-/

set_option autoImplicit false

namespace YMFormalization
namespace SU2

/--
**Central twisted-cell operator identity.**

For every four-link tangent vector `X`,

`Lstar (L X) = 8 • P_perp X`.

Here `P_perp = I - (1/8) K Kstar`.

This is the exact finite-dimensional identity underlying the
twisted-cell Wilson Hessian calculation.
-/
theorem plaquetteAdjoint_linearization_eq_eight_physicalProjection
    (X : CellTangent) :
    plaquetteAdjoint (plaquetteLinearization X) =
      (8 : ℝ) • physicalProjection X := by
  funext μ
  fin_cases μ <;>
    funext a <;>
    fin_cases a <;>
    simp [plaquetteAdjoint, plaquetteLinearization,
      plaquetteMu, plaquetteNu, cellA,
      physicalProjection, gaugeProjection,
      K, Kstar, A1, A2, A3, A4,
      Matrix.vecHead, Matrix.vecTail, Function.comp_apply] <;>
    ring

/--
On the physical slice, `Lstar L` acts exactly as multiplication by `8`.
-/
theorem plaquetteAdjoint_linearization_of_physical
    (X : CellTangent)
    (hX : physicalProjection X = X) :
    plaquetteAdjoint (plaquetteLinearization X) =
      (8 : ℝ) • X := by
  rw [plaquetteAdjoint_linearization_eq_eight_physicalProjection, hX]

/--
On an infinitesimal gauge direction, `Lstar L` vanishes.
-/
theorem plaquetteAdjoint_linearization_K (η : Vec3) :
    plaquetteAdjoint (plaquetteLinearization (K η)) = 0 := by
  rw [plaquetteLinearization_K]
  exact plaquetteAdjoint_zero

#print axioms plaquetteAdjoint_linearization_eq_eight_physicalProjection
#print axioms plaquetteAdjoint_linearization_of_physical
#print axioms plaquetteAdjoint_linearization_K

end SU2
end YMFormalization
