/-
Copyright (c) 2026 Travis Darshan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Travis Darshan
-/

import YMFormalization.SU2.PlaquetteLinearization
import Mathlib

/-!
# Explicit Adjoint of the Twisted SU(2) Plaquette Linearization

For the six plaquettes

`01, 02, 03, 12, 13, 23`

the linearized plaquette map is

`L_{μν}(X) = A_ν X_μ - A_μ X_ν`.

This file defines the corresponding coordinate adjoint `Lstar` and
proves directly, with the standard Euclidean pairings, that

`<L X, Y> = <X, Lstar Y>`.

The next target is the structural identity

`Lstar (L X) = 8 • P_perp X`.
-/

set_option autoImplicit false

namespace YMFormalization
namespace SU2

/--
Standard Euclidean pairing on the three real Pauli coordinates.
-/
def vecPairing (x y : Vec3) : ℝ :=
  x 0 * y 0 + x 1 * y 1 + x 2 * y 2

/--
Standard product pairing on the four-link cell tangent space.
-/
def cellPairing (X Y : CellTangent) : ℝ :=
  vecPairing (X 0) (Y 0) +
  vecPairing (X 1) (Y 1) +
  vecPairing (X 2) (Y 2) +
  vecPairing (X 3) (Y 3)

/--
Standard product pairing on the six plaquette tangent components.
-/
def plaquettePairing (X Y : PlaquetteTangent) : ℝ :=
  vecPairing (X 0) (Y 0) +
  vecPairing (X 1) (Y 1) +
  vecPairing (X 2) (Y 2) +
  vecPairing (X 3) (Y 3) +
  vecPairing (X 4) (Y 4) +
  vecPairing (X 5) (Y 5)

/--
Explicit coordinate adjoint of the six-plaquette linearization.

With plaquettes ordered as

`01, 02, 03, 12, 13, 23`,

the four link components are obtained by collecting every occurrence
of that link in `L_{μν}` with the appropriate sign.
-/
def plaquetteAdjoint (Y : PlaquetteTangent) : CellTangent :=
  ![
    cellA 1 (Y 0) + cellA 2 (Y 1) + cellA 3 (Y 2),

    -cellA 0 (Y 0) + cellA 2 (Y 3) + cellA 3 (Y 4),

    -cellA 0 (Y 1) - cellA 1 (Y 3) + cellA 3 (Y 5),

    -cellA 0 (Y 2) - cellA 1 (Y 4) - cellA 2 (Y 5)
  ]

/--
The explicit coordinate formula `plaquetteAdjoint` is genuinely
adjoint to `plaquetteLinearization` for the standard finite-dimensional
Euclidean pairings:

`<L X, Y> = <X, Lstar Y>`.
-/
theorem plaquetteAdjoint_spec
    (X : CellTangent) (Y : PlaquetteTangent) :
    plaquettePairing (plaquetteLinearization X) Y =
      cellPairing X (plaquetteAdjoint Y) := by
  simp [plaquettePairing, cellPairing, vecPairing,
    plaquetteAdjoint, plaquetteLinearization,
    plaquetteMu, plaquetteNu, cellA,
    A1, A2, A3, A4]
  ring

/--
The adjoint sends the zero plaquette tangent vector to zero.
-/
theorem plaquetteAdjoint_zero :
    plaquetteAdjoint (0 : PlaquetteTangent) = 0 := by
  funext μ
  fin_cases μ <;>
    funext a <;>
    fin_cases a <;>
    simp [plaquetteAdjoint, cellA, A1, A2, A3, A4]

#print axioms plaquetteAdjoint_spec
#print axioms plaquetteAdjoint_zero

end SU2
end YMFormalization
