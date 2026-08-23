/-
Copyright (c) 2026 Travis Darshan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Travis Darshan
-/

import YMFormalization.SU2.PhysicalProjection
import Mathlib

/-!
# Plaquette Linearization for the Twisted SU(2) Cell

This file introduces the six independent plaquettes of a four-link cell
and the linearized plaquette operator

`L_{μν}(X) = A_ν X_μ - A_μ X_ν`.

The first structural theorem proves that infinitesimal gauge directions
are annihilated:

`L (K η) = 0`.

This is the beginning of the exact twisted-cell complex whose central
target is

`L* L = 8 P_perp`.
-/

set_option autoImplicit false

namespace YMFormalization
namespace SU2

/--
The six independent plaquette components of a four-direction cell.
-/
abbrev PlaquetteTangent := Fin 6 → Vec3

/--
Uniform form of the four twisted adjoint-difference operators.

The Lean indices `0,1,2,3` correspond respectively to the manuscript's
`A₁,A₂,A₃,A₄`.
-/
def cellA (μ : Fin 4) (η : Vec3) : Vec3 :=
  ![A1 η, A2 η, A3 η, A4 η] μ

/--
Lower direction index of each of the six independent plaquettes:

`01, 02, 03, 12, 13, 23`.
-/
def plaquetteMu : Fin 6 → Fin 4 :=
  ![0, 0, 0, 1, 1, 2]

/--
Upper direction index of each of the six independent plaquettes:

`01, 02, 03, 12, 13, 23`.
-/
def plaquetteNu : Fin 6 → Fin 4 :=
  ![1, 2, 3, 2, 3, 3]

/--
Each stored plaquette has its lower direction strictly below its upper
direction.
-/
theorem plaquetteMu_lt_nu (p : Fin 6) :
    plaquetteMu p < plaquetteNu p := by
  fin_cases p <;>
    decide

/--
The original gauge map `K` is exactly the four-component map assembled
from `cellA`.
-/
theorem K_apply_eq_cellA (η : Vec3) (μ : Fin 4) :
    K η μ = cellA μ η := by
  fin_cases μ <;>
    rfl

/--
Linearized plaquette map

`L_{μν}(X) = A_ν X_μ - A_μ X_ν`

on the six independent plaquettes.
-/
def plaquetteLinearization (X : CellTangent) : PlaquetteTangent :=
  fun p =>
    cellA (plaquetteNu p) (X (plaquetteMu p)) -
      cellA (plaquetteMu p) (X (plaquetteNu p))

/--
The linearized plaquette curvature of the zero tangent vector vanishes.
-/
theorem plaquetteLinearization_zero :
    plaquetteLinearization (0 : CellTangent) = 0 := by
  funext p
  fin_cases p <;>
    funext a <;>
    fin_cases a <;>
    simp [plaquetteLinearization, plaquetteMu, plaquetteNu,
      cellA, A1, A2, A3, A4]

/--
**Gauge directions lie in the kernel of the linearized plaquette map.**

For every infinitesimal gauge parameter `η`,

`L (K η) = 0`.

This is the finite-dimensional linearized gauge-invariance statement
for the twisted SU(2) cell.
-/
theorem plaquetteLinearization_K (η : Vec3) :
    plaquetteLinearization (K η) = 0 := by
  funext p
  fin_cases p <;>
    funext a <;>
    fin_cases a <;>
    simp [plaquetteLinearization, plaquetteMu, plaquetteNu,
      cellA, K, A1, A2, A3, A4] <;>
    ring

#print axioms plaquetteMu_lt_nu
#print axioms K_apply_eq_cellA
#print axioms plaquetteLinearization_zero
#print axioms plaquetteLinearization_K

end SU2
end YMFormalization
