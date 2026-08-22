/-
Copyright (c) 2026 Travis Darshan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Travis Darshan
-/
import Mathlib

/-!
# SU(2) Twisted-Cell Gauge Map

This file begins the finite-dimensional Lean formalization of the
twisted SU(2) Wilson-cell Hessian calculation.

It defines the Pauli-coordinate operators `A1`, `A2`, `A3`, `A4`,
the infinitesimal gauge-direction map `K`, its coordinate adjoint
`Kstar`, and proves the exact identity

`Kstar (K η) = 8 • η`.

This is the first algebraic input for the gauge projection
`P_gauge = (1/8) K Kstar`.
-/

set_option autoImplicit false

namespace YMFormalization
namespace SU2

/--
The real three-dimensional coordinate model for `su(2)` used in the
twisted-cell Hessian calculation.

A vector `η : Vec3` represents the Lie-algebra element
`i η · σ`.
-/
abbrev Vec3 := Fin 3 → ℝ

/--
The tangent space of one four-link cell:
four copies of the real `su(2)` coordinate space.
-/
abbrev CellTangent := Fin 4 → Vec3

/--
`A₁ = I - Ad_{Γ₁}` in the Pauli-coordinate convention.

At the twist-eater background this is

    diag(0, 2, 2).
-/
def A1 (η : Vec3) : Vec3 :=
  ![0, 2 * η 1, 2 * η 2]

/--
`A₂ = I - Ad_{Γ₂}`:

    diag(2, 0, 2).
-/
def A2 (η : Vec3) : Vec3 :=
  ![2 * η 0, 0, 2 * η 2]

/--
`A₃ = I - Ad_{Γ₃}`:

    diag(2, 2, 0).
-/
def A3 (η : Vec3) : Vec3 :=
  ![2 * η 0, 2 * η 1, 0]

/--
`A₄ = I - Ad_{Γ₄} = 0`, since `Γ₄ = I`.
-/
def A4 (_η : Vec3) : Vec3 :=
  ![0, 0, 0]

/--
Infinitesimal gauge-direction map for the twisted SU(2) cell:

    K η = (A₁η, A₂η, A₃η, A₄η).
-/
def K (η : Vec3) : CellTangent :=
  ![A1 η, A2 η, A3 η, A4 η]

/--
Coordinate formula for the adjoint of `K`.

Because each `Aμ` is a real symmetric diagonal operator,

    K* X = A₁ X₁ + A₂ X₂ + A₃ X₃ + A₄ X₄.
-/
def Kstar (X : CellTangent) : Vec3 :=
  A1 (X 0) + A2 (X 1) + A3 (X 2) + A4 (X 3)

/--
**First certified Yang–Mills algebra theorem.**

For the twisted SU(2) cell gauge map,

    K* K = 8 I.

This is the exact finite-dimensional identity used to construct
the orthogonal gauge projection

    P_gauge = (1/8) K K*.
-/
theorem Kstar_K (η : Vec3) :
    Kstar (K η) = (8 : ℝ) • η := by
  funext a
  fin_cases a <;>
    simp [Kstar, K, A1, A2, A3, A4] <;>
    ring

#print axioms Kstar_K

end SU2
end YMFormalization
