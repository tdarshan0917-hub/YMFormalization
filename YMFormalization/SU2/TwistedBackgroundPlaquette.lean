/-
Copyright (c) 2026 Travis Darshan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Travis Darshan
-/

import YMFormalization.SU2.WilsonQuadratic
import Mathlib

/-!
# Exact Twisted Background Plaquettes

For the Pauli twist-eater background

`Γ₁ = iσ₁`, `Γ₂ = iσ₂`, `Γ₃ = iσ₃`, `Γ₄ = I`

the center twists are

`z₁₂ = z₁₃ = z₂₃ = -1`

and

`z₁₄ = z₂₄ = z₃₄ = 1`.

This file proves exactly that all six twisted background plaquettes
are the identity matrix.

No Taylor expansion or Hessian statement is used here.
-/

set_option autoImplicit false

namespace YMFormalization
namespace SU2

/--
`Γ₄` is the identity matrix.
-/
theorem gamma4_eq_one :
    gamma4 = (1 : Mat2C) := by
  funext i j
  fin_cases i <;>
    fin_cases j <;>
    simp [gamma4]

/--
`Γ₄⁻¹` is the identity matrix.
-/
theorem gamma4Inv_eq_one :
    gamma4Inv = (1 : Mat2C) := by
  rw [gamma4Inv, gamma4_eq_one]

/-!
## Spatial twist-eater anticommutation
-/

theorem gamma1_mul_gamma2_eq_neg :
    gamma1 * gamma2 = -(gamma2 * gamma1) := by
  funext i j
  fin_cases i <;> fin_cases j
  · change (gamma1 * gamma2) 0 0 =
      -((gamma2 * gamma1) 0 0)
    rw [mat2_mul_00, mat2_mul_00]
    simp [gamma1, gamma2, Complex.I_mul_I] <;> ring
  · change (gamma1 * gamma2) 0 1 =
      -((gamma2 * gamma1) 0 1)
    rw [mat2_mul_01, mat2_mul_01]
    simp [gamma1, gamma2, Complex.I_mul_I] <;> ring
  · change (gamma1 * gamma2) 1 0 =
      -((gamma2 * gamma1) 1 0)
    rw [mat2_mul_10, mat2_mul_10]
    simp [gamma1, gamma2, Complex.I_mul_I] <;> ring
  · change (gamma1 * gamma2) 1 1 =
      -((gamma2 * gamma1) 1 1)
    rw [mat2_mul_11, mat2_mul_11]
    simp [gamma1, gamma2, Complex.I_mul_I] <;> ring

theorem gamma1_mul_gamma3_eq_neg :
    gamma1 * gamma3 = -(gamma3 * gamma1) := by
  funext i j
  fin_cases i <;> fin_cases j
  · change (gamma1 * gamma3) 0 0 =
      -((gamma3 * gamma1) 0 0)
    rw [mat2_mul_00, mat2_mul_00]
    simp [gamma1, gamma3, Complex.I_mul_I] <;> ring
  · change (gamma1 * gamma3) 0 1 =
      -((gamma3 * gamma1) 0 1)
    rw [mat2_mul_01, mat2_mul_01]
    simp [gamma1, gamma3, Complex.I_mul_I] <;> ring
  · change (gamma1 * gamma3) 1 0 =
      -((gamma3 * gamma1) 1 0)
    rw [mat2_mul_10, mat2_mul_10]
    simp [gamma1, gamma3, Complex.I_mul_I] <;> ring
  · change (gamma1 * gamma3) 1 1 =
      -((gamma3 * gamma1) 1 1)
    rw [mat2_mul_11, mat2_mul_11]
    simp [gamma1, gamma3, Complex.I_mul_I] <;> ring

theorem gamma2_mul_gamma3_eq_neg :
    gamma2 * gamma3 = -(gamma3 * gamma2) := by
  funext i j
  fin_cases i <;> fin_cases j
  · change (gamma2 * gamma3) 0 0 =
      -((gamma3 * gamma2) 0 0)
    rw [mat2_mul_00, mat2_mul_00]
    simp [gamma2, gamma3, Complex.I_mul_I] <;> ring
  · change (gamma2 * gamma3) 0 1 =
      -((gamma3 * gamma2) 0 1)
    rw [mat2_mul_01, mat2_mul_01]
    simp [gamma2, gamma3, Complex.I_mul_I] <;> ring
  · change (gamma2 * gamma3) 1 0 =
      -((gamma3 * gamma2) 1 0)
    rw [mat2_mul_10, mat2_mul_10]
    simp [gamma2, gamma3, Complex.I_mul_I] <;> ring
  · change (gamma2 * gamma3) 1 1 =
      -((gamma3 * gamma2) 1 1)
    rw [mat2_mul_11, mat2_mul_11]
    simp [gamma2, gamma3, Complex.I_mul_I] <;> ring

/-!
## Untwisted background commutators
-/

theorem gamma1_gamma2_commutator :
    gamma1 * gamma2 * gamma1Inv * gamma2Inv =
      -(1 : Mat2C) := by
  calc
    gamma1 * gamma2 * gamma1Inv * gamma2Inv
        = -(gamma2 * gamma1 * gamma1Inv * gamma2Inv) := by
            rw [gamma1_mul_gamma2_eq_neg]
            simp
    _ = -(gamma2 * (gamma1 * gamma1Inv) * gamma2Inv) := by
            rw [mul_assoc gamma2 gamma1 gamma1Inv]
    _ = -(gamma2 * gamma2Inv) := by
            rw [gamma1_mul_gamma1Inv]
            simp
    _ = -(1 : Mat2C) := by
            rw [gamma2_mul_gamma2Inv]

theorem gamma1_gamma3_commutator :
    gamma1 * gamma3 * gamma1Inv * gamma3Inv =
      -(1 : Mat2C) := by
  calc
    gamma1 * gamma3 * gamma1Inv * gamma3Inv
        = -(gamma3 * gamma1 * gamma1Inv * gamma3Inv) := by
            rw [gamma1_mul_gamma3_eq_neg]
            simp
    _ = -(gamma3 * (gamma1 * gamma1Inv) * gamma3Inv) := by
            rw [mul_assoc gamma3 gamma1 gamma1Inv]
    _ = -(gamma3 * gamma3Inv) := by
            rw [gamma1_mul_gamma1Inv]
            simp
    _ = -(1 : Mat2C) := by
            rw [gamma3_mul_gamma3Inv]

theorem gamma2_gamma3_commutator :
    gamma2 * gamma3 * gamma2Inv * gamma3Inv =
      -(1 : Mat2C) := by
  calc
    gamma2 * gamma3 * gamma2Inv * gamma3Inv
        = -(gamma3 * gamma2 * gamma2Inv * gamma3Inv) := by
            rw [gamma2_mul_gamma3_eq_neg]
            simp
    _ = -(gamma3 * (gamma2 * gamma2Inv) * gamma3Inv) := by
            rw [mul_assoc gamma3 gamma2 gamma2Inv]
    _ = -(gamma3 * gamma3Inv) := by
            rw [gamma2_mul_gamma2Inv]
            simp
    _ = -(1 : Mat2C) := by
            rw [gamma3_mul_gamma3Inv]

theorem gamma1_gamma4_commutator :
    gamma1 * gamma4 * gamma1Inv * gamma4Inv =
      (1 : Mat2C) := by
  rw [gamma4_eq_one, gamma4Inv_eq_one]
  simp [gamma1_mul_gamma1Inv]

theorem gamma2_gamma4_commutator :
    gamma2 * gamma4 * gamma2Inv * gamma4Inv =
      (1 : Mat2C) := by
  rw [gamma4_eq_one, gamma4Inv_eq_one]
  simp [gamma2_mul_gamma2Inv]

theorem gamma3_gamma4_commutator :
    gamma3 * gamma4 * gamma3Inv * gamma4Inv =
      (1 : Mat2C) := by
  rw [gamma4_eq_one, gamma4Inv_eq_one]
  simp [gamma3_mul_gamma3Inv]

/--
Center twist attached to the six plaquettes in the ordering

`12, 13, 14, 23, 24, 34`

of the manuscript, represented internally by Lean directions

`01, 02, 03, 12, 13, 23`.
-/
def twistCenter : Fin 6 → ℂ :=
  ![-1, -1, 1, -1, 1, 1]

/--
The six untwisted group commutators of the background.
-/
def backgroundCommutator : Fin 6 → Mat2C :=
  ![
    gamma1 * gamma2 * gamma1Inv * gamma2Inv,
    gamma1 * gamma3 * gamma1Inv * gamma3Inv,
    gamma1 * gamma4 * gamma1Inv * gamma4Inv,
    gamma2 * gamma3 * gamma2Inv * gamma3Inv,
    gamma2 * gamma4 * gamma2Inv * gamma4Inv,
    gamma3 * gamma4 * gamma3Inv * gamma4Inv
  ]

/--
The six twisted plaquettes evaluated at the twist-eater background.
-/
def backgroundTwistedPlaquette (p : Fin 6) : Mat2C :=
  twistCenter p • backgroundCommutator p

/--
**Exact background plaquette identity.**

Every twisted plaquette of the Pauli twist-eater background is `I`.
-/
theorem backgroundTwistedPlaquette_eq_one
    (p : Fin 6) :
    backgroundTwistedPlaquette p = (1 : Mat2C) := by
  fin_cases p <;>
    simp [backgroundTwistedPlaquette, backgroundCommutator,
      twistCenter,
      gamma1_gamma2_commutator,
      gamma1_gamma3_commutator,
      gamma1_gamma4_commutator,
      gamma2_gamma3_commutator,
      gamma2_gamma4_commutator,
      gamma3_gamma4_commutator]

#print axioms gamma1_mul_gamma2_eq_neg
#print axioms gamma1_mul_gamma3_eq_neg
#print axioms gamma2_mul_gamma3_eq_neg
#print axioms gamma1_gamma2_commutator
#print axioms gamma1_gamma3_commutator
#print axioms gamma2_gamma3_commutator
#print axioms gamma1_gamma4_commutator
#print axioms gamma2_gamma4_commutator
#print axioms gamma3_gamma4_commutator
#print axioms backgroundTwistedPlaquette_eq_one

end SU2
end YMFormalization
