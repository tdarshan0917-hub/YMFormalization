/-
Copyright (c) 2026 Travis Darshan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Travis Darshan
-/

import YMFormalization.SU2.PauliTwist
import Mathlib

/-!
# Twisted Difference Operator

This file identifies the previously certified coordinate operators

`A₁, A₂, A₃, A₄`

with

`I - Ad_{Γμ}`

for the actual Pauli twist-eater background.

The coordinate statement is

`cellA μ η = η - twistRotation μ η`.

Using the certified Pauli conjugation theorem, we then prove the
matrix-level identity

`su2OfVec (cellA μ η)
  = su2OfVec η - Γμ * su2OfVec η * Γμ⁻¹`.
-/

set_option autoImplicit false

namespace YMFormalization
namespace SU2

/--
`su2OfVec` respects subtraction of Pauli-coordinate vectors.
-/
theorem su2OfVec_sub (η ξ : Vec3) :
    su2OfVec (η - ξ) = su2OfVec η - su2OfVec ξ := by
  funext i j
  fin_cases i <;> fin_cases j
  · change su2OfVec (η - ξ) 0 0 =
      (su2OfVec η - su2OfVec ξ) 0 0
    rw [Matrix.sub_apply]
    simp [su2OfVec]
    ring
  · change su2OfVec (η - ξ) 0 1 =
      (su2OfVec η - su2OfVec ξ) 0 1
    rw [Matrix.sub_apply]
    simp [su2OfVec]
    ring
  · change su2OfVec (η - ξ) 1 0 =
      (su2OfVec η - su2OfVec ξ) 1 0
    rw [Matrix.sub_apply]
    simp [su2OfVec]
    ring
  · change su2OfVec (η - ξ) 1 1 =
      (su2OfVec η - su2OfVec ξ) 1 1
    rw [Matrix.sub_apply]
    simp [su2OfVec]
    ring

theorem cellA_eq_id_sub_twistRotation
    (μ : Fin 4) (η : Vec3) :
    cellA μ η = η - twistRotation μ η := by
  funext a
  fin_cases μ <;>
    fin_cases a <;>
    simp [cellA, twistRotation,
      A1, A2, A3, A4,
      R1, R2, R3, R4] <;>
    ring

/--
**Matrix-level `I - Ad_Γ` bridge.**

The coordinate operator `cellA μ` is exactly the Lie-algebra
difference between a vector and its conjugate by the actual
twist-eater matrix:

`su2OfVec (Aμ η)
  = su2OfVec η - Γμ (su2OfVec η) Γμ⁻¹`.
-/
theorem su2OfVec_cellA_eq_sub_twistConjugation
    (μ : Fin 4) (η : Vec3) :
    su2OfVec (cellA μ η) =
      su2OfVec η - gamma μ * su2OfVec η * gammaInv μ := by
  rw [cellA_eq_id_sub_twistRotation]
  rw [su2OfVec_sub]
  rw [twistConjugation_su2]

#print axioms su2OfVec_sub
#print axioms cellA_eq_id_sub_twistRotation
#print axioms su2OfVec_cellA_eq_sub_twistConjugation

end SU2
end YMFormalization
