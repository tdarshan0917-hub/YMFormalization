/-
Copyright (c) 2026 Travis Darshan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Travis Darshan
-/

import YMFormalization.SU2.NonlinearPlaquetteDerivative
import YMFormalization.SU2.PlaquetteAdjoint
import Mathlib

/-!
# Pauli Trace Identity

Exact normalization identity for the Pauli realization

  A = i η · σ.

This is the trace normalization used in the genuine nonlinear
Wilson plaquette second-variation calculation.
-/

set_option autoImplicit false

namespace YMFormalization
namespace SU2

/--
For `A = su2OfVec η = i η · σ`,

`Re Tr(A²) = -2 <η,η>`.
-/
theorem su2OfVec_mul_self_trace_re
    (η : Vec3) :
    (Matrix.trace (su2OfVec η * su2OfVec η)).re =
      -2 * vecPairing η η := by

  have h00 :
      ((su2OfVec η * su2OfVec η) (0 : Fin 2) (0 : Fin 2)).re =
        -vecPairing η η := by
    rw [Matrix.mul_apply]
    simp [Fin.sum_univ_two, su2OfVec, vecPairing]
    ring

  have h11 :
      ((su2OfVec η * su2OfVec η) (1 : Fin 2) (1 : Fin 2)).re =
        -vecPairing η η := by
    rw [Matrix.mul_apply]
    simp [Fin.sum_univ_two, su2OfVec, vecPairing]
    ring

  change
    ((∑ i : Fin 2,
        (su2OfVec η * su2OfVec η) i i)).re =
      -2 * vecPairing η η

  rw [Fin.sum_univ_two]

  change
    ((su2OfVec η * su2OfVec η) (0 : Fin 2) (0 : Fin 2)).re +
      ((su2OfVec η * su2OfVec η) (1 : Fin 2) (1 : Fin 2)).re =
        -2 * vecPairing η η

  rw [h00, h11]
  ring

#print axioms su2OfVec_mul_self_trace_re

end SU2
end YMFormalization
