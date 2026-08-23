/-
Copyright (c) 2026 Travis Darshan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Travis Darshan
-/

import YMFormalization.SU2.GaugeMap
import Mathlib

/-!
# Gauge Projection for the Twisted SU(2) Cell

This file constructs the finite-dimensional gauge projection

`P_gauge = (1/8) K Kstar`

from the exact identity

`Kstar (K η) = 8 • η`.

The principal result is that `gaugeProjection` is idempotent.

This is the second certified algebraic brick in the twisted-cell
Yang–Mills Hessian formalization.
-/

set_option autoImplicit false

namespace YMFormalization
namespace SU2

/--
Gauge projection associated with the twisted-cell infinitesimal
gauge map.

Mathematically:

`P_gauge X = (1/8) K (K* X)`.
-/
noncomputable def gaugeProjection (X : CellTangent) : CellTangent :=
  (1 / 8 : ℝ) • K (Kstar X)

/--
The gauge projection fixes every infinitesimal gauge direction.
-/
theorem gaugeProjection_K (η : Vec3) :
    gaugeProjection (K η) = K η := by
  unfold gaugeProjection
  rw [Kstar_K]
  funext μ
  fin_cases μ <;>
    funext a <;>
    fin_cases a <;>
    simp [K, A1, A2, A3, A4] <;>
    ring

/--
The twisted-cell gauge projection is idempotent:

`P_gauge² = P_gauge`.
-/
theorem gaugeProjection_idempotent (X : CellTangent) :
    gaugeProjection (gaugeProjection X) = gaugeProjection X := by
  funext μ
  fin_cases μ <;>
    funext a <;>
    fin_cases a <;>
    simp [gaugeProjection, K, Kstar, A1, A2, A3, A4] <;>
    ring

#print axioms gaugeProjection_K
#print axioms gaugeProjection_idempotent

end SU2
end YMFormalization
