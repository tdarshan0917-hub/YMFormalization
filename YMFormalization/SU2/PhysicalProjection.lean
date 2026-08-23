/-
Copyright (c) 2026 Travis Darshan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Travis Darshan
-/

import YMFormalization.SU2.GaugeProjection
import Mathlib

/-!
# Physical Projection for the Twisted SU(2) Cell

This file defines the complementary projection

`P_perp = I - P_gauge`

for the twisted SU(2) cell.

The gauge projection was constructed from

`Kstar K = 8 I`.

Here we prove that the complementary map kills gauge directions,
is complementary to `P_gauge`, and is itself idempotent.
-/

set_option autoImplicit false

namespace YMFormalization
namespace SU2

/--
Complementary or physical projection

`P_perp = I - P_gauge`.
-/
noncomputable def physicalProjection (X : CellTangent) : CellTangent :=
  X - gaugeProjection X

/--
Every tangent vector decomposes exactly into gauge and physical parts.
-/
theorem gaugeProjection_add_physicalProjection (X : CellTangent) :
    gaugeProjection X + physicalProjection X = X := by
  unfold physicalProjection
  abel

/--
The physical projection kills every infinitesimal gauge direction:

`P_perp (K η) = 0`.
-/
theorem physicalProjection_K (η : Vec3) :
    physicalProjection (K η) = 0 := by
  unfold physicalProjection
  rw [gaugeProjection_K]
  simp

/--
Gauge projection of a physical component vanishes:

`P_gauge P_perp = 0`.
-/
theorem gaugeProjection_physicalProjection (X : CellTangent) :
    gaugeProjection (physicalProjection X) = 0 := by
  funext μ
  fin_cases μ <;>
    funext a <;>
    fin_cases a <;>
    simp [physicalProjection, gaugeProjection, K, Kstar,
      A1, A2, A3, A4] <;>
    ring

/--
The physical projection annihilates a gauge-projected vector:

`P_perp P_gauge = 0`.
-/
theorem physicalProjection_gaugeProjection (X : CellTangent) :
    physicalProjection (gaugeProjection X) = 0 := by
  unfold physicalProjection
  rw [gaugeProjection_idempotent]
  simp

/--
The complementary projection is idempotent:

`P_perp² = P_perp`.
-/
theorem physicalProjection_idempotent (X : CellTangent) :
    physicalProjection (physicalProjection X) = physicalProjection X := by
  calc
    physicalProjection (physicalProjection X)
        = physicalProjection X - gaugeProjection (physicalProjection X) := rfl
    _ = physicalProjection X := by
      rw [gaugeProjection_physicalProjection]
      simp

#print axioms gaugeProjection_add_physicalProjection
#print axioms physicalProjection_K
#print axioms gaugeProjection_physicalProjection
#print axioms physicalProjection_gaugeProjection
#print axioms physicalProjection_idempotent

end SU2
end YMFormalization
