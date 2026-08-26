/-
Copyright (c) 2026 Travis Darshan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Travis Darshan
-/

import YMFormalization.SU2.TwistDifference
import Mathlib

/-!
# Exact Kernel of the Twisted Plaquette Linearization

The twisted-cell plaquette map satisfies

`Lstar L = 8 P_perp`.

This file extracts the exact kernel consequence:

`L X = 0 ↔ X ∈ range K`.

Thus the only zero modes of the finite SU(2) cell plaquette
linearization are infinitesimal gauge directions.

This is the kernel statement required before interpreting the
quadratic operator as the physical Wilson-cell Hessian.
-/

set_option autoImplicit false

namespace YMFormalization
namespace SU2

/--
The gauge-direction map `K` commutes with real scalar multiplication.
-/
theorem K_smul (c : ℝ) (η : Vec3) :
    K (c • η) = c • K η := by
  funext μ
  fin_cases μ <;>
    funext a <;>
    fin_cases a <;>
    simp [K, A1, A2, A3, A4] <;>
    ring

/--
Every gauge projection is explicitly a vector in the image of `K`.

`P_gauge X = K ((1/8) Kstar X)`.
-/
theorem gaugeProjection_eq_K (X : CellTangent) :
    gaugeProjection X =
      K ((1 / 8 : ℝ) • Kstar X) := by
  unfold gaugeProjection
  rw [K_smul]

/--
If the plaquette linearization vanishes, then the physical
projection vanishes.
-/
theorem physicalProjection_eq_zero_of_plaquetteLinearization_eq_zero
    (X : CellTangent)
    (hL : plaquetteLinearization X = 0) :
    physicalProjection X = 0 := by
  have hAdj :
      plaquetteAdjoint (plaquetteLinearization X) = 0 := by
    rw [hL]
    exact plaquetteAdjoint_zero

  rw [plaquetteAdjoint_linearization_eq_eight_physicalProjection] at hAdj

  funext μ
  funext a

  have hcoord :=
    congrArg (fun Z : CellTangent => Z μ a) hAdj

  change
    (8 : ℝ) * physicalProjection X μ a = (0 : ℝ)
    at hcoord

  change physicalProjection X μ a = (0 : ℝ)

  have h8 : (8 : ℝ) ≠ 0 := by
    norm_num

  exact (mul_eq_zero.mp hcoord).resolve_left h8

/--
**Exact gauge-kernel theorem.**

The kernel of the six-plaquette linearization is exactly the
space of infinitesimal gauge directions:

`L X = 0 ↔ ∃ η, X = K η`.
-/
theorem plaquetteLinearization_eq_zero_iff_exists_K
    (X : CellTangent) :
    plaquetteLinearization X = 0 ↔
      ∃ η : Vec3, X = K η := by
  constructor

  · intro hL

    have hphys :
        physicalProjection X = 0 :=
      physicalProjection_eq_zero_of_plaquetteLinearization_eq_zero X hL

    have hdecomp :=
      gaugeProjection_add_physicalProjection X

    have hgauge :
        gaugeProjection X = X := by
      simpa [hphys] using hdecomp

    refine ⟨(1 / 8 : ℝ) • Kstar X, ?_⟩

    calc
      X = gaugeProjection X := hgauge.symm
      _ = K ((1 / 8 : ℝ) • Kstar X) :=
        gaugeProjection_eq_K X

  · rintro ⟨η, rfl⟩
    exact plaquetteLinearization_K η

/--
Equivalent formulation: `L X = 0` iff `X` has no physical component.
-/
theorem plaquetteLinearization_eq_zero_iff_physicalProjection_eq_zero
    (X : CellTangent) :
    plaquetteLinearization X = 0 ↔
      physicalProjection X = 0 := by
  constructor

  · exact
      physicalProjection_eq_zero_of_plaquetteLinearization_eq_zero X

  · intro hphys

    have hdecomp :=
      gaugeProjection_add_physicalProjection X

    have hgauge :
        gaugeProjection X = X := by
      simpa [hphys] using hdecomp

    rw [← hgauge, gaugeProjection_eq_K]

    exact
      plaquetteLinearization_K
        ((1 / 8 : ℝ) • Kstar X)

#print axioms K_smul
#print axioms gaugeProjection_eq_K
#print axioms physicalProjection_eq_zero_of_plaquetteLinearization_eq_zero
#print axioms plaquetteLinearization_eq_zero_iff_exists_K
#print axioms plaquetteLinearization_eq_zero_iff_physicalProjection_eq_zero

end SU2
end YMFormalization
