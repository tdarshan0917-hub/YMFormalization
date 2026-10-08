import YMFormalization.SU2.WilsonPlaquetteSecondVariation
import YMFormalization.SU2.WilsonQuadratic

set_option autoImplicit false

namespace YMFormalization
namespace SU2

/-- Actual six-plaquette Wilson cell action along the direction X. -/
noncomputable def wilsonCellActionPathD
    (β : ℝ) (X : CellTangent) (t : ℝ) : ℝ :=
  β * (
    twistedPlaquetteWilsonCostD 0 X t +
    twistedPlaquetteWilsonCostD 1 X t +
    twistedPlaquetteWilsonCostD 2 X t +
    twistedPlaquetteWilsonCostD 3 X t +
    twistedPlaquetteWilsonCostD 4 X t +
    twistedPlaquetteWilsonCostD 5 X t)

/-- The actual cell action vanishes at the background. -/
theorem wilsonCellActionPathD_zero
    (β : ℝ) (X : CellTangent) :
    wilsonCellActionPathD β X 0 = 0 := by
  simp [wilsonCellActionPathD, twistedPlaquetteWilsonCostD_zero]

/--
The actual nonlinear cell action has directional quadratic coefficient
4 β <X, P_perp X>. This theorem asserts a limit, not Hessian regularity.
-/
theorem wilsonCellActionPathD_quadratic_limit
    (β : ℝ) (X : CellTangent) :
    Filter.Tendsto
      (fun t : ℝ => wilsonCellActionPathD β X t / t ^ 2)
      (nhdsWithin 0 ({0}ᶜ))
      (nhds ((4 * β) * cellPairing X (physicalProjection X))) := by
  let q : Fin 6 → ℝ := fun p =>
    vecPairing (plaquetteLinearization X p)
      (plaquetteLinearization X p)
  have hs :=
    (((((twistedPlaquetteWilsonCostD_quadratic_limit 0 X).add
      (twistedPlaquetteWilsonCostD_quadratic_limit 1 X)).add
      (twistedPlaquetteWilsonCostD_quadratic_limit 2 X)).add
      (twistedPlaquetteWilsonCostD_quadratic_limit 3 X)).add
      (twistedPlaquetteWilsonCostD_quadratic_limit 4 X)).add
      (twistedPlaquetteWilsonCostD_quadratic_limit 5 X)
  have hcoeff :
      β * ((1 / 2 : ℝ) * q 0 + (1 / 2 : ℝ) * q 1 +
        (1 / 2 : ℝ) * q 2 + (1 / 2 : ℝ) * q 3 +
        (1 / 2 : ℝ) * q 4 + (1 / 2 : ℝ) * q 5) =
      (4 * β) * cellPairing X (physicalProjection X) := by
    calc
      _ = (β / 2) * plaquetteQuadratic
          (plaquetteLinearization X) := by
        dsimp [q, plaquetteQuadratic, plaquettePairing]
        ring
      _ = _ := by
        rw [plaquetteQuadratic_linearization_eq_eight_physical]
        ring
  have heq :
      (fun t : ℝ => wilsonCellActionPathD β X t / t ^ 2) =
      (fun t : ℝ => β * (
        twistedPlaquetteWilsonCostD 0 X t / t ^ 2 +
        twistedPlaquetteWilsonCostD 1 X t / t ^ 2 +
        twistedPlaquetteWilsonCostD 2 X t / t ^ 2 +
        twistedPlaquetteWilsonCostD 3 X t / t ^ 2 +
        twistedPlaquetteWilsonCostD 4 X t / t ^ 2 +
        twistedPlaquetteWilsonCostD 5 X t / t ^ 2)) := by
    funext t
    simp only [wilsonCellActionPathD, add_div, mul_div_assoc]
  rw [heq, ← hcoeff]
  exact hs.const_mul β

/-- On the physical slice the coefficient is 4 β <X,X>. -/
theorem wilsonCellActionPathD_quadratic_limit_of_physical
    (β : ℝ) (X : CellTangent)
    (hX : physicalProjection X = X) :
    Filter.Tendsto
      (fun t : ℝ => wilsonCellActionPathD β X t / t ^ 2)
      (nhdsWithin 0 ({0}ᶜ))
      (nhds ((4 * β) * cellPairing X X)) := by
  simpa only [hX] using
    wilsonCellActionPathD_quadratic_limit β X

#print axioms wilsonCellActionPathD_zero
#print axioms wilsonCellActionPathD_quadratic_limit
#print axioms wilsonCellActionPathD_quadratic_limit_of_physical

end SU2
end YMFormalization
