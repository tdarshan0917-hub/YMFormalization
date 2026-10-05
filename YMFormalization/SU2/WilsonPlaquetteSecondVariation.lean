/-
Copyright (c) 2026 Travis Darshan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Travis Darshan
-/

import YMFormalization.SU2.PauliTraceIdentity
import Mathlib

/-!
# Genuine Nonlinear Wilson Plaquette Second Variation

This file connects the genuine nonlinear twisted exponential plaquette
from YM-013 to the Wilson quadratic form.

Target:

  W_p(tX)
    = 1 - (1/2) Re Tr(P_p(tX))
    = (t^2 / 2) |L_p X|^2 + o(t^2).

The eventual capstone identifies the genuine nonlinear plaquette
second variation with the previously certified linearized quadratic form.
-/

set_option autoImplicit false

namespace YMFormalization
namespace SU2

attribute [local instance]
  matNR matNA matAddCommGroup matModule matTopologicalSpace

/--
SU(2)-normalized Wilson plaquette cost.
-/
noncomputable def wilsonPlaquetteCostD (U : Mat2C) : ℝ :=
  1 - (1 / 2 : ℝ) * (Matrix.trace U).re

/--
Wilson cost evaluated on the actual nonlinear twisted plaquette path.
-/
noncomputable def twistedPlaquetteWilsonCostD
    (p : Fin 6) (X : CellTangent) (t : ℝ) : ℝ :=
  wilsonPlaquetteCostD (twistedPlaquettePathD p X t)

/--
The Pauli tangent realization has zero real trace.
-/
theorem su2OfVec_trace_re_zero
    (η : Vec3) :
    (Matrix.trace (su2OfVec η)).re = 0 := by
  change ((∑ i : Fin 2, su2OfVec η i i)).re = 0
  rw [Fin.sum_univ_two]
  simp [su2OfVec]

/--
The genuine nonlinear twisted plaquette derivative has zero real trace.

This is the exact first-order stationarity input for the Wilson cost.
-/
theorem twistedPlaquetteDerivD_trace_re_zero
    (p : Fin 6) (X : CellTangent) :
    (Matrix.trace (twistedPlaquetteDerivD p X)).re = 0 := by
  rw [twistedPlaquetteDerivD_eq_su2OfVec_linearization]
  exact su2OfVec_trace_re_zero (plaquetteLinearization X p)

#print axioms su2OfVec_trace_re_zero
#print axioms twistedPlaquetteDerivD_trace_re_zero


/--
The genuine nonlinear twisted plaquette path starts exactly at the
identity twisted plaquette.
-/
theorem twistedPlaquettePathD_zero
    (p : Fin 6) (X : CellTangent) :
    twistedPlaquettePathD p X 0 = (1 : Mat2C) := by
  have hbg := backgroundTwistedPlaquette_eq_one p
  fin_cases p <;>
    simpa [twistedPlaquettePathD, rawPlaquettePathD,
      cellLinkD, cellInverseLinkD,
      forwardLinkD, inverseLinkD,
      twistMatrixD,
      backgroundTwistedPlaquette, backgroundCommutator,
      plaquetteMu, plaquetteNu,
      gamma, gammaInv] using hbg

/--
The genuine nonlinear Wilson plaquette cost vanishes at the
twist-eater background.
-/
theorem twistedPlaquetteWilsonCostD_zero
    (p : Fin 6) (X : CellTangent) :
    twistedPlaquetteWilsonCostD p X 0 = 0 := by
  unfold twistedPlaquetteWilsonCostD
  rw [twistedPlaquettePathD_zero]
  simp [wilsonPlaquetteCostD, Matrix.trace, Fin.sum_univ_two]

#print axioms twistedPlaquettePathD_zero
#print axioms twistedPlaquetteWilsonCostD_zero


/--
The genuine nonlinear twisted plaquette has derivative exactly equal
to the Pauli realization of the certified linearized plaquette map.
-/
theorem twistedPlaquettePathD_hasDerivAt_linearization
    (p : Fin 6) (X : CellTangent) :
    HasDerivAt
      (twistedPlaquettePathD p X)
      (su2OfVec (plaquetteLinearization X p))
      0 := by
  rw [← twistedPlaquetteDerivD_eq_su2OfVec_linearization p X]
  exact twistedPlaquettePathD_hasDerivAt_zero p X

/--
First-order Taylor remainder for the actual nonlinear twisted plaquette:

  P_p(tX) = I + t * su2OfVec(L_p X) + o(t).

This is the load-bearing analytic bridge from YM-013 to the
nonlinear Wilson quadratic expansion.
-/
theorem twistedPlaquettePathD_remainder_isLittleO
    (p : Fin 6) (X : CellTangent) :
    (fun t : ℝ =>
      twistedPlaquettePathD p X t -
        (1 : Mat2C) -
        t • su2OfVec (plaquetteLinearization X p))
      =o[nhds 0] (fun t : ℝ => t) := by
  have h :=
    (twistedPlaquettePathD_hasDerivAt_linearization p X).isLittleO
  simpa [twistedPlaquettePathD_zero p X] using h

#print axioms twistedPlaquettePathD_hasDerivAt_linearization
#print axioms twistedPlaquettePathD_remainder_isLittleO


/-!
## Exact 2x2 determinant bridge

For determinant-one 2x2 matrices the Wilson cost can be rewritten
exactly using the determinant of `U - I`.  This lets the already
certified first-order nonlinear plaquette expansion produce the
quadratic Wilson coefficient without differentiating the entire
four-factor plaquette a second time.
-/

/--
For the Pauli realization `A = i η · σ`,

  det A = |η|².

This is the determinant normalization corresponding to the previously
certified trace-square identity.
-/
theorem su2OfVec_det
    (η : Vec3) :
    Matrix.det (su2OfVec η) =
      ((vecPairing η η : ℝ) : ℂ) := by
  rw [Matrix.det_fin_two]
  simp [su2OfVec, vecPairing]
  ring_nf
  have hI : Complex.I ^ 2 = (-1 : ℂ) := by
    simpa [pow_two] using Complex.I_mul_I
  rw [hI]
  ring

/--
For a 2x2 determinant-one matrix,

  Tr U = 2 - det(U - I).

This is an exact algebraic identity, not an asymptotic expansion.
-/
theorem trace_eq_two_sub_det_sub_one
    (U : Mat2C)
    (hdet : Matrix.det U = 1) :
    Matrix.trace U =
      2 - Matrix.det (U - 1) := by
  simp [Matrix.trace, Fin.sum_univ_two, Matrix.det_fin_two] at hdet ⊢
  linear_combination hdet

/--
For a determinant-one 2x2 matrix the normalized Wilson cost is exactly

  W(U) = (1/2) Re det(U - I).
-/
theorem wilsonPlaquetteCostD_eq_half_det_sub_one
    (U : Mat2C)
    (hdet : Matrix.det U = 1) :
    wilsonPlaquetteCostD U =
      (1 / 2 : ℝ) * (Matrix.det (U - 1)).re := by
  unfold wilsonPlaquetteCostD
  rw [trace_eq_two_sub_det_sub_one U hdet]
  simp
  ring

#print axioms su2OfVec_det
#print axioms trace_eq_two_sub_det_sub_one
#print axioms wilsonPlaquetteCostD_eq_half_det_sub_one


/-- Opposite exponential factors have reciprocal determinants. -/
theorem det_exp_smul_mul_det_exp_neg
    (A : Mat2C) (t : ℝ) :
    Matrix.det (NormedSpace.exp (t • A)) *
      Matrix.det (NormedSpace.exp (t • (-A))) = 1 := by
  letI : NormedAlgebra ℚ Mat2C := Matrix.linftyOpNormedAlgebra
  have hmul :
      NormedSpace.exp (t • A) *
        NormedSpace.exp (t • (-A)) = (1 : Mat2C) := by
    rw [smul_neg]
    rw [← NormedSpace.exp_add_of_commute
      (Commute.refl (t • A)).neg_right]
    simp
  simpa only [Matrix.det_mul, Matrix.det_one] using
    congrArg Matrix.det hmul

/-- The genuine nonlinear twisted plaquette has determinant one. -/
theorem twistedPlaquettePathD_det_one
    (p : Fin 6) (X : CellTangent) (t : ℝ) :
    Matrix.det (twistedPlaquettePathD p X t) = 1 := by
  let μ := plaquetteMu p
  let ν := plaquetteNu p
  have hμ := det_exp_smul_mul_det_exp_neg (su2OfVec (X μ)) t
  have hν := det_exp_smul_mul_det_exp_neg (su2OfVec (X ν)) t
  have hbg :
      Matrix.det (twistMatrixD p) *
        (Matrix.det (gamma μ) * Matrix.det (gamma ν) *
          Matrix.det (gammaInv μ) * Matrix.det (gammaInv ν)) = 1 := by
    have h := congrArg Matrix.det (twistedPlaquettePathD_zero p X)
    simpa [twistedPlaquettePathD, rawPlaquettePathD,
      cellLinkD, cellInverseLinkD, forwardLinkD, inverseLinkD,
      Matrix.det_mul, μ, ν] using h
  unfold twistedPlaquettePathD rawPlaquettePathD
    cellLinkD cellInverseLinkD forwardLinkD inverseLinkD
  simp only [Matrix.det_mul]
  calc
    _ =
        (Matrix.det (twistMatrixD p) *
          (Matrix.det (gamma μ) * Matrix.det (gamma ν) *
            Matrix.det (gammaInv μ) * Matrix.det (gammaInv ν))) *
        ((Matrix.det (NormedSpace.exp (t • su2OfVec (X μ))) *
          Matrix.det (NormedSpace.exp (t • (-su2OfVec (X μ))))) *
         (Matrix.det (NormedSpace.exp (t • su2OfVec (X ν))) *
          Matrix.det (NormedSpace.exp (t • (-su2OfVec (X ν)))))) := by
            dsimp [μ, ν]
            ring
    _ = 1 := by rw [hbg, hμ, hν]; norm_num

#print axioms det_exp_smul_mul_det_exp_neg
#print axioms twistedPlaquettePathD_det_one


/-- Real scaling of the real part of a 2x2 determinant. -/
theorem det_real_smul_re_D
    (r : ℝ) (U : Mat2C) :
    (Matrix.det (r • U)).re =
      r ^ 2 * (Matrix.det U).re := by
  simp [Matrix.det_fin_two, pow_two, Complex.mul_re, Complex.mul_im]
  <;> ring

/--
The actual nonlinear Wilson plaquette has quadratic coefficient
one half of the squared certified plaquette linearization.
-/
theorem twistedPlaquetteWilsonCostD_quadratic_limit
    (p : Fin 6) (X : CellTangent) :
    Filter.Tendsto
      (fun t : ℝ => twistedPlaquetteWilsonCostD p X t / t ^ 2)
      (nhdsWithin 0 ({0}ᶜ))
      (nhds ((1 / 2 : ℝ) *
        vecPairing (plaquetteLinearization X p)
          (plaquetteLinearization X p))) := by
  have hs :
      Filter.Tendsto
        (fun t : ℝ =>
          t⁻¹ • (twistedPlaquettePathD p X t - (1 : Mat2C)))
        (nhdsWithin 0 ({0}ᶜ))
        (nhds (su2OfVec (plaquetteLinearization X p))) := by
    simpa only [zero_add, twistedPlaquettePathD_zero] using
      (twistedPlaquettePathD_hasDerivAt_linearization p X).tendsto_slope_zero
  have hc :
      Continuous (fun U : Mat2C => (Matrix.det U).re) := by
    fun_prop
  have hd :
      Filter.Tendsto
        (fun t : ℝ =>
          (Matrix.det
            (t⁻¹ • (twistedPlaquettePathD p X t - (1 : Mat2C)))).re)
        (nhdsWithin 0 ({0}ᶜ))
        (nhds (vecPairing (plaquetteLinearization X p)
          (plaquetteLinearization X p))) := by
    simpa only [Function.comp_def, su2OfVec_det, Complex.ofReal_re] using
      (hc.continuousAt.tendsto.comp hs)
  have heq :
      (fun t : ℝ => twistedPlaquetteWilsonCostD p X t / t ^ 2) =
      (fun t : ℝ =>
        (1 / 2 : ℝ) *
          (Matrix.det
            (t⁻¹ • (twistedPlaquettePathD p X t - (1 : Mat2C)))).re) := by
    funext t
    rw [det_real_smul_re_D]
    unfold twistedPlaquetteWilsonCostD
    rw [wilsonPlaquetteCostD_eq_half_det_sub_one
      _ (twistedPlaquettePathD_det_one p X t)]
    simp only [div_eq_mul_inv, inv_pow]
    ring
  rw [heq]
  exact hd.const_mul (1 / 2 : ℝ)

#print axioms det_real_smul_re_D
#print axioms twistedPlaquetteWilsonCostD_quadratic_limit

end SU2
end YMFormalization
