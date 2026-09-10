import YMFormalization.SU2.TwistedBackgroundPlaquette
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib

set_option autoImplicit false

namespace YMFormalization
namespace SU2

noncomputable section

/-!
Use one coherent matrix norm/algebra hierarchy.
-/

local instance matNR : NormedRing Mat2C :=
  Matrix.linftyOpNormedRing

local instance matNA : NormedAlgebra ℝ Mat2C :=
  Matrix.linftyOpNormedAlgebra

local instance matAddCommGroup : AddCommGroup Mat2C :=
  matNR.toAddCommGroup

local instance matModule : Module ℝ Mat2C :=
  matNA.toNormedSpace.toModule

local instance matTopologicalSpace : TopologicalSpace Mat2C :=
  matNR.toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

/-!
## Exponential and link derivatives
-/

/--
At zero,

`d/dt exp(tA) = A`.
-/
theorem exp_smul_hasDerivAt_zero
    (A : Mat2C) :
    HasDerivAt
      (fun t : ℝ => NormedSpace.exp (t • A))
      A
      0 := by
  simpa using
    (hasDerivAt_exp_smul_const A (0 : ℝ))

/--
Forward link path `exp(tA) G`.
-/
def forwardLinkD
    (A G : Mat2C) (t : ℝ) : Mat2C :=
  NormedSpace.exp (t • A) * G

theorem forwardLinkD_hasDerivAt_zero
    (A G : Mat2C) :
    HasDerivAt
      (forwardLinkD A G)
      (A * G)
      0 := by
  exact (exp_smul_hasDerivAt_zero A).mul_const G

/--
Inverse-link representation `G⁻¹ exp(-tA)`.
-/
def inverseLinkD
    (A Ginv : Mat2C) (t : ℝ) : Mat2C :=
  Ginv * NormedSpace.exp (t • (-A))

theorem inverseLinkD_hasDerivAt_zero
    (A Ginv : Mat2C) :
    HasDerivAt
      (inverseLinkD A Ginv)
      (Ginv * (-A))
      0 := by
  have h :
      HasDerivAt
        (fun t : ℝ => NormedSpace.exp (t • (-A)))
        (-A)
        0 := by
    exact exp_smul_hasDerivAt_zero (-A)

  exact HasDerivAt.const_mul Ginv h

/-!
## Cell-specialized links
-/

def cellLinkD
    (μ : Fin 4) (X : CellTangent) (t : ℝ) : Mat2C :=
  forwardLinkD (su2OfVec (X μ)) (gamma μ) t

def cellInverseLinkD
    (μ : Fin 4) (X : CellTangent) (t : ℝ) : Mat2C :=
  inverseLinkD (su2OfVec (X μ)) (gammaInv μ) t

def cellLinkDerivD
    (μ : Fin 4) (X : CellTangent) : Mat2C :=
  su2OfVec (X μ) * gamma μ

def cellInverseLinkDerivD
    (μ : Fin 4) (X : CellTangent) : Mat2C :=
  gammaInv μ * (-su2OfVec (X μ))

theorem cellLinkD_hasDerivAt_zero
    (μ : Fin 4) (X : CellTangent) :
    HasDerivAt
      (cellLinkD μ X)
      (cellLinkDerivD μ X)
      0 := by
  exact
    forwardLinkD_hasDerivAt_zero
      (su2OfVec (X μ))
      (gamma μ)

theorem cellInverseLinkD_hasDerivAt_zero
    (μ : Fin 4) (X : CellTangent) :
    HasDerivAt
      (cellInverseLinkD μ X)
      (cellInverseLinkDerivD μ X)
      0 := by
  exact
    inverseLinkD_hasDerivAt_zero
      (su2OfVec (X μ))
      (gammaInv μ)

/-!
## Explicit derivative bookkeeping
-/

def pairDerivD
    (μ ν : Fin 4) (X : CellTangent) : Mat2C :=
  cellLinkDerivD μ X * cellLinkD ν X 0 +
    cellLinkD μ X 0 * cellLinkDerivD ν X

def tripleDerivD
    (μ ν : Fin 4) (X : CellTangent) : Mat2C :=
  pairDerivD μ ν X * cellInverseLinkD μ X 0 +
    (cellLinkD μ X 0 * cellLinkD ν X 0) *
      cellInverseLinkDerivD μ X

def rawPlaquetteDerivD
    (μ ν : Fin 4) (X : CellTangent) : Mat2C :=
  tripleDerivD μ ν X * cellInverseLinkD ν X 0 +
    ((cellLinkD μ X 0 * cellLinkD ν X 0) *
      cellInverseLinkD μ X 0) *
      cellInverseLinkDerivD ν X

/--
Actual four-link commutator path.
-/
def rawPlaquettePathD
    (μ ν : Fin 4) (X : CellTangent) (t : ℝ) : Mat2C :=
  ((cellLinkD μ X t * cellLinkD ν X t) *
      cellInverseLinkD μ X t) *
    cellInverseLinkD ν X t

/--
**Core four-factor calculus theorem.**

This uses the real one-variable noncommutative product rule only.
-/
theorem rawPlaquettePathD_hasDerivAt_zero
    (μ ν : Fin 4) (X : CellTangent) :
    HasDerivAt
      (rawPlaquettePathD μ ν X)
      (rawPlaquetteDerivD μ ν X)
      0 := by

  have hμ :
      HasDerivAt
        (cellLinkD μ X)
        (cellLinkDerivD μ X)
        0 :=
    cellLinkD_hasDerivAt_zero μ X

  have hν :
      HasDerivAt
        (cellLinkD ν X)
        (cellLinkDerivD ν X)
        0 :=
    cellLinkD_hasDerivAt_zero ν X

  have hiμ :
      HasDerivAt
        (cellInverseLinkD μ X)
        (cellInverseLinkDerivD μ X)
        0 :=
    cellInverseLinkD_hasDerivAt_zero μ X

  have hiν :
      HasDerivAt
        (cellInverseLinkD ν X)
        (cellInverseLinkDerivD ν X)
        0 :=
    cellInverseLinkD_hasDerivAt_zero ν X

  have h12 := hμ.mul hν
  have h123 := h12.mul hiμ
  have h1234 := h123.mul hiν

  change HasDerivAt
    (((cellLinkD μ X * cellLinkD ν X) *
        cellInverseLinkD μ X) *
      cellInverseLinkD ν X)
    (rawPlaquetteDerivD μ ν X)
    0

  simpa [
    rawPlaquetteDerivD,
    tripleDerivD,
    pairDerivD,
    matAddCommGroup,
    matModule,
    matTopologicalSpace,
    matNR,
    matNA
  ] using h1234

/-!
## Center-twisted plaquette
-/

def twistMatrixD
    (p : Fin 6) : Mat2C :=
  twistCenter p • (1 : Mat2C)

def twistedPlaquettePathD
    (p : Fin 6) (X : CellTangent) (t : ℝ) : Mat2C :=
  twistMatrixD p *
    rawPlaquettePathD
      (plaquetteMu p)
      (plaquetteNu p)
      X t

def twistedPlaquetteDerivD
    (p : Fin 6) (X : CellTangent) : Mat2C :=
  twistMatrixD p *
    rawPlaquetteDerivD
      (plaquetteMu p)
      (plaquetteNu p)
      X

/--
The actual twisted plaquette path has the explicit four-factor
derivative at the twist-eater background.
-/
theorem twistedPlaquettePathD_hasDerivAt_zero
    (p : Fin 6) (X : CellTangent) :
    HasDerivAt
      (twistedPlaquettePathD p X)
      (twistedPlaquetteDerivD p X)
      0 := by

  have h :=
    rawPlaquettePathD_hasDerivAt_zero
      (plaquetteMu p)
      (plaquetteNu p)
      X

  change HasDerivAt
    (fun t : ℝ =>
      twistMatrixD p *
        rawPlaquettePathD
          (plaquetteMu p)
          (plaquetteNu p)
          X t)
    (twistedPlaquetteDerivD p X)
    0

  simpa [twistedPlaquetteDerivD] using
    (HasDerivAt.const_mul (twistMatrixD p) h)

#print axioms exp_smul_hasDerivAt_zero
#print axioms forwardLinkD_hasDerivAt_zero
#print axioms inverseLinkD_hasDerivAt_zero
#print axioms cellLinkD_hasDerivAt_zero
#print axioms cellInverseLinkD_hasDerivAt_zero
#print axioms rawPlaquettePathD_hasDerivAt_zero
#print axioms twistedPlaquettePathD_hasDerivAt_zero

end

/-!
## YM-013 — exact structural p=4 closure
-/

theorem cellLinkD_zero
    (μ : Fin 4) (X : CellTangent) :
    cellLinkD μ X 0 = gamma μ := by
  simp [cellLinkD, forwardLinkD]


theorem cellInverseLinkD_zero
    (μ : Fin 4) (X : CellTangent) :
    cellInverseLinkD μ X 0 = gammaInv μ := by
  simp [cellInverseLinkD, inverseLinkD]


/--
p=4 = internal directions (1,3), manuscript directions (2,4).

The X₁ terms cancel structurally through Γ₂ Γ₂⁻¹ = 1.
-/
theorem twistedPlaquetteDerivD_four_formula
    (X : CellTangent) :
    twistedPlaquetteDerivD (4 : Fin 6) X =
      gamma2 * su2OfVec (X 3) * gamma2Inv -
        su2OfVec (X 3) := by

  simp only [
    twistedPlaquetteDerivD,
    rawPlaquetteDerivD,
    tripleDerivD,
    pairDerivD,
    cellLinkDerivD,
    cellInverseLinkDerivD,
    cellLinkD_zero,
    cellInverseLinkD_zero,
    twistMatrixD,
    twistCenter,
    plaquetteMu,
    plaquetteNu,
    gamma,
    gammaInv,
    gamma4_eq_one,
    gamma4Inv_eq_one
  ]

  /-
  At this point the only obstruction is finite-vector evaluation:
    ![...] 4
  etc.  Ordinary simp reduces those lookups without unfolding
  gamma2/gamma2Inv themselves.
  -/
  simp

  -- Expand (A*Γ₂ + Γ₂*B) * Γ₂⁻¹.
  rw [add_mul]

  -- (A * Γ₂) * Γ₂⁻¹ = A.
  rw [mul_assoc (su2OfVec (X 1)) gamma2 gamma2Inv]
  rw [gamma2_mul_gamma2Inv]
  rw [mul_one]

  -- Γ₂ * (Γ₂⁻¹ * A) = A.
  rw [← mul_assoc gamma2 gamma2Inv (su2OfVec (X 1))]
  rw [gamma2_mul_gamma2Inv]
  rw [one_mul]

  -- What remains is only associativity/distributivity/additive cancellation.
  noncomm_ring


/--
The genuine nonlinear derivative on p=4 equals the previously
defined linearized plaquette map.
-/
theorem twistedPlaquetteDerivD_four_normalized
    (X : CellTangent) :
    twistedPlaquetteDerivD (4 : Fin 6) X =
      su2OfVec (plaquetteLinearization X (4 : Fin 6)) := by

  rw [twistedPlaquetteDerivD_four_formula]

  have hconj :
      su2OfVec (cellA (1 : Fin 4) (X 3)) =
        su2OfVec (X 3) -
          gamma2 * su2OfVec (X 3) * gamma2Inv := by
    simpa [gamma, gammaInv] using
      (su2OfVec_cellA_eq_sub_twistConjugation
        (1 : Fin 4) (X 3))

  -- Force the finite plaquette lookup to its concrete p=4 form.
  change
    gamma2 * su2OfVec (X 3) * gamma2Inv -
        su2OfVec (X 3) =
      su2OfVec
        (cellA (3 : Fin 4) (X 1) -
          cellA (1 : Fin 4) (X 3))

  have hA4 :
      cellA (3 : Fin 4) (X 1) = 0 := by
    funext a
    fin_cases a <;>
      simp [cellA, A4]

  rw [hA4]
  rw [su2OfVec_sub]

  have hzero :
      su2OfVec (0 : Vec3) = 0 := by
    funext i j
    fin_cases i <;> fin_cases j <;>
      simp [su2OfVec]

  rw [hzero, hconj]
  abel


#print axioms cellLinkD_zero
#print axioms cellInverseLinkD_zero
#print axioms twistedPlaquetteDerivD_four_formula
#print axioms twistedPlaquetteDerivD_four_normalized



/-!
## YM-013 — structural p=5 closure

p=5 has internal directions (2,3), manuscript directions (3,4).
This is the gamma3 twin of the now-green p=4 argument.
-/

/--
For p=5 the X₂ terms cancel through Γ₃ Γ₃⁻¹ = 1,
leaving Γ₃ B Γ₃⁻¹ - B with B = su2OfVec (X 3).
-/
theorem twistedPlaquetteDerivD_five_formula
    (X : CellTangent) :
    twistedPlaquetteDerivD (5 : Fin 6) X =
      gamma3 * su2OfVec (X 3) * gamma3Inv -
        su2OfVec (X 3) := by

  simp only [
    twistedPlaquetteDerivD,
    rawPlaquetteDerivD,
    tripleDerivD,
    pairDerivD,
    cellLinkDerivD,
    cellInverseLinkDerivD,
    cellLinkD_zero,
    cellInverseLinkD_zero,
    twistMatrixD,
    twistCenter,
    plaquetteMu,
    plaquetteNu,
    gamma,
    gammaInv,
    gamma4_eq_one,
    gamma4Inv_eq_one
  ]

  -- Normalize the finite-vector lookups p=5 -> μ=2, ν=3.
  -- Crucially, gamma3/gamma3Inv themselves remain opaque.
  simp

  -- Expand (A*Γ₃ + Γ₃*B) * Γ₃⁻¹.
  rw [add_mul]

  -- (A * Γ₃) * Γ₃⁻¹ = A.
  rw [mul_assoc (su2OfVec (X 2)) gamma3 gamma3Inv]
  rw [gamma3_mul_gamma3Inv]
  rw [mul_one]

  -- Γ₃ * (Γ₃⁻¹ * A) = A.
  rw [← mul_assoc gamma3 gamma3Inv (su2OfVec (X 2))]
  rw [gamma3_mul_gamma3Inv]
  rw [one_mul]

  noncomm_ring


/--
The genuine nonlinear derivative on p=5 equals the already-defined
linearized plaquette curvature.
-/
theorem twistedPlaquetteDerivD_five_normalized
    (X : CellTangent) :
    twistedPlaquetteDerivD (5 : Fin 6) X =
      su2OfVec (plaquetteLinearization X (5 : Fin 6)) := by

  rw [twistedPlaquetteDerivD_five_formula]

  have hconj :
      su2OfVec (cellA (2 : Fin 4) (X 3)) =
        su2OfVec (X 3) -
          gamma3 * su2OfVec (X 3) * gamma3Inv := by
    simpa [gamma, gammaInv] using
      (su2OfVec_cellA_eq_sub_twistConjugation
        (2 : Fin 4) (X 3))

  change
    gamma3 * su2OfVec (X 3) * gamma3Inv -
        su2OfVec (X 3) =
      su2OfVec
        (cellA (3 : Fin 4) (X 2) -
          cellA (2 : Fin 4) (X 3))

  have hA4 :
      cellA (3 : Fin 4) (X 2) = 0 := by
    funext a
    fin_cases a <;>
      simp [cellA, A4]

  rw [hA4]
  rw [su2OfVec_sub]

  have hzero :
      su2OfVec (0 : Vec3) = 0 := by
    funext i j
    fin_cases i <;> fin_cases j <;>
      simp [su2OfVec]

  rw [hzero, hconj]
  abel


#print axioms twistedPlaquetteDerivD_five_formula
#print axioms twistedPlaquetteDerivD_five_normalized



/-!
## YM-013 — minimal structural p=0

p=0 = internal (0,1), manuscript (1,2).

This version keeps only the structural lemmas actually required.
-/

/--
Reverse inverse for Γ₁.

We deliberately copy the working style of the permanent
gamma1_mul_gamma1Inv proof: after fin_cases, force literal matrix
indices with `change` before applying the 2×2 multiplication lemmas.
-/
theorem gamma1Inv_mul_gamma1 :
    gamma1Inv * gamma1 = (1 : Mat2C) := by
  funext i j
  fin_cases i <;> fin_cases j
  · change (gamma1Inv * gamma1) 0 0 = (1 : Mat2C) 0 0
    rw [mat2_mul_00]
    simp [gamma1Inv, gamma1, Complex.I_mul_I]
  · change (gamma1Inv * gamma1) 0 1 = (1 : Mat2C) 0 1
    rw [mat2_mul_01]
    simp [gamma1Inv, gamma1]
  · change (gamma1Inv * gamma1) 1 0 = (1 : Mat2C) 1 0
    rw [mat2_mul_10]
    simp [gamma1Inv, gamma1]
  · change (gamma1Inv * gamma1) 1 1 = (1 : Mat2C) 1 1
    rw [mat2_mul_11]
    simp [gamma1Inv, gamma1, Complex.I_mul_I]


/--
Right-associated form of the already-banked p=0 background
commutator.
-/
theorem gamma1_gamma2_commutator_assoc :
    gamma1 * (gamma2 * (gamma1Inv * gamma2Inv)) =
      -(1 : Mat2C) := by
  calc
    gamma1 * (gamma2 * (gamma1Inv * gamma2Inv))
        =
      gamma1 * gamma2 * gamma1Inv * gamma2Inv := by
        noncomm_ring
    _ = -(1 : Mat2C) := gamma1_gamma2_commutator


/--
Transport Γ₁⁻¹ through Γ₂ using the background commutator.
-/
theorem gamma2_gamma1Inv_gamma2Inv :
    gamma2 * (gamma1Inv * gamma2Inv) =
      -gamma1Inv := by
  calc
    gamma2 * (gamma1Inv * gamma2Inv)
        =
      (gamma1Inv * gamma1) *
        (gamma2 * (gamma1Inv * gamma2Inv)) := by
          rw [gamma1Inv_mul_gamma1]
          simp
    _ =
      gamma1Inv *
        (gamma1 * gamma2 * gamma1Inv * gamma2Inv) := by
          noncomm_ring
    _ = gamma1Inv * (-(1 : Mat2C)) := by
          rw [gamma1_gamma2_commutator]
    _ = -gamma1Inv := by
          simp


/--
Γ₁ Γ₁⁻¹ acts trivially on a following matrix.
-/
theorem gamma1_gamma1Inv_mul
    (M : Mat2C) :
    gamma1 * (gamma1Inv * M) = M := by
  calc
    gamma1 * (gamma1Inv * M)
        = (gamma1 * gamma1Inv) * M := by
            rw [mul_assoc]
    _ = M := by
          rw [gamma1_mul_gamma1Inv]
          simp


/--
Actual p=0 nonlinear derivative, reduced structurally.
-/
theorem twistedPlaquetteDerivD_zero_formula
    (X : CellTangent) :
    twistedPlaquetteDerivD (0 : Fin 6) X =
      (su2OfVec (X 0) -
        gamma2 * su2OfVec (X 0) * gamma2Inv)
      -
      (su2OfVec (X 1) -
        gamma1 * su2OfVec (X 1) * gamma1Inv) := by

  simp only [
    twistedPlaquetteDerivD,
    rawPlaquetteDerivD,
    tripleDerivD,
    pairDerivD,
    cellLinkDerivD,
    cellInverseLinkDerivD,
    cellLinkD_zero,
    cellInverseLinkD_zero,
    twistMatrixD,
    twistCenter,
    plaquetteMu,
    plaquetteNu,
    gamma,
    gammaInv
  ]

  -- Reduce p=0 finite-vector lookups and the center factor.
  -- This may already have been accomplished by the preceding simp_only.
  try simp

  -- Canonical right association exposes the structural patterns.
  simp only [mul_assoc]

  /-
  At this stage the finite p=0 bookkeeping is gone.
  Reduce the four genuine derivative terms one by one.
  -/

  have hcomm_mul :
      ∀ M : Mat2C,
        gamma1 * (gamma2 * (gamma1Inv * (gamma2Inv * M))) =
          -M := by
    intro M
    calc
      gamma1 * (gamma2 * (gamma1Inv * (gamma2Inv * M)))
          =
        (gamma1 * (gamma2 * (gamma1Inv * gamma2Inv))) * M := by
          noncomm_ring
      _ = (-(1 : Mat2C)) * M := by
          rw [gamma1_gamma2_commutator_assoc]
      _ = -M := by
          simp

  have hcomm_right :
      ∀ M : Mat2C,
        M * (gamma1 * (gamma2 * (gamma1Inv * gamma2Inv))) =
          -M := by
    intro M
    rw [gamma1_gamma2_commutator_assoc]
    simp

  have hmiddle :
      ∀ M : Mat2C,
        gamma1 * (M * (gamma2 * (gamma1Inv * gamma2Inv))) =
          -(gamma1 * (M * gamma1Inv)) := by
    intro M
    rw [gamma2_gamma1Inv_gamma2Inv]
    noncomm_ring

  have htail :
      ∀ M : Mat2C,
        gamma1 * (gamma2 * (gamma1Inv * (M * gamma2Inv))) =
          -(gamma2 * (M * gamma2Inv)) := by
    intro M
    calc
      gamma1 * (gamma2 * (gamma1Inv * (M * gamma2Inv)))
          =
        (gamma1 * gamma2) *
          (gamma1Inv * (M * gamma2Inv)) := by
            noncomm_ring
      _ =
        (-(gamma2 * gamma1)) *
          (gamma1Inv * (M * gamma2Inv)) := by
            rw [gamma1_mul_gamma2_eq_neg]
      _ =
        -(gamma2 *
          (gamma1 * (gamma1Inv * (M * gamma2Inv)))) := by
            noncomm_ring
      _ =
        -(gamma2 * (M * gamma2Inv)) := by
            rw [gamma1_gamma1Inv_mul]

  /-
  The current derivative is still bundled as products of sums.
  Build exact grouped reductions matching the terms obtained after
  distributivity, rather than asking rw to discover associativity.
  -/

  have hright0 :
      ((su2OfVec (X 0) * (gamma1 * gamma2)) * gamma1Inv) *
          gamma2Inv =
        -su2OfVec (X 0) := by
    calc
      ((su2OfVec (X 0) * (gamma1 * gamma2)) * gamma1Inv) *
            gamma2Inv
          =
        su2OfVec (X 0) *
          (gamma1 * (gamma2 * (gamma1Inv * gamma2Inv))) := by
            noncomm_ring
      _ = -su2OfVec (X 0) := by
            exact hcomm_right (su2OfVec (X 0))

  have hmiddle0 :
      ((gamma1 * (su2OfVec (X 1) * gamma2)) * gamma1Inv) *
          gamma2Inv =
        -(gamma1 * (su2OfVec (X 1) * gamma1Inv)) := by
    calc
      ((gamma1 * (su2OfVec (X 1) * gamma2)) * gamma1Inv) *
            gamma2Inv
          =
        gamma1 *
          (su2OfVec (X 1) *
            (gamma2 * (gamma1Inv * gamma2Inv))) := by
              noncomm_ring
      _ =
        -(gamma1 * (su2OfVec (X 1) * gamma1Inv)) := by
          exact hmiddle (su2OfVec (X 1))

  have htail0 :
      (gamma1 *
          (gamma2 * (gamma1Inv * su2OfVec (X 0)))) *
          gamma2Inv =
        -(gamma2 * (su2OfVec (X 0) * gamma2Inv)) := by
    calc
      (gamma1 *
          (gamma2 * (gamma1Inv * su2OfVec (X 0)))) *
            gamma2Inv
          =
        gamma1 *
          (gamma2 *
            (gamma1Inv *
              (su2OfVec (X 0) * gamma2Inv))) := by
                noncomm_ring
      _ =
        -(gamma2 * (su2OfVec (X 0) * gamma2Inv)) := by
          exact htail (su2OfVec (X 0))

  /-
  Distribute only multiplication over addition/negation.
  No matrix coordinates are unfolded.
  -/
  simp only [add_mul, neg_mul]

  rw [hright0, hmiddle0, htail0]
  rw [hcomm_mul (su2OfVec (X 1))]

  abel


/--
p=0 genuine nonlinear derivative equals the previously formalized
linearized plaquette map.
-/
theorem twistedPlaquetteDerivD_zero_normalized
    (X : CellTangent) :
    twistedPlaquetteDerivD (0 : Fin 6) X =
      su2OfVec (plaquetteLinearization X (0 : Fin 6)) := by

  rw [twistedPlaquetteDerivD_zero_formula]

  have hlin :
      plaquetteLinearization X (0 : Fin 6) =
        cellA (1 : Fin 4) (X 0) -
          cellA (0 : Fin 4) (X 1) := by
    simp [
      plaquetteLinearization,
      plaquetteMu,
      plaquetteNu
    ]

  rw [hlin]
  rw [su2OfVec_sub]

  rw [
    su2OfVec_cellA_eq_sub_twistConjugation
      (1 : Fin 4) (X 0)
  ]

  rw [
    su2OfVec_cellA_eq_sub_twistConjugation
      (0 : Fin 4) (X 1)
  ]

  simp [gamma, gammaInv]


#print axioms gamma1Inv_mul_gamma1
#print axioms gamma1_gamma2_commutator_assoc
#print axioms gamma2_gamma1Inv_gamma2Inv
#print axioms gamma1_gamma1Inv_mul
#print axioms twistedPlaquetteDerivD_zero_formula
#print axioms twistedPlaquetteDerivD_zero_normalized



/-!
# YM-013 — remaining spatial plaquettes

R15 closed p=0 = (0,1) structurally.

Here we clone exactly that architecture to:

* p=1 = internal (0,2), manuscript (1,3);
* p=3 = internal (1,2), manuscript (2,3).

No entrywise derivative calculation.
-/

/-!
## p=1 = (0,2) = Γ₁ / Γ₃
-/

theorem gamma1_gamma3_commutator_assoc :
    gamma1 * (gamma3 * (gamma1Inv * gamma3Inv)) =
      -(1 : Mat2C) := by
  calc
    gamma1 * (gamma3 * (gamma1Inv * gamma3Inv))
        =
      gamma1 * gamma3 * gamma1Inv * gamma3Inv := by
        noncomm_ring
    _ = -(1 : Mat2C) := gamma1_gamma3_commutator


theorem gamma3_gamma1Inv_gamma3Inv :
    gamma3 * (gamma1Inv * gamma3Inv) =
      -gamma1Inv := by
  calc
    gamma3 * (gamma1Inv * gamma3Inv)
        =
      (gamma1Inv * gamma1) *
        (gamma3 * (gamma1Inv * gamma3Inv)) := by
          rw [gamma1Inv_mul_gamma1]
          simp
    _ =
      gamma1Inv *
        (gamma1 * gamma3 * gamma1Inv * gamma3Inv) := by
          noncomm_ring
    _ = gamma1Inv * (-(1 : Mat2C)) := by
          rw [gamma1_gamma3_commutator]
    _ = -gamma1Inv := by
          simp


theorem twistedPlaquetteDerivD_one_formula
    (X : CellTangent) :
    twistedPlaquetteDerivD (1 : Fin 6) X =
      (su2OfVec (X 0) -
        gamma3 * su2OfVec (X 0) * gamma3Inv)
      -
      (su2OfVec (X 2) -
        gamma1 * su2OfVec (X 2) * gamma1Inv) := by

  simp only [
    twistedPlaquetteDerivD,
    rawPlaquetteDerivD,
    tripleDerivD,
    pairDerivD,
    cellLinkDerivD,
    cellInverseLinkDerivD,
    cellLinkD_zero,
    cellInverseLinkD_zero,
    twistMatrixD,
    twistCenter,
    plaquetteMu,
    plaquetteNu,
    gamma,
    gammaInv
  ]

  try simp
  simp only [mul_assoc]

  have hcomm_mul :
      ∀ M : Mat2C,
        gamma1 * (gamma3 * (gamma1Inv * (gamma3Inv * M))) =
          -M := by
    intro M
    calc
      gamma1 * (gamma3 * (gamma1Inv * (gamma3Inv * M)))
          =
        (gamma1 * (gamma3 * (gamma1Inv * gamma3Inv))) * M := by
          noncomm_ring
      _ = (-(1 : Mat2C)) * M := by
          rw [gamma1_gamma3_commutator_assoc]
      _ = -M := by
          simp

  have hcomm_right :
      ∀ M : Mat2C,
        M * (gamma1 * (gamma3 * (gamma1Inv * gamma3Inv))) =
          -M := by
    intro M
    rw [gamma1_gamma3_commutator_assoc]
    simp

  have hmiddle :
      ∀ M : Mat2C,
        gamma1 * (M * (gamma3 * (gamma1Inv * gamma3Inv))) =
          -(gamma1 * (M * gamma1Inv)) := by
    intro M
    rw [gamma3_gamma1Inv_gamma3Inv]
    noncomm_ring

  have htail :
      ∀ M : Mat2C,
        gamma1 * (gamma3 * (gamma1Inv * (M * gamma3Inv))) =
          -(gamma3 * (M * gamma3Inv)) := by
    intro M
    calc
      gamma1 * (gamma3 * (gamma1Inv * (M * gamma3Inv)))
          =
        (gamma1 * gamma3) *
          (gamma1Inv * (M * gamma3Inv)) := by
            noncomm_ring
      _ =
        (-(gamma3 * gamma1)) *
          (gamma1Inv * (M * gamma3Inv)) := by
            rw [gamma1_mul_gamma3_eq_neg]
      _ =
        -(gamma3 *
          (gamma1 * (gamma1Inv * (M * gamma3Inv)))) := by
            noncomm_ring
      _ =
        -(gamma3 * (M * gamma3Inv)) := by
            rw [gamma1_gamma1Inv_mul]

  have hright0 :
      ((su2OfVec (X 0) * (gamma1 * gamma3)) * gamma1Inv) *
          gamma3Inv =
        -su2OfVec (X 0) := by
    calc
      ((su2OfVec (X 0) * (gamma1 * gamma3)) * gamma1Inv) *
            gamma3Inv
          =
        su2OfVec (X 0) *
          (gamma1 * (gamma3 * (gamma1Inv * gamma3Inv))) := by
            noncomm_ring
      _ = -su2OfVec (X 0) := by
            exact hcomm_right (su2OfVec (X 0))

  have hmiddle0 :
      ((gamma1 * (su2OfVec (X 2) * gamma3)) * gamma1Inv) *
          gamma3Inv =
        -(gamma1 * (su2OfVec (X 2) * gamma1Inv)) := by
    calc
      ((gamma1 * (su2OfVec (X 2) * gamma3)) * gamma1Inv) *
            gamma3Inv
          =
        gamma1 *
          (su2OfVec (X 2) *
            (gamma3 * (gamma1Inv * gamma3Inv))) := by
              noncomm_ring
      _ =
        -(gamma1 * (su2OfVec (X 2) * gamma1Inv)) := by
          exact hmiddle (su2OfVec (X 2))

  have htail0 :
      (gamma1 *
          (gamma3 * (gamma1Inv * su2OfVec (X 0)))) *
          gamma3Inv =
        -(gamma3 * (su2OfVec (X 0) * gamma3Inv)) := by
    calc
      (gamma1 *
          (gamma3 * (gamma1Inv * su2OfVec (X 0)))) *
            gamma3Inv
          =
        gamma1 *
          (gamma3 *
            (gamma1Inv *
              (su2OfVec (X 0) * gamma3Inv))) := by
                noncomm_ring
      _ =
        -(gamma3 * (su2OfVec (X 0) * gamma3Inv)) := by
          exact htail (su2OfVec (X 0))

  simp only [add_mul, neg_mul]

  rw [hright0, hmiddle0, htail0]
  rw [hcomm_mul (su2OfVec (X 2))]

  abel


theorem twistedPlaquetteDerivD_one_normalized
    (X : CellTangent) :
    twistedPlaquetteDerivD (1 : Fin 6) X =
      su2OfVec (plaquetteLinearization X (1 : Fin 6)) := by

  rw [twistedPlaquetteDerivD_one_formula]

  have hlin :
      plaquetteLinearization X (1 : Fin 6) =
        cellA (2 : Fin 4) (X 0) -
          cellA (0 : Fin 4) (X 2) := by
    simp [
      plaquetteLinearization,
      plaquetteMu,
      plaquetteNu
    ]

  rw [hlin]
  rw [su2OfVec_sub]

  rw [
    su2OfVec_cellA_eq_sub_twistConjugation
      (2 : Fin 4) (X 0)
  ]

  rw [
    su2OfVec_cellA_eq_sub_twistConjugation
      (0 : Fin 4) (X 2)
  ]

  simp [gamma, gammaInv]


/-!
## p=3 = (1,2) = Γ₂ / Γ₃
-/

/--
Reverse inverse for Γ₂, using the same literal-index proof style
that made the Γ₁ reverse inverse green in R10.
-/
theorem gamma2Inv_mul_gamma2 :
    gamma2Inv * gamma2 = (1 : Mat2C) := by
  funext i j
  fin_cases i <;> fin_cases j
  · change (gamma2Inv * gamma2) 0 0 = (1 : Mat2C) 0 0
    rw [mat2_mul_00]
    simp [gamma2Inv, gamma2]
  · change (gamma2Inv * gamma2) 0 1 = (1 : Mat2C) 0 1
    rw [mat2_mul_01]
    simp [gamma2Inv, gamma2]
  · change (gamma2Inv * gamma2) 1 0 = (1 : Mat2C) 1 0
    rw [mat2_mul_10]
    simp [gamma2Inv, gamma2]
  · change (gamma2Inv * gamma2) 1 1 = (1 : Mat2C) 1 1
    rw [mat2_mul_11]
    simp [gamma2Inv, gamma2]


theorem gamma2_gamma2Inv_mul
    (M : Mat2C) :
    gamma2 * (gamma2Inv * M) = M := by
  calc
    gamma2 * (gamma2Inv * M)
        = (gamma2 * gamma2Inv) * M := by
            rw [mul_assoc]
    _ = M := by
          rw [gamma2_mul_gamma2Inv]
          simp


theorem gamma2_gamma3_commutator_assoc :
    gamma2 * (gamma3 * (gamma2Inv * gamma3Inv)) =
      -(1 : Mat2C) := by
  calc
    gamma2 * (gamma3 * (gamma2Inv * gamma3Inv))
        =
      gamma2 * gamma3 * gamma2Inv * gamma3Inv := by
        noncomm_ring
    _ = -(1 : Mat2C) := gamma2_gamma3_commutator


theorem gamma3_gamma2Inv_gamma3Inv :
    gamma3 * (gamma2Inv * gamma3Inv) =
      -gamma2Inv := by
  calc
    gamma3 * (gamma2Inv * gamma3Inv)
        =
      (gamma2Inv * gamma2) *
        (gamma3 * (gamma2Inv * gamma3Inv)) := by
          rw [gamma2Inv_mul_gamma2]
          simp
    _ =
      gamma2Inv *
        (gamma2 * gamma3 * gamma2Inv * gamma3Inv) := by
          noncomm_ring
    _ = gamma2Inv * (-(1 : Mat2C)) := by
          rw [gamma2_gamma3_commutator]
    _ = -gamma2Inv := by
          simp


theorem twistedPlaquetteDerivD_three_formula
    (X : CellTangent) :
    twistedPlaquetteDerivD (3 : Fin 6) X =
      (su2OfVec (X 1) -
        gamma3 * su2OfVec (X 1) * gamma3Inv)
      -
      (su2OfVec (X 2) -
        gamma2 * su2OfVec (X 2) * gamma2Inv) := by

  simp only [
    twistedPlaquetteDerivD,
    rawPlaquetteDerivD,
    tripleDerivD,
    pairDerivD,
    cellLinkDerivD,
    cellInverseLinkDerivD,
    cellLinkD_zero,
    cellInverseLinkD_zero,
    twistMatrixD,
    twistCenter,
    plaquetteMu,
    plaquetteNu,
    gamma,
    gammaInv
  ]

  try simp
  simp only [mul_assoc]

  have hcomm_mul :
      ∀ M : Mat2C,
        gamma2 * (gamma3 * (gamma2Inv * (gamma3Inv * M))) =
          -M := by
    intro M
    calc
      gamma2 * (gamma3 * (gamma2Inv * (gamma3Inv * M)))
          =
        (gamma2 * (gamma3 * (gamma2Inv * gamma3Inv))) * M := by
          noncomm_ring
      _ = (-(1 : Mat2C)) * M := by
          rw [gamma2_gamma3_commutator_assoc]
      _ = -M := by
          simp

  have hcomm_right :
      ∀ M : Mat2C,
        M * (gamma2 * (gamma3 * (gamma2Inv * gamma3Inv))) =
          -M := by
    intro M
    rw [gamma2_gamma3_commutator_assoc]
    simp

  have hmiddle :
      ∀ M : Mat2C,
        gamma2 * (M * (gamma3 * (gamma2Inv * gamma3Inv))) =
          -(gamma2 * (M * gamma2Inv)) := by
    intro M
    rw [gamma3_gamma2Inv_gamma3Inv]
    noncomm_ring

  have htail :
      ∀ M : Mat2C,
        gamma2 * (gamma3 * (gamma2Inv * (M * gamma3Inv))) =
          -(gamma3 * (M * gamma3Inv)) := by
    intro M
    calc
      gamma2 * (gamma3 * (gamma2Inv * (M * gamma3Inv)))
          =
        (gamma2 * gamma3) *
          (gamma2Inv * (M * gamma3Inv)) := by
            noncomm_ring
      _ =
        (-(gamma3 * gamma2)) *
          (gamma2Inv * (M * gamma3Inv)) := by
            rw [gamma2_mul_gamma3_eq_neg]
      _ =
        -(gamma3 *
          (gamma2 * (gamma2Inv * (M * gamma3Inv)))) := by
            noncomm_ring
      _ =
        -(gamma3 * (M * gamma3Inv)) := by
            rw [gamma2_gamma2Inv_mul]

  have hright0 :
      ((su2OfVec (X 1) * (gamma2 * gamma3)) * gamma2Inv) *
          gamma3Inv =
        -su2OfVec (X 1) := by
    calc
      ((su2OfVec (X 1) * (gamma2 * gamma3)) * gamma2Inv) *
            gamma3Inv
          =
        su2OfVec (X 1) *
          (gamma2 * (gamma3 * (gamma2Inv * gamma3Inv))) := by
            noncomm_ring
      _ = -su2OfVec (X 1) := by
            exact hcomm_right (su2OfVec (X 1))

  have hmiddle0 :
      ((gamma2 * (su2OfVec (X 2) * gamma3)) * gamma2Inv) *
          gamma3Inv =
        -(gamma2 * (su2OfVec (X 2) * gamma2Inv)) := by
    calc
      ((gamma2 * (su2OfVec (X 2) * gamma3)) * gamma2Inv) *
            gamma3Inv
          =
        gamma2 *
          (su2OfVec (X 2) *
            (gamma3 * (gamma2Inv * gamma3Inv))) := by
              noncomm_ring
      _ =
        -(gamma2 * (su2OfVec (X 2) * gamma2Inv)) := by
          exact hmiddle (su2OfVec (X 2))

  have htail0 :
      (gamma2 *
          (gamma3 * (gamma2Inv * su2OfVec (X 1)))) *
          gamma3Inv =
        -(gamma3 * (su2OfVec (X 1) * gamma3Inv)) := by
    calc
      (gamma2 *
          (gamma3 * (gamma2Inv * su2OfVec (X 1)))) *
            gamma3Inv
          =
        gamma2 *
          (gamma3 *
            (gamma2Inv *
              (su2OfVec (X 1) * gamma3Inv))) := by
                noncomm_ring
      _ =
        -(gamma3 * (su2OfVec (X 1) * gamma3Inv)) := by
          exact htail (su2OfVec (X 1))

  simp only [add_mul, neg_mul]

  rw [hright0, hmiddle0, htail0]
  rw [hcomm_mul (su2OfVec (X 2))]

  abel


theorem twistedPlaquetteDerivD_three_normalized
    (X : CellTangent) :
    twistedPlaquetteDerivD (3 : Fin 6) X =
      su2OfVec (plaquetteLinearization X (3 : Fin 6)) := by

  rw [twistedPlaquetteDerivD_three_formula]

  have hlin :
      plaquetteLinearization X (3 : Fin 6) =
        cellA (2 : Fin 4) (X 1) -
          cellA (1 : Fin 4) (X 2) := by
    simp [
      plaquetteLinearization,
      plaquetteMu,
      plaquetteNu
    ]

  rw [hlin]
  rw [su2OfVec_sub]

  rw [
    su2OfVec_cellA_eq_sub_twistConjugation
      (2 : Fin 4) (X 1)
  ]

  rw [
    su2OfVec_cellA_eq_sub_twistConjugation
      (1 : Fin 4) (X 2)
  ]

  simp [gamma, gammaInv]


#print axioms gamma1_gamma3_commutator_assoc
#print axioms gamma3_gamma1Inv_gamma3Inv
#print axioms twistedPlaquetteDerivD_one_formula
#print axioms twistedPlaquetteDerivD_one_normalized

#print axioms gamma2Inv_mul_gamma2
#print axioms gamma2_gamma2Inv_mul
#print axioms gamma2_gamma3_commutator_assoc
#print axioms gamma3_gamma2Inv_gamma3Inv
#print axioms twistedPlaquetteDerivD_three_formula
#print axioms twistedPlaquetteDerivD_three_normalized



/-!
# YM-013 — final individual plaquette p=2

p=2 = internal (0,3), manuscript (1,4).

Since Γ₄ = I and A₄ = 0, this is the gamma1 identity-direction
analogue of the already-green p=4/p=5 structural proofs.
-/

theorem twistedPlaquetteDerivD_two_formula
    (X : CellTangent) :
    twistedPlaquetteDerivD (2 : Fin 6) X =
      gamma1 * su2OfVec (X 3) * gamma1Inv -
        su2OfVec (X 3) := by

  simp only [
    twistedPlaquetteDerivD,
    rawPlaquetteDerivD,
    tripleDerivD,
    pairDerivD,
    cellLinkDerivD,
    cellInverseLinkDerivD,
    cellLinkD_zero,
    cellInverseLinkD_zero,
    twistMatrixD,
    twistCenter,
    plaquetteMu,
    plaquetteNu,
    gamma,
    gammaInv,
    gamma4_eq_one,
    gamma4Inv_eq_one
  ]

  -- Collapse only finite lookups / identity-direction scaffolding.
  -- gamma1 and gamma1Inv remain structural.
  simp

  rw [add_mul]

  -- (A Γ₁) Γ₁⁻¹ = A
  rw [mul_assoc (su2OfVec (X 0)) gamma1 gamma1Inv]
  rw [gamma1_mul_gamma1Inv]
  rw [mul_one]

  -- Γ₁ (Γ₁⁻¹ A) = A
  rw [← mul_assoc gamma1 gamma1Inv (su2OfVec (X 0))]
  rw [gamma1_mul_gamma1Inv]
  rw [one_mul]

  noncomm_ring


theorem twistedPlaquetteDerivD_two_normalized
    (X : CellTangent) :
    twistedPlaquetteDerivD (2 : Fin 6) X =
      su2OfVec (plaquetteLinearization X (2 : Fin 6)) := by

  rw [twistedPlaquetteDerivD_two_formula]

  have hconj :
      su2OfVec (cellA (0 : Fin 4) (X 3)) =
        su2OfVec (X 3) -
          gamma1 * su2OfVec (X 3) * gamma1Inv := by
    simpa [gamma, gammaInv] using
      (su2OfVec_cellA_eq_sub_twistConjugation
        (0 : Fin 4) (X 3))

  change
    gamma1 * su2OfVec (X 3) * gamma1Inv -
        su2OfVec (X 3) =
      su2OfVec
        (cellA (3 : Fin 4) (X 0) -
          cellA (0 : Fin 4) (X 3))

  have hA4 :
      cellA (3 : Fin 4) (X 0) = 0 := by
    funext a
    fin_cases a <;>
      simp [cellA, A4]

  rw [hA4]
  rw [su2OfVec_sub]

  have hzero :
      su2OfVec (0 : Vec3) = 0 := by
    funext i j
    fin_cases i <;> fin_cases j <;>
      simp [su2OfVec]

  rw [hzero, hconj]
  abel


#print axioms twistedPlaquetteDerivD_two_formula
#print axioms twistedPlaquetteDerivD_two_normalized



/-!
# YM-013 — six-plaquette capstone

All six individual nonlinear derivative normalization theorems
are already independently green.  This theorem packages them into
the universal Fin 6 endpoint.
-/

/--
**YM-013 headline theorem.**

For every twisted plaquette and every cell tangent X, the derivative
of the genuine nonlinear exponential twisted plaquette at the
twist-eater background is exactly the Pauli realization of the
previously formalized linearized plaquette map.
-/
theorem twistedPlaquetteDerivD_eq_su2OfVec_linearization
    (p : Fin 6) (X : CellTangent) :
    twistedPlaquetteDerivD p X =
      su2OfVec (plaquetteLinearization X p) := by
  fin_cases p
  · exact twistedPlaquetteDerivD_zero_normalized X
  · exact twistedPlaquetteDerivD_one_normalized X
  · exact twistedPlaquetteDerivD_two_normalized X
  · exact twistedPlaquetteDerivD_three_normalized X
  · exact twistedPlaquetteDerivD_four_normalized X
  · exact twistedPlaquetteDerivD_five_normalized X


#print axioms twistedPlaquetteDerivD_eq_su2OfVec_linearization


end SU2
end YMFormalization
