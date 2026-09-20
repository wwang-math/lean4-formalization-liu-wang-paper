import LiuWang.LiuWang2025SemilinearWaveLeadingAmplitudeTransport

/-!
# Liu--Wang 2025: source-consistency audit for the leading amplitude

The expansion displayed in equation (3.9) contains

`2 * partial_s b_(0,0) + Tr(C H) * b_(0,0)`.

The immediately following scalar display in arXiv:2511.08794v1 omits the
factor `b_(0,0)`.  This module proves that the omission changes the equation;
it is not a harmless normalization.  It also records a scalar diagnostic for
the subsequent logarithmic-determinant identity.  For the displayed system
`Y' = C Z`, `H = Z Y^-1`, the logarithmic derivative generated directly by
the system is that of `Y`.  A concrete scalar Riccati witness agrees with the
`Y` ratio and disagrees with the printed `H` ratio.

The audit does not amend the source paper.  It prevents the verification
platform from silently using either display and supplies the corrected,
branch-free transport theorem as the checked continuation.
-/

noncomputable section

namespace LiuWang2025SemilinearWaveSourceConsistencyAudit

open LiuWang2025SemilinearWaveLeadingAmplitudeTransport

/-- Residual dictated by the equation-(3.9) expansion. -/
def correctedLeadingResidual (q b db : Complex) : Complex :=
  2 * db + q * b

/-- Residual in the standalone display after equation (3.9), where the
amplitude factor is absent. -/
def printedLeadingResidual (q db : Complex) : Complex :=
  2 * db + q

/-- A unit-coefficient transport solution with initial value two. -/
def auditAmplitude : Real -> Complex :=
  leadingAmplitude (fun _ => 1) 0 2

@[simp] theorem auditAmplitude_at_initial : auditAmplitude 0 = 2 := by
  simp [auditAmplitude]

/-- The actual derivative of the audit amplitude at the initial point. -/
theorem auditAmplitude_hasDerivAt : HasDerivAt auditAmplitude (-1) 0 := by
  simpa [auditAmplitude] using
    leadingAmplitude_hasDerivAt (fun _ : Real => (1 : Complex))
      continuous_const 0 2 0

/-- The equation-(3.9) residual vanishes for the audit solution. -/
theorem correctedLeadingResidual_at_initial :
    correctedLeadingResidual 1 (auditAmplitude 0) (-1) = 0 := by
  norm_num [correctedLeadingResidual]

/-- The printed residual after equation (3.9) does not vanish for the same
solution and derivative. -/
theorem printedLeadingResidual_at_initial :
    printedLeadingResidual 1 (-1) = -1 := by
  norm_num [printedLeadingResidual]

theorem printedLeadingResidual_at_initial_ne_zero :
    printedLeadingResidual 1 (-1) ≠ 0 := by
  norm_num [printedLeadingResidual]

/-- Omitting the amplitude factor materially changes the scalar ODE. -/
theorem omitted_amplitude_factor_changes_equation :
    ∃ q b db : Complex,
      correctedLeadingResidual q b db = 0 ∧
      printedLeadingResidual q db ≠ 0 := by
  exact ⟨1, auditAmplitude 0, -1, correctedLeadingResidual_at_initial,
    printedLeadingResidual_at_initial_ne_zero⟩

/-! ## Scalar diagnostic for the logarithmic-determinant display -/

/-- Algebraic logarithmic derivative, used without choosing a complex
logarithm branch. -/
def logarithmicDerivativeRatio (du u : Complex) : Complex := du / u

/-- At the initial point of `Y(s) = 1 + i s`, `H(s) = i/(1+i s)`, the
displayed linear Hamiltonian system has these scalar values. -/
def witnessY : Complex := 1
def witnessDY : Complex := Complex.I
def witnessH : Complex := Complex.I
def witnessDH : Complex := 1
def witnessTraceCH : Complex := Complex.I

/-- The `Y` logarithmic derivative agrees with `Tr(C H)` in the scalar
witness. -/
theorem witness_Y_ratio_eq_traceCH :
    logarithmicDerivativeRatio witnessDY witnessY = witnessTraceCH := by
  norm_num [logarithmicDerivativeRatio, witnessDY, witnessY, witnessTraceCH]

/-- The printed `H` logarithmic derivative does not agree with `Tr(C H)` in
the same scalar Riccati witness. -/
theorem witness_H_ratio_ne_traceCH :
    logarithmicDerivativeRatio witnessDH witnessH ≠ witnessTraceCH := by
  norm_num [logarithmicDerivativeRatio, witnessDH, witnessH, witnessTraceCH,
    Complex.ext_iff]

/-- Compact machine-checkable record of both source diagnostics and the
corrected transport continuation. -/
structure Certificate : Prop where
  amplitudeDerivative : HasDerivAt auditAmplitude (-1) 0
  correctedEquation : correctedLeadingResidual 1 (auditAmplitude 0) (-1) = 0
  printedEquationFails : printedLeadingResidual 1 (-1) ≠ 0
  yLogarithmicDerivativeMatches :
    logarithmicDerivativeRatio witnessDY witnessY = witnessTraceCH
  hLogarithmicDerivativeFails :
    logarithmicDerivativeRatio witnessDH witnessH ≠ witnessTraceCH
  correctedTransportAvailable :
    ∀ (q : Real -> Complex), Continuous q →
      ∀ (s0 : Real) (initial : Complex) (s : Real),
        HasDerivAt (leadingAmplitude q s0 initial)
            (-((2 : Complex)⁻¹) * q s * leadingAmplitude q s0 initial s) s ∧
          correctedLeadingResidual (q s) (leadingAmplitude q s0 initial s)
            (-((2 : Complex)⁻¹) * q s *
              leadingAmplitude q s0 initial s) = 0

def certificate : Certificate where
  amplitudeDerivative := auditAmplitude_hasDerivAt
  correctedEquation := correctedLeadingResidual_at_initial
  printedEquationFails := printedLeadingResidual_at_initial_ne_zero
  yLogarithmicDerivativeMatches := witness_Y_ratio_eq_traceCH
  hLogarithmicDerivativeFails := witness_H_ratio_ne_traceCH
  correctedTransportAvailable := by
    intro q hq s0 initial s
    have h := leadingAmplitude_solves_transport q hq s0 initial s
    exact ⟨h.1, by simpa [correctedLeadingResidual] using h.2⟩

end LiuWang2025SemilinearWaveSourceConsistencyAudit
