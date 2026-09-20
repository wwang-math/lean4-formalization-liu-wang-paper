import LiuWang.LiuWang2025SemilinearWaveVerification
import LiuWang.LiuWang2025SemilinearWaveRiccatiExistenceExamples

noncomputable section

namespace LiuWangLeadingAmplitudeTransportTest

open LiuWang2025SemilinearWaveGaussianLocalization
open LiuWang2025SemilinearWaveDeterminantJacobi
open LiuWang2025SemilinearWaveLeadingAmplitudeTransport
open LiuWang2025SemilinearWaveLeadingAmplitudeTransport.RiccatiGeneratedTransport

/-- A nonzero leading amplitude cannot acquire a zero through complex
transport, even for an oscillatory coefficient. -/
example (s : Real) :
    leadingAmplitude (fun _ => Complex.I) 0 3 s ≠ 0 := by
  apply leadingAmplitude_ne_zero
  norm_num

example (s : Real) :
    HasDerivAt (leadingAmplitude (fun _ => Complex.I) 0 3)
      (-((2 : Complex)⁻¹) * Complex.I *
        leadingAmplitude (fun _ => Complex.I) 0 3 s) s := by
  exact leadingAmplitude_hasDerivAt
    (fun _ => Complex.I) continuous_const 0 3 s

/-- A nontrivial exact Jacobi path checks the branch-free invariant behind
the determinant amplitude formula. -/
example (s : Real) :
    HasDerivAt
      (fun t : Real =>
        leadingAmplitude (fun _ => 1) 0 2 t ^ 2 * Complex.exp t) 0 s := by
  apply leadingAmplitude_sq_mul_jacobiPath_hasDerivAt_zero
    (fun _ : Real => (1 : Complex)) continuous_const 0 2
    (fun t : Real => Complex.exp t) s
  simpa using (Complex.hasDerivAt_exp (s : Complex)).comp_ofReal

/-- The pointwise zero derivative closes to the exact invariant on the whole
unordered interval. -/
example (s : Real) :
    leadingAmplitude (fun _ => 1) 0 2 s ^ 2 * Complex.exp s = 4 := by
  convert
    (leadingAmplitude_sq_mul_jacobiPath_eq_initial
      (fun _ : Real => (1 : Complex)) continuous_const 0 2
      (fun t : Real => Complex.exp t) s (by
        intro t _
        simpa using (Complex.hasDerivAt_exp (t : Complex)).comp_ofReal)) using 1;
    norm_num

def fourConstantBeams : FourBeamTransportData where
  q := fun _ _ => 0
  q_continuous := fun _ => continuous_const
  initialTime := fun _ => 0
  arrivalTime := fun _ => 1
  initialAmplitude := fun _ => 1
  initialAmplitude_ne_zero := fun _ => one_ne_zero

def registeredConstantBeams : FourBeamPointRegistration PUnit where
  point := PUnit.unit
  amplitude := fun _ _ => 1
  transport := fourConstantBeams
  amplitude_at_point := by
    intro j
    simp [FourBeamTransportData.transportedAmplitude, fourConstantBeams,
      leadingAmplitude]

example :
    amplitudeProductAt
      (registeredConstantBeams.amplitude 0)
      (registeredConstantBeams.amplitude 1)
      (registeredConstantBeams.amplitude 2)
      (registeredConstantBeams.amplitude 3)
      registeredConstantBeams.point ≠ 0 :=
  registeredConstantBeams.amplitudeProductAt_ne_zero

/-- Four concrete nonconstant Riccati flows exercise the generated
`Tr(C H)` coefficient and product route. -/
def fourRiccatiBeams : RiccatiFourBeamTransportData (Fin 2) where
  coefficients := fun _ =>
    LiuWang2025SemilinearWaveRiccatiExistenceExamples.coefficients
  arrivalTime := fun _ => 1
  arrival_mem := by
    intro j
    norm_num [LiuWang2025SemilinearWaveRiccatiExistenceExamples.coefficients]
  initialAmplitude := fun _ => 1
  initialAmplitude_ne_zero := fun _ => one_ne_zero

example :
    traceTransportCoefficient
        LiuWang2025SemilinearWaveRiccatiExistenceExamples.coefficients 1 =
      Matrix.trace
        (LiuWang2025SemilinearWaveRiccatiExistenceExamples.coefficients.C 1 *
          LiuWang2025SemilinearWaveRiccatiExistenceExamples.coefficients.toRiccatiFlow.H 1) := by
  apply traceTransportCoefficient_eq_trace_CH
  norm_num [LiuWang2025SemilinearWaveRiccatiExistenceExamples.coefficients]

example :
    RiccatiFourBeamTransportData.FourBeamCertificate fourRiccatiBeams :=
  fourRiccatiBeams.fourBeamCertificate

/-- The nonconstant generated matrix flow supplies its own determinant
Jacobi equation; no source-level derivative witness is passed to the test. -/
example :
    HasDerivAt
      (fun s =>
        (LiuWang2025SemilinearWaveRiccatiExistenceExamples.coefficients.toRiccatiFlow.Y s).det)
      (Matrix.trace
          (LiuWang2025SemilinearWaveRiccatiExistenceExamples.coefficients.C 1 *
            LiuWang2025SemilinearWaveRiccatiExistenceExamples.coefficients.toRiccatiFlow.H 1) *
        (LiuWang2025SemilinearWaveRiccatiExistenceExamples.coefficients.toRiccatiFlow.Y 1).det) 1 := by
  apply generated_detY_hasDerivAt
  norm_num [LiuWang2025SemilinearWaveRiccatiExistenceExamples.coefficients]

example :
    GeneratedDeterminantCertificate
      LiuWang2025SemilinearWaveRiccatiExistenceExamples.coefficients 2 :=
  generatedDeterminantCertificate
    LiuWang2025SemilinearWaveRiccatiExistenceExamples.coefficients 2

/-- The generated Jacobi equation and scalar transport close to the exact
interval invariant with `Y(0)=I`. -/
example :
    leadingAmplitude
        (traceTransportCoefficient
          LiuWang2025SemilinearWaveRiccatiExistenceExamples.coefficients)
        0 2 1 ^ 2 *
      (LiuWang2025SemilinearWaveRiccatiExistenceExamples.coefficients.toRiccatiFlow.Y 1).det = 4 := by
  convert generated_leadingAmplitude_sq_mul_detY_eq_initial
    LiuWang2025SemilinearWaveRiccatiExistenceExamples.coefficients 2 (t := 1) (by
      norm_num [LiuWang2025SemilinearWaveRiccatiExistenceExamples.coefficients]) using 1;
    norm_num [LiuWang2025SemilinearWaveRiccatiExistenceExamples.coefficients]

example :
    (∏ j, fourRiccatiBeams.toFourBeamTransportData.transportedAmplitude j) ≠ 0 :=
  LiuWang2025SemilinearWaveVerification.riccatiFourBeamLeadingTransportVerificationBundle_product
    fourRiccatiBeams

#check LiuWang2025SemilinearWaveLeadingAmplitudeTransport.TransportGeneratedGaussianPointRecoveryData.coefficient_at_point_eq_zero
#check LiuWang2025SemilinearWaveVerification.leadingAmplitudeTransportVerificationBundle_endpoint
#check LiuWang2025SemilinearWaveVerification.leadingAmplitudeTransportNonvanishing_is_verified
#check LiuWang2025SemilinearWaveVerification.riccatiGeneratedLeadingTransportCoefficient_is_verified
#check LiuWang2025SemilinearWaveVerification.riccatiGeneratedLeadingTransportVerificationBundle
#check LiuWang2025SemilinearWaveVerification.riccatiGeneratedDetYJacobiVerificationBundle
#check LiuWang2025SemilinearWaveVerification.riccatiGeneratedDeterminantAmplitudeVerificationBundle
#check LiuWang2025SemilinearWaveVerification.riccatiDeterminantAmplitudeVerificationBundle
#check LiuWang2025SemilinearWaveVerification.riccatiIntervalDeterminantAmplitudeVerificationBundle
#check LiuWang2025SemilinearWaveVerification.riccatiFourBeamLeadingTransportVerificationBundle
#check LiuWang2025SemilinearWaveSourceConsistencyAudit.omitted_amplitude_factor_changes_equation
#check LiuWang2025SemilinearWaveSourceConsistencyAudit.witness_Y_ratio_eq_traceCH
#check LiuWang2025SemilinearWaveSourceConsistencyAudit.witness_H_ratio_ne_traceCH
#check LiuWang2025SemilinearWaveVerification.leadingAmplitudeSourceConsistencyVerificationBundle

#print axioms LiuWang2025SemilinearWaveLeadingAmplitudeTransport.leadingAmplitude_solves_transport
#print axioms LiuWang2025SemilinearWaveLeadingAmplitudeTransport.RiccatiGeneratedTransport.leadingAmplitude_solves_trace_CH_transport
#print axioms LiuWang2025SemilinearWaveLeadingAmplitudeTransport.RiccatiGeneratedTransport.certificate
#print axioms LiuWang2025SemilinearWaveLeadingAmplitudeTransport.RiccatiGeneratedTransport.determinantCertificate
#print axioms LiuWang2025SemilinearWaveLeadingAmplitudeTransport.RiccatiGeneratedTransport.intervalDeterminantCertificate
#print axioms LiuWang2025SemilinearWaveDeterminantJacobi.det_path_hasDerivAt
#print axioms LiuWang2025SemilinearWaveDeterminantJacobi.generated_detY_hasDerivAt
#print axioms LiuWang2025SemilinearWaveLeadingAmplitudeTransport.RiccatiGeneratedTransport.generatedDeterminantCertificate
#print axioms LiuWang2025SemilinearWaveLeadingAmplitudeTransport.RiccatiFourBeamTransportData.fourBeamCertificate
#print axioms LiuWang2025SemilinearWaveLeadingAmplitudeTransport.FourBeamPointRegistration.amplitudeProductAt_ne_zero
#print axioms LiuWang2025SemilinearWaveLeadingAmplitudeTransport.TransportGeneratedGaussianPointRecoveryData.coefficient_at_point_eq_zero
#print axioms LiuWang2025SemilinearWaveSourceConsistencyAudit.certificate

end LiuWangLeadingAmplitudeTransportTest
