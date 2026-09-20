import LiuWang.LiuWang2025SemilinearWaveComplexStationaryPhaseComposition

/-!
# Liu--Wang complex stationary-phase calibration

This module packages the complex stationary-phase calculation used near
equation (4.4) of Liu--Wang into reviewable certificates.  The phase value,
stationarity, local imaginary coercivity, nonvanishing complex Gaussian
constant, leading limit, and the quantitative `O(rho^(-1/2))` estimate are
all generated from the stated phase and amplitude hypotheses.

The certificate deliberately does not assert the paper's sharper
`O(rho^(-2))` remainder.  That estimate requires source-specific amplitude
jets and cancellations beyond the generic stationary-phase hypotheses; the
conditional composition theorem keeps that obligation visible.
-/

noncomputable section

open Filter MeasureTheory
open scoped Real Topology

namespace LiuWang2025SemilinearWaveComplexStationaryPhase

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace Real V]
  [FiniteDimensional Real V] [MeasurableSpace V] [BorelSpace V]

/-- Certificate for the generic complex stationary-phase layer. -/
structure CalibrationCertificate
    (mu : Measure V) [mu.IsAddHaarMeasure]
    (P : PhaseData V) (F : AmplitudeFamily V P.p P.r) : Prop where
  phaseValue : P.S P.p = 0
  phaseDerivative : fderiv Real P.S P.p = 0
  phaseImaginaryCoercivity : forall {h : V},
    ‖h‖ <= P.r -> P.c / 4 * ‖h‖ ^ 2 <= (P.S (P.p + h)).im
  gaussianConstantNonzero : gaussConst mu P.H ≠ 0
  leadingLimit :
    Tendsto (fun rho : Real => oscIntegral mu P F rho) atTop
      (nhds (F.lead * gaussConst mu P.H))
  genericRemainderRate :
    (fun rho : Real =>
        oscIntegral mu P F rho - F.a rho P.p * gaussConst mu P.H)
      =O[atTop] (fun rho : Real => (Real.sqrt rho)⁻¹)

/-- The calibration certificate contains no conclusion-shaped analytic
hypothesis: each field is filled by a theorem of the complex phase model. -/
def calibrationCertificate
    (mu : Measure V) [mu.IsAddHaarMeasure]
    (P : PhaseData V) (F : AmplitudeFamily V P.p P.r) :
    CalibrationCertificate mu P F where
  phaseValue := P.phase_apply_stationaryPoint
  phaseDerivative := P.fderiv_phase_eq_zero
  phaseImaginaryCoercivity := fun hh => P.im_phase_ge hh
  gaussianConstantNonzero := gaussConst_phase_ne_zero mu P
  leadingLimit := oscIntegral_tendsto mu P F
  genericRemainderRate := remainder_isBigO mu P F

/-- Certificate for the non-Haar chart measure.  It records both the exact
Jacobian adapter and the resulting leading asymptotic. -/
structure ChartCalibrationCertificate
    (mu : Measure V) [mu.IsAddHaarMeasure]
    (P : PhaseData V) (F : AmplitudeFamily V P.p P.r)
    (Jd : ChartDensity V) : Prop where
  chartAdapter : forall rho : Real,
    oscIntegral (Jd.measure mu) P F rho =
      oscIntegral mu P (F.mulDensity Jd) rho
  chartIntegrable : forall {rho : Real}, 0 < rho ->
    Integrable (oscIntegrand P F rho) (Jd.measure mu)
  chartLeadingLimit :
    Tendsto (fun rho : Real => oscIntegral (Jd.measure mu) P F rho) atTop
      (nhds (((Jd.J P.p : Complex) * F.lead) * gaussConst mu P.H))

def chartCalibrationCertificate
    (mu : Measure V) [mu.IsAddHaarMeasure]
    (P : PhaseData V) (F : AmplitudeFamily V P.p P.r)
    (Jd : ChartDensity V) : ChartCalibrationCertificate mu P F Jd where
  chartAdapter := oscIntegral_chartMeasure mu P F Jd
  chartIntegrable := integrable_oscIntegrand_chartMeasure mu P F Jd
  chartLeadingLimit := chartOscIntegral_tendsto mu P F Jd

/-- The exact additional statement needed to upgrade the generic
stationary-phase error to the `rho^(-2)` scale used in equation (4.4). -/
def PaperOrderTwoStationaryPhaseInput
    (mu : Measure V) (P : PhaseData V) (F : AmplitudeFamily V P.p P.r) : Prop :=
  (fun rho : Real => oscIntegral mu P F rho - F.lead * gaussConst mu P.H)
    =O[atTop] beamScale

end LiuWang2025SemilinearWaveComplexStationaryPhase
