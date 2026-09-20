import LiuWang.LiuWang2025SemilinearWaveComplexStationaryPhaseComposition

/-!
# Liu--Wang equation (4.4): rate-robust recovery

The source writes the normalized stationary-phase expansion with an
`O(rho^(-2))` remainder.  That quantitative order is stronger than the
uniqueness argument requires.  The recovery step only uses convergence of the
normalized interaction to its nonzero Gaussian leading term and convergence
of the beam-substitution remainder to zero.

This module records that weaker, source-faithful logical dependency.  It
combines the verified complex stationary-phase limit in a local chart with an
arbitrary vanishing beam remainder.  Once the leading amplitude is identified
with the stationary prefactor, the unknown coefficient, and the product of
the four beam amplitudes, Lean recovers the coefficient without assuming the
paper's stronger stationary-phase `O(rho^(-2))` estimate.
-/

noncomputable section

open Filter MeasureTheory
open scoped Real Topology

namespace LiuWang2025SemilinearWaveEquation44RateRobustRecovery

open LiuWang2025SemilinearWaveComplexStationaryPhase

section ChartComposition

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace Real V]
  [FiniteDimensional Real V] [MeasurableSpace V] [BorelSpace V]

/-- A local-chart stationary-phase quantity keeps its leading limit after any
additive remainder that merely tends to zero. -/
theorem chart_composed_tendsto_of_remainder_tendsto
    (mu : Measure V) [mu.IsAddHaarMeasure]
    (P : PhaseData V) (F : AmplitudeFamily V P.p P.r)
    (Jd : ChartDensity V) (measured remainder : Real -> Complex)
    (hdecomp : forall rho,
      measured rho = oscIntegral (Jd.measure mu) P F rho + remainder rho)
    (hremainder : Tendsto remainder atTop (nhds 0)) :
    Tendsto measured atTop
      (nhds (((Jd.J P.p : Complex) * F.lead) * gaussConst mu P.H)) := by
  have hdecomp' : forall rho,
      measured rho = oscIntegral mu P (F.mulDensity Jd) rho + remainder rho := by
    intro rho
    rw [hdecomp rho, oscIntegral_chartMeasure mu P F Jd rho]
  have hlimit := composed_tendsto mu P (F.mulDensity Jd)
    measured remainder hdecomp' hremainder
  rwa [AmplitudeFamily.mulDensity_lead] at hlimit

/-- If the measured interaction and its additive beam remainder both vanish,
the limiting amplitude at the interaction point vanishes.  No quantitative
stationary-phase rate is used. -/
theorem chart_composed_lead_eq_zero_of_remainder_tendsto
    (mu : Measure V) [mu.IsAddHaarMeasure]
    (P : PhaseData V) (F : AmplitudeFamily V P.p P.r)
    (Jd : ChartDensity V) (measured remainder : Real -> Complex)
    (hJ : Jd.J P.p ≠ 0)
    (hdecomp : forall rho,
      measured rho = oscIntegral (Jd.measure mu) P F rho + remainder rho)
    (hremainder : Tendsto remainder atTop (nhds 0))
    (hmeasured : Tendsto measured atTop (nhds 0)) :
    F.lead = 0 := by
  have hlimit := chart_composed_tendsto_of_remainder_tendsto
    mu P F Jd measured remainder hdecomp hremainder
  have hzero :
      ((Jd.J P.p : Complex) * F.lead) * gaussConst mu P.H = 0 :=
    tendsto_nhds_unique hlimit hmeasured
  rcases mul_eq_zero.mp hzero with hJacobianLead | hGaussian
  · rcases mul_eq_zero.mp hJacobianLead with hJacobian | hlead
    · exact (hJ (Complex.ofReal_eq_zero.mp hJacobian)).elim
    · exact hlead
  · exact (gaussConst_phase_ne_zero mu P hGaussian).elim

variable (mu : Measure V) [mu.IsAddHaarMeasure]

/-- Source-facing data for the recovery consequence of equation (4.4).
The analytic remainder is required only to vanish; the paper-order
`O(rho^(-2))` stationary-phase estimate is not a field. -/
structure RateRobustEquation44Data where
  phase : PhaseData V
  amplitude : AmplitudeFamily V phase.p phase.r
  chartDensity : ChartDensity V
  measured : Real -> Complex
  beamRemainder : Real -> Complex
  coefficient : Complex
  stationaryPrefactor : Complex
  amplitudeProduct : Complex
  chartJacobian_ne_zero : chartDensity.J phase.p ≠ 0
  stationaryPrefactor_ne_zero : stationaryPrefactor ≠ 0
  amplitudeProduct_ne_zero : amplitudeProduct ≠ 0
  lead_identification :
    amplitude.lead = stationaryPrefactor * coefficient * amplitudeProduct
  decomposition : forall rho,
    measured rho =
      oscIntegral (chartDensity.measure mu) phase amplitude rho + beamRemainder rho
  beamRemainder_tendsto_zero : Tendsto beamRemainder atTop (nhds 0)
  measured_tendsto_zero : Tendsto measured atTop (nhds 0)

namespace RateRobustEquation44Data

/-- The complete normalized interaction has the chart-correct Gaussian
stationary-phase limit. -/
theorem measured_tendsto_leading
    (data : RateRobustEquation44Data (V := V) mu) :
    Tendsto data.measured atTop
      (nhds
        (((data.chartDensity.J data.phase.p : Complex) * data.amplitude.lead) *
          gaussConst mu data.phase.H)) :=
  chart_composed_tendsto_of_remainder_tendsto
    mu data.phase data.amplitude data.chartDensity
    data.measured data.beamRemainder data.decomposition
    data.beamRemainder_tendsto_zero

/-- The measured zero limit forces the registered leading amplitude to
vanish. -/
theorem lead_eq_zero
    (data : RateRobustEquation44Data (V := V) mu) :
    data.amplitude.lead = 0 :=
  chart_composed_lead_eq_zero_of_remainder_tendsto
    mu data.phase data.amplitude data.chartDensity
    data.measured data.beamRemainder data.chartJacobian_ne_zero
    data.decomposition data.beamRemainder_tendsto_zero
    data.measured_tendsto_zero

/-- Rate-robust equation-(4.4) endpoint: the unknown coefficient vanishes.
The proof uses only convergence, plus nonvanishing of the stationary,
Jacobian, Gaussian, and beam-amplitude factors. -/
theorem coefficient_eq_zero
    (data : RateRobustEquation44Data (V := V) mu) :
    data.coefficient = 0 := by
  have hlead := data.lead_eq_zero
  rw [data.lead_identification] at hlead
  rcases mul_eq_zero.mp hlead with hPrefactorCoefficient | hAmplitude
  · rcases mul_eq_zero.mp hPrefactorCoefficient with hPrefactor | hCoefficient
    · exact (data.stationaryPrefactor_ne_zero hPrefactor).elim
    · exact hCoefficient
  · exact (data.amplitudeProduct_ne_zero hAmplitude).elim

/-- Product-facing certificate for the repaired logical dependency. -/
structure Certificate
    (data : RateRobustEquation44Data (V := V) mu) : Prop where
  beamRemainderVanishes : Tendsto data.beamRemainder atTop (nhds 0)
  measuredInteractionVanishes : Tendsto data.measured atTop (nhds 0)
  stationaryPhaseLimit : Tendsto data.measured atTop
    (nhds
      (((data.chartDensity.J data.phase.p : Complex) * data.amplitude.lead) *
        gaussConst mu data.phase.H))
  leadingAmplitudeZero : data.amplitude.lead = 0
  recoveredCoefficientZero : data.coefficient = 0

def certificate (data : RateRobustEquation44Data (V := V) mu) :
    Certificate mu data where
  beamRemainderVanishes := data.beamRemainder_tendsto_zero
  measuredInteractionVanishes := data.measured_tendsto_zero
  stationaryPhaseLimit := data.measured_tendsto_leading
  leadingAmplitudeZero := data.lead_eq_zero
  recoveredCoefficientZero := data.coefficient_eq_zero

end RateRobustEquation44Data

end ChartComposition

end LiuWang2025SemilinearWaveEquation44RateRobustRecovery
