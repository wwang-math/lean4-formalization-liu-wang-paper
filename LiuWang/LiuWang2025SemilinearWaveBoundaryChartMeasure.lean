import LiuWang.LiuWang2025SemilinearWaveGaussianBoundaryScaling
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Topology.Order.Compact

/-!
# Liu--Wang 2025: boundary-chart surface-measure control

The reflected Gaussian beam in Section 3.2 of arXiv:2511.08794v1 is
integrated in local boundary coordinates.  Passing from Euclidean coordinate
measure to the Lorentzian surface measure introduces a smooth nonnegative
Jacobian.  This module makes that change of measure explicit.

On a compact chart support, continuity supplies a finite Jacobian bound.
Lean then proves domination of the Jacobian-weighted surface measure by a
constant multiple of the restricted reference measure and transfers every
nonnegative integrable estimate, in particular squared `L^2` estimates, to
the physical chart measure.

The result isolates the genuinely geometric input: an application must
provide the chart support and its continuous nonnegative surface Jacobian.
No boundary-measure comparison is subsequently left implicit.
-/

noncomputable section

open Filter MeasureTheory Set Topology

namespace LiuWang2025SemilinearWaveBoundaryChartMeasure

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]

/-- Source-facing data for one compactly supported boundary chart.  In the
paper, `jacobian` is the local density of `dS_g dt` relative to Euclidean
coordinate measure. -/
structure CompactBoundaryChartDensity where
  support : Set X
  supportCompact : IsCompact support
  supportMeasurable : MeasurableSet support
  jacobian : X -> Real
  jacobianContinuousOn : ContinuousOn jacobian support
  jacobianNonnegative : forall x, x ∈ support -> 0 <= jacobian x

namespace CompactBoundaryChartDensity

/-- A continuous surface Jacobian is bounded above on the compact chart
support.  The bound is chosen nonnegative so it can be used as a measure
scaling constant. -/
theorem exists_nonnegative_upper_bound
    (chart : CompactBoundaryChartDensity (X := X)) :
    exists bound : Real,
      0 <= bound ∧ forall x, x ∈ chart.support -> chart.jacobian x <= bound := by
  obtain ⟨upper, hupper⟩ :=
    bddAbove_def.mp
      (chart.supportCompact.bddAbove_image chart.jacobianContinuousOn)
  refine ⟨max upper 0, le_max_right _ _, ?_⟩
  intro x hx
  have hximage : chart.jacobian x ∈ chart.jacobian '' chart.support :=
    mem_image_of_mem chart.jacobian hx
  exact (hupper (chart.jacobian x) hximage).trans (le_max_left _ _)

/-- The surface measure represented by the chart Jacobian. -/
def surfaceMeasure
    (chart : CompactBoundaryChartDensity (X := X))
    (referenceMeasure : Measure X) : Measure X :=
  (referenceMeasure.restrict chart.support).withDensity
    (fun x => ENNReal.ofReal (chart.jacobian x))

/-- A pointwise Jacobian bound gives measure domination on the chart. -/
theorem surfaceMeasure_le_smul_restrict
    (chart : CompactBoundaryChartDensity (X := X))
    (referenceMeasure : Measure X) {bound : Real}
    (hbound : forall x, x ∈ chart.support -> chart.jacobian x <= bound) :
    chart.surfaceMeasure referenceMeasure <=
      ENNReal.ofReal bound • referenceMeasure.restrict chart.support := by
  unfold surfaceMeasure
  calc
    (referenceMeasure.restrict chart.support).withDensity
        (fun x => ENNReal.ofReal (chart.jacobian x)) <=
      (referenceMeasure.restrict chart.support).withDensity
        (fun _ => ENNReal.ofReal bound) := by
      apply withDensity_mono
      refine (ae_restrict_iff' chart.supportMeasurable).2 ?_
      filter_upwards [] with x hx
      exact ENNReal.ofReal_le_ofReal (hbound x hx)
    _ = ENNReal.ofReal bound • referenceMeasure.restrict chart.support :=
      withDensity_const _

/-- The compactness-generated bound controls the whole physical chart
measure. -/
theorem exists_surfaceMeasure_domination
    (chart : CompactBoundaryChartDensity (X := X))
    (referenceMeasure : Measure X) :
    exists bound : Real,
      0 <= bound ∧
        chart.surfaceMeasure referenceMeasure <=
          ENNReal.ofReal bound • referenceMeasure.restrict chart.support := by
  obtain ⟨bound, hboundNonnegative, hbound⟩ :=
    chart.exists_nonnegative_upper_bound
  exact ⟨bound, hboundNonnegative,
    chart.surfaceMeasure_le_smul_restrict referenceMeasure
      hbound⟩

/-- Transfer a nonnegative integral from coordinate measure to the physical
surface measure.  This is the precise measure-theoretic step used after the
Gaussian change of variables. -/
theorem integral_surfaceMeasure_le
    (chart : CompactBoundaryChartDensity (X := X))
    (referenceMeasure : Measure X) {bound : Real} {f : X -> Real}
    (hboundNonnegative : 0 <= bound)
    (hbound : forall x, x ∈ chart.support -> chart.jacobian x <= bound)
    (hfNonnegative : forall x, 0 <= f x)
    (hfIntegrable : Integrable f (referenceMeasure.restrict chart.support)) :
    (∫ x, f x ∂chart.surfaceMeasure referenceMeasure) <=
      bound * ∫ x, f x ∂(referenceMeasure.restrict chart.support) := by
  have hmeasure := chart.surfaceMeasure_le_smul_restrict referenceMeasure
    hbound
  have hscaledIntegrable :
      Integrable f
        (ENNReal.ofReal bound • referenceMeasure.restrict chart.support) :=
    hfIntegrable.smul_measure ENNReal.ofReal_ne_top
  have hnonnegative :
      ∀ᵐ x ∂(ENNReal.ofReal bound • referenceMeasure.restrict chart.support),
        0 <= f x :=
    Filter.Eventually.of_forall hfNonnegative
  have hcomparison :=
    integral_mono_measure hmeasure hnonnegative hscaledIntegrable
  simpa [ENNReal.toReal_ofReal hboundNonnegative, smul_eq_mul] using hcomparison

/-- Squared `L^2` transfer for a chart-local function. -/
theorem integral_sqNorm_surfaceMeasure_le
    {E : Type*} [SeminormedAddCommGroup E]
    (chart : CompactBoundaryChartDensity (X := X))
    (referenceMeasure : Measure X) {bound : Real} {f : X -> E}
    (hboundNonnegative : 0 <= bound)
    (hbound : forall x, x ∈ chart.support -> chart.jacobian x <= bound)
    (hfIntegrable :
      Integrable (fun x => ‖f x‖ ^ 2)
        (referenceMeasure.restrict chart.support)) :
    (∫ x, ‖f x‖ ^ 2 ∂chart.surfaceMeasure referenceMeasure) <=
      bound * ∫ x, ‖f x‖ ^ 2 ∂(referenceMeasure.restrict chart.support) := by
  exact chart.integral_surfaceMeasure_le referenceMeasure
    hboundNonnegative hbound (fun x => sq_nonneg ‖f x‖) hfIntegrable

/-- A coordinate squared-mass estimate and the chart Jacobian bound combine
without changing the frequency exponent. -/
theorem integral_sqNorm_surfaceMeasure_le_of_coordinate_bound
    {E : Type*} [SeminormedAddCommGroup E]
    (chart : CompactBoundaryChartDensity (X := X))
    (referenceMeasure : Measure X) {bound coordinateBound : Real} {f : X -> E}
    (hboundNonnegative : 0 <= bound)
    (hbound : forall x, x ∈ chart.support -> chart.jacobian x <= bound)
    (hfIntegrable :
      Integrable (fun x => ‖f x‖ ^ 2)
        (referenceMeasure.restrict chart.support))
    (hcoordinate :
      (∫ x, ‖f x‖ ^ 2 ∂(referenceMeasure.restrict chart.support)) <=
        coordinateBound) :
    (∫ x, ‖f x‖ ^ 2 ∂chart.surfaceMeasure referenceMeasure) <=
      bound * coordinateBound := by
  exact (chart.integral_sqNorm_surfaceMeasure_le referenceMeasure
    hboundNonnegative hbound hfIntegrable).trans
      (mul_le_mul_of_nonneg_left hcoordinate hboundNonnegative)

/-- Product-facing certificate: compact chart density, measure domination,
and squared `L^2` transfer are all available from one object. -/
structure Certificate
    (chart : CompactBoundaryChartDensity (X := X))
    (referenceMeasure : Measure X) : Prop where
  finiteJacobianBound : exists bound : Real,
    0 <= bound ∧ forall x, x ∈ chart.support -> chart.jacobian x <= bound
  measureDomination : exists bound : Real,
    0 <= bound ∧ chart.surfaceMeasure referenceMeasure <=
      ENNReal.ofReal bound • referenceMeasure.restrict chart.support
  squaredL2Transfer : forall
    {bound coordinateBound : Real} {f : X -> Complex},
    0 <= bound ->
    (forall x, x ∈ chart.support -> chart.jacobian x <= bound) ->
    Integrable (fun x => ‖f x‖ ^ 2)
      (referenceMeasure.restrict chart.support) ->
    (∫ x, ‖f x‖ ^ 2 ∂(referenceMeasure.restrict chart.support)) <=
      coordinateBound ->
    (∫ x, ‖f x‖ ^ 2 ∂chart.surfaceMeasure referenceMeasure) <=
      bound * coordinateBound

def certificate
    (chart : CompactBoundaryChartDensity (X := X))
    (referenceMeasure : Measure X) : Certificate chart referenceMeasure where
  finiteJacobianBound := chart.exists_nonnegative_upper_bound
  measureDomination := chart.exists_surfaceMeasure_domination referenceMeasure
  squaredL2Transfer := fun hboundNonnegative hbound hfIntegrable hcoordinate =>
    chart.integral_sqNorm_surfaceMeasure_le_of_coordinate_bound referenceMeasure
      hboundNonnegative hbound hfIntegrable hcoordinate

end CompactBoundaryChartDensity

end LiuWang2025SemilinearWaveBoundaryChartMeasure
