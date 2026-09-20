import LiuWang.LiuWang2025SemilinearWaveBoundaryChartMeasure
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Liu--Wang 2025: reflected-boundary Sobolev closure

Equation (3.16) of arXiv:2511.08794v1 is followed by an induction over
tangential derivatives and then by the phrase "a change of variables".  Two
finite sums are hidden there:

* each multi-index derivative splits between phase hits and amplitude loss;
* the boundary Sobolev norm sums all multi-indices of order at most `k`.

This module closes both finite sums.  A `FiniteTangentialDerivativeExpansion`
carries the actual derivative components in a seminormed `L^2`-type space,
their finite phase/amplitude decomposition, and the termwise Gaussian bounds.
Lean proves that every lower derivative is controlled by the slowest
top-order rate, sums all multi-indices with an explicit constant, and derives
vanishing of the full boundary trace.  The resulting limit is then connected
to the existing point-recovery theorem.

Together with `LiuWang2025SemilinearWaveBoundaryChartMeasure`, this leaves the
source-specific construction of the Lorentzian chart and matched phase and
amplitude jets visible, but no longer leaves the finite derivative/Sobolev
closure or the change of surface measure implicit.
-/

noncomputable section

open Filter Finset Topology
open scoped BigOperators

namespace LiuWang2025SemilinearWaveReflectedBoundarySobolevClosure

open LiuWang2025SemilinearWaveGaussianBoundaryScaling
open LiuWang2025SemilinearWaveGaussianRecovery

/-- Increasing the derivative order decreases the positive boundary-decay
exponent. -/
theorem boundaryDecayExponent_antitone_in_derivativeOrder
    {d N lowerOrder upperOrder : Nat} (horder : lowerOrder <= upperOrder) :
    dimensionCorrectBoundaryDecayExponent d N upperOrder <=
      dimensionCorrectBoundaryDecayExponent d N lowerOrder := by
  have horderReal : (lowerOrder : Real) <= (upperOrder : Real) := by
    exact_mod_cast horder
  unfold dimensionCorrectBoundaryDecayExponent
  linarith

/-- For frequencies at least one, every lower derivative decays at least as
fast as the top Sobolev derivative. -/
theorem boundaryDecayRate_le_topOrder
    {d N lowerOrder upperOrder rho : Nat}
    (horder : lowerOrder <= upperOrder) (hrho : 1 <= rho) :
    dimensionCorrectBoundaryDecayRate d N lowerOrder rho <=
      dimensionCorrectBoundaryDecayRate d N upperOrder rho := by
  unfold dimensionCorrectBoundaryDecayRate
  apply Real.rpow_le_rpow_of_exponent_le
  · exact_mod_cast hrho
  · have hexponent :=
      boundaryDecayExponent_antitone_in_derivativeOrder
        (d := d) (N := N) horder
    linarith

/-- All multi-index derivatives needed for one boundary `H^k` estimate.

For an index `alpha`, `derivativeOrder alpha` is `|alpha|`.  The term indexed
by `phaseHits` represents the summand in which `phaseHits` derivatives strike
the oscillatory phase and the remaining derivatives produce amplitude or jet
loss. -/
structure FiniteTangentialDerivativeExpansion
    (Index E : Type*) [Fintype Index] [DecidableEq Index]
    [SeminormedAddCommGroup E] where
  transverseDimension : Nat
  beamOrder : Nat
  sobolevOrder : Nat
  transverseDimension_pos : 1 <= transverseDimension
  sobolevOrder_le : sobolevOrder <= beamOrder + 1
  derivativeOrder : Index -> Nat
  derivativeOrder_le : forall alpha, derivativeOrder alpha <= sobolevOrder
  boundaryDerivative : Nat -> Index -> E
  splitTerm : Nat -> Index -> Nat -> E
  splitConstant : Index -> Nat -> Real
  splitConstant_nonnegative : forall alpha phaseHits,
    phaseHits < derivativeOrder alpha + 1 ->
      0 <= splitConstant alpha phaseHits
  decomposition : forall rho alpha,
    boundaryDerivative rho alpha =
      ∑ phaseHits ∈ range (derivativeOrder alpha + 1),
        splitTerm rho alpha phaseHits
  termwiseGaussianBound : forall rho alpha phaseHits,
    1 <= rho -> phaseHits < derivativeOrder alpha + 1 ->
      ‖splitTerm rho alpha phaseHits‖ <=
        splitConstant alpha phaseHits *
          dimensionCorrectBoundaryDecayRate transverseDimension beamOrder
            (derivativeOrder alpha) rho

namespace FiniteTangentialDerivativeExpansion

variable {Index E : Type*} [Fintype Index] [DecidableEq Index]
  [SeminormedAddCommGroup E]

/-- Sum of the phase/amplitude split constants for one multi-index. -/
def derivativeConstant
    (data : FiniteTangentialDerivativeExpansion Index E) (alpha : Index) : Real :=
  ∑ phaseHits ∈ range (data.derivativeOrder alpha + 1),
    data.splitConstant alpha phaseHits

theorem derivativeConstant_nonnegative
    (data : FiniteTangentialDerivativeExpansion Index E) (alpha : Index) :
    0 <= data.derivativeConstant alpha := by
  unfold derivativeConstant
  apply sum_nonneg
  intro phaseHits hphaseHits
  exact data.splitConstant_nonnegative alpha phaseHits (mem_range.mp hphaseHits)

/-- Sum of all constants entering the finite `H^k` derivative family. -/
def totalConstant
    (data : FiniteTangentialDerivativeExpansion Index E) : Real :=
  ∑ alpha, data.derivativeConstant alpha

theorem totalConstant_nonnegative
    (data : FiniteTangentialDerivativeExpansion Index E) :
    0 <= data.totalConstant := by
  unfold totalConstant
  exact sum_nonneg (fun alpha _ => data.derivativeConstant_nonnegative alpha)

/-- The finite `l^1(L^2)` envelope of all chart derivatives.  It controls the
usual finite `l^2(L^2)` Sobolev norm and avoids hiding dimension-dependent
cardinality factors. -/
def derivativeL1Envelope
    (data : FiniteTangentialDerivativeExpansion Index E) (rho : Nat) : Real :=
  ∑ alpha, ‖data.boundaryDerivative rho alpha‖

theorem derivativeL1Envelope_nonnegative
    (data : FiniteTangentialDerivativeExpansion Index E) (rho : Nat) :
    0 <= data.derivativeL1Envelope rho := by
  unfold derivativeL1Envelope
  exact sum_nonneg (fun alpha _ => norm_nonneg _)

/-- The actual finite `l^2(L^2)` Sobolev envelope associated with the chart
derivatives. -/
def derivativeL2Envelope
    (data : FiniteTangentialDerivativeExpansion Index E) (rho : Nat) : Real :=
  Real.sqrt (∑ alpha, ‖data.boundaryDerivative rho alpha‖ ^ 2)

theorem derivativeL2Envelope_nonnegative
    (data : FiniteTangentialDerivativeExpansion Index E) (rho : Nat) :
    0 <= data.derivativeL2Envelope rho := by
  exact Real.sqrt_nonneg _

/-- The finite `l^2(L^2)` Sobolev envelope is controlled by the corresponding
`l^1(L^2)` envelope, with no hidden cardinality constant. -/
theorem derivativeL2Envelope_le_derivativeL1Envelope
    (data : FiniteTangentialDerivativeExpansion Index E) (rho : Nat) :
    data.derivativeL2Envelope rho <= data.derivativeL1Envelope rho := by
  unfold derivativeL2Envelope derivativeL1Envelope
  rw [Real.sqrt_le_iff]
  constructor
  · exact sum_nonneg (fun alpha _ => norm_nonneg _)
  · simpa using
      (Finset.sum_sq_le_sq_sum_of_nonneg
        (s := Finset.univ)
        (f := fun alpha : Index => ‖data.boundaryDerivative rho alpha‖)
        (fun alpha _ => norm_nonneg (data.boundaryDerivative rho alpha)))

/-- One multi-index derivative inherits the top-order boundary rate after all
phase/amplitude derivative splits are summed. -/
theorem norm_boundaryDerivative_le_topOrder
    (data : FiniteTangentialDerivativeExpansion Index E)
    {rho : Nat} (hrho : 1 <= rho) (alpha : Index) :
    ‖data.boundaryDerivative rho alpha‖ <=
      data.derivativeConstant alpha *
        dimensionCorrectBoundaryDecayRate data.transverseDimension
          data.beamOrder data.sobolevOrder rho := by
  rw [data.decomposition rho alpha]
  calc
    ‖∑ phaseHits ∈ range (data.derivativeOrder alpha + 1),
        data.splitTerm rho alpha phaseHits‖ <=
      ∑ phaseHits ∈ range (data.derivativeOrder alpha + 1),
        ‖data.splitTerm rho alpha phaseHits‖ := norm_sum_le _ _
    _ <= ∑ phaseHits ∈ range (data.derivativeOrder alpha + 1),
        data.splitConstant alpha phaseHits *
          dimensionCorrectBoundaryDecayRate data.transverseDimension
            data.beamOrder (data.derivativeOrder alpha) rho := by
      apply sum_le_sum
      intro phaseHits hphaseHits
      exact data.termwiseGaussianBound rho alpha phaseHits hrho
        (mem_range.mp hphaseHits)
    _ = data.derivativeConstant alpha *
        dimensionCorrectBoundaryDecayRate data.transverseDimension
          data.beamOrder (data.derivativeOrder alpha) rho := by
      simp [derivativeConstant, sum_mul]
    _ <= data.derivativeConstant alpha *
        dimensionCorrectBoundaryDecayRate data.transverseDimension
          data.beamOrder data.sobolevOrder rho := by
      exact mul_le_mul_of_nonneg_left
        (boundaryDecayRate_le_topOrder
          (data.derivativeOrder_le alpha) hrho)
        (data.derivativeConstant_nonnegative alpha)

/-- Full finite Sobolev envelope with an explicit derivative-count constant. -/
theorem derivativeL1Envelope_le_topOrder
    (data : FiniteTangentialDerivativeExpansion Index E)
    {rho : Nat} (hrho : 1 <= rho) :
    data.derivativeL1Envelope rho <=
      data.totalConstant *
        dimensionCorrectBoundaryDecayRate data.transverseDimension
          data.beamOrder data.sobolevOrder rho := by
  unfold derivativeL1Envelope totalConstant
  calc
    (∑ alpha, ‖data.boundaryDerivative rho alpha‖) <=
      ∑ alpha, data.derivativeConstant alpha *
        dimensionCorrectBoundaryDecayRate data.transverseDimension
          data.beamOrder data.sobolevOrder rho := by
      apply sum_le_sum
      intro alpha _
      exact data.norm_boundaryDerivative_le_topOrder hrho alpha
    _ = (∑ alpha, data.derivativeConstant alpha) *
        dimensionCorrectBoundaryDecayRate data.transverseDimension
          data.beamOrder data.sobolevOrder rho := by
      rw [sum_mul]

/-- The complete finite derivative family tends to zero. -/
theorem derivativeL1Envelope_tendsto_zero
    (data : FiniteTangentialDerivativeExpansion Index E) :
    Tendsto data.derivativeL1Envelope atTop (nhds 0) := by
  apply squeeze_zero'
  · exact Eventually.of_forall data.derivativeL1Envelope_nonnegative
  · filter_upwards [eventually_ge_atTop (1 : Nat)] with rho hrho
    exact data.derivativeL1Envelope_le_topOrder hrho
  · simpa using tendsto_const_nhds.mul
      (dimensionCorrectBoundaryDecayRate_tendsto_zero
        data.transverseDimension_pos data.sobolevOrder_le)

/-- The genuine finite Sobolev norm, rather than only its `l^1` majorant,
vanishes at high frequency. -/
theorem derivativeL2Envelope_tendsto_zero
    (data : FiniteTangentialDerivativeExpansion Index E) :
    Tendsto data.derivativeL2Envelope atTop (nhds 0) := by
  apply squeeze_zero'
  · exact Eventually.of_forall data.derivativeL2Envelope_nonnegative
  · exact Eventually.of_forall data.derivativeL2Envelope_le_derivativeL1Envelope
  · exact data.derivativeL1Envelope_tendsto_zero

end FiniteTangentialDerivativeExpansion

/-- A physical boundary trace controlled by its complete finite derivative
family.  In an application, `E` is the chart `L^2` carrier and `B` is the
boundary Sobolev carrier. -/
structure ReflectedBoundarySobolevClosure
    (Index E B : Type*) [Fintype Index] [DecidableEq Index]
    [SeminormedAddCommGroup E] [SeminormedAddCommGroup B] where
  derivatives : FiniteTangentialDerivativeExpansion Index E
  boundaryTrace : Nat -> B
  norm_boundaryTrace_le : forall rho,
    ‖boundaryTrace rho‖ <= derivatives.derivativeL2Envelope rho

namespace ReflectedBoundarySobolevClosure

variable {Index E B : Type*} [Fintype Index] [DecidableEq Index]
  [SeminormedAddCommGroup E] [SeminormedAddCommGroup B]

/-- The termwise Gaussian estimates, finite multi-index closure, and Sobolev
comparison together force the physical reflected trace to vanish. -/
theorem boundaryTrace_tendsto_zero
    (data : ReflectedBoundarySobolevClosure Index E B) :
    Tendsto data.boundaryTrace atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero
    (fun rho => norm_nonneg (data.boundaryTrace rho))
    data.norm_boundaryTrace_le
  exact data.derivatives.derivativeL2Envelope_tendsto_zero

/-- Product-facing certificate for the full finite Sobolev closure. -/
structure Certificate
    (data : ReflectedBoundarySobolevClosure Index E B) : Prop where
  explicitConstantNonnegative : 0 <= data.derivatives.totalConstant
  derivativeL1MajorantVanishes :
    Tendsto data.derivatives.derivativeL1Envelope atTop (nhds 0)
  finiteSobolevNormVanishes :
    Tendsto data.derivatives.derivativeL2Envelope atTop (nhds 0)
  physicalBoundaryTraceVanishes : Tendsto data.boundaryTrace atTop (nhds 0)

def certificate
    (data : ReflectedBoundarySobolevClosure Index E B) : Certificate data where
  explicitConstantNonnegative := data.derivatives.totalConstant_nonnegative
  derivativeL1MajorantVanishes :=
    data.derivatives.derivativeL1Envelope_tendsto_zero
  finiteSobolevNormVanishes :=
    data.derivatives.derivativeL2Envelope_tendsto_zero
  physicalBoundaryTraceVanishes := data.boundaryTrace_tendsto_zero

end ReflectedBoundarySobolevClosure

/-- Recovery packet whose inaccessible-boundary limit is generated by the
multi-index Sobolev closure rather than supplied as an independent premise. -/
structure SobolevClosedPointRecoveryData
    (Index E : Type*) [Fintype Index] [DecidableEq Index]
    [SeminormedAddCommGroup E] where
  boundaryClosure : ReflectedBoundarySobolevClosure Index E Complex
  coefficient : Complex
  stationaryConstant : Complex
  amplitudeProduct : Complex
  principal : Nat -> Complex
  error : Nat -> Complex
  stationaryConstant_ne_zero : stationaryConstant ≠ 0
  amplitudeProduct_ne_zero : amplitudeProduct ≠ 0
  principal_tendsto : Tendsto principal atTop
    (nhds (stationaryConstant * coefficient * amplitudeProduct))
  error_tendsto_zero : Tendsto error atTop (nhds 0)
  integralIdentity : forall rho,
    principal rho + error rho = boundaryClosure.boundaryTrace rho

namespace SobolevClosedPointRecoveryData

variable {Index E : Type*} [Fintype Index] [DecidableEq Index]
  [SeminormedAddCommGroup E]

/-- Forgetful map to the checked stationary-phase point-recovery theorem. -/
def toPointRecoveryData
    (data : SobolevClosedPointRecoveryData Index E) : PointRecoveryData where
  coefficient := data.coefficient
  stationaryConstant := data.stationaryConstant
  amplitudeProduct := data.amplitudeProduct
  principal := data.principal
  error := data.error
  boundary := data.boundaryClosure.boundaryTrace
  stationaryConstant_ne_zero := data.stationaryConstant_ne_zero
  amplitudeProduct_ne_zero := data.amplitudeProduct_ne_zero
  principal_tendsto := data.principal_tendsto
  error_tendsto_zero := data.error_tendsto_zero
  inaccessibleBoundary_tendsto_zero :=
    data.boundaryClosure.boundaryTrace_tendsto_zero
  integralIdentity := data.integralIdentity

/-- The chart-aware finite Sobolev closure still reaches exact pointwise
coefficient recovery. -/
theorem coefficient_eq_zero
    (data : SobolevClosedPointRecoveryData Index E) :
    data.coefficient = 0 :=
  data.toPointRecoveryData.coefficient_eq_zero

structure Certificate
    (data : SobolevClosedPointRecoveryData Index E) : Prop where
  boundaryClosure : data.boundaryClosure.Certificate
  coefficientZero : data.coefficient = 0

def certificate
    (data : SobolevClosedPointRecoveryData Index E) : Certificate data where
  boundaryClosure := data.boundaryClosure.certificate
  coefficientZero := data.coefficient_eq_zero

end SobolevClosedPointRecoveryData

end LiuWang2025SemilinearWaveReflectedBoundarySobolevClosure
