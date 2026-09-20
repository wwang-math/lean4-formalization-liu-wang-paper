import LiuWang.LiuWang2025SemilinearWaveGaussianLocalization
import LiuWang.LiuWang2025SemilinearWaveDeterminantJacobi
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Liu--Wang 2025: leading Gaussian-beam amplitude transport

The cubic point-recovery argument requires the product of four leading beam
amplitudes at the interaction point to be nonzero.  This module derives that
fact from the scalar transport ODE instead of accepting the product
nonvanishing as an isolated hypothesis.

For a continuous complex transport coefficient `q`, the formula

`b(s) = b(s0) exp(-1/2 integral_{s0}^s q(t) dt)`

solves `2 b' + q b = 0` and is nonzero at every time whenever `b(s0)` is
nonzero.  A four-beam registration packet identifies the source amplitudes at
the interaction point with four such transported values.  It then generates
the exact nonzero amplitude product consumed by the normalized-Gaussian
recovery theorem.

This argument deliberately avoids a determinant or logarithm branch formula.
The geometric construction identifying `q` with the Fermi-coordinate
transport coefficient and registering the actual four beam amplitudes remains
source-specific.
-/

noncomputable section

open scoped BigOperators Matrix.Norms.L2Operator
open Matrix MeasureTheory Set

namespace LiuWang2025SemilinearWaveLeadingAmplitudeTransport

open LiuWang2025SemilinearWaveGaussianLocalization
open LiuWang2025SemilinearWaveDeterminantJacobi
open LiuWang2025SemilinearWaveRiccatiExistence

/-- Explicit integrating-factor solution of the leading scalar transport ODE. -/
def leadingAmplitude
    (q : Real -> Complex) (s0 : Real) (initial : Complex) (s : Real) : Complex :=
  initial * Complex.exp
    (-((2 : Complex)⁻¹) * ∫ t in s0..s, q t)

@[simp] theorem leadingAmplitude_at_initial
    (q : Real -> Complex) (s0 : Real) (initial : Complex) :
    leadingAmplitude q s0 initial s0 = initial := by
  simp [leadingAmplitude]

/-- The integrating-factor amplitude is never zero if its initial value is
nonzero.  No determinant square root or logarithm branch is needed. -/
theorem leadingAmplitude_ne_zero
    (q : Real -> Complex) (s0 : Real) {initial : Complex}
    (hinitial : initial ≠ 0) (s : Real) :
    leadingAmplitude q s0 initial s ≠ 0 := by
  exact mul_ne_zero hinitial (Complex.exp_ne_zero _)

/-- The explicit amplitude has derivative `-(q/2)b`. -/
theorem leadingAmplitude_hasDerivAt
    (q : Real -> Complex) (hq : Continuous q)
    (s0 : Real) (initial : Complex) (s : Real) :
    HasDerivAt (leadingAmplitude q s0 initial)
      (-((2 : Complex)⁻¹) * q s * leadingAmplitude q s0 initial s) s := by
  have hIntegral : HasDerivAt (fun u => ∫ t in s0..u, q t) (q s) s :=
    intervalIntegral.integral_hasDerivAt_right
      (hq.intervalIntegrable _ _)
      hq.aestronglyMeasurable.stronglyMeasurableAtFilter
      hq.continuousAt
  have hExponent :
      HasDerivAt
        (fun u => -((2 : Complex)⁻¹) * ∫ t in s0..u, q t)
        (-((2 : Complex)⁻¹) * q s) s :=
    hIntegral.const_mul (-((2 : Complex)⁻¹))
  have hExp := hExponent.cexp.const_mul initial
  convert hExp using 1 <;> simp only [leadingAmplitude]
  ring

/-- Differential form of the source's leading transport equation. -/
theorem leadingAmplitude_solves_transport
    (q : Real -> Complex) (hq : Continuous q)
    (s0 : Real) (initial : Complex) (s : Real) :
    HasDerivAt (leadingAmplitude q s0 initial)
      (-((2 : Complex)⁻¹) * q s * leadingAmplitude q s0 initial s) s ∧
    2 * (-((2 : Complex)⁻¹) * q s * leadingAmplitude q s0 initial s) +
        q s * leadingAmplitude q s0 initial s = 0 := by
  refine ⟨leadingAmplitude_hasDerivAt q hq s0 initial s, ?_⟩
  ring

/-- Branch-free determinant/amplitude conservation at the differential
level.  If a nonvanishing determinant path satisfies the Jacobi equation
`J' = q J`, then the source-sign transport equation implies
`(b^2 J)' = 0`.  This is the invariant behind the usual square-root formula,
but it neither chooses a square root nor introduces a complex logarithm. -/
theorem leadingAmplitude_sq_mul_jacobiPath_hasDerivAt_zero
    (q : Real -> Complex) (hq : Continuous q)
    (s0 : Real) (initial : Complex)
    (jacobian : Real -> Complex) (s : Real)
    (hjacobian : HasDerivAt jacobian (q s * jacobian s) s) :
    HasDerivAt
      (fun t => leadingAmplitude q s0 initial t ^ 2 * jacobian t) 0 s := by
  have hb := leadingAmplitude_hasDerivAt q hq s0 initial s
  have hproduct := (hb.mul hb).mul hjacobian
  convert hproduct using 1
  · funext t
    simp only [Pi.mul_apply, pow_two]
  · simp only [Pi.mul_apply]
    ring

/-- Interval form of the branch-free determinant/amplitude invariant.  A
Jacobi path satisfying `J' = q J` on the whole segment obeys
`b(s)^2 J(s) = b(s0)^2 J(s0)`.  The proof uses the mean-value theorem on the
unordered interval, so it works in either time direction and when the two
endpoints coincide. -/
theorem leadingAmplitude_sq_mul_jacobiPath_eq_initial
    (q : Real -> Complex) (hq : Continuous q)
    (s0 : Real) (initial : Complex)
    (jacobian : Real -> Complex) (s : Real)
    (hjacobian : forall t, t ∈ uIcc s0 s ->
      HasDerivAt jacobian (q t * jacobian t) t) :
    leadingAmplitude q s0 initial s ^ 2 * jacobian s =
      initial ^ 2 * jacobian s0 := by
  let invariant : Real -> Complex := fun t =>
    leadingAmplitude q s0 initial t ^ 2 * jacobian t
  have hzero : forall t, t ∈ uIcc s0 s ->
      HasFDerivWithinAt invariant (0 : Real →L[Real] Complex) (uIcc s0 s) t := by
    intro t ht
    simpa [invariant] using
      (leadingAmplitude_sq_mul_jacobiPath_hasDerivAt_zero
        q hq s0 initial jacobian t (hjacobian t ht)).hasFDerivAt.hasFDerivWithinAt
          (s := uIcc s0 s)
  have hbound : ‖invariant s - invariant s0‖ ≤ 0 := by
    simpa using
      (convex_uIcc s0 s).norm_image_sub_le_of_norm_hasFDerivWithin_le
        (C := 0) hzero (fun _ _ => by simp) left_mem_uIcc right_mem_uIcc
  have hinvariant : invariant s = invariant s0 := by
    exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hbound (norm_nonneg _)))
  simpa only [invariant, leadingAmplitude_at_initial] using hinvariant

/-! ## Transport coefficient generated by the verified Riccati flow -/

namespace RiccatiGeneratedTransport

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The requested geodesic interval written with ordered endpoints. -/
abbrev TimeInterval (d : Coefficients n) : Set Real :=
  Icc (min d.startTime d.endTime) (max d.startTime d.endTime)

/-- The source initial time as a point of the ordered geodesic interval. -/
def startPoint (d : Coefficients n) : TimeInterval d :=
  ⟨d.startTime, min_le_left _ _, le_max_left _ _⟩

/-- The Riccati-generated scalar coefficient `Tr(C H)` on the requested
geodesic interval. -/
def traceCoefficientOnInterval (d : Coefficients n) (t : TimeInterval d) : Complex :=
  Matrix.trace (d.C t * d.toRiccatiFlow.H t)

theorem traceCoefficient_continuousOn (d : Coefficients n) :
    ContinuousOn
      (fun t : Real => Matrix.trace (d.C t * d.toRiccatiFlow.H t))
      (TimeInterval d) := by
  have hsubset : TimeInterval d ⊆ Icc d.lower d.upper := by
    intro t ht
    exact ⟨(d.interval_subset ht).1.le, (d.interval_subset ht).2.le⟩
  have hC : ContinuousOn d.C (TimeInterval d) :=
    d.C_continuous.mono hsubset
  have hH : ContinuousOn d.toRiccatiFlow.H (TimeInterval d) := by
    intro t ht
    exact (d.generated_H_hasDerivAt ht).continuousAt.continuousWithinAt
  have hprod : ContinuousOn
      (fun t : Real => d.C t * d.toRiccatiFlow.H t) (TimeInterval d) :=
    hC.mul hH
  exact (Matrix.traceLinearMap n Complex Complex).continuous_of_finiteDimensional.comp_continuousOn
    hprod

/-- Continuous path version of `Tr(C H)` on the geodesic interval. -/
def traceCoefficientPath (d : Coefficients n) : C(TimeInterval d, Complex) where
  toFun := traceCoefficientOnInterval d
  continuous_toFun := continuousOn_iff_continuous_restrict.mp
    (traceCoefficient_continuousOn d)

/-- Canonical globally continuous extension of `Tr(C H)`, obtained by
projecting time to the requested compact geodesic interval. -/
def traceTransportCoefficient (d : Coefficients n) : Real -> Complex :=
  CompactIntervalLipschitzODE.extend (startPoint d) (traceCoefficientPath d)

theorem continuous_traceTransportCoefficient (d : Coefficients n) :
    Continuous (traceTransportCoefficient d) :=
  CompactIntervalLipschitzODE.continuous_extend (startPoint d) (traceCoefficientPath d)

theorem traceTransportCoefficient_eq_trace_CH
    (d : Coefficients n) {t : Real}
    (ht : t ∈ uIcc d.startTime d.endTime) :
    traceTransportCoefficient d t =
      Matrix.trace (d.C t * d.toRiccatiFlow.H t) := by
  exact CompactIntervalLipschitzODE.extend_of_mem (startPoint d)
    (traceCoefficientPath d) ht

/-- The leading amplitude driven by the generated Riccati coefficient solves
the source transport equation with the literal coefficient `Tr(C H)` at every
point of the requested interval. -/
theorem leadingAmplitude_solves_trace_CH_transport
    (d : Coefficients n) (initial : Complex)
    {t : Real} (ht : t ∈ uIcc d.startTime d.endTime) :
    HasDerivAt
        (leadingAmplitude (traceTransportCoefficient d) d.startTime initial)
        (-((2 : Complex)⁻¹) *
          Matrix.trace (d.C t * d.toRiccatiFlow.H t) *
          leadingAmplitude (traceTransportCoefficient d) d.startTime initial t) t ∧
      2 * (-((2 : Complex)⁻¹) *
          Matrix.trace (d.C t * d.toRiccatiFlow.H t) *
          leadingAmplitude (traceTransportCoefficient d) d.startTime initial t) +
        Matrix.trace (d.C t * d.toRiccatiFlow.H t) *
          leadingAmplitude (traceTransportCoefficient d) d.startTime initial t = 0 := by
  simpa only [traceTransportCoefficient_eq_trace_CH d ht] using
    leadingAmplitude_solves_transport (traceTransportCoefficient d)
      (continuous_traceTransportCoefficient d) d.startTime initial t

theorem leadingAmplitude_trace_CH_ne_zero
    (d : Coefficients n) {initial : Complex} (hinitial : initial ≠ 0)
    (t : Real) :
    leadingAmplitude (traceTransportCoefficient d) d.startTime initial t ≠ 0 :=
  leadingAmplitude_ne_zero (traceTransportCoefficient d) d.startTime hinitial t

/-- Correct determinant handoff for the generated Riccati coefficient.  Once
the source-specific Jacobi identity for `det Y` is supplied, Lean proves that
`b^2 det Y` has zero derivative.  The premise deliberately names `det Y`, not
`det H`, matching the displayed Hamiltonian equation `Y' = C Z` and
`H = Z Y^-1`. -/
theorem leadingAmplitude_sq_mul_detY_hasDerivAt_zero
    (d : Coefficients n) (initial : Complex)
    (detY : Real -> Complex) {t : Real}
    (ht : t ∈ uIcc d.startTime d.endTime)
    (hdetY : HasDerivAt detY
      (Matrix.trace (d.C t * d.toRiccatiFlow.H t) * detY t) t) :
    HasDerivAt
      (fun s =>
        leadingAmplitude (traceTransportCoefficient d) d.startTime initial s ^ 2 *
          detY s) 0 t := by
  apply leadingAmplitude_sq_mul_jacobiPath_hasDerivAt_zero
    (traceTransportCoefficient d)
    (continuous_traceTransportCoefficient d)
    d.startTime initial detY t
  simpa only [traceTransportCoefficient_eq_trace_CH d ht] using hdetY

/-- Source-interval conservation law generated from the Riccati coefficient.
The only paper-specific premise is the literal Jacobi equation for `det Y` on
the geodesic interval. -/
theorem leadingAmplitude_sq_mul_detY_eq_initial
    (d : Coefficients n) (initial : Complex)
    (detY : Real -> Complex)
    (hdetY : forall t, t ∈ uIcc d.startTime d.endTime ->
      HasDerivAt detY
        (Matrix.trace (d.C t * d.toRiccatiFlow.H t) * detY t) t)
    {t : Real} (ht : t ∈ uIcc d.startTime d.endTime) :
    leadingAmplitude (traceTransportCoefficient d) d.startTime initial t ^ 2 * detY t =
      initial ^ 2 * detY d.startTime := by
  apply leadingAmplitude_sq_mul_jacobiPath_eq_initial
    (traceTransportCoefficient d)
    (continuous_traceTransportCoefficient d)
    d.startTime initial detY t
  intro s hs
  have hsSource : s ∈ uIcc d.startTime d.endTime :=
    Set.uIcc_subset_uIcc_left ht hs
  simpa only [traceTransportCoefficient_eq_trace_CH d hsSource] using
    hdetY s hsSource

/-- One proof object joining the Riccati flow, its generated trace
coefficient, the leading transport equation, and nonvanishing. -/
structure Certificate (d : Coefficients n) (initial : Complex)
    (t : Real) (ht : t ∈ uIcc d.startTime d.endTime) : Prop where
  coefficientContinuous : Continuous (traceTransportCoefficient d)
  coefficientAt :
    traceTransportCoefficient d t =
      Matrix.trace (d.C t * d.toRiccatiFlow.H t)
  transportEquation :
    HasDerivAt
        (leadingAmplitude (traceTransportCoefficient d) d.startTime initial)
        (-((2 : Complex)⁻¹) *
          Matrix.trace (d.C t * d.toRiccatiFlow.H t) *
          leadingAmplitude (traceTransportCoefficient d) d.startTime initial t) t ∧
      2 * (-((2 : Complex)⁻¹) *
          Matrix.trace (d.C t * d.toRiccatiFlow.H t) *
          leadingAmplitude (traceTransportCoefficient d) d.startTime initial t) +
        Matrix.trace (d.C t * d.toRiccatiFlow.H t) *
          leadingAmplitude (traceTransportCoefficient d) d.startTime initial t = 0
  amplitudeNonzero :
    initial ≠ 0 →
      leadingAmplitude (traceTransportCoefficient d) d.startTime initial t ≠ 0

def certificate (d : Coefficients n) (initial : Complex)
    {t : Real} (ht : t ∈ uIcc d.startTime d.endTime) :
    Certificate d initial t ht where
  coefficientContinuous := continuous_traceTransportCoefficient d
  coefficientAt := traceTransportCoefficient_eq_trace_CH d ht
  transportEquation := leadingAmplitude_solves_trace_CH_transport d initial ht
  amplitudeNonzero := fun hinitial =>
    leadingAmplitude_trace_CH_ne_zero d hinitial t

/-- A second certificate records the source-correct determinant bridge.  It
keeps the Jacobi formula as an explicit source-facing premise while checking
its exact composition with the generated Riccati transport coefficient. -/
structure DeterminantCertificate (d : Coefficients n) (initial : Complex)
    (detY : Real -> Complex) (t : Real)
    (ht : t ∈ uIcc d.startTime d.endTime) : Prop where
  jacobiEquation : HasDerivAt detY
    (Matrix.trace (d.C t * d.toRiccatiFlow.H t) * detY t) t
  amplitudeEquation :
    HasDerivAt
      (leadingAmplitude (traceTransportCoefficient d) d.startTime initial)
      (-((2 : Complex)⁻¹) *
        Matrix.trace (d.C t * d.toRiccatiFlow.H t) *
        leadingAmplitude (traceTransportCoefficient d) d.startTime initial t) t
  branchFreeInvariant :
    HasDerivAt
      (fun s =>
        leadingAmplitude (traceTransportCoefficient d) d.startTime initial s ^ 2 *
          detY s) 0 t

def determinantCertificate (d : Coefficients n) (initial : Complex)
    (detY : Real -> Complex) {t : Real}
    (ht : t ∈ uIcc d.startTime d.endTime)
    (hdetY : HasDerivAt detY
      (Matrix.trace (d.C t * d.toRiccatiFlow.H t) * detY t) t) :
    DeterminantCertificate d initial detY t ht where
  jacobiEquation := hdetY
  amplitudeEquation :=
    (leadingAmplitude_solves_trace_CH_transport d initial ht).1
  branchFreeInvariant :=
    leadingAmplitude_sq_mul_detY_hasDerivAt_zero d initial detY ht hdetY

/-- Interval proof object for the source-correct determinant bridge. -/
structure IntervalDeterminantCertificate (d : Coefficients n)
    (initial : Complex) (detY : Real -> Complex) : Prop where
  jacobiEquation : forall t, t ∈ uIcc d.startTime d.endTime ->
    HasDerivAt detY
      (Matrix.trace (d.C t * d.toRiccatiFlow.H t) * detY t) t
  branchFreeConservation : forall t, t ∈ uIcc d.startTime d.endTime ->
    leadingAmplitude (traceTransportCoefficient d) d.startTime initial t ^ 2 * detY t =
      initial ^ 2 * detY d.startTime

def intervalDeterminantCertificate (d : Coefficients n)
    (initial : Complex) (detY : Real -> Complex)
    (hdetY : forall t, t ∈ uIcc d.startTime d.endTime ->
      HasDerivAt detY
        (Matrix.trace (d.C t * d.toRiccatiFlow.H t) * detY t) t) :
    IntervalDeterminantCertificate d initial detY where
  jacobiEquation := hdetY
  branchFreeConservation := fun t ht =>
    leadingAmplitude_sq_mul_detY_eq_initial d initial detY hdetY ht

/-! ### Premise-free determinant/amplitude closure for the generated flow -/

/-- The generated Hamiltonian flow closes the pointwise determinant/amplitude
invariant without a separately supplied Jacobi equation. -/
theorem generated_leadingAmplitude_sq_mul_detY_hasDerivAt_zero
    (d : Coefficients n) (initial : Complex)
    {t : Real} (ht : t ∈ uIcc d.startTime d.endTime) :
    HasDerivAt
      (fun s =>
        leadingAmplitude (traceTransportCoefficient d) d.startTime initial s ^ 2 *
          (d.toRiccatiFlow.Y s).det) 0 t :=
  leadingAmplitude_sq_mul_detY_hasDerivAt_zero d initial
    (fun s => (d.toRiccatiFlow.Y s).det) ht
    (generated_detY_hasDerivAt d ht)

/-- The branch-free determinant/amplitude invariant holds across the whole
source geodesic interval, now derived solely from the generated Hamiltonian
flow and its initial condition `Y(startTime) = I`. -/
theorem generated_leadingAmplitude_sq_mul_detY_eq_initial
    (d : Coefficients n) (initial : Complex)
    {t : Real} (ht : t ∈ uIcc d.startTime d.endTime) :
    leadingAmplitude (traceTransportCoefficient d) d.startTime initial t ^ 2 *
        (d.toRiccatiFlow.Y t).det = initial ^ 2 := by
  have h := leadingAmplitude_sq_mul_detY_eq_initial d initial
    (fun s => (d.toRiccatiFlow.Y s).det)
    (generated_detY_jacobiEquation d) ht
  change
    leadingAmplitude (traceTransportCoefficient d) d.startTime initial t ^ 2 *
        (d.toRiccatiFlow.Y t).det =
      initial ^ 2 * (d.toRiccatiFlow.Y d.startTime).det at h
  have hinitialY : d.toRiccatiFlow.Y d.startTime = 1 :=
    d.toRiccatiFlow.initialY
  rw [hinitialY, Matrix.det_one, mul_one] at h
  exact h

/-- A premise-free certificate joining the matrix ODE, Jacobi determinant
identity, scalar transport equation, amplitude nonvanishing, and interval
conservation law. -/
structure GeneratedDeterminantCertificate (d : Coefficients n)
    (initial : Complex) : Prop where
  jacobiEquation : forall t, t ∈ uIcc d.startTime d.endTime ->
    HasDerivAt (fun s => (d.toRiccatiFlow.Y s).det)
      (Matrix.trace (d.C t * d.toRiccatiFlow.H t) *
        (d.toRiccatiFlow.Y t).det) t
  amplitudeEquation : forall t, t ∈ uIcc d.startTime d.endTime ->
    HasDerivAt
      (leadingAmplitude (traceTransportCoefficient d) d.startTime initial)
      (-((2 : Complex)⁻¹) *
        Matrix.trace (d.C t * d.toRiccatiFlow.H t) *
        leadingAmplitude (traceTransportCoefficient d) d.startTime initial t) t
  amplitudeNonzero : initial ≠ 0 -> forall t,
    leadingAmplitude (traceTransportCoefficient d) d.startTime initial t ≠ 0
  branchFreeDerivative : forall t, t ∈ uIcc d.startTime d.endTime ->
    HasDerivAt
      (fun s =>
        leadingAmplitude (traceTransportCoefficient d) d.startTime initial s ^ 2 *
          (d.toRiccatiFlow.Y s).det) 0 t
  branchFreeConservation : forall t, t ∈ uIcc d.startTime d.endTime ->
    leadingAmplitude (traceTransportCoefficient d) d.startTime initial t ^ 2 *
        (d.toRiccatiFlow.Y t).det = initial ^ 2

def generatedDeterminantCertificate (d : Coefficients n)
    (initial : Complex) : GeneratedDeterminantCertificate d initial where
  jacobiEquation := generated_detY_jacobiEquation d
  amplitudeEquation := fun _ ht =>
    (leadingAmplitude_solves_trace_CH_transport d initial ht).1
  amplitudeNonzero := fun hinitial t =>
    leadingAmplitude_trace_CH_ne_zero d hinitial t
  branchFreeDerivative := fun _ ht =>
    generated_leadingAmplitude_sq_mul_detY_hasDerivAt_zero d initial ht
  branchFreeConservation := fun _ ht =>
    generated_leadingAmplitude_sq_mul_detY_eq_initial d initial ht

end RiccatiGeneratedTransport

/-- Four leading amplitudes transported from nonzero initial values to their
respective arrival parameters at one interaction point. -/
structure FourBeamTransportData where
  q : Fin 4 -> Real -> Complex
  q_continuous : forall j, Continuous (q j)
  initialTime : Fin 4 -> Real
  arrivalTime : Fin 4 -> Real
  initialAmplitude : Fin 4 -> Complex
  initialAmplitude_ne_zero : forall j, initialAmplitude j ≠ 0

namespace FourBeamTransportData

def transportedAmplitude
    (data : FourBeamTransportData) (j : Fin 4) : Complex :=
  leadingAmplitude (data.q j) (data.initialTime j)
    (data.initialAmplitude j) (data.arrivalTime j)

theorem transportedAmplitude_ne_zero
    (data : FourBeamTransportData) (j : Fin 4) :
    data.transportedAmplitude j ≠ 0 :=
  leadingAmplitude_ne_zero (data.q j) (data.initialTime j)
    (data.initialAmplitude_ne_zero j) (data.arrivalTime j)

theorem transportedProduct_ne_zero (data : FourBeamTransportData) :
    (∏ j, data.transportedAmplitude j) ≠ 0 := by
  exact Finset.prod_ne_zero_iff.mpr fun j _ =>
    data.transportedAmplitude_ne_zero j

end FourBeamTransportData

/-! ## Four amplitudes generated by Riccati coefficient packets -/

/-- Four leading-amplitude transport problems whose scalar coefficients are
generated as `Tr(C H)` from four verified Riccati flows. -/
structure RiccatiFourBeamTransportData (n : Type*)
    [Fintype n] [DecidableEq n] where
  coefficients : Fin 4 -> LiuWang2025SemilinearWaveRiccatiExistence.Coefficients n
  arrivalTime : Fin 4 -> Real
  arrival_mem : forall j,
    arrivalTime j ∈ uIcc (coefficients j).startTime (coefficients j).endTime
  initialAmplitude : Fin 4 -> Complex
  initialAmplitude_ne_zero : forall j, initialAmplitude j ≠ 0

namespace RiccatiFourBeamTransportData

open RiccatiGeneratedTransport

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Forgetful map to the generic four-amplitude transport packet. Its four
continuous scalar coefficients are generated by the Riccati construction. -/
def toFourBeamTransportData (data : RiccatiFourBeamTransportData n) :
    FourBeamTransportData where
  q := fun j => traceTransportCoefficient (data.coefficients j)
  q_continuous := fun j =>
    continuous_traceTransportCoefficient (data.coefficients j)
  initialTime := fun j => (data.coefficients j).startTime
  arrivalTime := data.arrivalTime
  initialAmplitude := data.initialAmplitude
  initialAmplitude_ne_zero := data.initialAmplitude_ne_zero

@[simp] theorem transportedAmplitude_eq
    (data : RiccatiFourBeamTransportData n) (j : Fin 4) :
    data.toFourBeamTransportData.transportedAmplitude j =
      leadingAmplitude
        (traceTransportCoefficient (data.coefficients j))
        (data.coefficients j).startTime
        (data.initialAmplitude j) (data.arrivalTime j) := rfl

/-- Each generated amplitude satisfies the paper's literal
`2 b' + Tr(C H)b = 0` transport equation at its arrival parameter. -/
theorem each_solves_trace_CH_transport
    (data : RiccatiFourBeamTransportData n) (j : Fin 4) :
    HasDerivAt
        (leadingAmplitude
          (traceTransportCoefficient (data.coefficients j))
          (data.coefficients j).startTime (data.initialAmplitude j))
        (-((2 : Complex)⁻¹) *
          Matrix.trace
            ((data.coefficients j).C (data.arrivalTime j) *
              (data.coefficients j).toRiccatiFlow.H (data.arrivalTime j)) *
          data.toFourBeamTransportData.transportedAmplitude j)
        (data.arrivalTime j) ∧
      2 * (-((2 : Complex)⁻¹) *
          Matrix.trace
            ((data.coefficients j).C (data.arrivalTime j) *
              (data.coefficients j).toRiccatiFlow.H (data.arrivalTime j)) *
          data.toFourBeamTransportData.transportedAmplitude j) +
        Matrix.trace
            ((data.coefficients j).C (data.arrivalTime j) *
              (data.coefficients j).toRiccatiFlow.H (data.arrivalTime j)) *
          data.toFourBeamTransportData.transportedAmplitude j = 0 := by
  simpa only [transportedAmplitude_eq] using
    leadingAmplitude_solves_trace_CH_transport
      (data.coefficients j) (data.initialAmplitude j) (data.arrival_mem j)

theorem transportedAmplitude_ne_zero
    (data : RiccatiFourBeamTransportData n) (j : Fin 4) :
    data.toFourBeamTransportData.transportedAmplitude j ≠ 0 :=
  data.toFourBeamTransportData.transportedAmplitude_ne_zero j

theorem transportedProduct_ne_zero
    (data : RiccatiFourBeamTransportData n) :
    (∏ j, data.toFourBeamTransportData.transportedAmplitude j) ≠ 0 :=
  data.toFourBeamTransportData.transportedProduct_ne_zero

/-- One proof object certifying all four source-sign transport equations and
the resulting nonzero interaction product. -/
structure FourBeamCertificate (data : RiccatiFourBeamTransportData n) : Prop where
  eachTransportEquation : forall j,
    HasDerivAt
        (leadingAmplitude
          (traceTransportCoefficient (data.coefficients j))
          (data.coefficients j).startTime (data.initialAmplitude j))
        (-((2 : Complex)⁻¹) *
          Matrix.trace
            ((data.coefficients j).C (data.arrivalTime j) *
              (data.coefficients j).toRiccatiFlow.H (data.arrivalTime j)) *
          data.toFourBeamTransportData.transportedAmplitude j)
        (data.arrivalTime j) ∧
      2 * (-((2 : Complex)⁻¹) *
          Matrix.trace
            ((data.coefficients j).C (data.arrivalTime j) *
              (data.coefficients j).toRiccatiFlow.H (data.arrivalTime j)) *
          data.toFourBeamTransportData.transportedAmplitude j) +
        Matrix.trace
            ((data.coefficients j).C (data.arrivalTime j) *
              (data.coefficients j).toRiccatiFlow.H (data.arrivalTime j)) *
          data.toFourBeamTransportData.transportedAmplitude j = 0
  eachAmplitudeNonzero : forall j,
    data.toFourBeamTransportData.transportedAmplitude j ≠ 0
  productNonzero :
    (∏ j, data.toFourBeamTransportData.transportedAmplitude j) ≠ 0

def fourBeamCertificate (data : RiccatiFourBeamTransportData n) :
    FourBeamCertificate data where
  eachTransportEquation := data.each_solves_trace_CH_transport
  eachAmplitudeNonzero := data.transportedAmplitude_ne_zero
  productNonzero := data.transportedProduct_ne_zero

end RiccatiFourBeamTransportData

/-- Registration of the four source amplitude functions at the selected
interaction point with the values generated by the transport equations. -/
structure FourBeamPointRegistration (V : Type*) where
  point : V
  amplitude : Fin 4 -> V -> Complex
  transport : FourBeamTransportData
  amplitude_at_point : forall j,
    amplitude j point = transport.transportedAmplitude j

namespace FourBeamPointRegistration

theorem amplitudeProductAt_eq_transportProduct
    {V : Type*} (data : FourBeamPointRegistration V) :
    amplitudeProductAt (data.amplitude 0) (data.amplitude 1)
        (data.amplitude 2) (data.amplitude 3) data.point =
      ∏ j, data.transport.transportedAmplitude j := by
  rw [Fin.prod_univ_four]
  simp only [amplitudeProductAt]
  rw [data.amplitude_at_point 0, data.amplitude_at_point 1,
    data.amplitude_at_point 2, data.amplitude_at_point 3]

/-- The nonzero four-amplitude product required by stationary phase is a
consequence of the four transport ODEs and nonzero initial amplitudes. -/
theorem amplitudeProductAt_ne_zero
    {V : Type*} (data : FourBeamPointRegistration V) :
    amplitudeProductAt (data.amplitude 0) (data.amplitude 1)
        (data.amplitude 2) (data.amplitude 3) data.point ≠ 0 := by
  rw [data.amplitudeProductAt_eq_transportProduct]
  exact data.transport.transportedProduct_ne_zero

end FourBeamPointRegistration

/-! ## Transport-generated Gaussian recovery -/

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace Real V]
  [MeasurableSpace V] [BorelSpace V] [FiniteDimensional Real V]

/-- Source-facing Gaussian recovery data in which amplitude-product
nonvanishing is generated by four leading transport equations. -/
structure TransportGeneratedGaussianPointRecoveryData where
  coefficient : V -> Complex
  amplitudeRegistration : FourBeamPointRegistration V
  stationaryConstant : Complex
  stationaryConstant_ne_zero : stationaryConstant ≠ 0
  interactionProfile_integrable : Integrable
    (cubicInteractionProfile coefficient
      (amplitudeRegistration.amplitude 0)
      (amplitudeRegistration.amplitude 1)
      (amplitudeRegistration.amplitude 2)
      (amplitudeRegistration.amplitude 3))
  interactionProfile_continuousAt : ContinuousAt
    (cubicInteractionProfile coefficient
      (amplitudeRegistration.amplitude 0)
      (amplitudeRegistration.amplitude 1)
      (amplitudeRegistration.amplitude 2)
      (amplitudeRegistration.amplitude 3))
    amplitudeRegistration.point
  error : Nat -> Complex
  boundary : Nat -> Complex
  error_tendsto_zero : Filter.Tendsto error Filter.atTop (nhds 0)
  inaccessibleBoundary_tendsto_zero :
    Filter.Tendsto boundary Filter.atTop (nhds 0)
  integralIdentity : forall rho,
    scaledGaussianPrincipal stationaryConstant coefficient
        (amplitudeRegistration.amplitude 0)
        (amplitudeRegistration.amplitude 1)
        (amplitudeRegistration.amplitude 2)
        (amplitudeRegistration.amplitude 3)
        amplitudeRegistration.point rho +
      error rho = boundary rho

namespace TransportGeneratedGaussianPointRecoveryData

/-- Forgetful map to the Gaussian recovery packet.  Its nonzero-amplitude
field is proved from transport rather than supplied by the caller. -/
def toGaussianPointRecoveryData
    (data : TransportGeneratedGaussianPointRecoveryData (V := V)) :
    GaussianPointRecoveryData (V := V) where
  point := data.amplitudeRegistration.point
  coefficient := data.coefficient
  amplitude0 := data.amplitudeRegistration.amplitude 0
  amplitude1 := data.amplitudeRegistration.amplitude 1
  amplitude2 := data.amplitudeRegistration.amplitude 2
  amplitude3 := data.amplitudeRegistration.amplitude 3
  stationaryConstant := data.stationaryConstant
  stationaryConstant_ne_zero := data.stationaryConstant_ne_zero
  amplitudeProduct_ne_zero :=
    data.amplitudeRegistration.amplitudeProductAt_ne_zero
  interactionProfile_integrable := data.interactionProfile_integrable
  interactionProfile_continuousAt := data.interactionProfile_continuousAt
  error := data.error
  boundary := data.boundary
  error_tendsto_zero := data.error_tendsto_zero
  inaccessibleBoundary_tendsto_zero :=
    data.inaccessibleBoundary_tendsto_zero
  integralIdentity := data.integralIdentity

/-- Equation-(4.4) point recovery with the leading-amplitude nonvanishing
obligation discharged by the transport ODE. -/
theorem coefficient_at_point_eq_zero
    (data : TransportGeneratedGaussianPointRecoveryData (V := V)) :
    data.coefficient data.amplitudeRegistration.point = 0 :=
  data.toGaussianPointRecoveryData.coefficient_at_point_eq_zero

structure Certificate
    (data : TransportGeneratedGaussianPointRecoveryData (V := V)) : Prop where
  eachTransportedAmplitudeNonzero :
    forall j, data.amplitudeRegistration.transport.transportedAmplitude j ≠ 0
  amplitudeProductNonzero :
    amplitudeProductAt
      (data.amplitudeRegistration.amplitude 0)
      (data.amplitudeRegistration.amplitude 1)
      (data.amplitudeRegistration.amplitude 2)
      (data.amplitudeRegistration.amplitude 3)
      data.amplitudeRegistration.point ≠ 0
  coefficientZero :
    data.coefficient data.amplitudeRegistration.point = 0

def certificate
    (data : TransportGeneratedGaussianPointRecoveryData (V := V)) :
    Certificate data where
  eachTransportedAmplitudeNonzero :=
    data.amplitudeRegistration.transport.transportedAmplitude_ne_zero
  amplitudeProductNonzero :=
    data.amplitudeRegistration.amplitudeProductAt_ne_zero
  coefficientZero := data.coefficient_at_point_eq_zero

end TransportGeneratedGaussianPointRecoveryData

end LiuWang2025SemilinearWaveLeadingAmplitudeTransport
