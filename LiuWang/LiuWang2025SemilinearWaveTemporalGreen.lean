import LiuWang.LiuWang2025SemilinearWaveDirectedGreenRealization
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Liu--Wang weighted temporal Green core

This module verifies the temporal integration-by-parts mechanism used before
equation (4.3) of Liu--Wang, arXiv:2511.08794v1.  It keeps the forward and
backward endpoint conditions directed:

* the forward path has zero state and zero time derivative at `t = 0`;
* the backward path has zero state and zero time derivative at `t = T`.

The weighted theorem is written in divergence form.  If `mu` is the temporal
volume density, the temporal flux is `mu * partial_t u`; Lean proves

`integral partial_t(mu partial_t u) v
    = integral u partial_t(mu partial_t v)`

with all four endpoint terms eliminated by the directed Cauchy data.  A finite
spatial-mode theorem sums this identity over an arbitrary mode set.  Finally,
an adapter constructs `DirectedWaveGreenModel.timeIntegrationByParts` from
literal weighted spacetime pairings.  Thus the temporal Green equality is no
longer an independent field of that realization.

This is a smooth finite-mode core for the source's divergence-form wave
operator.  The concrete Lorentzian Sobolev carriers, spatial Green formula,
normal trace, and passage from the core to the full manifold remain explicit
analytic obligations.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory Set

namespace LiuWang2025SemilinearWaveTemporalGreen

open LiuWang2025SemilinearWaveDirectedGreenRealization

/-- A twice differentiated time path represented in weighted divergence form.
The density is shared by the forward and backward paths. -/
structure WeightedTemporalModePath {Mode : Type*} (modes : Finset Mode)
    (timeHorizon : Real) (density : Real -> Mode -> Complex) where
  state : Real -> Mode -> Complex
  timeDerivative : Real -> Mode -> Complex
  weightedFlux : Real -> Mode -> Complex
  fluxDerivative : Real -> Mode -> Complex
  hasTimeDerivative : forall k, k ∈ modes -> forall t,
    t ∈ uIcc 0 timeHorizon ->
      HasDerivAt (fun s => state s k) (timeDerivative t k) t
  hasFluxDerivative : forall k, k ∈ modes -> forall t,
    t ∈ uIcc 0 timeHorizon ->
      HasDerivAt (fun s => weightedFlux s k) (fluxDerivative t k) t
  timeDerivative_intervalIntegrable : forall k, k ∈ modes ->
    IntervalIntegrable (fun t => timeDerivative t k) volume 0 timeHorizon
  fluxDerivative_intervalIntegrable : forall k, k ∈ modes ->
    IntervalIntegrable (fun t => fluxDerivative t k) volume 0 timeHorizon
  weightedFlux_eq : forall t k,
    weightedFlux t k = density t k * timeDerivative t k

/-- Forward temporal carrier with the source's zero initial Cauchy data. -/
structure ZeroInitialTemporalModePath {Mode : Type*} (modes : Finset Mode)
    (timeHorizon : Real) (density : Real -> Mode -> Complex) extends
    WeightedTemporalModePath modes timeHorizon density where
  state_zero : forall k, k ∈ modes -> state 0 k = 0
  timeDerivative_zero : forall k, k ∈ modes -> timeDerivative 0 k = 0

/-- Backward temporal carrier with the source's zero terminal Cauchy data. -/
structure ZeroTerminalTemporalModePath {Mode : Type*} (modes : Finset Mode)
    (timeHorizon : Real) (density : Real -> Mode -> Complex) extends
    WeightedTemporalModePath modes timeHorizon density where
  state_terminal : forall k, k ∈ modes -> state timeHorizon k = 0
  timeDerivative_terminal : forall k, k ∈ modes ->
    timeDerivative timeHorizon k = 0

/-- Complex-bilinear spacetime pairing on a finite set of spatial modes.  No
conjugation is inserted, matching the Green pairing in equation (4.3). -/
def spacetimePairing {Mode : Type*} (modes : Finset Mode)
    (timeHorizon : Real) (u v : Real -> Mode -> Complex) : Complex :=
  ∑ k ∈ modes, ∫ t in 0..timeHorizon, u t k * v t k

/-- Two source-directed integrations by parts for the unweighted second time
derivative. -/
theorem secondDerivative_timeIntegrationByParts_zeroCauchy
    {u du ddu v dv ddv : Real -> Complex} {timeHorizon : Real}
    (hu : forall t, t ∈ uIcc 0 timeHorizon -> HasDerivAt u (du t) t)
    (hdu : forall t, t ∈ uIcc 0 timeHorizon -> HasDerivAt du (ddu t) t)
    (hv : forall t, t ∈ uIcc 0 timeHorizon -> HasDerivAt v (dv t) t)
    (hdv : forall t, t ∈ uIcc 0 timeHorizon -> HasDerivAt dv (ddv t) t)
    (hduInt : IntervalIntegrable du volume 0 timeHorizon)
    (hdduInt : IntervalIntegrable ddu volume 0 timeHorizon)
    (hdvInt : IntervalIntegrable dv volume 0 timeHorizon)
    (hddvInt : IntervalIntegrable ddv volume 0 timeHorizon)
    (hu0 : u 0 = 0) (hdu0 : du 0 = 0)
    (hvT : v timeHorizon = 0) (hdvT : dv timeHorizon = 0) :
    (∫ t in 0..timeHorizon, ddu t * v t) =
      ∫ t in 0..timeHorizon, u t * ddv t := by
  have hfirst := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    hdu hv hdduInt hdvInt
  have hsecond := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    hu hdv hduInt hddvInt
  have hfirst' :
      (∫ t in 0..timeHorizon, du t * dv t) =
        -(∫ t in 0..timeHorizon, ddu t * v t) := by
    simpa [hdu0, hvT] using hfirst
  have hsecond' :
      (∫ t in 0..timeHorizon, u t * ddv t) =
        -(∫ t in 0..timeHorizon, du t * dv t) := by
    simpa [hu0, hdvT] using hsecond
  calc
    (∫ t in 0..timeHorizon, ddu t * v t) =
        -(∫ t in 0..timeHorizon, du t * dv t) := by
      simpa using (congrArg Neg.neg hfirst').symm
    _ = ∫ t in 0..timeHorizon, u t * ddv t := hsecond'.symm

/-- Weighted temporal Green identity in divergence form.  The weight may vary
in time; the proof does not silently replace it by a constant density. -/
theorem weightedTemporalGreen_zeroCauchy
    {density u du fluxU dfluxU v dv fluxV dfluxV : Real -> Complex}
    {timeHorizon : Real}
    (hu : forall t, t ∈ uIcc 0 timeHorizon -> HasDerivAt u (du t) t)
    (hfluxU : forall t, t ∈ uIcc 0 timeHorizon ->
      HasDerivAt fluxU (dfluxU t) t)
    (hv : forall t, t ∈ uIcc 0 timeHorizon -> HasDerivAt v (dv t) t)
    (hfluxV : forall t, t ∈ uIcc 0 timeHorizon ->
      HasDerivAt fluxV (dfluxV t) t)
    (hduInt : IntervalIntegrable du volume 0 timeHorizon)
    (hdfluxUInt : IntervalIntegrable dfluxU volume 0 timeHorizon)
    (hdvInt : IntervalIntegrable dv volume 0 timeHorizon)
    (hdfluxVInt : IntervalIntegrable dfluxV volume 0 timeHorizon)
    (hfluxUDef : forall t, fluxU t = density t * du t)
    (hfluxVDef : forall t, fluxV t = density t * dv t)
    (hu0 : u 0 = 0) (hdu0 : du 0 = 0)
    (hvT : v timeHorizon = 0) (hdvT : dv timeHorizon = 0) :
    (∫ t in 0..timeHorizon, dfluxU t * v t) =
      ∫ t in 0..timeHorizon, u t * dfluxV t := by
  have hleft := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    hfluxU hv hdfluxUInt hdvInt
  have hright := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    hu hfluxV hduInt hdfluxVInt
  have hfluxU0 : fluxU 0 = 0 := by simp [hfluxUDef, hdu0]
  have hfluxVT : fluxV timeHorizon = 0 := by
    simp [hfluxVDef, hdvT]
  have hleft' :
      (∫ t in 0..timeHorizon, fluxU t * dv t) =
        -(∫ t in 0..timeHorizon, dfluxU t * v t) := by
    simpa [hfluxU0, hvT] using hleft
  have hright' :
      (∫ t in 0..timeHorizon, u t * dfluxV t) =
        -(∫ t in 0..timeHorizon, du t * fluxV t) := by
    simpa [hu0, hfluxVT] using hright
  have hmiddle :
      (∫ t in 0..timeHorizon, fluxU t * dv t) =
        ∫ t in 0..timeHorizon, du t * fluxV t := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [] with t _
    rw [hfluxUDef, hfluxVDef]
    ring
  calc
    (∫ t in 0..timeHorizon, dfluxU t * v t) =
        -(∫ t in 0..timeHorizon, fluxU t * dv t) := by
      simpa using (congrArg Neg.neg hleft').symm
    _ = -(∫ t in 0..timeHorizon, du t * fluxV t) := by rw [hmiddle]
    _ = ∫ t in 0..timeHorizon, u t * dfluxV t := hright'.symm

/-- Finite-mode weighted spacetime Green identity. -/
theorem weightedTemporalGreen_finiteModes {Mode : Type*} [DecidableEq Mode]
    {modes : Finset Mode} {timeHorizon : Real}
    {density : Real -> Mode -> Complex}
    (U : ZeroInitialTemporalModePath modes timeHorizon density)
    (V : ZeroTerminalTemporalModePath modes timeHorizon density) :
    spacetimePairing modes timeHorizon
        U.toWeightedTemporalModePath.fluxDerivative
        V.toWeightedTemporalModePath.state =
      spacetimePairing modes timeHorizon
        U.toWeightedTemporalModePath.state
        V.toWeightedTemporalModePath.fluxDerivative := by
  unfold spacetimePairing
  apply Finset.sum_congr rfl
  intro k hk
  exact weightedTemporalGreen_zeroCauchy
    (U.toWeightedTemporalModePath.hasTimeDerivative k hk)
    (U.toWeightedTemporalModePath.hasFluxDerivative k hk)
    (V.toWeightedTemporalModePath.hasTimeDerivative k hk)
    (V.toWeightedTemporalModePath.hasFluxDerivative k hk)
    (U.toWeightedTemporalModePath.timeDerivative_intervalIntegrable k hk)
    (U.toWeightedTemporalModePath.fluxDerivative_intervalIntegrable k hk)
    (V.toWeightedTemporalModePath.timeDerivative_intervalIntegrable k hk)
    (V.toWeightedTemporalModePath.fluxDerivative_intervalIntegrable k hk)
    (fun t => U.toWeightedTemporalModePath.weightedFlux_eq t k)
    (fun t => V.toWeightedTemporalModePath.weightedFlux_eq t k)
    (U.state_zero k hk) (U.timeDerivative_zero k hk)
    (V.state_terminal k hk) (V.timeDerivative_terminal k hk)

section Adapter

variable {ForwardGraph BackwardGraph ForwardResidual BackwardResidual : Type*}
variable {BoundaryFlux BoundaryValue : Type*}

variable [AddCommGroup ForwardGraph] [Module Complex ForwardGraph]
variable [AddCommGroup BackwardGraph] [Module Complex BackwardGraph]
variable [AddCommGroup ForwardResidual] [Module Complex ForwardResidual]
variable [AddCommGroup BackwardResidual] [Module Complex BackwardResidual]
variable [AddCommGroup BoundaryFlux] [Module Complex BoundaryFlux]
variable [AddCommGroup BoundaryValue] [Module Complex BoundaryValue]

/-- The wave and spatial Green data before temporal integration by parts is
supplied.  The missing temporal field will be generated from a literal
weighted finite-mode realization. -/
structure DirectedWaveGreenSkeleton where
  forwardTimeSecond : ForwardGraph →ₗ[Complex] ForwardResidual
  forwardSpatial : ForwardGraph →ₗ[Complex] ForwardResidual
  forwardWave : ForwardGraph →ₗ[Complex] ForwardResidual
  backwardTimeSecond : BackwardGraph →ₗ[Complex] BackwardResidual
  backwardSpatial : BackwardGraph →ₗ[Complex] BackwardResidual
  backwardWave : BackwardGraph →ₗ[Complex] BackwardResidual
  bulkPairing :
    ForwardResidual →ₗ[Complex] BackwardGraph →ₗ[Complex] Complex
  adjointBulkPairing :
    ForwardGraph →ₗ[Complex] BackwardResidual →ₗ[Complex] Complex
  normalTrace : ForwardGraph →ₗ[Complex] BoundaryFlux
  probeTrace : BackwardGraph →ₗ[Complex] BoundaryValue
  fullBoundaryPairing :
    BoundaryFlux →ₗ[Complex] BoundaryValue →ₗ[Complex] Complex
  forwardWave_decomposition :
    forwardWave = forwardTimeSecond - forwardSpatial
  backwardWave_decomposition :
    backwardWave = backwardTimeSecond - backwardSpatial
  spatialGreenFormula : forall (u : ForwardGraph) (v : BackwardGraph),
    bulkPairing (forwardSpatial u) v -
        adjointBulkPairing u (backwardSpatial v) =
      fullBoundaryPairing (normalTrace u) (probeTrace v)

/-- Identifies the skeleton's two temporal pairings with the same literal
weighted spacetime integral. -/
structure FiniteModeTemporalRealization {Mode : Type*} [DecidableEq Mode]
    (S : DirectedWaveGreenSkeleton
      (ForwardGraph := ForwardGraph) (BackwardGraph := BackwardGraph)
      (ForwardResidual := ForwardResidual) (BackwardResidual := BackwardResidual)
      (BoundaryFlux := BoundaryFlux) (BoundaryValue := BoundaryValue))
    (modes : Finset Mode) (timeHorizon : Real)
    (density : Real -> Mode -> Complex) where
  forwardPath : ForwardGraph ->
    ZeroInitialTemporalModePath modes timeHorizon density
  backwardPath : BackwardGraph ->
    ZeroTerminalTemporalModePath modes timeHorizon density
  forwardTimePairing_eq : forall u v,
    S.bulkPairing (S.forwardTimeSecond u) v =
      spacetimePairing modes timeHorizon
        (forwardPath u).toWeightedTemporalModePath.fluxDerivative
        (backwardPath v).toWeightedTemporalModePath.state
  backwardTimePairing_eq : forall u v,
    S.adjointBulkPairing u (S.backwardTimeSecond v) =
      spacetimePairing modes timeHorizon
        (forwardPath u).toWeightedTemporalModePath.state
        (backwardPath v).toWeightedTemporalModePath.fluxDerivative

namespace FiniteModeTemporalRealization

/-- The source-directed temporal Green equality is generated from two
weighted integrations by parts. -/
theorem timeIntegrationByParts {Mode : Type*} [DecidableEq Mode]
    {S : DirectedWaveGreenSkeleton
      (ForwardGraph := ForwardGraph) (BackwardGraph := BackwardGraph)
      (ForwardResidual := ForwardResidual) (BackwardResidual := BackwardResidual)
      (BoundaryFlux := BoundaryFlux) (BoundaryValue := BoundaryValue)}
    {modes : Finset Mode} {timeHorizon : Real}
    {density : Real -> Mode -> Complex}
    (R : FiniteModeTemporalRealization S modes timeHorizon density)
    (u : ForwardGraph) (v : BackwardGraph) :
    S.bulkPairing (S.forwardTimeSecond u) v =
      S.adjointBulkPairing u (S.backwardTimeSecond v) := by
  rw [R.forwardTimePairing_eq, R.backwardTimePairing_eq]
  exact weightedTemporalGreen_finiteModes (R.forwardPath u) (R.backwardPath v)

/-- Complete directed Green model whose temporal integration-by-parts field is
constructed, rather than supplied. -/
def toDirectedWaveGreenModel {Mode : Type*} [DecidableEq Mode]
    {S : DirectedWaveGreenSkeleton
      (ForwardGraph := ForwardGraph) (BackwardGraph := BackwardGraph)
      (ForwardResidual := ForwardResidual) (BackwardResidual := BackwardResidual)
      (BoundaryFlux := BoundaryFlux) (BoundaryValue := BoundaryValue)}
    {modes : Finset Mode} {timeHorizon : Real}
    {density : Real -> Mode -> Complex}
    (R : FiniteModeTemporalRealization S modes timeHorizon density) :
    DirectedWaveGreenModel
      (ForwardGraph := ForwardGraph) (BackwardGraph := BackwardGraph)
      (ForwardResidual := ForwardResidual) (BackwardResidual := BackwardResidual)
      (BoundaryFlux := BoundaryFlux) (BoundaryValue := BoundaryValue) where
  forwardTimeSecond := S.forwardTimeSecond
  forwardSpatial := S.forwardSpatial
  forwardWave := S.forwardWave
  backwardTimeSecond := S.backwardTimeSecond
  backwardSpatial := S.backwardSpatial
  backwardWave := S.backwardWave
  bulkPairing := S.bulkPairing
  adjointBulkPairing := S.adjointBulkPairing
  normalTrace := S.normalTrace
  probeTrace := S.probeTrace
  fullBoundaryPairing := S.fullBoundaryPairing
  forwardWave_decomposition := S.forwardWave_decomposition
  backwardWave_decomposition := S.backwardWave_decomposition
  timeIntegrationByParts := R.timeIntegrationByParts
  spatialGreenFormula := S.spatialGreenFormula

/-- The model produced by the adapter inherits the exact directed Green
identity used in equation (4.3). -/
theorem generated_greenIdentity {Mode : Type*} [DecidableEq Mode]
    {S : DirectedWaveGreenSkeleton
      (ForwardGraph := ForwardGraph) (BackwardGraph := BackwardGraph)
      (ForwardResidual := ForwardResidual) (BackwardResidual := BackwardResidual)
      (BoundaryFlux := BoundaryFlux) (BoundaryValue := BoundaryValue)}
    {modes : Finset Mode} {timeHorizon : Real}
    {density : Real -> Mode -> Complex}
    (R : FiniteModeTemporalRealization S modes timeHorizon density)
    (u : ForwardGraph) (v : BackwardGraph)
    (hv : S.backwardWave v = 0) :
    -S.bulkPairing (S.forwardWave u) v =
      S.fullBoundaryPairing (S.normalTrace u) (S.probeTrace v) := by
  exact R.toDirectedWaveGreenModel.greenIdentity u v hv

end FiniteModeTemporalRealization

end Adapter

end LiuWang2025SemilinearWaveTemporalGreen
