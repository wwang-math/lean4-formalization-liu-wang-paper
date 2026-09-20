import LiuWang.LiuWang2025SemilinearWaveGaussianLocalization
import LiuWang.LiuWang2025SemilinearWaveHolomorphicRecovery

/-!
# Gaussian coefficient recovery to holomorphic nonlinearity recovery

This module composes two source-facing parts of the Liu--Wang argument.  A
family of normalized Gaussian localization packets recovers each Taylor
coefficient difference at every point in the reachable interaction region.
The factorial-series theorem then identifies the two actual holomorphic
nonlinearities there for every complex parameter.

The data structure keeps the geometric/PDE handoff explicit: the caller must
construct the Gaussian packet for every reachable point and Taylor order and
identify its recovered coefficient with the corresponding source coefficient
difference.  Lean supplies the point-recovery and infinite coefficient-to-
function composition.
-/

noncomputable section

namespace LiuWang2025SemilinearWaveGaussianHolomorphicClosure

open LiuWang2025SemilinearWaveGaussianLocalization
open LiuWang2025SemilinearWaveHolomorphicRecovery

variable {V : Type*}
variable [NormedAddCommGroup V] [InnerProductSpace Real V]
variable [MeasurableSpace V] [BorelSpace V] [FiniteDimensional Real V]
variable {reachable : Set V}

/-- Source-facing handoff from one Gaussian-beam recovery packet per point
and Taylor order to the two reachable holomorphic expansions. -/
structure ReachableGaussianCoefficientData where
  expansions : ReachableExpansionPair reachable
  gaussianPacket : ∀ p : V, p ∈ reachable → Nat →
    GaussianPointRecoveryData (V := V)
  packetPoint : ∀ (p : V) (hp : p ∈ reachable) (m : Nat),
    (gaussianPacket p hp m).point = p
  packetCoefficientDifference : ∀ (p : V) (hp : p ∈ reachable) (m : Nat),
    (gaussianPacket p hp m).coefficient p =
      expansions.coefficients1 p m - expansions.coefficients2 p m

namespace ReachableGaussianCoefficientData

/-- Each Gaussian packet kills the corresponding Taylor coefficient
difference. -/
theorem coefficients_eq
    (data : ReachableGaussianCoefficientData (reachable := reachable))
    (p : V) (hp : p ∈ reachable) (m : Nat) :
    data.expansions.coefficients1 p m =
      data.expansions.coefficients2 p m := by
  have hzero :
      (data.gaussianPacket p hp m).coefficient p = 0 := by
    simpa only [data.packetPoint p hp m] using
      (data.gaussianPacket p hp m).coefficient_at_point_eq_zero
  have hdiff :
      data.expansions.coefficients1 p m -
          data.expansions.coefficients2 p m = 0 := by
    rw [← data.packetCoefficientDifference p hp m]
    exact hzero
  exact sub_eq_zero.mp hdiff

/-- Equality of all Gaussian-recovered coefficients determines the two actual
holomorphic nonlinearities on the reachable region. -/
theorem nonlinearities_eq
    (data : ReachableGaussianCoefficientData (reachable := reachable)) :
    ∀ (p : V), p ∈ reachable → ∀ z : Complex,
      data.expansions.nonlinearity1 p z =
        data.expansions.nonlinearity2 p z :=
  data.expansions.nonlinearities_eq_on_reachable data.coefficients_eq

/-- Auditable composition certificate for the coefficient and value
endpoints. -/
structure Certificate
    (data : ReachableGaussianCoefficientData (reachable := reachable)) : Prop where
  packetPointsAreSourcePoints : ∀ (p : V) (hp : p ∈ reachable) (m : Nat),
    (data.gaussianPacket p hp m).point = p
  coefficientEquality : ∀ (p : V), p ∈ reachable → ∀ m,
    data.expansions.coefficients1 p m =
      data.expansions.coefficients2 p m
  nonlinearityEquality : ∀ (p : V), p ∈ reachable → ∀ z : Complex,
    data.expansions.nonlinearity1 p z =
      data.expansions.nonlinearity2 p z

def certificate
    (data : ReachableGaussianCoefficientData (reachable := reachable)) :
    Certificate data where
  packetPointsAreSourcePoints := data.packetPoint
  coefficientEquality := data.coefficients_eq
  nonlinearityEquality := data.nonlinearities_eq

end ReachableGaussianCoefficientData

end LiuWang2025SemilinearWaveGaussianHolomorphicClosure
