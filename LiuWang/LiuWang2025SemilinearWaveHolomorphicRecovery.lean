import LiuWang.LiuWang2025SemilinearWaveLinearization
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Liu--Wang holomorphic nonlinearity recovery

Boya Liu and Weinan Wang, arXiv:2511.08794v1, recover the Taylor
coefficients

`V_m(t,x) = partial_z^m V(t,x,0)`

on the causally reachable interaction region and then use the convergent
factorial-weighted expansion

`V(t,x,z) = sum_m V_m(t,x) z^m / m!`

to identify the full nonlinearity.  The earlier linearization module checks
the cubic normalization, the higher-coefficient induction, and equality of
the corresponding formal power series.  This module closes the evaluation
step for the actual complex-valued nonlinearity.

The source-specific holomorphic expansion and the pointwise recovery of all
coefficients are explicit inputs.  Once supplied, Lean proves equality for
every complex parameter `z`; no additional analytic-continuation conclusion
is assumed.
-/

noncomputable section

namespace LiuWang2025SemilinearWaveHolomorphicRecovery

/-- The exact factorial-weighted Taylor term used in equation (1.1) of the
source paper. -/
def factorialWeightedTerm
    (coefficients : Nat -> Complex) (z : Complex) (m : Nat) : Complex :=
  coefficients m * z ^ m / (Nat.factorial m : Complex)

/-- Equality of one Taylor coefficient gives equality of the corresponding
factorial-weighted term at every complex parameter. -/
theorem factorialWeightedTerm_eq_of_coefficient_eq
    {coefficients1 coefficients2 : Nat -> Complex}
    (hcoeff : forall m, coefficients1 m = coefficients2 m)
    (z : Complex) (m : Nat) :
    factorialWeightedTerm coefficients1 z m =
      factorialWeightedTerm coefficients2 z m := by
  simp [factorialWeightedTerm, hcoeff m]

/-- A pointwise holomorphic nonlinearity together with the exact convergent
Taylor expansion used by the source. -/
structure PointwiseExpansion where
  nonlinearity : Complex -> Complex
  coefficients : Nat -> Complex
  hasSum_factorialExpansion : forall z,
    HasSum (fun m => factorialWeightedTerm coefficients z m)
      (nonlinearity z)

namespace PointwiseExpansion

/-- Two convergent source expansions with identical Taylor coefficients have
identical values at every complex parameter. -/
theorem nonlinearity_eq_of_coefficients_eq
    (data1 data2 : PointwiseExpansion)
    (hcoeff : forall m, data1.coefficients m = data2.coefficients m) :
    data1.nonlinearity = data2.nonlinearity := by
  funext z
  have hsum1 :
      HasSum
        (fun m => factorialWeightedTerm data2.coefficients z m)
        (data1.nonlinearity z) :=
    (data1.hasSum_factorialExpansion z).congr_fun
      (fun m =>
        (factorialWeightedTerm_eq_of_coefficient_eq hcoeff z m).symm)
  exact hsum1.unique (data2.hasSum_factorialExpansion z)

/-- Point-evaluation form of `nonlinearity_eq_of_coefficients_eq`. -/
theorem nonlinearity_apply_eq_of_coefficients_eq
    (data1 data2 : PointwiseExpansion)
    (hcoeff : forall m, data1.coefficients m = data2.coefficients m)
    (z : Complex) :
    data1.nonlinearity z = data2.nonlinearity z := by
  rw [data1.nonlinearity_eq_of_coefficients_eq data2 hcoeff]

/-- Auditable endpoint for one space-time point. -/
structure Certificate
    (data1 data2 : PointwiseExpansion) : Prop where
  coefficientEquality : forall m,
    data1.coefficients m = data2.coefficients m
  nonlinearityEquality : data1.nonlinearity = data2.nonlinearity

def certificate
    (data1 data2 : PointwiseExpansion)
    (hcoeff : forall m, data1.coefficients m = data2.coefficients m) :
    Certificate data1 data2 where
  coefficientEquality := hcoeff
  nonlinearityEquality :=
    data1.nonlinearity_eq_of_coefficients_eq data2 hcoeff

end PointwiseExpansion

/-! ## Recovery on the causally reachable interaction region -/

/-- Source-facing family of pointwise convergent expansions on a prescribed
reachable region.  The type `Point` can later be instantiated by the
space-time Lorentzian carrier. -/
structure ReachableExpansionPair
    {Point : Type*} (reachable : Set Point) where
  nonlinearity1 : Point -> Complex -> Complex
  nonlinearity2 : Point -> Complex -> Complex
  coefficients1 : Point -> Nat -> Complex
  coefficients2 : Point -> Nat -> Complex
  expansion1 : forall (p : Point), p ∈ reachable -> forall z : Complex,
    HasSum
      (fun m => factorialWeightedTerm (coefficients1 p) z m)
      (nonlinearity1 p z)
  expansion2 : forall (p : Point), p ∈ reachable -> forall z : Complex,
    HasSum
      (fun m => factorialWeightedTerm (coefficients2 p) z m)
      (nonlinearity2 p z)

namespace ReachableExpansionPair

variable {Point : Type*} {reachable : Set Point}

/-- Package the two source expansions at one reachable point. -/
def pointwiseExpansion1
    (data : ReachableExpansionPair reachable)
    (p : Point) (hp : p ∈ reachable) : PointwiseExpansion where
  nonlinearity := data.nonlinearity1 p
  coefficients := data.coefficients1 p
  hasSum_factorialExpansion := data.expansion1 p hp

/-- Package the second source expansion at one reachable point. -/
def pointwiseExpansion2
    (data : ReachableExpansionPair reachable)
    (p : Point) (hp : p ∈ reachable) : PointwiseExpansion where
  nonlinearity := data.nonlinearity2 p
  coefficients := data.coefficients2 p
  hasSum_factorialExpansion := data.expansion2 p hp

/-- Equality of every recovered Taylor coefficient on the reachable region
determines the full nonlinearity there for every complex parameter. -/
theorem nonlinearities_eq_on_reachable
    (data : ReachableExpansionPair reachable)
    (hcoeff : forall (p : Point), p ∈ reachable -> forall m,
      data.coefficients1 p m = data.coefficients2 p m) :
    forall (p : Point), p ∈ reachable -> forall z : Complex,
      data.nonlinearity1 p z = data.nonlinearity2 p z := by
  intro p hp z
  exact
    (data.pointwiseExpansion1 p hp).nonlinearity_apply_eq_of_coefficients_eq
      (data.pointwiseExpansion2 p hp) (hcoeff p hp) z

/-- Function-level form on each reachable point. -/
theorem nonlinearities_fun_eq_on_reachable
    (data : ReachableExpansionPair reachable)
    (hcoeff : forall (p : Point), p ∈ reachable -> forall m,
      data.coefficients1 p m = data.coefficients2 p m) :
    forall (p : Point), p ∈ reachable ->
      data.nonlinearity1 p = data.nonlinearity2 p := by
  intro p hp
  funext z
  exact data.nonlinearities_eq_on_reachable hcoeff p hp z

/-- Paper-facing certificate for the final coefficient-to-holomorphic-value
step on the causal interaction region. -/
structure Certificate
    (data : ReachableExpansionPair reachable) : Prop where
  coefficientEquality : forall (p : Point), p ∈ reachable -> forall m,
    data.coefficients1 p m = data.coefficients2 p m
  nonlinearityEquality : forall (p : Point), p ∈ reachable -> forall z : Complex,
    data.nonlinearity1 p z = data.nonlinearity2 p z

def certificate
    (data : ReachableExpansionPair reachable)
    (hcoeff : forall (p : Point), p ∈ reachable -> forall m,
      data.coefficients1 p m = data.coefficients2 p m) :
    Certificate data where
  coefficientEquality := hcoeff
  nonlinearityEquality := data.nonlinearities_eq_on_reachable hcoeff

end ReachableExpansionPair

end LiuWang2025SemilinearWaveHolomorphicRecovery
