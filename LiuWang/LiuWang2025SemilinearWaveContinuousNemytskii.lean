import LiuWang.LiuWang2025SemilinearWaveBanachAlgebraNemytskii
import Mathlib.Topology.ContinuousMap.Compact

/-! # A concrete continuous-function Nemytskii calibration for Liu--Wang

The Liu--Wang nonlinear source is pointwise multiplication by spatial
coefficients.  The Banach-algebra realization constructs this source for an
abstract commutative Banach algebra.  This module instantiates that algebra by
the actual continuous complex-valued functions on an arbitrary compact
space.

Lean therefore verifies pointwise, for every `x`, that the constructed
`k`-linear map is

`V_k(x) * u_1(x) * ... * u_k(x)`

and that the finite factorial source is

`sum_{k=3}^N V_k(x) u(x)^k / k!`.

With the identity linear residual, the checked implicit-function theorem also
produces a local solution of the corresponding nonlinear equation in the
sup-norm Banach algebra and identifies its first variation.  This is a fully
concrete semantic calibration of the Nemytskii layer.  It does not identify
the compact space with the paper's Lorentzian cylinder or prove the Sobolev,
trace, energy, and partial-DN estimates required by the PDE.
-/

noncomputable section

open scoped BigOperators Topology

namespace LiuWang2025SemilinearWaveContinuousNemytskii

open LiuWang2025SemilinearWaveBanachAlgebraNemytskii

variable {X Parameter : Type*}
variable [TopologicalSpace X] [CompactSpace X] [Nonempty X]
variable [NormedAddCommGroup Parameter] [NormedSpace Complex Parameter]
variable [CompleteSpace Parameter]
variable {order : Nat}

/-- Concrete state and residual algebra of continuous functions on a compact
space, equipped with the sup norm and pointwise multiplication. -/
abbrev ContinuousState := C(X, Complex)

/-- Identity embedding of the pointwise product into the residual space. -/
def identityInclusion :
    ContinuousState (X := X) →L[Complex] ContinuousState (X := X) :=
  ContinuousLinearMap.id Complex _

/-- Identity linearized residual for the calibration equation. -/
def identityLinearResidual :
    ContinuousState (X := X) ≃L[Complex] ContinuousState (X := X) :=
  ContinuousLinearEquiv.refl Complex _

/-- The abstract coefficient map evaluates to literal pointwise
multiplication on the continuous-function algebra. -/
theorem coefficientMultilinear_apply_point
    (coefficient : ContinuousState (X := X)) (k : Nat)
    (u : Fin k → ContinuousState (X := X)) (x : X) :
    coefficientMultilinear identityInclusion coefficient k u x =
      coefficient x * (List.ofFn (fun i => u i x)).prod := by
  rw [coefficientMultilinear_apply]
  change coefficient x * (List.ofFn u).prod x = _
  congr 1
  have hprod (l : List (ContinuousState (X := X))) :
      l.prod x = (l.map (fun f => f x)).prod := by
    induction l with
    | nil => simp
    | cons a l ih => simp [ih]
  simpa [List.map_ofFn] using hprod (List.ofFn u)

/-- The diagonal coefficient is exactly the pointwise power `V_k(x)u(x)^k`. -/
theorem coefficientMultilinear_apply_const_point
    (coefficient u : ContinuousState (X := X)) (k : Nat) (x : X) :
    coefficientMultilinear identityInclusion coefficient k (fun _ => u) x =
      coefficient x * (u x) ^ k := by
  rw [coefficientMultilinear_apply_const]
  rfl

/-- Source data for a literal finite continuous-function Nemytskii equation. -/
structure Data (order : Nat) where
  parameterInsertion :
    Parameter →L[Complex] ContinuousState (X := X)
  coefficient : Nat → ContinuousState (X := X)

namespace Data

/-- The continuous-function model instantiates the generic Banach-algebra
source with no opaque multiplication or embedding. -/
def toBanachAlgebraData
    (data : Data (X := X) (Parameter := Parameter) order) :
    LiuWang2025SemilinearWaveBanachAlgebraNemytskii.Data
      (Parameter := Parameter) (Algebra := ContinuousState (X := X))
      (Residual := ContinuousState (X := X)) order where
  linearResidual := identityLinearResidual
  parameterInsertion := data.parameterInsertion
  algebraInclusion := identityInclusion
  coefficient := data.coefficient

/-- Exact source formula as an equality of continuous functions. -/
theorem nonlinearResidual_apply
    (data : Data (X := X) (Parameter := Parameter) order)
    (u : ContinuousState (X := X)) :
    data.toBanachAlgebraData.toFactorialData.nonlinearResidual u =
      ∑ k ∈ Finset.Icc 3 order,
        (Nat.factorial k : Complex)⁻¹ •
          (data.coefficient k * u ^ k) := by
  simpa [toBanachAlgebraData, identityInclusion] using
    data.toBanachAlgebraData.nonlinearResidual_apply u

/-- Exact finite factorial source at every physical point. -/
theorem nonlinearResidual_apply_point
    (data : Data (X := X) (Parameter := Parameter) order)
    (u : ContinuousState (X := X)) (x : X) :
    data.toBanachAlgebraData.toFactorialData.nonlinearResidual u x =
      ∑ k ∈ Finset.Icc 3 order,
        (Nat.factorial k : Complex)⁻¹ *
          (data.coefficient k x * (u x) ^ k) := by
  have h := congrArg (fun f : ContinuousState (X := X) => f x)
    (data.nonlinearResidual_apply u)
  simpa using h

/-- Local solution map for the concrete sup-norm Nemytskii equation. -/
def solutionMap
    (data : Data (X := X) (Parameter := Parameter) order)
    (horder : 1 <= order) : Parameter → ContinuousState (X := X) :=
  data.toBanachAlgebraData.solutionMap horder

@[simp] theorem solutionMap_zero
    (data : Data (X := X) (Parameter := Parameter) order)
    (horder : 1 <= order) :
    data.solutionMap horder 0 = 0 :=
  data.toBanachAlgebraData.solutionMap_zero horder

/-- Near zero, the generated state solves the concrete pointwise Nemytskii
residual equation in the sup-norm function algebra. -/
theorem eventually_residual_solutionMap_eq_zero
    (data : Data (X := X) (Parameter := Parameter) order)
    (horder : 1 <= order) :
    ∀ᶠ parameter in nhds (0 : Parameter),
      data.toBanachAlgebraData.toFactorialData.toImplicitData.residual
        (parameter, data.solutionMap horder parameter) = 0 :=
  data.toBanachAlgebraData.eventually_residual_solutionMap_eq_zero horder

/-- Near zero, the generated solution satisfies the literal scalar
Nemytskii equation at every point of the compact space. -/
theorem eventually_solutionMap_pointwise_equation
    (data : Data (X := X) (Parameter := Parameter) order)
    (horder : 1 <= order) :
    ∀ᶠ parameter in nhds (0 : Parameter), ∀ x : X,
      data.solutionMap horder parameter x +
          (∑ k ∈ Finset.Icc 3 order,
            (Nat.factorial k : Complex)⁻¹ *
              (data.coefficient k x *
                (data.solutionMap horder parameter x) ^ k)) =
        data.parameterInsertion parameter x := by
  filter_upwards [data.eventually_residual_solutionMap_eq_zero horder] with
      parameter hresidual
  intro x
  have hpoint := congrArg
    (fun f : ContinuousState (X := X) => f x) hresidual
  change
    data.solutionMap horder parameter x +
          data.toBanachAlgebraData.toFactorialData.nonlinearResidual
            (data.solutionMap horder parameter) x -
        data.parameterInsertion parameter x = 0 at hpoint
  rw [data.nonlinearResidual_apply_point] at hpoint
  exact sub_eq_zero.mp hpoint

/-- Because the calibration linear residual is the identity, the first
variation is exactly the inserted source direction. -/
theorem fderiv_solutionMap_zero
    (data : Data (X := X) (Parameter := Parameter) order)
    (horder : 1 <= order) (direction : Parameter) :
    fderiv Complex (data.solutionMap horder) 0 direction =
      data.parameterInsertion direction := by
  simpa [solutionMap, toBanachAlgebraData, identityLinearResidual] using
    data.toBanachAlgebraData.linearResidual_fderiv_solutionMap_zero
      horder direction

/-! ## Concrete second- and third-order linearizations -/

/-- Because the pointwise source begins at cubic order, its second derivative
along the generated solution map vanishes at the zero source. -/
theorem nonlinearSourceSecondJet_eq_zero
    (data : Data (X := X) (Parameter := Parameter) order)
    (horder : 2 <= order) (direction : Fin 2 → Parameter) :
    iteratedFDeriv Complex 2
        (data.toBanachAlgebraData.toFactorialData.nonlinearResidual ∘
          data.solutionMap (by omega)) 0 direction = 0 := by
  rw [LiuWang2025SemilinearWaveGeneratedThirdOrder.iteratedFDeriv_comp_eq_atomic_of_lower_outer_zero
      data.toBanachAlgebraData.toFactorialData.nonlinearResidual
      (data.solutionMap (by omega)) 0
      ((data.toBanachAlgebraData.toFactorialData.nonlinearResidual_contDiff).contDiffAt.of_le
        (by exact_mod_cast horder))
      ((data.toBanachAlgebraData.toFactorialData.solutionMap_contDiffAt
        (by omega)).of_le (by exact_mod_cast horder))
      (data.solutionMap_zero (by omega))
      (fun r hr =>
        LiuWang2025SemilinearWaveGeneratedThirdOrder.nonlinearResidual_iteratedFDeriv_eq_zero_of_lt_three
            (by omega) data.toBanachAlgebraData.toFactorialData)
      direction]
  rw [LiuWang2025SemilinearWaveGeneratedThirdOrder.nonlinearResidual_iteratedFDeriv_eq_zero_of_lt_three
      (by omega) data.toBanachAlgebraData.toFactorialData]
  rfl

/-- The concrete generated solution has no quadratic response at the zero
background. This is derived from the solved nonlinear equation. -/
theorem secondVariation_eq_zero
    (data : Data (X := X) (Parameter := Parameter) order)
    (horder : 2 <= order) (direction : Fin 2 → Parameter) :
    iteratedFDeriv Complex 2 (data.solutionMap (by omega)) 0 direction = 0 := by
  have h :=
    LiuWang2025SemilinearWaveGeneratedJetEquation.Data.higherVariation_equation
      data.toBanachAlgebraData.toFactorialData (by omega)
      (by omega) horder direction
  unfold LiuWang2025SemilinearWaveGeneratedJetEquation.Data.nonlinearSourceJet at h
  have hsource :
      iteratedFDeriv Complex 2
          (data.toBanachAlgebraData.toFactorialData.nonlinearResidual ∘
            data.toBanachAlgebraData.toFactorialData.solutionMap (by omega))
          0 direction = 0 := by
    simpa [solutionMap] using
      data.nonlinearSourceSecondJet_eq_zero horder direction
  rw [hsource] at h
  simpa [LiuWang2025SemilinearWaveGeneratedJetEquation.Data.solutionJet,
    LiuWang2025SemilinearWaveGeneratedJetEquation.Data.nonlinearSourceJet,
    solutionMap, toBanachAlgebraData, identityLinearResidual] using h

/-- Generated cubic equation in the concrete continuous-function algebra.
The third solution variation is the negative coefficient times the product
of the three exact first variations. -/
theorem thirdVariation_equation
    (data : Data (X := X) (Parameter := Parameter) order)
    (horder : 3 <= order) (direction : Fin 3 → Parameter) :
    iteratedFDeriv Complex 3 (data.solutionMap (by omega)) 0 direction =
      -coefficientMultilinear identityInclusion (data.coefficient 3) 3
        (fun i => data.parameterInsertion (direction i)) := by
  have hsymmetric :
      LiuWang2025SemilinearWaveGeneratedThirdOrder.IsPermutationInvariant 3
        (data.toBanachAlgebraData.toFactorialData.sourceCoefficient 3) := by
    simpa [toBanachAlgebraData,
      LiuWang2025SemilinearWaveBanachAlgebraNemytskii.Data.toFactorialData] using
      coefficientMultilinear_permutationInvariant
        identityInclusion (data.coefficient 3) 3
  have h :=
    LiuWang2025SemilinearWaveGeneratedThirdOrder.generatedThirdVariation_equation horder
        data.toBanachAlgebraData.toFactorialData
        hsymmetric direction
  have hfirst : (fun i =>
      fderiv Complex
        (data.toBanachAlgebraData.toFactorialData.solutionMap (by omega))
        0 (direction i)) =
      fun i => data.parameterInsertion (direction i) := by
    funext i
    simpa [solutionMap] using
      data.fderiv_solutionMap_zero (by omega) (direction i)
  rw [hfirst] at h
  simpa [solutionMap, toBanachAlgebraData, identityLinearResidual] using h

/-- Literal pointwise form of the generated cubic equation. -/
theorem thirdVariation_pointwise_equation
    (data : Data (X := X) (Parameter := Parameter) order)
    (horder : 3 <= order) (direction : Fin 3 → Parameter) (x : X) :
    iteratedFDeriv Complex 3 (data.solutionMap (by omega)) 0 direction x =
      -(data.coefficient 3 x *
        (List.ofFn (fun i => data.parameterInsertion (direction i) x)).prod) := by
  have h := congrArg (fun f : ContinuousState (X := X) => f x)
    (data.thirdVariation_equation horder direction)
  simpa [coefficientMultilinear_apply_point] using h

/-- Auditable second/third-order certificate for the literal pointwise
Nemytskii calibration. -/
structure HigherLinearizationCertificate
    (data : Data (X := X) (Parameter := Parameter) order)
    (horder : 3 <= order) : Prop where
  secondVariationZero : forall direction : Fin 2 → Parameter,
    iteratedFDeriv Complex 2 (data.solutionMap (by omega)) 0 direction = 0
  thirdVariationEquation : forall direction : Fin 3 → Parameter,
    iteratedFDeriv Complex 3 (data.solutionMap (by omega)) 0 direction =
      -coefficientMultilinear identityInclusion (data.coefficient 3) 3
        (fun i => data.parameterInsertion (direction i))
  thirdVariationPointwise : forall direction : Fin 3 → Parameter, forall x : X,
    iteratedFDeriv Complex 3 (data.solutionMap (by omega)) 0 direction x =
      -(data.coefficient 3 x *
        (List.ofFn (fun i => data.parameterInsertion (direction i) x)).prod)

def higherLinearizationCertificate
    (data : Data (X := X) (Parameter := Parameter) order)
    (horder : 3 <= order) : HigherLinearizationCertificate data horder where
  secondVariationZero := fun direction =>
    data.secondVariation_eq_zero (by omega) direction
  thirdVariationEquation := data.thirdVariation_equation horder
  thirdVariationPointwise := data.thirdVariation_pointwise_equation horder

/-- Auditable certificate for the concrete pointwise calibration model. -/
structure Certificate
    (data : Data (X := X) (Parameter := Parameter) order)
    (horder : 1 <= order) : Prop where
  coefficientPointwise : forall k
      (u : Fin k → ContinuousState (X := X)) (x : X),
    coefficientMultilinear identityInclusion (data.coefficient k) k u x =
      data.coefficient k x * (List.ofFn (fun i => u i x)).prod
  sourceAsContinuousFunction : forall u,
    data.toBanachAlgebraData.toFactorialData.nonlinearResidual u =
      ∑ k ∈ Finset.Icc 3 order,
        (Nat.factorial k : Complex)⁻¹ •
          (data.coefficient k * u ^ k)
  sourcePointwise : forall u x,
    data.toBanachAlgebraData.toFactorialData.nonlinearResidual u x =
      ∑ k ∈ Finset.Icc 3 order,
        (Nat.factorial k : Complex)⁻¹ *
          (data.coefficient k x * (u x) ^ k)
  generatedPointwiseEquation :
    ∀ᶠ parameter in nhds (0 : Parameter), ∀ x : X,
      data.solutionMap horder parameter x +
          (∑ k ∈ Finset.Icc 3 order,
            (Nat.factorial k : Complex)⁻¹ *
              (data.coefficient k x *
                (data.solutionMap horder parameter x) ^ k)) =
        data.parameterInsertion parameter x
  generatedSolutionZero : data.solutionMap horder 0 = 0
  firstVariationPointwise : forall direction,
    fderiv Complex (data.solutionMap horder) 0 direction =
      data.parameterInsertion direction

def certificate
    (data : Data (X := X) (Parameter := Parameter) order)
    (horder : 1 <= order) : Certificate data horder where
  coefficientPointwise := fun k u x =>
    coefficientMultilinear_apply_point (data.coefficient k) k u x
  sourceAsContinuousFunction := data.nonlinearResidual_apply
  sourcePointwise := data.nonlinearResidual_apply_point
  generatedPointwiseEquation :=
    data.eventually_solutionMap_pointwise_equation horder
  generatedSolutionZero := data.solutionMap_zero horder
  firstVariationPointwise := data.fderiv_solutionMap_zero horder

end Data

end LiuWang2025SemilinearWaveContinuousNemytskii
