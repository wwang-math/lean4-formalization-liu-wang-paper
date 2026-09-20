import LiuWang.LiuWang2025SemilinearWaveFactorialImplicitSolutionMap
import LiuWang.LiuWang2025SemilinearWaveGeneratedThirdOrder

/-! # Liu--Wang Banach-algebra Nemytskii realization

The semilinear wave source in Liu--Wang is a factorially normalized
holomorphic power series whose coefficients multiply powers of the state.
The existing implicit-solution module accepted each coefficient as an
arbitrary bounded multilinear map.  This file constructs those maps from
ordinary multiplication in a commutative complex Banach algebra, the natural
setting for scalar Sobolev function spaces.

For a coefficient `V_k` in the algebra, Lean constructs the actual bounded
map

`(u_1, ..., u_k) |-> inclusion (V_k * u_1 * ... * u_k)`,

proves its product-norm estimate, identifies its diagonal with
`inclusion (V_k * u^k)`, and derives the exact finite factorial Nemytskii
source.  The source is proved `C^m`, vanishes at the zero background, and has
zero first Frechet derivative there because it starts at cubic order.  An
invertible linear residual then generates the local solution map and its
first variation through the already checked implicit-function theorem.
Commutativity also proves permutation invariance of every coefficient map and
supplies a two-model adapter to the generated third-order wave equations.

The remaining paper-facing obligation is now narrower: choose the concrete
Lorentzian solution algebra and residual space and prove the Sobolev product,
embedding, trace, and linear wave-isomorphism estimates that instantiate the
objects below.  This module does not assume or claim that realization.
-/

noncomputable section

open scoped BigOperators Topology

namespace LiuWang2025SemilinearWaveBanachAlgebraNemytskii

open LiuWang2025SemilinearWaveFactorialImplicitSolutionMap
open LiuWang2025SemilinearWaveGeneratedThirdOrder
open LiuWang2025SemilinearWaveThirdOrderGreen

variable {Parameter Algebra Residual : Type*}
variable [NormedAddCommGroup Parameter] [NormedSpace Complex Parameter]
variable [CompleteSpace Parameter]
variable [NormedCommRing Algebra] [NormedAlgebra Complex Algebra]
variable [NormOneClass Algebra] [CompleteSpace Algebra]
variable [NormedAddCommGroup Residual] [NormedSpace Complex Residual]
variable [CompleteSpace Residual]
variable {order : Nat}

/-- The bounded `k`-linear coefficient map obtained by multiplying the input
states in the Banach algebra, multiplying by the spatial coefficient, and
embedding the product into the equation residual. -/
def coefficientMultilinear
    (inclusion : Algebra →L[Complex] Residual)
    (coefficient : Algebra) (k : Nat) :
    Algebra [×k]→L[Complex] Residual :=
  inclusion.compContinuousMultilinearMap <|
    (ContinuousLinearMap.mulLeftRight Complex Algebra coefficient 1).compContinuousMultilinearMap
      (ContinuousMultilinearMap.mkPiAlgebraFin Complex k Algebra)

theorem coefficientMultilinear_apply
    (inclusion : Algebra →L[Complex] Residual)
    (coefficient : Algebra) (k : Nat) (u : Fin k → Algebra) :
    coefficientMultilinear inclusion coefficient k u =
      inclusion (coefficient * (List.ofFn u).prod) := by
  simp [coefficientMultilinear, Function.comp_def,
    ContinuousMultilinearMap.mkPiAlgebraFin_apply]

/-- On the diagonal, the constructed multilinear coefficient is exactly the
paper's pointwise power `V_k u^k`. -/
theorem coefficientMultilinear_apply_const
    (inclusion : Algebra →L[Complex] Residual)
    (coefficient : Algebra) (k : Nat) (u : Algebra) :
    coefficientMultilinear inclusion coefficient k (fun _ => u) =
      inclusion (coefficient * u ^ k) := by
  rw [coefficientMultilinear_apply]
  simp

/-- Product estimate for the actual Banach-algebra coefficient map. -/
theorem coefficientMultilinear_norm_apply_le
    (inclusion : Algebra →L[Complex] Residual)
    (coefficient : Algebra) (k : Nat) (u : Fin k → Algebra) :
    ‖coefficientMultilinear inclusion coefficient k u‖ <=
      ‖inclusion‖ * ‖coefficient‖ * ∏ i, ‖u i‖ := by
  rw [coefficientMultilinear_apply]
  calc
    ‖inclusion (coefficient * (List.ofFn u).prod)‖ <=
        ‖inclusion‖ * ‖coefficient * (List.ofFn u).prod‖ :=
      inclusion.le_opNorm _
    _ <= ‖inclusion‖ * (‖coefficient‖ * ‖(List.ofFn u).prod‖) := by
      gcongr
      exact norm_mul_le _ _
    _ <= ‖inclusion‖ * (‖coefficient‖ * ∏ i, ‖u i‖) := by
      gcongr
      have hprod : ‖(List.ofFn u).prod‖ <=
          ((List.ofFn u).map (fun x : Algebra => ‖x‖)).prod :=
        List.norm_prod_le (List.ofFn u)
      simpa [List.map_ofFn, List.prod_ofFn] using hprod
    _ = ‖inclusion‖ * ‖coefficient‖ * ∏ i, ‖u i‖ := by ring

/-- Pointwise coefficient multiplication is permutation invariant in the
commutative Banach algebra used for scalar Sobolev functions.  This is the
exact symmetry premise consumed by the generated cubic wave equation. -/
theorem coefficientMultilinear_permutationInvariant
    (inclusion : Algebra →L[Complex] Residual)
    (coefficient : Algebra) (k : Nat) :
    IsPermutationInvariant k
      (coefficientMultilinear inclusion coefficient k) := by
  intro sigma direction
  rw [coefficientMultilinear_apply, coefficientMultilinear_apply]
  congr 1
  exact congrArg (fun z : Algebra => coefficient * z) <| by
    simpa only [List.prod_ofFn] using
      (Fintype.prod_equiv sigma (fun i => direction (sigma i)) direction
        (fun _ => rfl))

/-- Paper-shaped finite Nemytskii data on a complex Banach algebra. -/
structure Data (order : Nat) where
  linearResidual : Algebra ≃L[Complex] Residual
  parameterInsertion : Parameter →L[Complex] Residual
  algebraInclusion : Algebra →L[Complex] Residual
  coefficient : Nat → Algebra

namespace Data

/-- The concrete multiplication maps instantiate the generic finite
factorial residual. -/
def toFactorialData (data : Data (Parameter := Parameter)
    (Algebra := Algebra) (Residual := Residual) order) :
    LiuWang2025SemilinearWaveFactorialImplicitSolutionMap.Data
      (Parameter := Parameter) (State := Algebra) (Residual := Residual) order where
  linearResidual := data.linearResidual
  parameterInsertion := data.parameterInsertion
  sourceCoefficient := fun k =>
    coefficientMultilinear data.algebraInclusion (data.coefficient k) k

/-- Exact source formula: no arbitrary multilinear coefficient remains. -/
theorem nonlinearResidual_apply (data : Data (Parameter := Parameter)
    (Algebra := Algebra) (Residual := Residual) order) (u : Algebra) :
    data.toFactorialData.nonlinearResidual u =
      ∑ k ∈ Finset.Icc 3 order,
        (Nat.factorial k : Complex)⁻¹ •
          data.algebraInclusion (data.coefficient k * u ^ k) := by
  unfold LiuWang2025SemilinearWaveFactorialImplicitSolutionMap.Data.nonlinearResidual
  apply Finset.sum_congr rfl
  intro k hk
  unfold normalizedFactorialTerm diagonalMonomial
  change (Nat.factorial k : Complex)⁻¹ •
      coefficientMultilinear data.algebraInclusion (data.coefficient k) k
        (fun _ => u) =
    (Nat.factorial k : Complex)⁻¹ •
      data.algebraInclusion (data.coefficient k * u ^ k)
  rw [coefficientMultilinear_apply_const]

/-- The generated finite Nemytskii source is smooth through the requested
order. -/
theorem nonlinearResidual_contDiff (data : Data (Parameter := Parameter)
    (Algebra := Algebra) (Residual := Residual) order) :
    ContDiff Complex order data.toFactorialData.nonlinearResidual :=
  data.toFactorialData.nonlinearResidual_contDiff

/-- Since the paper's source begins at order three, its derivative at the
zero background is exactly zero. -/
theorem nonlinearResidual_hasFDerivAt_zero
    (data : Data (Parameter := Parameter)
      (Algebra := Algebra) (Residual := Residual) order) :
    HasFDerivAt data.toFactorialData.nonlinearResidual
      (0 : Algebra →L[Complex] Residual) 0 :=
  data.toFactorialData.nonlinearResidual_hasFDerivAt_zero

/-- Local source-to-solution map generated from the Banach-algebra
Nemytskii source and the supplied linear wave isomorphism. -/
def solutionMap (data : Data (Parameter := Parameter)
    (Algebra := Algebra) (Residual := Residual) order)
    (horder : 1 <= order) : Parameter → Algebra :=
  data.toFactorialData.solutionMap horder

@[simp] theorem solutionMap_zero
    (data : Data (Parameter := Parameter)
      (Algebra := Algebra) (Residual := Residual) order)
    (horder : 1 <= order) :
    data.solutionMap horder 0 = 0 :=
  data.toFactorialData.solutionMap_zero horder

/-- The generated solution satisfies the full finite semilinear residual in
a neighborhood of the zero source. -/
theorem eventually_residual_solutionMap_eq_zero
    (data : Data (Parameter := Parameter)
      (Algebra := Algebra) (Residual := Residual) order)
    (horder : 1 <= order) :
    ∀ᶠ parameter in nhds (0 : Parameter),
      data.toFactorialData.toImplicitData.residual
        (parameter, data.solutionMap horder parameter) = 0 :=
  data.toFactorialData.eventually_residual_solutionMap_eq_zero horder

/-- The generated source-to-solution map has the requested local
differentiability. -/
theorem solutionMap_contDiffAt
    (data : Data (Parameter := Parameter)
      (Algebra := Algebra) (Residual := Residual) order)
    (horder : 1 <= order) :
    ContDiffAt Complex order (data.solutionMap horder) 0 :=
  data.toFactorialData.solutionMap_contDiffAt horder

/-- The first variation solves the supplied linear wave equation exactly. -/
theorem linearResidual_fderiv_solutionMap_zero
    (data : Data (Parameter := Parameter)
      (Algebra := Algebra) (Residual := Residual) order)
    (horder : 1 <= order) (direction : Parameter) :
    data.linearResidual
        (fderiv Complex (data.solutionMap horder) 0 direction) =
      data.parameterInsertion direction :=
  data.toFactorialData.linearResidual_fderiv_solutionMap_zero horder direction

/-- One product-facing certificate exposing the constructed Nemytskii map,
its norm estimate, smoothness, zero-background derivative, generated local
solution map, and exact first variation. -/
structure Certificate
    (data : Data (Parameter := Parameter)
      (Algebra := Algebra) (Residual := Residual) order)
    (horder : 1 <= order) : Prop where
  coefficientFormula : forall k (u : Fin k → Algebra),
    coefficientMultilinear data.algebraInclusion (data.coefficient k) k u =
      data.algebraInclusion (data.coefficient k * (List.ofFn u).prod)
  coefficientBound : forall k (u : Fin k → Algebra),
    ‖coefficientMultilinear data.algebraInclusion (data.coefficient k) k u‖ <=
      ‖data.algebraInclusion‖ * ‖data.coefficient k‖ * ∏ i, ‖u i‖
  coefficientPermutationInvariant : forall k,
    IsPermutationInvariant k
      (coefficientMultilinear data.algebraInclusion (data.coefficient k) k)
  sourceFormula : forall u,
    data.toFactorialData.nonlinearResidual u =
      ∑ k ∈ Finset.Icc 3 order,
        (Nat.factorial k : Complex)⁻¹ •
          data.algebraInclusion (data.coefficient k * u ^ k)
  sourceSmooth : ContDiff Complex order data.toFactorialData.nonlinearResidual
  sourceFirstDerivativeZero :
    HasFDerivAt data.toFactorialData.nonlinearResidual
      (0 : Algebra →L[Complex] Residual) 0
  generatedSolutionZero : data.solutionMap horder 0 = 0
  generatedSolutionSmooth :
    ContDiffAt Complex order (data.solutionMap horder) 0
  firstVariationEquation : forall direction,
    data.linearResidual
        (fderiv Complex (data.solutionMap horder) 0 direction) =
      data.parameterInsertion direction

def certificate
    (data : Data (Parameter := Parameter)
      (Algebra := Algebra) (Residual := Residual) order)
    (horder : 1 <= order) : Certificate data horder where
  coefficientFormula := fun k u =>
    coefficientMultilinear_apply _ _ k u
  coefficientBound := fun k u =>
    coefficientMultilinear_norm_apply_le _ _ k u
  coefficientPermutationInvariant := fun k =>
    coefficientMultilinear_permutationInvariant _ _ k
  sourceFormula := data.nonlinearResidual_apply
  sourceSmooth := data.nonlinearResidual_contDiff
  sourceFirstDerivativeZero := data.nonlinearResidual_hasFDerivAt_zero
  generatedSolutionZero := data.solutionMap_zero horder
  generatedSolutionSmooth := data.solutionMap_contDiffAt horder
  firstVariationEquation :=
    data.linearResidual_fderiv_solutionMap_zero horder

end Data

/-! ## Two-model adapter to the generated third-order wave equation -/

variable {Probe BoundaryFlux BoundaryValue : Type*}
variable [AddCommGroup Probe] [Module Complex Probe]
variable [AddCommGroup BoundaryFlux] [Module Complex BoundaryFlux]
variable [AddCommGroup BoundaryValue] [Module Complex BoundaryValue]

/-- Two literal coefficient families sharing the linear wave residual.  This
is the Nemytskii-level input needed to generate both third-order equations in
the Liu--Wang comparison argument. -/
structure ComparisonData
    (G : WaveGreenIdentityEngine
      (State := Algebra) (Residual := Residual) (Probe := Probe)
      (BoundaryFlux := BoundaryFlux) (BoundaryValue := BoundaryValue))
    (order : Nat) where
  linearResidual : Algebra ≃L[Complex] Residual
  parameterInsertion : Parameter →L[Complex] Residual
  algebraInclusion : Algebra →L[Complex] Residual
  coefficient1 : Nat → Algebra
  coefficient2 : Nat → Algebra
  wave_eq_linearResidual : G.wave = linearResidual.toLinearMap

namespace ComparisonData

variable
  {G : WaveGreenIdentityEngine
    (State := Algebra) (Residual := Residual) (Probe := Probe)
    (BoundaryFlux := BoundaryFlux) (BoundaryValue := BoundaryValue)}

/-- First concrete finite Nemytskii model. -/
def data1 (comparison : ComparisonData
    (Parameter := Parameter) G order) :
    Data (Parameter := Parameter) (Algebra := Algebra)
      (Residual := Residual) order where
  linearResidual := comparison.linearResidual
  parameterInsertion := comparison.parameterInsertion
  algebraInclusion := comparison.algebraInclusion
  coefficient := comparison.coefficient1

/-- Second concrete finite Nemytskii model. -/
def data2 (comparison : ComparisonData
    (Parameter := Parameter) G order) :
    Data (Parameter := Parameter) (Algebra := Algebra)
      (Residual := Residual) order where
  linearResidual := comparison.linearResidual
  parameterInsertion := comparison.parameterInsertion
  algebraInclusion := comparison.algebraInclusion
  coefficient := comparison.coefficient2

/-- Literal coefficient multiplication supplies the factorial data and the
permutation-invariance fields required by the generated cubic comparison. -/
def toGeneratedCubicComparisonData
    (comparison : ComparisonData (Parameter := Parameter) G order) :
    GeneratedCubicComparisonData (Parameter := Parameter) G order where
  linearResidual := comparison.linearResidual
  parameterInsertion := comparison.parameterInsertion
  sourceCoefficient1 := fun k =>
    coefficientMultilinear comparison.algebraInclusion
      (comparison.coefficient1 k) k
  sourceCoefficient2 := fun k =>
    coefficientMultilinear comparison.algebraInclusion
      (comparison.coefficient2 k) k
  cubicCoefficient1_permutationInvariant :=
    coefficientMultilinear_permutationInvariant _ _ 3
  cubicCoefficient2_permutationInvariant :=
    coefficientMultilinear_permutationInvariant _ _ 3
  wave_eq_linearResidual := comparison.wave_eq_linearResidual

/-- Both equation-(4.2) wave jets and their coefficient-difference equation
are generated from the two literal Nemytskii sources. -/
def generatedThirdOrderCertificate
    (comparison : ComparisonData (Parameter := Parameter) G order)
    (horder : 3 <= order) (direction : Fin 3 → Parameter) :=
  comparison.toGeneratedCubicComparisonData.certificate horder direction

end ComparisonData

end LiuWang2025SemilinearWaveBanachAlgebraNemytskii
