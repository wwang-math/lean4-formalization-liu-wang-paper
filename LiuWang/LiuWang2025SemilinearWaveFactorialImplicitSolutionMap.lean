import LiuWang.LiuWang2025SemilinearWaveImplicitSolutionMap
import LiuWang.LiuWang2025SemilinearWaveSolutionMapFaaDiBruno
import Mathlib.Analysis.Analytic.IteratedFDeriv

/-!
# Liu--Wang factorial semilinear residual and generated solution map

The Liu--Wang nonlinearity starts at cubic order and is written with
factorial normalization.  This file realizes that structure on abstract
complex Banach graph spaces.  A bounded `k`-linear coefficient map

`A_k : State^k -> Residual`

produces the diagonal homogeneous term `A_k(u,...,u)/k!`.  Lean proves that
every such term is smooth, that its first derivative at zero vanishes for
`k >= 2`, and therefore that the finite source beginning at `k = 3` satisfies
all nonlinear hypotheses of the implicit solution-map theorem.

Consequently, invertible linear wave residual data and bounded multilinear
source coefficients generate a local `C^m` source-to-solution map with exact
first variation `L^{-1}B`.  The companion Banach-algebra module constructs the
coefficient maps from multiplication and proves their permutation symmetry.
The remaining source-facing work is the concrete Lorentzian Sobolev-algebra
realization and the passage from finite truncations to the paper's convergent
holomorphic source.
-/

noncomputable section

open scoped BigOperators Topology

namespace LiuWang2025SemilinearWaveFactorialImplicitSolutionMap

open LiuWang2025SemilinearWaveImplicitSolutionMap
open LiuWang2025SemilinearWaveSolutionMapFaaDiBruno

variable {Parameter State Residual : Type*}
variable [NormedAddCommGroup Parameter] [NormedSpace Complex Parameter]
variable [CompleteSpace Parameter]
variable [NormedAddCommGroup State] [NormedSpace Complex State]
variable [CompleteSpace State]
variable [NormedAddCommGroup Residual] [NormedSpace Complex Residual]
variable [CompleteSpace Residual]
variable {order : Nat}

/-- Continuous diagonal embedding `u |-> (u,...,u)` into `k` state slots. -/
def diagonalMap (k : Nat) : State →L[Complex] (Fin k -> State) :=
  ContinuousLinearMap.pi (fun _ => ContinuousLinearMap.id Complex State)

@[simp]
theorem diagonalMap_apply (k : Nat) (state : State) :
    diagonalMap (State := State) k state = fun _ => state := by
  rfl

/-- Homogeneous polynomial obtained by evaluating a bounded multilinear
coefficient on the diagonal. -/
def diagonalMonomial (k : Nat) (coefficient : State [×k]→L[Complex] Residual) :
    State -> Residual :=
  fun state => coefficient (diagonalMap k state)

/-- Every bounded multilinear diagonal monomial is smooth to arbitrary
finite order. -/
theorem diagonalMonomial_contDiff
    (k : Nat) (coefficient : State [×k]→L[Complex] Residual)
    (differentiabilityOrder : WithTop ℕ∞) :
    ContDiff Complex differentiabilityOrder
      (diagonalMonomial k coefficient) := by
  simpa [diagonalMonomial] using
    coefficient.contDiff.comp (diagonalMap (State := State) k).contDiff

/-- A positive-degree diagonal monomial vanishes at the zero state. -/
@[simp]
theorem diagonalMonomial_zero_of_pos
    (k : Nat) (hk : 1 <= k)
    (coefficient : State [×k]→L[Complex] Residual) :
    diagonalMonomial k coefficient 0 = 0 := by
  let i : Fin k := ⟨0, hk⟩
  apply coefficient.map_coord_zero i
  simp [diagonalMap]

/-- Every homogeneous diagonal monomial of degree at least two has zero
first Fréchet derivative at the zero state. -/
theorem diagonalMonomial_hasFDerivAt_zero_of_two_le
    (k : Nat) (hk : 2 <= k)
    (coefficient : State [×k]→L[Complex] Residual) :
    HasFDerivAt (diagonalMonomial k coefficient)
      (0 : State →L[Complex] Residual) 0 := by
  classical
  have hderiv := coefficient.hasFDerivAt (0 : Fin k -> State) |>.comp 0
    (diagonalMap (State := State) k).hasFDerivAt
  convert hderiv using 1
  apply ContinuousLinearMap.ext
  intro direction
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousMultilinearMap.linearDeriv_apply, ContinuousLinearMap.zero_apply]
  symm
  apply Finset.sum_eq_zero
  intro i hi
  letI : Nontrivial (Fin k) := Fin.nontrivial_iff_two_le.mpr hk
  obtain ⟨j, hji⟩ := exists_ne i
  apply coefficient.map_coord_zero j
  simp [diagonalMap, hji]

/-- One factorial-normalized source term. -/
def normalizedFactorialTerm
    (k : Nat) (coefficient : State [×k]→L[Complex] Residual) :
    State -> Residual :=
  fun state =>
    (Nat.factorial k : Complex)⁻¹ • diagonalMonomial k coefficient state

/-- A normalized source term of positive degree vanishes at zero. -/
@[simp]
theorem normalizedFactorialTerm_zero_of_pos
    (k : Nat) (hk : 1 <= k)
    (coefficient : State [×k]→L[Complex] Residual) :
    normalizedFactorialTerm k coefficient 0 = 0 := by
  simp [normalizedFactorialTerm, diagonalMonomial_zero_of_pos k hk coefficient]

/-- A normalized source term is smooth to arbitrary finite order. -/
theorem normalizedFactorialTerm_contDiff
    (k : Nat) (coefficient : State [×k]→L[Complex] Residual)
    (differentiabilityOrder : WithTop ℕ∞) :
    ContDiff Complex differentiabilityOrder
      (normalizedFactorialTerm k coefficient) := by
  exact (diagonalMonomial_contDiff k coefficient differentiabilityOrder).const_smul
    (Nat.factorial k : Complex)⁻¹

/-- A normalized term of degree at least two has zero first derivative at
the zero state. -/
theorem normalizedFactorialTerm_hasFDerivAt_zero_of_two_le
    (k : Nat) (hk : 2 <= k)
    (coefficient : State [×k]→L[Complex] Residual) :
    HasFDerivAt (normalizedFactorialTerm k coefficient)
      (0 : State →L[Complex] Residual) 0 := by
  simpa [normalizedFactorialTerm] using
    (diagonalMonomial_hasFDerivAt_zero_of_two_le k hk coefficient).const_smul
      (Nat.factorial k : Complex)⁻¹

/-- Paper-shaped finite factorial source data.  `sourceCoefficient k` is the
bounded `k`-linear Nemytskii coefficient map into the equation residual. -/
structure Data (order : Nat) where
  linearResidual : State ≃L[Complex] Residual
  parameterInsertion : Parameter →L[Complex] Residual
  sourceCoefficient : (k : Nat) -> State [×k]→L[Complex] Residual

namespace Data

/-- Finite factorial source beginning at cubic order. -/
def nonlinearResidual
    (data : Data (Parameter := Parameter) (State := State)
      (Residual := Residual) order) : State -> Residual :=
  fun state =>
    ∑ k ∈ Finset.Icc 3 order,
      normalizedFactorialTerm k (data.sourceCoefficient k) state

/-- The factorial source vanishes at the zero state. -/
@[simp]
theorem nonlinearResidual_zero
    (data : Data (Parameter := Parameter) (State := State)
      (Residual := Residual) order) :
    data.nonlinearResidual 0 = 0 := by
  unfold nonlinearResidual
  apply Finset.sum_eq_zero
  intro k hk
  have hk3 : 3 <= k := (Finset.mem_Icc.mp hk).1
  exact normalizedFactorialTerm_zero_of_pos k (by omega)
    (data.sourceCoefficient k)

/-- Smoothness of the finite factorial source is derived term by term. -/
theorem nonlinearResidual_contDiff
    (data : Data (Parameter := Parameter) (State := State)
      (Residual := Residual) order) :
    ContDiff Complex order data.nonlinearResidual := by
  unfold nonlinearResidual
  apply ContDiff.sum
  intro k hk
  exact normalizedFactorialTerm_contDiff k (data.sourceCoefficient k) order

/-- Because the source begins at cubic order, its first derivative at zero
vanishes. -/
theorem nonlinearResidual_hasFDerivAt_zero
    (data : Data (Parameter := Parameter) (State := State)
      (Residual := Residual) order) :
    HasFDerivAt data.nonlinearResidual
      (0 : State →L[Complex] Residual) 0 := by
  unfold nonlinearResidual
  have hterm : ∀ k ∈ Finset.Icc 3 order,
      HasFDerivAt
        (normalizedFactorialTerm k (data.sourceCoefficient k))
        (0 : State →L[Complex] Residual) 0 := by
    intro k hk
    have hk3 : 3 <= k := (Finset.mem_Icc.mp hk).1
    exact normalizedFactorialTerm_hasFDerivAt_zero_of_two_le k (by omega)
      (data.sourceCoefficient k)
  simpa using HasFDerivAt.fun_sum hterm

/-- The factorial source data automatically satisfy the hypotheses of the
generic semilinear implicit solution-map theorem. -/
def toImplicitData
    (data : Data (Parameter := Parameter) (State := State)
      (Residual := Residual) order) :
  LiuWang2025SemilinearWaveImplicitSolutionMap.Data
      (𝕜 := Complex)
      (Parameter := Parameter) (State := State) (Residual := Residual) order where
  linearResidual := data.linearResidual
  parameterInsertion := data.parameterInsertion
  nonlinearResidual := data.nonlinearResidual
  nonlinearResidual_zero := data.nonlinearResidual_zero
  nonlinearResidual_contDiffAt := data.nonlinearResidual_contDiff.contDiffAt
  nonlinearResidual_hasFDerivAt_zero :=
    data.nonlinearResidual_hasFDerivAt_zero

/-- Local solution map generated directly from the factorial source. -/
def solutionMap
    (data : Data (Parameter := Parameter) (State := State)
      (Residual := Residual) order) (horder : 1 <= order) : Parameter -> State :=
  data.toImplicitData.solutionMap horder

@[simp]
theorem solutionMap_zero
    (data : Data (Parameter := Parameter) (State := State)
      (Residual := Residual) order) (horder : 1 <= order) :
    data.solutionMap horder 0 = 0 :=
  data.toImplicitData.solutionMap_zero horder

/-- The generated map solves the complete factorial semilinear equation near
the zero boundary/source datum. -/
theorem eventually_residual_solutionMap_eq_zero
    (data : Data (Parameter := Parameter) (State := State)
      (Residual := Residual) order) (horder : 1 <= order) :
    ∀ᶠ parameter in 𝓝 (0 : Parameter),
      data.toImplicitData.residual
        (parameter, data.solutionMap horder parameter) = 0 :=
  data.toImplicitData.eventually_residual_solutionMap_eq_zero horder

/-- The generated factorial solution map has the full requested local
`C^m` regularity. -/
theorem solutionMap_contDiffAt
    (data : Data (Parameter := Parameter) (State := State)
      (Residual := Residual) order) (horder : 1 <= order) :
    ContDiffAt Complex order (data.solutionMap horder) 0 :=
  data.toImplicitData.solutionMap_contDiffAt horder

/-- Exact first variation of the generated factorial solution map. -/
theorem fderiv_solutionMap_zero
    (data : Data (Parameter := Parameter) (State := State)
      (Residual := Residual) order) (horder : 1 <= order) :
    fderiv Complex (data.solutionMap horder) 0 =
      data.linearResidual.symm.toContinuousLinearMap ∘L
        data.parameterInsertion :=
  data.toImplicitData.fderiv_solutionMap_zero horder

/-- The generated first variation satisfies the linearized wave residual
equation exactly. -/
theorem linearResidual_fderiv_solutionMap_zero
    (data : Data (Parameter := Parameter) (State := State)
      (Residual := Residual) order) (horder : 1 <= order)
    (direction : Parameter) :
    data.linearResidual (fderiv Complex (data.solutionMap horder) 0 direction) =
      data.parameterInsertion direction :=
  data.toImplicitData.linearResidual_fderiv_solutionMap_zero horder direction

/-! ## Point evaluation and the coefficient-isolation interface -/

/-- A bounded point observation of the generated state-valued solution map.
In the concrete Lorentzian realization, `evaluation` is the continuous
point-evaluation map supplied by the chosen solution graph space. -/
def pointSolutionMap
    (data : Data (Parameter := Parameter) (State := State)
      (Residual := Residual) order) (horder : 1 <= order)
    (evaluation : State →L[Complex] Complex) : Parameter -> Complex :=
  evaluation ∘ data.solutionMap horder

@[simp]
theorem pointSolutionMap_zero
    (data : Data (Parameter := Parameter) (State := State)
      (Residual := Residual) order) (horder : 1 <= order)
    (evaluation : State →L[Complex] Complex) :
    data.pointSolutionMap horder evaluation 0 = 0 := by
  simp [pointSolutionMap]

/-- Local `C^m` regularity survives every bounded point observation. -/
theorem pointSolutionMap_contDiffAt
    (data : Data (Parameter := Parameter) (State := State)
      (Residual := Residual) order) (horder : 1 <= order)
    (evaluation : State →L[Complex] Complex) :
    ContDiffAt Complex order (data.pointSolutionMap horder evaluation) 0 := by
  exact (data.solutionMap_contDiffAt horder).continuousLinearMap_comp evaluation

/-- The observed first variation is the evaluation of the linear wave
solution `L^{-1}B f`. -/
theorem pointSolutionMap_hasStrictFDerivAt
    (data : Data (Parameter := Parameter) (State := State)
      (Residual := Residual) order) (horder : 1 <= order)
    (evaluation : State →L[Complex] Complex) :
    HasStrictFDerivAt (data.pointSolutionMap horder evaluation)
      (evaluation ∘L data.linearResidual.symm.toContinuousLinearMap ∘L
        data.parameterInsertion) 0 := by
  unfold pointSolutionMap
  exact evaluation.hasStrictFDerivAt.comp 0
    (data.toImplicitData.solutionMap_hasStrictFDerivAt horder)

/-- Exact Fréchet derivative of the observed solution map. -/
theorem fderiv_pointSolutionMap_zero
    (data : Data (Parameter := Parameter) (State := State)
      (Residual := Residual) order) (horder : 1 <= order)
    (evaluation : State →L[Complex] Complex) :
    fderiv Complex (data.pointSolutionMap horder evaluation) 0 =
      evaluation ∘L data.linearResidual.symm.toContinuousLinearMap ∘L
        data.parameterInsertion :=
  (data.pointSolutionMap_hasStrictFDerivAt horder evaluation).hasFDerivAt.fderiv

/-- The first scalar solution variation used in the Liu--Wang higher-order
linearization is generated by the inverse linear residual. -/
theorem firstPointSolutionVariation_eq
    (data : Data (Parameter := Parameter) (State := State)
      (Residual := Residual) order) (horder : 1 <= order)
    (evaluation : State →L[Complex] Complex) (direction : Parameter) :
    firstSolutionVariation (data.pointSolutionMap horder evaluation) 0 direction =
      evaluation (data.linearResidual.symm (data.parameterInsertion direction)) := by
  simp [firstSolutionVariation, iteratedFDeriv_one_apply,
    data.fderiv_pointSolutionMap_zero]

/-- The local implicit solution map supplies exactly the regularity input to
the verified ordered-partition Faà di Bruno expansion. -/
theorem iteratedFDeriv_composedPointSolution_eq_partitionSum
    (data : Data (Parameter := Parameter) (State := State)
      (Residual := Residual) order) (horder : 1 <= order)
    (evaluation : State →L[Complex] Complex) (coefficient : Nat -> Complex) :
    iteratedFDeriv Complex order
        (composedTruncatedSource order coefficient
          (data.pointSolutionMap horder evaluation)) 0 =
      ∑ partition : OrderedFinpartition order,
        sourceCompositionPartitionTerm order coefficient
          (data.pointSolutionMap horder evaluation) 0 partition :=
  iteratedFDeriv_composedTruncatedSource_eq_partitionSum order coefficient
    (data.pointSolutionMap horder evaluation) 0
    (data.pointSolutionMap_contDiffAt horder evaluation)

/-- The generated point solution produces the paper's top coefficient times
the product of linear wave solutions, plus the exact non-atomic remainder. -/
theorem iteratedFDeriv_composedPointSolution_eq_top_add_remainder
    (data : Data (Parameter := Parameter) (State := State)
      (Residual := Residual) order) (horder : 1 <= order)
    (evaluation : State →L[Complex] Complex) (coefficient : Nat -> Complex)
    (direction : Fin order -> Parameter) :
    iteratedFDeriv Complex order
        (composedTruncatedSource order coefficient
          (data.pointSolutionMap horder evaluation)) 0 direction =
      coefficient order *
          ∏ i, evaluation
            (data.linearResidual.symm (data.parameterInsertion (direction i))) +
        sourceCompositionRemainder order coefficient
          (data.pointSolutionMap horder evaluation) 0 direction := by
  rw [iteratedFDeriv_composedTruncatedSource_eq_top_add_remainder
    order coefficient (data.pointSolutionMap horder evaluation) 0
    (data.pointSolutionMap_contDiffAt horder evaluation)
    (data.pointSolutionMap_zero horder evaluation) direction]
  congr 2
  apply Finset.prod_congr rfl
  intro i hi
  exact data.firstPointSolutionVariation_eq horder evaluation (direction i)

/-- For two generated semilinear solution maps, local smoothness and the zero
background are no longer assumptions in coefficient isolation.  The only
remaining induction input is equality of the already-recovered lower
coefficients and lower solution jets. -/
theorem generatedPointSolution_coefficientIsolation
    (data1 data2 : Data (Parameter := Parameter) (State := State)
      (Residual := Residual) order)
    (horder : 3 <= order)
    (evaluation1 evaluation2 : State →L[Complex] Complex)
    (coefficient1 coefficient2 : Nat -> Complex)
    (agreement : LowerOrderJetAgreement order coefficient1 coefficient2
      (data1.pointSolutionMap (by omega) evaluation1)
      (data2.pointSolutionMap (by omega) evaluation2) 0)
    (direction : Fin order -> Parameter) :
    iteratedFDeriv Complex order
          (composedTruncatedSource order coefficient1
            (data1.pointSolutionMap (by omega) evaluation1)) 0 direction -
        iteratedFDeriv Complex order
          (composedTruncatedSource order coefficient2
            (data2.pointSolutionMap (by omega) evaluation2)) 0 direction =
      (coefficient1 order - coefficient2 order) *
        ∏ i, firstSolutionVariation
          (data1.pointSolutionMap (by omega) evaluation1) 0 (direction i) := by
  exact agreement.iteratedFDeriv_composedTruncatedSource_sub_eq_coefficientDifference
    horder
    (data1.pointSolutionMap_contDiffAt (by omega) evaluation1)
    (data2.pointSolutionMap_contDiffAt (by omega) evaluation2)
    (data1.pointSolutionMap_zero (by omega) evaluation1)
    (data2.pointSolutionMap_zero (by omega) evaluation2) direction

/-- Auditable Faà di Bruno certificate for two solution maps generated by the
factorial residual model. -/
def generatedPointSolutionFaaDiBrunoCertificate
    (data1 data2 : Data (Parameter := Parameter) (State := State)
      (Residual := Residual) order)
    (horder : 3 <= order)
    (evaluation1 evaluation2 : State →L[Complex] Complex)
    (coefficient1 coefficient2 : Nat -> Complex)
    (agreement : LowerOrderJetAgreement order coefficient1 coefficient2
      (data1.pointSolutionMap (by omega) evaluation1)
      (data2.pointSolutionMap (by omega) evaluation2) 0) :
    LowerOrderJetAgreement.Certificate order coefficient1 coefficient2
      (data1.pointSolutionMap (by omega) evaluation1)
      (data2.pointSolutionMap (by omega) evaluation2) 0 agreement horder
      (data1.pointSolutionMap_contDiffAt (by omega) evaluation1)
      (data2.pointSolutionMap_contDiffAt (by omega) evaluation2)
      (data1.pointSolutionMap_zero (by omega) evaluation1)
      (data2.pointSolutionMap_zero (by omega) evaluation2) :=
  agreement.certificate order coefficient1 coefficient2
    (data1.pointSolutionMap (by omega) evaluation1)
    (data2.pointSolutionMap (by omega) evaluation2) 0 horder
    (data1.pointSolutionMap_contDiffAt (by omega) evaluation1)
    (data2.pointSolutionMap_contDiffAt (by omega) evaluation2)
    (data1.pointSolutionMap_zero (by omega) evaluation1)
    (data2.pointSolutionMap_zero (by omega) evaluation2)

/-- Auditable certificate for the factorial source and its generated local
solution map. -/
structure Certificate
    (data : Data (Parameter := Parameter) (State := State)
      (Residual := Residual) order) (horder : 1 <= order) : Prop where
  sourceZero : data.nonlinearResidual 0 = 0
  sourceFirstDerivativeZero :
    HasFDerivAt data.nonlinearResidual
      (0 : State →L[Complex] Residual) 0
  zeroBackground : data.solutionMap horder 0 = 0
  residualEquation : ∀ᶠ parameter in 𝓝 (0 : Parameter),
    data.toImplicitData.residual
      (parameter, data.solutionMap horder parameter) = 0
  higherDifferentiability :
    ContDiffAt Complex order (data.solutionMap horder) 0
  firstVariation :
    fderiv Complex (data.solutionMap horder) 0 =
      data.linearResidual.symm.toContinuousLinearMap ∘L
        data.parameterInsertion
  linearizedEquation : forall direction,
    data.linearResidual (fderiv Complex (data.solutionMap horder) 0 direction) =
      data.parameterInsertion direction
  pointEvaluationRegularity : forall evaluation : State →L[Complex] Complex,
    ContDiffAt Complex order (data.pointSolutionMap horder evaluation) 0
  pointEvaluationFirstVariation : forall
      (evaluation : State →L[Complex] Complex) (direction : Parameter),
    firstSolutionVariation (data.pointSolutionMap horder evaluation) 0 direction =
      evaluation (data.linearResidual.symm (data.parameterInsertion direction))

/-- Every certificate field is proved from bounded multilinear coefficients
and linear residual invertibility. -/
def certificate
    (data : Data (Parameter := Parameter) (State := State)
      (Residual := Residual) order) (horder : 1 <= order) :
    Certificate data horder where
  sourceZero := data.nonlinearResidual_zero
  sourceFirstDerivativeZero := data.nonlinearResidual_hasFDerivAt_zero
  zeroBackground := data.solutionMap_zero horder
  residualEquation := data.eventually_residual_solutionMap_eq_zero horder
  higherDifferentiability := data.solutionMap_contDiffAt horder
  firstVariation := data.fderiv_solutionMap_zero horder
  linearizedEquation := data.linearResidual_fderiv_solutionMap_zero horder
  pointEvaluationRegularity := data.pointSolutionMap_contDiffAt horder
  pointEvaluationFirstVariation := data.firstPointSolutionVariation_eq horder

end Data

end LiuWang2025SemilinearWaveFactorialImplicitSolutionMap
