import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Analytic.IteratedFDeriv
import Mathlib.Analysis.Complex.Basic

/-!
# Liu--Wang semilinear-wave implicit solution map

This file isolates the Banach-space analytic mechanism underneath the
source-to-solution map used in the Liu--Wang higher-order linearization.
Let `Parameter` be the boundary/source-data space, `State` the directed wave
graph space, and `Residual` the equation-and-trace residual space.  Given

* an invertible linear residual operator `L : State equiv Residual`,
* a bounded parameter insertion `B : Parameter -> Residual`, and
* a `C^m` nonlinear residual `N : State -> Residual` satisfying
  `N(0) = 0` and `DN(0) = 0`,

we apply Mathlib's Banach-space implicit-function theorem to

`F(f,u) = L u + N(u) - B f`.

The resulting local solution map is proved to satisfy the semilinear
residual equation near zero, is `C^m` at zero, and has first derivative
`L^{-1} B`.  Thus higher differentiability is generated from the nonlinear
PDE residual and linear well-posedness rather than supplied as an opaque
property of an already chosen solution map.

Concrete construction of the Lorentzian graph spaces, the linear wave
isomorphism, the trace/source insertion, and the source-specific Nemytskii
estimates remain the paper-facing analytic work.
-/

noncomputable section

open scoped Topology

namespace LiuWang2025SemilinearWaveImplicitSolutionMap

variable {𝕜 : Type*} [RCLike 𝕜]
variable {Parameter State Residual : Type*}
variable [NormedAddCommGroup Parameter] [NormedSpace 𝕜 Parameter]
variable [CompleteSpace Parameter]
variable [NormedAddCommGroup State] [NormedSpace 𝕜 State]
variable [CompleteSpace State]
variable [NormedAddCommGroup Residual] [NormedSpace 𝕜 Residual]
variable [CompleteSpace Residual]
variable {order : Nat}

/-- Source-facing Banach-space data for the semilinear residual.  The
invertible linear residual is the place where concrete zero-data wave
well-posedness enters; smoothness and the vanishing first derivative of the
nonlinear residual are the Nemytskii estimates required at the zero
background. -/
structure Data (order : Nat) where
  linearResidual : State ≃L[𝕜] Residual
  parameterInsertion : Parameter →L[𝕜] Residual
  nonlinearResidual : State -> Residual
  nonlinearResidual_zero : nonlinearResidual 0 = 0
  nonlinearResidual_contDiffAt :
    ContDiffAt 𝕜 order nonlinearResidual 0
  nonlinearResidual_hasFDerivAt_zero :
    HasFDerivAt nonlinearResidual (0 : State →L[𝕜] Residual) 0

namespace Data

/-- The full semilinear equation-and-trace residual. -/
def residual (data : Data (𝕜 := 𝕜) (Parameter := Parameter) (State := State)
    (Residual := Residual) order) : Parameter × State -> Residual :=
  fun input =>
    data.linearResidual input.2 + data.nonlinearResidual input.2 -
      data.parameterInsertion input.1

/-- Linearization of the full residual at the zero background. -/
def linearizedResidual (data : Data (𝕜 := 𝕜) (Parameter := Parameter) (State := State)
    (Residual := Residual) order) : Parameter × State →L[𝕜] Residual :=
  (-data.parameterInsertion).coprod data.linearResidual

/-- The zero parameter and zero state solve the residual equation. -/
@[simp]
theorem residual_zero (data : Data (𝕜 := 𝕜) (Parameter := Parameter) (State := State)
    (Residual := Residual) order) : data.residual (0, 0) = 0 := by
  simp [residual, data.nonlinearResidual_zero]

/-- The full residual has the expected derivative at the zero background:
`(delta f, delta u) |-> L delta u - B delta f`. -/
theorem residual_hasFDerivAt_zero
    (data : Data (𝕜 := 𝕜) (Parameter := Parameter) (State := State)
      (Residual := Residual) order) :
    HasFDerivAt data.residual data.linearizedResidual (0, 0) := by
  have hlinear :
      HasFDerivAt
        (fun input : Parameter × State => data.linearResidual input.2)
        (data.linearResidual.toContinuousLinearMap.comp
          (ContinuousLinearMap.snd 𝕜 Parameter State)) (0, 0) :=
    data.linearResidual.toContinuousLinearMap.hasFDerivAt.comp (0, 0)
      hasFDerivAt_snd
  have hnonlinear :
      HasFDerivAt
        (fun input : Parameter × State => data.nonlinearResidual input.2)
        (0 : Parameter × State →L[𝕜] Residual) (0, 0) := by
    convert data.nonlinearResidual_hasFDerivAt_zero.comp (0, 0)
      (hasFDerivAt_snd (𝕜 := 𝕜) (E := Parameter) (F := State)) using 1
  have hparameter :
      HasFDerivAt
        (fun input : Parameter × State => data.parameterInsertion input.1)
        (data.parameterInsertion.comp
          (ContinuousLinearMap.fst 𝕜 Parameter State)) (0, 0) :=
    data.parameterInsertion.hasFDerivAt.comp (0, 0) hasFDerivAt_fst
  convert (hlinear.add hnonlinear).sub hparameter using 1
  apply ContinuousLinearMap.ext
  intro input
  rcases input with ⟨parameter, state⟩
  simp [linearizedResidual]
  abel

/-- Exact Fréchet derivative of the residual at zero. -/
theorem fderiv_residual_zero
    (data : Data (𝕜 := 𝕜) (Parameter := Parameter) (State := State)
      (Residual := Residual) order) :
    fderiv 𝕜 data.residual (0, 0) = data.linearizedResidual :=
  data.residual_hasFDerivAt_zero.fderiv

/-- Smoothness of the full residual is generated from smoothness of the
nonlinear residual and bounded linearity of the other two terms. -/
theorem residual_contDiffAt
    (data : Data (𝕜 := 𝕜) (Parameter := Parameter) (State := State)
      (Residual := Residual) order) :
    ContDiffAt 𝕜 order data.residual (0, 0) := by
  have hlinear :
      ContDiffAt 𝕜 order
        (fun input : Parameter × State => data.linearResidual input.2) (0, 0) :=
    data.linearResidual.contDiff.contDiffAt.comp (0, 0) contDiffAt_snd
  have hnonlinear :
      ContDiffAt 𝕜 order
        (fun input : Parameter × State => data.nonlinearResidual input.2) (0, 0) :=
    data.nonlinearResidual_contDiffAt.comp (0, 0) contDiffAt_snd
  have hparameter :
      ContDiffAt 𝕜 order
        (fun input : Parameter × State => data.parameterInsertion input.1) (0, 0) :=
    data.parameterInsertion.contDiff.contDiffAt.comp (0, 0) contDiffAt_fst
  simpa [residual] using (hlinear.add hnonlinear).sub hparameter

/-- The state derivative of the residual is exactly the invertible linear
wave residual operator. -/
theorem stateDerivative_eq_linearResidual
    (data : Data (𝕜 := 𝕜) (Parameter := Parameter) (State := State)
      (Residual := Residual) order) :
    fderiv 𝕜 data.residual (0, 0) ∘L
        ContinuousLinearMap.inr 𝕜 Parameter State =
      data.linearResidual := by
  rw [data.fderiv_residual_zero]
  simp [linearizedResidual]

/-- The parameter derivative of the residual is minus the source/trace
insertion. -/
theorem parameterDerivative_eq_neg_insertion
    (data : Data (𝕜 := 𝕜) (Parameter := Parameter) (State := State)
      (Residual := Residual) order) :
    fderiv 𝕜 data.residual (0, 0) ∘L
        ContinuousLinearMap.inl 𝕜 Parameter State =
      -data.parameterInsertion := by
  rw [data.fderiv_residual_zero]
  simp [linearizedResidual]

/-- Invertibility required by the implicit-function theorem follows from
linear wave well-posedness. -/
theorem stateDerivative_isInvertible
    (data : Data (𝕜 := 𝕜) (Parameter := Parameter) (State := State)
      (Residual := Residual) order) :
    (fderiv 𝕜 data.residual (0, 0) ∘L
      ContinuousLinearMap.inr 𝕜 Parameter State).IsInvertible := by
  rw [data.stateDerivative_eq_linearResidual]
  exact ContinuousLinearMap.isInvertible_equiv

/-- Positive differentiability order, expressed in the index type consumed
by Mathlib's implicit-function theorem. -/
theorem differentiabilityOrder_ne_zero
    (data : Data (𝕜 := 𝕜) (Parameter := Parameter) (State := State)
      (Residual := Residual) order) (horder : 1 <= order) :
    (order : WithTop ℕ∞) ≠ 0 := by
  have hpositive : 0 < order := lt_of_lt_of_le Nat.zero_lt_one horder
  exact_mod_cast hpositive.ne'

/-- Canonical local semilinear source-to-solution map generated by the
implicit-function theorem. -/
def solutionMap
    (data : Data (𝕜 := 𝕜) (Parameter := Parameter) (State := State)
      (Residual := Residual) order) (horder : 1 <= order) : Parameter -> State :=
  data.residual_contDiffAt.implicitFunction
    (data.differentiabilityOrder_ne_zero horder)
    data.stateDerivative_isInvertible

/-- The generated solution map sends zero data to the zero state. -/
@[simp]
theorem solutionMap_zero
    (data : Data (𝕜 := 𝕜) (Parameter := Parameter) (State := State)
      (Residual := Residual) order) (horder : 1 <= order) :
    data.solutionMap horder 0 = 0 := by
  exact data.residual_contDiffAt.implicitFunction_apply_self
    (data.differentiabilityOrder_ne_zero horder)
    data.stateDerivative_isInvertible

/-- Near zero, the generated map solves the complete semilinear residual
equation rather than only its linearization. -/
theorem eventually_residual_solutionMap_eq_zero
    (data : Data (𝕜 := 𝕜) (Parameter := Parameter) (State := State)
      (Residual := Residual) order) (horder : 1 <= order) :
    ∀ᶠ parameter in 𝓝 (0 : Parameter),
      data.residual (parameter, data.solutionMap horder parameter) = 0 := by
  simpa only [data.residual_zero] using
    data.residual_contDiffAt.eventually_apply_implicitFunction
      (data.differentiabilityOrder_ne_zero horder)
      data.stateDerivative_isInvertible

/-- Local uniqueness in graph form: near the zero parameter-state pair, a
state solves the residual equation exactly when it is the generated implicit
solution. -/
theorem eventually_residual_eq_zero_iff_solutionMap
    (data : Data (𝕜 := 𝕜) (Parameter := Parameter) (State := State)
      (Residual := Residual) order) (horder : 1 <= order) :
    ∀ᶠ input in 𝓝 ((0 : Parameter), (0 : State)),
      data.residual input = 0 ↔
        data.solutionMap horder input.1 = input.2 := by
  simpa only [data.residual_zero] using
    data.residual_contDiffAt.eventually_apply_eq_iff_implicitFunction
      (data.differentiabilityOrder_ne_zero horder)
      data.stateDerivative_isInvertible

/-- The implicit solution map is `C^m` at zero. -/
theorem solutionMap_contDiffAt
    (data : Data (𝕜 := 𝕜) (Parameter := Parameter) (State := State)
      (Residual := Residual) order) (horder : 1 <= order) :
    ContDiffAt 𝕜 order (data.solutionMap horder) 0 := by
  exact data.residual_contDiffAt.contDiffAt_implicitFunction
    (data.differentiabilityOrder_ne_zero horder)
    data.stateDerivative_isInvertible

/-- The first variation solves the linearized wave equation:
`D u(0) = L^{-1} B`. -/
theorem solutionMap_hasStrictFDerivAt
    (data : Data (𝕜 := 𝕜) (Parameter := Parameter) (State := State)
      (Residual := Residual) order) (horder : 1 <= order) :
    HasStrictFDerivAt (data.solutionMap horder)
      (data.linearResidual.symm.toContinuousLinearMap ∘L
        data.parameterInsertion) 0 := by
  unfold solutionMap
  convert data.residual_contDiffAt.hasStrictFDerivAt_implicitFunction
    (data.differentiabilityOrder_ne_zero horder)
    data.stateDerivative_isInvertible using 1
  rw [data.stateDerivative_eq_linearResidual,
    data.parameterDerivative_eq_neg_insertion]
  simp

/-- Exact derivative of the generated solution map at zero. -/
theorem fderiv_solutionMap_zero
    (data : Data (𝕜 := 𝕜) (Parameter := Parameter) (State := State)
      (Residual := Residual) order) (horder : 1 <= order) :
    fderiv 𝕜 (data.solutionMap horder) 0 =
      data.linearResidual.symm.toContinuousLinearMap ∘L
        data.parameterInsertion :=
  (data.solutionMap_hasStrictFDerivAt horder).hasFDerivAt.fderiv

/-- The first variation satisfies the exact linear residual equation. -/
theorem linearResidual_fderiv_solutionMap_zero
    (data : Data (𝕜 := 𝕜) (Parameter := Parameter) (State := State)
      (Residual := Residual) order) (horder : 1 <= order)
    (direction : Parameter) :
    data.linearResidual (fderiv 𝕜 (data.solutionMap horder) 0 direction) =
      data.parameterInsertion direction := by
  rw [data.fderiv_solutionMap_zero]
  simp

/-! ## Generated higher solution jets -/

/-- The `m`th derivative of the generated solution map in an ordered family
of parameter directions. -/
def solutionJet
    (data : Data (𝕜 := 𝕜) (Parameter := Parameter) (State := State)
      (Residual := Residual) order) (horder : 1 <= order)
    (m : Nat) (direction : Fin m -> Parameter) : State :=
  iteratedFDeriv 𝕜 m (data.solutionMap horder) 0 direction

/-- The corresponding derivative of the nonlinear residual composed with
the generated solution map. -/
def nonlinearSourceJet
    (data : Data (𝕜 := 𝕜) (Parameter := Parameter) (State := State)
      (Residual := Residual) order) (horder : 1 <= order)
    (m : Nat) (direction : Fin m -> Parameter) : Residual :=
  iteratedFDeriv 𝕜 m
    (data.nonlinearResidual ∘ data.solutionMap horder) 0 direction

/-- The actual locally solved residual has zero derivatives of every order
at the base parameter. -/
theorem iteratedFDeriv_residualAlongSolution_eq_zero
    (data : Data (𝕜 := 𝕜) (Parameter := Parameter) (State := State)
      (Residual := Residual) order) (horder : 1 <= order) (m : Nat) :
    iteratedFDeriv 𝕜 m
      (fun parameter =>
        data.residual (parameter, data.solutionMap horder parameter)) 0 = 0 := by
  have hlocal :
      (fun parameter =>
          data.residual (parameter, data.solutionMap horder parameter)) =ᶠ[
            𝓝 (0 : Parameter)]
        (fun _ => (0 : Residual)) := by
    filter_upwards [data.eventually_residual_solutionMap_eq_zero horder]
      with parameter hp
    exact hp
  have hderiv := Filter.EventuallyEq.iteratedFDeriv 𝕜 hlocal m
  exact hderiv.eq_of_nhds.trans (by simp)

/-- Every derivative of order at least two of the bounded linear parameter
insertion vanishes. -/
theorem iteratedFDeriv_parameterInsertion_eq_zero_of_two_le
    (data : Data (𝕜 := 𝕜) (Parameter := Parameter) (State := State)
      (Residual := Residual) order) {m : Nat} (hm : 2 <= m) :
    iteratedFDeriv 𝕜 m data.parameterInsertion 0 = 0 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hm
  rw [show 2 + n = (n + 1) + 1 by omega]
  rw [iteratedFDeriv_succ_eq_comp_right]
  have hfderiv :
      (fun y : Parameter => fderiv 𝕜 data.parameterInsertion y) =
        fun _ => data.parameterInsertion := by
    funext y
    exact data.parameterInsertion.hasFDerivAt.fderiv
  rw [hfderiv,
    iteratedFDeriv_const_of_ne (by omega) data.parameterInsertion]
  rfl

/-- Differentiating the solved semilinear residual generates the higher
variation equation

`L(D^m u(0)) = -D^m(N o u)(0)`

for every `2 <= m <= order`. -/
theorem higherVariation_equation
    (data : Data (𝕜 := 𝕜) (Parameter := Parameter) (State := State)
      (Residual := Residual) order) (horder : 1 <= order)
    {m : Nat} (hm : 2 <= m) (hmorder : m <= order)
    (direction : Fin m -> Parameter) :
    data.linearResidual (data.solutionJet horder m direction) =
      -data.nonlinearSourceJet horder m direction := by
  have hmorder' : (m : WithTop ℕ∞) <= (order : WithTop ℕ∞) := by
    exact_mod_cast hmorder
  have hsolution : ContDiffAt 𝕜 m (data.solutionMap horder) 0 :=
    (data.solutionMap_contDiffAt horder).of_le hmorder'
  have hlinear : ContDiffAt 𝕜 m
      (data.linearResidual.toContinuousLinearMap ∘ data.solutionMap horder) 0 :=
    hsolution.continuousLinearMap_comp data.linearResidual.toContinuousLinearMap
  have hnonlinearAt : ContDiffAt 𝕜 m data.nonlinearResidual
      (data.solutionMap horder 0) := by
    simpa only [data.solutionMap_zero horder] using
      data.nonlinearResidual_contDiffAt.of_le hmorder'
  have hnonlinear : ContDiffAt 𝕜 m
      (data.nonlinearResidual ∘ data.solutionMap horder) 0 :=
    hnonlinearAt.comp 0 hsolution
  have hparameter : ContDiffAt 𝕜 m data.parameterInsertion 0 :=
    data.parameterInsertion.contDiff.contDiffAt
  have hresidual :=
    data.iteratedFDeriv_residualAlongSolution_eq_zero horder m
  have hdecomposed := congrArg (fun jet => jet direction) hresidual
  change iteratedFDeriv 𝕜 m
      (fun parameter =>
        (data.linearResidual.toContinuousLinearMap ∘ data.solutionMap horder)
            parameter +
          (data.nonlinearResidual ∘ data.solutionMap horder) parameter -
          data.parameterInsertion parameter) 0 direction = 0 at hdecomposed
  have hsplit := iteratedFDeriv_sub_apply
    (x := (0 : Parameter))
    (f := fun parameter =>
      (data.linearResidual.toContinuousLinearMap ∘ data.solutionMap horder)
          parameter +
        (data.nonlinearResidual ∘ data.solutionMap horder) parameter)
    (g := fun parameter => data.parameterInsertion parameter)
    (hlinear.add hnonlinear) hparameter
  have hadd := iteratedFDeriv_add_apply hlinear hnonlinear
  have hadd' :
      iteratedFDeriv 𝕜 m
          (fun parameter =>
            (data.linearResidual.toContinuousLinearMap ∘ data.solutionMap horder)
                parameter +
              (data.nonlinearResidual ∘ data.solutionMap horder) parameter) 0 =
        iteratedFDeriv 𝕜 m
            (data.linearResidual.toContinuousLinearMap ∘ data.solutionMap horder) 0 +
          iteratedFDeriv 𝕜 m
            (data.nonlinearResidual ∘ data.solutionMap horder) 0 := by
    simpa only [Pi.add_apply] using hadd
  have hsplitDirection := congrArg (fun jet => jet direction) hsplit
  rw [hadd',
    data.linearResidual.toContinuousLinearMap.iteratedFDeriv_comp_left
      hsolution (by rfl)] at hsplitDirection
  rw [data.iteratedFDeriv_parameterInsertion_eq_zero_of_two_le hm]
    at hsplitDirection
  simp only [ContinuousMultilinearMap.add_apply, sub_zero] at hsplitDirection
  change (iteratedFDeriv 𝕜 m
      ((fun parameter =>
          (data.linearResidual.toContinuousLinearMap ∘ data.solutionMap horder)
              parameter +
            (data.nonlinearResidual ∘ data.solutionMap horder) parameter) -
        fun parameter => data.parameterInsertion parameter) 0) direction =
      data.linearResidual
          (iteratedFDeriv 𝕜 m (data.solutionMap horder) 0 direction) +
        iteratedFDeriv 𝕜 m
          (data.nonlinearResidual ∘ data.solutionMap horder) 0 direction
    at hsplitDirection
  have hreform :
      (fun parameter =>
        (data.linearResidual.toContinuousLinearMap ∘ data.solutionMap horder)
            parameter +
          (data.nonlinearResidual ∘ data.solutionMap horder) parameter -
          data.parameterInsertion parameter) =
        ((fun parameter =>
          (data.linearResidual.toContinuousLinearMap ∘ data.solutionMap horder)
              parameter +
            (data.nonlinearResidual ∘ data.solutionMap horder) parameter) -
          fun parameter => data.parameterInsertion parameter) := rfl
  rw [hreform, hsplitDirection] at hdecomposed
  exact eq_neg_of_add_eq_zero_left hdecomposed

/-- Auditable certificate for the generated local solution map. -/
structure Certificate
    (data : Data (𝕜 := 𝕜) (Parameter := Parameter) (State := State)
      (Residual := Residual) order) (horder : 1 <= order) : Prop where
  zeroBackground : data.solutionMap horder 0 = 0
  residualEquation : ∀ᶠ parameter in 𝓝 (0 : Parameter),
    data.residual (parameter, data.solutionMap horder parameter) = 0
  higherDifferentiability :
    ContDiffAt 𝕜 order (data.solutionMap horder) 0
  firstVariation :
    fderiv 𝕜 (data.solutionMap horder) 0 =
      data.linearResidual.symm.toContinuousLinearMap ∘L
        data.parameterInsertion
  linearizedEquation : forall direction,
    data.linearResidual (fderiv 𝕜 (data.solutionMap horder) 0 direction) =
      data.parameterInsertion direction

/-- The certificate fields are all generated from residual smoothness and
linear wave invertibility. -/
def certificate
    (data : Data (𝕜 := 𝕜) (Parameter := Parameter) (State := State)
      (Residual := Residual) order) (horder : 1 <= order) :
    Certificate data horder where
  zeroBackground := data.solutionMap_zero horder
  residualEquation := data.eventually_residual_solutionMap_eq_zero horder
  higherDifferentiability := data.solutionMap_contDiffAt horder
  firstVariation := data.fderiv_solutionMap_zero horder
  linearizedEquation := data.linearResidual_fderiv_solutionMap_zero horder

end Data

end LiuWang2025SemilinearWaveImplicitSolutionMap
