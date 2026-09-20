import LiuWang.LiuWang2025SemilinearWaveFactorialImplicitSolutionMap

/-!
# Generated higher linearizations for the Liu--Wang solution map

The factorial implicit-solution module constructs a local source-to-solution
map `u` from the semilinear residual equation

`L u + N(u) - B f = 0`.

This file differentiates that generated equation. For every `m >= 2`, Lean
proves

`L (D^m u(0)[f_1,...,f_m]) = -D^m (N o u)(0)[f_1,...,f_m]`.

Thus the higher linearized wave equation is derived from the local nonlinear
solution map, the bounded linear wave residual, and the factorial source. It
is not supplied as a separate paper-facing hypothesis.
-/

noncomputable section

open scoped Topology

namespace LiuWang2025SemilinearWaveGeneratedJetEquation

open LiuWang2025SemilinearWaveFactorialImplicitSolutionMap

variable {Parameter State Residual : Type*}
variable [NormedAddCommGroup Parameter] [NormedSpace Complex Parameter]
variable [CompleteSpace Parameter]
variable [NormedAddCommGroup State] [NormedSpace Complex State]
variable [CompleteSpace State]
variable [NormedAddCommGroup Residual] [NormedSpace Complex Residual]
variable [CompleteSpace Residual]
variable {order m : Nat}

namespace Data

/-- The `m`th source derivative of the generated state, evaluated on an
ordered family of source directions. -/
def solutionJet
    (data : LiuWang2025SemilinearWaveFactorialImplicitSolutionMap.Data
      (Parameter := Parameter) (State := State) (Residual := Residual) order)
    (horder : 1 <= order) (m : Nat) (direction : Fin m -> Parameter) : State :=
  iteratedFDeriv Complex m (data.solutionMap horder) 0 direction

/-- The corresponding `m`th differentiated nonlinear source. -/
def nonlinearSourceJet
    (data : LiuWang2025SemilinearWaveFactorialImplicitSolutionMap.Data
      (Parameter := Parameter) (State := State) (Residual := Residual) order)
    (horder : 1 <= order) (m : Nat) (direction : Fin m -> Parameter) : Residual :=
  iteratedFDeriv Complex m
    (data.nonlinearResidual ∘ data.solutionMap horder) 0 direction

/-- The locally solved residual vanishes to every iterated Frechet order at
the zero source. This follows from the actual neighborhood equation. -/
theorem iteratedFDeriv_residualAlongSolution_eq_zero
    (data : LiuWang2025SemilinearWaveFactorialImplicitSolutionMap.Data
      (Parameter := Parameter) (State := State) (Residual := Residual) order)
    (horder : 1 <= order) (m : Nat) :
    iteratedFDeriv Complex m
      (fun parameter => data.toImplicitData.residual
        (parameter, data.solutionMap horder parameter)) 0 = 0 := by
  have hlocal :
      (fun parameter => data.toImplicitData.residual
          (parameter, data.solutionMap horder parameter)) =ᶠ[𝓝 (0 : Parameter)]
        (fun _ => (0 : Residual)) := by
    filter_upwards [data.eventually_residual_solutionMap_eq_zero horder] with parameter hp
    exact hp
  have hderiv := Filter.EventuallyEq.iteratedFDeriv Complex hlocal m
  exact hderiv.eq_of_nhds.trans (by simp)

/-- Every derivative of order at least two of the bounded linear source
insertion vanishes. -/
theorem iteratedFDeriv_parameterInsertion_eq_zero_of_two_le
    (data : LiuWang2025SemilinearWaveFactorialImplicitSolutionMap.Data
      (Parameter := Parameter) (State := State) (Residual := Residual) order)
    (hm : 2 <= m) :
    iteratedFDeriv Complex m data.parameterInsertion 0 = 0 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hm
  rw [show 2 + n = (n + 1) + 1 by omega]
  rw [iteratedFDeriv_succ_eq_comp_right]
  have hfderiv :
      (fun y : Parameter => fderiv Complex data.parameterInsertion y) =
        fun _ => data.parameterInsertion := by
    funext y
    exact data.parameterInsertion.hasFDerivAt.fderiv
  rw [hfderiv, iteratedFDeriv_const_of_ne (by omega) data.parameterInsertion]
  rfl

/-- Generated higher-linearization equation. For `m >= 2`, applying the
linear wave residual to the `m`th solution jet gives the negative `m`th jet
of the composed nonlinear source. -/
theorem higherVariation_equation
    (data : LiuWang2025SemilinearWaveFactorialImplicitSolutionMap.Data
      (Parameter := Parameter) (State := State) (Residual := Residual) order)
    (horder : 1 <= order) (hm : 2 <= m) (hmorder : m <= order)
    (direction : Fin m -> Parameter) :
    data.linearResidual (solutionJet data horder m direction) =
      -nonlinearSourceJet data horder m direction := by
  have hsolution : ContDiffAt Complex m (data.solutionMap horder) 0 :=
    (data.solutionMap_contDiffAt horder).of_le (by exact_mod_cast hmorder)
  have hlinear : ContDiffAt Complex m
      (data.linearResidual.toContinuousLinearMap ∘ data.solutionMap horder) 0 :=
    hsolution.continuousLinearMap_comp data.linearResidual.toContinuousLinearMap
  have hnonlinear : ContDiffAt Complex m
      (data.nonlinearResidual ∘ data.solutionMap horder) 0 :=
    (data.nonlinearResidual_contDiff.contDiffAt.of_le
      (by exact_mod_cast hmorder)).comp 0 hsolution
  have hparameter : ContDiffAt Complex m data.parameterInsertion 0 :=
    data.parameterInsertion.contDiff.contDiffAt
  have hresidual :=
    iteratedFDeriv_residualAlongSolution_eq_zero data horder m
  have hdecomposed := congrArg (fun jet => jet direction) hresidual
  change iteratedFDeriv Complex m
      (fun parameter =>
        (data.linearResidual.toContinuousLinearMap ∘ data.solutionMap horder) parameter +
          (data.nonlinearResidual ∘ data.solutionMap horder) parameter -
          data.parameterInsertion parameter) 0 direction = 0 at hdecomposed
  have hsplit := iteratedFDeriv_sub_apply
    (x := (0 : Parameter))
    (f := fun parameter =>
      (data.linearResidual.toContinuousLinearMap ∘ data.solutionMap horder) parameter +
        (data.nonlinearResidual ∘ data.solutionMap horder) parameter)
    (g := fun parameter => data.parameterInsertion parameter)
    (hlinear.add hnonlinear) hparameter
  have hadd := iteratedFDeriv_add_apply hlinear hnonlinear
  have hadd' :
      iteratedFDeriv Complex m
          (fun parameter =>
            (data.linearResidual.toContinuousLinearMap ∘ data.solutionMap horder) parameter +
              (data.nonlinearResidual ∘ data.solutionMap horder) parameter) 0 =
        iteratedFDeriv Complex m
            (data.linearResidual.toContinuousLinearMap ∘ data.solutionMap horder) 0 +
          iteratedFDeriv Complex m
            (data.nonlinearResidual ∘ data.solutionMap horder) 0 := by
    simpa only [Pi.add_apply] using hadd
  have hsplitDirection := congrArg (fun jet => jet direction) hsplit
  rw [hadd',
    data.linearResidual.toContinuousLinearMap.iteratedFDeriv_comp_left
      hsolution (by rfl)] at hsplitDirection
  rw [iteratedFDeriv_parameterInsertion_eq_zero_of_two_le data hm] at hsplitDirection
  simp only [ContinuousMultilinearMap.add_apply, sub_zero] at hsplitDirection
  change (iteratedFDeriv Complex m
      ((fun parameter =>
          (data.linearResidual.toContinuousLinearMap ∘ data.solutionMap horder) parameter +
            (data.nonlinearResidual ∘ data.solutionMap horder) parameter) -
        fun parameter => data.parameterInsertion parameter) 0) direction =
      data.linearResidual
          (iteratedFDeriv Complex m (data.solutionMap horder) 0 direction) +
        iteratedFDeriv Complex m
          (data.nonlinearResidual ∘ data.solutionMap horder) 0 direction at hsplitDirection
  have hreform :
      (fun parameter =>
        (data.linearResidual.toContinuousLinearMap ∘ data.solutionMap horder) parameter +
          (data.nonlinearResidual ∘ data.solutionMap horder) parameter -
          data.parameterInsertion parameter) =
        ((fun parameter =>
          (data.linearResidual.toContinuousLinearMap ∘ data.solutionMap horder) parameter +
            (data.nonlinearResidual ∘ data.solutionMap horder) parameter) -
          fun parameter => data.parameterInsertion parameter) := rfl
  rw [hreform, hsplitDirection] at hdecomposed
  exact eq_neg_of_add_eq_zero_left hdecomposed

/-- Auditable certificate recording both the nonlinear residual provenance and
the generated higher-linearization equation for one ordered direction tuple. -/
structure HigherVariationCertificate
    (data : LiuWang2025SemilinearWaveFactorialImplicitSolutionMap.Data
      (Parameter := Parameter) (State := State) (Residual := Residual) order)
    (horder : 1 <= order) (hm : 2 <= m) (hmorder : m <= order)
    (direction : Fin m -> Parameter) : Prop where
  residualJetZero :
    iteratedFDeriv Complex m
      (fun parameter => data.toImplicitData.residual
        (parameter, data.solutionMap horder parameter)) 0 direction = 0
  linearSourceJetZero :
    iteratedFDeriv Complex m data.parameterInsertion 0 direction = 0
  generatedWaveEquation :
    data.linearResidual (solutionJet data horder m direction) =
      -nonlinearSourceJet data horder m direction

/-- The certificate is generated without any paper-supplied higher-order wave
equation. -/
def higherVariationCertificate
    (data : LiuWang2025SemilinearWaveFactorialImplicitSolutionMap.Data
      (Parameter := Parameter) (State := State) (Residual := Residual) order)
    (horder : 1 <= order) (hm : 2 <= m) (hmorder : m <= order)
    (direction : Fin m -> Parameter) :
    HigherVariationCertificate data horder hm hmorder direction where
  residualJetZero := by
    rw [iteratedFDeriv_residualAlongSolution_eq_zero data horder m]
    rfl
  linearSourceJetZero := by
    rw [iteratedFDeriv_parameterInsertion_eq_zero_of_two_le data hm]
    rfl
  generatedWaveEquation := higherVariation_equation data horder hm hmorder direction

end Data

end LiuWang2025SemilinearWaveGeneratedJetEquation
