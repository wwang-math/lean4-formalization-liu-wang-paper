import LiuWang.LiuWang2025SemilinearWaveBanachAlgebraNemytskii

noncomputable section

open scoped BigOperators Topology

open LiuWang2025SemilinearWaveBanachAlgebraNemytskii
open LiuWang2025SemilinearWaveGeneratedThirdOrder

namespace LiuWangBanachAlgebraNemytskiiRegression

def complexData (order : Nat) : Data
    (Parameter := Complex) (Algebra := Complex) (Residual := Complex) order where
  linearResidual := ContinuousLinearEquiv.refl Complex Complex
  parameterInsertion := ContinuousLinearMap.id Complex Complex
  algebraInclusion := ContinuousLinearMap.id Complex Complex
  coefficient := fun k => if k = 3 then 1 else 0

example (k : Nat) (u : Fin k → Complex) :
    coefficientMultilinear (ContinuousLinearMap.id Complex Complex)
        (1 : Complex) k u =
      (List.ofFn u).prod := by
  rw [coefficientMultilinear_apply]
  simp

example (k : Nat) (u : Fin k → Complex) :
    ‖coefficientMultilinear (ContinuousLinearMap.id Complex Complex)
        (1 : Complex) k u‖ <= ∏ i, ‖u i‖ := by
  simpa using coefficientMultilinear_norm_apply_le
    (ContinuousLinearMap.id Complex Complex) (1 : Complex) k u

example (k : Nat) :
    IsPermutationInvariant k
      (coefficientMultilinear (ContinuousLinearMap.id Complex Complex)
        (1 : Complex) k) :=
  coefficientMultilinear_permutationInvariant _ _ k

example : ContDiff Complex 3
    (complexData 3).toFactorialData.nonlinearResidual :=
  (complexData 3).nonlinearResidual_contDiff

example : HasFDerivAt (complexData 3).toFactorialData.nonlinearResidual
    (0 : Complex →L[Complex] Complex) 0 :=
  (complexData 3).nonlinearResidual_hasFDerivAt_zero

example : Data.Certificate (complexData 3) (by norm_num) :=
  (complexData 3).certificate (by norm_num)

#print axioms LiuWang2025SemilinearWaveBanachAlgebraNemytskii.coefficientMultilinear_apply_const
#print axioms LiuWang2025SemilinearWaveBanachAlgebraNemytskii.coefficientMultilinear_norm_apply_le
#print axioms LiuWang2025SemilinearWaveBanachAlgebraNemytskii.coefficientMultilinear_permutationInvariant
#print axioms LiuWang2025SemilinearWaveBanachAlgebraNemytskii.Data.nonlinearResidual_apply
#print axioms LiuWang2025SemilinearWaveBanachAlgebraNemytskii.Data.nonlinearResidual_contDiff
#print axioms LiuWang2025SemilinearWaveBanachAlgebraNemytskii.Data.nonlinearResidual_hasFDerivAt_zero
#print axioms LiuWang2025SemilinearWaveBanachAlgebraNemytskii.Data.eventually_residual_solutionMap_eq_zero
#print axioms LiuWang2025SemilinearWaveBanachAlgebraNemytskii.Data.linearResidual_fderiv_solutionMap_zero
#print axioms LiuWang2025SemilinearWaveBanachAlgebraNemytskii.Data.certificate
#print axioms LiuWang2025SemilinearWaveBanachAlgebraNemytskii.ComparisonData.toGeneratedCubicComparisonData
#print axioms LiuWang2025SemilinearWaveBanachAlgebraNemytskii.ComparisonData.generatedThirdOrderCertificate

end LiuWangBanachAlgebraNemytskiiRegression
