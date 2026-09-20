import LiuWang.LiuWang2025SemilinearWaveVerification

noncomputable section

open LiuWang2025SemilinearWaveContractionRadius
open LiuWang2025SemilinearWaveBanachBall
open LiuWang2025SemilinearWaveVerification

namespace LiuWangContractionRadiusRegression

example {C K T rho : Real} (hC : 0 < C) (hrho : 0 < rho)
    (hrhoSmall : rho < stateRadiusCeiling C K T) :
    ContractionRadiusCertificate C K T rho :=
  contractionRadiusVerificationBundle hC hrho hrhoSmall

example : boundaryDataRadius 1 0 0 (1 / 4) = (1 / 8 : Real) := by
  norm_num [boundaryDataRadius]

example : stateRadiusCeiling 1 0 0 = (1 / 3 : Real) := by
  norm_num [stateRadiusCeiling]

-- The strict self-map estimate closes below the explicit threshold.
example :
    1 * (boundaryDataRadius 1 0 0 (1 / 4) +
      boundaryDataRadius 1 0 0 (1 / 4) * (1 / 4) + (1 / 4) ^ 2) *
        Real.exp (0 * 0) < (1 / 4 : Real) := by
  norm_num [boundaryDataRadius]

/-- A concrete complete-space regression for the full Banach-ball handoff. -/
def zeroPicardMap : Real → Real := fun _ => 0

def zeroPicardEstimates : PicardEstimates 1 0 0 (1 / 4) zeroPicardMap where
  selfMapBound := by
    intro x hx
    norm_num [zeroPicardMap, selfMapBudget, boundaryDataRadius]
  differenceBound := by
    intro x y hx hy
    simp [zeroPicardMap, contractionFactor, boundaryDataRadius]
    positivity

example :
    ∃ u : Real,
      ‖u‖ ≤ (1 / 4 : Real) ∧
      Function.IsFixedPt zeroPicardMap u ∧
      (∀ v : Real, ‖v‖ ≤ (1 / 4 : Real) →
        Function.IsFixedPt zeroPicardMap v → v = u) ∧
      (∀ x : Real, ‖x‖ ≤ (1 / 4 : Real) →
        Filter.Tendsto (fun n : Nat => zeroPicardMap^[n] x)
          Filter.atTop (nhds u)) := by
  exact exists_unique_fixedPoint_and_picard_converges
    (C := 1) (K := 0) (T := 0) (rho := 1 / 4)
    (map := zeroPicardMap) (by norm_num) (by norm_num)
    (by norm_num [stateRadiusCeiling]) zeroPicardEstimates

-- At the ceiling, the same self-map expression uses the entire state budget.
example :
    1 * (boundaryDataRadius 1 0 0 (1 / 3) +
      boundaryDataRadius 1 0 0 (1 / 3) * (1 / 3) + (1 / 3) ^ 2) *
        Real.exp (0 * 0) = (1 / 3 : Real) := by
  norm_num [boundaryDataRadius]

#print axioms LiuWang2025SemilinearWaveContractionRadius.boundary_contribution_eq_half
#print axioms LiuWang2025SemilinearWaveContractionRadius.selfMap_inequality
#print axioms LiuWang2025SemilinearWaveContractionRadius.contraction_inequality
#print axioms LiuWang2025SemilinearWaveContractionRadius.contractionRadiusCertificate
#print axioms LiuWang2025SemilinearWaveBanachBall.mapsTo_stateBall
#print axioms LiuWang2025SemilinearWaveBanachBall.restrictedMap_contractingWith
#print axioms LiuWang2025SemilinearWaveBanachBall.exists_unique_fixedPoint_and_picard_converges
#print axioms LiuWang2025SemilinearWaveBanachBall.banachBallCertificate
#print axioms LiuWang2025SemilinearWaveVerification.contractionRadiusVerificationBundle
#print axioms LiuWang2025SemilinearWaveVerification.section2BanachBallVerificationBundle

end LiuWangContractionRadiusRegression
