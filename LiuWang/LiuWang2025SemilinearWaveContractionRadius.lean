import Mathlib.Analysis.SpecialFunctions.Exp

/-! # Explicit small-data radius for the Liu--Wang semilinear wave map

Section 2 of Liu--Wang chooses the boundary-data size

`epsilon0 = exp (-K*T) * rho0 / (2*C)`

and then shrinks `rho0` so that the solution operator maps the state ball to
itself and is a contraction.  This file supplies one explicit radius that
simultaneously closes both scalar inequalities.  The PDE energy estimate with
constants `C` and `K` remains the source-facing analytic input.
-/

noncomputable section

namespace LiuWang2025SemilinearWaveContractionRadius

/-- The boundary-data size used in the paper after fixing a state radius. -/
def boundaryDataRadius (C K T rho : Real) : Real :=
  Real.exp (-K * T) * rho / (2 * C)

/-- An explicit sufficient ceiling for the state radius. -/
def stateRadiusCeiling (C K T : Real) : Real :=
  (1 + 2 * C * Real.exp (K * T))⁻¹

theorem stateRadiusCeiling_pos {C K T : Real} (hC : 0 < C) :
    0 < stateRadiusCeiling C K T := by
  rw [stateRadiusCeiling, inv_pos]
  positivity

theorem boundaryDataRadius_pos {C K T rho : Real} (hC : 0 < C) (hrho : 0 < rho) :
    0 < boundaryDataRadius C K T rho := by
  rw [boundaryDataRadius]
  positivity

/-- The source contribution uses exactly half of the state-radius budget. -/
theorem boundary_contribution_eq_half {C K T rho : Real} (hC : 0 < C) :
    C * boundaryDataRadius C K T rho * Real.exp (K * T) = rho / 2 := by
  have hC0 : C ≠ 0 := ne_of_gt hC
  rw [boundaryDataRadius]
  field_simp
  calc
    Real.exp (-(K * T)) * rho * Real.exp (K * T) =
        rho * (Real.exp (-(K * T)) * Real.exp (K * T)) := by ring
    _ = rho * Real.exp (-(K * T) + K * T) := by rw [Real.exp_add]
    _ = rho := by simp

/-- The explicit ceiling closes the paper's ball-invariance estimate (2.5). -/
theorem selfMap_inequality {C K T rho : Real} (hC : 0 < C) (hrho : 0 < rho)
    (hrhoSmall : rho < stateRadiusCeiling C K T) :
    C * (boundaryDataRadius C K T rho +
        boundaryDataRadius C K T rho * rho + rho ^ 2) * Real.exp (K * T) < rho := by
  have hE : 0 < Real.exp (K * T) := Real.exp_pos _
  have hden : 0 < 1 + 2 * C * Real.exp (K * T) := by positivity
  have hmul : rho * (1 + 2 * C * Real.exp (K * T)) < 1 := by
    rw [stateRadiusCeiling, inv_eq_one_div] at hrhoSmall
    exact (lt_div_iff₀ hden).mp hrhoSmall
  have hbudget : rho * (1 / 2 + C * Real.exp (K * T)) < 1 / 2 := by
    nlinarith [hmul]
  calc
    C * (boundaryDataRadius C K T rho +
        boundaryDataRadius C K T rho * rho + rho ^ 2) * Real.exp (K * T)
        = (C * boundaryDataRadius C K T rho * Real.exp (K * T)) +
            (C * boundaryDataRadius C K T rho * Real.exp (K * T)) * rho +
            C * Real.exp (K * T) * rho ^ 2 := by ring
    _ = rho / 2 + (rho / 2) * rho + C * Real.exp (K * T) * rho ^ 2 := by
      rw [boundary_contribution_eq_half hC]
    _ = rho / 2 + rho ^ 2 * (1 / 2 + C * Real.exp (K * T)) := by ring
    _ < rho / 2 + rho / 2 := by
      gcongr
      calc
        rho ^ 2 * (1 / 2 + C * Real.exp (K * T))
            = rho * (rho * (1 / 2 + C * Real.exp (K * T))) := by ring
        _ < rho * (1 / 2) := by gcongr
        _ = rho / 2 := by ring
    _ = rho := by ring

/-- The same radius also makes the solution map a strict contraction. -/
theorem contraction_inequality {C K T rho : Real} (hC : 0 < C)
    (hrhoSmall : rho < stateRadiusCeiling C K T) :
    C * (boundaryDataRadius C K T rho + rho) * Real.exp (K * T) < 1 := by
  have hden : 0 < 1 + 2 * C * Real.exp (K * T) := by positivity
  have hmul : rho * (1 + 2 * C * Real.exp (K * T)) < 1 := by
    rw [stateRadiusCeiling, inv_eq_one_div] at hrhoSmall
    exact (lt_div_iff₀ hden).mp hrhoSmall
  have hbudget : rho * (1 / 2 + C * Real.exp (K * T)) < 1 / 2 := by
    nlinarith [hmul]
  calc
    C * (boundaryDataRadius C K T rho + rho) * Real.exp (K * T)
        = rho * (1 / 2 + C * Real.exp (K * T)) := by
          rw [mul_add, add_mul, boundary_contribution_eq_half hC]
          ring
    _ < 1 / 2 := hbudget
    _ < 1 := by norm_num

structure ContractionRadiusCertificate (C K T rho : Real) : Prop where
  sourceRadiusPositive : 0 < boundaryDataRadius C K T rho
  selfMap : C * (boundaryDataRadius C K T rho +
    boundaryDataRadius C K T rho * rho + rho ^ 2) * Real.exp (K * T) < rho
  strictContraction :
    C * (boundaryDataRadius C K T rho + rho) * Real.exp (K * T) < 1

def contractionRadiusCertificate {C K T rho : Real} (hC : 0 < C) (hrho : 0 < rho)
    (hrhoSmall : rho < stateRadiusCeiling C K T) :
    ContractionRadiusCertificate C K T rho where
  sourceRadiusPositive := boundaryDataRadius_pos hC hrho
  selfMap := selfMap_inequality hC hrho hrhoSmall
  strictContraction := contraction_inequality hC hrhoSmall

end LiuWang2025SemilinearWaveContractionRadius
