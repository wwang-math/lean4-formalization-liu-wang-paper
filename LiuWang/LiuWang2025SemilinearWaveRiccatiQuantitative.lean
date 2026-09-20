import LiuWang.LiuWang2025SemilinearWaveRiccatiExistence
import LiuWang.CompactIntervalODEEstimates

/-!
# Coefficient-dependent bounds for the generated Liu--Wang Riccati flow

The constants below depend on coefficient bounds, interval length, the
initial Hessian, and its coercivity. They do not assume a bound for an
already constructed solution. Matrix norms are Euclidean operator norms;
vector norms are the existing Pi norms, with their conversion recorded.
These are forward-construction estimates, not inverse-data stability.
-/

noncomputable section

open Matrix Set
open scoped Matrix.Norms.L2Operator

namespace LiuWang2025SemilinearWaveRiccatiQuantitative

open LiuWang2025SemilinearWaveRiccatiExistence
open LiuWang2025SemilinearWaveRiccatiFlow
open LiuWang2025SemilinearWaveRiccatiPhase

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
theorem norm_dotProduct_le (x y : n → Complex) :
    ‖x ⬝ᵥ y‖ ≤ Fintype.card n * ‖x‖ * ‖y‖ := by
  calc
    _ ≤ ∑ i, ‖x i * y i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : n, ‖x‖ * ‖y‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_mul]
      exact mul_le_mul (norm_le_pi_norm x i) (norm_le_pi_norm y i)
        (norm_nonneg _) (norm_nonneg _)
    _ = Fintype.card n * ‖x‖ * ‖y‖ := by simp [mul_assoc]

omit [DecidableEq n] in
theorem quadratic_adjoint_product (Y Z : Mat n) (x : n → Complex) :
    complexQuadratic (Yᴴ * Z) x = star (Y *ᵥ x) ⬝ᵥ (Z *ᵥ x) := by
  unfold complexQuadratic
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec]

theorem normalizedWronskian_quadratic_bound (Y Z : Mat n) (x : n → Complex) :
    (complexQuadratic ((-Complex.I / 2) • (Yᴴ * Z - Zᴴ * Y)) x).re ≤
      Fintype.card n * ‖Y *ᵥ x‖ * ‖Z *ᵥ x‖ := by
  apply (Complex.re_le_norm _).trans
  rw [complexQuadratic_smul, norm_mul, complexQuadratic_sub]
  have hscalar : ‖(-Complex.I / 2 : Complex)‖ = (1 / 2 : Real) := by norm_num
  rw [hscalar, quadratic_adjoint_product, quadratic_adjoint_product]
  apply (mul_le_mul_of_nonneg_left (norm_sub_le _ _) (by positivity : (0 : Real) ≤ 1 / 2)).trans
  have hYZ := norm_dotProduct_le (star (Y *ᵥ x)) (Z *ᵥ x)
  have hZY := norm_dotProduct_le (star (Z *ᵥ x)) (Y *ᵥ x)
  simp only [norm_star] at hYZ hZY
  nlinarith

/-- Quantitative no-caustic estimate from the conserved Wronskian. -/
theorem inverse_action_bound
    (flow : RiccatiFlow n) {t c0 M : Real}
    (ht : t ∈ uIcc flow.startTime flow.endTime)
    (hc0 : 0 < c0) (hM : 0 ≤ M)
    (hcoercive : RealCoercive (hermitianImaginaryPart flow.H0) c0)
    (hZ : ∀ x : n → Complex, ‖flow.Z t *ᵥ x‖ ≤ M * ‖x‖)
    (v : n → Complex) :
    ‖(flow.Y t)⁻¹ *ᵥ v‖ ≤ (Fintype.card n * M / c0) * ‖v‖ := by
  let x := (flow.Y t)⁻¹ *ᵥ v
  have hrecover : flow.Y t *ᵥ x = v := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (flow.YdetUnit t ht), one_mulVec]
  have hq := hcoercive x
  rw [← flow.normalizedHermitianWronskian ht] at hq
  have hbound := hq.trans (normalizedWronskian_quadratic_bound (flow.Y t) (flow.Z t) x)
  rw [hrecover] at hbound
  have hscaled := mul_le_mul_of_nonneg_left (hZ x)
    (show 0 ≤ (Fintype.card n : Real) * ‖v‖ by positivity)
  have hineq : (c0 * ‖x‖) * ‖x‖ ≤
      ((Fintype.card n : Real) * M * ‖v‖) * ‖x‖ := by
    nlinarith [hbound.trans hscaled]
  by_cases hx : ‖x‖ = 0
  · change ‖x‖ ≤ _
    rw [hx]
    positivity
  · have hpos : 0 < ‖x‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hx)
    have hcancel := (mul_le_mul_iff_left₀ hpos).mp hineq
    change ‖x‖ ≤ _
    calc
      ‖x‖ ≤ (Fintype.card n * M * ‖v‖) / c0 :=
        (le_div_iff₀ hc0).mpr (by simpa only [mul_comm c0] using hcancel)
      _ = (Fintype.card n * M / c0) * ‖v‖ := by ring

/-- Only coefficient bounds and initial coercivity are additional inputs. -/
structure Bounds (d : Coefficients n) where
  rate : Real
  rate_nonneg : 0 ≤ rate
  C_bound : ∀ t ∈ uIcc d.startTime d.endTime, ‖d.C t‖ ≤ rate
  D_bound : ∀ t ∈ uIcc d.startTime d.endTime, ‖d.D t‖ ≤ rate
  initialCoercivity : Real
  initialCoercivity_pos : 0 < initialCoercivity
  H0_coercive : RealCoercive (hermitianImaginaryPart d.H0) initialCoercivity

namespace Bounds

variable {d : Coefficients n} (b : Bounds d)

def duration (_b : Bounds d) : Real := |d.endTime - d.startTime|

def initialSize (_b : Bounds d) : Real := max ‖(1 : Mat n)‖ ‖d.H0‖

def stateBound : Real := b.initialSize * Real.exp (b.rate * b.duration)

theorem stateBound_nonneg : 0 ≤ b.stateBound := by
  unfold stateBound initialSize
  positivity

theorem solution_pointwise_bound {t : Real} (ht : t ∈ uIcc d.startTime d.endTime) :
    ‖d.solution t‖ ≤ b.initialSize * Real.exp (b.rate * |t - d.startTime|) := by
  apply CompactIntervalODEEstimates.norm_le_exp_uIcc
    (fun s hs => d.solution_hasDerivAt (d.interval_subset (uIcc_subset_uIcc_left ht hs)))
  · rw [d.solution_initial]
    exact le_rfl
  · intro s hs
    have hs' := uIcc_subset_uIcc_left ht hs
    exact (hamiltonianOperator_norm_apply_le (d.C s) (d.D s) (d.solution s)).trans
      (mul_le_mul_of_nonneg_right (max_le (b.C_bound s hs') (b.D_bound s hs'))
        (norm_nonneg _))

theorem solution_bound {t : Real} (ht : t ∈ uIcc d.startTime d.endTime) :
    ‖d.solution t‖ ≤ b.stateBound := by
  apply (b.solution_pointwise_bound ht).trans
  unfold stateBound duration
  apply mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (abs_sub_left_of_mem_uIcc ht) b.rate_nonneg))
  exact le_max_of_le_left (norm_nonneg _)

def actionBound : Real := ‖(vectorActionEquiv (n := n)).toContinuousLinearMap‖ * b.stateBound + 1

theorem actionBound_pos : 0 < b.actionBound := by
  unfold actionBound
  have := b.stateBound_nonneg
  positivity

theorem action_bound {t : Real} (ht : t ∈ uIcc d.startTime d.endTime)
    (A : Mat n) (hA : ‖A‖ ≤ ‖d.solution t‖) (x : n → Complex) :
    ‖A *ᵥ x‖ ≤ b.actionBound * ‖x‖ := by
  apply ((vectorActionEquiv A).le_opNorm x).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  have ha := (vectorActionEquiv (n := n)).toContinuousLinearMap.le_opNorm A
  have hg := mul_le_mul_of_nonneg_left (hA.trans (b.solution_bound ht))
    (norm_nonneg (vectorActionEquiv (n := n)).toContinuousLinearMap)
  exact (ha.trans hg).trans (le_add_of_nonneg_right zero_le_one)

theorem Y_action_bound {t : Real} (ht : t ∈ uIcc d.startTime d.endTime) (x : n → Complex) :
    ‖d.toRiccatiFlow.Y t *ᵥ x‖ ≤ b.actionBound * ‖x‖ :=
  b.action_bound ht _ (norm_fst_le _) x

theorem Z_action_bound {t : Real} (ht : t ∈ uIcc d.startTime d.endTime) (x : n → Complex) :
    ‖d.toRiccatiFlow.Z t *ᵥ x‖ ≤ b.actionBound * ‖x‖ :=
  b.action_bound ht _ (norm_snd_le _) x

def inverseBound : Real :=
  ‖(vectorActionEquiv (n := n)).symm.toContinuousLinearMap‖ *
    (Fintype.card n * b.actionBound / b.initialCoercivity)

theorem inverseBound_nonneg : 0 ≤ b.inverseBound := by
  unfold inverseBound
  have := b.actionBound_pos
  have := b.initialCoercivity_pos
  positivity

theorem Y_inverse_bound {t : Real} (ht : t ∈ uIcc d.startTime d.endTime) :
    ‖(d.toRiccatiFlow.Y t)⁻¹‖ ≤ b.inverseBound := by
  have hinv := inverse_action_bound d.toRiccatiFlow ht b.initialCoercivity_pos
    b.actionBound_pos.le b.H0_coercive (b.Z_action_bound ht)
  have hop : ‖vectorActionEquiv ((d.toRiccatiFlow.Y t)⁻¹)‖ ≤
      Fintype.card n * b.actionBound / b.initialCoercivity :=
    ContinuousLinearMap.opNorm_le_bound _ (by
      have := b.actionBound_pos
      have := b.initialCoercivity_pos
      positivity) hinv
  have h := (vectorActionEquiv (n := n)).symm.toContinuousLinearMap.le_opNorm
    (vectorActionEquiv ((d.toRiccatiFlow.Y t)⁻¹))
  change ‖(vectorActionEquiv (n := n)).symm
    (vectorActionEquiv ((d.toRiccatiFlow.Y t)⁻¹))‖ ≤ _ at h
  simp only [ContinuousLinearEquiv.symm_apply_apply] at h
  exact h.trans (mul_le_mul_of_nonneg_left hop (norm_nonneg _))

def phaseBound : Real := b.stateBound * b.inverseBound

theorem phaseBound_nonneg : 0 ≤ b.phaseBound :=
  mul_nonneg b.stateBound_nonneg b.inverseBound_nonneg

theorem H_bound {t : Real} (ht : t ∈ uIcc d.startTime d.endTime) :
    ‖d.toRiccatiFlow.H t‖ ≤ b.phaseBound :=
  (norm_mul_le _ _).trans (mul_le_mul
    ((norm_snd_le (d.solution t)).trans (b.solution_bound ht))
    (b.Y_inverse_bound ht) (norm_nonneg _) b.stateBound_nonneg)

def toUniformRiccatiFlow : UniformRiccatiFlow n where
  toRiccatiFlow := d.toRiccatiFlow
  initialCoercivity := b.initialCoercivity
  initialCoercivity_pos := b.initialCoercivity_pos
  H0_coercive := b.H0_coercive
  YActionBound := b.actionBound
  YActionBound_pos := b.actionBound_pos
  Y_mulVec_bound := fun _ ht x => b.Y_action_bound ht x

theorem phase_coercivity {t : Real} (ht : t ∈ uIcc d.startTime d.endTime) (x : n → Complex) :
    (b.initialCoercivity / b.actionBound ^ 2) * ‖x‖ ^ 2 ≤
      (complexQuadratic (d.toRiccatiFlow.H t) x).im :=
  b.toUniformRiccatiFlow.phase_uniform_coercivity ht x

end Bounds
end LiuWang2025SemilinearWaveRiccatiQuantitative
