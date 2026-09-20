import LiuWang.LiuWang2025SemilinearWaveRiccatiQuantitative

/-!
# Stability and residual certification for the Riccati construction

The generated a priori bounds turn coefficient and initial-phase errors into
an explicit Gronwall bound. This concerns the forward Gaussian-beam phase,
not recovery from noisy boundary measurements. A separate residual theorem
requires a proved continuous-time defect bound, not sampled residuals.
-/

noncomputable section

set_option maxHeartbeats 800000

open Matrix Set
open scoped Matrix.Norms.L2Operator

namespace LiuWang2025SemilinearWaveRiccatiStability

open LiuWang2025SemilinearWaveRiccatiExistence
open LiuWang2025SemilinearWaveRiccatiQuantitative

variable {n : Type*} [Fintype n] [DecidableEq n]

def rhs (C D X : Mat n) : Mat n := -(X * C * X) - D

theorem rhs_coefficient_difference_bound (C1 D1 C2 D2 X : Mat n) :
    dist (rhs C1 D1 X) (rhs C2 D2 X) ≤
      ‖X‖ ^ 2 * ‖C1 - C2‖ + ‖D1 - D2‖ := by
  rw [dist_eq_norm]
  have h : rhs C1 D1 X - rhs C2 D2 X = -(X * (C1 - C2) * X) - (D1 - D2) := by
    unfold rhs
    noncomm_ring
  rw [h]
  apply (norm_sub_le _ _).trans
  rw [norm_neg]
  apply add_le_add _ le_rfl
  calc
    ‖X * (C1 - C2) * X‖ ≤ (‖X‖ * ‖C1 - C2‖) * ‖X‖ :=
      (norm_mul_le _ _).trans
        (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ = ‖X‖ ^ 2 * ‖C1 - C2‖ := by ring

theorem rhs_joint_difference_bound (C1 D1 C2 D2 X Y : Mat n) :
    dist (rhs C1 D1 X) (rhs C2 D2 Y) ≤
      (‖X‖ + ‖Y‖) * ‖C1‖ * dist X Y +
        (‖Y‖ ^ 2 * ‖C1 - C2‖ + ‖D1 - D2‖) :=
  (dist_triangle _ (rhs C1 D1 Y) _).trans
    (add_le_add (riccati_rhs_difference_bound C1 D1 X Y)
      (rhs_coefficient_difference_bound C1 D1 C2 D2 Y))

structure Comparison {d1 d2 : Coefficients n} (b1 : Bounds d1) (b2 : Bounds d2) where
  same_start : d1.startTime = d2.startTime
  same_end : d1.endTime = d2.endTime
  coefficientError : Real
  coefficientError_nonneg : 0 ≤ coefficientError
  forcingError : Real
  forcingError_nonneg : 0 ≤ forcingError
  C_difference : ∀ t ∈ uIcc d1.startTime d1.endTime,
    ‖d1.C t - d2.C t‖ ≤ coefficientError
  D_difference : ∀ t ∈ uIcc d1.startTime d1.endTime,
    ‖d1.D t - d2.D t‖ ≤ forcingError

namespace Comparison

variable {d1 d2 : Coefficients n} {b1 : Bounds d1} {b2 : Bounds d2}
variable (p : Comparison b1 b2)

include p

def initialError (_p : Comparison b1 b2) : Real := ‖d1.H0 - d2.H0‖

def growthRate (_p : Comparison b1 b2) : Real := (b1.phaseBound + b2.phaseBound) * b1.rate

def residualError : Real := b2.phaseBound ^ 2 * p.coefficientError + p.forcingError

theorem growthRate_nonneg : 0 ≤ p.growthRate :=
  mul_nonneg (add_nonneg b1.phaseBound_nonneg b2.phaseBound_nonneg) b1.rate_nonneg

theorem residualError_nonneg : 0 ≤ p.residualError :=
  add_nonneg (mul_nonneg (sq_nonneg _) p.coefficientError_nonneg) p.forcingError_nonneg

theorem right_mem {t : Real} (ht : t ∈ uIcc d1.startTime d1.endTime) :
    t ∈ uIcc d2.startTime d2.endTime := by
  simpa only [p.same_start, p.same_end] using ht

theorem derivative_difference_bound {t : Real} (ht : t ∈ uIcc d1.startTime d1.endTime) :
    dist (rhs (d1.C t) (d1.D t) (d1.toRiccatiFlow.H t))
      (rhs (d2.C t) (d2.D t) (d2.toRiccatiFlow.H t)) ≤
        p.growthRate * dist (d1.toRiccatiFlow.H t) (d2.toRiccatiFlow.H t) +
          p.residualError := by
  apply (rhs_joint_difference_bound _ _ _ _ _ _).trans
  apply add_le_add
  · apply mul_le_mul_of_nonneg_right _ dist_nonneg
    exact mul_le_mul (add_le_add (b1.H_bound ht) (b2.H_bound (p.right_mem ht)))
      (b1.C_bound t ht) (norm_nonneg _) (add_nonneg b1.phaseBound_nonneg b2.phaseBound_nonneg)
  · apply add_le_add _ (p.D_difference t ht)
    apply mul_le_mul _ (p.C_difference t ht) (norm_nonneg _) (sq_nonneg _)
    exact pow_le_pow_left₀ (norm_nonneg _) (b2.H_bound (p.right_mem ht)) 2

theorem phase_distance_bound {t : Real} (ht : t ∈ uIcc d1.startTime d1.endTime) :
    dist (d1.toRiccatiFlow.H t) (d2.toRiccatiFlow.H t) ≤
      gronwallBound p.initialError p.growthRate p.residualError |t - d1.startTime| := by
  rw [dist_eq_norm]
  apply CompactIntervalODEEstimates.norm_le_gronwallBound_uIcc
    (f := fun s => d1.toRiccatiFlow.H s - d2.toRiccatiFlow.H s)
    (a := d1.startTime) (b := t)
    (δ := p.initialError) (K := p.growthRate) (ε := p.residualError)
    (f' := fun s => rhs (d1.C s) (d1.D s) (d1.toRiccatiFlow.H s) -
      rhs (d2.C s) (d2.D s) (d2.toRiccatiFlow.H s))
  · intro s hs
    have hs' := uIcc_subset_uIcc_left ht hs
    exact (d1.generated_H_hasDerivAt hs').sub
      (d2.generated_H_hasDerivAt (p.right_mem hs'))
  · rw [d1.generated_H_initial, p.same_start, d2.generated_H_initial]
    exact le_rfl
  · intro s hs
    simpa only [dist_eq_norm] using p.derivative_difference_bound (uIcc_subset_uIcc_left ht hs)

theorem uniform_phase_distance_bound {t : Real} (ht : t ∈ uIcc d1.startTime d1.endTime) :
    dist (d1.toRiccatiFlow.H t) (d2.toRiccatiFlow.H t) ≤
      gronwallBound p.initialError p.growthRate p.residualError b1.duration :=
  (p.phase_distance_bound ht).trans
    (gronwallBound_mono (norm_nonneg _) p.residualError_nonneg p.growthRate_nonneg
      (abs_sub_left_of_mem_uIcc ht))

end Comparison

/-- A certified continuous-time residual yields a phase error bound. A
sampled numerical residual alone does not supply the hypotheses. -/
theorem approximate_phase_error_bound
    {d : Coefficients n} (b : Bounds d) (Q Q' : Real → Mat n)
    {R δ ε : Real} (hR : 0 ≤ R)
    (hQ : ∀ t ∈ uIcc d.startTime d.endTime, HasDerivAt Q (Q' t) t)
    (hsize : ∀ t ∈ uIcc d.startTime d.endTime, ‖Q t‖ ≤ R)
    (hresidual : ∀ t ∈ uIcc d.startTime d.endTime,
      ‖Q' t + Q t * d.C t * Q t + d.D t‖ ≤ ε)
    (hinitial : dist (Q d.startTime) d.H0 ≤ δ)
    {t : Real} (ht : t ∈ uIcc d.startTime d.endTime) :
    dist (Q t) (d.toRiccatiFlow.H t) ≤
      gronwallBound δ ((R + b.phaseBound) * b.rate) ε |t - d.startTime| := by
  rw [dist_eq_norm]
  apply CompactIntervalODEEstimates.norm_le_gronwallBound_uIcc
    (f := fun s => Q s - d.toRiccatiFlow.H s)
    (a := d.startTime) (b := t) (δ := δ) (K := (R + b.phaseBound) * b.rate) (ε := ε)
    (f' := fun s => Q' s - rhs (d.C s) (d.D s) (d.toRiccatiFlow.H s))
  · intro s hs
    have hs' := uIcc_subset_uIcc_left ht hs
    exact (hQ s hs').sub (d.generated_H_hasDerivAt hs')
  · simpa only [d.generated_H_initial, dist_eq_norm] using hinitial
  · intro s hs
    have hs' := uIcc_subset_uIcc_left ht hs
    have hdefect : dist (Q' s) (rhs (d.C s) (d.D s) (Q s)) ≤ ε := by
      have heq : Q' s - rhs (d.C s) (d.D s) (Q s) =
          Q' s + Q s * d.C s * Q s + d.D s := by
        unfold rhs
        abel
      rw [dist_eq_norm, heq]
      exact hresidual s hs'
    have hphase := riccati_rhs_difference_bound (d.C s) (d.D s) (Q s) (d.toRiccatiFlow.H s)
    have hcoeff : (‖Q s‖ + ‖d.toRiccatiFlow.H s‖) * ‖d.C s‖ ≤
        (R + b.phaseBound) * b.rate :=
      mul_le_mul (add_le_add (hsize s hs') (b.H_bound hs')) (b.C_bound s hs')
        (norm_nonneg _) (add_nonneg hR b.phaseBound_nonneg)
    have h := (dist_triangle (Q' s) (rhs (d.C s) (d.D s) (Q s))
      (rhs (d.C s) (d.D s) (d.toRiccatiFlow.H s))).trans
        (add_le_add hdefect (hphase.trans (mul_le_mul_of_nonneg_right hcoeff dist_nonneg)))
    simpa only [dist_eq_norm, add_comm] using h

end LiuWang2025SemilinearWaveRiccatiStability
