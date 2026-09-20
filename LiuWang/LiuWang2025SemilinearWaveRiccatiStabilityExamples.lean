import LiuWang.LiuWang2025SemilinearWaveRiccatiStability
import LiuWang.LiuWang2025SemilinearWaveRiccatiExistenceExamples

/-!
# Exact witnesses for the quantitative Riccati estimates

The initial phase is `i I` in two transverse dimensions. We compare the
generated nonconstant flow for `C=I` against the constant flow for `C=0`,
and separately certify the constant phase as an approximate solution of
the first system using its exact, nonzero residual.
-/

noncomputable section

open Matrix Set
open scoped Matrix.Norms.L2Operator

namespace LiuWang2025SemilinearWaveRiccatiStabilityExamples

open LiuWang2025SemilinearWaveRiccatiExistence
open LiuWang2025SemilinearWaveRiccatiExistenceExamples
open LiuWang2025SemilinearWaveRiccatiFlow
open LiuWang2025SemilinearWaveRiccatiPhase
open LiuWang2025SemilinearWaveRiccatiQuantitative
open LiuWang2025SemilinearWaveRiccatiStability

theorem initialPhase_coercive : RealCoercive (hermitianImaginaryPart initialPhase) 1 := by
  rw [initialPhase_imaginaryPart]
  intro x
  have hsum : 0 ≤ ∑ i : Fin 2, Complex.normSq (x i) :=
    Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _
  have hnorm : ‖x‖ ≤ Real.sqrt (∑ i : Fin 2, Complex.normSq (x i)) := by
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
    intro i
    apply (Real.le_sqrt (norm_nonneg _) hsum).mpr
    rw [Complex.sq_norm]
    exact Finset.single_le_sum (fun j _ => Complex.normSq_nonneg _) (Finset.mem_univ i)
  have hsq := (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mpr hnorm
  rw [Real.sq_sqrt hsum] at hsq
  simpa [complexQuadratic, dotProduct, Complex.normSq_apply, Complex.mul_re] using hsq

def bounds : Bounds coefficients where
  rate := 1
  rate_nonneg := by norm_num
  C_bound := fun _ _ => by simp [coefficients]
  D_bound := fun _ _ => by simp [coefficients]
  initialCoercivity := 1
  initialCoercivity_pos := by norm_num
  H0_coercive := initialPhase_coercive

def zeroCoefficients : Coefficients (Fin 2) :=
  { coefficients with
    C := fun _ => 0
    C_continuous := continuousOn_const
    C_symmetric := fun _ _ => by simp
    C_hermitian := fun _ _ => by simp }

def zeroBounds : Bounds zeroCoefficients where
  rate := 0
  rate_nonneg := le_rfl
  C_bound := fun _ _ => by simp [zeroCoefficients]
  D_bound := fun _ _ => by simp [zeroCoefficients, coefficients]
  initialCoercivity := 1
  initialCoercivity_pos := by norm_num
  H0_coercive := initialPhase_coercive

def comparison : Comparison bounds zeroBounds where
  same_start := rfl
  same_end := rfl
  coefficientError := 1
  coefficientError_nonneg := by norm_num
  forcingError := 0
  forcingError_nonneg := le_rfl
  C_difference := fun _ _ => by simp [zeroCoefficients, coefficients]
  D_difference := fun _ _ => by simp [zeroCoefficients, coefficients]

theorem zero_solution_constant {t : Real} (ht : t ∈ Icc (-1 : Real) 2) :
    zeroCoefficients.solution t = (1, initialPhase) := by
  have h := zeroCoefficients.solution_unique (fun _ => (1, initialPhase)) continuousOn_const
    (fun s _ => by simpa [Coefficients.vectorField, zeroCoefficients, coefficients] using
      hasDerivAt_const s ((1 : Mat (Fin 2)), initialPhase)) rfl
  exact (h ht).symm

theorem zero_phase_constant {t : Real} (ht : t ∈ Icc (0 : Real) 1) :
    zeroCoefficients.toRiccatiFlow.H t = initialPhase := by
  change (zeroCoefficients.solution t).2 * (zeroCoefficients.solution t).1⁻¹ = _
  rw [zero_solution_constant (show t ∈ Icc (-1 : Real) 2 by
    constructor <;> linarith [ht.1, ht.2])]
  simp

theorem perturbed_phase_bound {t : Real} (ht : t ∈ Icc (0 : Real) 1) :
    dist (coefficients.toRiccatiFlow.H t) initialPhase ≤
      gronwallBound comparison.initialError comparison.growthRate comparison.residualError |t| := by
  have h := comparison.phase_distance_bound
    (show t ∈ uIcc coefficients.startTime coefficients.endTime by simpa [coefficients] using ht)
  rw [zero_phase_constant ht] at h
  simpa [coefficients] using h

theorem constant_phase_residual (t : Real) :
    ‖(0 : Mat (Fin 2)) + initialPhase * coefficients.C t * initialPhase + coefficients.D t‖ = 1 := by
  have hmul : initialPhase * initialPhase = -(1 : Mat (Fin 2)) := by
    simp [initialPhase, smul_smul]
  simp [coefficients, hmul]

theorem constant_phase_certified_error {t : Real} (ht : t ∈ Icc (0 : Real) 1) :
    dist initialPhase (coefficients.toRiccatiFlow.H t) ≤
      gronwallBound 0 ((‖initialPhase‖ + bounds.phaseBound) * bounds.rate) 1 |t| := by
  have h := approximate_phase_error_bound bounds (fun _ => initialPhase) (fun _ => 0)
    (norm_nonneg _) (fun s _ => hasDerivAt_const s initialPhase) (fun _ _ => le_rfl)
    (fun s _ => (constant_phase_residual s).le)
    (by simp [coefficients] : dist initialPhase coefficients.H0 ≤ 0)
    (show t ∈ uIcc coefficients.startTime coefficients.endTime by simpa [coefficients] using ht)
  simpa [coefficients] using h

end LiuWang2025SemilinearWaveRiccatiStabilityExamples
