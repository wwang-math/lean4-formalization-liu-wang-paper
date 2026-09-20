import LiuWang.LiuWang2025SemilinearWaveRiccatiExistence

/-!
# Nonconstant witness for the generated Liu--Wang Riccati flow

The constant coefficients `C=1`, `D=0`, `H0=i*1` yield
`Y(t)=1+t*(i*1)`, `Z(t)=i*1`. Uniqueness identifies the abstractly constructed
path with this explicit solution. The witness uses two transverse coordinates
and does not represent the paper's full Fermi metric or reflected beams.
-/

noncomputable section

open Matrix Set
open scoped Matrix.Norms.L2Operator

namespace LiuWang2025SemilinearWaveRiccatiExistenceExamples

open LiuWang2025SemilinearWaveRiccatiExistence
open LiuWang2025SemilinearWaveRiccatiPhase

def initialPhase : Mat (Fin 2) := Complex.I • 1

theorem initialPhase_imaginaryPart : hermitianImaginaryPart initialPhase = 1 := by
  ext i j
  by_cases hij : i = j
  · subst j
    norm_num [initialPhase, hermitianImaginaryPart, Matrix.conjTranspose, Complex.ext_iff]
  · simp [initialPhase, hermitianImaginaryPart, Matrix.conjTranspose, hij]

theorem identity_positive : ComplexPosDef (1 : Mat (Fin 2)) := by
  refine ⟨by simp, fun {x} hx => ?_⟩
  have hx' : ∃ i, x i ≠ 0 := by
    by_contra h
    push Not at h
    exact hx (funext h)
  obtain ⟨i, hi⟩ := hx'
  have hsum : 0 < ∑ j : Fin 2, Complex.normSq (x j) :=
    Finset.sum_pos' (fun j _ => Complex.normSq_nonneg (x j))
      ⟨i, Finset.mem_univ i, Complex.normSq_pos.mpr hi⟩
  simpa [complexQuadratic, dotProduct, Complex.normSq_apply, Complex.mul_re] using hsum

def coefficients : Coefficients (Fin 2) where
  lower := -1
  upper := 2
  startTime := 0
  endTime := 1
  start_mem := by norm_num
  end_mem := by norm_num
  C := fun _ => 1
  D := fun _ => 0
  C_continuous := continuousOn_const
  D_continuous := continuousOn_const
  C_symmetric := fun _ _ => by simp
  D_symmetric := fun _ _ => by simp
  C_hermitian := fun _ _ => by simp
  D_hermitian := fun _ _ => by simp
  H0 := initialPhase
  H0_symmetric := by simp [initialPhase, Matrix.IsSymm]
  H0_imaginaryPositive := by rw [initialPhase_imaginaryPart]; exact identity_positive

def explicitSolution (t : Real) : State (Fin 2) := (1 + t • initialPhase, initialPhase)

theorem explicitSolution_hasDerivAt (t : Real) :
    HasDerivAt explicitSolution (coefficients.vectorField t (explicitSolution t)) t := by
  convert (((hasDerivAt_id t).smul_const initialPhase).const_add 1).prodMk
    (hasDerivAt_const t initialPhase) using 1 <;>
    simp [explicitSolution, Coefficients.vectorField, coefficients]

theorem generated_eq_explicit {t : Real} (ht : t ∈ Icc (-1 : Real) 2) :
    coefficients.solution t = explicitSolution t := by
  have h := coefficients.solution_unique explicitSolution
    (HasDerivAt.continuousOn (fun t _ => explicitSolution_hasDerivAt t))
    (fun t _ => explicitSolution_hasDerivAt t) (by
      change (1 + (0 : Real) • initialPhase, initialPhase) = (1, initialPhase)
      apply Prod.ext
      · ext i j
        simp [Matrix.add_apply, Matrix.smul_apply, Complex.real_smul]
      · rfl)
  exact (h ht).symm

theorem generated_Y_at_one : coefficients.toRiccatiFlow.Y 1 = 1 + initialPhase := by
  change (coefficients.solution 1).1 = _
  rw [generated_eq_explicit (by norm_num)]
  change 1 + (1 : Real) • initialPhase = 1 + initialPhase
  ext i j
  simp [Matrix.add_apply, Matrix.smul_apply, Complex.real_smul]

theorem generated_Y_nonconstant :
    coefficients.toRiccatiFlow.Y 1 ≠ coefficients.toRiccatiFlow.Y 0 := by
  rw [generated_Y_at_one]
  change 1 + initialPhase ≠ (coefficients.solution 0).1
  rw [generated_eq_explicit (by norm_num)]
  intro h
  have h00 := congrArg (fun A : Mat (Fin 2) => (A 0 0).im) h
  norm_num [explicitSolution, initialPhase] at h00

/-- With a real, nonpositive-imaginary initial phase, the same linear
coefficient system admits a singular `Y`. Positivity is essential here. -/
def realPhaseSolution (t : Real) : State (Fin 2) := (1 - t • (1 : Mat (Fin 2)), -1)

theorem realPhaseSolution_hasDerivAt (t : Real) :
    HasDerivAt realPhaseSolution
      (hamiltonianOperator (1 : Mat (Fin 2)) 0 (realPhaseSolution t)) t := by
  convert ((hasDerivAt_const t (1 : Mat (Fin 2))).sub
    ((hasDerivAt_id t).smul_const (1 : Mat (Fin 2)))).prodMk
      (hasDerivAt_const t (-1 : Mat (Fin 2))) using 1 <;>
    simp [realPhaseSolution]

theorem realPhase_Y_at_one : (realPhaseSolution 1).1 = 0 := by
  ext i j
  simp [realPhaseSolution, Matrix.sub_apply, Matrix.smul_apply, Complex.real_smul]

theorem dropping_positivity_allows_singular_Y : ¬ IsUnit (realPhaseSolution 1).1 := by
  rw [realPhase_Y_at_one]
  exact not_isUnit_zero

end LiuWang2025SemilinearWaveRiccatiExistenceExamples
