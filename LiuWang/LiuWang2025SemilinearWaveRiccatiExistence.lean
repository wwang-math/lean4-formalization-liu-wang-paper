import LiuWang.CompactIntervalLipschitzODE
import LiuWang.LiuWang2025SemilinearWaveRiccatiFlow
import Mathlib.Analysis.Normed.Operator.Prod

/-!
# Liu--Wang: constructing the Riccati flow from continuous coefficients

The input consists of coefficient matrices and initial phase data, not paths
`Y` and `Z` solving an ODE. A globally state-Lipschitz Hamiltonian system
generates those paths on the whole requested finite interval. Its unique
solution feeds the previously checked Wronskian, invertibility, Riccati,
positivity, and WKB results.

Coefficients are continuous on a slightly larger compact interval, so the
constructed paths have ordinary two-sided derivatives even at the requested
endpoints. Identifying these coefficients with the paper's Fermi geometry is
separate from this finite-dimensional analytic theorem.
-/

noncomputable section

set_option maxHeartbeats 800000

open Function Matrix Set
open scoped Matrix.Norms.L2Operator Topology

namespace LiuWang2025SemilinearWaveRiccatiExistence

open LiuWang2025SemilinearWaveRiccatiFlow
open LiuWang2025SemilinearWaveRiccatiPhase

variable {n : Type*} [Fintype n] [DecidableEq n]

abbrev Mat (n : Type*) := Matrix n n Complex
abbrev State (n : Type*) := Mat n × Mat n

def hamiltonianOperator (C D : Mat n) : State n →L[Real] State n :=
  (((ContinuousLinearMap.mul Real (Mat n)) C).comp
    (ContinuousLinearMap.snd Real (Mat n) (Mat n))).prod
      (-(((ContinuousLinearMap.mul Real (Mat n)) D).comp
        (ContinuousLinearMap.fst Real (Mat n) (Mat n))))

@[simp] theorem hamiltonianOperator_apply (C D : Mat n) (s : State n) :
    hamiltonianOperator C D s = (C * s.2, -(D * s.1)) := rfl

theorem hamiltonianOperator_norm_apply_le (C D : Mat n) (s : State n) :
    ‖hamiltonianOperator C D s‖ ≤ max ‖C‖ ‖D‖ * ‖s‖ := by
  simp only [hamiltonianOperator_apply, Prod.norm_def, norm_neg]
  apply max_le
  · apply (norm_mul_le C s.2).trans
    exact mul_le_mul (le_max_left _ _) (le_max_right _ _) (norm_nonneg _) (by positivity)
  · apply (norm_mul_le D s.1).trans
    exact mul_le_mul (le_max_right _ _) (le_max_left _ _) (norm_nonneg _) (by positivity)

/-- The action is bundled in the existing vector norm, not silently
identified with the matrix's Euclidean operator norm. -/
def vectorActionEquiv : Mat n ≃L[Complex] ((n → Complex) →L[Complex] (n → Complex)) :=
  ((Matrix.toLin' : Mat n ≃ₗ[Complex] ((n → Complex) →ₗ[Complex] (n → Complex))).trans
    LinearMap.toContinuousLinearMap).toContinuousLinearEquiv

@[simp] theorem vectorActionEquiv_apply (A : Mat n) (x : n → Complex) :
    vectorActionEquiv A x = A *ᵥ x := rfl

theorem riccati_rhs_difference_bound (C D X Y : Mat n) :
    dist (-(X * C * X) - D) (-(Y * C * Y) - D) ≤
      (‖X‖ + ‖Y‖) * ‖C‖ * dist X Y := by
  rw [dist_sub_right, dist_neg_neg, dist_eq_norm, dist_eq_norm]
  have hexpand : X * C * X - Y * C * Y = (X - Y) * C * X + Y * C * (X - Y) := by
    noncomm_ring
  rw [hexpand]
  calc
    _ ≤ ‖(X - Y) * C * X‖ + ‖Y * C * (X - Y)‖ := norm_add_le _ _
    _ ≤ ‖X - Y‖ * ‖C‖ * ‖X‖ + ‖Y‖ * ‖C‖ * ‖X - Y‖ := by
      exact add_le_add
        ((norm_mul_le ((X - Y) * C) X).trans
          (mul_le_mul_of_nonneg_right (norm_mul_le (X - Y) C) (norm_nonneg X)))
        ((norm_mul_le (Y * C) (X - Y)).trans
          (mul_le_mul_of_nonneg_right (norm_mul_le Y C) (norm_nonneg (X - Y))))
    _ = (‖X‖ + ‖Y‖) * ‖C‖ * ‖X - Y‖ := by ring

theorem riccati_rhs_lipschitz (C D : Mat n) (R : NNReal) (hC : ‖C‖ ≤ R) :
    LipschitzOnWith (2 * R * R) (fun X : Mat n => -(X * C * X) - D)
      {X | ‖X‖ ≤ R} := by
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro X hX Y hY
  apply (riccati_rhs_difference_bound C D X Y).trans
  apply mul_le_mul_of_nonneg_right _ dist_nonneg
  change (‖X‖ + ‖Y‖) * ‖C‖ ≤ (2 : Real) * R * R
  calc
    (‖X‖ + ‖Y‖) * ‖C‖ ≤ (R + R) * R :=
      mul_le_mul (add_le_add hX hY) hC (norm_nonneg _) (by positivity)
    _ = (2 : Real) * R * R := by ring

/-- All inputs are coefficients, initial conditions, and interval geometry.
No solution path, conserved invariant, inverse, or flow bound is an input. -/
structure Coefficients (n : Type*) [Fintype n] [DecidableEq n] where
  lower : Real
  upper : Real
  startTime : Real
  endTime : Real
  start_mem : startTime ∈ Ioo lower upper
  end_mem : endTime ∈ Ioo lower upper
  C : Real → Mat n
  D : Real → Mat n
  C_continuous : ContinuousOn C (Icc lower upper)
  D_continuous : ContinuousOn D (Icc lower upper)
  C_symmetric : ∀ t ∈ uIcc startTime endTime, (C t).IsSymm
  D_symmetric : ∀ t ∈ uIcc startTime endTime, (D t).IsSymm
  C_hermitian : ∀ t ∈ uIcc startTime endTime, (C t).IsHermitian
  D_hermitian : ∀ t ∈ uIcc startTime endTime, (D t).IsHermitian
  H0 : Mat n
  H0_symmetric : H0.IsSymm
  H0_imaginaryPositive : ComplexPosDef (hermitianImaginaryPart H0)

namespace Coefficients

variable (d : Coefficients n)

def vectorField (t : Real) (s : State n) : State n :=
  hamiltonianOperator (d.C t) (d.D t) s

theorem vectorField_continuous :
    ContinuousOn (uncurry d.vectorField) ((Icc d.lower d.upper) ×ˢ (univ : Set (State n))) := by
  change ContinuousOn (fun p : Real × State n =>
    (d.C p.1 * p.2.2, -(d.D p.1 * p.2.1))) _
  exact ((d.C_continuous.comp continuousOn_fst (fun _ h => h.1)).mul
    continuousOn_snd.snd).prodMk
      (((d.D_continuous.comp continuousOn_fst (fun _ h => h.1)).mul
        continuousOn_snd.fst).neg)

theorem exists_lipschitz_bound :
    ∃ K : NNReal, ∀ t ∈ Icc d.lower d.upper, LipschitzWith K (d.vectorField t) := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (d.C_continuous.norm.add d.D_continuous.norm)
  refine ⟨⟨max M 0, le_max_right _ _⟩, fun t ht => ?_⟩
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [vectorField, dist_eq_norm, ← map_sub]
  apply (hamiltonianOperator_norm_apply_le (d.C t) (d.D t) (x - y)).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  have hsum : ‖d.C t‖ + ‖d.D t‖ ≤ M :=
    (le_abs_self _).trans (hM t ht)
  exact (max_le (le_add_of_nonneg_right (norm_nonneg _))
    (le_add_of_nonneg_left (norm_nonneg _))).trans (hsum.trans (le_max_left _ _))

theorem exists_hamiltonian_solution :
    ∃ u : Real → State n,
      u d.startTime = (1, d.H0) ∧ Continuous u ∧
      ∀ t ∈ Icc d.lower d.upper,
        HasDerivWithinAt u (d.vectorField t (u t)) (Icc d.lower d.upper) t := by
  obtain ⟨K, hK⟩ := d.exists_lipschitz_bound
  exact CompactIntervalLipschitzODE.exists_solution
    ⟨d.startTime, d.start_mem.1.le, d.start_mem.2.le⟩
    d.vectorField d.vectorField_continuous K hK (1, d.H0)

def solution : Real → State n := Classical.choose d.exists_hamiltonian_solution

theorem solution_initial : d.solution d.startTime = (1, d.H0) :=
  (Classical.choose_spec d.exists_hamiltonian_solution).1

theorem solution_continuous : Continuous d.solution :=
  (Classical.choose_spec d.exists_hamiltonian_solution).2.1

theorem solution_hasDerivWithinAt {t : Real} (ht : t ∈ Icc d.lower d.upper) :
    HasDerivWithinAt d.solution (d.vectorField t (d.solution t)) (Icc d.lower d.upper) t :=
  (Classical.choose_spec d.exists_hamiltonian_solution).2.2 t ht

theorem solution_hasDerivAt {t : Real} (ht : t ∈ Ioo d.lower d.upper) :
    HasDerivAt d.solution (d.vectorField t (d.solution t)) t :=
  (d.solution_hasDerivWithinAt ⟨ht.1.le, ht.2.le⟩).hasDerivAt (Icc_mem_nhds ht.1 ht.2)

theorem interval_subset : uIcc d.startTime d.endTime ⊆ Ioo d.lower d.upper := by
  intro t ht
  rcases (mem_uIcc.mp ht) with h | h
  · exact ⟨d.start_mem.1.trans_le h.1, h.2.trans_lt d.end_mem.2⟩
  · exact ⟨d.end_mem.1.trans_le h.1, h.2.trans_lt d.start_mem.2⟩

/-- Generated Hamiltonian paths, with the actual equation at both requested
endpoints. The existing Riccati engine derives all interval invariants. -/
def toRiccatiFlow : RiccatiFlow n where
  startTime := d.startTime
  endTime := d.endTime
  C := d.C
  D := d.D
  Y := fun t => (d.solution t).1
  Z := fun t => (d.solution t).2
  hasDerivY := fun t ht =>
    (ContinuousLinearMap.fst Real (Mat n) (Mat n)).hasFDerivAt.comp_hasDerivAt t
      (d.solution_hasDerivAt (d.interval_subset ht))
  hasDerivZ := fun t ht => by
    simpa [vectorField, hamiltonianOperator_apply, neg_mul] using
      (ContinuousLinearMap.snd Real (Mat n) (Mat n)).hasFDerivAt.comp_hasDerivAt t
        (d.solution_hasDerivAt (d.interval_subset ht))
  C_symmetric := d.C_symmetric
  D_symmetric := d.D_symmetric
  C_hermitian := d.C_hermitian
  D_hermitian := d.D_hermitian
  H0 := d.H0
  H0_symmetric := d.H0_symmetric
  H0_imaginaryPositive := d.H0_imaginaryPositive
  initialY := congrArg Prod.fst d.solution_initial
  initialZ := congrArg Prod.snd d.solution_initial

theorem solution_unique (u : Real → State n)
    (hu : ContinuousOn u (Icc d.lower d.upper))
    (hdu : ∀ t ∈ Ioo d.lower d.upper, HasDerivAt u (d.vectorField t (u t)) t)
    (hinit : u d.startTime = (1, d.H0)) :
    EqOn u d.solution (Icc d.lower d.upper) := by
  obtain ⟨K, hK⟩ := d.exists_lipschitz_bound
  exact ODE_solution_unique_of_mem_Icc
    (s := fun _ => univ) (fun t ht => (hK t ⟨ht.1.le, ht.2.le⟩).lipschitzOnWith)
    d.start_mem hu hdu (fun _ _ => mem_univ _)
    d.solution_continuous.continuousOn (fun _ ht => d.solution_hasDerivAt ht)
    (fun _ _ => mem_univ _) (hinit.trans d.solution_initial.symm)

theorem generated_Y_invertible {t : Real} (ht : t ∈ uIcc d.startTime d.endTime) :
    IsUnit (d.toRiccatiFlow.Y t) := d.toRiccatiFlow.Y_isUnit t ht

theorem generated_riccati_equation {t : Real} (ht : t ∈ uIcc d.startTime d.endTime) :
    d.toRiccatiFlow.dH t + d.toRiccatiFlow.H t * d.C t * d.toRiccatiFlow.H t + d.D t = 0 :=
  d.toRiccatiFlow.equation38 ht

theorem generated_H_initial : d.toRiccatiFlow.H d.startTime = d.H0 := by
  change (d.solution d.startTime).2 * (d.solution d.startTime).1⁻¹ = d.H0
  rw [d.solution_initial]
  simp

theorem generated_H_hasDerivAt {t : Real} (ht : t ∈ uIcc d.startTime d.endTime) :
    HasDerivAt d.toRiccatiFlow.H
      (-(d.toRiccatiFlow.H t * d.C t * d.toRiccatiFlow.H t) - d.D t) t := by
  have heq := d.generated_riccati_equation ht
  have hderiv : d.toRiccatiFlow.dH t =
      -(d.toRiccatiFlow.H t * d.C t * d.toRiccatiFlow.H t) - d.D t := by
    apply eq_sub_iff_add_eq.mpr
    apply eq_neg_iff_add_eq_zero.mpr
    simpa only [add_right_comm] using heq
  rw [← hderiv]
  exact d.toRiccatiFlow.H_hasDerivAt ht

/-- Uniqueness for the nonlinear Riccati equation itself, not merely for its
linear lift. Neither positivity nor an inverse is required of the competitor. -/
theorem riccati_solution_unique (Q : Real → Mat n)
    (hQ : ∀ t ∈ uIcc d.startTime d.endTime,
      HasDerivAt Q (-(Q t * d.C t * Q t) - d.D t) t)
    (hinit : Q d.startTime = d.H0) :
    EqOn Q d.toRiccatiFlow.H (uIcc d.startTime d.endTime) := by
  have hQcont := HasDerivAt.continuousOn hQ
  have hHderiv := fun t (ht : t ∈ uIcc d.startTime d.endTime) => d.generated_H_hasDerivAt ht
  have hHcont := HasDerivAt.continuousOn hHderiv
  have hCcont := d.C_continuous.mono (d.interval_subset.trans Ioo_subset_Icc_self)
  obtain ⟨B, hB⟩ := isCompact_uIcc.exists_bound_of_continuousOn
    ((hQcont.norm.add hHcont.norm).add hCcont.norm)
  let R : NNReal := ⟨max B 0 + 1, by positivity⟩
  have hbound (t : Real) (ht : t ∈ uIcc d.startTime d.endTime) :
      ‖Q t‖ ≤ R ∧ ‖d.toRiccatiFlow.H t‖ ≤ R ∧ ‖d.C t‖ ≤ R := by
    have hb : ‖Q t‖ + ‖d.toRiccatiFlow.H t‖ + ‖d.C t‖ ≤ B :=
      (le_abs_self _).trans (hB t ht)
    have hbR : B ≤ (R : Real) := (le_max_left B 0).trans (by
      change max B 0 ≤ max B 0 + 1
      linarith)
    have hq0 := norm_nonneg (Q t)
    have hh0 := norm_nonneg (d.toRiccatiFlow.H t)
    have hc0 := norm_nonneg (d.C t)
    exact ⟨by linarith, by linarith, by linarith⟩
  have hv (t : Real) (ht : t ∈ uIcc d.startTime d.endTime) :=
    riccati_rhs_lipschitz (d.C t) (d.D t) R (hbound t ht).2.2
  have hsame : Q d.startTime = d.toRiccatiFlow.H d.startTime :=
    hinit.trans d.generated_H_initial.symm
  rcases le_total d.startTime d.endTime with hle | hle
  · rw [uIcc_of_le hle] at *
    exact ODE_solution_unique_of_mem_Icc_right
      (fun t ht => hv t (Ico_subset_Icc_self ht))
      hQcont (fun t ht => (hQ t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
      (fun t ht => (hbound t (Ico_subset_Icc_self ht)).1)
      hHcont (fun t ht => (hHderiv t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
      (fun t ht => (hbound t (Ico_subset_Icc_self ht)).2.1) hsame
  · rw [uIcc_of_ge hle] at *
    exact ODE_solution_unique_of_mem_Icc_left
      (fun t ht => hv t (Ioc_subset_Icc_self ht))
      hQcont (fun t ht => (hQ t (Ioc_subset_Icc_self ht)).hasDerivWithinAt)
      (fun t ht => (hbound t (Ioc_subset_Icc_self ht)).1)
      hHcont (fun t ht => (hHderiv t (Ioc_subset_Icc_self ht)).hasDerivWithinAt)
      (fun t ht => (hbound t (Ioc_subset_Icc_self ht)).2.1) hsame

def intervalCertificate : RiccatiFlow.IntervalCertificate d.toRiccatiFlow :=
  d.toRiccatiFlow.intervalCertificate

/-- Compactness of the constructed path supplies the uniform action bound.
This is not an additional geometric or ODE-solution assumption. -/
theorem exists_positive_action_bound : ∃ M : Real, 0 < M ∧
    ∀ t ∈ uIcc d.startTime d.endTime, ∀ x : n → Complex,
      ‖d.toRiccatiFlow.Y t *ᵥ x‖ ≤ M * ‖x‖ := by
  have hcont : Continuous (fun t => ‖vectorActionEquiv (d.solution t).1‖) :=
    (vectorActionEquiv.continuous.comp d.solution_continuous.fst).norm
  obtain ⟨B, hB⟩ := isCompact_uIcc.exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨max B 0 + 1, by positivity, fun t ht x => ?_⟩
  calc
    ‖d.toRiccatiFlow.Y t *ᵥ x‖ ≤ ‖vectorActionEquiv (d.solution t).1‖ * ‖x‖ :=
      (vectorActionEquiv (d.solution t).1).le_opNorm x
    _ ≤ (max B 0 + 1) * ‖x‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg x)
      have hb : ‖vectorActionEquiv (d.solution t).1‖ ≤ B := by
        simpa only [norm_norm] using hB t ht
      exact hb.trans ((le_max_left B 0).trans (by linarith))

def actionBound : Real := Classical.choose d.exists_positive_action_bound

theorem actionBound_pos : 0 < d.actionBound :=
  (Classical.choose_spec d.exists_positive_action_bound).1

theorem actionBound_spec {t : Real} (ht : t ∈ uIcc d.startTime d.endTime)
    (x : n → Complex) : ‖d.toRiccatiFlow.Y t *ᵥ x‖ ≤ d.actionBound * ‖x‖ :=
  (Classical.choose_spec d.exists_positive_action_bound).2 t ht x

/-- A supplied quantitative lower bound on the initial phase now generates
the whole uniform Riccati packet, including its positive interval constant. -/
def toUniformRiccatiFlow (c0 : Real) (hc0 : 0 < c0)
    (hcoercive : RealCoercive (hermitianImaginaryPart d.H0) c0) : UniformRiccatiFlow n where
  toRiccatiFlow := d.toRiccatiFlow
  initialCoercivity := c0
  initialCoercivity_pos := hc0
  H0_coercive := hcoercive
  YActionBound := d.actionBound
  YActionBound_pos := d.actionBound_pos
  Y_mulVec_bound := fun _ ht x => d.actionBound_spec ht x

theorem generated_uniform_coercivity (c0 : Real) (hc0 : 0 < c0)
    (hcoercive : RealCoercive (hermitianImaginaryPart d.H0) c0)
    {t : Real} (ht : t ∈ uIcc d.startTime d.endTime) (x : n → Complex) :
    (c0 / d.actionBound ^ 2) * ‖x‖ ^ 2 ≤
      (complexQuadratic (d.toRiccatiFlow.H t) x).im :=
  (d.toUniformRiccatiFlow c0 hc0 hcoercive).phase_uniform_coercivity ht x

end Coefficients
end LiuWang2025SemilinearWaveRiccatiExistence
