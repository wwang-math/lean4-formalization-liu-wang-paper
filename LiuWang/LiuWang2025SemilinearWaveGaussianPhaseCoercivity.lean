import LiuWang.LiuWang2025SemilinearWaveGaussianL2Bridge
import LiuWang.LiuWang2025SemilinearWaveRiccatiPhase
import LiuWang.LiuWang2025SemilinearWaveRiccatiFlow
import LiuWang.LiuWang2025SemilinearWaveFourBeamPhaseLemma
import LiuWang.LiuWang2025SemilinearWaveComplexGaussianNormalForm

/-!
# Liu-Wang semilinear wave: uniform Gaussian coercivity from the Riccati phase

`LiuWang2025SemilinearWaveRiccatiPhase` proves that the Riccati-transported
phase Hessian `H` has positive definite Hermitian imaginary part, hence

`0 < Im (x^* H x)` for every `x != 0`                           (pointwise)

and `LiuWang2025SemilinearWaveGaussianL2Bridge` converts a *uniform*
transverse Gaussian bound

`b |z|^2 <= Im phi(z)`                                          (uniform)

into the source's `L^2` rate.  The step between the two -- pointwise strict
positivity of a quadratic form implies a uniform coercivity constant -- is the
missing analytic link, and it is a genuine compactness statement, not a
restatement.  This file supplies it:

* `exists_coercivity_of_pos` : for any continuous, `2`-homogeneous
  `Q : (Fin d -> Real) -> Real` which is strictly positive away from the
  origin there is `b > 0` with `b |z|^2 <= Q z` for **every** `z`.  The proof
  minimises `Q` on the compact transverse unit sphere `{radiusSq = 1}` and
  propagates the minimum by homogeneity.
* `exists_riccatiPhase_coercivity` : the specialisation to the Riccati phase
  `phi_H(z) = z^* H z`, whose positivity is exactly
  `RiccatiPhase.quadraticPhase_im_pos`.
* `riccatiBeam_L2_rate` and `reflectedRiccatiBeam_L2_rate` : the end-to-end
  consequence.  A Gaussian beam built on a Riccati-transported phase Hessian,
  with amplitude dominated by `A |z|^{2m}`, has transverse `L^2` norm
  `O(rho^{-(m + d/4)})`, and the same holds for the incident-minus-reflected
  combination which vanishes on the inaccessible face.

The coercivity constant is *produced* here rather than postulated, so the
`hIm` hypothesis of the `L^2` bridge is discharged from the Riccati layer.
-/

noncomputable section

open Real MeasureTheory
open scoped BigOperators

namespace LiuWang2025SemilinearWaveGaussianPhaseCoercivity

open LiuWang2025SemilinearWaveGaussianMassScaling (radiusSq)
open LiuWang2025SemilinearWaveGaussianL2Bridge
open LiuWang2025SemilinearWaveRiccatiPhase

/-! ## The transverse unit sphere -/

/-- A vanishing transverse radius forces a vanishing transverse vector. -/
theorem radiusSq_eq_zero_iff {d : Nat} {z : Fin d -> Real} :
    radiusSq z = 0 ↔ z = 0 := by
  constructor
  · intro h
    rw [radiusSq] at h
    funext i
    have hnn : ∀ j ∈ (Finset.univ : Finset (Fin d)), (0 : Real) ≤ (z j) ^ 2 :=
      fun j _ => sq_nonneg _
    have hi := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 h i (Finset.mem_univ i)
    exact sq_eq_zero_iff.1 hi
  · intro h
    subst h
    simp [radiusSq]

/-- **Uniform coercivity from pointwise positivity.**  A continuous quadratic
homogeneous function which is strictly positive away from the origin is bounded
below by a positive multiple of the transverse radius, uniformly. -/
theorem exists_coercivity_of_pos {d : Nat} {Q : (Fin d -> Real) -> Real}
    (hQc : Continuous Q)
    (hhom : ∀ (r : Real) (z : Fin d -> Real), Q (r • z) = r ^ 2 * Q z)
    (hpos : ∀ z : Fin d -> Real, z ≠ 0 -> 0 < Q z) :
    ∃ b : Real, 0 < b ∧ ∀ z : Fin d -> Real, b * radiusSq z ≤ Q z := by
  classical
  have hQ0 : Q 0 = 0 := by
    have h := hhom 0 0
    simpa using h
  set S : Set (Fin d -> Real) := {z | radiusSq z = 1} with hSdef
  have hunit : ∀ z : Fin d -> Real, radiusSq z ≠ 0 ->
      (Real.sqrt (radiusSq z))⁻¹ • z ∈ S := by
    intro z hz
    have hposz : 0 < radiusSq z :=
      lt_of_le_of_ne (radiusSq_nonneg z) (Ne.symm hz)
    have hsq : Real.sqrt (radiusSq z) ^ 2 = radiusSq z := Real.sq_sqrt hposz.le
    show radiusSq ((Real.sqrt (radiusSq z))⁻¹ • z) = 1
    rw [radiusSq_smul, inv_pow, hsq, inv_mul_cancel₀ hz]
  have hscale : ∀ z : Fin d -> Real, radiusSq z ≠ 0 ->
      Q z = radiusSq z * Q ((Real.sqrt (radiusSq z))⁻¹ • z) := by
    intro z hz
    have hposz : 0 < radiusSq z :=
      lt_of_le_of_ne (radiusSq_nonneg z) (Ne.symm hz)
    have hsq : Real.sqrt (radiusSq z) ^ 2 = radiusSq z := Real.sq_sqrt hposz.le
    rw [hhom, inv_pow, hsq, ← mul_assoc, mul_inv_cancel₀ hz, one_mul]
  by_cases hSne : S.Nonempty
  · have hSclosed : IsClosed S :=
      isClosed_eq continuous_radiusSq continuous_const
    have hsub : S ⊆ Metric.closedBall (0 : Fin d -> Real) 1 := by
      intro z hz
      have hz1 : radiusSq z = 1 := hz
      rw [Metric.mem_closedBall, dist_zero_right]
      refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_
      have hle : (z i) ^ 2 ≤ radiusSq z := by
        rw [radiusSq]
        exact Finset.single_le_sum (fun j _ => sq_nonneg (z j)) (Finset.mem_univ i)
      rw [hz1] at hle
      rw [Real.norm_eq_abs]
      exact (sq_le_one_iff_abs_le_one _).1 hle
    have hcompact : IsCompact S :=
      Metric.isCompact_of_isClosed_isBounded hSclosed
        (Metric.isBounded_closedBall.subset hsub)
    obtain ⟨z0, hz0S, hz0min⟩ := hcompact.exists_isMinOn hSne hQc.continuousOn
    have hz0one : radiusSq z0 = 1 := hz0S
    have hz0ne : z0 ≠ 0 := by
      intro h
      rw [h] at hz0one
      simp [radiusSq] at hz0one
    refine ⟨Q z0, hpos z0 hz0ne, fun z => ?_⟩
    by_cases hz : radiusSq z = 0
    · refine le_of_eq ?_
      rw [hz, mul_zero, radiusSq_eq_zero_iff.1 hz, hQ0]
    · have hposz : 0 < radiusSq z :=
        lt_of_le_of_ne (radiusSq_nonneg z) (Ne.symm hz)
      have hmin : Q z0 ≤ Q ((Real.sqrt (radiusSq z))⁻¹ • z) :=
        isMinOn_iff.1 hz0min _ (hunit z hz)
      calc Q z0 * radiusSq z
          ≤ Q ((Real.sqrt (radiusSq z))⁻¹ • z) * radiusSq z :=
            mul_le_mul_of_nonneg_right hmin hposz.le
        _ = Q z := by rw [hscale z hz]; ring
  · refine ⟨1, one_pos, fun z => ?_⟩
    have hz : radiusSq z = 0 := by
      by_contra h
      exact hSne ⟨_, hunit z h⟩
    refine le_of_eq ?_
    rw [hz, mul_zero, radiusSq_eq_zero_iff.1 hz, hQ0]

/-! ## The Riccati-transported quadratic phase in the transverse variable -/

/-- The Riccati phase evaluated on a real transverse vector. -/
def phaseValue {d : Nat} (H : Matrix (Fin d) (Fin d) Complex)
    (z : Fin d -> Real) : Complex :=
  complexQuadratic H (fun i => (z i : Complex))

/-- Its imaginary part, written as a real quadratic form. -/
def phaseIm {d : Nat} (H : Matrix (Fin d) (Fin d) Complex)
    (z : Fin d -> Real) : Real :=
  ∑ i, ∑ j, (H i j).im * z i * z j

theorem phaseValue_eq_sum {d : Nat} (H : Matrix (Fin d) (Fin d) Complex)
    (z : Fin d -> Real) :
    phaseValue H z = ∑ i, ∑ j, H i j * (z i : Complex) * (z j : Complex) := by
  simp only [phaseValue, complexQuadratic, dotProduct, Matrix.mulVec,
    Pi.star_apply, Complex.star_def, Complex.conj_ofReal, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ =>
    Finset.sum_congr rfl fun j _ => by ring

theorem phaseValue_im {d : Nat} (H : Matrix (Fin d) (Fin d) Complex)
    (z : Fin d -> Real) : (phaseValue H z).im = phaseIm H z := by
  rw [phaseValue_eq_sum, phaseIm, Complex.im_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.im_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [Complex.mul_im, Complex.mul_re]

theorem phaseIm_smul {d : Nat} (H : Matrix (Fin d) (Fin d) Complex)
    (r : Real) (z : Fin d -> Real) :
    phaseIm H (r • z) = r ^ 2 * phaseIm H z := by
  rw [phaseIm, phaseIm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem continuous_phaseIm {d : Nat} (H : Matrix (Fin d) (Fin d) Complex) :
    Continuous (phaseIm H) := by
  show Continuous fun z : Fin d -> Real => ∑ i, ∑ j, (H i j).im * z i * z j
  exact continuous_finset_sum _ fun i _ =>
    continuous_finset_sum _ fun j _ =>
      (continuous_const.mul (continuous_apply i)).mul (continuous_apply j)

/-- Pointwise strict positivity of the Riccati phase, transported to the real
transverse variable. -/
theorem phaseIm_pos {d : Nat} (H : Matrix (Fin d) (Fin d) Complex)
    (hH : ComplexPosDef (hermitianImaginaryPart H))
    {z : Fin d -> Real} (hz : z ≠ 0) : 0 < phaseIm H z := by
  have hx : (fun i => (z i : Complex)) ≠ 0 := by
    intro h
    refine hz (funext fun i => ?_)
    have hi := congrFun h i
    simpa using hi
  have hpos := LiuWang2025SemilinearWaveRiccatiPhase.quadraticPhase_im_pos H hH hx
  rw [← phaseValue, phaseValue_im] at hpos
  exact hpos

/-- **The Riccati phase is uniformly coercive.**  The constant is produced by
compactness from the pointwise positivity proved in the Riccati layer. -/
theorem exists_riccatiPhase_coercivity {d : Nat}
    (H : Matrix (Fin d) (Fin d) Complex)
    (hH : ComplexPosDef (hermitianImaginaryPart H)) :
    ∃ b : Real, 0 < b ∧
      ∀ z : Fin d -> Real, b * radiusSq z ≤ (phaseValue H z).im := by
  obtain ⟨b, hb, hcoer⟩ :=
    exists_coercivity_of_pos (Q := phaseIm H) (continuous_phaseIm H)
      (fun r z => phaseIm_smul H r z) (fun z hz => phaseIm_pos H hH hz)
  refine ⟨b, hb, fun z => ?_⟩
  rw [phaseValue_im]
  exact hcoer z

/-! ## The quadratic phase near the beam centre

The source's phase is `phi = phi_1 + phi_2 + ...` with `phi_1 = z_1` linear and
`phi_2` the Riccati quadratic form.  The linear part carries the null covector
and the quadratic part is quadratically small, so the differential of the phase
at the beam centre is the covector itself.  That is what the four-beam
configuration of `LiuWang2025SemilinearWaveFourBeamPhaseLemma` requires.
-/

theorem phaseValue_zero {d : Nat} (H : Matrix (Fin d) (Fin d) Complex) :
    phaseValue H 0 = 0 := by
  rw [phaseValue_eq_sum]
  simp

/-- The Riccati quadratic phase is quadratically small. -/
theorem norm_phaseValue_le {d : Nat} (H : Matrix (Fin d) (Fin d) Complex)
    (z : Fin d -> Real) :
    ‖phaseValue H z‖ ≤ (∑ i, ∑ j, ‖H i j‖) * ‖z‖ ^ 2 := by
  rw [phaseValue_eq_sum]
  calc ‖∑ i, ∑ j, H i j * (z i : Complex) * (z j : Complex)‖
      ≤ ∑ i, ‖∑ j, H i j * (z i : Complex) * (z j : Complex)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ i, ∑ j, ‖H i j * (z i : Complex) * (z j : Complex)‖ :=
        Finset.sum_le_sum fun i _ => norm_sum_le _ _
    _ ≤ ∑ i, ∑ j, ‖H i j‖ * ‖z‖ ^ 2 := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
        rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real]
        have hi : ‖z i‖ ≤ ‖z‖ := norm_le_pi_norm z i
        have hj : ‖z j‖ ≤ ‖z‖ := norm_le_pi_norm z j
        calc ‖H i j‖ * ‖z i‖ * ‖z j‖
            ≤ ‖H i j‖ * ‖z‖ * ‖z‖ :=
              mul_le_mul (mul_le_mul_of_nonneg_left hi (norm_nonneg _)) hj
                (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
          _ = ‖H i j‖ * ‖z‖ ^ 2 := by ring
    _ = (∑ i, ∑ j, ‖H i j‖) * ‖z‖ ^ 2 := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => (Finset.sum_mul _ _ _).symm

/-- **The Riccati quadratic phase has vanishing differential at the beam
centre**, so it does not disturb the covector carried by the linear part. -/
theorem hasFDerivAt_phaseValue_zero {d : Nat}
    (H : Matrix (Fin d) (Fin d) Complex) :
    HasFDerivAt (phaseValue H) (0 : (Fin d -> Real) →L[Real] Complex) 0 := by
  have hCnn : (0 : Real) ≤ ∑ i, ∑ j, ‖H i j‖ :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => norm_nonneg _
  rw [hasFDerivAt_iff_isLittleO]
  simp only [phaseValue_zero, sub_zero, ContinuousLinearMap.zero_apply]
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  have hden : (0 : Real) < (∑ i, ∑ j, ‖H i j‖) + 1 := by linarith
  have hradius : (0 : Real) < c / ((∑ i, ∑ j, ‖H i j‖) + 1) := div_pos hc hden
  filter_upwards [Metric.ball_mem_nhds (0 : Fin d -> Real) hradius] with z hz
  have hznorm : ‖z‖ < c / ((∑ i, ∑ j, ‖H i j‖) + 1) := by
    simpa [dist_zero_right] using hz
  have hkey : (∑ i, ∑ j, ‖H i j‖) * ‖z‖ ≤ c := by
    have h1 : ((∑ i, ∑ j, ‖H i j‖) + 1) * ‖z‖
        < ((∑ i, ∑ j, ‖H i j‖) + 1) * (c / ((∑ i, ∑ j, ‖H i j‖) + 1)) :=
      mul_lt_mul_of_pos_left hznorm hden
    rw [mul_div_cancel₀ _ hden.ne'] at h1
    nlinarith [norm_nonneg z]
  calc ‖phaseValue H z‖ ≤ (∑ i, ∑ j, ‖H i j‖) * ‖z‖ ^ 2 := norm_phaseValue_le H z
    _ = ((∑ i, ∑ j, ‖H i j‖) * ‖z‖) * ‖z‖ := by ring
    _ ≤ c * ‖z‖ := mul_le_mul_of_nonneg_right hkey (norm_nonneg _)

/-! ## The end-to-end transverse `L^2` rate of a Riccati beam -/

/-- **A Riccati-generated Gaussian beam obeys the source's transverse `L^2`
rate.**  No coercivity is assumed: it is produced from the Riccati positivity. -/
theorem riccatiBeam_L2_rate {d : Nat} (H : Matrix (Fin d) (Fin d) Complex)
    (hH : ComplexPosDef (hermitianImaginaryPart H))
    {a : (Fin d -> Real) -> Complex} {A rho : Real} {m : Nat}
    (hA : 0 ≤ A) (hrho : 0 < rho)
    (ha : ∀ z, ‖a z‖ ≤ A * (radiusSq z) ^ m) :
    ∃ b : Real, 0 < b ∧
      Real.sqrt (∫ z : Fin d -> Real,
          ‖Complex.exp (Complex.I * (rho : Complex) * phaseValue H z) * a z‖ ^ 2)
        ≤ A * rho ^ (-((m : Real) + (d : Real) / 4))
            * Real.sqrt (gaussianMoment d (2 * m) (2 * b)) := by
  obtain ⟨b, hb, hcoer⟩ := exists_riccatiPhase_coercivity H hH
  exact ⟨b, hb, beamProfile_L2_rate_of_beam hA hb hrho hcoer ha⟩

/-- **The reflected Riccati beam.**  The incident-minus-reflected combination
vanishes identically on the reflecting face and obeys the same transverse `L^2`
rate with the constant merely doubled. -/
theorem reflectedRiccatiBeam_L2_rate {d : Nat} (H : Matrix (Fin d) (Fin d) Complex)
    (hH : ComplexPosDef (hermitianImaginaryPart H))
    {a : (Fin d -> Real) -> Complex} {A rho : Real} {m : Nat} (i0 : Fin d)
    (hA : 0 ≤ A) (hrho : 0 < rho)
    (ha : ∀ z, ‖a z‖ ≤ A * (radiusSq z) ^ m) :
    ∃ b : Real, 0 < b ∧
      Real.sqrt (∫ z : Fin d -> Real,
          ‖(fun y => Complex.exp (Complex.I * (rho : Complex) * phaseValue H y) * a y) z
            - (fun y => Complex.exp (Complex.I * (rho : Complex) * phaseValue H y) * a y)
                (reflect i0 z)‖ ^ 2)
        ≤ (A + A) * rho ^ (-((m : Real) + (d : Real) / 4))
            * Real.sqrt (gaussianMoment d (2 * m) (2 * b)) := by
  obtain ⟨b, hb, hcoer⟩ := exists_riccatiPhase_coercivity H hH
  exact ⟨b, hb, reflectedDifference_L2_rate i0 hA hb hrho
    (profileBound_of_beam hrho hcoer ha)⟩

/-! ## The explicit constant from a uniform Riccati flow

`LiuWang2025SemilinearWaveRiccatiFlow` produces, for a uniform Riccati flow, a
*quantitative* coercivity constant for the transported phase Hessian, stated in
the ambient supremum norm:

`c * ||x||^2 <= Im (x^* H(t) x)`  for every complex `x`.

Composed with the norm comparison of the bridge this yields the Gaussian width
`c / d` in the Euclidean radius, so the transverse `L^2` rate acquires an
explicit constant rather than one obtained abstractly by compactness.
-/

/-- The ambient norm of the complexification of a real transverse vector. -/
theorem norm_ofReal_vec {d : Nat} (z : Fin d -> Real) :
    ‖fun i => ((z i : Complex))‖ = ‖z‖ := by
  refine le_antisymm ?_ ?_
  · refine (pi_norm_le_iff_of_nonneg (norm_nonneg z)).2 fun i => ?_
    rw [Complex.norm_real]
    exact norm_le_pi_norm z i
  · refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
    have h := norm_le_pi_norm (fun i => ((z i : Complex))) i
    rwa [Complex.norm_real] at h

/-- **The explicit Gaussian width from a normwise coercivity constant.**  A
coercivity `c ||x||^2 <= Im (x^* H x)` in the ambient supremum norm becomes the
Euclidean-radius coercivity with constant `c / d`. -/
theorem quantitative_coercivity_of_normCoercive {d : Nat}
    (H : Matrix (Fin d) (Fin d) Complex) {c : Real} (hd : 0 < d) (hc : 0 ≤ c)
    (hcoer : ∀ x : Fin d -> Complex, c * ‖x‖ ^ 2 ≤ (complexQuadratic H x).im)
    (z : Fin d -> Real) :
    (c / (d : Real)) * radiusSq z ≤ (phaseValue H z).im := by
  have hdR : (0 : Real) < (d : Real) := by exact_mod_cast hd
  have hcomp := radiusSq_le_dim_mul_norm_sq z
  have hstep : (c / (d : Real)) * radiusSq z
      ≤ (c / (d : Real)) * ((d : Real) * ‖z‖ ^ 2) :=
    mul_le_mul_of_nonneg_left hcomp (div_nonneg hc hdR.le)
  have hsimp : (c / (d : Real)) * ((d : Real) * ‖z‖ ^ 2) = c * ‖z‖ ^ 2 := by
    field_simp
  have hphase : c * ‖z‖ ^ 2 ≤ (phaseValue H z).im := by
    have h := hcoer (fun i => ((z i : Complex)))
    rwa [norm_ofReal_vec] at h
  rw [hsimp] at hstep
  exact hstep.trans hphase

/-- **The transverse `L^2` rate with an explicit Gaussian width.**  A beam built
on a phase Hessian with normwise coercivity constant `c` has transverse `L^2`
norm bounded using the explicit width `c / d`. -/
theorem quantitativeBeam_L2_rate {d : Nat} (H : Matrix (Fin d) (Fin d) Complex)
    {c : Real} (hd : 0 < d) (hc : 0 < c)
    (hcoer : ∀ x : Fin d -> Complex, c * ‖x‖ ^ 2 ≤ (complexQuadratic H x).im)
    {a : (Fin d -> Real) -> Complex} {A rho : Real} {m : Nat}
    (hA : 0 ≤ A) (hrho : 0 < rho)
    (ha : ∀ z, ‖a z‖ ≤ A * (radiusSq z) ^ m) :
    Real.sqrt (∫ z : Fin d -> Real,
        ‖Complex.exp (Complex.I * (rho : Complex) * phaseValue H z) * a z‖ ^ 2)
      ≤ A * rho ^ (-((m : Real) + (d : Real) / 4))
          * Real.sqrt (gaussianMoment d (2 * m) (2 * (c / (d : Real)))) := by
  have hdR : (0 : Real) < (d : Real) := by exact_mod_cast hd
  have hb : (0 : Real) < c / (d : Real) := div_pos hc hdR
  exact beamProfile_L2_rate_of_beam hA hb hrho
    (quantitative_coercivity_of_normCoercive H hd hc.le hcoer) ha

/-- The explicit width also controls the source's interaction integral. -/
theorem quantitativeBeam_interaction_bound {d : Nat}
    (H : Matrix (Fin d) (Fin d) Complex) {c : Real} (hd : 0 < d) (hc : 0 < c)
    (hcoer : ∀ x : Fin d -> Complex, c * ‖x‖ ^ 2 ≤ (complexQuadratic H x).im)
    {a : (Fin d -> Real) -> Complex} {A rho : Real} {m : Nat}
    (_hA : 0 ≤ A) (hrho : 0 < rho)
    (ha : ∀ z, ‖a z‖ ≤ A * (radiusSq z) ^ m) :
    ‖∫ z : Fin d -> Real,
        Complex.exp (Complex.I * (rho : Complex) * phaseValue H z) * a z‖
      ≤ A * (rho ^ (-((m : Real) + (d : Real) / 2))
          * gaussianMoment d m (c / (d : Real))) := by
  have hdR : (0 : Real) < (d : Real) := by exact_mod_cast hd
  have hb : (0 : Real) < c / (d : Real) := div_pos hc hdR
  exact norm_integral_le_of_profileBound hb hrho
    (profileBound_of_beam hrho
      (quantitative_coercivity_of_normCoercive H hd hc.le hcoer) ha)

/-- **The complete chain from a uniform Riccati flow to the source's transverse
`L^2` rate.**  The flow supplies the explicit coercivity constant
`c_0 / M^2`; the norm comparison converts it to the Gaussian width
`c_0 / (M^2 d)`; the bridge converts that to the rate `rho^{-(m + d/4)}`.
No coercivity, integrability or rate is assumed anywhere along the chain. -/
theorem uniformFlowBeam_L2_rate {d : Nat}
    (flow : LiuWang2025SemilinearWaveRiccatiFlow.UniformRiccatiFlow (Fin d))
    {t : Real} (ht : t ∈ Set.uIcc flow.startTime flow.endTime) (hd : 0 < d)
    {a : (Fin d -> Real) -> Complex} {A rho : Real} {m : Nat}
    (hA : 0 ≤ A) (hrho : 0 < rho)
    (ha : ∀ z, ‖a z‖ ≤ A * (radiusSq z) ^ m) :
    Real.sqrt (∫ z : Fin d -> Real,
        ‖Complex.exp (Complex.I * (rho : Complex) * phaseValue (flow.H t) z)
          * a z‖ ^ 2)
      ≤ A * rho ^ (-((m : Real) + (d : Real) / 4))
          * Real.sqrt (gaussianMoment d (2 * m)
              (2 * (flow.phaseCoercivityConstant / (d : Real)))) :=
  quantitativeBeam_L2_rate (flow.H t) hd flow.phaseCoercivityConstant_pos
    (fun x => flow.phase_uniform_coercivity ht x) hA hrho ha

/-- The same chain for the source's interaction integral. -/
theorem uniformFlowBeam_interaction_bound {d : Nat}
    (flow : LiuWang2025SemilinearWaveRiccatiFlow.UniformRiccatiFlow (Fin d))
    {t : Real} (ht : t ∈ Set.uIcc flow.startTime flow.endTime) (hd : 0 < d)
    {a : (Fin d -> Real) -> Complex} {A rho : Real} {m : Nat}
    (hA : 0 ≤ A) (hrho : 0 < rho)
    (ha : ∀ z, ‖a z‖ ≤ A * (radiusSq z) ^ m) :
    ‖∫ z : Fin d -> Real,
        Complex.exp (Complex.I * (rho : Complex) * phaseValue (flow.H t) z) * a z‖
      ≤ A * (rho ^ (-((m : Real) + (d : Real) / 2))
          * gaussianMoment d m (flow.phaseCoercivityConstant / (d : Real))) :=
  quantitativeBeam_interaction_bound (flow.H t) hd flow.phaseCoercivityConstant_pos
    (fun x => flow.phase_uniform_coercivity ht x) hA hrho ha

/-! ## The source's four-beam phase, realized from the Riccati layer

`LiuWang2025SemilinearWaveFourBeamPhaseLemma` proves the source's summed-phase
lemma for any configuration whose phases vanish at the interaction point, carry
the four null covectors as differentials there, and are transversally coercive.
Those three were hypotheses.  Here they are *discharged*: the source's phase is
the null covector's linear part plus the Riccati quadratic form, and each
property is a theorem of the preceding sections.
-/

open LiuWang2025SemilinearWaveFourNullCovectors
open LiuWang2025SemilinearWaveFourBeamPhaseLemma

/-- The source's phase: the null covector's linear part `phi_1` plus the
Riccati quadratic form `phi_2`. -/
def sourcePhase {d : Nat} (theta : (Fin d -> Real) →L[Real] Real)
    (H : Matrix (Fin d) (Fin d) Complex) (z : Fin d -> Real) : Complex :=
  ((theta z : Real) : Complex) + phaseValue H z

theorem sourcePhase_zero {d : Nat} (theta : (Fin d -> Real) →L[Real] Real)
    (H : Matrix (Fin d) (Fin d) Complex) : sourcePhase theta H 0 = 0 := by
  rw [sourcePhase, phaseValue_zero, map_zero]
  simp

/-- **The differential at the beam centre is the null covector**: the quadratic
part contributes nothing. -/
theorem hasFDerivAt_sourcePhase {d : Nat} (theta : (Fin d -> Real) →L[Real] Real)
    (H : Matrix (Fin d) (Fin d) Complex) :
    HasFDerivAt (sourcePhase theta H) (Complex.ofRealCLM.comp theta) 0 := by
  have hlin : HasFDerivAt (fun z : Fin d -> Real => ((theta z : Real) : Complex))
      (Complex.ofRealCLM.comp theta) 0 :=
    (Complex.ofRealCLM.comp theta).hasFDerivAt
  simpa using hlin.add (hasFDerivAt_phaseValue_zero H)

theorem sourcePhase_im {d : Nat} (theta : (Fin d -> Real) →L[Real] Real)
    (H : Matrix (Fin d) (Fin d) Complex) (z : Fin d -> Real) :
    (sourcePhase theta H z).im = (phaseValue H z).im := by
  rw [sourcePhase, Complex.add_im, Complex.ofReal_im, zero_add]

/-- **Transverse coercivity in the ambient norm**, which is the form the
four-beam configuration consumes. -/
theorem sourcePhase_im_lower {d : Nat} (theta : (Fin d -> Real) →L[Real] Real)
    (H : Matrix (Fin d) (Fin d) Complex) {b : Real} (hb : 0 ≤ b)
    (hcoer : ∀ z : Fin d -> Real, b * radiusSq z ≤ (phaseValue H z).im)
    (z : Fin d -> Real) : b * ‖z‖ ^ 2 ≤ (sourcePhase theta H z).im := by
  rw [sourcePhase_im]
  exact le_trans (mul_le_mul_of_nonneg_left (norm_sq_le_radiusSq z) hb) (hcoer z)

/-- **The source's four-beam summed-phase configuration exists, built from
Riccati data.**  Four Riccati phase Hessians with positive definite imaginary
parts, together with the explicit Lorentz-frame null covectors, produce a
configuration carrying the source's weights and satisfying the summed-phase
lemma.  No phase property is assumed: vanishing at the interaction point, the
covector differentials, and the coercivity constants are all theorems. -/
theorem exists_riccatiFourBeamConfiguration {d : Nat}
    (frame : LorentzOrthonormalTwoFrame (Fin d -> Real))
    (H : Fin 4 -> Matrix (Fin d) (Fin d) Complex)
    (hH : ∀ j, ComplexPosDef (hermitianImaginaryPart (H j)))
    (radius : Real) (radius_pos : 0 < radius) :
    ∃ C : FourBeamPhaseConfiguration (Fin d -> Real),
      C.weight = frame.weight ∧ FourBeamPhaseConfiguration.Certificate C := by
  choose b hbpos hbcoer using fun j => exists_riccatiPhase_coercivity (H j) (hH j)
  refine ⟨ofLorentzFrame frame 0 radius radius_pos
      (fun j => sourcePhase (frame.covector j) (H j)) b
      (fun j => sourcePhase_zero _ _)
      (fun j => hasFDerivAt_sourcePhase _ _)
      hbpos
      (fun j q _ => ?_), ?_, ?_⟩
  · have hq : dist q (0 : Fin d -> Real) = ‖q‖ := by
      rw [dist_zero_right]
    rw [hq]
    exact sourcePhase_im_lower _ _ (hbpos j).le (hbcoer j) q
  · exact ofLorentzFrame_weight _ _ _ _ _ _ _ _ _ _
  · exact lorentzFrameCertificate _ _ _ _ _ _ _ _ _ _

/-! ## Stationary phase at the actual complex quadratic phase

The Gaussian-weight limit of `LiuWang2025SemilinearWaveGaussianL2Bridge` uses
the real weight `e^{-(b rho)|z|^2}`.  The source's integrand is instead
`e^{i rho S}`, whose modulus is only *bounded* by such a weight.  For the
Riccati phase -- which is exactly quadratic -- the same mechanism applies
verbatim: the rescaling `z = rho^{-1/2} w` cancels `rho` against the quadratic
homogeneity of the phase *exactly*, leaving a fixed complex Gaussian, and
coercivity supplies the dominating function.  The limiting constant is the
complex Gaussian integral rather than the real one.
-/

/-- The Riccati phase is homogeneous of degree two. -/
theorem phaseValue_smul {d : Nat} (H : Matrix (Fin d) (Fin d) Complex)
    (r : Real) (z : Fin d -> Real) :
    phaseValue H (r • z) = ((r ^ 2 : Real) : Complex) * phaseValue H z := by
  rw [phaseValue_eq_sum, phaseValue_eq_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul, Complex.ofReal_pow]
  ring

theorem continuous_phaseValue {d : Nat} (H : Matrix (Fin d) (Fin d) Complex) :
    Continuous (phaseValue H) := by
  have h : phaseValue H
      = fun z : Fin d -> Real => ∑ i, ∑ j, H i j * (z i : Complex) * (z j : Complex) :=
    funext (phaseValue_eq_sum H)
  rw [h]
  exact continuous_finset_sum _ fun i _ =>
    continuous_finset_sum _ fun j _ =>
      (continuous_const.mul (Complex.continuous_ofReal.comp (continuous_apply i))).mul
        (Complex.continuous_ofReal.comp (continuous_apply j))

/-- The source's oscillatory kernel `e^{i rho S}` at the Riccati phase. -/
def quadraticKernel {d : Nat} (H : Matrix (Fin d) (Fin d) Complex) (rho : Real)
    (z : Fin d -> Real) : Complex :=
  Complex.exp (Complex.I * ((rho : Real) : Complex) * phaseValue H z)

theorem norm_quadraticKernel {d : Nat} (H : Matrix (Fin d) (Fin d) Complex)
    (rho : Real) (z : Fin d -> Real) :
    ‖quadraticKernel H rho z‖ = Real.exp (-(rho * (phaseValue H z).im)) := by
  rw [quadraticKernel, Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.mul_im]

/-- Pulling a complex constant out on the right, through a real-linear
continuous map, avoiding the ambient `NormedSpace Real Complex` diamond. -/
theorem integral_mul_const_complex {d : Nat} (c : Complex)
    {F : (Fin d -> Real) -> Complex} (hF : Integrable F) :
    (∫ w : Fin d -> Real, F w * c) = (∫ w : Fin d -> Real, F w) * c :=
  ContinuousLinearMap.integral_comp_comm
    ((ContinuousLinearMap.mul Real Complex).flip c) hF

/-- **The exact rescaling identity for the quadratic phase.**  Because the phase
is homogeneous of degree two, the frequency cancels completely: no asymptotics
are involved. -/
theorem rescaled_quadratic_integral {d : Nat}
    (H : Matrix (Fin d) (Fin d) Complex) (g : (Fin d -> Real) -> Complex)
    {rho : Real} (hrho : 0 < rho) :
    ((Real.sqrt rho ^ d : Real)) • (∫ z : Fin d -> Real,
        quadraticKernel H rho z * g z)
      = ∫ w : Fin d -> Real,
          Complex.exp (Complex.I * phaseValue H w) * g ((Real.sqrt rho)⁻¹ • w) := by
  have hsqrt : 0 < Real.sqrt rho := Real.sqrt_pos.2 hrho
  have hr : (0 : Real) ≤ (Real.sqrt rho)⁻¹ := inv_nonneg.2 hsqrt.le
  have hrsq : ((Real.sqrt rho)⁻¹) ^ 2 = rho⁻¹ := by
    rw [inv_pow, Real.sq_sqrt hrho.le]
  have hinv : (((Real.sqrt rho)⁻¹ : Real) ^ d)⁻¹ = Real.sqrt rho ^ d := by
    rw [inv_pow, inv_inv]
  have hpt : ∀ w : Fin d -> Real,
      quadraticKernel H rho ((Real.sqrt rho)⁻¹ • w)
            * g ((Real.sqrt rho)⁻¹ • w)
        = Complex.exp (Complex.I * phaseValue H w)
            * g ((Real.sqrt rho)⁻¹ • w) := by
    intro w
    have hker : quadraticKernel H rho ((Real.sqrt rho)⁻¹ • w)
        = Complex.exp (Complex.I * phaseValue H w) := by
      rw [quadraticKernel, phaseValue_smul, hrsq]
      congr 1
      have hmul : ((rho : Real) : Complex) * ((rho⁻¹ : Real) : Complex) = 1 := by
        rw [← Complex.ofReal_mul, mul_inv_cancel₀ hrho.ne', Complex.ofReal_one]
      calc Complex.I * ((rho : Real) : Complex)
              * (((rho⁻¹ : Real) : Complex) * phaseValue H w)
          = Complex.I * (((rho : Real) : Complex) * ((rho⁻¹ : Real) : Complex))
              * phaseValue H w := by ring
        _ = Complex.I * 1 * phaseValue H w := by rw [hmul]
        _ = Complex.I * phaseValue H w := by ring
    rw [hker]
  have h := integral_comp_smul_pi_complex
    (fun z : Fin d -> Real => quadraticKernel H rho z * g z) hr
  simp only at h
  rw [hinv] at h
  rw [← h]
  exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt)

/-- **The complex Gaussian stationary-phase limit.**  With the phase coercive
and the amplitude bounded and continuous, the normalized integral converges to
the amplitude at the beam centre times the complex Gaussian constant. -/
theorem tendsto_normalized_quadratic_integral {d : Nat}
    (H : Matrix (Fin d) (Fin d) Complex) (g : (Fin d -> Real) -> Complex)
    {A b : Real} (hb : 0 < b)
    (hcoer : ∀ z : Fin d -> Real, b * radiusSq z ≤ (phaseValue H z).im)
    (hg : Continuous g) (hA : ∀ z, ‖g z‖ ≤ A) :
    Filter.Tendsto
      (fun rho : Real => ((Real.sqrt rho ^ d : Real)) • ∫ z : Fin d -> Real,
          quadraticKernel H rho z * g z)
      Filter.atTop
      (nhds ((∫ w : Fin d -> Real, Complex.exp (Complex.I * phaseValue H w))
        * g 0)) := by
  have hkercont : Continuous
      (fun w : Fin d -> Real => Complex.exp (Complex.I * phaseValue H w)) :=
    Complex.continuous_exp.comp (continuous_const.mul (continuous_phaseValue H))
  have hkerbound : ∀ w : Fin d -> Real,
      ‖Complex.exp (Complex.I * phaseValue H w)‖
        ≤ Real.exp (-b * radiusSq w) := by
    intro w
    have h1 : ‖Complex.exp (Complex.I * phaseValue H w)‖
        = Real.exp (-(phaseValue H w).im) := by
      rw [Complex.norm_exp]
      congr 1
      simp [Complex.mul_re]
    rw [h1]
    refine Real.exp_le_exp.2 ?_
    have := hcoer w
    linarith
  have hkerint : Integrable
      (fun w : Fin d -> Real => Complex.exp (Complex.I * phaseValue H w)) := by
    refine (integrable_gaussian_pi (d := d) hb).mono'
      hkercont.aestronglyMeasurable
      (Filter.Eventually.of_forall fun w => hkerbound w)
  have hbound_int : Integrable
      (fun w : Fin d -> Real => Real.exp (-b * radiusSq w) * A) :=
    (integrable_gaussian_pi (d := d) hb).mul_const _
  have hkey := MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (μ := (volume : Measure (Fin d -> Real)))
    (l := (Filter.atTop : Filter Real))
    (F := fun rho : Real => fun w : Fin d -> Real =>
      Complex.exp (Complex.I * phaseValue H w) * g ((Real.sqrt rho)⁻¹ • w))
    (f := fun w : Fin d -> Real =>
      Complex.exp (Complex.I * phaseValue H w) * g 0)
    (bound := fun w : Fin d -> Real => Real.exp (-b * radiusSq w) * A)
    (Filter.Eventually.of_forall fun rho =>
      (hkercont.mul
        (hg.comp (continuous_const_smul ((Real.sqrt rho)⁻¹)))).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun rho =>
      Filter.Eventually.of_forall fun w => by
        rw [norm_mul]
        exact mul_le_mul (hkerbound w) (hA _) (norm_nonneg _)
          (Real.exp_pos _).le)
    hbound_int
    (Filter.Eventually.of_forall fun w => by
      have hsmul : Filter.Tendsto
          (fun rho : Real => (Real.sqrt rho)⁻¹ • w) Filter.atTop
          (nhds ((0 : Real) • w)) :=
        Filter.Tendsto.smul_const
          (tendsto_inv_atTop_zero.comp Real.tendsto_sqrt_atTop) w
      rw [zero_smul] at hsmul
      exact ((hg.tendsto (0 : Fin d -> Real)).comp hsmul).const_mul _)
  rw [integral_mul_const_complex (g 0) hkerint] at hkey
  have heq : (fun rho : Real => ∫ w : Fin d -> Real,
        Complex.exp (Complex.I * phaseValue H w) * g ((Real.sqrt rho)⁻¹ • w))
      =ᶠ[Filter.atTop] (fun rho : Real => ((Real.sqrt rho ^ d : Real)) •
        ∫ z : Fin d -> Real, quadraticKernel H rho z * g z) := by
    filter_upwards [Filter.eventually_gt_atTop (0 : Real)] with rho hrho
    exact (rescaled_quadratic_integral H g hrho).symm
  exact hkey.congr' heq

/-- **The complex Gaussian constant of the Riccati phase is nonzero**, once the
phase is presented as a bounded bilinear form.  With that presentation the
non-vanishing is the repository's `gaussConst_ne_zero`, which derives it from
coercivity alone -- the source's Lemma 4.1 (iii) nondegeneracy.  Constructing
the bilinear presentation from the matrix is the one step left here; it is an
algebraic repackaging, not an analytic input. -/
theorem quadraticConstant_ne_zero {d : Nat} (H : Matrix (Fin d) (Fin d) Complex)
    (HH : (Fin d -> Real) →L[Real] (Fin d -> Real) →L[Real] Complex)
    (hHH : ∀ z : Fin d -> Real, HH z z = 2 * phaseValue H z)
    {c : Real} (hc : 0 < c)
    (hcoer : ∀ z : Fin d -> Real, c * ‖z‖ ^ 2 ≤ (HH z z).im) :
    (∫ w : Fin d -> Real, Complex.exp (Complex.I * phaseValue H w)) ≠ 0 := by
  have hconst := LiuWang2025SemilinearWaveComplexStationaryPhase.gaussConst_ne_zero
    (volume : Measure (Fin d -> Real)) hc hcoer
  have heq : LiuWang2025SemilinearWaveComplexStationaryPhase.gaussConst
        (volume : Measure (Fin d -> Real)) HH
      = ∫ w : Fin d -> Real, Complex.exp (Complex.I * phaseValue H w) := by
    rw [LiuWang2025SemilinearWaveComplexStationaryPhase.gaussConst]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    rw [LiuWang2025SemilinearWaveComplexStationaryPhase.gaussKernel, hHH]
    congr 1
    ring
  rwa [heq] at hconst

/-- **The source's pointwise conclusion at the actual complex quadratic
phase.**  If the normalized identity holds with a vanishing boundary side and
the complex Gaussian constant is nonzero, the amplitude vanishes at the
interaction point. -/
theorem amplitude_eq_zero_of_quadratic_identity {d : Nat}
    (H : Matrix (Fin d) (Fin d) Complex) (g : (Fin d -> Real) -> Complex)
    {A b : Real} (hb : 0 < b)
    (hcoer : ∀ z : Fin d -> Real, b * radiusSq z ≤ (phaseValue H z).im)
    (hg : Continuous g) (hA : ∀ z, ‖g z‖ ≤ A)
    (hconst : (∫ w : Fin d -> Real, Complex.exp (Complex.I * phaseValue H w)) ≠ 0)
    (boundary : Real -> Complex)
    (hbdry : Filter.Tendsto boundary Filter.atTop (nhds 0))
    (hid : ∀ rho : Real,
      ((Real.sqrt rho ^ d : Real)) • (∫ z : Fin d -> Real,
          quadraticKernel H rho z * g z) = boundary rho) :
    g 0 = 0 := by
  have h1 := tendsto_normalized_quadratic_integral H g hb hcoer hg hA
  rw [funext hid] at h1
  have hzero := tendsto_nhds_unique h1 hbdry
  exact (mul_eq_zero.1 hzero).resolve_left hconst

/-! ## The cubic recovery, assembled

Every piece of the source's Subsection 4.2 argument is now available: the
Riccati layer gives positivity, compactness turns it into a uniform coercivity
constant, the rescaling plus dominated convergence give the stationary-phase
limit at the actual oscillatory kernel, and the reflected-beam estimate makes
the inaccessible-boundary term vanish.  The theorem below composes them, which
is also a check that they fit together.
-/

/-- **The source's cubic recovery, assembled.**  Given a Riccati phase Hessian
with positive definite imaginary part, a coefficient and beam amplitudes that
are continuous and bounded with nonvanishing product at the interaction point,
the source's normalized identity, and a boundary side that vanishes, the
coefficient vanishes at the interaction point.  The coercivity constant is not
supplied: it is produced from the Riccati positivity. -/
theorem riccatiRecovery_coefficient_eq_zero {d : Nat} {iota : Type} [Fintype iota]
    (H : Matrix (Fin d) (Fin d) Complex)
    (hH : ComplexPosDef (hermitianImaginaryPart H))
    (V : (Fin d -> Real) -> Complex) (a : iota -> (Fin d -> Real) -> Complex)
    {KV : Real} {Ka : iota -> Real}
    (hV : Continuous V) (ha : ∀ j, Continuous (a j))
    (hVb : ∀ z, ‖V z‖ ≤ KV) (hab : ∀ j z, ‖a j z‖ ≤ Ka j)
    (hprod : (∏ j, a j 0) ≠ 0)
    (hconst : (∫ w : Fin d -> Real, Complex.exp (Complex.I * phaseValue H w)) ≠ 0)
    (boundary : Real -> Complex)
    (hbdry : Filter.Tendsto boundary Filter.atTop (nhds 0))
    (hid : ∀ rho : Real,
      ((Real.sqrt rho ^ d : Real)) • (∫ z : Fin d -> Real,
          quadraticKernel H rho z * (V z * ∏ j, a j z)) = boundary rho) :
    V 0 = 0 := by
  obtain ⟨b, hb, hcoer⟩ := exists_riccatiPhase_coercivity H hH
  have hcont : Continuous (fun z : Fin d -> Real => V z * ∏ j, a j z) :=
    hV.mul (continuous_finset_prod _ fun j _ => (ha j))
  have hKV : (0 : Real) ≤ KV := (norm_nonneg (V 0)).trans (hVb 0)
  have hbound : ∀ z : Fin d -> Real, ‖V z * ∏ j, a j z‖ ≤ KV * ∏ j, Ka j := by
    intro z
    rw [norm_mul, norm_prod]
    refine mul_le_mul (hVb z) ?_
      (Finset.prod_nonneg fun j _ => norm_nonneg _) hKV
    exact Finset.prod_le_prod (fun j _ => norm_nonneg _) (fun j _ => hab j z)
  have h := amplitude_eq_zero_of_quadratic_identity H
    (fun z : Fin d -> Real => V z * ∏ j, a j z) hb hcoer hcont hbound hconst
    boundary hbdry hid
  simp only at h
  exact (mul_eq_zero.1 h).resolve_right hprod

/-! ### The model instance: every hypothesis discharged

For the model phase Hessian `i * Id` the complex Gaussian constant is computed
outright, so the assembled recovery above has *no* remaining input beyond the
identity and the vanishing boundary side.
-/

theorem phaseValue_model {d : Nat} (w : Fin d -> Real) :
    phaseValue ((Complex.I : Complex) • (1 : Matrix (Fin d) (Fin d) Complex)) w
      = Complex.I * ((radiusSq w : Real) : Complex) := by
  rw [phaseValue_eq_sum, radiusSq]
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ i)]
  · simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
    ring
  · intro j _ hji
    simp [Matrix.smul_apply, Matrix.one_apply_ne (Ne.symm hji)]

/-- The model complex Gaussian constant is the computed, nonzero number
`sqrt(pi)^d`. -/
theorem modelQuadraticConstant {d : Nat} :
    (∫ w : Fin d -> Real, Complex.exp (Complex.I *
        phaseValue ((Complex.I : Complex) • (1 : Matrix (Fin d) (Fin d) Complex)) w))
      = ((Real.sqrt Real.pi ^ d : Real) : Complex) := by
  have hpt : ∀ w : Fin d -> Real,
      Complex.exp (Complex.I * phaseValue
          ((Complex.I : Complex) • (1 : Matrix (Fin d) (Fin d) Complex)) w)
        = ((Real.exp (-1 * radiusSq w) : Real) : Complex) := by
    intro w
    rw [phaseValue_model]
    have harg : Complex.I * (Complex.I * ((radiusSq w : Real) : Complex))
        = ((-1 * radiusSq w : Real) : Complex) := by
      push_cast
      rw [← mul_assoc, Complex.I_mul_I]
    rw [harg, ← Complex.ofReal_exp]
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt)]
  have hconv : (∫ w : Fin d -> Real, ((Real.exp (-1 * radiusSq w) : Real) : Complex))
      = ((∫ w : Fin d -> Real, Real.exp (-1 * radiusSq w) : Real) : Complex) := by
    simpa using ContinuousLinearMap.integral_comp_comm Complex.ofRealCLM
      (integrable_gaussian_pi (d := d) one_pos)
  rw [hconv, integral_gaussian_pi_eq one_pos, div_one]

theorem modelQuadraticConstant_ne_zero {d : Nat} :
    (∫ w : Fin d -> Real, Complex.exp (Complex.I *
        phaseValue ((Complex.I : Complex) • (1 : Matrix (Fin d) (Fin d) Complex)) w))
      ≠ 0 := by
  rw [modelQuadraticConstant]
  have hpos : (0 : Real) < Real.sqrt Real.pi ^ d :=
    pow_pos (Real.sqrt_pos.2 Real.pi_pos) d
  exact_mod_cast hpos.ne'

/-! ## Non-vacuity: the model phase Hessian -/

/-- The real part of `x^* x`. -/
theorem complexQuadratic_one_re {d : Nat} (x : Fin d -> Complex) :
    (complexQuadratic (1 : Matrix (Fin d) (Fin d) Complex) x).re
      = ∑ i, Complex.normSq (x i) := by
  rw [complexQuadratic, Matrix.one_mulVec, dotProduct, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Pi.star_apply, Complex.normSq_apply, Complex.mul_re]

/-- The identity matrix is positive definite in the sense used by the Riccati
layer. -/
theorem posDef_one {d : Nat} :
    ComplexPosDef (1 : Matrix (Fin d) (Fin d) Complex) := by
  refine ⟨Matrix.isHermitian_one, ?_⟩
  intro x hx
  rw [complexQuadratic_one_re]
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra h
    push Not at h
    exact hx (funext h)
  exact Finset.sum_pos' (fun j _ => Complex.normSq_nonneg _)
    ⟨i, Finset.mem_univ i, Complex.normSq_pos.2 hi⟩

/-- The model phase Hessian `i * Id` has Hermitian imaginary part `Id`. -/
theorem hermitianImaginaryPart_I_smul_one {d : Nat} :
    hermitianImaginaryPart
        ((Complex.I : Complex) • (1 : Matrix (Fin d) (Fin d) Complex))
      = 1 := by
  have hadj : Matrix.conjTranspose
        ((Complex.I : Complex) • (1 : Matrix (Fin d) (Fin d) Complex))
      = (-Complex.I) • (1 : Matrix (Fin d) (Fin d) Complex) := by
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_one]
    simp
  rw [hermitianImaginaryPart, hadj, ← sub_smul, smul_smul]
  have hconst : (-Complex.I / 2) * (Complex.I - -Complex.I) = 1 := by
    have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
    linear_combination -hI
  rw [hconst, one_smul]

/-- **The coercivity chain is not vacuous**: the model Riccati phase Hessian
satisfies the positivity hypothesis, so a coercivity constant genuinely
exists. -/
theorem model_exists_coercivity {d : Nat} :
    ∃ b : Real, 0 < b ∧ ∀ z : Fin d -> Real,
      b * radiusSq z
        ≤ (phaseValue ((Complex.I : Complex) • (1 : Matrix (Fin d) (Fin d) Complex)) z).im :=
  exists_riccatiPhase_coercivity _ (by rw [hermitianImaginaryPart_I_smul_one]; exact posDef_one)

/-! ## The reviewable certificate -/

/-- One reviewable object: pointwise Riccati positivity yields a uniform
Gaussian coercivity constant, and hence the transverse `L^2` rate. -/
structure Certificate (d : Nat) : Prop where
  homogeneousCoercivity : ∀ (Q : (Fin d -> Real) -> Real), Continuous Q ->
    (∀ (r : Real) (z : Fin d -> Real), Q (r • z) = r ^ 2 * Q z) ->
    (∀ z : Fin d -> Real, z ≠ 0 -> 0 < Q z) ->
      ∃ b : Real, 0 < b ∧ ∀ z : Fin d -> Real, b * radiusSq z ≤ Q z
  riccatiCoercivity : ∀ (H : Matrix (Fin d) (Fin d) Complex),
    ComplexPosDef (hermitianImaginaryPart H) ->
      ∃ b : Real, 0 < b ∧
        ∀ z : Fin d -> Real, b * radiusSq z ≤ (phaseValue H z).im
  beamRate : ∀ (H : Matrix (Fin d) (Fin d) Complex),
    ComplexPosDef (hermitianImaginaryPart H) ->
    ∀ (a : (Fin d -> Real) -> Complex) (A rho : Real) (m : Nat),
      0 ≤ A -> 0 < rho -> (∀ z, ‖a z‖ ≤ A * (radiusSq z) ^ m) ->
        ∃ b : Real, 0 < b ∧
          Real.sqrt (∫ z : Fin d -> Real,
              ‖Complex.exp (Complex.I * (rho : Complex) * phaseValue H z) * a z‖ ^ 2)
            ≤ A * rho ^ (-((m : Real) + (d : Real) / 4))
                * Real.sqrt (gaussianMoment d (2 * m) (2 * b))
  explicitWidth : ∀ (H : Matrix (Fin d) (Fin d) Complex) (c : Real),
    0 < d -> 0 ≤ c ->
    (∀ x : Fin d -> Complex, c * ‖x‖ ^ 2 ≤ (complexQuadratic H x).im) ->
      ∀ z : Fin d -> Real, (c / (d : Real)) * radiusSq z ≤ (phaseValue H z).im
  uniformFlowRate : ∀ (flow :
      LiuWang2025SemilinearWaveRiccatiFlow.UniformRiccatiFlow (Fin d)) (t : Real),
    t ∈ Set.uIcc flow.startTime flow.endTime -> 0 < d ->
    ∀ (a : (Fin d -> Real) -> Complex) (A rho : Real) (m : Nat),
      0 ≤ A -> 0 < rho -> (∀ z, ‖a z‖ ≤ A * (radiusSq z) ^ m) ->
        Real.sqrt (∫ z : Fin d -> Real,
            ‖Complex.exp (Complex.I * (rho : Complex) * phaseValue (flow.H t) z)
              * a z‖ ^ 2)
          ≤ A * rho ^ (-((m : Real) + (d : Real) / 4))
              * Real.sqrt (gaussianMoment d (2 * m)
                  (2 * (flow.phaseCoercivityConstant / (d : Real))))
  nonVacuous : hermitianImaginaryPart
      ((Complex.I : Complex) • (1 : Matrix (Fin d) (Fin d) Complex)) = 1

/-- Every field of the coercivity certificate is a theorem. -/
def certificate (d : Nat) : Certificate d where
  homogeneousCoercivity := fun _Q hQc hhom hpos =>
    exists_coercivity_of_pos hQc hhom hpos
  riccatiCoercivity := fun H hH => exists_riccatiPhase_coercivity H hH
  beamRate := fun H hH _a _A _rho _m hA hrho ha =>
    riccatiBeam_L2_rate H hH hA hrho ha
  explicitWidth := fun H _c hd hc hcoer z =>
    quantitative_coercivity_of_normCoercive H hd hc hcoer z
  uniformFlowRate := fun flow _t ht hd _a _A _rho _m hA hrho ha =>
    uniformFlowBeam_L2_rate flow ht hd hA hrho ha
  nonVacuous := hermitianImaginaryPart_I_smul_one

end LiuWang2025SemilinearWaveGaussianPhaseCoercivity
