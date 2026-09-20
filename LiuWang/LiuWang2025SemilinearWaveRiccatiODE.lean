import LiuWang.LiuWang2025SemilinearWaveDegreeBlockODE

/-!
# Liu-Wang semilinear wave: the degree-two (Riccati) block equation

The degree-two eikonal equation is quadratic, so its vector field is only
locally Lipschitz and the repository's compact-interval Picard iteration, which
needs a globally state-Lipschitz field, does not apply to it directly.

This file closes that gap honestly.  The quadratic field is composed with a
coordinatewise clamp onto a ball; the clamped field is globally Lipschitz and
globally bounded, so the Picard iteration does solve it; and a mean value
estimate then shows the resulting path stays inside the ball -- where the clamp
is the identity -- on an explicit subinterval around the initial parameter.  On
that subinterval the path solves the *true* Riccati equation.

Nothing here is assumed: the Lipschitz constant, the uniform bound and the
length of the subinterval are all produced by theorems.
-/

noncomputable section

open scoped BigOperators
open Set

namespace LiuWang2025SemilinearWaveRiccatiODE

open LiuWang2025SemilinearWaveTransverseJet
open LiuWang2025SemilinearWaveDegreeBlock
open LiuWang2025SemilinearWaveDegreeBlockODE

variable {d r : Nat}

/-! ## A Lipschitz clamp onto a ball -/

/-- Clamp a real number to `[-R, R]`. -/
def clampR (R t : Real) : Real := max (-R) (min R t)

theorem clampR_le {R : Real} (hR : 0 ≤ R) (t : Real) : clampR R t ≤ R :=
  max_le (by linarith) (min_le_left _ _)

theorem le_clampR (R t : Real) : -R ≤ clampR R t := le_max_left _ _

theorem abs_clampR_le {R : Real} (hR : 0 ≤ R) (t : Real) : |clampR R t| ≤ R :=
  abs_le.2 ⟨le_clampR R t, clampR_le hR t⟩

theorem clampR_eq_self {R t : Real} (h : |t| ≤ R) : clampR R t = t := by
  have h1 := (abs_le.1 h).1
  have h2 := (abs_le.1 h).2
  rw [clampR, min_eq_right h2, max_eq_right h1]

theorem abs_clampR_sub (R a b : Real) :
    |clampR R a - clampR R b| ≤ |a - b| := by
  have hneg : ∀ X Y : Real, |(-X) - (-Y)| = |X - Y| := fun X Y => by
    rw [show (-X) - (-Y) = -(X - Y) by ring, abs_neg]
  have hmin : |min R a - min R b| ≤ |a - b| := by
    have hA : min R a = -max (-R) (-a) := by rw [max_neg_neg, neg_neg]
    have hB : min R b = -max (-R) (-b) := by rw [max_neg_neg, neg_neg]
    rw [hA, hB, hneg, max_comm (-R) (-a), max_comm (-R) (-b)]
    calc |max (-a) (-R) - max (-b) (-R)|
        ≤ |(-a) - (-b)| := abs_max_sub_max_le_abs _ _ _
      _ = |a - b| := hneg a b
  calc |clampR R a - clampR R b|
      = |max (min R a) (-R) - max (min R b) (-R)| := by
        rw [clampR, clampR, max_comm (-R) (min R a), max_comm (-R) (min R b)]
    _ ≤ |min R a - min R b| := abs_max_sub_max_le_abs _ _ _
    _ ≤ |a - b| := hmin

/-- Clamp a complex number by clamping its real and imaginary parts. -/
def clampC (R : Real) (z : Complex) : Complex :=
  ⟨clampR R z.re, clampR R z.im⟩

@[simp] theorem clampC_re (R : Real) (z : Complex) :
    (clampC R z).re = clampR R z.re := rfl

@[simp] theorem clampC_im (R : Real) (z : Complex) :
    (clampC R z).im = clampR R z.im := rfl

theorem norm_clampC_le {R : Real} (hR : 0 ≤ R) (z : Complex) :
    ‖clampC R z‖ ≤ 2 * R := by
  refine le_trans (Complex.norm_le_abs_re_add_abs_im _) ?_
  have h1 := abs_clampR_le hR z.re
  have h2 := abs_clampR_le hR z.im
  simp only [clampC_re, clampC_im]
  linarith

theorem clampC_eq_self {R : Real} {z : Complex} (h : ‖z‖ ≤ R) :
    clampC R z = z := by
  refine Complex.ext ?_ ?_
  · exact clampR_eq_self (le_trans (Complex.abs_re_le_norm z) h)
  · exact clampR_eq_self (le_trans (Complex.abs_im_le_norm z) h)

theorem norm_clampC_sub (R : Real) (z w : Complex) :
    ‖clampC R z - clampC R w‖ ≤ 2 * ‖z - w‖ := by
  refine le_trans (Complex.norm_le_abs_re_add_abs_im _) ?_
  have hre : |(clampC R z - clampC R w).re| ≤ ‖z - w‖ := by
    show |clampR R z.re - clampR R w.re| ≤ ‖z - w‖
    have h := Complex.abs_re_le_norm (z - w)
    rw [Complex.sub_re] at h
    exact le_trans (abs_clampR_sub R z.re w.re) h
  have him : |(clampC R z - clampC R w).im| ≤ ‖z - w‖ := by
    show |clampR R z.im - clampR R w.im| ≤ ‖z - w‖
    have h := Complex.abs_im_le_norm (z - w)
    rw [Complex.sub_im] at h
    exact le_trans (abs_clampR_sub R z.im w.im) h
  linarith

theorem lipschitz_clampC (R : Real) : LipschitzWith 2 (clampC R) := by
  refine LipschitzWith.of_dist_le_mul fun z w => ?_
  rw [dist_eq_norm, dist_eq_norm]
  have h := norm_clampC_sub R z w
  have hc : ((2 : NNReal) : Real) = 2 := by norm_num
  rw [hc]
  exact h

theorem continuous_clampC (R : Real) : Continuous (clampC R) :=
  (lipschitz_clampC R).continuous

/-! ## The clamped Riccati field -/

/-- Coordinatewise clamp of a block onto the ball of radius `R`. -/
def clampBlock (R : Real) (x : DegreeBlock d r) : DegreeBlock d r :=
  fun a => clampC R (x a)

theorem norm_clampBlock_le {R : Real} (hR : 0 ≤ R) (x : DegreeBlock d r)
    (a : DegreeIndex d r) : ‖clampBlock R x a‖ ≤ 2 * R :=
  norm_clampC_le hR _

theorem clampBlock_eq_self {R : Real} {x : DegreeBlock d r}
    (h : ∀ a, ‖x a‖ ≤ R) : clampBlock R x = x :=
  funext fun a => clampC_eq_self (h a)

theorem dist_clampBlock_apply (R : Real) (x y : DegreeBlock d r)
    (a : DegreeIndex d r) :
    ‖clampBlock R x a - clampBlock R y a‖ ≤ 2 * dist x y := by
  refine le_trans (norm_clampC_sub R (x a) (y a)) ?_
  have h : ‖x a - y a‖ ≤ dist x y := by
    rw [← dist_eq_norm]
    exact dist_le_pi_dist x y a
  linarith

/-- The clamped field of the degree-two equation `2 c' + K c + Q(c,c) = source`.
-/
def riccatiField (K : Real -> DegreeIndex d r -> DegreeIndex d r -> Complex)
    (T : Real -> DegreeIndex d r -> DegreeIndex d r -> DegreeIndex d r -> Complex)
    (source : Real -> DegreeBlock d r) (R : Real) (s : Real)
    (x : DegreeBlock d r) : DegreeBlock d r :=
  fun a => ((2 : Complex))⁻¹ * (source s a - ∑ b, K s a b * clampBlock R x b
    - ∑ beta, (∑ gamma, T s a beta gamma * clampBlock R x gamma)
        * clampBlock R x beta)

theorem continuous_riccatiField
    {K : Real -> DegreeIndex d r -> DegreeIndex d r -> Complex}
    {T : Real -> DegreeIndex d r -> DegreeIndex d r -> DegreeIndex d r -> Complex}
    {source : Real -> DegreeBlock d r}
    (hK : ∀ a b, Continuous fun s => K s a b)
    (hT : ∀ a b c, Continuous fun s => T s a b c)
    (hsrc : ∀ a, Continuous fun s => source s a) (R : Real) :
    Continuous (Function.uncurry (riccatiField K T source R)) := by
  have hcl : ∀ b : DegreeIndex d r,
      Continuous fun p : Real × DegreeBlock d r => clampBlock R p.2 b :=
    fun b => (continuous_clampC R).comp ((continuous_apply b).comp continuous_snd)
  refine continuous_pi fun a => ?_
  refine continuous_const.mul (Continuous.sub (Continuous.sub
    ((hsrc a).comp continuous_fst) ?_) ?_)
  · exact continuous_finset_sum _ fun b _ =>
      ((hK a b).comp continuous_fst).mul (hcl b)
  · exact continuous_finset_sum _ fun beta _ =>
      (continuous_finset_sum _ fun gamma _ =>
        ((hT a beta gamma).comp continuous_fst).mul (hcl gamma)).mul (hcl beta)

/-- **The clamped field is globally state-Lipschitz.**  The constant is produced
from the row sums of `K` and the coefficient sums of the quadratic tensor. -/
theorem lipschitz_riccatiField
    (K : Real -> DegreeIndex d r -> DegreeIndex d r -> Complex)
    (T : Real -> DegreeIndex d r -> DegreeIndex d r -> DegreeIndex d r -> Complex)
    (source : Real -> DegreeBlock d r) {R BK BT : Real}
    (hR : 0 ≤ R) (hBK : 0 ≤ BK) (hBT : 0 ≤ BT) (s : Real)
    (hKb : ∀ a : DegreeIndex d r, ∑ b, ‖K s a b‖ ≤ BK)
    (hTb : ∀ a : DegreeIndex d r, ∑ beta, ∑ gamma, ‖T s a beta gamma‖ ≤ BT) :
    LipschitzWith (Real.toNNReal (BK + 4 * R * BT))
      (riccatiField K T source R s) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [Real.coe_toNNReal _ (by positivity)]
  refine (dist_pi_le_iff (by positivity)).2 fun a => ?_
  have hdcl : ∀ b : DegreeIndex d r,
      ‖clampBlock R x b - clampBlock R y b‖ ≤ 2 * dist x y :=
    fun b => dist_clampBlock_apply R x y b
  have hbd : ∀ b : DegreeIndex d r, ‖clampBlock R x b‖ ≤ 2 * R :=
    fun b => norm_clampBlock_le hR x b
  have hbdy : ∀ b : DegreeIndex d r, ‖clampBlock R y b‖ ≤ 2 * R :=
    fun b => norm_clampBlock_le hR y b
  -- the linear part
  have hlin : ‖(∑ b, K s a b * clampBlock R x b)
      - ∑ b, K s a b * clampBlock R y b‖ ≤ BK * (2 * dist x y) := by
    have hterm : ∀ b : DegreeIndex d r,
        K s a b * clampBlock R x b - K s a b * clampBlock R y b
          = K s a b * (clampBlock R x b - clampBlock R y b) := fun b => by ring
    rw [← Finset.sum_sub_distrib _ _]
    refine le_trans (norm_sum_le _ _) ?_
    calc (∑ b, ‖K s a b * clampBlock R x b - K s a b * clampBlock R y b‖)
        ≤ ∑ b, ‖K s a b‖ * (2 * dist x y) := by
          refine Finset.sum_le_sum fun b _ => ?_
          rw [hterm b, norm_mul]
          exact mul_le_mul_of_nonneg_left (hdcl b) (norm_nonneg _)
      _ = (∑ b, ‖K s a b‖) * (2 * dist x y) := by rw [Finset.sum_mul]
      _ ≤ BK * (2 * dist x y) :=
          mul_le_mul_of_nonneg_right (hKb a) (by positivity)
  -- the quadratic part
  have hquad : ‖(∑ beta, (∑ gamma, T s a beta gamma * clampBlock R x gamma)
        * clampBlock R x beta)
      - ∑ beta, (∑ gamma, T s a beta gamma * clampBlock R y gamma)
        * clampBlock R y beta‖
      ≤ BT * (8 * R * dist x y) := by
    rw [← Finset.sum_sub_distrib _ _]
    refine le_trans (norm_sum_le _ _) ?_
    have hterm : ∀ beta : DegreeIndex d r,
        ‖(∑ gamma, T s a beta gamma * clampBlock R x gamma)
            * clampBlock R x beta
          - (∑ gamma, T s a beta gamma * clampBlock R y gamma)
            * clampBlock R y beta‖
        ≤ (∑ gamma, ‖T s a beta gamma‖) * (8 * R * dist x y) := by
      intro beta
      have hsplit : (∑ gamma, T s a beta gamma * clampBlock R x gamma)
            * clampBlock R x beta
          - (∑ gamma, T s a beta gamma * clampBlock R y gamma)
            * clampBlock R y beta
          = ∑ gamma, T s a beta gamma
              * ((clampBlock R x gamma - clampBlock R y gamma)
                  * clampBlock R x beta
                + clampBlock R y gamma
                  * (clampBlock R x beta - clampBlock R y beta)) := by
        rw [Finset.sum_congr rfl fun gamma (_ : gamma ∈ Finset.univ) => by
          ring_nf
          rfl]
        rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun gamma _ => by ring
      rw [hsplit]
      refine le_trans (norm_sum_le _ _) ?_
      refine le_trans (Finset.sum_le_sum (g := fun gamma =>
        ‖T s a beta gamma‖ * (8 * R * dist x y)) fun gamma _ => ?_) ?_
      · rw [norm_mul]
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        refine le_trans (norm_add_le _ _) ?_
        rw [norm_mul, norm_mul]
        have h1 : ‖clampBlock R x gamma - clampBlock R y gamma‖
            * ‖clampBlock R x beta‖ ≤ (2 * dist x y) * (2 * R) :=
          mul_le_mul (hdcl gamma) (hbd beta) (norm_nonneg _) (by positivity)
        have h2 : ‖clampBlock R y gamma‖
            * ‖clampBlock R x beta - clampBlock R y beta‖
            ≤ (2 * R) * (2 * dist x y) :=
          mul_le_mul (hbdy gamma) (hdcl beta) (norm_nonneg _) (by positivity)
        nlinarith [dist_nonneg (x := x) (y := y)]
      · rw [← Finset.sum_mul]
    calc (∑ beta, ‖(∑ gamma, T s a beta gamma * clampBlock R x gamma)
            * clampBlock R x beta
          - (∑ gamma, T s a beta gamma * clampBlock R y gamma)
            * clampBlock R y beta‖)
        ≤ ∑ beta, (∑ gamma, ‖T s a beta gamma‖) * (8 * R * dist x y) :=
          Finset.sum_le_sum fun beta _ => hterm beta
      _ = (∑ beta, ∑ gamma, ‖T s a beta gamma‖) * (8 * R * dist x y) := by
          rw [Finset.sum_mul]
      _ ≤ BT * (8 * R * dist x y) :=
          mul_le_mul_of_nonneg_right (hTb a) (by positivity)
  have hhalf : ‖((2 : Complex))⁻¹‖ = 1 / 2 := by
    rw [norm_inv]
    norm_num
  have hdiff : riccatiField K T source R s x a - riccatiField K T source R s y a
      = ((2 : Complex))⁻¹ *
        (-((∑ b, K s a b * clampBlock R x b)
            - ∑ b, K s a b * clampBlock R y b)
          - ((∑ beta, (∑ gamma, T s a beta gamma * clampBlock R x gamma)
              * clampBlock R x beta)
            - ∑ beta, (∑ gamma, T s a beta gamma * clampBlock R y gamma)
              * clampBlock R y beta)) := by
    rw [riccatiField, riccatiField]
    ring
  rw [dist_eq_norm, hdiff, norm_mul, hhalf]
  have hsum : ‖-((∑ b, K s a b * clampBlock R x b)
        - ∑ b, K s a b * clampBlock R y b)
      - ((∑ beta, (∑ gamma, T s a beta gamma * clampBlock R x gamma)
          * clampBlock R x beta)
        - ∑ beta, (∑ gamma, T s a beta gamma * clampBlock R y gamma)
          * clampBlock R y beta)‖
      ≤ BK * (2 * dist x y) + BT * (8 * R * dist x y) := by
    refine le_trans (norm_sub_le _ _) ?_
    rw [norm_neg]
    exact add_le_add hlin hquad
  nlinarith [dist_nonneg (x := x) (y := y), norm_nonneg
    (-((∑ b, K s a b * clampBlock R x b) - ∑ b, K s a b * clampBlock R y b)
      - ((∑ beta, (∑ gamma, T s a beta gamma * clampBlock R x gamma)
          * clampBlock R x beta)
        - ∑ beta, (∑ gamma, T s a beta gamma * clampBlock R y gamma)
          * clampBlock R y beta))]

/-! ## Uniform bounds, all derived -/

theorem exists_tensor_bound
    {T : Real -> DegreeIndex d r -> DegreeIndex d r -> DegreeIndex d r -> Complex}
    (hT : ∀ a b c, Continuous fun s => T s a b c) (lo hi : Real) :
    ∃ BT : Real, 0 ≤ BT ∧ ∀ s ∈ Icc lo hi, ∀ a : DegreeIndex d r,
      ∑ beta, ∑ gamma, ‖T s a beta gamma‖ ≤ BT := by
  have hF : Continuous fun s => ∑ a : DegreeIndex d r, ∑ beta, ∑ gamma,
      ‖T s a beta gamma‖ :=
    continuous_finset_sum _ fun a _ => continuous_finset_sum _ fun beta _ =>
      continuous_finset_sum _ fun gamma _ => (hT a beta gamma).norm
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := lo) (b := hi)).exists_bound_of_continuousOn
    hF.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun s hs a => ?_⟩
  have h1 : ∑ beta, ∑ gamma, ‖T s a beta gamma‖
      ≤ ∑ a' : DegreeIndex d r, ∑ beta, ∑ gamma, ‖T s a' beta gamma‖ :=
    Finset.single_le_sum
      (f := fun a' : DegreeIndex d r => ∑ beta, ∑ gamma, ‖T s a' beta gamma‖)
      (fun a' _ => Finset.sum_nonneg fun beta _ =>
        Finset.sum_nonneg fun gamma _ => norm_nonneg _) (Finset.mem_univ a)
  have h2 := hC s hs
  rw [Real.norm_eq_abs] at h2
  calc ∑ beta, ∑ gamma, ‖T s a beta gamma‖
      ≤ ∑ a' : DegreeIndex d r, ∑ beta, ∑ gamma, ‖T s a' beta gamma‖ := h1
    _ ≤ |∑ a' : DegreeIndex d r, ∑ beta, ∑ gamma, ‖T s a' beta gamma‖| :=
        le_abs_self _
    _ ≤ C := h2
    _ ≤ max C 0 := le_max_left _ _

theorem exists_source_bound {source : Real -> DegreeBlock d r}
    (hsrc : ∀ a, Continuous fun s => source s a) (lo hi : Real) :
    ∃ BS : Real, 0 ≤ BS ∧ ∀ s ∈ Icc lo hi, ∀ a : DegreeIndex d r,
      ‖source s a‖ ≤ BS := by
  have hF : Continuous fun s => ∑ a : DegreeIndex d r, ‖source s a‖ :=
    continuous_finset_sum _ fun a _ => (hsrc a).norm
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := lo) (b := hi)).exists_bound_of_continuousOn
    hF.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun s hs a => ?_⟩
  have h1 : ‖source s a‖ ≤ ∑ a' : DegreeIndex d r, ‖source s a'‖ :=
    Finset.single_le_sum (f := fun a' : DegreeIndex d r => ‖source s a'‖)
      (fun a' _ => norm_nonneg _) (Finset.mem_univ a)
  have h2 := hC s hs
  rw [Real.norm_eq_abs] at h2
  calc ‖source s a‖ ≤ ∑ a' : DegreeIndex d r, ‖source s a'‖ := h1
    _ ≤ |∑ a' : DegreeIndex d r, ‖source s a'‖| := le_abs_self _
    _ ≤ C := h2
    _ ≤ max C 0 := le_max_left _ _

/-- **The clamped field is globally bounded**, because it factors through the
ball. -/
theorem norm_riccatiField_le
    (K : Real -> DegreeIndex d r -> DegreeIndex d r -> Complex)
    (T : Real -> DegreeIndex d r -> DegreeIndex d r -> DegreeIndex d r -> Complex)
    (source : Real -> DegreeBlock d r) {R BK BT BS : Real}
    (hR : 0 ≤ R) {s : Real}
    (hKb : ∀ a : DegreeIndex d r, ∑ b, ‖K s a b‖ ≤ BK)
    (hTb : ∀ a : DegreeIndex d r, ∑ beta, ∑ gamma, ‖T s a beta gamma‖ ≤ BT)
    (hSb : ∀ a : DegreeIndex d r, ‖source s a‖ ≤ BS)
    (x : DegreeBlock d r) (a : DegreeIndex d r) :
    ‖riccatiField K T source R s x a‖
      ≤ (BS + 2 * R * BK + 4 * R * R * BT) / 2 := by
  have hbd : ∀ b : DegreeIndex d r, ‖clampBlock R x b‖ ≤ 2 * R :=
    fun b => norm_clampBlock_le hR x b
  have hlin : ‖∑ b, K s a b * clampBlock R x b‖ ≤ BK * (2 * R) := by
    refine le_trans (norm_sum_le _ _) ?_
    calc (∑ b, ‖K s a b * clampBlock R x b‖)
        ≤ ∑ b, ‖K s a b‖ * (2 * R) := by
          refine Finset.sum_le_sum fun b _ => ?_
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (hbd b) (norm_nonneg _)
      _ = (∑ b, ‖K s a b‖) * (2 * R) := by rw [Finset.sum_mul]
      _ ≤ BK * (2 * R) := mul_le_mul_of_nonneg_right (hKb a) (by positivity)
  have hquad : ‖∑ beta, (∑ gamma, T s a beta gamma * clampBlock R x gamma)
      * clampBlock R x beta‖ ≤ BT * (4 * R * R) := by
    refine le_trans (norm_sum_le _ _) ?_
    have hterm : ∀ beta : DegreeIndex d r,
        ‖(∑ gamma, T s a beta gamma * clampBlock R x gamma)
          * clampBlock R x beta‖
        ≤ (∑ gamma, ‖T s a beta gamma‖) * (4 * R * R) := by
      intro beta
      rw [norm_mul]
      have hinner : ‖∑ gamma, T s a beta gamma * clampBlock R x gamma‖
          ≤ (∑ gamma, ‖T s a beta gamma‖) * (2 * R) := by
        refine le_trans (norm_sum_le _ _) ?_
        calc (∑ gamma, ‖T s a beta gamma * clampBlock R x gamma‖)
            ≤ ∑ gamma, ‖T s a beta gamma‖ * (2 * R) := by
              refine Finset.sum_le_sum fun gamma _ => ?_
              rw [norm_mul]
              exact mul_le_mul_of_nonneg_left (hbd gamma) (norm_nonneg _)
          _ = (∑ gamma, ‖T s a beta gamma‖) * (2 * R) := by rw [Finset.sum_mul]
      have hsum_nonneg : 0 ≤ ∑ gamma, ‖T s a beta gamma‖ :=
        Finset.sum_nonneg fun gamma _ => norm_nonneg _
      nlinarith [hbd beta, norm_nonneg
        (∑ gamma, T s a beta gamma * clampBlock R x gamma)]
    calc (∑ beta, ‖(∑ gamma, T s a beta gamma * clampBlock R x gamma)
          * clampBlock R x beta‖)
        ≤ ∑ beta, (∑ gamma, ‖T s a beta gamma‖) * (4 * R * R) :=
          Finset.sum_le_sum fun beta _ => hterm beta
      _ = (∑ beta, ∑ gamma, ‖T s a beta gamma‖) * (4 * R * R) := by
          rw [Finset.sum_mul]
      _ ≤ BT * (4 * R * R) := mul_le_mul_of_nonneg_right (hTb a) (by positivity)
  have hhalf : ‖((2 : Complex))⁻¹‖ = 1 / 2 := by
    rw [norm_inv]
    norm_num
  show ‖((2 : Complex))⁻¹ * (source s a - ∑ b, K s a b * clampBlock R x b
    - ∑ beta, (∑ gamma, T s a beta gamma * clampBlock R x gamma)
        * clampBlock R x beta)‖ ≤ _
  rw [norm_mul, hhalf]
  have htot : ‖source s a - ∑ b, K s a b * clampBlock R x b
      - ∑ beta, (∑ gamma, T s a beta gamma * clampBlock R x gamma)
        * clampBlock R x beta‖
      ≤ BS + BK * (2 * R) + BT * (4 * R * R) := by
    refine le_trans (norm_sub_le _ _) ?_
    refine add_le_add (le_trans (norm_sub_le _ _) (add_le_add (hSb a) hlin)) hquad
  linarith

/-! ## Local existence for the actual quadratic equation -/

/-- **A solution of the actual degree-two Riccati equation, on an explicit
window around the initial parameter.**  The clamped equation is solved on the
whole interval by the repository's Picard iteration; a mean value estimate then
confines the path to the ball on which the clamp is the identity, and there the
path satisfies the *unclamped* quadratic equation.  The window length is
produced by the proof, not assumed. -/
theorem exists_riccatiSolution
    (K : Real -> DegreeIndex d r -> DegreeIndex d r -> Complex)
    (T : Real -> DegreeIndex d r -> DegreeIndex d r -> DegreeIndex d r -> Complex)
    (source : Real -> DegreeBlock d r)
    (hK : ∀ a b, Continuous fun s => K s a b)
    (hT : ∀ a b c, Continuous fun s => T s a b c)
    (hsrc : ∀ a, Continuous fun s => source s a)
    {lo hi : Real} (t0 : Icc lo hi) (x0 : DegreeBlock d r) :
    ∃ (delta : Real) (c : Real -> DegreeBlock d r),
      0 < delta ∧ c t0 = x0 ∧ Continuous c ∧
      ∀ t ∈ Icc lo hi, |t - (t0 : Real)| ≤ delta ->
        HasDerivWithinAt c
          (fun a => ((2 : Complex))⁻¹ * (source t a - ∑ b, K t a b * c t b
            - ∑ beta, (∑ gamma, T t a beta gamma * c t gamma) * c t beta))
          (Icc lo hi) t := by
  obtain ⟨BK, hBKnn, hKb⟩ := exists_rowSum_bound hK lo hi
  obtain ⟨BT, hBTnn, hTb⟩ := exists_tensor_bound hT lo hi
  obtain ⟨BS, hBSnn, hSb⟩ := exists_source_bound hsrc lo hi
  obtain ⟨R, hRdef⟩ : ∃ R : Real, R = ‖x0‖ + 1 := ⟨_, rfl⟩
  have hx0nn : (0 : Real) ≤ ‖x0‖ := norm_nonneg _
  have hRnn : 0 ≤ R := by rw [hRdef]; linarith
  obtain ⟨M, hMdef⟩ : ∃ M : Real, M = (BS + 2 * R * BK + 4 * R * R * BT) / 2 :=
    ⟨_, rfl⟩
  have hMnn : 0 ≤ M := by
    rw [hMdef]
    have h1 : 0 ≤ 2 * R * BK := by positivity
    have h2 : 0 ≤ 4 * R * R * BT := by positivity
    linarith
  obtain ⟨c, hc0, hccont, hcderiv⟩ :=
    CompactIntervalLipschitzODE.exists_solution t0 (riccatiField K T source R)
      (continuous_riccatiField hK hT hsrc R).continuousOn
      (Real.toNNReal (BK + 4 * R * BT))
      (fun t ht => lipschitz_riccatiField K T source hRnn hBKnn hBTnn t
        (hKb t ht) (hTb t ht))
      x0
  have hfieldbd : ∀ t ∈ Icc lo hi, ∀ x : DegreeBlock d r,
      ‖riccatiField K T source R t x‖ ≤ M := by
    intro t ht x
    refine (pi_norm_le_iff_of_nonneg hMnn).2 fun a => ?_
    rw [hMdef]
    exact norm_riccatiField_le K T source hRnn (hKb t ht) (hTb t ht)
      (hSb t ht) x a
  have hmvt : ∀ t ∈ Icc lo hi, ‖c t - c t0‖ ≤ M * ‖t - (t0 : Real)‖ :=
    fun t ht => (convex_Icc lo hi).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun w hw => hcderiv w hw) (fun w hw => hfieldbd w hw (c w)) t0.2 ht
  refine ⟨1 / (M + 1), c, by positivity, hc0, hccont, ?_⟩
  intro t ht hdist
  have hball : ∀ a : DegreeIndex d r, ‖c t a‖ ≤ R := by
    intro a
    have h1 : ‖c t a - c t0 a‖ ≤ ‖c t - c t0‖ := norm_le_pi_norm (c t - c t0) a
    have h2 : ‖c t0 a‖ ≤ ‖x0‖ := by
      rw [hc0]
      exact norm_le_pi_norm x0 a
    have h3 : M * ‖t - (t0 : Real)‖ ≤ 1 := by
      rw [Real.norm_eq_abs]
      have hstep : M * |t - (t0 : Real)| ≤ M * (1 / (M + 1)) :=
        mul_le_mul_of_nonneg_left hdist hMnn
      have hfrac : M * (1 / (M + 1)) ≤ 1 := by
        rw [mul_one_div, div_le_one (by linarith)]
        linarith
      linarith
    have h4 := hmvt t ht
    have heq : c t a = (c t a - c t0 a) + c t0 a := by ring
    have h5 : ‖c t a‖ ≤ ‖c t a - c t0 a‖ + ‖c t0 a‖ := by
      calc ‖c t a‖ = ‖(c t a - c t0 a) + c t0 a‖ := by rw [← heq]
        _ ≤ ‖c t a - c t0 a‖ + ‖c t0 a‖ := norm_add_le _ _
    rw [hRdef]
    linarith
  have hcl : clampBlock R (c t) = c t := clampBlock_eq_self hball
  have hfield : riccatiField K T source R t (c t)
      = fun a => ((2 : Complex))⁻¹ * (source t a - ∑ b, K t a b * c t b
        - ∑ beta, (∑ gamma, T t a beta gamma * c t gamma) * c t beta) := by
    funext a
    show ((2 : Complex))⁻¹ * (source t a
        - ∑ b, K t a b * clampBlock R (c t) b
        - ∑ beta, (∑ gamma, T t a beta gamma * clampBlock R (c t) gamma)
            * clampBlock R (c t) beta) = _
    rw [hcl]
  rw [← hfield]
  exact hcderiv t ht

end LiuWang2025SemilinearWaveRiccatiODE
