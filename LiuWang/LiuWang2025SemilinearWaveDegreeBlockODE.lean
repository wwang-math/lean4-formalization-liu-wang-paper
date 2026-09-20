import LiuWang.LiuWang2025SemilinearWaveDegreeBlock
import LiuWang.CompactIntervalLipschitzODE

/-!
# Liu-Wang semilinear wave: the homogeneous block ODE

At fixed transverse degree the source's eikonal equation is the affine linear
system

  `2 c_r'(s) + K(s) c_r(s) = source(s)`

on the finite dimensional space `DegreeBlock d r`, with `K(s)` the same-degree
operator induced by the transverse block of the metric and the quadratic phase.
It is a genuine system, not a family of scalar equations, because `K(s)` mixes
distinct multi-indices of the same total degree.

This file solves it.  The solution is *constructed* by the repository's
compact-interval Picard iteration
(`CompactIntervalLipschitzODE.exists_solution`), which needs a globally
state-Lipschitz field; for an affine field with uniformly bounded row sums that
bound is elementary and is proved here.  The vector field's continuity, its
Lipschitz constant, the existence of the path, its initial value and the block
equation it satisfies are all theorems -- none of them is an input.
-/

noncomputable section

open scoped BigOperators
open Set

namespace LiuWang2025SemilinearWaveDegreeBlockODE

open LiuWang2025SemilinearWaveTransverseJet
open LiuWang2025SemilinearWaveDegreeBlock

variable {d r : Nat}

/-- The affine vector field of `2 c' + K c = source`, solved for `c'`. -/
def blockField (K : Real -> DegreeIndex d r -> DegreeIndex d r -> Complex)
    (source : Real -> DegreeBlock d r) (s : Real) (x : DegreeBlock d r) :
    DegreeBlock d r :=
  fun a => ((2 : Complex))⁻¹ * (source s a - ∑ b, K s a b * x b)

/-- **The vector field is continuous.** -/
theorem continuous_blockField
    {K : Real -> DegreeIndex d r -> DegreeIndex d r -> Complex}
    {source : Real -> DegreeBlock d r}
    (hK : ∀ a b, Continuous fun s => K s a b)
    (hsrc : ∀ a, Continuous fun s => source s a) :
    Continuous (Function.uncurry (blockField K source)) := by
  refine continuous_pi fun a => ?_
  refine continuous_const.mul (Continuous.sub ((hsrc a).comp continuous_fst) ?_)
  refine continuous_finset_sum _ fun b _ => ?_
  exact ((hK a b).comp continuous_fst).mul
    ((continuous_apply b).comp continuous_snd)

/-- **A global state-Lipschitz bound from the row sums of `K`.**  On the finite
dimensional block the supremum norm turns the matrix bound directly into a
Lipschitz constant. -/
theorem lipschitz_blockField
    (K : Real -> DegreeIndex d r -> DegreeIndex d r -> Complex)
    (source : Real -> DegreeBlock d r) {B : Real} (hBnn : 0 ≤ B) (s : Real)
    (hKb : ∀ a : DegreeIndex d r, ∑ b, ‖K s a b‖ ≤ B) :
    LipschitzWith (Real.toNNReal (B / 2)) (blockField K source s) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [Real.coe_toNNReal _ (by positivity)]
  refine (dist_pi_le_iff (by positivity)).2 fun a => ?_
  have heq : blockField K source s x a - blockField K source s y a
      = ((2 : Complex))⁻¹ * ∑ b, K s a b * (y b - x b) := by
    have hterm : ∀ b : DegreeIndex d r,
        K s a b * (y b - x b) = K s a b * y b - K s a b * x b := fun b => by ring
    rw [blockField, blockField,
      Finset.sum_congr rfl fun b (_ : b ∈ Finset.univ) => hterm b,
      Finset.sum_sub_distrib]
    ring
  rw [dist_eq_norm, heq, norm_mul]
  have hhalf : ‖((2 : Complex))⁻¹‖ = 1 / 2 := by
    rw [norm_inv]
    norm_num
  have hbound : ‖∑ b, K s a b * (y b - x b)‖ ≤ B * dist x y := by
    refine le_trans (norm_sum_le _ _) ?_
    have hterm : ∀ b ∈ (Finset.univ : Finset (DegreeIndex d r)),
        ‖K s a b * (y b - x b)‖ ≤ ‖K s a b‖ * dist x y := by
      intro b _
      rw [norm_mul]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      rw [← dist_eq_norm, dist_comm]
      exact dist_le_pi_dist x y b
    calc (∑ b, ‖K s a b * (y b - x b)‖)
        ≤ ∑ b, ‖K s a b‖ * dist x y := Finset.sum_le_sum hterm
      _ = (∑ b, ‖K s a b‖) * dist x y := by rw [Finset.sum_mul]
      _ ≤ B * dist x y := mul_le_mul_of_nonneg_right (hKb a) dist_nonneg
  rw [hhalf]
  calc 1 / 2 * ‖∑ b, K s a b * (y b - x b)‖
      ≤ 1 / 2 * (B * dist x y) :=
        mul_le_mul_of_nonneg_left hbound (by norm_num)
    _ = B / 2 * dist x y := by ring

/-- **The block solution exists**, on the whole prescribed compact interval and
with the prescribed initial value.  Constructed by Picard iteration, not
assumed. -/
theorem exists_blockSolution
    (K : Real -> DegreeIndex d r -> DegreeIndex d r -> Complex)
    (source : Real -> DegreeBlock d r)
    (hK : ∀ a b, Continuous fun s => K s a b)
    (hsrc : ∀ a, Continuous fun s => source s a)
    {B : Real} (hBnn : 0 ≤ B) {lo hi : Real}
    (hKb : ∀ s ∈ Icc lo hi, ∀ a : DegreeIndex d r, ∑ b, ‖K s a b‖ ≤ B)
    (t0 : Icc lo hi) (x0 : DegreeBlock d r) :
    ∃ c : Real -> DegreeBlock d r,
      c t0 = x0 ∧ Continuous c ∧
        ∀ t ∈ Icc lo hi,
          HasDerivWithinAt c (blockField K source t (c t)) (Icc lo hi) t :=
  CompactIntervalLipschitzODE.exists_solution t0 (blockField K source)
    (continuous_blockField hK hsrc).continuousOn (Real.toNNReal (B / 2))
    (fun t ht => lipschitz_blockField K source hBnn t (hKb t ht)) x0

/-- **The block equation, coordinatewise.**  Whatever the constructed path is,
its derivative satisfies `2 c' + K c = source` at every index. -/
theorem blockField_equation
    (K : Real -> DegreeIndex d r -> DegreeIndex d r -> Complex)
    (source : Real -> DegreeBlock d r) (s : Real) (x : DegreeBlock d r)
    (a : DegreeIndex d r) :
    2 * blockField K source s x a + ∑ b, K s a b * x b = source s a := by
  rw [blockField]
  field_simp
  ring

/-! ## From an interval solution to a globally differentiable one

`exists_blockSolution` produces a path differentiable *within* the compact
interval, while the repository's jet structures demand a derivative at every
real parameter.  Using the former as if it were the latter would be a genuine
gap, so it is closed here by an honest construction: the vector field is frozen
outside the interval (composing with the continuous clamp), and the global path
is defined as the primitive of that frozen field.  The fundamental theorem of
calculus gives a derivative at *every* real number, and the mean value
inequality shows the primitive coincides with the interval solution on the
interval itself.  No interval derivative is ever used as a global one.
-/

/-- Clamp a real parameter to the paper interval. -/
def clamp (lo hi t : Real) : Real := max lo (min hi t)

theorem continuous_clamp (lo hi : Real) : Continuous (clamp lo hi) :=
  continuous_const.max (continuous_const.min continuous_id)

theorem clamp_eq_self {lo hi t : Real} (ht : t ∈ Icc lo hi) : clamp lo hi t = t := by
  rw [clamp, min_eq_right ht.2, max_eq_right ht.1]

theorem clamp_mem {lo hi : Real} (h : lo ≤ hi) (t : Real) :
    clamp lo hi t ∈ Icc lo hi :=
  ⟨le_max_left _ _, max_le h (min_le_left _ _)⟩

/-- The block vector field evaluated along a path, frozen outside the paper
interval.  This is continuous on all of `Real`. -/
def clampedField (K : Real -> DegreeIndex d r -> DegreeIndex d r -> Complex)
    (source : Real -> DegreeBlock d r) (lo hi : Real)
    (u : Real -> DegreeBlock d r) (t : Real) : DegreeBlock d r :=
  blockField K source (clamp lo hi t) (u (clamp lo hi t))

theorem continuous_clampedField
    {K : Real -> DegreeIndex d r -> DegreeIndex d r -> Complex}
    {source : Real -> DegreeBlock d r}
    (hK : ∀ a b, Continuous fun s => K s a b)
    (hsrc : ∀ a, Continuous fun s => source s a) (lo hi : Real)
    {u : Real -> DegreeBlock d r} (hu : Continuous u) :
    Continuous (clampedField K source lo hi u) :=
  (continuous_blockField hK hsrc).comp
    ((continuous_clamp lo hi).prodMk (hu.comp (continuous_clamp lo hi)))

/-- **The block solution, globally differentiable.**  There is a path defined on
all of `Real`, differentiable at every real parameter in every coordinate, whose
derivative on the paper interval satisfies the block equation
`2 c' + K c = source` and which takes the prescribed initial value. -/
theorem exists_global_blockSolution
    (K : Real -> DegreeIndex d r -> DegreeIndex d r -> Complex)
    (source : Real -> DegreeBlock d r)
    (hK : ∀ a b, Continuous fun s => K s a b)
    (hsrc : ∀ a, Continuous fun s => source s a)
    {B : Real} (hBnn : 0 ≤ B) {lo hi : Real}
    (hKb : ∀ s ∈ Icc lo hi, ∀ a : DegreeIndex d r, ∑ b, ‖K s a b‖ ≤ B)
    (t0 : Icc lo hi) (x0 : DegreeBlock d r) :
    ∃ c c' : Real -> DegreeBlock d r,
      c t0 = x0 ∧ Continuous c ∧
      (∀ (a : DegreeIndex d r) (t : Real),
        HasDerivAt (fun v => c v a) (c' t a) t) ∧
      (∀ t ∈ Icc lo hi, ∀ a : DegreeIndex d r,
        2 * c' t a + ∑ b, K t a b * c t b = source t a) := by
  obtain ⟨u, hu0, hucont, huderiv⟩ :=
    exists_blockSolution K source hK hsrc hBnn hKb t0 x0
  have hGcont : Continuous (clampedField K source lo hi u) :=
    continuous_clampedField hK hsrc lo hi hucont
  -- the primitive of the frozen field, differentiable at every real parameter
  have hprim : ∀ t : Real,
      HasDerivAt (fun y => x0 + ∫ v in (t0 : Real)..y, clampedField K source lo hi u v)
        (clampedField K source lo hi u t) t := by
    intro t
    exact (intervalIntegral.integral_hasDerivAt_right
      (hGcont.intervalIntegrable _ _)
      hGcont.stronglyMeasurable.stronglyMeasurableAtFilter
      hGcont.continuousAt).const_add x0
  -- on the interval the frozen field is the true field along `u`
  have hfield : ∀ t ∈ Icc lo hi,
      clampedField K source lo hi u t = blockField K source t (u t) := by
    intro t ht
    rw [clampedField, clamp_eq_self ht]
  -- the primitive agrees with the interval solution on the interval
  have hagree : ∀ t ∈ Icc lo hi,
      x0 + ∫ v in (t0 : Real)..t, clampedField K source lo hi u v = u t := by
    intro t ht
    have hderiv : ∀ w ∈ Icc lo hi,
        HasDerivWithinAt
          (fun y => (x0 + ∫ v in (t0 : Real)..y, clampedField K source lo hi u v) - u y)
          0 (Icc lo hi) w := by
      intro w hw
      have h1 := (hprim w).hasDerivWithinAt (s := Icc lo hi)
      rw [hfield w hw] at h1
      simpa using h1.sub (huderiv w hw)
    have hbd : ∀ w ∈ Icc lo hi, ‖(0 : DegreeBlock d r)‖ ≤ 0 := by
      intro w _
      simp
    have hmvt := (convex_Icc lo hi).norm_image_sub_le_of_norm_hasDerivWithin_le
      hderiv hbd t0.2 ht
    have hzero : (x0 + ∫ v in (t0 : Real)..(t0 : Real),
        clampedField K source lo hi u v) - u t0 = 0 := by
      rw [intervalIntegral.integral_same, add_zero, hu0, sub_self]
    rw [hzero, sub_zero, zero_mul] at hmvt
    exact sub_eq_zero.1 (norm_le_zero_iff.1 hmvt)
  refine ⟨fun t => x0 + ∫ v in (t0 : Real)..t, clampedField K source lo hi u v,
    clampedField K source lo hi u, ?_, ?_, ?_, ?_⟩
  · simp only []
    rw [intervalIntegral.integral_same, add_zero]
  · exact continuous_iff_continuousAt.2 fun t => (hprim t).continuousAt
  · intro a t
    exact hasDerivAt_pi.1 (hprim t) a
  · intro t ht a
    simp only []
    rw [hagree t ht, hfield t ht]
    exact blockField_equation K source t (u t) a

/-! ## A twice differentiable block solution

`LongJet` carries a derivative certificate, and `SourcePhaseJet` stores the
longitudinal derivative as a second `LongJet`.  A phase block must therefore be
twice differentiable at *every* real parameter, not once.  The construction
below produces that: the second derivative is prescribed first (as a globally
continuous field obtained by differentiating the block equation), the first
derivative and the path are then its iterated primitives, and the mean value
inequality identifies both with the Picard solution on the paper interval.
-/

/-- Two functions with a common derivative on the interval and a common value
somewhere on it agree on it. -/
theorem eq_of_hasDerivWithinAt_eq {E : Type*} [NormedAddCommGroup E]
    [NormedSpace Real E] {f g F : Real -> E} {lo hi t0 : Real}
    (ht0 : t0 ∈ Icc lo hi) (hfg0 : f t0 = g t0)
    (hf : ∀ t ∈ Icc lo hi, HasDerivWithinAt f (F t) (Icc lo hi) t)
    (hg : ∀ t ∈ Icc lo hi, HasDerivWithinAt g (F t) (Icc lo hi) t) :
    ∀ t ∈ Icc lo hi, f t = g t := by
  intro t ht
  have hderiv : ∀ w ∈ Icc lo hi,
      HasDerivWithinAt (fun y => f y - g y) 0 (Icc lo hi) w := by
    intro w hw
    simpa using (hf w hw).sub (hg w hw)
  have hbd : ∀ w ∈ Icc lo hi, ‖(0 : E)‖ ≤ 0 := fun w _ => by simp
  have hmvt := (convex_Icc lo hi).norm_image_sub_le_of_norm_hasDerivWithin_le
    hderiv hbd ht0 ht
  rw [hfg0, sub_self, sub_zero, zero_mul] at hmvt
  exact sub_eq_zero.1 (norm_le_zero_iff.1 hmvt)

/-- The second-order field: the longitudinal derivative of `blockField` along a
path that satisfies the block equation. -/
def secondField (K dK : Real -> DegreeIndex d r -> DegreeIndex d r -> Complex)
    (source dsource : Real -> DegreeBlock d r) (s : Real) (x : DegreeBlock d r) :
    DegreeBlock d r :=
  fun a => ((2 : Complex))⁻¹ * (dsource s a - ∑ b, dK s a b * x b
    - ∑ b, K s a b * blockField K source s x b)

theorem continuous_secondField
    {K dK : Real -> DegreeIndex d r -> DegreeIndex d r -> Complex}
    {source dsource : Real -> DegreeBlock d r}
    (hK : ∀ a b, Continuous fun s => K s a b)
    (hdK : ∀ a b, Continuous fun s => dK s a b)
    (hsrc : ∀ a, Continuous fun s => source s a)
    (hdsrc : ∀ a, Continuous fun s => dsource s a) :
    Continuous (Function.uncurry (secondField K dK source dsource)) := by
  refine continuous_pi fun a => ?_
  refine continuous_const.mul (Continuous.sub (Continuous.sub
    ((hdsrc a).comp continuous_fst) ?_) ?_)
  · exact continuous_finset_sum _ fun b _ =>
      ((hdK a b).comp continuous_fst).mul ((continuous_apply b).comp continuous_snd)
  · exact continuous_finset_sum _ fun b _ =>
      ((hK a b).comp continuous_fst).mul
        ((continuous_apply b).comp (continuous_blockField hK hsrc))

/-- **`secondField` is the derivative of `blockField` along a solution.** -/
theorem hasDerivWithinAt_blockField_along
    {K dK : Real -> DegreeIndex d r -> DegreeIndex d r -> Complex}
    {source dsource : Real -> DegreeBlock d r}
    {u : Real -> DegreeBlock d r} {S : Set Real} {t : Real}
    (hKd : ∀ a b s, HasDerivAt (fun v => K v a b) (dK s a b) s)
    (hsrcd : ∀ a s, HasDerivAt (fun v => source v a) (dsource s a) s)
    (hu : HasDerivWithinAt u (blockField K source t (u t)) S t) :
    HasDerivWithinAt (fun v => blockField K source v (u v))
      (secondField K dK source dsource t (u t)) S t := by
  refine hasDerivWithinAt_pi.2 fun a => ?_
  have hub : ∀ b : DegreeIndex d r,
      HasDerivWithinAt (fun v => u v b) (blockField K source t (u t) b) S t :=
    fun b => hasDerivWithinAt_pi.1 hu b
  have hsum : HasDerivWithinAt (fun v => ∑ b, K v a b * u v b)
      (∑ b, (dK t a b * u t b
        + K t a b * blockField K source t (u t) b)) S t := by
    have hsum0 := HasDerivWithinAt.sum
      (A := fun (b : DegreeIndex d r) (v : Real) => K v a b * u v b)
      (A' := fun b => dK t a b * u t b
        + K t a b * blockField K source t (u t) b)
      (u := (Finset.univ : Finset (DegreeIndex d r)))
      (fun b _ => ((hKd a b t).hasDerivWithinAt).mul (hub b))
    have hfun : (∑ b : DegreeIndex d r, fun v : Real => K v a b * u v b)
        = fun v => ∑ b : DegreeIndex d r, K v a b * u v b := by
      funext v
      rw [Finset.sum_apply]
    rw [hfun] at hsum0
    exact hsum0
  have hmain := (((hsrcd a t).hasDerivWithinAt).sub hsum).const_mul ((2 : Complex))⁻¹
  have hsplit : ∑ b : DegreeIndex d r,
      (dK t a b * u t b + K t a b * blockField K source t (u t) b)
      = (∑ b, dK t a b * u t b)
        + ∑ b, K t a b * blockField K source t (u t) b := Finset.sum_add_distrib
  rw [hsplit] at hmain
  refine hmain.congr_deriv ?_
  show ((2 : Complex))⁻¹ * (dsource t a
      - ((∑ b, dK t a b * u t b)
        + ∑ b, K t a b * blockField K source t (u t) b))
    = secondField K dK source dsource t (u t) a
  rw [secondField]
  ring

/-- **The block solution, twice differentiable at every real parameter.**  It
satisfies the block equation `2 c' + K c = source` on the paper interval, takes
the prescribed initial value, and its first and second derivatives are
certified everywhere -- exactly the data `LongJet` and `SourcePhaseJet`
require. -/
theorem exists_c2_blockSolution
    (K dK : Real -> DegreeIndex d r -> DegreeIndex d r -> Complex)
    (source dsource : Real -> DegreeBlock d r)
    (hKd : ∀ a b s, HasDerivAt (fun v => K v a b) (dK s a b) s)
    (hdK : ∀ a b, Continuous fun s => dK s a b)
    (hsrcd : ∀ a s, HasDerivAt (fun v => source v a) (dsource s a) s)
    (hdsrc : ∀ a, Continuous fun s => dsource s a)
    {B : Real} (hBnn : 0 ≤ B) {lo hi : Real}
    (hKb : ∀ s ∈ Icc lo hi, ∀ a : DegreeIndex d r, ∑ b, ‖K s a b‖ ≤ B)
    (t0 : Icc lo hi) (x0 : DegreeBlock d r) :
    ∃ c c' c'' : Real -> DegreeBlock d r,
      c t0 = x0 ∧
      (∀ (a : DegreeIndex d r) (t : Real),
        HasDerivAt (fun v => c v a) (c' t a) t) ∧
      (∀ (a : DegreeIndex d r) (t : Real),
        HasDerivAt (fun v => c' v a) (c'' t a) t) ∧
      (∀ a : DegreeIndex d r, Continuous fun t => c'' t a) ∧
      (∀ t ∈ Icc lo hi, ∀ a : DegreeIndex d r,
        2 * c' t a + ∑ b, K t a b * c t b = source t a) := by
  have hK : ∀ a b, Continuous fun s => K s a b :=
    fun a b => continuous_iff_continuousAt.2 fun s => (hKd a b s).continuousAt
  have hsrc : ∀ a, Continuous fun s => source s a :=
    fun a => continuous_iff_continuousAt.2 fun s => (hsrcd a s).continuousAt
  obtain ⟨u, hu0, hucont, huderiv⟩ :=
    exists_blockSolution K source hK hsrc hBnn hKb t0 x0
  obtain ⟨H, hHdef⟩ : ∃ H : Real -> DegreeBlock d r, H = fun t =>
      secondField K dK source dsource (clamp lo hi t) (u (clamp lo hi t)) :=
    ⟨_, rfl⟩
  have hHcont : Continuous H := by
    rw [hHdef]
    exact (continuous_secondField hK hdK hsrc hdsrc).comp
      ((continuous_clamp lo hi).prodMk (hucont.comp (continuous_clamp lo hi)))
  obtain ⟨V, hVdef⟩ : ∃ V : Real -> DegreeBlock d r, V = fun t =>
      blockField K source (t0 : Real) x0 + ∫ v in (t0 : Real)..t, H v := ⟨_, rfl⟩
  have hVderiv : ∀ t : Real, HasDerivAt V (H t) t := by
    intro t
    rw [hVdef]
    exact (intervalIntegral.integral_hasDerivAt_right
      (hHcont.intervalIntegrable _ _)
      hHcont.stronglyMeasurable.stronglyMeasurableAtFilter
      hHcont.continuousAt).const_add _
  have hVcont : Continuous V :=
    continuous_iff_continuousAt.2 fun t => (hVderiv t).continuousAt
  obtain ⟨C, hCdef⟩ : ∃ C : Real -> DegreeBlock d r, C = fun t =>
      x0 + ∫ v in (t0 : Real)..t, V v := ⟨_, rfl⟩
  have hCderiv : ∀ t : Real, HasDerivAt C (V t) t := by
    intro t
    rw [hCdef]
    exact (intervalIntegral.integral_hasDerivAt_right
      (hVcont.intervalIntegrable _ _)
      hVcont.stronglyMeasurable.stronglyMeasurableAtFilter
      hVcont.continuousAt).const_add _
  -- on the interval the clamped second-order field is the true one
  have hHeq : ∀ t ∈ Icc lo hi, H t = secondField K dK source dsource t (u t) := by
    intro t ht
    rw [hHdef]
    simp only []
    rw [clamp_eq_self ht]
  -- the first derivative agrees with the field along the Picard solution
  have hVeq : ∀ t ∈ Icc lo hi, V t = blockField K source t (u t) := by
    refine eq_of_hasDerivWithinAt_eq (F := H) t0.2 ?_ (fun t ht => (hVderiv t).hasDerivWithinAt)
      (fun t ht => ?_)
    · rw [hVdef]
      simp only []
      rw [intervalIntegral.integral_same, add_zero, hu0]
    · rw [hHeq t ht]
      exact hasDerivWithinAt_blockField_along hKd hsrcd (huderiv t ht)
  -- hence the path agrees with the Picard solution
  have hCeq : ∀ t ∈ Icc lo hi, C t = u t := by
    refine eq_of_hasDerivWithinAt_eq (F := fun t => blockField K source t (u t))
      t0.2 ?_ (fun t ht => ?_) (fun t ht => huderiv t ht)
    · rw [hCdef]
      simp only []
      rw [intervalIntegral.integral_same, add_zero, hu0]
    · simp only []
      rw [← hVeq t ht]
      exact (hCderiv t).hasDerivWithinAt
  refine ⟨C, V, H, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hCdef]
    simp only []
    rw [intervalIntegral.integral_same, add_zero]
  · exact fun a t => hasDerivAt_pi.1 (hCderiv t) a
  · exact fun a t => hasDerivAt_pi.1 (hVderiv t) a
  · exact fun a => (continuous_apply a).comp hHcont
  · intro t ht a
    rw [hCeq t ht, hVeq t ht]
    exact blockField_equation K source t (u t) a

/-- **A uniform nonnegative row-sum bound is automatic** on a compact interval
for a continuous matrix: the caller never has to supply one. -/
theorem exists_rowSum_bound
    {K : Real -> DegreeIndex d r -> DegreeIndex d r -> Complex}
    (hK : ∀ a b, Continuous fun s => K s a b) (lo hi : Real) :
    ∃ B : Real, 0 ≤ B ∧
      ∀ s ∈ Icc lo hi, ∀ a : DegreeIndex d r, ∑ b, ‖K s a b‖ ≤ B := by
  have hF : Continuous fun s => ∑ a : DegreeIndex d r, ∑ b, ‖K s a b‖ :=
    continuous_finset_sum _ fun a _ =>
      continuous_finset_sum _ fun b _ => (hK a b).norm
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := lo) (b := hi)).exists_bound_of_continuousOn
    hF.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun s hs a => ?_⟩
  have h1 : ∑ b, ‖K s a b‖ ≤ ∑ a' : DegreeIndex d r, ∑ b, ‖K s a' b‖ :=
    Finset.single_le_sum (f := fun a' : DegreeIndex d r => ∑ b, ‖K s a' b‖)
      (fun a' _ => Finset.sum_nonneg fun b _ => norm_nonneg _) (Finset.mem_univ a)
  have h2 := hC s hs
  rw [Real.norm_eq_abs] at h2
  calc ∑ b, ‖K s a b‖
      ≤ ∑ a' : DegreeIndex d r, ∑ b, ‖K s a' b‖ := h1
    _ ≤ |∑ a' : DegreeIndex d r, ∑ b, ‖K s a' b‖| := le_abs_self _
    _ ≤ C := h2
    _ ≤ max C 0 := le_max_left _ _

end LiuWang2025SemilinearWaveDegreeBlockODE
