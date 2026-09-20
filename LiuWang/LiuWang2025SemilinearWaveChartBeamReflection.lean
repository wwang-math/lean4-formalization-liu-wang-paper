import LiuWang.LiuWang2025SemilinearWaveChartBeamProfile
import LiuWang.LiuWang2025SemilinearWaveBoundaryReflection
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Liu-Wang semilinear wave: reflecting the constructed chart beam

This file does the two things Subsection 3.2 of the source needs, for the beam
that `LiuWang2025SemilinearWaveChartWKB` actually constructs.

## The reflection

`chartReflection i0` presents the coordinate reflection of the chart as a
`LiuWang2025SemilinearWaveBoundaryReflection.BoundaryReflection`, so the
existing variable-geometry reflection argument applies verbatim: the incident
minus reflected beam has vanishing Dirichlet trace on the face, all its
tangential derivatives vanish there, and its normal derivative doubles.  No new
reflection theory is introduced.  `ChartJet.comp_reflect` upgrades this to the
jet level, so the reflected beam is again a `ChartJet` and `waveOp` applies to
it; the reflected jet's residual therefore inherits the constructed rate.

## The boundary rate, derived

The source matches the incident and reflected phases to order `N + 1` at the
reflection point and then estimates `exp (i rho phi^inc) - exp (i rho phi^ref)`.
`norm_exp_sub_exp_le` proves the underlying complex estimate from the mean value
inequality, and `expPhaseDifference_radiusProfileBound` turns the order-`N+1`
phase matching plus the transverse coercivity of the two phases into a genuine
`RadiusProfileBound` with constant `C * rho`, weight `N + 1` and Gaussian width
`b * rho`.  That is exactly the `k = 1`, `j = 1` slot of the source's displayed
splitting `k + j = |alpha|`, so `reflectedBoundaryTerm_L2_rate` consumes it and
returns the boundary Sobolev rate.  The rate is computed, not assumed: the only
inputs are the phase matching and the coercivity.

The exponent obtained is the source's `rho^{-(N - |alpha| + 1)/2 - d/4}` at
`|alpha| = 2`, i.e. `rho^{-(N-1)/2 - d/4}`; the frequency power produced by
differentiating the exponential is what occupies two of the source's slots.
-/

noncomputable section

open scoped BigOperators

namespace LiuWang2025SemilinearWaveChartBeamReflection

open LiuWang2025SemilinearWaveChartWKB
open LiuWang2025SemilinearWaveChartWKB.ChartJet
open LiuWang2025SemilinearWaveGaussianL2Bridge
open LiuWang2025SemilinearWaveGaussianMassScaling (radiusSq)
open LiuWang2025SemilinearWaveBoundaryReflection

/-! ## The coordinate reflection as a `BoundaryReflection` -/

variable {n : Nat}

/-- The coordinate reflection of the chart, as a continuous linear map. -/
def chartReflectCLM (i0 : Fin n) : (Fin n -> Real) →L[Real] (Fin n -> Real) :=
  ContinuousLinearMap.pi fun i =>
    (if i = i0 then (-1 : Real) else 1) • ContinuousLinearMap.proj i

@[simp] theorem chartReflectCLM_apply (i0 : Fin n) (x : Fin n -> Real) (i : Fin n) :
    chartReflectCLM i0 x i = (if i = i0 then (-1 : Real) else 1) * x i := by
  by_cases hi : i = i0 <;> simp [chartReflectCLM, hi]

/-- The linear map really is the bridge's specular reflection. -/
theorem chartReflectCLM_eq_reflect (i0 : Fin n) (x : Fin n -> Real) :
    chartReflectCLM i0 x = reflect i0 x := by
  funext i
  by_cases hi : i = i0
  · subst hi; simp [reflect]
  · simp [reflect, hi]

/-- **The chart's coordinate reflection, presented to the existing
variable-geometry reflection module.**  Generalizes the flat instance to an
arbitrary dimension and an arbitrary reflecting coordinate. -/
def chartReflection (i0 : Fin n) : BoundaryReflection (Fin n -> Real) where
  boundary := {x : Fin n -> Real | x i0 = 0}
  point := 0
  point_mem := by simp
  reflect := reflect i0
  differential := chartReflectCLM i0
  hasFDeriv := by
    have hfun : (reflect i0 : (Fin n -> Real) -> (Fin n -> Real))
        = fun x => chartReflectCLM i0 x := by
      funext x; rw [chartReflectCLM_eq_reflect]
    rw [hfun]
    exact (chartReflectCLM i0).hasFDerivAt
  involutive := reflect_reflect i0
  fixesBoundary := fun _ hx => reflect_of_eq_zero hx
  tangent := LinearMap.ker (LinearMap.proj i0 : (Fin n -> Real) →ₗ[Real] Real)
  normal := dir i0
  differential_tangent := by
    intro v hv
    have hv0 : v i0 = 0 := by simpa using hv
    rw [chartReflectCLM_eq_reflect]
    exact reflect_of_eq_zero hv0
  differential_normal := by
    funext i
    by_cases hi : i = i0
    · subst hi; simp [dir, Pi.single]
    · simp [dir, Pi.single, hi]

@[simp] theorem chartReflection_reflect (i0 : Fin n) (x : Fin n -> Real) :
    (chartReflection i0).reflect x = reflect i0 x := rfl

/-- The chart reflection is non-degenerate: its normal is transversal. -/
theorem chartReflection_normal_notMem_tangent (i0 : Fin n) :
    (chartReflection i0).normal ∉ (chartReflection i0).tangent := by
  intro hmem
  have h : dir i0 i0 = 0 := by simpa [chartReflection] using hmem
  simp [dir, Pi.single] at h

/-! ## Reflecting a jet -/

/-- Composing with a linear rescaling of the parameter. -/
theorem hasDerivAt_comp_const_mul {f : Real -> Complex} {a : Complex} {c : Real}
    (h : HasDerivAt f a 0) :
    HasDerivAt (fun t : Real => f (c * t)) ((c : Complex) * a) 0 := by
  have hinner : HasDerivAt (fun t : Real => c * t) c 0 := by
    simpa using (hasDerivAt_id (0 : Real)).const_mul c
  have h0 : HasDerivAt f a (c * 0) := by simpa using h
  simpa [Function.comp, Complex.real_smul] using HasDerivAt.scomp (0 : Real) h0 hinner

/-- The sign a coordinate direction picks up under the reflection. -/
def dirSign (i0 j : Fin n) : Real := if j = i0 then -1 else 1

/-- Reflection turns a translation along `dir j` into a translation along
`dir j` with the reversed parameter when `j` is the reflecting coordinate. -/
theorem reflect_add_smul_dir (i0 j : Fin n) (x : Fin n -> Real) (t : Real) :
    reflect i0 (x + t • dir j) = reflect i0 x + (dirSign i0 j * t) • dir j := by
  funext i
  by_cases hj : j = i0
  · subst hj
    by_cases hi : i = j
    · subst hi; simp [reflect, dir, Pi.single, dirSign]; ring
    · simp [reflect, dir, Pi.single, dirSign, hi]
  · by_cases hi : i = i0
    · subst hi
      simp [reflect, dir, Pi.single, dirSign, hj, Ne.symm hj]
    · simp [reflect, dir, Pi.single, dirSign, hj, hi]

/-- **The reflected jet.**  Pulling a `ChartJet` back by the coordinate
reflection gives a `ChartJet` again, with the derivative data carrying the
expected signs.  Proved by the chain rule, not assumed. -/
def ChartJet.compReflect (i0 : Fin n) (u : ChartJet n) : ChartJet n where
  val := fun x => u.val (reflect i0 x)
  d := fun j x => (dirSign i0 j : Complex) * u.d j (reflect i0 x)
  d2 := fun j k x =>
    (dirSign i0 j : Complex) * (dirSign i0 k : Complex) * u.d2 j k (reflect i0 x)
  hasDeriv := by
    intro j x
    have h : HasDerivAt
        (fun t : Real => u.val (reflect i0 x + (dirSign i0 j * t) • dir j))
        ((dirSign i0 j : Complex) * u.d j (reflect i0 x)) 0 :=
      hasDerivAt_comp_const_mul (u.hasDeriv j (reflect i0 x))
    refine h.congr_of_eventuallyEq ?_
    filter_upwards with t
    rw [reflect_add_smul_dir]
  hasDeriv2 := by
    intro j k x
    have h : HasDerivAt
        (fun t : Real =>
          (dirSign i0 k : Complex) * u.d k (reflect i0 x + (dirSign i0 j * t) • dir j))
        ((dirSign i0 j : Complex)
          * ((dirSign i0 k : Complex) * u.d2 j k (reflect i0 x))) 0 :=
      hasDerivAt_comp_const_mul
        ((u.hasDeriv2 j k (reflect i0 x)).const_mul (dirSign i0 k : Complex))
    have h' : HasDerivAt
        (fun t : Real =>
          (dirSign i0 k : Complex) * u.d k (reflect i0 (x + t • dir j)))
        ((dirSign i0 j : Complex)
          * ((dirSign i0 k : Complex) * u.d2 j k (reflect i0 x))) 0 := by
      refine h.congr_of_eventuallyEq ?_
      filter_upwards with t
      rw [reflect_add_smul_dir]
    convert h' using 1
    ring

@[simp] theorem ChartJet.compReflect_val (i0 : Fin n) (u : ChartJet n)
    (x : Fin n -> Real) : (ChartJet.compReflect i0 u).val x = u.val (reflect i0 x) := rfl

/-! ## The incident minus reflected beam -/

/-- The source's admissible combination: incident minus reflected. -/
def reflectedDifferenceJet (i0 : Fin n) (u : ChartJet n) :
    (Fin n -> Real) -> Complex :=
  (chartReflection i0).difference u.val

/-- **Exact Dirichlet cancellation on the reflecting face**, for the beam the
chart construction produces.  This is the existing reflection module's theorem
applied to the constructed jet, not a new argument. -/
theorem reflectedDifferenceJet_eq_zero_on_face (i0 : Fin n) (u : ChartJet n)
    {z : Fin n -> Real} (hz : z i0 = 0) : reflectedDifferenceJet i0 u z = 0 :=
  (chartReflection i0).difference_eq_zero_on_boundary u.val (x := z) hz

/-- The reflected difference of the constructed beam, spelled out. -/
theorem reflectedDifferenceJet_apply (i0 : Fin n) (u : ChartJet n)
    (z : Fin n -> Real) :
    reflectedDifferenceJet i0 u z = u.val z - u.val (reflect i0 z) := rfl

/-! ## The phase-difference estimate -/

/-- **The mean value estimate for the complex exponential.**  If the real part
stays below `M` along the segment joining `z2` to `z1`, then
`|e^{z1} - e^{z2}| <= |z1 - z2| e^M`.  This is the estimate the source uses to
convert order-`N+1` phase matching into a boundary bound. -/
theorem norm_exp_sub_exp_le (z1 z2 : Complex) (M : Real)
    (hM : ∀ s : Real, s ∈ Set.Icc (0 : Real) 1 →
      (z2 + (s : Complex) * (z1 - z2)).re ≤ M) :
    ‖Complex.exp z1 - Complex.exp z2‖ ≤ ‖z1 - z2‖ * Real.exp M := by
  set f : Real -> Complex := fun s => Complex.exp (z2 + (s : Complex) * (z1 - z2)) with hf
  set f' : Real -> Complex :=
    fun s => (z1 - z2) * Complex.exp (z2 + (s : Complex) * (z1 - z2)) with hf'
  have hderiv : ∀ s : Real, HasDerivAt f (f' s) s := by
    intro s
    have hinner : HasDerivAt (fun z : Complex => z2 + z * (z1 - z2)) (z1 - z2)
        ((s : Complex)) := by
      simpa using (((hasDerivAt_id ((s : Complex))).mul_const (z1 - z2)).const_add z2)
    have hcexp : HasDerivAt (fun z : Complex => Complex.exp (z2 + z * (z1 - z2)))
        ((z1 - z2) * Complex.exp (z2 + (s : Complex) * (z1 - z2))) ((s : Complex)) := by
      simpa [mul_comm] using hinner.cexp
    exact hcexp.comp_ofReal
  have hbound : ∀ s : Real, s ∈ Set.Icc (0 : Real) 1 →
      ‖f' s‖ ≤ ‖z1 - z2‖ * Real.exp M := by
    intro s hs
    rw [hf', norm_mul, Complex.norm_exp]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (hM s hs)) (norm_nonneg _)
  have hmvt := (convex_Icc (0 : Real) 1).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := f) (f' := f') (fun s hs => (hderiv s).hasDerivWithinAt) hbound
    (Set.left_mem_Icc.2 zero_le_one) (Set.right_mem_Icc.2 zero_le_one)
  have h1 : f 1 = Complex.exp z1 := by simp [hf]
  have h0 : f 0 = Complex.exp z2 := by simp [hf]
  rw [h1, h0] at hmvt
  simpa using hmvt

/-- **The source's boundary profile bound, derived.**  Order-`N+1` matching of
the incident and reflected phases, together with the transverse coercivity of
both, forces the exponential difference into the `k = 1`, `j = 1` slot of the
source's displayed splitting: constant `C * rho`, transverse weight `N + 1`,
Gaussian width `b * rho`.  Neither the frequency power nor the Gaussian weight
is assumed. -/
theorem expPhaseDifference_radiusProfileBound {d : Nat} (rho : Real) (hrho : 0 < rho)
    (phi1 phi2 : (Fin d -> Real) -> Complex) {C b : Real} {N : Nat}
    (hdiff : ∀ y, ‖phi1 y - phi2 y‖ ≤ C * (radius y) ^ (N + 1))
    (hcoer1 : ∀ y, b * radiusSq y ≤ (phi1 y).im)
    (hcoer2 : ∀ y, b * radiusSq y ≤ (phi2 y).im) :
    RadiusProfileBound
      (fun y => Complex.exp (Complex.I * (rho : Complex) * phi1 y)
        - Complex.exp (Complex.I * (rho : Complex) * phi2 y))
      (C * rho ^ ((1 : Nat) : Real)) (1 + (N + 1 - 1)) (b * rho) := by
  have hslot : 1 + (N + 1 - 1) = N + 1 := by omega
  rw [hslot, Nat.cast_one, Real.rpow_one]
  intro y
  set z1 : Complex := Complex.I * (rho : Complex) * phi1 y with hz1
  set z2 : Complex := Complex.I * (rho : Complex) * phi2 y with hz2
  have hre : ∀ w : Complex, (Complex.I * (rho : Complex) * w).re = -(rho * w.im) := by
    intro w
    simp [Complex.mul_re, Complex.mul_im]
  have hM : ∀ s : Real, s ∈ Set.Icc (0 : Real) 1 →
      (z2 + (s : Complex) * (z1 - z2)).re ≤ -(b * rho) * radiusSq y := by
    intro s hs
    have hs0 : (0 : Real) ≤ s := hs.1
    have hs1 : s ≤ 1 := hs.2
    have hz : z2 + (s : Complex) * (z1 - z2)
        = Complex.I * (rho : Complex)
            * (((1 - s : Real) : Complex) * phi2 y + ((s : Real) : Complex) * phi1 y) := by
      rw [hz1, hz2]
      push_cast
      ring
    rw [hz, hre]
    have him : (((1 - s : Real) : Complex) * phi2 y + ((s : Real) : Complex) * phi1 y).im
        = (1 - s) * (phi2 y).im + s * (phi1 y).im := by
      simp [Complex.add_im, Complex.mul_im]
    rw [him]
    have h1 : (1 - s) * (b * radiusSq y) ≤ (1 - s) * (phi2 y).im :=
      mul_le_mul_of_nonneg_left (hcoer2 y) (by linarith)
    have h2 : s * (b * radiusSq y) ≤ s * (phi1 y).im :=
      mul_le_mul_of_nonneg_left (hcoer1 y) hs0
    have hsum : b * radiusSq y ≤ (1 - s) * (phi2 y).im + s * (phi1 y).im := by nlinarith
    have := mul_le_mul_of_nonneg_left hsum hrho.le
    nlinarith [this]
  have hmain := norm_exp_sub_exp_le z1 z2 (-(b * rho) * radiusSq y) hM
  have hsub : z1 - z2 = Complex.I * (rho : Complex) * (phi1 y - phi2 y) := by
    rw [hz1, hz2]; ring
  have hnorm : ‖z1 - z2‖ = rho * ‖phi1 y - phi2 y‖ := by
    rw [hsub, norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_of_nonneg hrho.le]
  rw [hnorm] at hmain
  refine hmain.trans ?_
  have hstep : rho * ‖phi1 y - phi2 y‖ ≤ rho * (C * (radius y) ^ (N + 1)) :=
    mul_le_mul_of_nonneg_left (hdiff y) hrho.le
  have := mul_le_mul_of_nonneg_right hstep (Real.exp_pos (-(b * rho) * radiusSq y)).le
  refine this.trans_eq ?_
  ring

/-- **The reflected boundary Sobolev rate for the constructed beam.**  Feeding
the derived profile bound into the source's displayed splitting at `|alpha| = 2`
gives `O(rho^{-(N-1)/2 - d/4})`.  Every ingredient is computed from the phase
matching and the coercivity. -/
theorem reflectedBoundary_L2_rate_of_phaseMatching {d : Nat} (rho : Real)
    (hrho : 0 < rho) (phi1 phi2 : (Fin d -> Real) -> Complex) {C b : Real} {N : Nat}
    (hC : 0 ≤ C) (hb : 0 < b)
    (hdiff : ∀ y, ‖phi1 y - phi2 y‖ ≤ C * (radius y) ^ (N + 1))
    (hcoer1 : ∀ y, b * radiusSq y ≤ (phi1 y).im)
    (hcoer2 : ∀ y, b * radiusSq y ≤ (phi2 y).im) :
    Real.sqrt (∫ y : Fin d -> Real,
        ‖Complex.exp (Complex.I * (rho : Complex) * phi1 y)
          - Complex.exp (Complex.I * (rho : Complex) * phi2 y)‖ ^ 2)
      ≤ C * Real.sqrt (gaussianMoment d (1 + (N + 1 - 1)) (2 * b))
          * rho ^ (-(((N : Real) - 2 + 1) / 2) - (d : Real) / 4) :=
  reflectedBoundaryTerm_L2_rate (N := N) (alpha := 2) (k := 1) (j := 1)
    rfl (by omega) hC hb hrho
    (expPhaseDifference_radiusProfileBound rho hrho phi1 phi2 hdiff hcoer1 hcoer2)

end LiuWang2025SemilinearWaveChartBeamReflection
