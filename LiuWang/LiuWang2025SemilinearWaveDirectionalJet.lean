import LiuWang.LiuWang2025SemilinearWaveGaussianL2Bridge
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Liu-Wang semilinear wave: finite directional jets and the Taylor remainder

The source's Gaussian beam only kills transverse derivatives *at the central
ray*: `partial^alpha F(s, 0) = 0` for `|alpha| <= N`.  Away from the ray the
eikonal and transport expressions are Taylor remainders, and the whole
construction rests on the elementary fact that such a remainder is
`O(|z'|^{N+1})` on a compact transverse tube.

This file proves that fact rather than assuming it.

A `DirJet n N` carries a function together with its iterated *directional*
derivatives, indexed by the list of directions taken, each certified by a
`HasDerivAt` witness.  From that data alone:

* `dirJet_replicate_smul` derives positive homogeneity,
  `D (replicate k (c . v)) = c^k * D (replicate k v)`, by uniqueness of
  derivatives -- it is not a field;
* `rayDeriv_hasDerivAt` exhibits the radial derivatives of `t |-> F(t z)` as the
  repeated directional derivatives along `z` itself, so no multinomial chain
  rule is needed;
* `norm_le_of_chain` runs the mean value inequality `N + 1` times;
* `taylor_remainder_bound` concludes `|F(z)| <= M |z|^{N+1}` from vanishing of
  all derivatives through order `N` at the centre and a bound `M` on the
  order-`N+1` directional derivatives in unit directions over the tube.

The tube radius, the unit-direction quantifier and the constant `M` are all
explicit in the statement; nothing is hidden in a certificate.
-/

noncomputable section

open scoped BigOperators

namespace LiuWang2025SemilinearWaveDirectionalJet

open LiuWang2025SemilinearWaveGaussianL2Bridge
open LiuWang2025SemilinearWaveGaussianMassScaling (radiusSq)

variable {n : Nat}

/-! ## Transverse radius under scaling -/

theorem radiusSq_smul (c : Real) (z : Fin n -> Real) :
    radiusSq (c • z) = c ^ 2 * radiusSq z := by
  rw [radiusSq, radiusSq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Pi.smul_apply, smul_eq_mul]
  ring

theorem radius_smul (c : Real) (z : Fin n -> Real) :
    radius (c • z) = |c| * radius z := by
  rw [radius, radius, radiusSq_smul, Real.sqrt_mul (sq_nonneg c)]
  congr 1
  exact Real.sqrt_sq_eq_abs c

@[simp] theorem radius_zero : radius (0 : Fin n -> Real) = 0 := by
  simp [radius, radiusSq]

theorem eq_zero_of_radius_eq_zero {z : Fin n -> Real} (h : radius z = 0) :
    z = 0 := by
  have hnn : 0 ≤ radiusSq z := Finset.sum_nonneg fun i _ => sq_nonneg _
  have h' : Real.sqrt (radiusSq z) = 0 := h
  have hsq : radiusSq z = 0 := le_antisymm (Real.sqrt_eq_zero'.1 h') hnn
  funext i
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg
    (fun j (_ : j ∈ (Finset.univ : Finset (Fin n))) => sq_nonneg (z j))).1 hsq i
    (Finset.mem_univ i)
  simpa using sq_eq_zero_iff.1 hterm

/-! ## Finite directional jets -/

/-- A function on the chart together with its iterated directional derivatives
through order `N + 1`, indexed by the list of directions taken.  `D []` is the
function itself and `D (v :: l)` is the derivative of `D l` along `v`. -/
structure DirJet (n N : Nat) where
  /-- `D l x` is the iterated directional derivative of the function along the
  directions of `l`, evaluated at `x`. -/
  D : List (Fin n -> Real) -> (Fin n -> Real) -> Complex
  /-- Each entry of the family really is the directional derivative of the
  previous one. -/
  hasDeriv : ∀ (l : List (Fin n -> Real)), l.length ≤ N ->
    ∀ (v x : Fin n -> Real),
      HasDerivAt (fun t : Real => D l (x + t • v)) (D (v :: l) x) 0

namespace DirJet

variable {N : Nat}

/-- Reparametrizing the line by a constant multiple. -/
theorem hasDerivAt_comp_const_mul {f : Real -> Complex} {a : Complex} {c : Real}
    (h : HasDerivAt f a 0) :
    HasDerivAt (fun t : Real => f (c * t)) ((c : Complex) * a) 0 := by
  have hinner : HasDerivAt (fun t : Real => c * t) c 0 := by
    simpa using (hasDerivAt_id (0 : Real)).const_mul c
  have h0 : HasDerivAt f a (c * 0) := by simpa using h
  simpa [Function.comp, Complex.real_smul] using HasDerivAt.scomp (0 : Real) h0 hinner

/-- The derivative along a rescaled direction, before any homogeneity is
known. -/
theorem hasDerivAt_smul_dir (J : DirJet n N) (l : List (Fin n -> Real))
    (hl : l.length ≤ N) (c : Real) (v x : Fin n -> Real) :
    HasDerivAt (fun t : Real => J.D l (x + t • (c • v)))
      ((c : Complex) * J.D (v :: l) x) 0 := by
  have hbase := hasDerivAt_comp_const_mul (c := c) (J.hasDeriv l hl v x)
  refine hbase.congr_of_eventuallyEq ?_
  filter_upwards with t
  congr 1
  funext i
  simp [Pi.smul_apply, smul_eq_mul]
  ring

/-- **Positive homogeneity of the iterated directional derivative**, derived
from uniqueness of derivatives rather than assumed. -/
theorem replicate_smul (J : DirJet n N) (c : Real) (v : Fin n -> Real) :
    ∀ k : Nat, k ≤ N + 1 -> ∀ x : Fin n -> Real,
      J.D (List.replicate k (c • v)) x
        = (c : Complex) ^ k * J.D (List.replicate k v) x := by
  intro k
  induction k with
  | zero => intro _ x; simp
  | succ k ih =>
    intro hk x
    have hkN : k ≤ N := by omega
    have hlen : (List.replicate k (c • v)).length ≤ N := by
      simpa using hkN
    have hlen' : (List.replicate k v).length ≤ N := by
      simpa using hkN
    have h1 : HasDerivAt
        (fun t : Real => J.D (List.replicate k (c • v)) (x + t • (c • v)))
        (J.D (List.replicate (k + 1) (c • v)) x) 0 := by
      have := J.hasDeriv (List.replicate k (c • v)) hlen (c • v) x
      rwa [← List.replicate_succ] at this
    have h2 : HasDerivAt
        (fun t : Real => (c : Complex) ^ k * J.D (List.replicate k v) (x + t • (c • v)))
        ((c : Complex) ^ k * ((c : Complex) * J.D (List.replicate (k + 1) v) x)) 0 := by
      have hinner := hasDerivAt_smul_dir J (List.replicate k v) hlen' c v x
      rw [← List.replicate_succ] at hinner
      exact hinner.const_mul _
    have h3 : HasDerivAt
        (fun t : Real => J.D (List.replicate k (c • v)) (x + t • (c • v)))
        ((c : Complex) ^ k * ((c : Complex) * J.D (List.replicate (k + 1) v) x)) 0 := by
      refine h2.congr_of_eventuallyEq ?_
      filter_upwards with t
      exact ih (by omega) (x + t • (c • v))
    have := h1.unique h3
    rw [this]
    ring

/-! ## The radial derivatives -/

/-- The `k`-th derivative of `t |-> F(t z)`, exhibited as the `k`-fold
directional derivative along `z` itself. -/
def rayDeriv (J : DirJet n N) (z : Fin n -> Real) (k : Nat) (t : Real) : Complex :=
  J.D (List.replicate k z) (t • z)

/-- Translating the base point of a one-parameter family. -/
theorem hasDerivAt_of_shift {G : Real -> Complex} {c : Complex} {t : Real}
    (h : HasDerivAt (fun s : Real => G (t + s)) c 0) : HasDerivAt G c t := by
  have hinner : HasDerivAt (fun r : Real => r - t) 1 t := by
    simpa using (hasDerivAt_id t).sub_const t
  have h0 : HasDerivAt (fun s : Real => G (t + s)) c (t - t) := by
    simpa using h
  have hcomp : HasDerivAt
      ((fun s : Real => G (t + s)) ∘ (fun r : Real => r - t)) ((1 : Real) • c) t :=
    HasDerivAt.scomp t h0 hinner
  have hfun : ((fun s : Real => G (t + s)) ∘ (fun r : Real => r - t)) = G := by
    funext r
    simp
  rw [hfun] at hcomp
  simpa using hcomp

/-- **The radial derivative chain.**  No multinomial chain rule is needed: the
`k`-th radial derivative is literally the `k`-fold directional derivative along
the ray direction. -/
theorem rayDeriv_hasDerivAt (J : DirJet n N) (z : Fin n -> Real) {k : Nat}
    (hk : k ≤ N) (t : Real) :
    HasDerivAt (rayDeriv J z k) (rayDeriv J z (k + 1) t) t := by
  refine hasDerivAt_of_shift ?_
  have hlen : (List.replicate k z).length ≤ N := by simpa using hk
  have h := J.hasDeriv (List.replicate k z) hlen z (t • z)
  rw [← List.replicate_succ] at h
  refine h.congr_of_eventuallyEq ?_
  filter_upwards with s
  show J.D (List.replicate k z) ((t + s) • z) = J.D (List.replicate k z) (t • z + s • z)
  rw [add_smul]

end DirJet

/-! ## The iterated mean value inequality -/

/-- **`N + 1` applications of the mean value inequality.**  If a chain of
derivatives all vanish at `0` and the top one is bounded by `M` on `[0,1]`, the
bottom one is bounded by `M` on `[0,1]`. -/
theorem norm_le_of_chain (g : Nat -> Real -> Complex) (N : Nat) (M : Real)
    (hg : ∀ k, k ≤ N -> ∀ t, HasDerivAt (g k) (g (k + 1) t) t)
    (hz : ∀ k, k ≤ N -> g k 0 = 0)
    (hM : ∀ t ∈ Set.Icc (0 : Real) 1, ‖g (N + 1) t‖ ≤ M) :
    ∀ t ∈ Set.Icc (0 : Real) 1, ‖g 0 t‖ ≤ M := by
  have hMnn : 0 ≤ M :=
    le_trans (norm_nonneg _) (hM 0 (Set.left_mem_Icc.2 zero_le_one))
  have key : ∀ j : Nat, j ≤ N + 1 ->
      ∀ t ∈ Set.Icc (0 : Real) 1, ‖g (N + 1 - j) t‖ ≤ M := by
    intro j
    induction j with
    | zero => intro _ t ht; simpa using hM t ht
    | succ j ih =>
      intro hj t ht
      have hidx : N + 1 - (j + 1) = N - j := by omega
      have hsucc : N - j + 1 = N + 1 - j := by omega
      rw [hidx]
      have hih := ih (by omega)
      have hderiv : ∀ s ∈ Set.Icc (0 : Real) 1,
          HasDerivWithinAt (g (N - j)) (g (N - j + 1) s) (Set.Icc (0 : Real) 1) s :=
        fun s _ => (hg (N - j) (by omega) s).hasDerivWithinAt
      have hbd : ∀ s ∈ Set.Icc (0 : Real) 1, ‖g (N - j + 1) s‖ ≤ M := by
        intro s hs
        rw [hsucc]
        exact hih s hs
      have hmvt := (convex_Icc (0 : Real) 1).norm_image_sub_le_of_norm_hasDerivWithin_le
        hderiv hbd (Set.left_mem_Icc.2 zero_le_one) ht
      rw [hz (N - j) (by omega)] at hmvt
      have ht1 : ‖t - (0 : Real)‖ ≤ 1 := by
        rw [sub_zero, Real.norm_of_nonneg ht.1]
        exact ht.2
      calc ‖g (N - j) t‖ = ‖g (N - j) t - 0‖ := by rw [sub_zero]
        _ ≤ M * ‖t - (0 : Real)‖ := hmvt
        _ ≤ M * 1 := mul_le_mul_of_nonneg_left ht1 hMnn
        _ = M := mul_one M
  intro t ht
  simpa [Nat.sub_self] using key (N + 1) le_rfl t ht

/-! ## The Taylor remainder -/

/-- **The finite Taylor remainder estimate.**  If every directional derivative
through order `N` vanishes at the centre, and the order-`N+1` directional
derivatives in unit directions are bounded by `M` on the transverse tube of
radius `r`, then the function is `O(|z|^{N+1})` on that tube.  The polynomial
bound is the conclusion, not a hypothesis. -/
theorem taylor_remainder_bound {N : Nat} (J : DirJet n N) {M r : Real}
    (hvanish : ∀ l : List (Fin n -> Real), l.length ≤ N -> J.D l 0 = 0)
    (hbound : ∀ u : Fin n -> Real, radius u = 1 ->
      ∀ y : Fin n -> Real, radius y ≤ r ->
        ‖J.D (List.replicate (N + 1) u) y‖ ≤ M)
    (z : Fin n -> Real) (hz : radius z ≤ r) :
    ‖J.D [] z‖ ≤ M * (radius z) ^ (N + 1) := by
  rcases eq_or_lt_of_le (radius_nonneg z) with hR | hR
  · have hz0 : z = 0 := eq_zero_of_radius_eq_zero hR.symm
    rw [hz0, hvanish [] (by simp), radius_zero]
    simp
  · set R : Real := radius z with hRdef
    set u : Fin n -> Real := R⁻¹ • z with hu
    have hRne : R ≠ 0 := ne_of_gt hR
    have hzu : z = R • u := by
      rw [hu, smul_smul, mul_inv_cancel₀ hRne, one_smul]
    have hradu : radius u = 1 := by
      rw [hu, radius_smul, abs_of_pos (inv_pos.2 hR), ← hRdef,
        inv_mul_cancel₀ hRne]
    -- the ray family
    have hrnn : (0 : Real) ≤ r := le_trans (radius_nonneg z) hz
    have hMnn : 0 ≤ M :=
      le_trans (norm_nonneg _) (hbound u hradu 0 (by rw [radius_zero]; exact hrnn))
    have hchain : ∀ k, k ≤ N -> ∀ t,
        HasDerivAt (DirJet.rayDeriv J z k) (DirJet.rayDeriv J z (k + 1) t) t :=
      fun k hk t => DirJet.rayDeriv_hasDerivAt J z hk t
    have hzero : ∀ k, k ≤ N -> DirJet.rayDeriv J z k 0 = 0 := by
      intro k hk
      rw [DirJet.rayDeriv, zero_smul]
      exact hvanish _ (by simpa using hk)
    have htop : ∀ t ∈ Set.Icc (0 : Real) 1,
        ‖DirJet.rayDeriv J z (N + 1) t‖ ≤ M * R ^ (N + 1) := by
      intro t ht
      rw [DirJet.rayDeriv]
      have hhom : ∀ y : Fin n -> Real, J.D (List.replicate (N + 1) z) y
          = (R : Complex) ^ (N + 1) * J.D (List.replicate (N + 1) u) y := by
        intro y
        have hy := J.replicate_smul R u (N + 1) le_rfl y
        rwa [← hzu] at hy
      rw [hhom (t • z), norm_mul, norm_pow, Complex.norm_real,
        Real.norm_of_nonneg (radius_nonneg z)]
      have hty : radius (t • z) ≤ r := by
        rw [radius_smul, abs_of_nonneg ht.1, ← hRdef]
        calc t * R ≤ 1 * R := mul_le_mul_of_nonneg_right ht.2 (le_of_lt hR)
          _ = R := one_mul R
          _ ≤ r := hz
      have := hbound u hradu (t • z) hty
      calc R ^ (N + 1) * ‖J.D (List.replicate (N + 1) u) (t • z)‖
          ≤ R ^ (N + 1) * M :=
            mul_le_mul_of_nonneg_left this (pow_nonneg (radius_nonneg z) _)
        _ = M * R ^ (N + 1) := by ring
    have hfinal := norm_le_of_chain (DirJet.rayDeriv J z) N (M * R ^ (N + 1))
      hchain hzero htop 1 (Set.right_mem_Icc.2 zero_le_one)
    rwa [DirJet.rayDeriv, one_smul, List.replicate_zero] at hfinal

/-! ## Cutoff extension

The source's amplitude carries a cutoff supported near the central ray, so the
Taylor bound, valid only on the tube, extends to the whole chart for free.
-/

/-- **From a tube bound to a global bound.**  A function supported in the tube
and polynomially bounded there is polynomially bounded everywhere. -/
theorem global_of_tube {N : Nat} {M r : Real} (hM : 0 ≤ M)
    (F : (Fin n -> Real) -> Complex)
    (hsupp : ∀ z : Fin n -> Real, r < radius z -> F z = 0)
    (htube : ∀ z : Fin n -> Real, radius z ≤ r ->
      ‖F z‖ ≤ M * (radius z) ^ (N + 1))
    (z : Fin n -> Real) : ‖F z‖ ≤ M * (radius z) ^ (N + 1) := by
  rcases le_or_gt (radius z) r with h | h
  · exact htube z h
  · rw [hsupp z h, norm_zero]
    exact mul_nonneg hM (pow_nonneg (radius_nonneg z) _)

/-- **The source's polynomial bound, from the source's jet conditions.**  A
cutoff function whose directional derivatives all vanish at the centre through
order `N`, and whose order-`N+1` directional derivatives are bounded on the
tube, obeys `|F(z')| <= M |z'|^{N+1}` at every chart point.  Both the vanishing
and the derivative bound are conditions on the constructed jet; the polynomial
bound is the conclusion. -/
theorem global_polynomial_bound_of_vanishing_jet {N : Nat} (J : DirJet n N)
    {M r : Real} (hM : 0 ≤ M)
    (hvanish : ∀ l : List (Fin n -> Real), l.length ≤ N -> J.D l 0 = 0)
    (hbound : ∀ u : Fin n -> Real, radius u = 1 ->
      ∀ y : Fin n -> Real, radius y ≤ r ->
        ‖J.D (List.replicate (N + 1) u) y‖ ≤ M)
    (hsupp : ∀ z : Fin n -> Real, r < radius z -> J.D [] z = 0)
    (z : Fin n -> Real) : ‖J.D [] z‖ ≤ M * (radius z) ^ (N + 1) :=
  global_of_tube (N := N) hM (J.D []) hsupp
    (fun y hy => taylor_remainder_bound J hvanish hbound y hy) z

end LiuWang2025SemilinearWaveDirectionalJet
