import LiuWang.LiuWang2025SemilinearWaveLongitudinalJet

/-!
# Liu-Wang semilinear wave: the operators at jet level

With the longitudinal jets of `LiuWang2025SemilinearWaveLongitudinalJet` in
hand, the chart operators of Section 3 can be written directly on coefficient
families: the metric components become jets, transverse differentiation is the
formal `transverseDeriv`, longitudinal differentiation is the stored derivative
family, and every product is the convolution.

`jetEikonal` is the source's `S phi = <d phi, d phi>_g` written this way, split
into its longitudinal-longitudinal, longitudinal-transverse and
transverse-transverse blocks.

The section closes with the **degree-zero cancellation, derived**: with the
source's `phi_0 = 0` and `phi_1 = z^1`, the degree-zero coefficient of
`jetEikonal` is exactly the degree-zero coefficient of the metric component
`A^{1 1}`, so it vanishes precisely when the central curve is a null geodesic.
That is the source's first Fermi normalization condition, obtained by
computation rather than assumed.
-/

noncomputable section

open scoped BigOperators

namespace LiuWang2025SemilinearWaveJetOperators

open LiuWang2025SemilinearWaveTransverseJet
open LiuWang2025SemilinearWaveLongitudinalJet
open LiuWang2025SemilinearWaveLongitudinalJet.LongJet

variable {d : Nat}

/-! ## Convolution at the beam centre -/

/-- Only the zero multi-index lies below the zero multi-index. -/
theorem below_zero : below (0 : Multiindex d) = {(0 : Multiindex d)} := by
  ext b
  rw [mem_below, Finset.mem_singleton]
  constructor
  · intro h
    funext i
    exact Nat.le_zero.1 (h i)
  · intro h i
    rw [h]

/-- At the beam centre the convolution is the plain product. -/
@[simp] theorem mul_c_zero (u v : LongJet d) (s : Real) :
    (mul u v).c 0 s = u.c 0 s * v.c 0 s := by
  have hsub : (0 : Multiindex d) - 0 = 0 := by
    funext i
    simp
  rw [mul_c, below_zero, Finset.sum_singleton, hsub]

/-- The degree-zero coefficient of a transverse derivative is the degree-one
coefficient it differentiates. -/
@[simp] theorem transverseDeriv_c_zero (i : Fin d) (u : LongJet d) (s : Real) :
    (transverseDeriv i u).c 0 s = u.c (Pi.single i 1) s := by
  have h : (0 : Multiindex d) + Pi.single i 1 = Pi.single i 1 := zero_add _
  simp [transverseDeriv, h]

/-! ## The eikonal symbol at jet level -/

/-- **The eikonal symbol on coefficient families.**  `Ass`, `Bs` and `Att` are
the longitudinal-longitudinal, longitudinal-transverse and
transverse-transverse blocks of the inverse metric, `phi` the phase jet and
`dphi` its longitudinal derivative jet. -/
def jetEikonal (Ass : LongJet d) (Bs : Fin d -> LongJet d)
    (Att : Fin d -> Fin d -> LongJet d) (phi dphi : LongJet d)
    (a : Multiindex d) (s : Real) : Complex :=
  (mul Ass (mul dphi dphi)).c a s
    + 2 * ∑ i, (mul (Bs i) (mul dphi (transverseDeriv i phi))).c a s
    + ∑ i, ∑ j,
        (mul (Att i j)
          (mul (transverseDeriv i phi) (transverseDeriv j phi))).c a s

/-- **The degree-zero coefficient of the eikonal symbol, computed.**  With the
source's `phi_0 = 0` (so the longitudinal derivative vanishes at the centre)
and `phi_1 = z^1` (so the transverse gradient at the centre is the `i1`-th
covector), everything collapses to the single metric coefficient `A^{i1 i1}`. -/
theorem jetEikonal_coeff_zero (Ass : LongJet d) (Bs : Fin d -> LongJet d)
    (Att : Fin d -> Fin d -> LongJet d) (phi dphi : LongJet d) (i1 : Fin d)
    (s : Real) (hphi0 : dphi.c 0 s = 0)
    (hphi1 : ∀ i, phi.c (Pi.single i 1) s = if i = i1 then 1 else 0) :
    jetEikonal Ass Bs Att phi dphi 0 s = (Att i1 i1).c 0 s := by
  have hgrad : ∀ i, (transverseDeriv i phi).c 0 s = if i = i1 then 1 else 0 := by
    intro i
    rw [transverseDeriv_c_zero, hphi1 i]
  rw [jetEikonal]
  have h1 : (mul Ass (mul dphi dphi)).c 0 s = 0 := by
    rw [mul_c_zero, mul_c_zero, hphi0]
    ring
  have h2 : ∀ i, (mul (Bs i) (mul dphi (transverseDeriv i phi))).c 0 s = 0 := by
    intro i
    rw [mul_c_zero, mul_c_zero, hphi0]
    ring
  have h3 : ∀ i, (∑ j, (mul (Att i j)
      (mul (transverseDeriv i phi) (transverseDeriv j phi))).c 0 s)
      = if i = i1 then (Att i1 i1).c 0 s else 0 := by
    intro i
    have hterm : ∀ j, (mul (Att i j)
        (mul (transverseDeriv i phi) (transverseDeriv j phi))).c 0 s
        = (Att i j).c 0 s * ((if i = i1 then (1 : Complex) else 0)
            * (if j = i1 then (1 : Complex) else 0)) := by
      intro j
      rw [mul_c_zero, mul_c_zero, hgrad i, hgrad j]
    rw [Finset.sum_congr rfl fun j _ => hterm j]
    by_cases hi : i = i1
    · have hif : (if i = i1 then (Att i1 i1).c 0 s else 0) = (Att i1 i1).c 0 s :=
        if_pos hi
      rw [hif, Finset.sum_eq_single_of_mem i1 (Finset.mem_univ i1)]
      · simp [hi]
      · intro j _ hj
        simp [hj]
    · have hif : (if i = i1 then (Att i1 i1).c 0 s else 0) = 0 := if_neg hi
      rw [hif]
      refine Finset.sum_eq_zero fun j _ => ?_
      simp [hi]
  have hsum2 : (∑ i, (mul (Bs i) (mul dphi (transverseDeriv i phi))).c 0 s) = 0 :=
    Finset.sum_eq_zero fun i _ => h2 i
  have hsum3 : (∑ i, ∑ j,
      (mul (Att i j) (mul (transverseDeriv i phi) (transverseDeriv j phi))).c 0 s)
      = (Att i1 i1).c 0 s := by
    rw [Finset.sum_eq_single_of_mem i1 (Finset.mem_univ i1)]
    · rw [h3 i1, if_pos rfl]
    · intro i _ hi
      rw [h3 i, if_neg hi]
  rw [h1, hsum2, hsum3]
  ring

/-- **Degree-zero eikonal cancellation from the null condition.**  The source's
Fermi normalization makes `A^{i1 i1}` vanish on the central curve, and the
computation above then forces the degree-zero eikonal coefficient to vanish. -/
theorem jetEikonal_coeff_zero_eq_zero (Ass : LongJet d) (Bs : Fin d -> LongJet d)
    (Att : Fin d -> Fin d -> LongJet d) (phi dphi : LongJet d) (i1 : Fin d)
    (s : Real) (hphi0 : dphi.c 0 s = 0)
    (hphi1 : ∀ i, phi.c (Pi.single i 1) s = if i = i1 then 1 else 0)
    (hnull : (Att i1 i1).c 0 s = 0) :
    jetEikonal Ass Bs Att phi dphi 0 s = 0 := by
  rw [jetEikonal_coeff_zero Ass Bs Att phi dphi i1 s hphi0 hphi1, hnull]


/-! ## The graded structure of the convolution

Total degree is additive along the convolution index, which is what makes the
coefficient calculus graded and the eikonal system triangular.
-/

/-- **Total degree is additive along the convolution index.** -/
theorem deg_add_deg_sub {a b : Multiindex d} (hb : b ∈ below a) :
    deg b + deg (a - b) = deg a := by
  rw [deg, deg, deg, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact Nat.add_sub_cancel' (mem_below.1 hb i)

/-- A factor supported in degrees at least `p` convolved with one supported in
degrees at least `q` is supported in degrees at least `p + q`. -/
theorem mul_c_eq_zero_of_deg_lt {u v : LongJet d} {p q : Nat}
    (hu : ∀ b s, deg b < p -> u.c b s = 0)
    (hv : ∀ b s, deg b < q -> v.c b s = 0)
    {a : Multiindex d} (ha : deg a < p + q) (s : Real) :
    (mul u v).c a s = 0 := by
  rw [mul_c]
  refine Finset.sum_eq_zero fun b hb => ?_
  have hsum : deg b + deg (a - b) = deg a := deg_add_deg_sub hb
  rcases Nat.lt_or_ge (deg b) p with h | h
  · rw [hu b s h, zero_mul]
  · rw [hv (a - b) s (by omega), mul_zero]

/-! ## Degree one -/

/-- Only the zero multi-index and `alpha` itself lie below a multi-index of
total degree one. -/
theorem below_single (k : Fin d) :
    below (Pi.single k 1 : Multiindex d) = {0, Pi.single k 1} := by
  ext b
  rw [mem_below, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro h
    have hoff : ∀ i, i ≠ k -> b i = 0 := by
      intro i hi
      have hb := h i
      rw [Pi.single_apply, if_neg hi] at hb
      exact Nat.le_zero.1 hb
    have hk : b k ≤ 1 := by
      have hb := h k
      rwa [Pi.single_eq_same] at hb
    rcases Nat.eq_zero_or_pos (b k) with hk0 | hk0
    · left
      funext i
      by_cases hi : i = k
      · subst hi
        simpa using hk0
      · simpa using hoff i hi
    · right
      funext i
      by_cases hi : i = k
      · subst hi
        rw [Pi.single_eq_same]
        omega
      · rw [hoff i hi, Pi.single_apply, if_neg hi]
  · intro h i
    rcases h with h | h <;> rw [h]
    exact Nat.zero_le _

/-- At a multi-index of total degree one the convolution has exactly two
terms. -/
theorem mul_c_single (u v : LongJet d) (k : Fin d) (s : Real) :
    (mul u v).c (Pi.single k 1) s
      = u.c 0 s * v.c (Pi.single k 1) s + u.c (Pi.single k 1) s * v.c 0 s := by
  have hne : (0 : Multiindex d) ≠ Pi.single k 1 := by
    intro h
    have hk := congrFun h k
    simp at hk
  have h1 : (Pi.single k 1 : Multiindex d) - 0 = Pi.single k 1 := by
    funext i
    simp
  have h2 : (Pi.single k 1 : Multiindex d) - Pi.single k 1 = 0 := by
    funext i
    simp
  rw [mul_c, below_single, Finset.sum_pair hne, h1, h2]

/-- **The degree-one coefficient of the eikonal symbol, computed.**  With the
source's `phi_0 = 0` and `phi_1 = z^{i1}` the whole first transverse jet of the
eikonal collapses to three terms: the longitudinal derivative of the linear
phase against `A^{s i1}`, the null row of the transverse block against the
transverse 2-jet of the phase, and the first transverse derivative of the
metric coefficient `A^{i1 i1}`.  This is the source's first-jet computation,
carried out rather than assumed. -/
theorem jetEikonal_coeff_one (Ass : LongJet d) (Bs : Fin d -> LongJet d)
    (Att : Fin d -> Fin d -> LongJet d) (phi dphi : LongJet d) (i1 k : Fin d)
    (s : Real) (hphi0 : dphi.c 0 s = 0)
    (hphi1 : ∀ i, phi.c (Pi.single i 1) s = if i = i1 then 1 else 0) :
    jetEikonal Ass Bs Att phi dphi (Pi.single k 1) s
      = 2 * ((Bs i1).c 0 s * dphi.c (Pi.single k 1) s)
        + ((∑ j, (Att i1 j).c 0 s * (transverseDeriv j phi).c (Pi.single k 1) s)
            + (∑ i, (Att i i1).c 0 s * (transverseDeriv i phi).c (Pi.single k 1) s)
            + (Att i1 i1).c (Pi.single k 1) s) := by
  have hgrad : ∀ i, (transverseDeriv i phi).c 0 s = if i = i1 then 1 else 0 := by
    intro i
    rw [transverseDeriv_c_zero, hphi1 i]
  rw [jetEikonal]
  -- the longitudinal-longitudinal block
  have h1 : (mul Ass (mul dphi dphi)).c (Pi.single k 1) s = 0 := by
    rw [mul_c_single, mul_c_single, mul_c_zero, hphi0]
    ring
  -- the longitudinal-transverse block
  have h2 : ∀ i, (mul (Bs i) (mul dphi (transverseDeriv i phi))).c
      (Pi.single k 1) s
      = (Bs i).c 0 s * (dphi.c (Pi.single k 1) s * (if i = i1 then 1 else 0)) := by
    intro i
    rw [mul_c_single, mul_c_single, mul_c_zero, hphi0, hgrad i]
    ring
  have hsum2 : (∑ i, (mul (Bs i) (mul dphi (transverseDeriv i phi))).c
      (Pi.single k 1) s) = (Bs i1).c 0 s * dphi.c (Pi.single k 1) s := by
    rw [Finset.sum_eq_single_of_mem i1 (Finset.mem_univ i1)]
    · rw [h2 i1]
      simp
    · intro i _ hi
      rw [h2 i]
      simp [hi]
  -- the transverse-transverse block
  have hexp : ∀ i j, (mul (Att i j)
      (mul (transverseDeriv i phi) (transverseDeriv j phi))).c (Pi.single k 1) s
      = ((if i = i1 then
            (Att i j).c 0 s * (transverseDeriv j phi).c (Pi.single k 1) s else 0)
          + (if j = i1 then
              (Att i j).c 0 s * (transverseDeriv i phi).c (Pi.single k 1) s else 0))
        + (if i = i1 then
            (if j = i1 then (Att i j).c (Pi.single k 1) s else 0) else 0) := by
    intro i j
    rw [mul_c_single, mul_c_single, mul_c_zero, hgrad i, hgrad j]
    by_cases hi : i = i1 <;> by_cases hj : j = i1 <;> simp [hi, hj]
    ring
  have hstep : (∑ i, ∑ j, (mul (Att i j)
        (mul (transverseDeriv i phi) (transverseDeriv j phi))).c (Pi.single k 1) s)
      = ∑ i, ∑ j,
          (((if i = i1 then
              (Att i j).c 0 s * (transverseDeriv j phi).c (Pi.single k 1) s else 0)
            + (if j = i1 then
                (Att i j).c 0 s * (transverseDeriv i phi).c (Pi.single k 1) s else 0))
          + (if i = i1 then
              (if j = i1 then (Att i j).c (Pi.single k 1) s else 0) else 0)) :=
    Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hexp i j
  have hA : (∑ i, ∑ j, (if i = i1 then
        (Att i j).c 0 s * (transverseDeriv j phi).c (Pi.single k 1) s else 0))
      = ∑ j, (Att i1 j).c 0 s * (transverseDeriv j phi).c (Pi.single k 1) s := by
    rw [Finset.sum_eq_single_of_mem i1 (Finset.mem_univ i1)]
    · exact Finset.sum_congr rfl fun j _ => if_pos rfl
    · intro i _ hi
      exact Finset.sum_eq_zero fun j _ => if_neg hi
  have hB : (∑ i, ∑ j, (if j = i1 then
        (Att i j).c 0 s * (transverseDeriv i phi).c (Pi.single k 1) s else 0))
      = ∑ i, (Att i i1).c 0 s * (transverseDeriv i phi).c (Pi.single k 1) s := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single_of_mem i1 (Finset.mem_univ i1)]
    · exact if_pos rfl
    · intro j _ hj
      exact if_neg hj
  have hC : (∑ i, ∑ j, (if i = i1 then
        (if j = i1 then (Att i j).c (Pi.single k 1) s else 0) else 0))
      = (Att i1 i1).c (Pi.single k 1) s := by
    rw [Finset.sum_eq_single_of_mem i1 (Finset.mem_univ i1)]
    · rw [Finset.sum_eq_single_of_mem i1 (Finset.mem_univ i1)]
      · rw [if_pos rfl, if_pos rfl]
      · intro j _ hj
        rw [if_pos rfl, if_neg hj]
    · intro i _ hi
      exact Finset.sum_eq_zero fun j _ => if_neg hi
  have hsplit : (∑ i, ∑ j,
        (((if i = i1 then
            (Att i j).c 0 s * (transverseDeriv j phi).c (Pi.single k 1) s else 0)
          + (if j = i1 then
              (Att i j).c 0 s * (transverseDeriv i phi).c (Pi.single k 1) s else 0))
        + (if i = i1 then
            (if j = i1 then (Att i j).c (Pi.single k 1) s else 0) else 0)))
      = ((∑ i, ∑ j, (if i = i1 then
            (Att i j).c 0 s * (transverseDeriv j phi).c (Pi.single k 1) s else 0))
        + (∑ i, ∑ j, (if j = i1 then
            (Att i j).c 0 s * (transverseDeriv i phi).c (Pi.single k 1) s else 0)))
        + (∑ i, ∑ j, (if i = i1 then
            (if j = i1 then (Att i j).c (Pi.single k 1) s else 0) else 0)) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  rw [h1, hsum2, hstep, hsplit, hA, hB, hC]
  ring

/-- **Degree-one eikonal cancellation from Fermi normalization.**  The source's
chart makes the null row of the transverse block vanish along the central curve
and makes `A^{i1 i1}` vanish to second order there, while the prescribed linear
phase `z^{i1}` is independent of the geodesic parameter.  Those three
normalization facts -- about the chart and the prescribed low-order phase only
-- force the whole first transverse jet of the eikonal to vanish. -/
theorem jetEikonal_coeff_one_eq_zero (Ass : LongJet d) (Bs : Fin d -> LongJet d)
    (Att : Fin d -> Fin d -> LongJet d) (phi dphi : LongJet d) (i1 k : Fin d)
    (s : Real) (hphi0 : dphi.c 0 s = 0)
    (hphi1 : ∀ i, phi.c (Pi.single i 1) s = if i = i1 then 1 else 0)
    (hlinear : dphi.c (Pi.single k 1) s = 0)
    (hnullRow : ∀ j, (Att i1 j).c 0 s = 0)
    (hnullCol : ∀ i, (Att i i1).c 0 s = 0)
    (hsecondOrder : (Att i1 i1).c (Pi.single k 1) s = 0) :
    jetEikonal Ass Bs Att phi dphi (Pi.single k 1) s = 0 := by
  rw [jetEikonal_coeff_one Ass Bs Att phi dphi i1 k s hphi0 hphi1, hlinear,
    hsecondOrder]
  have hA : (∑ j, (Att i1 j).c 0 s
      * (transverseDeriv j phi).c (Pi.single k 1) s) = 0 :=
    Finset.sum_eq_zero fun j _ => by rw [hnullRow j, zero_mul]
  have hB : (∑ i, (Att i i1).c 0 s
      * (transverseDeriv i phi).c (Pi.single k 1) s) = 0 :=
    Finset.sum_eq_zero fun i _ => by rw [hnullCol i, zero_mul]
  rw [hA, hB]
  ring


/-! ## Locality of the coefficient calculus

Which coefficients of the phase can the degree-`alpha` coefficient of the
eikonal actually read?  The convolution index never exceeds `alpha` in total
degree, and `transverseDeriv` raises the index by exactly one, so the answer is
`deg <= deg alpha + 1` for the phase and `deg <= deg alpha` for its longitudinal
derivative.  That is the triangularity input the recursion needs, and it is
proved here rather than assumed.
-/

/-- The convolution reads its factors only at multi-indices of total degree at
most that of the result. -/
theorem mul_c_congr {u u' v v' : LongJet d} {a : Multiindex d} {s : Real}
    (hu : ∀ b, deg b ≤ deg a -> u.c b s = u'.c b s)
    (hv : ∀ b, deg b ≤ deg a -> v.c b s = v'.c b s) :
    (mul u v).c a s = (mul u' v').c a s := by
  rw [mul_c, mul_c]
  refine Finset.sum_congr rfl fun b hb => ?_
  have hd := deg_add_deg_sub hb
  rw [hu b (by omega), hv (a - b) (by omega)]

/-- The formal transverse derivative reads its argument one degree higher. -/
theorem transverseDeriv_c_congr {u u' : LongJet d} {i : Fin d}
    {b : Multiindex d} {s : Real}
    (h : u.c (b + Pi.single i 1) s = u'.c (b + Pi.single i 1) s) :
    (transverseDeriv i u).c b s = (transverseDeriv i u').c b s := by
  show ((b i + 1 : Nat) : Complex) * u.c (b + Pi.single i 1) s
    = ((b i + 1 : Nat) : Complex) * u'.c (b + Pi.single i 1) s
  rw [h]

/-- **Locality of the jet eikonal.**  Its degree-`alpha` coefficient depends on
the phase only through multi-indices of total degree at most `deg alpha + 1`,
and on the longitudinal derivative only through degrees at most `deg alpha`. -/
theorem jetEikonal_congr (Ass : LongJet d) (Bs : Fin d -> LongJet d)
    (Att : Fin d -> Fin d -> LongJet d) {phi phi' dphi dphi' : LongJet d}
    {a : Multiindex d} {s : Real}
    (hphi : ∀ b, deg b ≤ deg a + 1 -> phi.c b s = phi'.c b s)
    (hdphi : ∀ b, deg b ≤ deg a -> dphi.c b s = dphi'.c b s) :
    jetEikonal Ass Bs Att phi dphi a s
      = jetEikonal Ass Bs Att phi' dphi' a s := by
  have hgrad : ∀ (i : Fin d) (b : Multiindex d), deg b ≤ deg a ->
      (transverseDeriv i phi).c b s = (transverseDeriv i phi').c b s := by
    intro i b hb
    refine transverseDeriv_c_congr ?_
    exact hphi _ (by
      rw [LiuWang2025SemilinearWaveLongitudinalJet.deg_add_single]
      omega)
  have hdd : ∀ b, deg b ≤ deg a ->
      (mul dphi dphi).c b s = (mul dphi' dphi').c b s := by
    intro b hb
    exact mul_c_congr (fun e he => hdphi e (by omega)) (fun e he => hdphi e (by omega))
  have hblock1 : (mul Ass (mul dphi dphi)).c a s
      = (mul Ass (mul dphi' dphi')).c a s :=
    mul_c_congr (fun _ _ => rfl) hdd
  have hblock2 : ∀ i, (mul (Bs i) (mul dphi (transverseDeriv i phi))).c a s
      = (mul (Bs i) (mul dphi' (transverseDeriv i phi'))).c a s := by
    intro i
    refine mul_c_congr (fun _ _ => rfl) fun b hb => ?_
    exact mul_c_congr (fun e he => hdphi e (by omega))
      (fun e he => hgrad i e (by omega))
  have hblock3 : ∀ i j, (mul (Att i j)
        (mul (transverseDeriv i phi) (transverseDeriv j phi))).c a s
      = (mul (Att i j)
        (mul (transverseDeriv i phi') (transverseDeriv j phi'))).c a s := by
    intro i j
    refine mul_c_congr (fun _ _ => rfl) fun b hb => ?_
    exact mul_c_congr (fun e he => hgrad i e (by omega))
      (fun e he => hgrad j e (by omega))
  have hs2 : (∑ i, (mul (Bs i) (mul dphi (transverseDeriv i phi))).c a s)
      = ∑ i, (mul (Bs i) (mul dphi' (transverseDeriv i phi'))).c a s :=
    Finset.sum_congr rfl fun i _ => hblock2 i
  have hs3 : (∑ i, ∑ j, (mul (Att i j)
        (mul (transverseDeriv i phi) (transverseDeriv j phi))).c a s)
      = ∑ i, ∑ j, (mul (Att i j)
        (mul (transverseDeriv i phi') (transverseDeriv j phi'))).c a s :=
    Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hblock3 i j
  rw [jetEikonal, jetEikonal, hblock1, hs2, hs3]


/-! ## Extracting the top and bottom of a graded convolution

These three lemmas are what make the variable-metric eikonal system genuinely
triangular.  They are stated at a fixed geodesic parameter, which is all the
recursion ever needs.
-/

/-- A strictly smaller convolution index has strictly smaller total degree. -/
theorem deg_lt_of_mem_below_ne {a b : Multiindex d} (hb : b ∈ below a)
    (hne : b ≠ a) : deg b < deg a := by
  have hd := deg_add_deg_sub hb
  rcases Nat.eq_zero_or_pos (deg (a - b)) with h | h
  · exfalso
    refine hne (funext fun i => ?_)
    have hle := mem_below.1 hb i
    have hle2 := le_deg (a - b) i
    have hz : a i - b i = (a - b) i := rfl
    omega
  · omega

/-- Fixed-parameter version of the graded vanishing lemma. -/
theorem mul_c_vanish {u v : LongJet d} {p q : Nat} {s : Real}
    (hu : ∀ b, deg b < p -> u.c b s = 0)
    (hv : ∀ b, deg b < q -> v.c b s = 0)
    {a : Multiindex d} (ha : deg a < p + q) : (mul u v).c a s = 0 := by
  rw [mul_c]
  refine Finset.sum_eq_zero fun b hb => ?_
  have hd := deg_add_deg_sub hb
  rcases Nat.lt_or_ge (deg b) p with h | h
  · rw [hu b h, zero_mul]
  · rw [hv (a - b) (by omega), mul_zero]

/-- **Top extraction.**  If the left factor vanishes strictly below the target
degree, only the top term of the convolution survives. -/
theorem mul_c_top {u v : LongJet d} {a : Multiindex d} {s : Real}
    (hu : ∀ b, deg b < deg a -> u.c b s = 0) :
    (mul u v).c a s = u.c a s * v.c 0 s := by
  rw [mul_c, Finset.sum_eq_single_of_mem a (self_mem_below a)]
  · have hz : a - a = (0 : Multiindex d) := by
      funext i
      show a i - a i = 0
      omega
    rw [hz]
  · intro b hb hne
    rw [hu b (deg_lt_of_mem_below_ne hb hne), zero_mul]

/-- **Bottom extraction.**  If the right factor vanishes strictly below the
target degree, only the bottom term survives. -/
theorem mul_c_bot {u v : LongJet d} {a : Multiindex d} {s : Real}
    (hv : ∀ b, deg b < deg a -> v.c b s = 0) :
    (mul u v).c a s = u.c 0 s * v.c a s := by
  have h0 : (0 : Multiindex d) ∈ below a := mem_below.2 fun _ => Nat.zero_le _
  rw [mul_c, Finset.sum_eq_single_of_mem (0 : Multiindex d) h0]
  · have hz : a - (0 : Multiindex d) = a := by
      funext i
      show a i - 0 = a i
      omega
    rw [hz]
  · intro b hb hne
    have hd := deg_add_deg_sub hb
    have hpos : 0 < deg b := by
      rcases Nat.eq_zero_or_pos (deg b) with h | h
      · exfalso
        refine hne (funext fun i => ?_)
        have hle := le_deg b i
        show b i = 0
        omega
      · exact h
    rw [hv (a - b) (by omega), mul_zero]

@[simp] theorem deg_single (j : Fin d) :
    deg (Pi.single j 1 : Multiindex d) = 1 := by
  simp [deg]

/-- A vanishing hypothesis below degree zero is vacuous. -/
theorem vanish_below_zero {u : LongJet d} {s : Real} :
    ∀ b : Multiindex d, deg b < 0 -> u.c b s = 0 :=
  fun _ h => absurd h (Nat.not_lt_zero _)

/-- A multi-index of total degree one is a coordinate index. -/
theorem eq_single_of_deg_eq_one {b : Multiindex d} (h : deg b = 1) :
    ∃ k, b = Pi.single k 1 := by
  have hex : ∃ k, b k ≠ 0 := by
    by_contra hc
    push Not at hc
    have hz : deg b = 0 := Finset.sum_eq_zero fun i _ => hc i
    omega
  obtain ⟨k, hk⟩ := hex
  refine ⟨k, funext fun j => ?_⟩
  by_cases hj : j = k
  · subst hj
    have hle := le_deg b j
    have hval : b j = 1 := by omega
    rw [hval]
    simp
  · have hpair : b k + b j ≤ deg b := by
      have hsub : ({k, j} : Finset (Fin d)) ⊆ Finset.univ := Finset.subset_univ _
      have hle := Finset.sum_le_sum_of_subset (f := fun i => b i) hsub
      rw [Finset.sum_pair (Ne.symm hj)] at hle
      exact hle
    have hbj : b j = 0 := by omega
    rw [hbj]
    simp [hj]

/-- The formal transverse derivative lowers the vanishing order by one. -/
theorem transverseDeriv_vanish {u : LongJet d} {p : Nat} {i : Fin d} {s : Real}
    (hu : ∀ b, deg b < p + 1 -> u.c b s = 0) :
    ∀ b, deg b < p -> (transverseDeriv i u).c b s = 0 := by
  intro b hb
  show ((b i + 1 : Nat) : Complex) * u.c (b + Pi.single i 1) s = 0
  rw [hu _ (by
    rw [LiuWang2025SemilinearWaveLongitudinalJet.deg_add_single]
    omega), mul_zero]

/-! ## No leakage: the variable-metric eikonal system is triangular

The degree-`alpha` coefficient of the eikonal reads the phase at total degree
`deg alpha + 1` through `transverseDeriv`.  Those contributions are exactly the
ones pairing a top-degree gradient against the *constant* gradient of the linear
phase, and the Fermi null row and column annihilate them.  Hence the
degree-`alpha` coefficient depends on the phase only through degrees at most
`deg alpha`: the system really is triangular, with no assumption to that
effect.
-/

theorem jetEikonal_congr_of_deg_le (Ass : LongJet d) (Bs : Fin d -> LongJet d)
    (Att : Fin d -> Fin d -> LongJet d) (i1 : Fin d)
    {phi phi' dphi dphi' : LongJet d} {a : Multiindex d} {s : Real}
    (ha : 1 ≤ deg a)
    (hphi : ∀ b, deg b ≤ deg a -> phi.c b s = phi'.c b s)
    (hdphi : ∀ b, deg b ≤ deg a -> dphi.c b s = dphi'.c b s)
    (hp1 : ∀ i, phi.c (Pi.single i 1) s = if i = i1 then 1 else 0)
    (hd0 : dphi.c 0 s = 0)
    (hd1 : ∀ k, dphi.c (Pi.single k 1) s = 0)
    (hnullRow : ∀ j, (Att i1 j).c 0 s = 0)
    (hnullCol : ∀ i, (Att i i1).c 0 s = 0) :
    jetEikonal Ass Bs Att phi dphi a s
      = jetEikonal Ass Bs Att phi' dphi' a s := by
  classical
  -- the differences vanish through degree `deg a`
  have hdd : ∀ b, deg b < deg a + 1 -> (sub dphi dphi').c b s = 0 := by
    intro b hb
    show dphi.c b s - dphi'.c b s = 0
    rw [hdphi b (by omega), sub_self]
  have hpp : ∀ b, deg b < deg a + 1 -> (sub phi phi').c b s = 0 := by
    intro b hb
    show phi.c b s - phi'.c b s = 0
    rw [hphi b (by omega), sub_self]
  have hgrad : ∀ (i : Fin d) b, deg b < deg a ->
      (transverseDeriv i (sub phi phi')).c b s = 0 :=
    fun i => transverseDeriv_vanish hpp
  -- `dphi` vanishes below degree two
  have hdlow : ∀ b, deg b < 2 -> dphi.c b s = 0 := by
    intro b hb
    interval_cases h : deg b
    · have hz : b = 0 := by
        refine funext fun i => ?_
        have := le_deg b i
        show b i = 0
        omega
      rw [hz]
      exact hd0
    · obtain ⟨k, hk⟩ := eq_single_of_deg_eq_one h
      rw [hk]
      exact hd1 k
  have hdlow' : ∀ b, deg b < 2 -> dphi'.c b s = 0 := by
    intro b hb
    rw [← hdphi b (by omega)]
    exact hdlow b hb
  -- block one
  have hb1 : (mul Ass (mul dphi dphi)).c a s = (mul Ass (mul dphi' dphi')).c a s := by
    have hkey : ∀ b, deg b < deg a + 1 ->
        (sub (mul dphi dphi) (mul dphi' dphi')).c b s = 0 := by
      intro b hb
      show (mul dphi dphi).c b s - (mul dphi' dphi').c b s = 0
      rw [mul_c_diff]
      rw [mul_c_vanish hdd vanish_below_zero (p := deg a + 1) (q := 0) (by omega),
        mul_c_vanish vanish_below_zero hdd (p := 0) (q := deg a + 1) (by omega)]
      ring
    have := mul_c_sub_right Ass (mul dphi dphi) (mul dphi' dphi') a s
    have hzero : (mul Ass (sub (mul dphi dphi) (mul dphi' dphi'))).c a s = 0 :=
      mul_c_vanish (p := 0) (q := deg a + 1) vanish_below_zero hkey (by omega)
    rw [hzero] at this
    linear_combination this
  -- block two
  have hb2 : ∀ i, (mul (Bs i) (mul dphi (transverseDeriv i phi))).c a s
      = (mul (Bs i) (mul dphi' (transverseDeriv i phi'))).c a s := by
    intro i
    have hkey : ∀ b, deg b < deg a + 1 ->
        (sub (mul dphi (transverseDeriv i phi))
          (mul dphi' (transverseDeriv i phi'))).c b s = 0 := by
      intro b hb
      show (mul dphi (transverseDeriv i phi)).c b s
        - (mul dphi' (transverseDeriv i phi')).c b s = 0
      rw [mul_c_diff]
      have hA : (mul (sub dphi dphi') (transverseDeriv i phi)).c b s = 0 :=
        mul_c_vanish hdd vanish_below_zero (p := deg a + 1) (q := 0) (by omega)
      have hsubgrad : ∀ e, deg e < deg a ->
          (sub (transverseDeriv i phi) (transverseDeriv i phi')).c e s = 0 := by
        intro e he
        show (transverseDeriv i phi).c e s - (transverseDeriv i phi').c e s = 0
        have := hgrad i e he
        rw [LiuWang2025SemilinearWaveLongitudinalJet.LongJet.transverseDeriv_c_sub]
          at this
        linear_combination this
      have hB : (mul dphi' (sub (transverseDeriv i phi)
          (transverseDeriv i phi'))).c b s = 0 :=
        mul_c_vanish hdlow' hsubgrad (p := 2) (q := deg a) (by omega)
      rw [hA, hB]
      ring
    have hthis := mul_c_sub_right (Bs i) (mul dphi (transverseDeriv i phi))
      (mul dphi' (transverseDeriv i phi')) a s
    have hzero : (mul (Bs i) (sub (mul dphi (transverseDeriv i phi))
        (mul dphi' (transverseDeriv i phi')))).c a s = 0 :=
      mul_c_vanish (p := 0) (q := deg a + 1) vanish_below_zero hkey (by omega)
    rw [hzero] at hthis
    linear_combination hthis
  -- block three: the leak survives termwise and is killed by the null row/column
  have hsubgrad : ∀ (i : Fin d) e, deg e < deg a ->
      (sub (transverseDeriv i phi) (transverseDeriv i phi')).c e s = 0 := by
    intro i e he
    show (transverseDeriv i phi).c e s - (transverseDeriv i phi').c e s = 0
    have hg := hgrad i e he
    rw [LiuWang2025SemilinearWaveLongitudinalJet.LongJet.transverseDeriv_c_sub] at hg
    linear_combination hg
  have hgrad0 : ∀ j, (transverseDeriv j phi).c 0 s = if j = i1 then 1 else 0 := by
    intro j
    rw [transverseDeriv_c_zero, hp1 j]
  have hgrad0' : ∀ j, (transverseDeriv j phi').c 0 s = if j = i1 then 1 else 0 := by
    intro j
    rw [transverseDeriv_c_zero, ← hphi _ (by rw [deg_single]; omega), hp1 j]
  have hb3 : ∀ i j, (mul (Att i j)
        (mul (transverseDeriv i phi) (transverseDeriv j phi))).c a s
      - (mul (Att i j)
        (mul (transverseDeriv i phi') (transverseDeriv j phi'))).c a s
      = (Att i j).c 0 s
        * ((sub (transverseDeriv i phi) (transverseDeriv i phi')).c a s
            * (if j = i1 then (1 : Complex) else 0)
          + (if i = i1 then (1 : Complex) else 0)
            * (sub (transverseDeriv j phi) (transverseDeriv j phi')).c a s) := by
    intro i j
    rw [mul_c_sub_right]
    have hvan : ∀ b, deg b < deg a ->
        (sub (mul (transverseDeriv i phi) (transverseDeriv j phi))
          (mul (transverseDeriv i phi') (transverseDeriv j phi'))).c b s = 0 := by
      intro b hb
      show (mul (transverseDeriv i phi) (transverseDeriv j phi)).c b s
        - (mul (transverseDeriv i phi') (transverseDeriv j phi')).c b s = 0
      rw [mul_c_diff]
      have hA : (mul (sub (transverseDeriv i phi) (transverseDeriv i phi'))
          (transverseDeriv j phi)).c b s = 0 :=
        mul_c_vanish (hsubgrad i) vanish_below_zero (p := deg a) (q := 0) (by omega)
      have hB : (mul (transverseDeriv i phi')
          (sub (transverseDeriv j phi) (transverseDeriv j phi'))).c b s = 0 :=
        mul_c_vanish vanish_below_zero (hsubgrad j) (p := 0) (q := deg a) (by omega)
      rw [hA, hB]
      ring
    rw [mul_c_bot hvan]
    congr 1
    show (mul (transverseDeriv i phi) (transverseDeriv j phi)).c a s
      - (mul (transverseDeriv i phi') (transverseDeriv j phi')).c a s = _
    rw [mul_c_diff, mul_c_top (hsubgrad i), mul_c_bot (hsubgrad j),
      hgrad0 j, hgrad0' i]
  have hb3sum : (∑ i, ∑ j, (mul (Att i j)
        (mul (transverseDeriv i phi) (transverseDeriv j phi))).c a s)
      = ∑ i, ∑ j, (mul (Att i j)
        (mul (transverseDeriv i phi') (transverseDeriv j phi'))).c a s := by
    have hdiff : (∑ i, ∑ j, (mul (Att i j)
          (mul (transverseDeriv i phi) (transverseDeriv j phi))).c a s)
        - ∑ i, ∑ j, (mul (Att i j)
          (mul (transverseDeriv i phi') (transverseDeriv j phi'))).c a s = 0 := by
      rw [← Finset.sum_sub_distrib]
      have hinner : ∀ i, (∑ j, (mul (Att i j)
            (mul (transverseDeriv i phi) (transverseDeriv j phi))).c a s)
          - ∑ j, (mul (Att i j)
            (mul (transverseDeriv i phi') (transverseDeriv j phi'))).c a s
          = (Att i i1).c 0 s
              * (sub (transverseDeriv i phi) (transverseDeriv i phi')).c a s
            + ∑ j, (if i = i1 then (1 : Complex) else 0) * ((Att i j).c 0 s
                * (sub (transverseDeriv j phi) (transverseDeriv j phi')).c a s) := by
        intro i
        rw [← Finset.sum_sub_distrib,
          Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) => hb3 i j]
        have hsplit : ∀ j : Fin d, (Att i j).c 0 s
              * ((sub (transverseDeriv i phi) (transverseDeriv i phi')).c a s
                  * (if j = i1 then (1 : Complex) else 0)
                + (if i = i1 then (1 : Complex) else 0)
                  * (sub (transverseDeriv j phi) (transverseDeriv j phi')).c a s)
            = (if j = i1 then (1 : Complex) else 0) * ((Att i j).c 0 s
                * (sub (transverseDeriv i phi) (transverseDeriv i phi')).c a s)
              + (if i = i1 then (1 : Complex) else 0) * ((Att i j).c 0 s
                * (sub (transverseDeriv j phi) (transverseDeriv j phi')).c a s) := by
          intro j
          ring
        rw [Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) => hsplit j,
          Finset.sum_add_distrib]
        congr 1
        · rw [Finset.sum_eq_single_of_mem i1 (Finset.mem_univ i1)]
          · rw [if_pos rfl, one_mul]
          · intro j _ hj
            rw [if_neg hj, zero_mul]
      rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hinner i,
        Finset.sum_add_distrib]
      have hA : (∑ i, (Att i i1).c 0 s
          * (sub (transverseDeriv i phi) (transverseDeriv i phi')).c a s) = 0 :=
        Finset.sum_eq_zero fun i _ => by rw [hnullCol i, zero_mul]
      have hB : (∑ i, ∑ j, (if i = i1 then (1 : Complex) else 0)
            * ((Att i j).c 0 s
              * (sub (transverseDeriv j phi) (transverseDeriv j phi')).c a s)) = 0 := by
        rw [Finset.sum_eq_single_of_mem i1 (Finset.mem_univ i1)]
        · refine Finset.sum_eq_zero fun j _ => ?_
          rw [hnullRow j, zero_mul, mul_zero]
        · intro i _ hi
          exact Finset.sum_eq_zero fun j _ => by rw [if_neg hi, zero_mul]
      rw [hA, hB]
      ring
    linear_combination hdiff
  rw [jetEikonal, jetEikonal, hb1,
    Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hb2 i, hb3sum]


/-! ## Extracting the longitudinal derivative

With triangularity in hand the degree-`alpha` equation can be read.  Comparing
two phases that agree in all degrees *strictly* below `deg alpha`, the
longitudinal-longitudinal block contributes nothing, the
longitudinal-transverse block contributes exactly
`2 A^{s i1}(0) d_s c_alpha`, and everything else sits in the
transverse-transverse block.  The coefficient `2 A^{s i1}(0)` is the source's
`2 lambda`, and it is computed here, not posited.
-/

theorem jetEikonal_longitudinal_extraction (Ass : LongJet d)
    (Bs : Fin d -> LongJet d) (Att : Fin d -> Fin d -> LongJet d) (i1 : Fin d)
    {phi phi' dphi dphi' : LongJet d} {a : Multiindex d} {s : Real}
    (ha : 2 ≤ deg a)
    (hphi : ∀ b, deg b < deg a -> phi.c b s = phi'.c b s)
    (hdphi : ∀ b, deg b < deg a -> dphi.c b s = dphi'.c b s)
    (hp1 : ∀ i, phi.c (Pi.single i 1) s = if i = i1 then 1 else 0)
    (hd0 : dphi.c 0 s = 0) (hd1 : ∀ k, dphi.c (Pi.single k 1) s = 0) :
    jetEikonal Ass Bs Att phi dphi a s - jetEikonal Ass Bs Att phi' dphi' a s
      = 2 * ((Bs i1).c 0 s * (dphi.c a s - dphi'.c a s))
        + ∑ i, ∑ j, ((mul (Att i j)
              (mul (transverseDeriv i phi) (transverseDeriv j phi))).c a s
            - (mul (Att i j)
              (mul (transverseDeriv i phi') (transverseDeriv j phi'))).c a s) := by
  classical
  -- low-degree vanishing of the longitudinal derivative
  have hdlow : ∀ b, deg b < 2 -> dphi.c b s = 0 := by
    intro b hb
    interval_cases h : deg b
    · have hz : b = 0 := by
        refine funext fun i => ?_
        have := le_deg b i
        show b i = 0
        omega
      rw [hz]
      exact hd0
    · obtain ⟨k, hk⟩ := eq_single_of_deg_eq_one h
      rw [hk]
      exact hd1 k
  have hdlow' : ∀ b, deg b < 2 -> dphi'.c b s = 0 := by
    intro b hb
    rw [← hdphi b (by omega)]
    exact hdlow b hb
  have hdd : ∀ b, deg b < deg a -> (sub dphi dphi').c b s = 0 := by
    intro b hb
    show dphi.c b s - dphi'.c b s = 0
    rw [hdphi b hb, sub_self]
  have hpp : ∀ b, deg b < deg a -> (sub phi phi').c b s = 0 := by
    intro b hb
    show phi.c b s - phi'.c b s = 0
    rw [hphi b hb, sub_self]
  -- the transverse gradient of the difference vanishes one degree lower
  obtain ⟨r', hr'⟩ : ∃ r', deg a = r' + 1 := ⟨deg a - 1, by omega⟩
  have hgradd : ∀ (i : Fin d) b, deg b < r' ->
      (sub (transverseDeriv i phi) (transverseDeriv i phi')).c b s = 0 := by
    intro i b hb
    have hstep : (transverseDeriv i (sub phi phi')).c b s = 0 := by
      refine transverseDeriv_vanish (p := r') ?_ b hb
      intro e he
      exact hpp e (by omega)
    rw [LiuWang2025SemilinearWaveLongitudinalJet.LongJet.transverseDeriv_c_sub] at hstep
    show (transverseDeriv i phi).c b s - (transverseDeriv i phi').c b s = 0
    linear_combination hstep
  -- block one contributes nothing
  have hb1 : (mul Ass (mul dphi dphi)).c a s
      - (mul Ass (mul dphi' dphi')).c a s = 0 := by
    have hinner : ∀ b, deg b < deg a + 2 ->
        (sub (mul dphi dphi) (mul dphi' dphi')).c b s = 0 := by
      intro b hb
      show (mul dphi dphi).c b s - (mul dphi' dphi').c b s = 0
      rw [mul_c_diff]
      have hA : (mul (sub dphi dphi') dphi).c b s = 0 :=
        mul_c_vanish (p := deg a) (q := 2) hdd hdlow (by omega)
      have hB : (mul dphi' (sub dphi dphi')).c b s = 0 :=
        mul_c_vanish (p := 2) (q := deg a) hdlow' hdd (by omega)
      rw [hA, hB]
      ring
    have hz : (mul Ass (sub (mul dphi dphi) (mul dphi' dphi'))).c a s = 0 :=
      mul_c_vanish (p := 0) (q := deg a + 2) vanish_below_zero hinner (by omega)
    have hsplit := mul_c_sub_right Ass (mul dphi dphi) (mul dphi' dphi') a s
    rw [hz] at hsplit
    exact hsplit
  -- block two contributes exactly the longitudinal derivative
  have hgrad0 : ∀ i, (transverseDeriv i phi).c 0 s = if i = i1 then 1 else 0 := by
    intro i
    rw [transverseDeriv_c_zero, hp1 i]
  have hb2 : ∀ i, (mul (Bs i) (mul dphi (transverseDeriv i phi))).c a s
      - (mul (Bs i) (mul dphi' (transverseDeriv i phi'))).c a s
      = (Bs i).c 0 s * ((dphi.c a s - dphi'.c a s)
          * (if i = i1 then (1 : Complex) else 0)) := by
    intro i
    have hW : ∀ b, deg b < deg a ->
        (sub (mul dphi (transverseDeriv i phi))
          (mul dphi' (transverseDeriv i phi'))).c b s = 0 := by
      intro b hb
      show (mul dphi (transverseDeriv i phi)).c b s
        - (mul dphi' (transverseDeriv i phi')).c b s = 0
      rw [mul_c_diff]
      have hA : (mul (sub dphi dphi') (transverseDeriv i phi)).c b s = 0 :=
        mul_c_vanish (p := deg a) (q := 0) hdd vanish_below_zero (by omega)
      have hB : (mul dphi' (sub (transverseDeriv i phi)
          (transverseDeriv i phi'))).c b s = 0 :=
        mul_c_vanish (p := 2) (q := r') hdlow' (hgradd i) (by omega)
      rw [hA, hB]
      ring
    have hsplit := mul_c_sub_right (Bs i) (mul dphi (transverseDeriv i phi))
      (mul dphi' (transverseDeriv i phi')) a s
    rw [hsplit, mul_c_bot hW]
    congr 1
    show (mul dphi (transverseDeriv i phi)).c a s
      - (mul dphi' (transverseDeriv i phi')).c a s = _
    rw [mul_c_diff]
    have hB : (mul dphi' (sub (transverseDeriv i phi)
        (transverseDeriv i phi'))).c a s = 0 :=
      mul_c_vanish (p := 2) (q := r') hdlow' (hgradd i) (by omega)
    rw [hB, mul_c_top hdd, hgrad0 i]
    show (dphi.c a s - dphi'.c a s) * (if i = i1 then (1 : Complex) else 0) + 0 = _
    ring
  have hb2sum : (∑ i, (mul (Bs i) (mul dphi (transverseDeriv i phi))).c a s)
      - ∑ i, (mul (Bs i) (mul dphi' (transverseDeriv i phi'))).c a s
      = (Bs i1).c 0 s * (dphi.c a s - dphi'.c a s) := by
    rw [← Finset.sum_sub_distrib,
      Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hb2 i,
      Finset.sum_eq_single_of_mem i1 (Finset.mem_univ i1)]
    · rw [if_pos rfl]
      ring
    · intro i _ hi
      rw [if_neg hi]
      ring
  have hb3 : (∑ i, ∑ j, ((mul (Att i j)
        (mul (transverseDeriv i phi) (transverseDeriv j phi))).c a s
      - (mul (Att i j)
        (mul (transverseDeriv i phi') (transverseDeriv j phi'))).c a s))
      = (∑ i, ∑ j, (mul (Att i j)
          (mul (transverseDeriv i phi) (transverseDeriv j phi))).c a s)
        - ∑ i, ∑ j, (mul (Att i j)
          (mul (transverseDeriv i phi') (transverseDeriv j phi'))).c a s := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_sub_distrib _ _
  rw [jetEikonal, jetEikonal, hb3]
  linear_combination hb1 + 2 * hb2sum

/-- **The eikonal coefficient is continuous in the longitudinal parameter**,
automatically, from the derivative certificates of the jets involved. -/
theorem continuous_jetEikonal (Ass : LongJet d) (Bs : Fin d -> LongJet d)
    (Att : Fin d -> Fin d -> LongJet d) (phi dphi : LongJet d)
    (a : Multiindex d) :
    Continuous fun s => jetEikonal Ass Bs Att phi dphi a s := by
  refine Continuous.add (Continuous.add ((mul Ass (mul dphi dphi)).continuous_c a) ?_) ?_
  · exact continuous_const.mul
      (continuous_finset_sum _ fun i _ =>
        (mul (Bs i) (mul dphi (transverseDeriv i phi))).continuous_c a)
  · exact continuous_finset_sum _ fun i _ =>
      continuous_finset_sum _ fun j _ =>
        (mul (Att i j)
          (mul (transverseDeriv i phi) (transverseDeriv j phi))).continuous_c a

/-- The certified longitudinal derivative of the eikonal coefficient, read off
from the derivative fields already carried by the jets. -/
def jetEikonalDeriv (Ass : LongJet d) (Bs : Fin d -> LongJet d)
    (Att : Fin d -> Fin d -> LongJet d) (phi dphi : LongJet d)
    (a : Multiindex d) (s : Real) : Complex :=
  (mul Ass (mul dphi dphi)).dc a s
    + 2 * ∑ i, (mul (Bs i) (mul dphi (transverseDeriv i phi))).dc a s
    + ∑ i, ∑ j,
        (mul (Att i j)
          (mul (transverseDeriv i phi) (transverseDeriv j phi))).dc a s

/-- **The eikonal coefficient is differentiable in the longitudinal parameter**,
automatically, with `jetEikonalDeriv` as derivative. -/
theorem hasDerivAt_jetEikonal (Ass : LongJet d) (Bs : Fin d -> LongJet d)
    (Att : Fin d -> Fin d -> LongJet d) (phi dphi : LongJet d)
    (a : Multiindex d) (s : Real) :
    HasDerivAt (fun v => jetEikonal Ass Bs Att phi dphi a v)
      (jetEikonalDeriv Ass Bs Att phi dphi a s) s := by
  refine HasDerivAt.add (HasDerivAt.add ((mul Ass (mul dphi dphi)).hasDeriv a s) ?_) ?_
  · exact HasDerivAt.const_mul (2 : Complex)
      (hasDerivAt_finsum
        (fun i v => (mul (Bs i) (mul dphi (transverseDeriv i phi))).c a v)
        (fun i => (mul (Bs i) (mul dphi (transverseDeriv i phi))).dc a s) s
        fun i => (mul (Bs i) (mul dphi (transverseDeriv i phi))).hasDeriv a s)
  · refine hasDerivAt_finsum _ _ s fun i => ?_
    exact hasDerivAt_finsum
      (fun j v => (mul (Att i j)
        (mul (transverseDeriv i phi) (transverseDeriv j phi))).c a v)
      (fun j => (mul (Att i j)
        (mul (transverseDeriv i phi) (transverseDeriv j phi))).dc a s) s
      fun j => (mul (Att i j)
        (mul (transverseDeriv i phi) (transverseDeriv j phi))).hasDeriv a s

/-- **The eikonal coefficient's derivative is continuous** once the metric and
phase jets are. -/
theorem continuous_jetEikonalDeriv {Ass : LongJet d} {Bs : Fin d -> LongJet d}
    {Att : Fin d -> Fin d -> LongJet d} {phi dphi : LongJet d}
    (hAss : Ass.C1) (hBs : ∀ i, (Bs i).C1) (hAtt : ∀ i j, (Att i j).C1)
    (hphi : phi.C1) (hdphi : dphi.C1) (a : Multiindex d) :
    Continuous fun s => jetEikonalDeriv Ass Bs Att phi dphi a s := by
  refine Continuous.add (Continuous.add (hAss.mul (hdphi.mul hdphi) a) ?_) ?_
  · exact continuous_const.mul (continuous_finset_sum _ fun i _ =>
      (hBs i).mul (hdphi.mul (hphi.transverseDeriv i)) a)
  · exact continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ =>
      (hAtt i j).mul ((hphi.transverseDeriv i).mul (hphi.transverseDeriv j)) a

/-- Convolution against a factor supported at a single index collapses to one
term.  Used to evaluate concrete matrix entries. -/
theorem mul_c_of_left_single (u v : LongJet d) (a a0 : Multiindex d) (s : Real)
    (ha0 : a0 ∈ below a)
    (hu : ∀ b ∈ below a, b ≠ a0 -> u.c b s = 0) :
    (mul u v).c a s = u.c a0 s * v.c (a - a0) s :=
  Finset.sum_eq_single_of_mem a0 ha0 fun b hb hne => by rw [hu b hb hne, zero_mul]

end LiuWang2025SemilinearWaveJetOperators
