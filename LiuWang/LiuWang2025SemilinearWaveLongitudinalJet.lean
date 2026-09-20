import LiuWang.LiuWang2025SemilinearWaveTransverseJet
import LiuWang.LiuWang2025SemilinearWaveChartWKB

/-!
# Liu-Wang semilinear wave: transverse jets along the geodesic

The source's phase and amplitude coefficients are functions of the longitudinal
geodesic parameter `s`, one for each transverse multi-index.  This file gives
that object a type.

A `LongJet d` carries a coefficient family `c : Multiindex d -> Real -> Complex`
together with its longitudinal derivative `dc` and a `HasDerivAt` witness for
every multi-index and every `s`.  The jet-level operations -- sum, scalar
multiple, convolution product, transverse differentiation, truncation by total
transverse degree -- are all defined *with* their derivative data, so the
longitudinal product rule (`mul_dc`) is a theorem about the construction, not a
field.

The last section proves the two correspondences that make the coefficient
calculus legitimate:

* `monomial_mul_sub` and `jmul_coeff_eq` : the convolution coefficient really
  is the coefficient of `z^alpha` in the product of the two polynomials;
* `hasDerivAt_monomial` and `jderiv_coeff_eq` : the formal derivative `jderiv`
  really is the coefficient family of the transverse partial derivative, with
  the derivative certified by `HasDerivAt`.
-/

noncomputable section

open scoped BigOperators

namespace LiuWang2025SemilinearWaveLongitudinalJet

open LiuWang2025SemilinearWaveTransverseJet
open LiuWang2025SemilinearWaveChartWKB

variable {d : Nat}

/-! ## Coefficient families along the geodesic -/

/-- A transverse jet whose coefficients move along the geodesic, together with
their longitudinal derivatives. -/
structure LongJet (d : Nat) where
  /-- The coefficient of `z^alpha` at longitudinal parameter `s`. -/
  c : Multiindex d -> Real -> Complex
  /-- Its longitudinal derivative. -/
  dc : Multiindex d -> Real -> Complex
  /-- Certification that `dc` is the derivative of `c`. -/
  hasDeriv : ∀ (a : Multiindex d) (s : Real), HasDerivAt (c a) (dc a s) s

namespace LongJet

/-- Sum of two coefficient families. -/
def add (u v : LongJet d) : LongJet d where
  c := fun a s => u.c a s + v.c a s
  dc := fun a s => u.dc a s + v.dc a s
  hasDeriv := fun a s => (u.hasDeriv a s).add (v.hasDeriv a s)

/-- Constant scalar multiple. -/
def smul (k : Complex) (u : LongJet d) : LongJet d where
  c := fun a s => k * u.c a s
  dc := fun a s => k * u.dc a s
  hasDeriv := fun a s => (u.hasDeriv a s).const_mul k

/-- Convolution product: the coefficients of the product polynomial. -/
def mul (u v : LongJet d) : LongJet d where
  c := fun a s => ∑ b ∈ below a, u.c b s * v.c (a - b) s
  dc := fun a s =>
    ∑ b ∈ below a, (u.dc b s * v.c (a - b) s + u.c b s * v.dc (a - b) s)
  hasDeriv := by
    intro a s
    exact HasDerivAt.fun_sum fun b _ => (u.hasDeriv b s).mul (v.hasDeriv (a - b) s)

/-- Difference of two coefficient families. -/
def sub (u v : LongJet d) : LongJet d where
  c := fun a s => u.c a s - v.c a s
  dc := fun a s => u.dc a s - v.dc a s
  hasDeriv := fun a s => (u.hasDeriv a s).sub (v.hasDeriv a s)

@[simp] theorem sub_c (u v : LongJet d) (a : Multiindex d) (s : Real) :
    (sub u v).c a s = u.c a s - v.c a s := rfl

/-- Formal transverse differentiation in the `i`-th variable. -/
def transverseDeriv (i : Fin d) (u : LongJet d) : LongJet d where
  c := fun a s => ((a i + 1 : Nat) : Complex) * u.c (a + Pi.single i 1) s
  dc := fun a s => ((a i + 1 : Nat) : Complex) * u.dc (a + Pi.single i 1) s
  hasDeriv := fun a s => (u.hasDeriv (a + Pi.single i 1) s).const_mul _

/-- The convolution is bilinear: subtraction in the left slot. -/
theorem mul_c_sub_left (u u' v : LongJet d) (a : Multiindex d) (s : Real) :
    (mul u v).c a s - (mul u' v).c a s = (mul (sub u u') v).c a s := by
  show (∑ b ∈ below a, u.c b s * v.c (a - b) s)
      - ∑ b ∈ below a, u'.c b s * v.c (a - b) s
    = ∑ b ∈ below a, (u.c b s - u'.c b s) * v.c (a - b) s
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun b _ => by ring

/-- ... and in the right slot. -/
theorem mul_c_sub_right (u v v' : LongJet d) (a : Multiindex d) (s : Real) :
    (mul u v).c a s - (mul u v').c a s = (mul u (sub v v')).c a s := by
  show (∑ b ∈ below a, u.c b s * v.c (a - b) s)
      - ∑ b ∈ below a, u.c b s * v'.c (a - b) s
    = ∑ b ∈ below a, u.c b s * (v.c (a - b) s - v'.c (a - b) s)
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun b _ => by ring

/-- The convolution is additive in the left slot. -/
theorem mul_c_add_left (u u' v : LongJet d) (a : Multiindex d) (s : Real) :
    (mul (add u u') v).c a s = (mul u v).c a s + (mul u' v).c a s := by
  show (∑ b ∈ below a, (u.c b s + u'.c b s) * v.c (a - b) s)
    = (∑ b ∈ below a, u.c b s * v.c (a - b) s)
      + ∑ b ∈ below a, u'.c b s * v.c (a - b) s
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun b _ => by ring

/-- ... and in the right slot. -/
theorem mul_c_add_right (u v v' : LongJet d) (a : Multiindex d) (s : Real) :
    (mul u (add v v')).c a s = (mul u v).c a s + (mul u v').c a s := by
  show (∑ b ∈ below a, u.c b s * (v.c (a - b) s + v'.c (a - b) s))
    = (∑ b ∈ below a, u.c b s * v.c (a - b) s)
      + ∑ b ∈ below a, u.c b s * v'.c (a - b) s
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun b _ => by ring

/-- The convolution is homogeneous in the left slot. -/
theorem mul_c_smul_left (k : Complex) (u v : LongJet d) (a : Multiindex d)
    (s : Real) : (mul (smul k u) v).c a s = k * (mul u v).c a s := by
  show (∑ b ∈ below a, (k * u.c b s) * v.c (a - b) s)
    = k * ∑ b ∈ below a, u.c b s * v.c (a - b) s
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun b _ => by ring

/-- ... and in the right slot. -/
theorem mul_c_smul_right (k : Complex) (u v : LongJet d) (a : Multiindex d)
    (s : Real) : (mul u (smul k v)).c a s = k * (mul u v).c a s := by
  show (∑ b ∈ below a, u.c b s * (k * v.c (a - b) s))
    = k * ∑ b ∈ below a, u.c b s * v.c (a - b) s
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun b _ => by ring

/-- The formal transverse derivative is additive. -/
theorem transverseDeriv_c_add (i : Fin d) (u v : LongJet d) (a : Multiindex d)
    (s : Real) :
    (transverseDeriv i (add u v)).c a s
      = (transverseDeriv i u).c a s + (transverseDeriv i v).c a s := by
  show ((a i + 1 : Nat) : Complex) * (u.c (a + Pi.single i 1) s
      + v.c (a + Pi.single i 1) s)
    = ((a i + 1 : Nat) : Complex) * u.c (a + Pi.single i 1) s
      + ((a i + 1 : Nat) : Complex) * v.c (a + Pi.single i 1) s
  ring

/-- ... and homogeneous. -/
theorem transverseDeriv_c_smul (i : Fin d) (k : Complex) (u : LongJet d)
    (a : Multiindex d) (s : Real) :
    (transverseDeriv i (smul k u)).c a s = k * (transverseDeriv i u).c a s := by
  show ((a i + 1 : Nat) : Complex) * (k * u.c (a + Pi.single i 1) s)
    = k * (((a i + 1 : Nat) : Complex) * u.c (a + Pi.single i 1) s)
  ring

/-- A finite sum of coefficient families. -/
def sumJet {iota : Type*} [Fintype iota] (f : iota -> LongJet d) : LongJet d where
  c := fun a s => ∑ i, (f i).c a s
  dc := fun a s => ∑ i, (f i).dc a s
  hasDeriv := fun a s => HasDerivAt.fun_sum fun i _ => (f i).hasDeriv a s

@[simp] theorem sumJet_c {iota : Type*} [Fintype iota] (f : iota -> LongJet d)
    (a : Multiindex d) (s : Real) : (sumJet f).c a s = ∑ i, (f i).c a s := rfl

/-- The convolution distributes over finite sums in the left slot. -/
theorem mul_c_sum_left {iota : Type*} [Fintype iota] (f : iota -> LongJet d)
    (v : LongJet d) (a : Multiindex d) (s : Real) :
    (mul (sumJet f) v).c a s = ∑ i, (mul (f i) v).c a s := by
  show (∑ b ∈ below a, (∑ i, (f i).c b s) * v.c (a - b) s)
    = ∑ i, ∑ b ∈ below a, (f i).c b s * v.c (a - b) s
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_mul]

/-- ... and in the right slot. -/
theorem mul_c_sum_right {iota : Type*} [Fintype iota] (u : LongJet d)
    (f : iota -> LongJet d) (a : Multiindex d) (s : Real) :
    (mul u (sumJet f)).c a s = ∑ i, (mul u (f i)).c a s := by
  show (∑ b ∈ below a, u.c b s * ∑ i, (f i).c (a - b) s)
    = ∑ i, ∑ b ∈ below a, u.c b s * (f i).c (a - b) s
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.mul_sum]

/-- The formal transverse derivative distributes over finite sums. -/
theorem transverseDeriv_c_sum {iota : Type*} [Fintype iota] (i : Fin d)
    (f : iota -> LongJet d) (a : Multiindex d) (s : Real) :
    (transverseDeriv i (sumJet f)).c a s
      = ∑ k, (transverseDeriv i (f k)).c a s := by
  show ((a i + 1 : Nat) : Complex) * ∑ k, (f k).c (a + Pi.single i 1) s
    = ∑ k, ((a i + 1 : Nat) : Complex) * (f k).c (a + Pi.single i 1) s
  rw [Finset.mul_sum]

/-- **The bilinear difference identity.**  Comparing two convolutions splits
into one difference in each slot. -/
theorem mul_c_diff (u u' v v' : LongJet d) (a : Multiindex d) (s : Real) :
    (mul u v).c a s - (mul u' v').c a s
      = (mul (sub u u') v).c a s + (mul u' (sub v v')).c a s := by
  rw [← mul_c_sub_left, ← mul_c_sub_right]
  ring

/-- The formal transverse derivative is linear. -/
theorem transverseDeriv_c_sub (i : Fin d) (u v : LongJet d) (a : Multiindex d)
    (s : Real) :
    (transverseDeriv i (sub u v)).c a s
      = (transverseDeriv i u).c a s - (transverseDeriv i v).c a s := by
  show ((a i + 1 : Nat) : Complex) * (u.c (a + Pi.single i 1) s
      - v.c (a + Pi.single i 1) s)
    = ((a i + 1 : Nat) : Complex) * u.c (a + Pi.single i 1) s
      - ((a i + 1 : Nat) : Complex) * v.c (a + Pi.single i 1) s
  ring

/-- Longitudinal differentiation is reading off the stored derivative; the
result is again a jet once second derivatives are supplied. -/
def longitudinalDeriv (u : LongJet d) (d2 : Multiindex d -> Real -> Complex)
    (h : ∀ a s, HasDerivAt (u.dc a) (d2 a s) s) : LongJet d where
  c := u.dc
  dc := d2
  hasDeriv := h

/-- Truncation to total transverse degree at most `N`. -/
def truncate (N : Nat) (u : LongJet d) : LongJet d where
  c := fun a s => if deg a ≤ N then u.c a s else 0
  dc := fun a s => if deg a ≤ N then u.dc a s else 0
  hasDeriv := by
    intro a s
    by_cases h : deg a ≤ N
    · simpa [h] using u.hasDeriv a s
    · simpa [h] using (hasDerivAt_const s (0 : Complex))

@[simp] theorem add_c (u v : LongJet d) (a : Multiindex d) (s : Real) :
    (add u v).c a s = u.c a s + v.c a s := rfl

@[simp] theorem smul_c (k : Complex) (u : LongJet d) (a : Multiindex d) (s : Real) :
    (smul k u).c a s = k * u.c a s := rfl

@[simp] theorem mul_c (u v : LongJet d) (a : Multiindex d) (s : Real) :
    (mul u v).c a s = ∑ b ∈ below a, u.c b s * v.c (a - b) s := rfl

/-- **The longitudinal product rule at jet level.**  The stored derivative of
the convolution is the Leibniz combination of the two coefficient
convolutions -- proved from the `HasDerivAt` witnesses, not declared. -/
theorem mul_dc (u v : LongJet d) (a : Multiindex d) (s : Real) :
    (mul u v).dc a s
      = (∑ b ∈ below a, u.dc b s * v.c (a - b) s)
        + ∑ b ∈ below a, u.c b s * v.dc (a - b) s := by
  show (∑ b ∈ below a, (u.dc b s * v.c (a - b) s + u.c b s * v.dc (a - b) s)) = _
  rw [← Finset.sum_add_distrib]

@[simp] theorem truncate_c_of_le {N : Nat} (u : LongJet d) {a : Multiindex d}
    (h : deg a ≤ N) (s : Real) : (truncate N u).c a s = u.c a s := by
  simp [truncate, h]

@[simp] theorem truncate_c_of_gt {N : Nat} (u : LongJet d) {a : Multiindex d}
    (h : ¬ deg a ≤ N) (s : Real) : (truncate N u).c a s = 0 := by
  simp [truncate, h]

end LongJet

/-! ## The two coefficient correspondences -/

/-- Splitting a monomial along a dominated multi-index. -/
theorem monomial_mul_sub {a b : Multiindex d} (hb : b ∈ below a)
    (z : Fin d -> Real) :
    monomial b z * monomial (a - b) z = monomial a z := by
  rw [monomial, monomial, monomial, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← pow_add]
  congr 1
  exact Nat.add_sub_cancel' (mem_below.1 hb i)

/-- **The convolution coefficient is the coefficient of `z^alpha` in the
product.**  Each convolution term is exactly the product of the two monomial
terms it comes from. -/
theorem jmul_coeff_eq (u v : Jet d) (a : Multiindex d) (z : Fin d -> Real) :
    jmul u v a * monomial a z
      = ∑ b ∈ below a, (u b * monomial b z) * (v (a - b) * monomial (a - b) z) := by
  rw [jmul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun b hb => ?_
  rw [← monomial_mul_sub hb z]
  ring

/-- **The transverse derivative of a monomial**, computed rather than
postulated. -/
theorem hasDerivAt_monomial (a : Multiindex d) (i : Fin d) (z : Fin d -> Real) :
    HasDerivAt (fun t : Real => monomial a (z + t • dir i))
      (((a i : Nat) : Complex) * ((z i : Real) : Complex) ^ (a i - 1)
        * ∏ j ∈ Finset.univ.erase i, ((z j : Real) : Complex) ^ (a j)) 0 := by
  have hreal : HasDerivAt (fun t : Real => z i + t) 1 0 := by
    simpa using (hasDerivAt_id (0 : Real)).const_add (z i)
  have hline : HasDerivAt (fun t : Real => (((z i + t : Real)) : Complex)) 1 0 := by
    simpa using hreal.ofReal_comp
  have hpow : HasDerivAt
      (fun t : Real => (((z i + t : Real)) : Complex) ^ (a i))
      (((a i : Nat) : Complex) * (((z i : Real)) : Complex) ^ (a i - 1) * 1) 0 := by
    simpa using hline.pow (a i)
  have hmul := hpow.mul_const
    (∏ j ∈ Finset.univ.erase i, ((z j : Real) : Complex) ^ (a j))
  have hfun : (fun t : Real => monomial a (z + t • dir i))
      = fun t : Real => (((z i + t : Real)) : Complex) ^ (a i)
          * ∏ j ∈ Finset.univ.erase i, ((z j : Real) : Complex) ^ (a j) := by
    funext t
    rw [monomial, ← Finset.mul_prod_erase Finset.univ
      (fun j => (((z + t • dir i) j : Real) : Complex) ^ (a j)) (Finset.mem_univ i)]
    have hi : ((z + t • dir i) i : Real) = z i + t := by
      simp [dir, Pi.single]
    have hrest : ∀ j ∈ Finset.univ.erase i,
        (((z + t • dir i) j : Real) : Complex) ^ (a j)
          = ((z j : Real) : Complex) ^ (a j) := by
      intro j hj
      have hji : j ≠ i := (Finset.mem_erase.1 hj).1
      simp [dir, hji]
    rw [hi, Finset.prod_congr rfl hrest]
  rw [hfun]
  refine hmul.congr_deriv ?_
  ring


/-! ## Chart functions realized from a longitudinal jet

The constructed coefficient family names an actual finite polynomial function
on the chart.  The three theorems below say that its value and both its
derivatives are exactly what the coefficient calculus predicts.
-/

/-- The chart function a longitudinal jet realizes at parameter `s`. -/
def chartValue (u : LongJet d) (S : Finset (Multiindex d)) (s : Real)
    (z : Fin d -> Real) : Complex :=
  realize S (fun a => u.c a s) z

/-- **The longitudinal derivative of the realization is the realization of the
derivative coefficients.** -/
theorem hasDerivAt_chartValue_longitudinal (u : LongJet d)
    (S : Finset (Multiindex d)) (z : Fin d -> Real) (s : Real) :
    HasDerivAt (fun t : Real => chartValue u S t z)
      (realize S (fun a => u.dc a s) z) s := by
  show HasDerivAt (fun t : Real => ∑ a ∈ S, u.c a t * monomial a z)
    (∑ a ∈ S, u.dc a s * monomial a z) s
  exact HasDerivAt.fun_sum fun a _ => (u.hasDeriv a s).mul_const (monomial a z)

/-- **The transverse derivative of the realization**, computed term by term
from `hasDerivAt_monomial`. -/
theorem hasDerivAt_realize_transverse (S : Finset (Multiindex d)) (c : Jet d)
    (i : Fin d) (z : Fin d -> Real) :
    HasDerivAt (fun t : Real => realize S c (z + t • dir i))
      (∑ a ∈ S, c a * (((a i : Nat) : Complex) * ((z i : Real) : Complex) ^ (a i - 1)
        * ∏ j ∈ Finset.univ.erase i, ((z j : Real) : Complex) ^ (a j))) 0 := by
  show HasDerivAt (fun t : Real => ∑ a ∈ S, c a * monomial a (z + t • dir i)) _ 0
  exact HasDerivAt.fun_sum fun a _ => (hasDerivAt_monomial a i z).const_mul (c a)

/-- The value at the beam centre is the degree-zero coefficient. -/
theorem realize_at_origin (S : Finset (Multiindex d)) (c : Jet d)
    (h0 : (0 : Multiindex d) ∈ S) :
    realize S c (0 : Fin d -> Real) = c 0 := by
  rw [realize, Finset.sum_eq_single_of_mem (0 : Multiindex d) h0]
  · simp
  · intro a _ ha
    have hne : ∃ i, a i ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact ha (funext hcon)
    obtain ⟨i, hi⟩ := hne
    have hzero : monomial a (0 : Fin d -> Real) = 0 := by
      rw [monomial]
      refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
      simp [hi]
    rw [hzero, mul_zero]

/-- **The first transverse derivative at the beam centre is the degree-one
coefficient.**  Every other multi-index contributes zero, so the formal jet
coefficient and the actual derivative agree. -/
theorem realize_transverse_deriv_at_origin (S : Finset (Multiindex d)) (c : Jet d)
    (i : Fin d) (hi : (Pi.single i 1 : Multiindex d) ∈ S) :
    HasDerivAt (fun t : Real => realize S c ((0 : Fin d -> Real) + t • dir i))
      (c (Pi.single i 1)) 0 := by
  have h := hasDerivAt_realize_transverse S c i (0 : Fin d -> Real)
  refine h.congr_deriv ?_
  rw [Finset.sum_eq_single_of_mem (Pi.single i 1 : Multiindex d) hi]
  · have hii : (Pi.single i 1 : Multiindex d) i = 1 := by simp
    rw [hii]
    have hrest : ∀ j ∈ Finset.univ.erase i,
        (((0 : Fin d -> Real) j : Real) : Complex) ^ ((Pi.single i 1 : Multiindex d) j)
          = 1 := by
      intro j hj
      have hji : j ≠ i := (Finset.mem_erase.1 hj).1
      have : (Pi.single i 1 : Multiindex d) j = 0 := by
        simp [hji]
      rw [this, pow_zero]
    rw [Finset.prod_congr rfl hrest, Finset.prod_const_one]
    norm_num
  · intro a _ ha
    rcases Nat.eq_zero_or_pos (a i) with hai | hai
    · rw [hai]
      norm_num
    · rcases Nat.lt_or_ge (a i) 2 with hlt | hge
      · have hai1 : a i = 1 := by omega
        have hex : ∃ j, j ≠ i ∧ a j ≠ 0 := by
          by_contra hcon
          push Not at hcon
          refine ha (funext fun j => ?_)
          by_cases hj : j = i
          · subst hj; simp [hai1]
          · rw [hcon j hj]
            simp [hj]
        obtain ⟨j, hji, hj0⟩ := hex
        have hzero : (∏ k ∈ Finset.univ.erase i,
            (((0 : Fin d -> Real) k : Real) : Complex) ^ (a k)) = 0 := by
          refine Finset.prod_eq_zero (Finset.mem_erase.2 ⟨hji, Finset.mem_univ j⟩) ?_
          simp [hj0]
        rw [hzero]
        ring
      · have hpow : (((0 : Fin d -> Real) i : Real) : Complex) ^ (a i - 1) = 0 := by
          have : a i - 1 ≠ 0 := by omega
          simp [this]
        rw [hpow]
        ring


/-! ## Normalization audit

`realize S c z = sum_alpha c alpha * z^alpha` with `z^alpha = prod_i z_i^{alpha_i}`,
so `c alpha` is the **ordinary monomial coefficient**, *not* a derivative divided
by `alpha!`.  Two consequences, both proved below.

* The convolution `jmul` is the right product rule for this normalization, with
  no combinatorial factor: `jmul_coeff_eq` above.
* The formal derivative must carry the factor `alpha_i + 1`, which is exactly
  what `jderiv` does; `hasDerivAt_realize_jderiv` proves that `jderiv` is the
  coefficient family of the transverse partial derivative.

Consequently `partial^alpha f(0) = alpha! * c alpha`: at `|alpha| = 0` and
`|alpha| = 1` the factorial is `1`, which is why `realize_at_origin` and
`realize_transverse_deriv_at_origin` read off the coefficient directly, and from
degree two onwards the factor is genuinely present.  Nothing in the development
divides by `alpha!`, so the normalization is consistent throughout.
-/

/-- The multi-indices of total degree at most `N`. -/
def degreeLE (d N : Nat) : Finset (Multiindex d) :=
  (Fintype.piFinset fun _ => Finset.range (N + 1)).filter (fun a => deg a ≤ N)

theorem le_deg (a : Multiindex d) (i : Fin d) : a i ≤ deg a :=
  Finset.single_le_sum (f := fun j => a j) (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ i)

@[simp] theorem mem_degreeLE {N : Nat} {a : Multiindex d} :
    a ∈ degreeLE d N ↔ deg a ≤ N := by
  rw [degreeLE, Finset.mem_filter]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    rw [Fintype.mem_piFinset]
    intro i
    rw [Finset.mem_range]
    exact Nat.lt_succ_of_le (le_trans (le_deg a i) h)

/-- Splitting off one variable from a monomial whose exponent there is
positive. -/
theorem monomial_sub_single {a : Multiindex d} {i : Fin d} (_hi : 1 ≤ a i)
    (z : Fin d -> Real) :
    ((z i : Real) : Complex) ^ (a i - 1)
        * ∏ j ∈ Finset.univ.erase i, ((z j : Real) : Complex) ^ (a j)
      = monomial (a - (Pi.single i 1 : Multiindex d)) z := by
  have hsplit := Finset.mul_prod_erase (Finset.univ : Finset (Fin d))
    (fun j => ((z j : Real) : Complex) ^ ((a - (Pi.single i 1 : Multiindex d)) j))
    (Finset.mem_univ i)
  rw [monomial, ← hsplit]
  show ((z i : Real) : Complex) ^ (a i - 1)
      * ∏ j ∈ Finset.univ.erase i, ((z j : Real) : Complex) ^ (a j)
    = ((z i : Real) : Complex) ^ ((a - (Pi.single i 1 : Multiindex d)) i)
      * ∏ j ∈ Finset.univ.erase i,
          ((z j : Real) : Complex) ^ ((a - (Pi.single i 1 : Multiindex d)) j)
  have hii : (a - (Pi.single i 1 : Multiindex d)) i = a i - 1 := by simp
  have hrest : ∀ j ∈ Finset.univ.erase i,
      ((z j : Real) : Complex) ^ (a j)
        = ((z j : Real) : Complex) ^ ((a - (Pi.single i 1 : Multiindex d)) j) := by
    intro j hj
    have hji : j ≠ i := (Finset.mem_erase.1 hj).1
    have hval : (a - (Pi.single i 1 : Multiindex d)) j = a j := by simp [hji]
    rw [hval]
  rw [hii, Finset.prod_congr rfl hrest]

/-- Degree is additive under adding one to a slot. -/
theorem deg_add_single (b : Multiindex d) (i : Fin d) :
    deg (b + (Pi.single i 1 : Multiindex d)) = deg b + 1 := by
  have h : ∀ j : Fin d,
      (b + (Pi.single i 1 : Multiindex d)) j = b j + (Pi.single i 1 : Multiindex d) j :=
    fun _ => rfl
  rw [deg, Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) => h j,
    Finset.sum_add_distrib, deg]
  congr 1
  simp

/-- ... and subtractive when the slot is nonzero. -/
theorem deg_sub_single {a : Multiindex d} {i : Fin d} (hi : 1 ≤ a i) :
    deg (a - (Pi.single i 1 : Multiindex d)) + 1 = deg a := by
  have hback : a - (Pi.single i 1 : Multiindex d) + (Pi.single i 1 : Multiindex d) = a := by
    funext k
    by_cases hk : k = i
    · have hk1 : 1 ≤ a k := by rw [hk]; exact hi
      have hv : (a - (Pi.single i 1 : Multiindex d) + (Pi.single i 1 : Multiindex d)) k
          = a k - 1 + 1 := by simp [hk]
      rw [hv]
      omega
    · simp [hk]
  calc deg (a - (Pi.single i 1 : Multiindex d)) + 1
      = deg (a - (Pi.single i 1 : Multiindex d) + (Pi.single i 1 : Multiindex d)) :=
        (deg_add_single _ i).symm
    _ = deg a := by rw [hback]

/-- **`jderiv` is the coefficient family of the transverse partial
derivative.**  The normalization is consistent: no `alpha!` appears, and the
factor `alpha_i + 1` carried by `jderiv` is exactly the one produced by the
reindexing `alpha = beta + e_i`. -/
theorem hasDerivAt_realize_jderiv (N : Nat) (c : Jet d) (i : Fin d)
    (z : Fin d -> Real) :
    HasDerivAt (fun t : Real => realize (degreeLE d (N + 1)) c (z + t • dir i))
      (realize (degreeLE d N) (jderiv i c) z) 0 := by
  classical
  have hbase := hasDerivAt_realize_transverse (degreeLE d (N + 1)) c i z
  set F : Multiindex d -> Complex := fun a =>
    c a * (((a i : Nat) : Complex) * ((z i : Real) : Complex) ^ (a i - 1)
      * ∏ j ∈ Finset.univ.erase i, ((z j : Real) : Complex) ^ (a j)) with hF
  have hvanish : ∀ a ∈ degreeLE d (N + 1),
      a ∉ (degreeLE d (N + 1)).filter (fun a => ¬ a i = 0) -> F a = 0 := by
    intro a ha hnot
    have hai : a i = 0 := by
      by_contra hc
      exact hnot (Finset.mem_filter.2 ⟨ha, hc⟩)
    rw [hF]
    simp [hai]
  have hsum : (∑ a ∈ degreeLE d (N + 1), F a)
      = realize (degreeLE d N) (jderiv i c) z := by
    rw [← Finset.sum_subset (Finset.filter_subset
      (fun a => ¬ a i = 0) (degreeLE d (N + 1))) hvanish, realize]
    refine Finset.sum_nbij' (fun a => a - (Pi.single i 1 : Multiindex d))
      (fun b => b + (Pi.single i 1 : Multiindex d)) ?_ ?_ ?_ ?_ ?_
    · intro a ha
      have hmem := Finset.mem_filter.1 ha
      have hai : 1 ≤ a i := Nat.one_le_iff_ne_zero.2 hmem.2
      have hd := deg_sub_single hai
      have hle := mem_degreeLE.1 hmem.1
      show a - (Pi.single i 1 : Multiindex d) ∈ degreeLE d N
      rw [mem_degreeLE]
      omega
    · intro b hb
      refine Finset.mem_filter.2 ⟨?_, ?_⟩
      · show b + (Pi.single i 1 : Multiindex d) ∈ degreeLE d (N + 1)
        rw [mem_degreeLE, deg_add_single]
        have := mem_degreeLE.1 hb
        omega
      · show ¬ (b + (Pi.single i 1 : Multiindex d)) i = 0
        simp
    · intro a ha
      have hmem := Finset.mem_filter.1 ha
      have hai : 1 ≤ a i := Nat.one_le_iff_ne_zero.2 hmem.2
      show a - (Pi.single i 1 : Multiindex d) + (Pi.single i 1 : Multiindex d) = a
      funext k
      by_cases hk : k = i
      · have hk1 : 1 ≤ a k := by rw [hk]; exact hai
        have hv : (a - (Pi.single i 1 : Multiindex d)
            + (Pi.single i 1 : Multiindex d)) k = a k - 1 + 1 := by simp [hk]
        rw [hv]
        omega
      · simp [hk]
    · intro b _
      show b + (Pi.single i 1 : Multiindex d) - (Pi.single i 1 : Multiindex d) = b
      funext k
      by_cases hk : k = i
      · simp [hk]
      · simp [hk]
    · intro a ha
      have hmem := Finset.mem_filter.1 ha
      have hai : 1 ≤ a i := Nat.one_le_iff_ne_zero.2 hmem.2
      have hidx : a - (Pi.single i 1 : Multiindex d)
          + (Pi.single i 1 : Multiindex d) = a := by
        funext k
        by_cases hk : k = i
        · have hk1 : 1 ≤ a k := by rw [hk]; exact hai
          have hv : (a - (Pi.single i 1 : Multiindex d)
              + (Pi.single i 1 : Multiindex d)) k = a k - 1 + 1 := by simp [hk]
          rw [hv]
          omega
        · simp [hk]
      have hcoef : (a - (Pi.single i 1 : Multiindex d)) i + 1 = a i := by
        have hv : (a - (Pi.single i 1 : Multiindex d)) i = a i - 1 := by simp
        omega
      show F a = jderiv i c (a - (Pi.single i 1 : Multiindex d))
        * monomial (a - (Pi.single i 1 : Multiindex d)) z
      rw [hF, jderiv, hidx, hcoef, ← monomial_sub_single hai z]
      ring
  rw [hsum] at hbase
  exact hbase

/-- **Every jet coefficient is continuous in the longitudinal parameter.**  This
is not an assumption: it is forced by the derivative certificate carried by the
structure.  Continuity of derived objects (products, transverse derivatives,
the eikonal, the same-degree matrix) therefore never has to be supplied by a
caller. -/
theorem LongJet.continuous_c (J : LongJet d) (a : Multiindex d) :
    Continuous (J.c a) :=
  continuous_iff_continuousAt.2 fun s => (J.hasDeriv a s).continuousAt

/-- A finite sum of certified derivatives is a certified derivative. -/
theorem hasDerivAt_finsum {iota : Type*} [Fintype iota]
    (A : iota -> Real -> Complex) (A' : iota -> Complex) (s : Real)
    (h : ∀ i, HasDerivAt (A i) (A' i) s) :
    HasDerivAt (fun v => ∑ i, A i v) (∑ i, A' i) s := by
  have h0 := HasDerivAt.sum (A := A) (A' := A')
    (u := (Finset.univ : Finset iota)) (fun i _ => h i)
  have hfun : (∑ i : iota, A i) = fun v => ∑ i : iota, A i v := by
    funext v
    rw [Finset.sum_apply]
  rw [hfun] at h0
  exact h0

/-! ## Continuity of the derivative family

A differentiable function need not have a continuous derivative, so continuity
of `dc` is genuinely extra information and is tracked as a predicate rather than
pretended to be automatic.  Every jet this development builds satisfies it, and
the closure lemmas below carry it through the whole jet algebra. -/

/-- A jet is `C1` when its certified derivative family is continuous. -/
def LongJet.C1 (J : LongJet d) : Prop := ∀ a, Continuous (J.dc a)

theorem LongJet.C1.mul {u v : LongJet d} (hu : u.C1) (hv : v.C1) :
    (LongJet.mul u v).C1 := by
  intro a
  show Continuous fun s =>
    ∑ b ∈ below a, (u.dc b s * v.c (a - b) s + u.c b s * v.dc (a - b) s)
  refine continuous_finset_sum _ fun b _ => ?_
  exact ((hu b).mul (v.continuous_c (a - b))).add
    ((u.continuous_c b).mul (hv (a - b)))

theorem LongJet.C1.transverseDeriv {u : LongJet d} (hu : u.C1) (i : Fin d) :
    (LongJet.transverseDeriv i u).C1 := fun a =>
  continuous_const.mul (hu (a + Pi.single i 1))

theorem LongJet.C1.add {u v : LongJet d} (hu : u.C1) (hv : v.C1) :
    (LongJet.add u v).C1 := fun a => (hu a).add (hv a)

theorem LongJet.C1.sub {u v : LongJet d} (hu : u.C1) (hv : v.C1) :
    (LongJet.sub u v).C1 := fun a => (hu a).sub (hv a)

end LiuWang2025SemilinearWaveLongitudinalJet
