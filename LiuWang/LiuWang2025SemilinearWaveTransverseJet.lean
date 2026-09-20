import LiuWang.LiuWang2025SemilinearWaveGaussianL2Bridge

/-!
# Liu-Wang semilinear wave: finite transverse multi-index jets

The source's Gaussian beam phase and amplitude are finite sums of homogeneous
polynomials in the transverse variables,

  `phi = sum_{j=0}^N phi_j`,   `a_rho = chi sum_{k=0}^N rho^{-k} sum_{j=0}^N v_{k,j}`,

with the jet conditions imposed on the coefficients of total degree at most
`N`.  This file gives the finite multi-index jet layer those sums live in:

* `Multiindex d`, `deg`, and `below` -- the multi-indices dominated by a given
  one, used for the convolution product;
* `Jet d` together with `jadd`, `jsmul`, `jmul`, `jderiv` and `truncate`, with
  the algebraic laws proved;
* `monomial` and `realize` -- the actual chart functions the coefficients name;
* `monomial_smul`, the exact homogeneity `z^alpha(c z) = c^{|alpha|} z^alpha`;
* `norm_monomial_le`, the pointwise bound `|z^alpha| <= |z|^{|alpha|}`;
* `norm_realize_le_of_degree_ge`, which is the point of the whole layer: a jet
  whose coefficients all sit in degree `>= N + 1` realizes a function of size
  `O(|z|^{N+1})` on the unit tube.  That is the source's "the Taylor expansion
  starts at order `N + 1`" step, proved rather than assumed.
-/

noncomputable section

open scoped BigOperators

namespace LiuWang2025SemilinearWaveTransverseJet

open LiuWang2025SemilinearWaveGaussianL2Bridge
open LiuWang2025SemilinearWaveGaussianMassScaling (radiusSq)

variable {d : Nat}

/-! ## Multi-indices -/

/-- A transverse multi-index. -/
abbrev Multiindex (d : Nat) := Fin d -> Nat

/-- Total degree `|alpha|`. -/
def deg (a : Multiindex d) : Nat := ∑ i, a i

@[simp] theorem deg_zero : deg (0 : Multiindex d) = 0 := by
  simp [deg]

/-- The multi-indices dominated by `a`, the index set of the convolution
product. -/
def below (a : Multiindex d) : Finset (Multiindex d) :=
  Fintype.piFinset fun i => Finset.range (a i + 1)

theorem mem_below {a b : Multiindex d} : b ∈ below a ↔ ∀ i, b i ≤ a i := by
  simp [below, Fintype.mem_piFinset]

@[simp] theorem self_mem_below (a : Multiindex d) : a ∈ below a :=
  mem_below.2 fun _ => le_rfl

/-! ## Jets -/

/-- A finite transverse jet: a coefficient for each multi-index. -/
abbrev Jet (d : Nat) := Multiindex d -> Complex

/-- Truncation to total degree at most `N`. -/
def truncate (N : Nat) (c : Jet d) : Jet d :=
  fun a => if deg a ≤ N then c a else 0

/-- Sum of jets. -/
def jadd (c c' : Jet d) : Jet d := fun a => c a + c' a

/-- Scalar multiple of a jet. -/
def jsmul (k : Complex) (c : Jet d) : Jet d := fun a => k * c a

/-- Convolution product of jets: the coefficients of the product polynomial. -/
def jmul (c c' : Jet d) : Jet d :=
  fun a => ∑ b ∈ below a, c b * c' (a - b)

/-- Formal partial derivative of a jet in the `i`-th transverse variable. -/
def jderiv (i : Fin d) (c : Jet d) : Jet d :=
  fun a => ((a i + 1 : Nat) : Complex) * c (a + Pi.single i 1)

@[simp] theorem truncate_truncate (N : Nat) (c : Jet d) :
    truncate N (truncate N c) = truncate N c := by
  funext a
  by_cases h : deg a ≤ N <;> simp [truncate, h]

theorem truncate_jadd (N : Nat) (c c' : Jet d) :
    truncate N (jadd c c') = jadd (truncate N c) (truncate N c') := by
  funext a
  by_cases h : deg a ≤ N <;> simp [truncate, jadd, h]

theorem truncate_jsmul (N : Nat) (k : Complex) (c : Jet d) :
    truncate N (jsmul k c) = jsmul k (truncate N c) := by
  funext a
  by_cases h : deg a ≤ N <;> simp [truncate, jsmul, h]

theorem jadd_comm (c c' : Jet d) : jadd c c' = jadd c' c := by
  funext a; simp [jadd]; ring

theorem jadd_assoc (c c' c'' : Jet d) :
    jadd (jadd c c') c'' = jadd c (jadd c' c'') := by
  funext a; simp [jadd]; ring

theorem jsmul_jadd (k : Complex) (c c' : Jet d) :
    jsmul k (jadd c c') = jadd (jsmul k c) (jsmul k c') := by
  funext a; simp [jsmul, jadd]; ring

theorem jsmul_jsmul (k k' : Complex) (c : Jet d) :
    jsmul k (jsmul k' c) = jsmul (k * k') c := by
  funext a; simp [jsmul]; ring

/-- **The convolution product is commutative.**  The index reflection
`b |-> a - b` is an involution of `below a`. -/
theorem jmul_comm (c c' : Jet d) : jmul c c' = jmul c' c := by
  funext a
  rw [jmul, jmul]
  refine Finset.sum_nbij' (fun b => a - b) (fun b => a - b) ?_ ?_ ?_ ?_ ?_
  · intro b hb
    exact mem_below.2 fun i => Nat.sub_le _ _
  · intro b hb
    exact mem_below.2 fun i => Nat.sub_le _ _
  · intro b hb
    funext i
    exact Nat.sub_sub_self (mem_below.1 hb i)
  · intro b hb
    funext i
    exact Nat.sub_sub_self (mem_below.1 hb i)
  · intro b hb
    have hsub : a - (a - b) = b := by
      funext i
      exact Nat.sub_sub_self (mem_below.1 hb i)
    rw [hsub]
    ring

/-! ## Realization as chart functions -/

/-- The monomial `z^alpha`, as an actual function on the chart. -/
def monomial (a : Multiindex d) (z : Fin d -> Real) : Complex :=
  ∏ i, ((z i : Complex)) ^ (a i)

@[simp] theorem monomial_zero (z : Fin d -> Real) :
    monomial (0 : Multiindex d) z = 1 := by
  simp [monomial]

/-- **Exact homogeneity of a monomial.** -/
theorem monomial_smul (k : Real) (a : Multiindex d) (z : Fin d -> Real) :
    monomial a (k • z) = (k : Complex) ^ (deg a) * monomial a z := by
  rw [monomial, monomial, deg, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul, mul_pow]

/-- Each coordinate is bounded by the transverse radius. -/
theorem abs_le_radius (z : Fin d -> Real) (i : Fin d) : |z i| ≤ radius z := by
  have hle : (z i) ^ 2 ≤ radiusSq z :=
    Finset.single_le_sum (f := fun j => (z j) ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  have := Real.sqrt_le_sqrt hle
  rwa [Real.sqrt_sq_eq_abs] at this

/-- **The pointwise bound for a monomial.** -/
theorem norm_monomial_le (a : Multiindex d) (z : Fin d -> Real) :
    ‖monomial a z‖ ≤ (radius z) ^ (deg a) := by
  rw [monomial, norm_prod, deg, ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_le_prod (fun i _ => norm_nonneg _) fun i _ => ?_
  rw [norm_pow, Complex.norm_real]
  exact pow_le_pow_left₀ (abs_nonneg _) (abs_le_radius z i) _

/-- Realization of a jet over a given finite family of multi-indices. -/
def realize (S : Finset (Multiindex d)) (c : Jet d) (z : Fin d -> Real) : Complex :=
  ∑ a ∈ S, c a * monomial a z

/-- **The Taylor tail bound.**  If every multi-index carrying a coefficient has
total degree at least `N + 1`, the realized polynomial is `O(|z|^{N+1})` on the
unit tube.  This is the source's "the expansion starts at order `N+1`" step. -/
theorem norm_realize_le_of_degree_ge {S : Finset (Multiindex d)} {c : Jet d}
    {K : Real} {N : Nat}
    (hdeg : ∀ a ∈ S, N + 1 ≤ deg a)
    (hc : ∑ a ∈ S, ‖c a‖ ≤ K)
    (z : Fin d -> Real) (hz : radius z ≤ 1) :
    ‖realize S c z‖ ≤ K * (radius z) ^ (N + 1) := by
  have hr : (0 : Real) ≤ radius z := radius_nonneg z
  have hterm : ∀ a ∈ S, ‖c a * monomial a z‖ ≤ ‖c a‖ * (radius z) ^ (N + 1) := by
    intro a ha
    rw [norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    refine le_trans (norm_monomial_le a z) ?_
    exact pow_le_pow_of_le_one hr hz (hdeg a ha)
  calc ‖realize S c z‖
      ≤ ∑ a ∈ S, ‖c a * monomial a z‖ := norm_sum_le _ _
    _ ≤ ∑ a ∈ S, ‖c a‖ * (radius z) ^ (N + 1) := Finset.sum_le_sum hterm
    _ = (∑ a ∈ S, ‖c a‖) * (radius z) ^ (N + 1) := by rw [Finset.sum_mul]
    _ ≤ K * (radius z) ^ (N + 1) :=
        mul_le_mul_of_nonneg_right hc (pow_nonneg hr _)

/-- The degree-`N` truncation kills exactly the multi-indices the source's jet
conditions constrain, so a jet all of whose constrained coefficients vanish
realizes only its tail. -/
theorem realize_truncate_eq_zero {S : Finset (Multiindex d)} {c : Jet d} {N : Nat}
    (hS : ∀ a ∈ S, deg a ≤ N) (hc : ∀ a, deg a ≤ N -> c a = 0)
    (z : Fin d -> Real) : realize S c z = 0 := by
  refine Finset.sum_eq_zero fun a ha => ?_
  rw [hc a (hS a ha), zero_mul]

end LiuWang2025SemilinearWaveTransverseJet
