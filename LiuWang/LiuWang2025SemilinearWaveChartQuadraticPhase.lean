import LiuWang.LiuWang2025SemilinearWaveChartBeamProfile

/-!
# Liu-Wang semilinear wave: the constructed quadratic phase jet

The source's Gaussian beam phase is, to second order in the transverse
variables, the quadratic form built from the solution `H(s)` of the matrix
Riccati equation (3.8), and its imaginary part is positive definite -- that is
what makes the beam Gaussian.

This file constructs that phase as an honest `ChartJet`: the value, the first
directional derivatives and the second directional derivatives are written
down, and every `HasDerivAt` witness is obtained by differentiating the
displayed quadratic form, not assumed.  Two facts are then derived:

* `quadraticPhaseJet_d2` : the second directional derivative data really is the
  symmetrization `H_{ml} + H_{lm}`, so the constructed jet carries the Riccati
  unknown in its transverse 2-jet;
* `quadraticPhaseJet_im_coercive` : positive definiteness of the imaginary
  quadratic form -- the source's Gaussian condition -- gives exactly the
  transverse coercivity hypothesis that the remainder estimate consumes.

Consequently the coercivity input of
`LiuWang2025SemilinearWaveChartBeamProfile.residual_L2_rate` is supplied by a
constructed object rather than assumed of an abstract one;
`constructedPhase_L2_rate` records that specialization.
-/

noncomputable section

open scoped BigOperators

namespace LiuWang2025SemilinearWaveChartQuadraticPhase

open LiuWang2025SemilinearWaveChartWKB
open LiuWang2025SemilinearWaveChartWKB.ChartJet
open LiuWang2025SemilinearWaveChartBeamResidual
open LiuWang2025SemilinearWaveChartBeamProfile
open LiuWang2025SemilinearWaveGaussianL2Bridge
open LiuWang2025SemilinearWaveGaussianMassScaling (radiusSq)

variable {n : Nat}

/-- The value of the source's quadratic phase. -/
def quadVal (H : Fin n -> Fin n -> Complex) (c : Complex) (x : Fin n -> Real) :
    Complex :=
  c + ∑ j, ∑ k, H j k * (x j : Complex) * (x k : Complex)

/-- Its first directional derivative data. -/
def quadD (H : Fin n -> Fin n -> Complex) (m : Fin n) (x : Fin n -> Real) :
    Complex :=
  ∑ j, ∑ k, H j k
    * (((dir m j : Real) : Complex) * (x k : Complex)
        + (x j : Complex) * ((dir m k : Real) : Complex))

/-- Its second directional derivative data. -/
def quadD2 (H : Fin n -> Fin n -> Complex) (l m : Fin n) (_x : Fin n -> Real) :
    Complex :=
  ∑ j, ∑ k, H j k
    * (((dir m j : Real) : Complex) * ((dir l k : Real) : Complex)
        + ((dir l j : Real) : Complex) * ((dir m k : Real) : Complex))

/-- The complexified real coordinate line. -/
theorem hasDerivAt_lineC (a d : Real) :
    HasDerivAt (fun t : Real => (a : Complex) + (t : Complex) * (d : Complex))
      (d : Complex) 0 := by
  have hreal : HasDerivAt (fun t : Real => a + t * d) d 0 := by
    simpa using ((hasDerivAt_id (0 : Real)).mul_const d).const_add a
  have hC := hreal.ofReal_comp
  refine hC.congr_of_eventuallyEq ?_
  filter_upwards with t
  push_cast
  ring

/-- **The source's quadratic phase, as a constructed jet.** -/
def quadraticPhaseJet (H : Fin n -> Fin n -> Complex) (c : Complex) : ChartJet n where
  val := quadVal H c
  d := quadD H
  d2 := quadD2 H
  hasDeriv := by
    intro m x
    have hrw : (fun t : Real => quadVal H c (x + t • dir m))
        = fun t : Real => c + ∑ j, ∑ k, H j k
            * ((x j : Complex) + (t : Complex) * ((dir m j : Real) : Complex))
            * ((x k : Complex) + (t : Complex) * ((dir m k : Real) : Complex)) := by
      funext t
      simp only [quadVal, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        Complex.ofReal_add, Complex.ofReal_mul]
    rw [hrw, quadD]
    refine HasDerivAt.const_add c ?_
    refine HasDerivAt.fun_sum fun j _ => HasDerivAt.fun_sum fun k _ => ?_
    have hmul := ((hasDerivAt_lineC (x j) (dir m j)).mul
      (hasDerivAt_lineC (x k) (dir m k))).const_mul (H j k)
    convert hmul using 1
    · funext t
      simp only [Pi.mul_apply]
      ring
    · push_cast
      ring
  hasDeriv2 := by
    intro l m x
    have hrw : (fun t : Real => quadD H m (x + t • dir l))
        = fun t : Real => ∑ j, ∑ k, H j k
            * (((dir m j : Real) : Complex)
                * ((x k : Complex) + (t : Complex) * ((dir l k : Real) : Complex))
              + ((x j : Complex) + (t : Complex) * ((dir l j : Real) : Complex))
                * ((dir m k : Real) : Complex)) := by
      funext t
      simp only [quadD, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        Complex.ofReal_add, Complex.ofReal_mul]
    rw [hrw, quadD2]
    refine HasDerivAt.fun_sum fun j _ => HasDerivAt.fun_sum fun k _ => ?_
    have hsum := (((hasDerivAt_lineC (x k) (dir l k)).const_mul
        ((dir m j : Real) : Complex)).add
      ((hasDerivAt_lineC (x j) (dir l j)).mul_const
        ((dir m k : Real) : Complex))).const_mul (H j k)
    convert hsum using 1

@[simp] theorem quadraticPhaseJet_val (H : Fin n -> Fin n -> Complex) (c : Complex)
    (x : Fin n -> Real) : (quadraticPhaseJet H c).val x = quadVal H c x := rfl

/-- Collapsing one coordinate direction against a `Pi.single`. -/
theorem sum_dir_collapse (i0 : Fin n) (f : Fin n -> Complex) :
    (∑ k, f k * ((dir i0 k : Real) : Complex)) = f i0 := by
  rw [Finset.sum_eq_single_of_mem i0 (Finset.mem_univ i0)]
  · simp [dir]
  · intro k _ hk
    simp only [dir, Pi.single_apply, if_neg hk, Complex.ofReal_zero, mul_zero]

/-- **The jet's second derivative data is the symmetrized Riccati matrix.** -/
theorem quadraticPhaseJet_d2 (H : Fin n -> Fin n -> Complex) (c : Complex)
    (l m : Fin n) (x : Fin n -> Real) :
    (quadraticPhaseJet H c).d2 l m x = H m l + H l m := by
  show quadD2 H l m x = _
  rw [quadD2]
  have hinner : ∀ j : Fin n, (∑ k, H j k
      * (((dir m j : Real) : Complex) * ((dir l k : Real) : Complex)
          + ((dir l j : Real) : Complex) * ((dir m k : Real) : Complex)))
      = H j l * ((dir m j : Real) : Complex)
        + H j m * ((dir l j : Real) : Complex) := by
    intro j
    have hsplit : ∀ k : Fin n, H j k
        * (((dir m j : Real) : Complex) * ((dir l k : Real) : Complex)
            + ((dir l j : Real) : Complex) * ((dir m k : Real) : Complex))
        = (H j k * ((dir m j : Real) : Complex)) * ((dir l k : Real) : Complex)
          + (H j k * ((dir l j : Real) : Complex)) * ((dir m k : Real) : Complex) := by
      intro k; ring
    rw [Finset.sum_congr rfl fun k _ => hsplit k, Finset.sum_add_distrib,
      sum_dir_collapse l (fun k => H j k * ((dir m j : Real) : Complex)),
      sum_dir_collapse m (fun k => H j k * ((dir l j : Real) : Complex))]
  rw [Finset.sum_congr rfl fun j _ => hinner j, Finset.sum_add_distrib,
    sum_dir_collapse m (fun j => H j l), sum_dir_collapse l (fun j => H j m)]

/-- The imaginary part of the constructed phase is the imaginary quadratic
form plus the constant's. -/
theorem quadVal_im (H : Fin n -> Fin n -> Complex) (c : Complex) (x : Fin n -> Real) :
    (quadVal H c x).im = c.im + ∑ j, ∑ k, (H j k).im * x j * x k := by
  rw [quadVal, Complex.add_im]
  congr 1
  rw [Complex.im_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.im_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [Complex.mul_im]

/-- **The constructed phase is transversely coercive.**  Positive definiteness
of the imaginary quadratic form -- the source's Gaussian condition on the
Riccati solution -- gives exactly the hypothesis the remainder estimate
needs. -/
theorem quadraticPhaseJet_im_coercive (H : Fin n -> Fin n -> Complex) (c : Complex)
    {bcoer : Real} (hc : 0 ≤ c.im)
    (hpos : ∀ x : Fin n -> Real,
      bcoer * radiusSq x ≤ ∑ j, ∑ k, (H j k).im * x j * x k)
    (x : Fin n -> Real) :
    bcoer * radiusSq x ≤ ((quadraticPhaseJet H c).val x).im := by
  rw [quadraticPhaseJet_val, quadVal_im]
  have h := hpos x
  linarith

/-- **The remainder estimate with a constructed phase.**  Specializing
`residual_L2_rate` to `quadraticPhaseJet` removes the abstract coercivity
hypothesis in favour of positive definiteness of the imaginary quadratic form,
so the Gaussian gain is produced by the construction itself. -/
theorem constructedPhase_L2_rate
    (A : Fin n -> Fin n -> (Fin n -> Real) -> Complex)
    (B : Fin n -> (Fin n -> Real) -> Complex)
    (H : Fin n -> Fin n -> Complex) (c : Complex) (rho : Real) (hrho : 0 < rho)
    (b : Nat -> ChartJet n) (N : Nat)
    {coer amp : Real} {p : Nat} (hamp : 0 ≤ amp) (hcoer : 0 < coer)
    (hc : 0 ≤ c.im)
    (hpos : ∀ x : Fin n -> Real,
      coer * radiusSq x ≤ ∑ j, ∑ k, (H j k).im * x j * x k)
    (heik : ∀ x, eikonalSymbol A (quadraticPhaseJet H c) x = 0)
    (htrans0 : ∀ x, transportTerm A B (quadraticPhaseJet H c) (b 0) x = 0)
    (hhier : ∀ m ∈ Finset.range N, ∀ x,
      Complex.I * transportTerm A B (quadraticPhaseJet H c) (b (m + 1)) x
        + waveOp A B (b m) x = 0)
    (hterm : ∀ x, ‖waveOp A B (b N) x‖ ≤ amp * (radius x) ^ p) :
    Real.sqrt (∫ x : Fin n -> Real,
        ‖waveOp A B (beam (Complex.I * (rho : Complex)) (quadraticPhaseJet H c)
          (truncatedAmplitude rho b N)) x‖ ^ 2)
      ≤ (amp * (rho⁻¹) ^ N)
          * rho ^ (-((p : Real) / 2 + (n : Real) / 4))
          * Real.sqrt (gaussianMoment n p (2 * coer)) :=
  residual_L2_rate A B rho hrho (quadraticPhaseJet H c) b N hamp hcoer heik htrans0
    hhier (quadraticPhaseJet_im_coercive H c hc hpos) hterm

end LiuWang2025SemilinearWaveChartQuadraticPhase
