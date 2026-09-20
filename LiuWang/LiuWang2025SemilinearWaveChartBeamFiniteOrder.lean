import LiuWang.LiuWang2025SemilinearWaveChartBeamAssembly
import LiuWang.LiuWang2025SemilinearWaveChartBeamProfile
import LiuWang.LiuWang2025SemilinearWaveEquation312EnergyClosure

/-!
# Liu-Wang semilinear wave: the finite-order residual estimate

This is the estimate the source actually proves.  The three WKB expressions are
*not* zero away from the central ray; they are Taylor remainders of size
`O(|z'|^{N+1})`, which is what the finite-jet construction delivers and what
`LiuWang2025SemilinearWaveDirectionalJet.taylor_remainder_bound` proves from
vanishing jets plus a compact-tube derivative bound.

Feeding those remainders into the unconditional expansion
(`LiuWang2025SemilinearWaveChartBeamAssembly.waveOp_beam_expand`) splits the
residual into

* `beamRemainderPart`, carrying `rho^2` and transverse weight `|z'|^{N+1}`;
* `beamTerminalPart`, carrying `rho^{-N}` and no transverse weight.

Their transverse `L^2` rates are computed, and the first one is shown to be
exactly the source's equation-(3.11) rate
`rho^{-((N+1)/2 + n/4 - k - 2)}`: the two powers of the frequency that the
eikonal term carries are precisely the `- 2` of the source's exponent.
-/

noncomputable section

open scoped BigOperators

namespace LiuWang2025SemilinearWaveChartBeamFiniteOrder

open LiuWang2025SemilinearWaveChartWKB
open LiuWang2025SemilinearWaveChartWKB.ChartJet
open LiuWang2025SemilinearWaveChartBeamResidual
open LiuWang2025SemilinearWaveChartBeamAssembly
open LiuWang2025SemilinearWaveChartBeamProfile
open LiuWang2025SemilinearWaveGaussianL2Bridge
open LiuWang2025SemilinearWaveGaussianMassScaling (radiusSq)
open LiuWang2025SemilinearWaveEquation312EnergyClosure

variable {n : Nat}
variable (A : Fin n -> Fin n -> (Fin n -> Real) -> Complex)
  (B : Fin n -> (Fin n -> Real) -> Complex)

/-- The part of the residual built from the three Taylor remainders. -/
def beamRemainderPart (rho : Real) (phi : ChartJet n) (b : Nat -> ChartJet n)
    (N : Nat) (x : Fin n -> Real) : Complex :=
  Complex.exp (Complex.I * (rho : Complex) * phi.val x)
    * (Complex.I * (rho : Complex) * transportTerm A B phi (b 0) x
        + (∑ m ∈ Finset.range N,
            ((rho : Complex))⁻¹ ^ m * hierarchyExpr A B phi b m x)
        - (rho : Complex) ^ 2 * (truncatedAmplitude rho b N).val x
            * eikonalSymbol A phi x)

/-- The terminal part of the residual. -/
def beamTerminalPart (rho : Real) (phi : ChartJet n) (b : Nat -> ChartJet n)
    (N : Nat) (x : Fin n -> Real) : Complex :=
  Complex.exp (Complex.I * (rho : Complex) * phi.val x)
    * (((rho : Complex))⁻¹ ^ N * waveOp A B (b N) x)

/-- **The residual splits.**  A restatement of the unconditional expansion. -/
theorem waveOp_beam_split (rho : Real) (hrho : (rho : Complex) ≠ 0)
    (phi : ChartJet n) (b : Nat -> ChartJet n) (N : Nat) (x : Fin n -> Real) :
    waveOp A B (beam (Complex.I * (rho : Complex)) phi (truncatedAmplitude rho b N)) x
      = beamRemainderPart A B rho phi b N x + beamTerminalPart A B rho phi b N x := by
  rw [waveOp_beam_expand A B rho hrho phi b N x, beamRemainderPart, beamTerminalPart]
  ring

/-! ## The pointwise profile of each part -/

/-- **The remainder part obeys the source's profile.**  Two powers of the
frequency, transverse weight `N + 1`, Gaussian width `coer * rho`. -/
theorem beamRemainderPart_radiusProfileBound (rho : Real) (hrho : 1 ≤ rho)
    (phi : ChartJet n) (b : Nat -> ChartJet n) (N : Nat)
    {coer CT CH Ca Ce : Real} (hCH : 0 ≤ CH) (hCa : 0 ≤ Ca)
    (hIm : ∀ x, coer * radiusSq x ≤ (phi.val x).im)
    (hT : ∀ x, ‖transportTerm A B phi (b 0) x‖ ≤ CT * (radius x) ^ (N + 1))
    (hH : ∀ m ∈ Finset.range N, ∀ x,
      ‖hierarchyExpr A B phi b m x‖ ≤ CH * (radius x) ^ (N + 1))
    (ha : ∀ x, ‖(truncatedAmplitude rho b N).val x‖ ≤ Ca)
    (he : ∀ x, ‖eikonalSymbol A phi x‖ ≤ Ce * (radius x) ^ (N + 1)) :
    RadiusProfileBound (beamRemainderPart A B rho phi b N)
      (rho ^ 2 * (CT + (N : Real) * CH + Ca * Ce)) (N + 1) (coer * rho) := by
  have hrho0 : (0 : Real) < rho := lt_of_lt_of_le zero_lt_one hrho
  intro x
  have hRnn : (0 : Real) ≤ radius x ^ (N + 1) := pow_nonneg (radius_nonneg x) _
  have hsq : rho ≤ rho ^ 2 := by nlinarith
  have hone : (1 : Real) ≤ rho ^ 2 := by nlinarith
  have hgauss : Real.exp (-(rho * (phi.val x).im))
      ≤ Real.exp (-(coer * rho) * radiusSq x) := by
    refine Real.exp_le_exp.2 ?_
    have h := mul_le_mul_of_nonneg_left (hIm x) hrho0.le
    linarith
  have hinvle : ∀ m : Nat, ‖((rho : Complex))⁻¹ ^ m‖ ≤ 1 := by
    intro m
    rw [norm_pow, norm_inv, Complex.norm_real, Real.norm_of_nonneg hrho0.le]
    exact pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hrho)
  have hCTnn : (0 : Real) ≤ CT * radius x ^ (N + 1) :=
    le_trans (norm_nonneg _) (hT x)
  -- leading transport term
  have hA : ‖Complex.I * (rho : Complex) * transportTerm A B phi (b 0) x‖
      ≤ rho ^ 2 * CT * radius x ^ (N + 1) := by
    have hlead : ‖Complex.I * (rho : Complex) * transportTerm A B phi (b 0) x‖
        ≤ rho * (CT * radius x ^ (N + 1)) := by
      rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
        Real.norm_of_nonneg hrho0.le]
      exact mul_le_mul_of_nonneg_left (hT x) hrho0.le
    have hstep : rho * (CT * radius x ^ (N + 1))
        ≤ rho ^ 2 * (CT * radius x ^ (N + 1)) :=
      mul_le_mul_of_nonneg_right hsq hCTnn
    calc ‖Complex.I * (rho : Complex) * transportTerm A B phi (b 0) x‖
        ≤ rho * (CT * radius x ^ (N + 1)) := hlead
      _ ≤ rho ^ 2 * (CT * radius x ^ (N + 1)) := hstep
      _ = rho ^ 2 * CT * radius x ^ (N + 1) := by ring
  -- hierarchy remainders
  have hB : ‖∑ m ∈ Finset.range N,
        ((rho : Complex))⁻¹ ^ m * hierarchyExpr A B phi b m x‖
      ≤ rho ^ 2 * ((N : Real) * CH) * radius x ^ (N + 1) := by
    have hsum : ‖∑ m ∈ Finset.range N,
        ((rho : Complex))⁻¹ ^ m * hierarchyExpr A B phi b m x‖
        ≤ (N : Real) * (CH * radius x ^ (N + 1)) := by
      refine le_trans (norm_sum_le _ _) ?_
      have hterm : ∀ m ∈ Finset.range N,
          ‖((rho : Complex))⁻¹ ^ m * hierarchyExpr A B phi b m x‖
            ≤ CH * radius x ^ (N + 1) := by
        intro m hm
        rw [norm_mul]
        calc ‖((rho : Complex))⁻¹ ^ m‖ * ‖hierarchyExpr A B phi b m x‖
            ≤ 1 * (CH * radius x ^ (N + 1)) :=
              mul_le_mul (hinvle m) (hH m hm x) (norm_nonneg _) zero_le_one
          _ = CH * radius x ^ (N + 1) := one_mul _
      calc (∑ m ∈ Finset.range N,
              ‖((rho : Complex))⁻¹ ^ m * hierarchyExpr A B phi b m x‖)
          ≤ ∑ _m ∈ Finset.range N, CH * radius x ^ (N + 1) :=
            Finset.sum_le_sum hterm
        _ = (N : Real) * (CH * radius x ^ (N + 1)) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hbase : (0 : Real) ≤ (N : Real) * (CH * radius x ^ (N + 1)) := by positivity
    have hstep : (N : Real) * (CH * radius x ^ (N + 1))
        ≤ rho ^ 2 * ((N : Real) * (CH * radius x ^ (N + 1))) := by
      nlinarith [hbase, hone]
    calc ‖∑ m ∈ Finset.range N,
            ((rho : Complex))⁻¹ ^ m * hierarchyExpr A B phi b m x‖
        ≤ (N : Real) * (CH * radius x ^ (N + 1)) := hsum
      _ ≤ rho ^ 2 * ((N : Real) * (CH * radius x ^ (N + 1))) := hstep
      _ = rho ^ 2 * ((N : Real) * CH) * radius x ^ (N + 1) := by ring
  -- eikonal remainder
  have hC' : ‖(rho : Complex) ^ 2 * (truncatedAmplitude rho b N).val x
        * eikonalSymbol A phi x‖
      ≤ rho ^ 2 * (Ca * Ce) * radius x ^ (N + 1) := by
    rw [norm_mul, norm_mul, norm_pow, Complex.norm_real,
      Real.norm_of_nonneg hrho0.le]
    have h1 : rho ^ 2 * ‖(truncatedAmplitude rho b N).val x‖ ≤ rho ^ 2 * Ca :=
      mul_le_mul_of_nonneg_left (ha x) (by positivity)
    calc rho ^ 2 * ‖(truncatedAmplitude rho b N).val x‖ * ‖eikonalSymbol A phi x‖
        ≤ (rho ^ 2 * Ca) * (Ce * radius x ^ (N + 1)) :=
          mul_le_mul h1 (he x) (norm_nonneg _) (by positivity)
      _ = rho ^ 2 * (Ca * Ce) * radius x ^ (N + 1) := by ring
  -- assemble the inner factor
  have hinner : ‖Complex.I * (rho : Complex) * transportTerm A B phi (b 0) x
        + (∑ m ∈ Finset.range N,
            ((rho : Complex))⁻¹ ^ m * hierarchyExpr A B phi b m x)
        - (rho : Complex) ^ 2 * (truncatedAmplitude rho b N).val x
            * eikonalSymbol A phi x‖
      ≤ rho ^ 2 * (CT + (N : Real) * CH + Ca * Ce) * radius x ^ (N + 1) := by
    have hsplit := norm_sub_le
      (Complex.I * (rho : Complex) * transportTerm A B phi (b 0) x
        + ∑ m ∈ Finset.range N,
            ((rho : Complex))⁻¹ ^ m * hierarchyExpr A B phi b m x)
      ((rho : Complex) ^ 2 * (truncatedAmplitude rho b N).val x
        * eikonalSymbol A phi x)
    have hsplit2 := norm_add_le
      (Complex.I * (rho : Complex) * transportTerm A B phi (b 0) x)
      (∑ m ∈ Finset.range N,
        ((rho : Complex))⁻¹ ^ m * hierarchyExpr A B phi b m x)
    have hfin : rho ^ 2 * CT * radius x ^ (N + 1)
        + rho ^ 2 * ((N : Real) * CH) * radius x ^ (N + 1)
        + rho ^ 2 * (Ca * Ce) * radius x ^ (N + 1)
        = rho ^ 2 * (CT + (N : Real) * CH + Ca * Ce) * radius x ^ (N + 1) := by
      ring
    linarith [hA, hB, hC', hsplit, hsplit2, hfin]
  rw [beamRemainderPart, norm_mul, norm_beamExponential rho phi x]
  calc Real.exp (-(rho * (phi.val x).im))
        * ‖Complex.I * (rho : Complex) * transportTerm A B phi (b 0) x
            + (∑ m ∈ Finset.range N,
                ((rho : Complex))⁻¹ ^ m * hierarchyExpr A B phi b m x)
            - (rho : Complex) ^ 2 * (truncatedAmplitude rho b N).val x
                * eikonalSymbol A phi x‖
      ≤ Real.exp (-(coer * rho) * radiusSq x)
          * (rho ^ 2 * (CT + (N : Real) * CH + Ca * Ce) * radius x ^ (N + 1)) :=
        mul_le_mul hgauss hinner (norm_nonneg _) (Real.exp_pos _).le
    _ = rho ^ 2 * (CT + (N : Real) * CH + Ca * Ce) * radius x ^ (N + 1)
          * Real.exp (-(coer * rho) * radiusSq x) := by ring

/-- **The terminal part obeys a weight-zero profile.** -/
theorem beamTerminalPart_radiusProfileBound (rho : Real) (hrho : 0 < rho)
    (phi : ChartJet n) (b : Nat -> ChartJet n) (N : Nat)
    {coer CW : Real}
    (hIm : ∀ x, coer * radiusSq x ≤ (phi.val x).im)
    (hW : ∀ x, ‖waveOp A B (b N) x‖ ≤ CW) :
    RadiusProfileBound (beamTerminalPart A B rho phi b N)
      ((rho⁻¹) ^ N * CW) 0 (coer * rho) := by
  intro x
  have hgauss : Real.exp (-(rho * (phi.val x).im))
      ≤ Real.exp (-(coer * rho) * radiusSq x) := by
    refine Real.exp_le_exp.2 ?_
    have h := mul_le_mul_of_nonneg_left (hIm x) hrho.le
    linarith
  have hinvnn : (0 : Real) ≤ (rho⁻¹) ^ N := pow_nonneg (inv_nonneg.2 hrho.le) N
  rw [beamTerminalPart, norm_mul, norm_beamExponential rho phi x, norm_mul]
  have hinv : ‖((rho : Complex))⁻¹ ^ N‖ = (rho⁻¹) ^ N := by
    rw [norm_pow, norm_inv, Complex.norm_real, Real.norm_of_nonneg hrho.le]
  rw [hinv]
  calc Real.exp (-(rho * (phi.val x).im))
        * ((rho⁻¹) ^ N * ‖waveOp A B (b N) x‖)
      ≤ Real.exp (-(coer * rho) * radiusSq x) * ((rho⁻¹) ^ N * CW) :=
        mul_le_mul hgauss (mul_le_mul_of_nonneg_left (hW x) hinvnn)
          (mul_nonneg hinvnn (norm_nonneg _)) (Real.exp_pos _).le
    _ = (rho⁻¹) ^ N * CW * (radius x) ^ 0
          * Real.exp (-(coer * rho) * radiusSq x) := by
        rw [pow_zero]
        ring

/-! ## The equation-(3.11) exponent -/

/-- **The source's equation-(3.11) exponent, derived.**  The `rho^{2+k}` that
the eikonal term carries combines with the Gaussian gain
`rho^{-((N+1)/2 + n/4)}` to give exactly `rho^{-K}` with
`K = (N+1)/2 + n/4 - k - 2`.  The `- 2` of the source's exponent is the two
powers of the frequency in front of the eikonal symbol. -/
theorem equation311_exponent_identity (n N k : Nat) {rho : Real} (hrho : 0 < rho) :
    rho ^ (2 + k : Nat)
        * rho ^ (-(((N + 1 : Nat) : Real) / 2 + (n : Real) / 4))
      = rho ^ (-(equation311DecayExponent n N k)) := by
  rw [← Real.rpow_natCast rho (2 + k), ← Real.rpow_add hrho]
  congr 1
  unfold equation311DecayExponent
  push_cast
  ring

/-- **The finite-order Gaussian-beam remainder estimate at Sobolev order
zero.**  The transverse `L^2` norm of the remainder part is exactly the
source's equation-(3.11) rate. -/
theorem beamRemainderPart_L2_equation311 (rho : Real) (hrho : 1 ≤ rho)
    (phi : ChartJet n) (b : Nat -> ChartJet n) (N : Nat)
    {coer CT CH Ca Ce : Real} (hcoer : 0 < coer)
    (hCT : 0 ≤ CT) (hCH : 0 ≤ CH) (hCa : 0 ≤ Ca) (hCe : 0 ≤ Ce)
    (hIm : ∀ x, coer * radiusSq x ≤ (phi.val x).im)
    (hT : ∀ x, ‖transportTerm A B phi (b 0) x‖ ≤ CT * (radius x) ^ (N + 1))
    (hH : ∀ m ∈ Finset.range N, ∀ x,
      ‖hierarchyExpr A B phi b m x‖ ≤ CH * (radius x) ^ (N + 1))
    (ha : ∀ x, ‖(truncatedAmplitude rho b N).val x‖ ≤ Ca)
    (he : ∀ x, ‖eikonalSymbol A phi x‖ ≤ Ce * (radius x) ^ (N + 1)) :
    Real.sqrt (∫ x : Fin n -> Real, ‖beamRemainderPart A B rho phi b N x‖ ^ 2)
      ≤ (CT + (N : Real) * CH + Ca * Ce)
          * Real.sqrt (gaussianMoment n (N + 1) (2 * coer))
          * rho ^ (-(equation311DecayExponent n N 0)) := by
  have hrho0 : (0 : Real) < rho := lt_of_lt_of_le zero_lt_one hrho
  have hK : (0 : Real) ≤ CT + (N : Real) * CH + Ca * Ce := by positivity
  have hC : (0 : Real) ≤ rho ^ 2 * (CT + (N : Real) * CH + Ca * Ce) := by positivity
  have h := sqrt_integral_normSq_le_of_radiusProfileBound hC hcoer hrho0
    (beamRemainderPart_radiusProfileBound A B rho hrho phi b N hCH hCa hIm hT hH ha he)
  have hid : rho ^ 2 * rho ^ (-(((N + 1 : Nat) : Real) / 2 + (n : Real) / 4))
      = rho ^ (-(equation311DecayExponent n N 0)) := by
    have := equation311_exponent_identity n N 0 hrho0
    simpa using this
  refine h.trans_eq ?_
  calc rho ^ 2 * (CT + (N : Real) * CH + Ca * Ce)
        * rho ^ (-(((N + 1 : Nat) : Real) / 2 + (n : Real) / 4))
        * Real.sqrt (gaussianMoment n (N + 1) (2 * coer))
      = (CT + (N : Real) * CH + Ca * Ce)
          * Real.sqrt (gaussianMoment n (N + 1) (2 * coer))
          * (rho ^ 2 * rho ^ (-(((N + 1 : Nat) : Real) / 2 + (n : Real) / 4))) := by
        ring
    _ = (CT + (N : Real) * CH + Ca * Ce)
          * Real.sqrt (gaussianMoment n (N + 1) (2 * coer))
          * rho ^ (-(equation311DecayExponent n N 0)) := by rw [hid]

end LiuWang2025SemilinearWaveChartBeamFiniteOrder
