/-
# Genuine `L²` certificates for the 1+3 null-Fermi Gaussian beam  (v0.3)

Every `L²` statement in this module is preceded by the measure-theoretic hypotheses that
make it non-vacuous:

* `AEStronglyMeasurable` (§11, from continuity),
* `Integrable` of the squared norm (§13, by domination against an explicit Gaussian),
* `MemLp _ 2 volume` (§14),

and only then is an estimate stated, in terms of the genuine seminorm
`MeasureTheory.eLpNorm _ 2 volume` — never as a bare Bochner integral, which would evaluate
to `0` for a non-integrable integrand and so certify nothing.

The measure is the product Lebesgue measure on the genuinely three-dimensional transverse
space `Fin 3 → ℝ`.

§15 contains the negative counterpart: the undamped (`λ = 0`) beam, which solves the
equation exactly, has modulus independent of the longitudinal coordinate `z₀` and is
therefore **not** integrable along it — the reason a non-zero residual is unavoidable in
this first-order construction.
-/
import LiuWang.LiuWang2025SemilinearWaveFlatFermiBeam
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

namespace LiuWang2025SemilinearWaveFlatBeam
namespace Fermi

noncomputable section

open MeasureTheory

/-! ## §11  Elementary exponential inequalities -/

/-- `ξ e^{-ξ} ≤ 1`. -/
theorem xexp_le_one (ξ : ℝ) : ξ * Real.exp (-ξ) ≤ 1 := by
  have h1 : ξ ≤ Real.exp ξ := by linarith [Real.add_one_le_exp ξ]
  have hpos : 0 < Real.exp (-ξ) := Real.exp_pos _
  have hmul : ξ * Real.exp (-ξ) ≤ Real.exp ξ * Real.exp (-ξ) :=
    mul_le_mul_of_nonneg_right h1 hpos.le
  have hone : Real.exp ξ * Real.exp (-ξ) = 1 := by
    rw [← Real.exp_add]; simp
  linarith

/-- `ξ e^{-aξ} ≤ 1/a` for `ξ ≥ 0` and `a > 0`.  This is the single quantitative input from
which every `ρ`-power below is produced. -/
theorem xexp_le_inv {a ξ : ℝ} (ha : 0 < a) :
    ξ * Real.exp (-(a * ξ)) ≤ 1 / a := by
  have h := xexp_le_one (a * ξ)
  have hrw : ξ * Real.exp (-(a * ξ)) = (1 / a) * ((a * ξ) * Real.exp (-(a * ξ))) := by
    field_simp
  rw [hrw]
  calc (1 / a) * ((a * ξ) * Real.exp (-(a * ξ)))
      ≤ (1 / a) * 1 := mul_le_mul_of_nonneg_left h (by positivity)
    _ = 1 / a := mul_one _

/-! ## §12  Gaussian integrals on the three-dimensional transverse space -/

theorem exp_nsq_prod (b : ℝ) (z : Fin 3 → ℝ) :
    Real.exp (-b * nsq z) = ∏ i, Real.exp (-b * z i ^ 2) := by
  rw [← Real.exp_sum]
  congr 1
  simp [nsq, Finset.mul_sum]

/-- The three-dimensional Gaussian is integrable for the product Lebesgue measure. -/
theorem integrable_gauss3 {b : ℝ} (hb : 0 < b) :
    Integrable (fun z : Fin 3 → ℝ => Real.exp (-b * nsq z)) volume := by
  simp_rw [exp_nsq_prod b]
  rw [volume_pi]
  exact Integrable.fintype_prod (fun _ => integrable_exp_neg_mul_sq hb)

/-- The exact value of the three-dimensional Gaussian integral. -/
theorem integral_gauss3 (b : ℝ) :
    (∫ z : Fin 3 → ℝ, Real.exp (-b * nsq z)) = Real.sqrt (Real.pi / b) ^ 3 := by
  simp_rw [exp_nsq_prod b]
  rw [integral_fintype_prod_volume_eq_prod (fun (_ : Fin 3) (x : ℝ) => Real.exp (-b * x ^ 2))]
  have hval : (∫ x : ℝ, Real.exp (-(b * x ^ 2))) = Real.sqrt (Real.pi / b) := by
    simpa [neg_mul] using integral_gaussian b
  simp [hval]

/-! ## §13  Continuity, hence almost-everywhere strong measurability -/

theorem continuous_coord (i : Fin 3) : Continuous (fun z : Fin 3 → ℝ => z i) :=
  continuous_apply i

theorem continuous_coordC (i : Fin 3) : Continuous (fun z : Fin 3 → ℝ => ((z i : ℝ) : ℂ)) :=
  Complex.continuous_ofReal.comp (continuous_apply i)

theorem continuous_EF_fin3 (ρ lam : ℝ) :
    Continuous (fun z : Fin 3 → ℝ => EF ρ lam (z 0)) := by
  simp only [EF]
  exact Continuous.cexp ((continuous_const.mul (continuous_coordC 0)).sub
    (continuous_const.mul ((continuous_coordC 0).pow 2)))

theorem continuous_gaussArg_fin3 (ρ σ : ℝ) :
    Continuous (fun z : Fin 3 → ℝ => gaussArg ρ σ (z 1) (z 2)) := by
  simp only [gaussArg, rsq]
  exact (Complex.continuous_ofReal.comp (continuous_const.mul
    (((continuous_coord 1).pow 2).add ((continuous_coord 2).pow 2)))).neg.div_const _

theorem continuous_A_fin3 (ρ σ : ℝ) :
    Continuous (fun z : Fin 3 → ℝ => A ρ σ (z 1) (z 2)) := by
  simp only [A]
  exact continuous_const.mul (continuous_gaussArg_fin3 ρ σ).cexp

theorem continuous_dsA_fin3 (ρ σ : ℝ) :
    Continuous (fun z : Fin 3 → ℝ => dsA ρ σ (z 1) (z 2)) := by
  simp only [dsA, rsq]
  refine Continuous.div_const (Continuous.mul (continuous_gaussArg_fin3 ρ σ).cexp ?_) _
  exact continuous_const.sub (continuous_const.mul (Complex.continuous_ofReal.comp
    (continuous_const.mul (((continuous_coord 1).pow 2).add ((continuous_coord 2).pow 2)))))

theorem continuous_beamF (ρ lam s : ℝ) :
    Continuous (fun z : Fin 3 → ℝ => beamF ρ lam s z) := by
  simp only [beamF, UF]
  exact (continuous_EF_fin3 ρ lam).mul (continuous_A_fin3 ρ (2 * s))

/-- The residual as a function of the three-dimensional transverse variable. -/
def resFv (ρ lam s : ℝ) (z : Fin 3 → ℝ) : ℂ := resF ρ lam s (z 0) (z 1) (z 2)

theorem continuous_resFv (ρ lam s : ℝ) :
    Continuous (fun z : Fin 3 → ℝ => resFv ρ lam s z) := by
  simp only [resFv, resF]
  refine Continuous.mul (Continuous.mul ?_ (continuous_EF_fin3 ρ lam))
    (continuous_dsA_fin3 ρ (2 * s))
  exact continuous_const.mul (Complex.continuous_ofReal.comp
    (continuous_const.mul (continuous_coord 0)))

theorem aestronglyMeasurable_beamF (ρ lam s : ℝ) :
    AEStronglyMeasurable (fun z : Fin 3 → ℝ => beamF ρ lam s z) volume :=
  (continuous_beamF ρ lam s).aestronglyMeasurable

theorem aestronglyMeasurable_resFv (ρ lam s : ℝ) :
    AEStronglyMeasurable (fun z : Fin 3 → ℝ => resFv ρ lam s z) volume :=
  (continuous_resFv ρ lam s).aestronglyMeasurable

/-! ## §14  From an `L²` integral bound to a genuine `eLpNorm` bound -/

/-- A `MemLp` function whose squared norm has integral at most `C` has `eLpNorm ≤ √C`.
The `MemLp` hypothesis is what makes the conclusion meaningful. -/
theorem eLpNorm_le_of_integral_normSq_le {f : (Fin 3 → ℝ) → ℂ}
    (hf : MemLp f 2 (volume : Measure (Fin 3 → ℝ))) {C : ℝ}
    (hC : (∫ z : Fin 3 → ℝ, ‖f z‖ ^ 2) ≤ C) :
    eLpNorm f 2 volume ≤ ENNReal.ofReal (Real.sqrt C) := by
  have hsq : Integrable (fun z : Fin 3 → ℝ => ‖f z‖ ^ 2) volume :=
    (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf
  have hnn : (0 : ℝ) ≤ ∫ z : Fin 3 → ℝ, ‖f z‖ ^ 2 :=
    integral_nonneg (fun z => by positivity)
  rw [hf.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  refine ENNReal.ofReal_le_ofReal ?_
  have htoReal : (2 : ENNReal).toReal = 2 := by norm_num
  rw [htoReal]
  have hrpow : (∫ z : Fin 3 → ℝ, ‖f z‖ ^ (2 : ℝ)) = ∫ z : Fin 3 → ℝ, ‖f z‖ ^ 2 := by
    congr 1
    funext z
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [hrpow, Real.sqrt_eq_rpow, one_div]
  exact Real.rpow_le_rpow hnn hC (by norm_num)

/-! ## §15  Pointwise bounds -/

/-- A pointwise bound for `∂_s A_ρ`, read off the closed form. -/
theorem norm_dsA_le {ρ : ℝ} (hρ : 0 ≤ ρ) (s x₁ x₂ : ℝ) :
    ‖dsA ρ s x₁ x₂‖
      ≤ Real.exp (-(ρ * rsq x₁ x₂) / (2 * (1 + s ^ 2 / 4)))
          * ((2 * Real.sqrt (1 + s ^ 2 / 4) + ρ * rsq x₁ x₂) / 4) := by
  have hw : 0 ≤ ρ * rsq x₁ x₂ := mul_nonneg hρ (rsq_nonneg _ _)
  have hcsn : ‖cs s‖ = Real.sqrt (1 + s ^ 2 / 4) := norm_cs s
  have hcs1 : (1 : ℝ) ≤ ‖cs s‖ := by rw [hcsn]; exact one_le_sqrt_cs s
  have hC3 : (1 : ℝ) ≤ ‖cs s‖ ^ 3 := one_le_pow₀ hcs1
  have hnum : ‖2 * Complex.I * cs s - Complex.I * ((ρ * rsq x₁ x₂ : ℝ) : ℂ)‖
      ≤ 2 * ‖cs s‖ + ρ * rsq x₁ x₂ := by
    have heq : 2 * Complex.I * cs s - Complex.I * ((ρ * rsq x₁ x₂ : ℝ) : ℂ)
        = Complex.I * (2 * cs s - ((ρ * rsq x₁ x₂ : ℝ) : ℂ)) := by ring
    rw [heq, norm_mul, Complex.norm_I, one_mul]
    calc ‖2 * cs s - ((ρ * rsq x₁ x₂ : ℝ) : ℂ)‖
        ≤ ‖(2 : ℂ) * cs s‖ + ‖((ρ * rsq x₁ x₂ : ℝ) : ℂ)‖ := norm_sub_le _ _
      _ = 2 * ‖cs s‖ + ρ * rsq x₁ x₂ := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw]
          norm_num
  have hden : ‖(4 : ℂ) * cs s ^ 3‖ = 4 * ‖cs s‖ ^ 3 := by
    rw [norm_mul, norm_pow]
    norm_num
  rw [dsA, norm_div, norm_mul, Complex.norm_exp, gaussArg_re, hden, ← hcsn]
  have hpos : (0 : ℝ) < 4 * ‖cs s‖ ^ 3 := by positivity
  have hkey : ‖2 * Complex.I * cs s - Complex.I * ((ρ * rsq x₁ x₂ : ℝ) : ℂ)‖
      / (4 * ‖cs s‖ ^ 3) ≤ (2 * ‖cs s‖ + ρ * rsq x₁ x₂) / 4 := by
    rw [div_le_iff₀ hpos]
    have hrw : (2 * ‖cs s‖ + ρ * rsq x₁ x₂) / 4 * (4 * ‖cs s‖ ^ 3)
        = (2 * ‖cs s‖ + ρ * rsq x₁ x₂) * ‖cs s‖ ^ 3 := by ring
    rw [hrw]
    nlinarith [hnum, hC3, hcs1, hw,
      mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * ‖cs s‖ + ρ * rsq x₁ x₂)
        (by linarith : (0 : ℝ) ≤ ‖cs s‖ ^ 3 - 1)]
  have hE : (0 : ℝ) ≤ Real.exp (-(ρ * rsq x₁ x₂) / (2 * (1 + s ^ 2 / 4))) := (Real.exp_pos _).le
  calc Real.exp (-(ρ * rsq x₁ x₂) / (2 * (1 + s ^ 2 / 4)))
        * ‖2 * Complex.I * cs s - Complex.I * ((ρ * rsq x₁ x₂ : ℝ) : ℂ)‖ / (4 * ‖cs s‖ ^ 3)
      = Real.exp (-(ρ * rsq x₁ x₂) / (2 * (1 + s ^ 2 / 4)))
        * (‖2 * Complex.I * cs s - Complex.I * ((ρ * rsq x₁ x₂ : ℝ) : ℂ)‖
            / (4 * ‖cs s‖ ^ 3)) := by ring
    _ ≤ Real.exp (-(ρ * rsq x₁ x₂) / (2 * (1 + s ^ 2 / 4)))
        * ((2 * ‖cs s‖ + ρ * rsq x₁ x₂) / 4) := mul_le_mul_of_nonneg_left hkey hE

/-- The transverse-amplitude derivative on a bounded slab, with the `ρ r²` growth already
absorbed into the constant at the cost of half the Gaussian decay. -/
theorem norm_dsA_two_s_le {ρ : ℝ} (hρ : 0 ≤ ρ) {S s : ℝ} (hs : |s| ≤ S) (z₁ z₂ : ℝ) :
    ‖dsA ρ (2 * s) z₁ z₂‖
      ≤ ((2 * Real.sqrt (mS S) + 4 * mS S) / 4)
          * Real.exp (-(ρ * rsq z₁ z₂ / (4 * mS S))) := by
  have hw : 0 ≤ rsq z₁ z₂ := rsq_nonneg z₁ z₂
  have hρw : 0 ≤ ρ * rsq z₁ z₂ := mul_nonneg hρ hw
  have hsq : s ^ 2 ≤ S ^ 2 := by nlinarith [sq_abs s, abs_nonneg s]
  have hm : (0 : ℝ) < 1 + s ^ 2 := by positivity
  have hmS : (1 : ℝ) ≤ mS S := one_le_mS S
  have hle : 1 + s ^ 2 ≤ mS S := by unfold mS; linarith
  have hbase := norm_dsA_le hρ (2 * s) z₁ z₂
  have heq : 1 + (2 * s) ^ 2 / 4 = 1 + s ^ 2 := by ring
  rw [heq] at hbase
  set E : ℝ := Real.exp (-(1 / (4 * (1 + s ^ 2)) * (ρ * rsq z₁ z₂))) with hEdef
  have hEpos : 0 < E := Real.exp_pos _
  have hE1 : E ≤ 1 := by
    have hnn : (0 : ℝ) ≤ 1 / (4 * (1 + s ^ 2)) * (ρ * rsq z₁ z₂) := by positivity
    have hle0 : E ≤ Real.exp 0 := Real.exp_le_exp.mpr (by linarith)
    simpa using hle0
  have hsplit : Real.exp (-(ρ * rsq z₁ z₂) / (2 * (1 + s ^ 2)))
      = E * Real.exp (-(ρ * rsq z₁ z₂ / (4 * (1 + s ^ 2)))) := by
    rw [hEdef, ← Real.exp_add]
    congr 1
    field_simp
    ring
  have h1 : ρ * rsq z₁ z₂ * E ≤ 4 * (1 + s ^ 2) := by
    have hx := xexp_le_inv (a := 1 / (4 * (1 + s ^ 2))) (ξ := ρ * rsq z₁ z₂) (by positivity)
    calc ρ * rsq z₁ z₂ * E ≤ 1 / (1 / (4 * (1 + s ^ 2))) := hx
      _ = 4 * (1 + s ^ 2) := by field_simp
  have hsq1 : Real.sqrt (1 + s ^ 2) ≤ Real.sqrt (mS S) := Real.sqrt_le_sqrt hle
  have hA : (2 * Real.sqrt (1 + s ^ 2) + ρ * rsq z₁ z₂) * E
      ≤ 2 * Real.sqrt (mS S) + 4 * mS S := by
    have hterm1 : 2 * Real.sqrt (1 + s ^ 2) * E ≤ 2 * Real.sqrt (mS S) := by
      calc 2 * Real.sqrt (1 + s ^ 2) * E ≤ 2 * Real.sqrt (1 + s ^ 2) * 1 :=
            mul_le_mul_of_nonneg_left hE1 (by positivity)
        _ = 2 * Real.sqrt (1 + s ^ 2) := by ring
        _ ≤ 2 * Real.sqrt (mS S) := by linarith
    have hterm2 : ρ * rsq z₁ z₂ * E ≤ 4 * mS S := by linarith
    have hexpand : (2 * Real.sqrt (1 + s ^ 2) + ρ * rsq z₁ z₂) * E
        = 2 * Real.sqrt (1 + s ^ 2) * E + ρ * rsq z₁ z₂ * E := by ring
    rw [hexpand]
    linarith
  have hmono : Real.exp (-(ρ * rsq z₁ z₂ / (4 * (1 + s ^ 2))))
      ≤ Real.exp (-(ρ * rsq z₁ z₂ / (4 * mS S))) := by
    refine Real.exp_le_exp.mpr ?_
    have : ρ * rsq z₁ z₂ / (4 * mS S) ≤ ρ * rsq z₁ z₂ / (4 * (1 + s ^ 2)) :=
      div_le_div_of_nonneg_left hρw (by positivity) (by linarith)
    linarith
  calc ‖dsA ρ (2 * s) z₁ z₂‖
      ≤ Real.exp (-(ρ * rsq z₁ z₂) / (2 * (1 + s ^ 2)))
          * ((2 * Real.sqrt (1 + s ^ 2) + ρ * rsq z₁ z₂) / 4) := hbase
    _ = ((2 * Real.sqrt (1 + s ^ 2) + ρ * rsq z₁ z₂) * E / 4)
          * Real.exp (-(ρ * rsq z₁ z₂ / (4 * (1 + s ^ 2)))) := by rw [hsplit]; ring
    _ ≤ ((2 * Real.sqrt (mS S) + 4 * mS S) / 4)
          * Real.exp (-(ρ * rsq z₁ z₂ / (4 * (1 + s ^ 2)))) := by
        refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
        linarith
    _ ≤ ((2 * Real.sqrt (mS S) + 4 * mS S) / 4)
          * Real.exp (-(ρ * rsq z₁ z₂ / (4 * mS S))) := by
        refine mul_le_mul_of_nonneg_left hmono ?_
        have := Real.sqrt_nonneg (mS S)
        have := (mS_pos S).le
        positivity

/-- The exact modulus of the residual. -/
theorem norm_resFv {ρ lam : ℝ} (hρ : 0 ≤ ρ) (hlam : 0 ≤ lam) (s : ℝ) (z : Fin 3 → ℝ) :
    ‖resFv ρ lam s z‖
      = 4 * (ρ * lam * |z 0|) * Real.exp (-(ρ * lam / 2 * z 0 ^ 2))
          * ‖dsA ρ (2 * s) (z 1) (z 2)‖ := by
  simp only [resFv, resF, norm_mul, norm_neg, norm_EF, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hρ, abs_of_nonneg hlam]
  norm_num

/-- The residual constant. -/
def Kres (lam S : ℝ) : ℝ := 32 * lam * ((2 * Real.sqrt (mS S) + 4 * mS S) / 4) ^ 2

theorem Kres_nonneg {lam : ℝ} (hlam : 0 ≤ lam) (S : ℝ) : 0 ≤ Kres lam S := by
  unfold Kres
  have := Real.sqrt_nonneg (mS S)
  have := (mS_pos S).le
  positivity

/-- **The pointwise squared bound for the interior residual**, with every power of `ρ`
displayed: one factor `ρ¹` in front, and a Gaussian of width `ρ^{-1/2}` in all three
transverse directions. -/
theorem normSq_resFv_le {ρ lam : ℝ} (hρ : 0 < ρ) (hlam : 0 < lam) {S s : ℝ} (hs : |s| ≤ S)
    (z : Fin 3 → ℝ) :
    ‖resFv ρ lam s z‖ ^ 2
      ≤ Kres lam S * ρ * Real.exp (-(ρ * betS lam S / 2) * nsq z) := by
  have hmS : (1 : ℝ) ≤ mS S := one_le_mS S
  have hmSpos : (0 : ℝ) < mS S := mS_pos S
  have hbet : 0 < betS lam S := betS_pos hlam S
  have hKd : (0 : ℝ) ≤ (2 * Real.sqrt (mS S) + 4 * mS S) / 4 := by
    have := Real.sqrt_nonneg (mS S); positivity
  -- the longitudinal factor
  have hstep1 : z 0 ^ 2 * Real.exp (-(ρ * lam * z 0 ^ 2))
      ≤ 2 / (ρ * lam) * Real.exp (-(ρ * lam / 2 * z 0 ^ 2)) := by
    have hx := xexp_le_inv (a := ρ * lam / 2) (ξ := z 0 ^ 2) (by positivity)
    have h2 : (1 : ℝ) / (ρ * lam / 2) = 2 / (ρ * lam) := by field_simp
    rw [h2] at hx
    have hfac : Real.exp (-(ρ * lam * z 0 ^ 2))
        = Real.exp (-(ρ * lam / 2 * z 0 ^ 2)) * Real.exp (-(ρ * lam / 2 * z 0 ^ 2)) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [hfac, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right hx (Real.exp_pos _).le
  -- the transverse factor
  have hd := norm_dsA_two_s_le hρ.le hs (z 1) (z 2)
  have hdnn : (0 : ℝ) ≤ ‖dsA ρ (2 * s) (z 1) (z 2)‖ := norm_nonneg _
  have hd2 : ‖dsA ρ (2 * s) (z 1) (z 2)‖ ^ 2
      ≤ ((2 * Real.sqrt (mS S) + 4 * mS S) / 4) ^ 2
          * Real.exp (-(ρ * rsq (z 1) (z 2) / (2 * mS S))) := by
    have hmul := mul_self_le_mul_self hdnn hd
    have hrhs : (((2 * Real.sqrt (mS S) + 4 * mS S) / 4)
          * Real.exp (-(ρ * rsq (z 1) (z 2) / (4 * mS S))))
        * (((2 * Real.sqrt (mS S) + 4 * mS S) / 4)
          * Real.exp (-(ρ * rsq (z 1) (z 2) / (4 * mS S))))
        = ((2 * Real.sqrt (mS S) + 4 * mS S) / 4) ^ 2
          * Real.exp (-(ρ * rsq (z 1) (z 2) / (2 * mS S))) := by
      rw [sq, mul_mul_mul_comm, ← Real.exp_add]
      congr 2
      field_simp
      ring
    rw [sq]
    rw [hrhs] at hmul
    exact hmul
  -- assemble
  have hnorm := norm_resFv hρ.le hlam.le s z
  have habs : |z 0| ^ 2 = z 0 ^ 2 := sq_abs _
  have hexp2 : Real.exp (-(ρ * lam / 2 * z 0 ^ 2)) ^ 2 = Real.exp (-(ρ * lam * z 0 ^ 2)) := by
    rw [sq, ← Real.exp_add]; congr 1; ring
  have hsqexp : ‖resFv ρ lam s z‖ ^ 2
      = 16 * (ρ * lam) ^ 2 * (z 0 ^ 2 * Real.exp (-(ρ * lam * z 0 ^ 2)))
          * ‖dsA ρ (2 * s) (z 1) (z 2)‖ ^ 2 := by
    rw [hnorm]
    rw [mul_pow, mul_pow, mul_pow, mul_pow, habs, hexp2]
    ring
  rw [hsqexp]
  have hfinal : Real.exp (-(ρ * lam / 2 * z 0 ^ 2))
        * Real.exp (-(ρ * rsq (z 1) (z 2) / (2 * mS S)))
      ≤ Real.exp (-(ρ * betS lam S / 2) * nsq z) := by
    rw [← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have hbl : betS lam S ≤ lam := betS_le_lam lam S
    have hbm : betS lam S ≤ 1 / mS S := betS_le_inv_mS lam S
    have hrsq : rsq (z 1) (z 2) = z 1 ^ 2 + z 2 ^ 2 := rfl
    rw [hrsq, nsq_apply]
    have h1 : ρ * betS lam S / 2 * z 0 ^ 2 ≤ ρ * lam / 2 * z 0 ^ 2 := by
      nlinarith [mul_nonneg (mul_nonneg hρ.le (sq_nonneg (z 0))) (sub_nonneg.mpr hbl)]
    have h2 : ρ * betS lam S / 2 * (z 1 ^ 2 + z 2 ^ 2)
        ≤ ρ * (z 1 ^ 2 + z 2 ^ 2) / (2 * mS S) := by
      have hnn : (0 : ℝ) ≤ z 1 ^ 2 + z 2 ^ 2 := by positivity
      have hdiff : 0 ≤ 1 / mS S - betS lam S := by linarith
      have hbase : (0 : ℝ) ≤ ρ * (z 1 ^ 2 + z 2 ^ 2) := by positivity
      have hprod : 0 ≤ ρ * (z 1 ^ 2 + z 2 ^ 2) * (1 / mS S - betS lam S) / 2 := by
        have := mul_nonneg hbase hdiff
        linarith
      have hid : ρ * (z 1 ^ 2 + z 2 ^ 2) / (2 * mS S) - ρ * betS lam S / 2 * (z 1 ^ 2 + z 2 ^ 2)
          = ρ * (z 1 ^ 2 + z 2 ^ 2) * (1 / mS S - betS lam S) / 2 := by
        field_simp
      linarith
    linarith
  have hconst : (0 : ℝ) ≤ 16 * (ρ * lam) ^ 2 := by positivity
  calc 16 * (ρ * lam) ^ 2 * (z 0 ^ 2 * Real.exp (-(ρ * lam * z 0 ^ 2)))
        * ‖dsA ρ (2 * s) (z 1) (z 2)‖ ^ 2
      ≤ 16 * (ρ * lam) ^ 2 * (2 / (ρ * lam) * Real.exp (-(ρ * lam / 2 * z 0 ^ 2)))
        * (((2 * Real.sqrt (mS S) + 4 * mS S) / 4) ^ 2
            * Real.exp (-(ρ * rsq (z 1) (z 2) / (2 * mS S)))) := by
        have hY : (0:ℝ) ≤ ‖dsA ρ (2 * s) (z 1) (z 2)‖ ^ 2 := by positivity
        have hconst : (0:ℝ) ≤ 16 * (ρ * lam) ^ 2 := by positivity
        have step1 : 16 * (ρ * lam) ^ 2 * (z 0 ^ 2 * Real.exp (-(ρ * lam * z 0 ^ 2)))
            ≤ 16 * (ρ * lam) ^ 2 * (2 / (ρ * lam) * Real.exp (-(ρ * lam / 2 * z 0 ^ 2))) :=
          mul_le_mul_of_nonneg_left hstep1 hconst
        refine mul_le_mul step1 hd2 hY ?_
        have hx : (0:ℝ) ≤ 2 / (ρ * lam) * Real.exp (-(ρ * lam / 2 * z 0 ^ 2)) := by positivity
        positivity
    _ = Kres lam S * ρ
          * (Real.exp (-(ρ * lam / 2 * z 0 ^ 2))
              * Real.exp (-(ρ * rsq (z 1) (z 2) / (2 * mS S)))) := by
        unfold Kres
        field_simp
        ring
    _ ≤ Kres lam S * ρ * Real.exp (-(ρ * betS lam S / 2) * nsq z) := by
        refine mul_le_mul_of_nonneg_left hfinal ?_
        have := Kres_nonneg hlam.le S
        positivity

/-- **The pointwise squared bound for the beam.** -/
theorem normSq_beamF_le {ρ lam : ℝ} (hρ : 0 ≤ ρ) (hlam : 0 < lam) {S s : ℝ} (hs : |s| ≤ S)
    (z : Fin 3 → ℝ) :
    ‖beamF ρ lam s z‖ ^ 2 ≤ Real.exp (-(ρ * betS lam S) * nsq z) := by
  have h := norm_beamF_le hρ hlam hs z
  have hnn : (0 : ℝ) ≤ ‖beamF ρ lam s z‖ := norm_nonneg _
  have hmul := mul_self_le_mul_self hnn h
  have hrhs : Real.exp (-(ρ * betS lam S / 2 * nsq z)) * Real.exp (-(ρ * betS lam S / 2 * nsq z))
      = Real.exp (-(ρ * betS lam S) * nsq z) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [sq]
  rw [hrhs] at hmul
  exact hmul

/-- **The pointwise squared lower bound for the beam.** -/
theorem le_normSq_beamF {ρ lam : ℝ} (hρ : 0 ≤ ρ) {S s : ℝ} (hs : |s| ≤ S) (z : Fin 3 → ℝ) :
    (mS S)⁻¹ * Real.exp (-(ρ * gamS lam) * nsq z) ≤ ‖beamF ρ lam s z‖ ^ 2 := by
  have hmSpos : (0 : ℝ) < mS S := mS_pos S
  have h := le_norm_beamF (lam := lam) hρ hs z
  have hLnn : (0 : ℝ) ≤ (Real.sqrt (mS S))⁻¹ * Real.exp (-(ρ * gamS lam / 2 * nsq z)) := by
    have := Real.sqrt_nonneg (mS S); positivity
  have hmul := mul_self_le_mul_self hLnn h
  have hlhs : ((Real.sqrt (mS S))⁻¹ * Real.exp (-(ρ * gamS lam / 2 * nsq z)))
        * ((Real.sqrt (mS S))⁻¹ * Real.exp (-(ρ * gamS lam / 2 * nsq z)))
      = (mS S)⁻¹ * Real.exp (-(ρ * gamS lam) * nsq z) := by
    have hx : -(ρ * gamS lam / 2 * nsq z) + -(ρ * gamS lam / 2 * nsq z)
        = -(ρ * gamS lam) * nsq z := by ring
    rw [mul_mul_mul_comm, ← Real.exp_add, ← mul_inv, Real.mul_self_sqrt hmSpos.le, hx]
  rw [sq]
  rw [hlhs] at hmul
  exact hmul


/-! ## §16  Integrability, `MemLp`, and genuine `eLpNorm` bounds -/

theorem integrable_normSq_resFv {ρ lam : ℝ} (hρ : 0 < ρ) (hlam : 0 < lam) {S s : ℝ}
    (hs : |s| ≤ S) :
    Integrable (fun z : Fin 3 → ℝ => ‖resFv ρ lam s z‖ ^ 2) volume := by
  have hbet : 0 < betS lam S := betS_pos hlam S
  have hb : 0 < ρ * betS lam S / 2 := by positivity
  refine Integrable.mono' ((integrable_gauss3 hb).const_mul (Kres lam S * ρ)) ?_ ?_
  · exact ((continuous_resFv ρ lam s).norm.pow 2).aestronglyMeasurable
  · filter_upwards with z
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact normSq_resFv_le hρ hlam hs z

theorem integrable_normSq_beamF {ρ lam : ℝ} (hρ : 0 < ρ) (hlam : 0 < lam) {S s : ℝ}
    (hs : |s| ≤ S) :
    Integrable (fun z : Fin 3 → ℝ => ‖beamF ρ lam s z‖ ^ 2) volume := by
  have hbet : 0 < betS lam S := betS_pos hlam S
  have hb : 0 < ρ * betS lam S := by positivity
  refine Integrable.mono' (integrable_gauss3 hb) ?_ ?_
  · exact ((continuous_beamF ρ lam s).norm.pow 2).aestronglyMeasurable
  · filter_upwards with z
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact normSq_beamF_le hρ.le hlam hs z

/-- **`MemLp` for the beam** — proved before any `L²` estimate is stated. -/
theorem memLp_beamF {ρ lam : ℝ} (hρ : 0 < ρ) (hlam : 0 < lam) {S s : ℝ} (hs : |s| ≤ S) :
    MemLp (fun z : Fin 3 → ℝ => beamF ρ lam s z) 2 volume :=
  (memLp_two_iff_integrable_sq_norm (aestronglyMeasurable_beamF ρ lam s)).mpr
    (integrable_normSq_beamF hρ hlam hs)

/-- **`MemLp` for the interior residual.** -/
theorem memLp_resFv {ρ lam : ℝ} (hρ : 0 < ρ) (hlam : 0 < lam) {S s : ℝ} (hs : |s| ≤ S) :
    MemLp (fun z : Fin 3 → ℝ => resFv ρ lam s z) 2 volume :=
  (memLp_two_iff_integrable_sq_norm (aestronglyMeasurable_resFv ρ lam s)).mpr
    (integrable_normSq_resFv hρ hlam hs)

/-! ### The squared `L²` integrals, with every power of `ρ` explicit -/

theorem integral_normSq_resFv_le {ρ lam : ℝ} (hρ : 0 < ρ) (hlam : 0 < lam) {S s : ℝ}
    (hs : |s| ≤ S) :
    (∫ z : Fin 3 → ℝ, ‖resFv ρ lam s z‖ ^ 2)
      ≤ Kres lam S * ρ * Real.sqrt (Real.pi / (ρ * betS lam S / 2)) ^ 3 := by
  have hbet : 0 < betS lam S := betS_pos hlam S
  have hb : 0 < ρ * betS lam S / 2 := by positivity
  have hmono : (fun z : Fin 3 → ℝ => ‖resFv ρ lam s z‖ ^ 2)
      ≤ fun z : Fin 3 → ℝ => Kres lam S * ρ * Real.exp (-(ρ * betS lam S / 2) * nsq z) :=
    fun z => normSq_resFv_le hρ hlam hs z
  calc (∫ z : Fin 3 → ℝ, ‖resFv ρ lam s z‖ ^ 2)
      ≤ ∫ z : Fin 3 → ℝ, Kres lam S * ρ * Real.exp (-(ρ * betS lam S / 2) * nsq z) :=
        integral_mono (integrable_normSq_resFv hρ hlam hs)
          ((integrable_gauss3 hb).const_mul _) hmono
    _ = Kres lam S * ρ * ∫ z : Fin 3 → ℝ, Real.exp (-(ρ * betS lam S / 2) * nsq z) :=
        integral_const_mul _ _
    _ = Kres lam S * ρ * Real.sqrt (Real.pi / (ρ * betS lam S / 2)) ^ 3 := by
        rw [integral_gauss3]

theorem integral_normSq_beamF_le {ρ lam : ℝ} (hρ : 0 < ρ) (hlam : 0 < lam) {S s : ℝ}
    (hs : |s| ≤ S) :
    (∫ z : Fin 3 → ℝ, ‖beamF ρ lam s z‖ ^ 2)
      ≤ Real.sqrt (Real.pi / (ρ * betS lam S)) ^ 3 := by
  have hbet : 0 < betS lam S := betS_pos hlam S
  have hb : 0 < ρ * betS lam S := by positivity
  have hmono : (fun z : Fin 3 → ℝ => ‖beamF ρ lam s z‖ ^ 2)
      ≤ fun z : Fin 3 → ℝ => Real.exp (-(ρ * betS lam S) * nsq z) :=
    fun z => normSq_beamF_le hρ.le hlam hs z
  calc (∫ z : Fin 3 → ℝ, ‖beamF ρ lam s z‖ ^ 2)
      ≤ ∫ z : Fin 3 → ℝ, Real.exp (-(ρ * betS lam S) * nsq z) :=
        integral_mono (integrable_normSq_beamF hρ hlam hs) (integrable_gauss3 hb) hmono
    _ = Real.sqrt (Real.pi / (ρ * betS lam S)) ^ 3 := integral_gauss3 _

theorem le_integral_normSq_beamF {ρ lam : ℝ} (hρ : 0 < ρ) (hlam : 0 < lam) {S s : ℝ}
    (hs : |s| ≤ S) :
    (mS S)⁻¹ * Real.sqrt (Real.pi / (ρ * gamS lam)) ^ 3
      ≤ ∫ z : Fin 3 → ℝ, ‖beamF ρ lam s z‖ ^ 2 := by
  have hgam : 0 < gamS lam := gamS_pos lam
  have hb : 0 < ρ * gamS lam := by positivity
  have hmono : (fun z : Fin 3 → ℝ => (mS S)⁻¹ * Real.exp (-(ρ * gamS lam) * nsq z))
      ≤ fun z : Fin 3 → ℝ => ‖beamF ρ lam s z‖ ^ 2 :=
    fun z => le_normSq_beamF hρ.le hs z
  calc (mS S)⁻¹ * Real.sqrt (Real.pi / (ρ * gamS lam)) ^ 3
      = (mS S)⁻¹ * ∫ z : Fin 3 → ℝ, Real.exp (-(ρ * gamS lam) * nsq z) := by
        rw [integral_gauss3]
    _ = ∫ z : Fin 3 → ℝ, (mS S)⁻¹ * Real.exp (-(ρ * gamS lam) * nsq z) :=
        (integral_const_mul _ _).symm
    _ ≤ ∫ z : Fin 3 → ℝ, ‖beamF ρ lam s z‖ ^ 2 :=
        integral_mono ((integrable_gauss3 hb).const_mul _)
          (integrable_normSq_beamF hρ hlam hs) hmono

/-! ### The `ρ`-order bookkeeping -/

/-- The residual constant: `‖residual‖_{L²}² ≤ C_res ρ^{-1/2}`. -/
def Cres (lam S : ℝ) : ℝ := Kres lam S * Real.sqrt (2 * Real.pi / betS lam S) ^ 3

/-- The beam upper constant: `‖U‖_{L²}² ≤ C_beam ρ^{-3/2}`. -/
def Cbeam (lam S : ℝ) : ℝ := Real.sqrt (Real.pi / betS lam S) ^ 3

/-- The beam lower constant: `‖U‖_{L²}² ≥ c_beam ρ^{-3/2}`. -/
def cbeam (lam S : ℝ) : ℝ := (mS S)⁻¹ * Real.sqrt (Real.pi / gamS lam) ^ 3

theorem cbeam_pos (lam S : ℝ) : 0 < cbeam lam S := by
  have hgam : 0 < gamS lam := gamS_pos lam
  have hmS : 0 < mS S := mS_pos S
  have hpi : 0 < Real.pi := Real.pi_pos
  have : 0 < Real.sqrt (Real.pi / gamS lam) := Real.sqrt_pos.mpr (by positivity)
  unfold cbeam
  positivity

theorem sqrt_cube_rho {ρ : ℝ} (hρ : 0 < ρ) : Real.sqrt ρ ^ 3 = ρ * Real.sqrt ρ := by
  have h := Real.sq_sqrt hρ.le
  calc Real.sqrt ρ ^ 3 = Real.sqrt ρ ^ 2 * Real.sqrt ρ := by ring
    _ = ρ * Real.sqrt ρ := by rw [h]

/-- **`ρ`-order of the interior residual**: `∫ ‖□_F U‖² ≤ C_res ρ^{-1/2}`.

Hence `‖□_F U‖_{L²(ℝ³)} = O(ρ^{-1/4})`. -/
theorem integral_normSq_resFv_le_rho {ρ lam : ℝ} (hρ : 0 < ρ) (hlam : 0 < lam) {S s : ℝ}
    (hs : |s| ≤ S) :
    (∫ z : Fin 3 → ℝ, ‖resFv ρ lam s z‖ ^ 2) ≤ Cres lam S / Real.sqrt ρ := by
  have hbet : 0 < betS lam S := betS_pos hlam S
  have hsr : 0 < Real.sqrt ρ := Real.sqrt_pos.mpr hρ
  have harg : Real.pi / (ρ * betS lam S / 2) = (2 * Real.pi / betS lam S) / ρ := by
    field_simp
  have hkey : Kres lam S * ρ * Real.sqrt (Real.pi / (ρ * betS lam S / 2)) ^ 3
      = Cres lam S / Real.sqrt ρ := by
    rw [harg, Real.sqrt_div (by positivity) ρ, div_pow, sqrt_cube_rho hρ, Cres]
    field_simp
  calc (∫ z : Fin 3 → ℝ, ‖resFv ρ lam s z‖ ^ 2)
      ≤ Kres lam S * ρ * Real.sqrt (Real.pi / (ρ * betS lam S / 2)) ^ 3 :=
        integral_normSq_resFv_le hρ hlam hs
    _ = Cres lam S / Real.sqrt ρ := hkey

/-- **`ρ`-order of the beam (upper)**: `∫ ‖U‖² ≤ C_beam ρ^{-3/2}`. -/
theorem integral_normSq_beamF_le_rho {ρ lam : ℝ} (hρ : 0 < ρ) (hlam : 0 < lam) {S s : ℝ}
    (hs : |s| ≤ S) :
    (∫ z : Fin 3 → ℝ, ‖beamF ρ lam s z‖ ^ 2) ≤ Cbeam lam S / (ρ * Real.sqrt ρ) := by
  have hbet : 0 < betS lam S := betS_pos hlam S
  have hsr : 0 < Real.sqrt ρ := Real.sqrt_pos.mpr hρ
  have harg : Real.pi / (ρ * betS lam S) = (Real.pi / betS lam S) / ρ := by
    field_simp
  have hkey : Real.sqrt (Real.pi / (ρ * betS lam S)) ^ 3 = Cbeam lam S / (ρ * Real.sqrt ρ) := by
    rw [harg, Real.sqrt_div (by positivity) ρ, div_pow, sqrt_cube_rho hρ, Cbeam]
  calc (∫ z : Fin 3 → ℝ, ‖beamF ρ lam s z‖ ^ 2)
      ≤ Real.sqrt (Real.pi / (ρ * betS lam S)) ^ 3 := integral_normSq_beamF_le hρ hlam hs
    _ = Cbeam lam S / (ρ * Real.sqrt ρ) := hkey

/-- **`ρ`-order of the beam (lower)**: `∫ ‖U‖² ≥ c_beam ρ^{-3/2}`, with `c_beam > 0`.
The beam really does carry mass of exactly this order; the upper bound is not vacuous. -/
theorem le_integral_normSq_beamF_rho {ρ lam : ℝ} (hρ : 0 < ρ) (hlam : 0 < lam) {S s : ℝ}
    (hs : |s| ≤ S) :
    cbeam lam S / (ρ * Real.sqrt ρ) ≤ ∫ z : Fin 3 → ℝ, ‖beamF ρ lam s z‖ ^ 2 := by
  have hgam : 0 < gamS lam := gamS_pos lam
  have hsr : 0 < Real.sqrt ρ := Real.sqrt_pos.mpr hρ
  have harg : Real.pi / (ρ * gamS lam) = (Real.pi / gamS lam) / ρ := by field_simp
  have hkey : (mS S)⁻¹ * Real.sqrt (Real.pi / (ρ * gamS lam)) ^ 3
      = cbeam lam S / (ρ * Real.sqrt ρ) := by
    rw [harg, Real.sqrt_div (by positivity) ρ, div_pow, sqrt_cube_rho hρ, cbeam]
    ring
  calc cbeam lam S / (ρ * Real.sqrt ρ)
      = (mS S)⁻¹ * Real.sqrt (Real.pi / (ρ * gamS lam)) ^ 3 := hkey.symm
    _ ≤ ∫ z : Fin 3 → ℝ, ‖beamF ρ lam s z‖ ^ 2 := le_integral_normSq_beamF hρ hlam hs

/-- **The honest relative statement.**

`∫ ‖□_F U‖² ≤ (C_res / c_beam) · ρ · ∫ ‖U‖²`.

Thus `‖□_F U‖_{L²} / ‖U‖_{L²} = O(ρ^{1/2})`: the residual of this **first-order** beam is
*not* small relative to the beam.  Making it small requires higher-order phase and amplitude
corrections, which are outside the scope of this packet and are **not** claimed here. -/
theorem residual_relative_bound {ρ lam : ℝ} (hρ : 0 < ρ) (hlam : 0 < lam) {S s : ℝ}
    (hs : |s| ≤ S) :
    (∫ z : Fin 3 → ℝ, ‖resFv ρ lam s z‖ ^ 2)
      ≤ (Cres lam S / cbeam lam S) * ρ * (∫ z : Fin 3 → ℝ, ‖beamF ρ lam s z‖ ^ 2) := by
  have hcb : 0 < cbeam lam S := cbeam_pos lam S
  have hsr : 0 < Real.sqrt ρ := Real.sqrt_pos.mpr hρ
  have hlow := le_integral_normSq_beamF_rho hρ hlam hs
  have hup := integral_normSq_resFv_le_rho hρ hlam hs
  have hcoef : 0 ≤ Cres lam S / cbeam lam S * ρ := by
    have hCres : 0 ≤ Cres lam S := by
      unfold Cres
      have h1 := Kres_nonneg hlam.le S
      have h2 := Real.sqrt_nonneg (2 * Real.pi / betS lam S)
      positivity
    positivity
  have hstep : (Cres lam S / cbeam lam S) * ρ * (cbeam lam S / (ρ * Real.sqrt ρ))
      = Cres lam S / Real.sqrt ρ := by
    field_simp
  calc (∫ z : Fin 3 → ℝ, ‖resFv ρ lam s z‖ ^ 2)
      ≤ Cres lam S / Real.sqrt ρ := hup
    _ = (Cres lam S / cbeam lam S) * ρ * (cbeam lam S / (ρ * Real.sqrt ρ)) := hstep.symm
    _ ≤ (Cres lam S / cbeam lam S) * ρ * (∫ z : Fin 3 → ℝ, ‖beamF ρ lam s z‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hlow hcoef

/-! ### Genuine `eLpNorm` bounds -/

/-- **`eLpNorm` bound for the beam.** -/
theorem eLpNorm_beamF_le {ρ lam : ℝ} (hρ : 0 < ρ) (hlam : 0 < lam) {S s : ℝ} (hs : |s| ≤ S) :
    eLpNorm (fun z : Fin 3 → ℝ => beamF ρ lam s z) 2 volume
      ≤ ENNReal.ofReal (Real.sqrt (Cbeam lam S / (ρ * Real.sqrt ρ))) :=
  eLpNorm_le_of_integral_normSq_le (memLp_beamF hρ hlam hs)
    (integral_normSq_beamF_le_rho hρ hlam hs)

/-- **`eLpNorm` bound for the interior residual.** -/
theorem eLpNorm_resFv_le {ρ lam : ℝ} (hρ : 0 < ρ) (hlam : 0 < lam) {S s : ℝ} (hs : |s| ≤ S) :
    eLpNorm (fun z : Fin 3 → ℝ => resFv ρ lam s z) 2 volume
      ≤ ENNReal.ofReal (Real.sqrt (Cres lam S / Real.sqrt ρ)) :=
  eLpNorm_le_of_integral_normSq_le (memLp_resFv hρ hlam hs)
    (integral_normSq_resFv_le_rho hρ hlam hs)

/-- **The boundary mismatch, measured in the same genuine seminorm, is exactly zero.**
Not `O(ρ^{-N})` for some `N`: identically `0`. -/
theorem eLpNorm_boundary_mismatch (ρ lam : ℝ) :
    eLpNorm (fun p : ℝ × ℝ × ℝ => Udiff ρ lam p.1 p.2.1 p.2.2 0) 2 volume = 0 := by
  have hzero : (fun p : ℝ × ℝ × ℝ => Udiff ρ lam p.1 p.2.1 p.2.2 0) = fun _ => (0 : ℂ) := by
    funext p
    exact Udiff_zero_at_z_zero ρ lam p.1 p.2.1 p.2.2
  rw [hzero]
  simp

/-! ## §17  The negative `L²` theorem: why `λ > 0` is unavoidable -/

theorem norm_beamF_zero_lam (ρ s : ℝ) (z : Fin 3 → ℝ) :
    ‖beamF ρ 0 s z‖ = ‖A ρ (2 * s) (z 1) (z 2)‖ := by
  rw [beamF, UF, norm_mul, norm_EF]
  norm_num

theorem A_ne_zero (ρ σ x₁ x₂ : ℝ) : A ρ σ x₁ x₂ ≠ 0 := by
  rw [A]
  exact mul_ne_zero (inv_ne_zero (cs_ne_zero _)) (Complex.exp_ne_zero _)

/-- **The undamped (`λ = 0`) Fermi beam is not square-integrable along the third transverse
direction.**

Its modulus is *independent* of the longitudinal coordinate `z₀`, so the squared modulus is a
non-zero constant along that line and `volume (ℝ) = ∞`.

This is the sharpest form of the failure of the version-0.2 two-transverse model: the exact
solution of `□_F U = 0` produced by that phase carries no decay whatsoever in the omitted
direction.  Introducing `λ > 0` repairs square-integrability, at the price of the non-zero
interior residual computed in `boxF_UF`. -/
theorem not_integrable_beamF_zero_lam (ρ s z₁ z₂ : ℝ) :
    ¬ Integrable (fun z₀ : ℝ => ‖beamF ρ 0 s ![z₀, z₁, z₂]‖ ^ 2) volume := by
  intro h
  have hconst : (fun z₀ : ℝ => ‖beamF ρ 0 s ![z₀, z₁, z₂]‖ ^ 2)
      = fun _ : ℝ => ‖A ρ (2 * s) z₁ z₂‖ ^ 2 := by
    funext z₀
    rw [norm_beamF_zero_lam]
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, Matrix.head_cons]
  rw [hconst] at h
  rcases integrable_const_iff.mp h with hc | hfin
  · have hA : ‖A ρ (2 * s) z₁ z₂‖ ≠ 0 := norm_ne_zero_iff.mpr (A_ne_zero ρ (2 * s) z₁ z₂)
    exact hA (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hc)
  · have hlt := measure_lt_top (volume : Measure ℝ) Set.univ
    rw [Real.volume_univ] at hlt
    exact absurd hlt (by simp)

/-- The same failure at the level of `MemLp`. -/
theorem not_memLp_beamF_zero_lam (ρ s z₁ z₂ : ℝ) :
    ¬ MemLp (fun z₀ : ℝ => beamF ρ 0 s ![z₀, z₁, z₂]) 2 volume := by
  intro h
  exact not_integrable_beamF_zero_lam ρ s z₁ z₂
    ((memLp_two_iff_integrable_sq_norm h.aestronglyMeasurable).mp h)


end

end Fermi
end LiuWang2025SemilinearWaveFlatBeam
