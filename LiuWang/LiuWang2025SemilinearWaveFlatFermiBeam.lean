/-
# The 1+3 null-Fermi Gaussian beam, its exact residual, and boundary matching (v0.3)

Building on `LiuWangFermiModel`, this module constructs the beam itself:

* **§7** the longitudinal factor `E(z₀) = exp(i ρ z₀ - ρ λ z₀²/2)`, the beam
  `U(s,z') = E(z₀) · A_ρ(2s, z₁, z₂)`, the **WKB factorisation** `U = a(s) e^{iρ φ(s,z')}`
  with the ρ-independent amplitude `a(s) = c_F(s)⁻¹` and the ρ-independent phase `φ` of
  `LiuWangFermiModel`, and the **exact** interior residual

      `□_F U = - 4 ρ λ z₀ E(z₀) ∂_s A_ρ(2s, z₁, z₂)`,

  obtained by specialising the paraxial identity `4 i ρ ∂_s A - Δ_⊥ A = 0`;
* **§8** the exact modulus of the beam, and the fact that switching the longitudinal
  focusing off (`λ = 0`) gives an exact solution `□_F U = 0` whose modulus is constant in
  `z₀` — the trade-off that forces a non-zero residual in §7;
* **§9** the Cartesian identification of the Fermi beam, the reflected beam obtained by
  `z ↦ -z`, and the **exact phase and amplitude matching on the boundary `{z = 0}`**,
  together with the specular reversal of the normal phase derivative and the exact
  Dirichlet cancellation of the difference `U_in - U_ref`;
* **§10** a negative test: the *sum* `U_in + U_ref` has non-vanishing Dirichlet trace.

**Scope.**  Flat metric throughout.  No stationary phase, no four-beam product, no
coefficient recovery, no Runge approximation.
-/
import LiuWang.LiuWang2025SemilinearWaveFlatFermiModel

namespace LiuWang2025SemilinearWaveFlatBeam
namespace Fermi

noncomputable section

open scoped Matrix

/-! ## §7  The beam and its exact residual -/

/-- The longitudinal factor `E(z₀) = exp(i ρ z₀ - (ρλ/2) z₀²)`.

The first term is the oscillation along the null geodesic; the second is the Gaussian
localisation in the *third* transverse direction `z₀` that the version-0.2 model lacked. -/
def EF (ρ lam z₀ : ℝ) : ℂ :=
  Complex.exp (Complex.I * (ρ : ℂ) * (z₀ : ℂ) - ((ρ * lam / 2 : ℝ) : ℂ) * (z₀ : ℂ) ^ 2)

theorem EF_ne_zero (ρ lam z₀ : ℝ) : EF ρ lam z₀ ≠ 0 := Complex.exp_ne_zero _

/-- `d/dz₀ E = (iρ - ρλ z₀) E`, from the actual derivative. -/
theorem hasDerivAt_EF (ρ lam z₀ : ℝ) :
    HasDerivAt (fun Z : ℝ => EF ρ lam Z)
      ((Complex.I * (ρ : ℂ) - ((ρ * lam * z₀ : ℝ) : ℂ)) * EF ρ lam z₀) z₀ := by
  have hid : HasDerivAt (fun y : ℝ => (y : ℂ)) ((1 : ℝ) : ℂ) z₀ := (hasDerivAt_id z₀).ofReal_comp
  have h1 : HasDerivAt (fun Z : ℝ => Complex.I * (ρ : ℂ) * (Z : ℂ))
      (Complex.I * (ρ : ℂ) * ((1 : ℝ) : ℂ)) z₀ := hid.const_mul _
  have h2 : HasDerivAt (fun Z : ℝ => ((ρ * lam / 2 : ℝ) : ℂ) * (Z : ℂ) ^ 2)
      (((ρ * lam / 2 : ℝ) : ℂ) * (2 * (z₀ : ℂ) ^ 1 * ((1 : ℝ) : ℂ))) z₀ :=
    (hid.pow 2).const_mul _
  have h3 := (h1.fun_sub h2).cexp
  refine h3.congr_deriv ?_
  simp only [EF]
  push_cast
  ring

/-- The **1+3 null-Fermi Gaussian beam**. -/
def UF (ρ lam : ℝ) : ℝ → ℝ → ℝ → ℝ → ℂ :=
  fun s z₀ z₁ z₂ => EF ρ lam z₀ * A ρ (2 * s) z₁ z₂

/-- `d/ds A_ρ(2s, ·)` by the chain rule. -/
theorem hasDerivAt_A_two_s (ρ s z₁ z₂ : ℝ) :
    HasDerivAt (fun S : ℝ => A ρ (2 * S) z₁ z₂) (2 * dsA ρ (2 * s) z₁ z₂) s := by
  have h1 : HasDerivAt (fun S : ℝ => 2 * S) 2 s := by
    simpa using (hasDerivAt_id s).const_mul (2 : ℝ)
  have h2 : HasDerivAt (fun σ : ℝ => A ρ σ z₁ z₂) (dsA ρ (2 * s) z₁ z₂) (2 * s) :=
    hasDerivAt_A_s ρ (2 * s) z₁ z₂
  simpa using h2.scomp s h1

/-- `∂_s U`, in closed form. -/
theorem dS_UF (ρ lam : ℝ) (s z₀ z₁ z₂ : ℝ) :
    dS (UF ρ lam) s z₀ z₁ z₂ = EF ρ lam z₀ * (2 * dsA ρ (2 * s) z₁ z₂) :=
  ((hasDerivAt_A_two_s ρ s z₁ z₂).const_mul (EF ρ lam z₀)).deriv

/-- `∂_{z₀} U`, in closed form. -/
theorem dZ0_UF (ρ lam : ℝ) (s z₀ z₁ z₂ : ℝ) :
    dZ0 (UF ρ lam) s z₀ z₁ z₂ =
      (Complex.I * (ρ : ℂ) - ((ρ * lam * z₀ : ℝ) : ℂ)) * EF ρ lam z₀ * A ρ (2 * s) z₁ z₂ :=
  ((hasDerivAt_EF ρ lam z₀).mul_const (A ρ (2 * s) z₁ z₂)).deriv

/-- `∂_{z₀} ∂_s U`. -/
theorem dZ0_dS_UF (ρ lam : ℝ) (s z₀ z₁ z₂ : ℝ) :
    dZ0 (dS (UF ρ lam)) s z₀ z₁ z₂ =
      (Complex.I * (ρ : ℂ) - ((ρ * lam * z₀ : ℝ) : ℂ)) * EF ρ lam z₀ *
        (2 * dsA ρ (2 * s) z₁ z₂) := by
  have hfun : (fun Z : ℝ => dS (UF ρ lam) s Z z₁ z₂)
      = fun Z : ℝ => EF ρ lam Z * (2 * dsA ρ (2 * s) z₁ z₂) := by
    funext Z; exact dS_UF ρ lam s Z z₁ z₂
  show deriv (fun Z : ℝ => dS (UF ρ lam) s Z z₁ z₂) z₀ = _
  rw [hfun]
  exact ((hasDerivAt_EF ρ lam z₀).mul_const _).deriv

/-- `∂_s ∂_{z₀} U`.  Equal to `∂_{z₀} ∂_s U`, but computed independently: the definition of
`□_F` does not assume symmetry of mixed partials. -/
theorem dS_dZ0_UF (ρ lam : ℝ) (s z₀ z₁ z₂ : ℝ) :
    dS (dZ0 (UF ρ lam)) s z₀ z₁ z₂ =
      (Complex.I * (ρ : ℂ) - ((ρ * lam * z₀ : ℝ) : ℂ)) * EF ρ lam z₀ *
        (2 * dsA ρ (2 * s) z₁ z₂) := by
  have hfun : (fun S : ℝ => dZ0 (UF ρ lam) S z₀ z₁ z₂)
      = fun S : ℝ =>
          (Complex.I * (ρ : ℂ) - ((ρ * lam * z₀ : ℝ) : ℂ)) * EF ρ lam z₀ * A ρ (2 * S) z₁ z₂ := by
    funext S; exact dZ0_UF ρ lam S z₀ z₁ z₂
  show deriv (fun S : ℝ => dZ0 (UF ρ lam) S z₀ z₁ z₂) s = _
  rw [hfun]
  exact ((hasDerivAt_A_two_s ρ s z₁ z₂).const_mul _).deriv

/-- `∂_{z₁} U`. -/
theorem dZ1_UF (ρ lam : ℝ) (s z₀ z₁ z₂ : ℝ) :
    dZ1 (UF ρ lam) s z₀ z₁ z₂ = EF ρ lam z₀ * dx1A ρ (2 * s) z₁ z₂ :=
  ((hasDerivAt_A_x1 ρ (2 * s) z₁ z₂).const_mul (EF ρ lam z₀)).deriv

/-- `∂_{z₁}² U`. -/
theorem dZ1_dZ1_UF (ρ lam : ℝ) (s z₀ z₁ z₂ : ℝ) :
    dZ1 (dZ1 (UF ρ lam)) s z₀ z₁ z₂ = EF ρ lam z₀ * dx1x1A ρ (2 * s) z₁ z₂ := by
  have hfun : (fun X : ℝ => dZ1 (UF ρ lam) s z₀ X z₂)
      = fun X : ℝ => EF ρ lam z₀ * dx1A ρ (2 * s) X z₂ := by
    funext X; exact dZ1_UF ρ lam s z₀ X z₂
  show deriv (fun X : ℝ => dZ1 (UF ρ lam) s z₀ X z₂) z₁ = _
  rw [hfun]
  exact ((hasDerivAt_dx1A ρ (2 * s) z₁ z₂).const_mul _).deriv

/-- `∂_{z₂} U`. -/
theorem dZ2_UF (ρ lam : ℝ) (s z₀ z₁ z₂ : ℝ) :
    dZ2 (UF ρ lam) s z₀ z₁ z₂ = EF ρ lam z₀ * dx2A ρ (2 * s) z₁ z₂ :=
  ((hasDerivAt_A_x2 ρ (2 * s) z₁ z₂).const_mul (EF ρ lam z₀)).deriv

/-- `∂_{z₂}² U`. -/
theorem dZ2_dZ2_UF (ρ lam : ℝ) (s z₀ z₁ z₂ : ℝ) :
    dZ2 (dZ2 (UF ρ lam)) s z₀ z₁ z₂ = EF ρ lam z₀ * dx2x2A ρ (2 * s) z₁ z₂ := by
  have hfun : (fun X : ℝ => dZ2 (UF ρ lam) s z₀ z₁ X)
      = fun X : ℝ => EF ρ lam z₀ * dx2A ρ (2 * s) z₁ X := by
    funext X; exact dZ2_UF ρ lam s z₀ z₁ X
  show deriv (fun X : ℝ => dZ2 (UF ρ lam) s z₀ z₁ X) z₂ = _
  rw [hfun]
  exact ((hasDerivAt_dx2A ρ (2 * s) z₁ z₂).const_mul _).deriv

/-- The **exact interior residual** of the 1+3 Fermi beam. -/
def resF (ρ lam : ℝ) : ℝ → ℝ → ℝ → ℝ → ℂ :=
  fun s z₀ z₁ z₂ =>
    -(4 : ℂ) * ((ρ * lam * z₀ : ℝ) : ℂ) * EF ρ lam z₀ * dsA ρ (2 * s) z₁ z₂

/-- **The exact interior residual.**

`□_F U = -4 ρ λ z₀ E(z₀) ∂_s A_ρ(2s, z₁, z₂)`.

Every term of the paraxial part cancels identically (by `paraxial`); the *entire* residual
is produced by the longitudinal Gaussian factor, and it is exactly proportional to `λ`.
In particular the residual vanishes identically when `λ = 0` or on `{z₀ = 0}`. -/
theorem boxF_UF (ρ lam : ℝ) (s z₀ z₁ z₂ : ℝ) :
    boxF (UF ρ lam) s z₀ z₁ z₂ = resF ρ lam s z₀ z₁ z₂ := by
  rw [boxF_apply, dS_dZ0_UF, dZ0_dS_UF, dZ1_dZ1_UF, dZ2_dZ2_UF]
  have hpar : 4 * Complex.I * (ρ : ℂ) * dsA ρ (2 * s) z₁ z₂
      - (dx1x1A ρ (2 * s) z₁ z₂ + dx2x2A ρ (2 * s) z₁ z₂) = 0 := paraxial ρ (2 * s) z₁ z₂
  simp only [resF]
  push_cast
  linear_combination (EF ρ lam z₀) * hpar

/-- **With `λ = 0` the beam is an exact solution**: `□_F U = 0`.

This is the undamped Fermi beam.  It solves the equation exactly, but §11 shows that its
modulus does not decay in `z₀` at all, so it is not square-integrable over the
three-dimensional transverse space.  That is precisely why `λ > 0` is introduced, at the
cost of the residual of `boxF_UF`. -/
theorem boxF_UF_zero_lam (ρ : ℝ) (s z₀ z₁ z₂ : ℝ) :
    boxF (UF ρ 0) s z₀ z₁ z₂ = 0 := by
  rw [boxF_UF]
  simp [resF]

/-! ### The WKB factorisation: ρ-independent phase and amplitude -/

/-- The **ρ-independent amplitude** `a(s) = c_F(s)⁻¹`. -/
def ampF (s : ℝ) : ℂ := (cF s)⁻¹

theorem norm_ampF (s : ℝ) : ‖ampF s‖ = (Real.sqrt (1 + s ^ 2))⁻¹ := by
  rw [ampF, norm_inv, norm_cF]

theorem norm_ampF_le_one (s : ℝ) : ‖ampF s‖ ≤ 1 := by
  rw [norm_ampF]
  exact inv_le_one_of_one_le₀ (by rw [← norm_cF]; exact one_le_norm_cF s)

/-- The beam evaluated on a three-dimensional transverse vector. -/
def beamF (ρ lam s : ℝ) (z : Fin 3 → ℝ) : ℂ := UF ρ lam s (z 0) (z 1) (z 2)

/-- **The WKB factorisation.**

`U(s, z') = a(s) · exp(i ρ φ(s, z'))` with `a` and `φ` both **independent of `ρ`**.
Consequently every power of `ρ` in the beam is displayed explicitly: `ρ¹` in the phase
exponent, `ρ⁰` in the amplitude. -/
theorem beamF_eq_amp_mul_phase (ρ lam s : ℝ) (z : Fin 3 → ℝ) :
    beamF ρ lam s z = ampF s * Complex.exp (Complex.I * (ρ : ℂ) * phiF lam s z) := by
  have hcs : cs (2 * s) ≠ 0 := cs_ne_zero _
  have hexp : Complex.I * (ρ : ℂ) * phiF lam s z
      = (Complex.I * (ρ : ℂ) * ((z 0 : ℝ) : ℂ) - ((ρ * lam / 2 : ℝ) : ℂ) * ((z 0 : ℝ) : ℂ) ^ 2)
        + gaussArg ρ (2 * s) (z 1) (z 2) := by
    rw [phiF_apply, gaussArg, cF_eq_cs]
    simp only [rsq]
    push_cast
    set c := cs (2 * s) with hcdef
    have hcne : c ≠ 0 := hcs
    field_simp
    linear_combination
      ((ρ : ℂ) * ((z 0 : ℝ) : ℂ) ^ 2 * (lam : ℂ) * c + (ρ : ℂ) * ((z 1 : ℝ) : ℂ) ^ 2
        + (ρ : ℂ) * ((z 2 : ℝ) : ℂ) ^ 2) * Complex.I_mul_I
  rw [beamF, UF, EF, A, ampF, cF_eq_cs, hexp, Complex.exp_add]
  ring

/-! ## §8  The exact modulus and the three-dimensional Gaussian localisation -/

theorem norm_EF (ρ lam z₀ : ℝ) :
    ‖EF ρ lam z₀‖ = Real.exp (-(ρ * lam / 2 * z₀ ^ 2)) := by
  rw [EF, Complex.norm_exp]
  congr 1
  have h1 : (Complex.I * (ρ : ℂ) * (z₀ : ℂ)).re = 0 := by
    simp [Complex.mul_re, Complex.mul_im]
  have h2 : (((ρ * lam / 2 : ℝ) : ℂ) * (z₀ : ℂ) ^ 2).re = ρ * lam / 2 * z₀ ^ 2 := by
    rw [← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]
  rw [Complex.sub_re, h1, h2]
  ring

/-- **The exact modulus of the beam**, expressed through the phase:
`|U(s,z')| = |a(s)| · exp(-ρ Im φ(s,z'))`.

This is the identity that converts the coercivity estimate of `phiF_im_coercive` into a
genuine three-dimensional Gaussian bound. -/
theorem norm_beamF (ρ lam s : ℝ) (z : Fin 3 → ℝ) :
    ‖beamF ρ lam s z‖ = ‖ampF s‖ * Real.exp (-(ρ * (phiF lam s z).im)) := by
  rw [beamF_eq_amp_mul_phase, norm_mul, Complex.norm_exp]
  congr 2
  simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im]
  ring

/-- `Im φ ≤ (max λ 1)/2 · ‖z'‖²`: the upper bound complementing the coercivity estimate. -/
def gamS (lam : ℝ) : ℝ := max lam 1

theorem one_le_gamS (lam : ℝ) : 1 ≤ gamS lam := le_max_right _ _

theorem lam_le_gamS (lam : ℝ) : lam ≤ gamS lam := le_max_left _ _

theorem gamS_pos (lam : ℝ) : 0 < gamS lam := lt_of_lt_of_le one_pos (one_le_gamS lam)

theorem phiF_im_le (lam : ℝ) (s : ℝ) (z : Fin 3 → ℝ) :
    (phiF lam s z).im ≤ gamS lam / 2 * nsq z := by
  have hm : (0 : ℝ) < 1 + s ^ 2 := by positivity
  have h1 : (1 : ℝ) ≤ 1 + s ^ 2 := by nlinarith [sq_nonneg s]
  rw [phiF_im, nsq_apply]
  have hA : lam * z 0 ^ 2 / 2 ≤ gamS lam / 2 * z 0 ^ 2 := by
    nlinarith [sq_nonneg (z 0), lam_le_gamS lam]
  have hB : (z 1 ^ 2 + z 2 ^ 2) / (2 * (1 + s ^ 2)) ≤ gamS lam / 2 * (z 1 ^ 2 + z 2 ^ 2) := by
    have hnn : (0 : ℝ) ≤ z 1 ^ 2 + z 2 ^ 2 := by positivity
    have hstep : (z 1 ^ 2 + z 2 ^ 2) / (2 * (1 + s ^ 2)) ≤ (z 1 ^ 2 + z 2 ^ 2) / 2 := by
      apply div_le_div_of_nonneg_left hnn (by norm_num)
      · linarith
    have hstep2 : (z 1 ^ 2 + z 2 ^ 2) / 2 ≤ gamS lam / 2 * (z 1 ^ 2 + z 2 ^ 2) := by
      nlinarith [one_le_gamS lam]
    linarith
  nlinarith

/-- **The beam is Gaussian-localised in all three transverse directions.**

For `λ > 0`, `ρ ≥ 0` and `|s| ≤ S`,
`|U(s,z')| ≤ exp(-(ρ β(λ,S)/2) ‖z'‖²)` with `β(λ,S) = min(λ, 1/(1+S²)) > 0`.

The concentration scale is therefore `ρ^{-1/2}` in **each** of `z₀, z₁, z₂`. -/
theorem norm_beamF_le {ρ lam : ℝ} (hρ : 0 ≤ ρ) (hlam : 0 < lam) {S s : ℝ} (hs : |s| ≤ S)
    (z : Fin 3 → ℝ) :
    ‖beamF ρ lam s z‖ ≤ Real.exp (-(ρ * betS lam S / 2 * nsq z)) := by
  rw [norm_beamF]
  have hcoer : betS lam S / 2 * nsq z ≤ (phiF lam s z).im := phiF_im_coercive hlam hs z
  have hexp : Real.exp (-(ρ * (phiF lam s z).im)) ≤ Real.exp (-(ρ * betS lam S / 2 * nsq z)) := by
    apply Real.exp_le_exp.mpr
    have : ρ * (betS lam S / 2 * nsq z) ≤ ρ * (phiF lam s z).im :=
      mul_le_mul_of_nonneg_left hcoer hρ
    nlinarith
  calc ‖ampF s‖ * Real.exp (-(ρ * (phiF lam s z).im))
      ≤ 1 * Real.exp (-(ρ * (phiF lam s z).im)) :=
        mul_le_mul_of_nonneg_right (norm_ampF_le_one s) (Real.exp_pos _).le
    _ = Real.exp (-(ρ * (phiF lam s z).im)) := one_mul _
    _ ≤ _ := hexp

/-- The matching lower bound: the beam really does carry mass of the stated order. -/
theorem le_norm_beamF {ρ lam : ℝ} (hρ : 0 ≤ ρ) {S s : ℝ} (hs : |s| ≤ S) (z : Fin 3 → ℝ) :
    (Real.sqrt (mS S))⁻¹ * Real.exp (-(ρ * gamS lam / 2 * nsq z)) ≤ ‖beamF ρ lam s z‖ := by
  have hsq : s ^ 2 ≤ S ^ 2 := by nlinarith [sq_abs s, abs_nonneg s]
  rw [norm_beamF, norm_ampF]
  have hamp : (Real.sqrt (mS S))⁻¹ ≤ (Real.sqrt (1 + s ^ 2))⁻¹ := by
    have hpos : (0 : ℝ) < Real.sqrt (1 + s ^ 2) := Real.sqrt_pos.mpr (by positivity)
    have hle : Real.sqrt (1 + s ^ 2) ≤ Real.sqrt (mS S) :=
      Real.sqrt_le_sqrt (by unfold mS; linarith)
    simpa [one_div] using one_div_le_one_div_of_le hpos hle
  have hexp : Real.exp (-(ρ * gamS lam / 2 * nsq z)) ≤ Real.exp (-(ρ * (phiF lam s z).im)) := by
    apply Real.exp_le_exp.mpr
    have h := phiF_im_le lam s z
    nlinarith [mul_le_mul_of_nonneg_left h hρ]
  exact mul_le_mul hamp hexp (Real.exp_pos _).le (by positivity)

/-! ## §9  Cartesian form, reflection, and exact boundary matching -/

/-- The incident Fermi beam read in Cartesian coordinates `(t, x₁, x₂, z)`. -/
def Uin (ρ lam : ℝ) : ℝ → ℝ → ℝ → ℝ → ℂ :=
  fun t x₁ x₂ z => UF ρ lam ((t + z) / 2) (t - z) x₁ x₂

/-- The reflected beam, obtained from the incident beam by the reflection `z ↦ -z`
across the hyperplane `{z = 0}`. -/
def Uref (ρ lam : ℝ) : ℝ → ℝ → ℝ → ℝ → ℂ :=
  fun t x₁ x₂ z => Uin ρ lam t x₁ x₂ (-z)

/-- The Dirichlet combination `U_in - U_ref` (reflection coefficient `-1`). -/
def Udiff (ρ lam : ℝ) : ℝ → ℝ → ℝ → ℝ → ℂ :=
  fun t x₁ x₂ z => Uin ρ lam t x₁ x₂ z - Uref ρ lam t x₁ x₂ z

/-- The *wrong-sign* combination `U_in + U_ref`, used only as a negative test. -/
def Usum (ρ lam : ℝ) : ℝ → ℝ → ℝ → ℝ → ℂ :=
  fun t x₁ x₂ z => Uin ρ lam t x₁ x₂ z + Uref ρ lam t x₁ x₂ z

theorem Uin_eq_beamF (ρ lam t x₁ x₂ z : ℝ) :
    Uin ρ lam t x₁ x₂ z = beamF ρ lam ((t + z) / 2) ![t - z, x₁, x₂] := by
  simp [Uin, beamF]

/-- **The 1+3 Fermi beam is the version-0.2 beam times a longitudinal Gaussian.** -/
theorem Uin_eq_gauss_mul_Bin (ρ lam t x₁ x₂ z : ℝ) :
    Uin ρ lam t x₁ x₂ z
      = Complex.exp (-(((ρ * lam / 2) * (t - z) ^ 2 : ℝ) : ℂ)) * Bin ρ t x₁ x₂ z := by
  simp only [Uin, UF, EF, Bin]
  rw [show (2 : ℝ) * ((t + z) / 2) = t + z by ring, ← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

theorem Uref_eq_gauss_mul_Bref (ρ lam t x₁ x₂ z : ℝ) :
    Uref ρ lam t x₁ x₂ z
      = Complex.exp (-(((ρ * lam / 2) * (t + z) ^ 2 : ℝ) : ℂ)) * Bref ρ t x₁ x₂ z := by
  rw [Uref, Uin_eq_gauss_mul_Bin, Bin_neg_z, sub_neg_eq_add]

/-! ### The Cartesian phase and amplitude, and their boundary matching -/

/-- The ρ-independent incident phase in Cartesian coordinates. -/
def PhiIn (lam : ℝ) : ℝ → ℝ → ℝ → ℝ → ℂ :=
  fun t x₁ x₂ z => phiF lam ((t + z) / 2) ![t - z, x₁, x₂]

/-- The ρ-independent reflected phase: the incident phase composed with `z ↦ -z`. -/
def PhiRef (lam : ℝ) : ℝ → ℝ → ℝ → ℝ → ℂ :=
  fun t x₁ x₂ z => PhiIn lam t x₁ x₂ (-z)

/-- The ρ-independent incident amplitude. -/
def AmpIn : ℝ → ℝ → ℝ → ℝ → ℂ := fun t _ _ z => ampF ((t + z) / 2)

/-- The ρ-independent reflected amplitude. -/
def AmpRef : ℝ → ℝ → ℝ → ℝ → ℂ := fun t x₁ x₂ z => AmpIn t x₁ x₂ (-z)

/-- The closed form of the Cartesian incident phase. -/
theorem PhiIn_apply (lam t x₁ x₂ z : ℝ) :
    PhiIn lam t x₁ x₂ z = ((t : ℂ) - (z : ℂ))
      + Complex.I * ((lam : ℂ) / 2) * ((t : ℂ) - (z : ℂ)) ^ 2
      + Complex.I * ((rsq x₁ x₂ : ℝ) : ℂ) / (2 * cF ((t + z) / 2)) := by
  have hc : cF ((t + z) / 2) ≠ 0 := cF_ne_zero _
  rw [PhiIn, phiF_apply]
  norm_num [rsq, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, Matrix.head_cons]
  ring

/-- **WKB form of the Cartesian incident beam**: `U_in = a e^{iρΦ_in}` with `a`, `Φ_in`
independent of `ρ`. -/
theorem Uin_wkb (ρ lam t x₁ x₂ z : ℝ) :
    Uin ρ lam t x₁ x₂ z
      = AmpIn t x₁ x₂ z * Complex.exp (Complex.I * (ρ : ℂ) * PhiIn lam t x₁ x₂ z) := by
  rw [Uin_eq_beamF, beamF_eq_amp_mul_phase]
  rfl

/-- **WKB form of the Cartesian reflected beam.** -/
theorem Uref_wkb (ρ lam t x₁ x₂ z : ℝ) :
    Uref ρ lam t x₁ x₂ z
      = AmpRef t x₁ x₂ z * Complex.exp (Complex.I * (ρ : ℂ) * PhiRef lam t x₁ x₂ z) := by
  rw [Uref, Uin_wkb]
  rfl

/-- **Exact phase matching on the boundary `{z = 0}`.** -/
theorem PhiIn_eq_PhiRef_at_z_zero (lam t x₁ x₂ : ℝ) :
    PhiIn lam t x₁ x₂ 0 = PhiRef lam t x₁ x₂ 0 := by
  rw [PhiRef, neg_zero]

/-- **Exact amplitude matching on the boundary `{z = 0}`.** -/
theorem AmpIn_eq_AmpRef_at_z_zero (t x₁ x₂ : ℝ) :
    AmpIn t x₁ x₂ 0 = AmpRef t x₁ x₂ 0 := by
  rw [AmpRef, neg_zero]

/-- The explicit boundary values of the matched phase and amplitude. -/
theorem PhiIn_at_z_zero (lam t x₁ x₂ : ℝ) :
    PhiIn lam t x₁ x₂ 0 = (t : ℂ) + Complex.I * ((lam : ℂ) / 2) * (t : ℂ) ^ 2
      + Complex.I * ((rsq x₁ x₂ : ℝ) : ℂ) / (2 * cF (t / 2)) := by
  rw [PhiIn_apply]
  norm_num

theorem AmpIn_at_z_zero (t x₁ x₂ : ℝ) : AmpIn t x₁ x₂ 0 = ampF (t / 2) := by
  rw [AmpIn]
  norm_num

/-! ### The specular reversal of the normal phase derivative -/

/-- `∂_z Φ_in` in closed form, with every sign retained. -/
theorem hasDerivAt_PhiIn_z (lam t x₁ x₂ z : ℝ) :
    HasDerivAt (fun Z : ℝ => PhiIn lam t x₁ x₂ Z)
      (-1 - Complex.I * (lam : ℂ) * ((t : ℂ) - (z : ℂ))
        - ((rsq x₁ x₂ : ℝ) : ℂ) / (4 * cF ((t + z) / 2) ^ 2)) z := by
  have hcne : cF ((t + z) / 2) ≠ 0 := cF_ne_zero _
  have hid : HasDerivAt (fun Z : ℝ => (Z : ℂ)) ((1 : ℝ) : ℂ) z := (hasDerivAt_id z).ofReal_comp
  -- first summand
  have h1 : HasDerivAt (fun Z : ℝ => (t : ℂ) - (Z : ℂ)) (-((1 : ℝ) : ℂ)) z := hid.const_sub _
  -- second summand
  have h2 : HasDerivAt (fun Z : ℝ => Complex.I * ((lam : ℂ) / 2) * ((t : ℂ) - (Z : ℂ)) ^ 2)
      (Complex.I * ((lam : ℂ) / 2) * (2 * ((t : ℂ) - (z : ℂ)) ^ 1 * (-((1 : ℝ) : ℂ)))) z :=
    (h1.pow 2).const_mul _
  -- the `c_F` factor in the denominator
  have hhalf : HasDerivAt (fun Z : ℝ => (t + Z) / 2) (1 / 2 : ℝ) z :=
    deriv_affine_eq_hasDerivAt t z
  have hcc : HasDerivAt (fun Z : ℝ => (((t + Z) / 2 : ℝ) : ℂ)) (((1 / 2 : ℝ) : ℝ) : ℂ) z :=
    hhalf.ofReal_comp
  have hcf : HasDerivAt (fun Z : ℝ => cF ((t + Z) / 2)) (-(Complex.I / 2)) z := by
    have h2 : HasDerivAt (fun Z : ℝ => (1 : ℂ) - Complex.I * (((t + Z) / 2 : ℝ) : ℂ))
        (-(Complex.I * (((1 / 2 : ℝ) : ℝ) : ℂ))) z := (hcc.const_mul Complex.I).const_sub 1
    exact h2.congr_deriv (by push_cast; ring)
  have hden : HasDerivAt (fun Z : ℝ => 2 * cF ((t + Z) / 2))
      (2 * -(Complex.I / 2)) z := hcf.const_mul 2
  have hdenne : 2 * cF ((t + z) / 2) ≠ 0 := mul_ne_zero two_ne_zero hcne
  have h3 : HasDerivAt
      (fun Z : ℝ => Complex.I * ((rsq x₁ x₂ : ℝ) : ℂ) / (2 * cF ((t + Z) / 2)))
      ((0 * (2 * cF ((t + z) / 2))
          - Complex.I * ((rsq x₁ x₂ : ℝ) : ℂ) * (2 * -(Complex.I / 2)))
        / (2 * cF ((t + z) / 2)) ^ 2) z :=
    (hasDerivAt_const z _).fun_div hden hdenne
  have hsum := (h1.fun_add h2).fun_add h3
  have hfun : (fun Z : ℝ => PhiIn lam t x₁ x₂ Z)
      = fun Z : ℝ => ((t : ℂ) - (Z : ℂ))
          + Complex.I * ((lam : ℂ) / 2) * ((t : ℂ) - (Z : ℂ)) ^ 2
          + Complex.I * ((rsq x₁ x₂ : ℝ) : ℂ) / (2 * cF ((t + Z) / 2)) := by
    funext Z; exact PhiIn_apply lam t x₁ x₂ Z
  rw [hfun]
  refine hsum.congr_deriv ?_
  push_cast
  field_simp
  linear_combination (4 * ((rsq x₁ x₂ : ℝ) : ℂ)) * Complex.I_mul_I

/-- `∂_z Φ_in` at the boundary, with all signs. -/
theorem dZ_PhiIn_at_z_zero (lam t x₁ x₂ : ℝ) :
    deriv (fun Z : ℝ => PhiIn lam t x₁ x₂ Z) 0
      = -1 - Complex.I * (lam : ℂ) * (t : ℂ)
        - ((rsq x₁ x₂ : ℝ) : ℂ) / (4 * cF (t / 2) ^ 2) := by
  have h := (hasDerivAt_PhiIn_z lam t x₁ x₂ 0).deriv
  rw [h]
  norm_num

/-- **Specular reflection of the normal phase derivative.**

`∂_z Φ_ref = -∂_z Φ_in` on the boundary: the tangential derivatives match (by
`PhiIn_eq_PhiRef_at_z_zero`) while the normal derivative reverses sign.  This is the
reflection law at a Dirichlet hyperplane. -/
theorem dZ_PhiRef_eq_neg_dZ_PhiIn (lam t x₁ x₂ : ℝ) :
    deriv (fun Z : ℝ => PhiRef lam t x₁ x₂ Z) 0
      = -deriv (fun Z : ℝ => PhiIn lam t x₁ x₂ Z) 0 := by
  have hfun : (fun Z : ℝ => PhiRef lam t x₁ x₂ Z)
      = fun Z : ℝ => (fun W : ℝ => PhiIn lam t x₁ x₂ W) (-Z) := rfl
  rw [hfun, deriv_comp_neg]
  norm_num

/-- The explicit reflected normal derivative. -/
theorem dZ_PhiRef_at_z_zero (lam t x₁ x₂ : ℝ) :
    deriv (fun Z : ℝ => PhiRef lam t x₁ x₂ Z) 0
      = 1 + Complex.I * (lam : ℂ) * (t : ℂ)
        + ((rsq x₁ x₂ : ℝ) : ℂ) / (4 * cF (t / 2) ^ 2) := by
  rw [dZ_PhiRef_eq_neg_dZ_PhiIn, dZ_PhiIn_at_z_zero]
  ring

/-! ### Exact Dirichlet cancellation, and the negative test -/

/-- **The boundary mismatch of the Dirichlet combination is exactly zero.**

`(U_in - U_ref)(t, x₁, x₂, 0) = 0` for every `t, x₁, x₂, ρ, λ`.  There is no residual
boundary term of any order in `ρ`. -/
theorem Udiff_zero_at_z_zero (ρ lam t x₁ x₂ : ℝ) : Udiff ρ lam t x₁ x₂ 0 = 0 := by
  simp [Udiff, Uref]

/-- The reflection is an exact symmetry: `U_in(-z) = U_ref(z)`. -/
theorem Uin_neg_z (ρ lam t x₁ x₂ z : ℝ) :
    Uin ρ lam t x₁ x₂ (-z) = Uref ρ lam t x₁ x₂ z := rfl

/-- `U_in - U_ref` is odd in `z`. -/
theorem Udiff_odd_in_z (ρ lam t x₁ x₂ z : ℝ) :
    Udiff ρ lam t x₁ x₂ (-z) = -Udiff ρ lam t x₁ x₂ z := by
  simp only [Udiff, Uref, neg_neg]
  ring

/-- **Negative test.**  The *sum* convention with reflection coefficient `+1` does **not**
satisfy the Dirichlet condition: its boundary trace is `2 U_in|_{z=0}`, which is non-zero
whenever `ρ > 0` — indeed for every `ρ`, since the beam never vanishes. -/
theorem Usum_at_z_zero (ρ lam t x₁ x₂ : ℝ) :
    Usum ρ lam t x₁ x₂ 0 = 2 * Uin ρ lam t x₁ x₂ 0 := by
  simp only [Usum, Uref, neg_zero]
  ring

theorem Uin_ne_zero (ρ lam t x₁ x₂ z : ℝ) : Uin ρ lam t x₁ x₂ z ≠ 0 := by
  rw [Uin, UF]
  refine mul_ne_zero (EF_ne_zero _ _ _) ?_
  rw [A]
  exact mul_ne_zero (inv_ne_zero (cs_ne_zero _)) (Complex.exp_ne_zero _)

/-- **The wrong-sign packet has non-vanishing Dirichlet trace.** -/
theorem Usum_ne_zero_at_z_zero (ρ lam t x₁ x₂ : ℝ) : Usum ρ lam t x₁ x₂ 0 ≠ 0 := by
  rw [Usum_at_z_zero]
  exact mul_ne_zero two_ne_zero (Uin_ne_zero ρ lam t x₁ x₂ 0)

end

end Fermi
end LiuWang2025SemilinearWaveFlatBeam
