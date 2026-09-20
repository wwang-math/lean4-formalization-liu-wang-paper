/-
# The reflected Gaussian beam for the flat `1+3` dimensional wave equation

Coordinates `(t, x₁, x₂, z)`, transverse radius `r² = x₁² + x₂²`, null coordinates
`u = t - z`, `v = t + z`.  With `Aρ` from `LiuWangFlatGaussianBeam` we set

  `Bin  = e^{iρu} Aρ(v, x₁, x₂)`,
  `Bref = e^{iρv} Aρ(u, x₁, x₂)`,
  `B    = Bin - Bref`.

The d'Alembertian `□ = ∂_t² - ∂_{x₁}² - ∂_{x₂}² - ∂_z²` is *defined* by iterating the
honest one-variable `deriv` in each slot, so `□B = 0` is a statement about actual
derivatives, not a postulate.

Main results.

* `dAlembert_beam`       : the exact `□` of a general null-factorised beam
                           `e^{iρ(t+σz)} Aρ(t+τz)`, for arbitrary real `σ, τ`;
* `dAlembert_Bin`, `dAlembert_Bref`, `dAlembert_B` : `□ = 0`;
* `B_zero_at_z_zero`     : `B(t,x₁,x₂,0) = 0` exactly;
* `dZ_B_at_z_zero`       : the exact normal-derivative formula at `z = 0`,
                           `∂_z B|_{z=0} = 2 e^{iρt} (∂_s Aρ(t) - iρ Aρ(t))`, all signs kept;
* `B_odd_in_z`           : `B` is odd under `z ↦ -z`, i.e. under the swap `u ↔ v`;
* `dAlembert_mul`        : the product-rule cutoff identity with the commutator terms
                           exposed, and `dAlembert_cutoff_B` its specialisation to `B`.
-/
import LiuWang.LiuWang2025SemilinearWaveFlatGaussianBeam

namespace LiuWang2025SemilinearWaveFlatBeam

noncomputable section

/-! ## Partial derivatives and the d'Alembertian -/

/-- `∂_t` acting on functions of `(t, x₁, x₂, z)`. -/
def dT (F : ℝ → ℝ → ℝ → ℝ → ℂ) : ℝ → ℝ → ℝ → ℝ → ℂ :=
  fun t x₁ x₂ z => deriv (fun T : ℝ => F T x₁ x₂ z) t

/-- `∂_{x₁}`. -/
def dX1 (F : ℝ → ℝ → ℝ → ℝ → ℂ) : ℝ → ℝ → ℝ → ℝ → ℂ :=
  fun t x₁ x₂ z => deriv (fun X : ℝ => F t X x₂ z) x₁

/-- `∂_{x₂}`. -/
def dX2 (F : ℝ → ℝ → ℝ → ℝ → ℂ) : ℝ → ℝ → ℝ → ℝ → ℂ :=
  fun t x₁ x₂ z => deriv (fun X : ℝ => F t x₁ X z) x₂

/-- `∂_z`. -/
def dZ (F : ℝ → ℝ → ℝ → ℝ → ℂ) : ℝ → ℝ → ℝ → ℝ → ℂ :=
  fun t x₁ x₂ z => deriv (fun Z : ℝ => F t x₁ x₂ Z) z

/-- The flat d'Alembertian `□ = ∂_t² - ∂_{x₁}² - ∂_{x₂}² - ∂_z²`. -/
def dAlembert (F : ℝ → ℝ → ℝ → ℝ → ℂ) : ℝ → ℝ → ℝ → ℝ → ℂ :=
  fun t x₁ x₂ z =>
    dT (dT F) t x₁ x₂ z - dX1 (dX1 F) t x₁ x₂ z - dX2 (dX2 F) t x₁ x₂ z - dZ (dZ F) t x₁ x₂ z

/-! ## The phase factor -/

/-- The oscillatory factor `e^{iρ(t+σz)}`.  `σ = -1` gives `e^{iρu}`, `σ = 1` gives `e^{iρv}`. -/
def ph (ρ σ t z : ℝ) : ℂ := Complex.exp (Complex.I * ((ρ * (t + σ * z) : ℝ) : ℂ))

theorem ph_ne_zero (ρ σ t z : ℝ) : ph ρ σ t z ≠ 0 := Complex.exp_ne_zero _

theorem hasDerivAt_ph_t (ρ σ t z : ℝ) :
    HasDerivAt (fun T : ℝ => ph ρ σ T z) (ph ρ σ t z * (Complex.I * (ρ : ℂ))) t := by
  have hr : HasDerivAt (fun T : ℝ => ρ * (T + σ * z)) (ρ * 1) t :=
    ((hasDerivAt_id t).add_const (σ * z)).const_mul ρ
  refine ((hr.ofReal_comp.const_mul Complex.I).cexp).congr_deriv ?_
  simp only [ph]
  push_cast
  ring

theorem hasDerivAt_ph_z (ρ σ t z : ℝ) :
    HasDerivAt (fun Z : ℝ => ph ρ σ t Z) (ph ρ σ t z * (Complex.I * (ρ : ℂ) * (σ : ℂ))) z := by
  have hr : HasDerivAt (fun Z : ℝ => ρ * (t + σ * Z)) (ρ * (σ * 1)) z :=
    (((hasDerivAt_id z).const_mul σ).const_add t).const_mul ρ
  refine ((hr.ofReal_comp.const_mul Complex.I).cexp).congr_deriv ?_
  simp only [ph]
  push_cast
  ring

/-! ## The general null-factorised beam -/

/-- The general beam `e^{iρ(t+σz)} Aρ(t+τz, x₁, x₂)`. -/
def beam (ρ σ τ : ℝ) : ℝ → ℝ → ℝ → ℝ → ℂ :=
  fun t x₁ x₂ z => ph ρ σ t z * A ρ (t + τ * z) x₁ x₂

/-- `∂_t` of `beam`. -/
def dTbeam (ρ σ τ : ℝ) : ℝ → ℝ → ℝ → ℝ → ℂ :=
  fun t x₁ x₂ z => ph ρ σ t z *
    (Complex.I * (ρ : ℂ) * A ρ (t + τ * z) x₁ x₂ + dsA ρ (t + τ * z) x₁ x₂)

/-- `∂_t²` of `beam`. -/
def dTTbeam (ρ σ τ : ℝ) : ℝ → ℝ → ℝ → ℝ → ℂ :=
  fun t x₁ x₂ z => ph ρ σ t z *
    (-(ρ : ℂ) ^ 2 * A ρ (t + τ * z) x₁ x₂
      + 2 * Complex.I * (ρ : ℂ) * dsA ρ (t + τ * z) x₁ x₂
      + d2sA ρ (t + τ * z) x₁ x₂)

/-- `∂_z` of `beam`. -/
def dZbeam (ρ σ τ : ℝ) : ℝ → ℝ → ℝ → ℝ → ℂ :=
  fun t x₁ x₂ z => ph ρ σ t z *
    (Complex.I * (ρ : ℂ) * (σ : ℂ) * A ρ (t + τ * z) x₁ x₂
      + (τ : ℂ) * dsA ρ (t + τ * z) x₁ x₂)

/-- `∂_z²` of `beam`. -/
def dZZbeam (ρ σ τ : ℝ) : ℝ → ℝ → ℝ → ℝ → ℂ :=
  fun t x₁ x₂ z => ph ρ σ t z *
    (-(σ : ℂ) ^ 2 * (ρ : ℂ) ^ 2 * A ρ (t + τ * z) x₁ x₂
      + 2 * Complex.I * (ρ : ℂ) * (σ : ℂ) * (τ : ℂ) * dsA ρ (t + τ * z) x₁ x₂
      + (τ : ℂ) ^ 2 * d2sA ρ (t + τ * z) x₁ x₂)

/-- `∂_{x₁}` of `beam`. -/
def dX1beam (ρ σ τ : ℝ) : ℝ → ℝ → ℝ → ℝ → ℂ :=
  fun t x₁ x₂ z => ph ρ σ t z * dx1A ρ (t + τ * z) x₁ x₂

/-- `∂_{x₁}²` of `beam`. -/
def dX1X1beam (ρ σ τ : ℝ) : ℝ → ℝ → ℝ → ℝ → ℂ :=
  fun t x₁ x₂ z => ph ρ σ t z * dx1x1A ρ (t + τ * z) x₁ x₂

/-- `∂_{x₂}` of `beam`. -/
def dX2beam (ρ σ τ : ℝ) : ℝ → ℝ → ℝ → ℝ → ℂ :=
  fun t x₁ x₂ z => ph ρ σ t z * dx2A ρ (t + τ * z) x₁ x₂

/-- `∂_{x₂}²` of `beam`. -/
def dX2X2beam (ρ σ τ : ℝ) : ℝ → ℝ → ℝ → ℝ → ℂ :=
  fun t x₁ x₂ z => ph ρ σ t z * dx2x2A ρ (t + τ * z) x₁ x₂

/-! ### First and second slice derivatives of `beam` -/

/-- Derivative of the affine shift `Y ↦ a + b Y`. -/
theorem hasDerivAt_affine (a b y : ℝ) : HasDerivAt (fun Y : ℝ => a + b * Y) b y := by
  simpa using ((hasDerivAt_id y).const_mul b).const_add a

theorem hasDerivAt_A_shift_t (ρ τ t z x₁ x₂ : ℝ) :
    HasDerivAt (fun T : ℝ => A ρ (T + τ * z) x₁ x₂) (dsA ρ (t + τ * z) x₁ x₂) t := by
  have h1 : HasDerivAt (fun T : ℝ => T + τ * z) 1 t := by
    simpa using (hasDerivAt_id t).add_const (τ * z)
  simpa using (hasDerivAt_A_s ρ (t + τ * z) x₁ x₂).scomp t h1

theorem hasDerivAt_dsA_shift_t (ρ τ t z x₁ x₂ : ℝ) :
    HasDerivAt (fun T : ℝ => dsA ρ (T + τ * z) x₁ x₂) (d2sA ρ (t + τ * z) x₁ x₂) t := by
  have h1 : HasDerivAt (fun T : ℝ => T + τ * z) 1 t := by
    simpa using (hasDerivAt_id t).add_const (τ * z)
  simpa using (hasDerivAt_dsA ρ (t + τ * z) x₁ x₂).scomp t h1

theorem hasDerivAt_A_shift_z (ρ τ t z x₁ x₂ : ℝ) :
    HasDerivAt (fun Z : ℝ => A ρ (t + τ * Z) x₁ x₂) ((τ : ℂ) * dsA ρ (t + τ * z) x₁ x₂) z := by
  simpa [Complex.real_smul] using
    (hasDerivAt_A_s ρ (t + τ * z) x₁ x₂).scomp z (hasDerivAt_affine t τ z)

theorem hasDerivAt_dsA_shift_z (ρ τ t z x₁ x₂ : ℝ) :
    HasDerivAt (fun Z : ℝ => dsA ρ (t + τ * Z) x₁ x₂) ((τ : ℂ) * d2sA ρ (t + τ * z) x₁ x₂) z := by
  simpa [Complex.real_smul] using
    (hasDerivAt_dsA ρ (t + τ * z) x₁ x₂).scomp z (hasDerivAt_affine t τ z)

theorem hasDerivAt_beam_t (ρ σ τ t x₁ x₂ z : ℝ) :
    HasDerivAt (fun T : ℝ => beam ρ σ τ T x₁ x₂ z) (dTbeam ρ σ τ t x₁ x₂ z) t := by
  refine ((hasDerivAt_ph_t ρ σ t z).fun_mul (hasDerivAt_A_shift_t ρ τ t z x₁ x₂)).congr_deriv ?_
  simp only [dTbeam]
  ring

theorem hasDerivAt_dTbeam_t (ρ σ τ t x₁ x₂ z : ℝ) :
    HasDerivAt (fun T : ℝ => dTbeam ρ σ τ T x₁ x₂ z) (dTTbeam ρ σ τ t x₁ x₂ z) t := by
  have h := (hasDerivAt_ph_t ρ σ t z).fun_mul
    ((((hasDerivAt_A_shift_t ρ τ t z x₁ x₂).const_mul (Complex.I * (ρ : ℂ))).fun_add
      (hasDerivAt_dsA_shift_t ρ τ t z x₁ x₂)))
  refine h.congr_deriv ?_
  simp only [dTTbeam]
  linear_combination (ph ρ σ t z * (ρ : ℂ) ^ 2 * A ρ (t + τ * z) x₁ x₂) * Complex.I_mul_I

theorem hasDerivAt_beam_z (ρ σ τ t x₁ x₂ z : ℝ) :
    HasDerivAt (fun Z : ℝ => beam ρ σ τ t x₁ x₂ Z) (dZbeam ρ σ τ t x₁ x₂ z) z := by
  refine ((hasDerivAt_ph_z ρ σ t z).fun_mul (hasDerivAt_A_shift_z ρ τ t z x₁ x₂)).congr_deriv ?_
  simp only [dZbeam]
  ring

theorem hasDerivAt_dZbeam_z (ρ σ τ t x₁ x₂ z : ℝ) :
    HasDerivAt (fun Z : ℝ => dZbeam ρ σ τ t x₁ x₂ Z) (dZZbeam ρ σ τ t x₁ x₂ z) z := by
  have h := (hasDerivAt_ph_z ρ σ t z).fun_mul
    ((((hasDerivAt_A_shift_z ρ τ t z x₁ x₂).const_mul (Complex.I * (ρ : ℂ) * (σ : ℂ))).fun_add
      ((hasDerivAt_dsA_shift_z ρ τ t z x₁ x₂).const_mul (τ : ℂ))))
  refine h.congr_deriv ?_
  simp only [dZZbeam]
  linear_combination
    (ph ρ σ t z * (σ : ℂ) ^ 2 * (ρ : ℂ) ^ 2 * A ρ (t + τ * z) x₁ x₂) * Complex.I_mul_I

theorem hasDerivAt_beam_x1 (ρ σ τ t x₁ x₂ z : ℝ) :
    HasDerivAt (fun X : ℝ => beam ρ σ τ t X x₂ z) (dX1beam ρ σ τ t x₁ x₂ z) x₁ :=
  (hasDerivAt_A_x1 ρ (t + τ * z) x₁ x₂).const_mul (ph ρ σ t z)

theorem hasDerivAt_dX1beam_x1 (ρ σ τ t x₁ x₂ z : ℝ) :
    HasDerivAt (fun X : ℝ => dX1beam ρ σ τ t X x₂ z) (dX1X1beam ρ σ τ t x₁ x₂ z) x₁ :=
  (hasDerivAt_dx1A ρ (t + τ * z) x₁ x₂).const_mul (ph ρ σ t z)

theorem hasDerivAt_beam_x2 (ρ σ τ t x₁ x₂ z : ℝ) :
    HasDerivAt (fun X : ℝ => beam ρ σ τ t x₁ X z) (dX2beam ρ σ τ t x₁ x₂ z) x₂ :=
  (hasDerivAt_A_x2 ρ (t + τ * z) x₁ x₂).const_mul (ph ρ σ t z)

theorem hasDerivAt_dX2beam_x2 (ρ σ τ t x₁ x₂ z : ℝ) :
    HasDerivAt (fun X : ℝ => dX2beam ρ σ τ t x₁ X z) (dX2X2beam ρ σ τ t x₁ x₂ z) x₂ :=
  (hasDerivAt_dx2A ρ (t + τ * z) x₁ x₂).const_mul (ph ρ σ t z)

/-! ### `□` of the general beam -/

theorem dT_beam (ρ σ τ : ℝ) : dT (beam ρ σ τ) = dTbeam ρ σ τ := by
  funext t x₁ x₂ z; exact (hasDerivAt_beam_t ρ σ τ t x₁ x₂ z).deriv

theorem dTT_beam (ρ σ τ : ℝ) : dT (dT (beam ρ σ τ)) = dTTbeam ρ σ τ := by
  rw [dT_beam]
  funext t x₁ x₂ z; exact (hasDerivAt_dTbeam_t ρ σ τ t x₁ x₂ z).deriv

theorem dZ_beam (ρ σ τ : ℝ) : dZ (beam ρ σ τ) = dZbeam ρ σ τ := by
  funext t x₁ x₂ z; exact (hasDerivAt_beam_z ρ σ τ t x₁ x₂ z).deriv

theorem dZZ_beam (ρ σ τ : ℝ) : dZ (dZ (beam ρ σ τ)) = dZZbeam ρ σ τ := by
  rw [dZ_beam]
  funext t x₁ x₂ z; exact (hasDerivAt_dZbeam_z ρ σ τ t x₁ x₂ z).deriv

theorem dX1_beam (ρ σ τ : ℝ) : dX1 (beam ρ σ τ) = dX1beam ρ σ τ := by
  funext t x₁ x₂ z; exact (hasDerivAt_beam_x1 ρ σ τ t x₁ x₂ z).deriv

theorem dX1X1_beam (ρ σ τ : ℝ) : dX1 (dX1 (beam ρ σ τ)) = dX1X1beam ρ σ τ := by
  rw [dX1_beam]
  funext t x₁ x₂ z; exact (hasDerivAt_dX1beam_x1 ρ σ τ t x₁ x₂ z).deriv

theorem dX2_beam (ρ σ τ : ℝ) : dX2 (beam ρ σ τ) = dX2beam ρ σ τ := by
  funext t x₁ x₂ z; exact (hasDerivAt_beam_x2 ρ σ τ t x₁ x₂ z).deriv

theorem dX2X2_beam (ρ σ τ : ℝ) : dX2 (dX2 (beam ρ σ τ)) = dX2X2beam ρ σ τ := by
  rw [dX2_beam]
  funext t x₁ x₂ z; exact (hasDerivAt_dX2beam_x2 ρ σ τ t x₁ x₂ z).deriv

/-- **The exact `□` of a general null-factorised beam.**  Note the three structural
coefficients: `σ² - 1`, `1 - στ` and `1 - τ²`.  The genuine null factorisation is
`σ² = τ² = 1` with `στ = -1`, and only then does the paraxial equation close the identity. -/
theorem dAlembert_beam (ρ σ τ : ℝ) :
    dAlembert (beam ρ σ τ) = fun t x₁ x₂ z => ph ρ σ t z *
      (((σ : ℂ) ^ 2 - 1) * (ρ : ℂ) ^ 2 * A ρ (t + τ * z) x₁ x₂
        + 2 * Complex.I * (ρ : ℂ) * (1 - (σ : ℂ) * (τ : ℂ)) * dsA ρ (t + τ * z) x₁ x₂
        + (1 - (τ : ℂ) ^ 2) * d2sA ρ (t + τ * z) x₁ x₂
        - lapA ρ (t + τ * z) x₁ x₂) := by
  funext t x₁ x₂ z
  simp only [dAlembert]
  rw [dTT_beam, dX1X1_beam, dX2X2_beam, dZZ_beam]
  simp only [dTTbeam, dX1X1beam, dX2X2beam, dZZbeam, lapA]
  ring

/-- **`□` vanishes on a genuinely null-factorised beam.** -/
theorem dAlembert_beam_null (ρ σ τ : ℝ) (hσ : σ ^ 2 = 1) (hτ : τ ^ 2 = 1) (hστ : σ * τ = -1) :
    dAlembert (beam ρ σ τ) = fun _ _ _ _ => (0 : ℂ) := by
  have hσc : (σ : ℂ) ^ 2 = 1 := by
    have h : ((σ ^ 2 : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := by rw [hσ]
    push_cast at h; exact h
  have hτc : (τ : ℂ) ^ 2 = 1 := by
    have h : ((τ ^ 2 : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := by rw [hτ]
    push_cast at h; exact h
  have hστc : (σ : ℂ) * (τ : ℂ) = -1 := by
    have h : ((σ * τ : ℝ) : ℂ) = ((-1 : ℝ) : ℂ) := by rw [hστ]
    push_cast at h; exact h
  rw [dAlembert_beam]
  funext t x₁ x₂ z
  rw [hσc, hτc, hστc]
  linear_combination (ph ρ σ t z) * paraxial ρ (t + τ * z) x₁ x₂

/-! ## Differences of beams -/

/-- The difference of two null-factorised beams. -/
def beamSub (ρ σ₁ τ₁ σ₂ τ₂ : ℝ) : ℝ → ℝ → ℝ → ℝ → ℂ :=
  fun t x₁ x₂ z => beam ρ σ₁ τ₁ t x₁ x₂ z - beam ρ σ₂ τ₂ t x₁ x₂ z

theorem dT_beamSub (ρ σ₁ τ₁ σ₂ τ₂ : ℝ) :
    dT (beamSub ρ σ₁ τ₁ σ₂ τ₂)
      = fun t x₁ x₂ z => dTbeam ρ σ₁ τ₁ t x₁ x₂ z - dTbeam ρ σ₂ τ₂ t x₁ x₂ z := by
  funext t x₁ x₂ z
  exact ((hasDerivAt_beam_t ρ σ₁ τ₁ t x₁ x₂ z).sub (hasDerivAt_beam_t ρ σ₂ τ₂ t x₁ x₂ z)).deriv

theorem dTT_beamSub (ρ σ₁ τ₁ σ₂ τ₂ : ℝ) :
    dT (dT (beamSub ρ σ₁ τ₁ σ₂ τ₂))
      = fun t x₁ x₂ z => dTTbeam ρ σ₁ τ₁ t x₁ x₂ z - dTTbeam ρ σ₂ τ₂ t x₁ x₂ z := by
  rw [dT_beamSub]
  funext t x₁ x₂ z
  exact ((hasDerivAt_dTbeam_t ρ σ₁ τ₁ t x₁ x₂ z).sub
    (hasDerivAt_dTbeam_t ρ σ₂ τ₂ t x₁ x₂ z)).deriv

theorem dZ_beamSub (ρ σ₁ τ₁ σ₂ τ₂ : ℝ) :
    dZ (beamSub ρ σ₁ τ₁ σ₂ τ₂)
      = fun t x₁ x₂ z => dZbeam ρ σ₁ τ₁ t x₁ x₂ z - dZbeam ρ σ₂ τ₂ t x₁ x₂ z := by
  funext t x₁ x₂ z
  exact ((hasDerivAt_beam_z ρ σ₁ τ₁ t x₁ x₂ z).sub (hasDerivAt_beam_z ρ σ₂ τ₂ t x₁ x₂ z)).deriv

theorem dZZ_beamSub (ρ σ₁ τ₁ σ₂ τ₂ : ℝ) :
    dZ (dZ (beamSub ρ σ₁ τ₁ σ₂ τ₂))
      = fun t x₁ x₂ z => dZZbeam ρ σ₁ τ₁ t x₁ x₂ z - dZZbeam ρ σ₂ τ₂ t x₁ x₂ z := by
  rw [dZ_beamSub]
  funext t x₁ x₂ z
  exact ((hasDerivAt_dZbeam_z ρ σ₁ τ₁ t x₁ x₂ z).sub
    (hasDerivAt_dZbeam_z ρ σ₂ τ₂ t x₁ x₂ z)).deriv

theorem dX1_beamSub (ρ σ₁ τ₁ σ₂ τ₂ : ℝ) :
    dX1 (beamSub ρ σ₁ τ₁ σ₂ τ₂)
      = fun t x₁ x₂ z => dX1beam ρ σ₁ τ₁ t x₁ x₂ z - dX1beam ρ σ₂ τ₂ t x₁ x₂ z := by
  funext t x₁ x₂ z
  exact ((hasDerivAt_beam_x1 ρ σ₁ τ₁ t x₁ x₂ z).sub (hasDerivAt_beam_x1 ρ σ₂ τ₂ t x₁ x₂ z)).deriv

theorem dX1X1_beamSub (ρ σ₁ τ₁ σ₂ τ₂ : ℝ) :
    dX1 (dX1 (beamSub ρ σ₁ τ₁ σ₂ τ₂))
      = fun t x₁ x₂ z => dX1X1beam ρ σ₁ τ₁ t x₁ x₂ z - dX1X1beam ρ σ₂ τ₂ t x₁ x₂ z := by
  rw [dX1_beamSub]
  funext t x₁ x₂ z
  exact ((hasDerivAt_dX1beam_x1 ρ σ₁ τ₁ t x₁ x₂ z).sub
    (hasDerivAt_dX1beam_x1 ρ σ₂ τ₂ t x₁ x₂ z)).deriv

theorem dX2_beamSub (ρ σ₁ τ₁ σ₂ τ₂ : ℝ) :
    dX2 (beamSub ρ σ₁ τ₁ σ₂ τ₂)
      = fun t x₁ x₂ z => dX2beam ρ σ₁ τ₁ t x₁ x₂ z - dX2beam ρ σ₂ τ₂ t x₁ x₂ z := by
  funext t x₁ x₂ z
  exact ((hasDerivAt_beam_x2 ρ σ₁ τ₁ t x₁ x₂ z).sub (hasDerivAt_beam_x2 ρ σ₂ τ₂ t x₁ x₂ z)).deriv

theorem dX2X2_beamSub (ρ σ₁ τ₁ σ₂ τ₂ : ℝ) :
    dX2 (dX2 (beamSub ρ σ₁ τ₁ σ₂ τ₂))
      = fun t x₁ x₂ z => dX2X2beam ρ σ₁ τ₁ t x₁ x₂ z - dX2X2beam ρ σ₂ τ₂ t x₁ x₂ z := by
  rw [dX2_beamSub]
  funext t x₁ x₂ z
  exact ((hasDerivAt_dX2beam_x2 ρ σ₁ τ₁ t x₁ x₂ z).sub
    (hasDerivAt_dX2beam_x2 ρ σ₂ τ₂ t x₁ x₂ z)).deriv

/-- `□` is additive on differences of beams (proved, not assumed). -/
theorem dAlembert_beamSub (ρ σ₁ τ₁ σ₂ τ₂ : ℝ) :
    dAlembert (beamSub ρ σ₁ τ₁ σ₂ τ₂)
      = fun t x₁ x₂ z =>
          dAlembert (beam ρ σ₁ τ₁) t x₁ x₂ z - dAlembert (beam ρ σ₂ τ₂) t x₁ x₂ z := by
  funext t x₁ x₂ z
  simp only [dAlembert, dTT_beamSub, dX1X1_beamSub, dX2X2_beamSub, dZZ_beamSub,
    dTT_beam, dX1X1_beam, dX2X2_beam, dZZ_beam]
  ring

/-! ## The incoming, reflected and total beams -/

/-- The incoming beam `Bin = e^{iρu} Aρ(v, x₁, x₂)`, `u = t - z`, `v = t + z`. -/
def Bin (ρ : ℝ) : ℝ → ℝ → ℝ → ℝ → ℂ :=
  fun t x₁ x₂ z => Complex.exp (Complex.I * ((ρ * (t - z) : ℝ) : ℂ)) * A ρ (t + z) x₁ x₂

/-- The reflected beam `Bref = e^{iρv} Aρ(u, x₁, x₂)`. -/
def Bref (ρ : ℝ) : ℝ → ℝ → ℝ → ℝ → ℂ :=
  fun t x₁ x₂ z => Complex.exp (Complex.I * ((ρ * (t + z) : ℝ) : ℂ)) * A ρ (t - z) x₁ x₂

/-- The total reflected beam packet `B = Bin - Bref`. -/
def B (ρ : ℝ) : ℝ → ℝ → ℝ → ℝ → ℂ :=
  fun t x₁ x₂ z => Bin ρ t x₁ x₂ z - Bref ρ t x₁ x₂ z

theorem Bin_eq_beam (ρ : ℝ) : Bin ρ = beam ρ (-1) 1 := by
  funext t x₁ x₂ z
  simp only [Bin, beam, ph]
  rw [show t + (-1 : ℝ) * z = t - z from by ring, show t + (1 : ℝ) * z = t + z from by ring]

theorem Bref_eq_beam (ρ : ℝ) : Bref ρ = beam ρ 1 (-1) := by
  funext t x₁ x₂ z
  simp only [Bref, beam, ph]
  rw [show t + (-1 : ℝ) * z = t - z from by ring, show t + (1 : ℝ) * z = t + z from by ring]

theorem B_eq_beamSub (ρ : ℝ) : B ρ = beamSub ρ (-1) 1 1 (-1) := by
  funext t x₁ x₂ z
  simp only [B, beamSub, Bin_eq_beam, Bref_eq_beam]

/-! ### `□ Bin = □ Bref = □ B = 0` -/

theorem dAlembert_Bin (ρ : ℝ) : dAlembert (Bin ρ) = fun _ _ _ _ => (0 : ℂ) := by
  rw [Bin_eq_beam]
  exact dAlembert_beam_null ρ (-1) 1 (by norm_num) (by norm_num) (by norm_num)

theorem dAlembert_Bref (ρ : ℝ) : dAlembert (Bref ρ) = fun _ _ _ _ => (0 : ℂ) := by
  rw [Bref_eq_beam]
  exact dAlembert_beam_null ρ 1 (-1) (by norm_num) (by norm_num) (by norm_num)

/-- **The reflected beam packet solves the flat wave equation.** -/
theorem dAlembert_B (ρ : ℝ) : dAlembert (B ρ) = fun _ _ _ _ => (0 : ℂ) := by
  rw [B_eq_beamSub, dAlembert_beamSub,
    dAlembert_beam_null ρ (-1) 1 (by norm_num) (by norm_num) (by norm_num),
    dAlembert_beam_null ρ 1 (-1) (by norm_num) (by norm_num) (by norm_num)]
  funext t x₁ x₂ z
  simp

theorem dZ_B (ρ : ℝ) :
    dZ (B ρ) = fun t x₁ x₂ z => dZbeam ρ (-1) 1 t x₁ x₂ z - dZbeam ρ 1 (-1) t x₁ x₂ z := by
  rw [B_eq_beamSub, dZ_beamSub]

/-! ## Boundary behaviour at `z = 0` -/

/-- **`B` vanishes identically on the reflecting hyperplane `z = 0`.** -/
theorem B_zero_at_z_zero (ρ t x₁ x₂ : ℝ) : B ρ t x₁ x₂ 0 = 0 := by
  simp only [B, Bin, Bref]
  rw [show t - (0 : ℝ) = t from by ring, show t + (0 : ℝ) = t from by ring]
  ring

/-- Under `z ↦ -z` the incoming beam becomes the reflected beam. -/
theorem Bin_neg_z (ρ t x₁ x₂ z : ℝ) : Bin ρ t x₁ x₂ (-z) = Bref ρ t x₁ x₂ z := by
  simp only [Bin, Bref]
  rw [show t - -z = t + z from by ring, show t + -z = t - z from by ring]

/-- **`B` is odd under `z ↦ -z`**, i.e. under the swap of the null coordinates `u ↔ v`.
This is the structural reason for the exact Dirichlet condition above. -/
theorem B_odd_in_z (ρ t x₁ x₂ z : ℝ) : B ρ t x₁ x₂ (-z) = -B ρ t x₁ x₂ z := by
  simp only [B, Bin, Bref]
  rw [show t - -z = t + z from by ring, show t + -z = t - z from by ring]
  ring

/-- **The exact `z`-coordinate derivative on `{z = 0}`,** with every sign retained:
`∂_z B|_{z=0} = 2 e^{iρt} (∂_s Aρ(t,x₁,x₂) - i ρ Aρ(t,x₁,x₂))`.

This is a derivative in the `z` *coordinate direction*.  It is **not** by itself an
outward-normal derivative: `∂_z` carries no orientation, and the outward normal of a
half-space `{z > 0}` and of `{z < 0}` differ by a sign.  For the genuinely oriented
statement see `dNuOmega_B` (upper half-space) and `dNuOmegaLower_B` (lower half-space)
below. -/
theorem dZ_B_at_z_zero (ρ t x₁ x₂ : ℝ) :
    dZ (B ρ) t x₁ x₂ 0
      = 2 * Complex.exp (Complex.I * ((ρ * t : ℝ) : ℂ)) *
          (dsA ρ t x₁ x₂ - Complex.I * (ρ : ℂ) * A ρ t x₁ x₂) := by
  rw [dZ_B]
  simp only [dZbeam, ph]
  push_cast
  ring_nf

/-- The fully explicit form of the `z`-coordinate derivative, with `∂_s Aρ` written out.
As with `dZ_B_at_z_zero`, this is a coordinate derivative, not an oriented normal
derivative. -/
theorem dZ_B_at_z_zero_explicit (ρ t x₁ x₂ : ℝ) :
    dZ (B ρ) t x₁ x₂ 0
      = 2 * Complex.exp (Complex.I * ((ρ * t : ℝ) : ℂ)) *
          Complex.exp (gaussArg ρ t x₁ x₂) *
          ((2 * Complex.I * cs t - Complex.I * ((ρ * rsq x₁ x₂ : ℝ) : ℂ)) / (4 * cs t ^ 3)
            - Complex.I * (ρ : ℂ) / cs t) := by
  rw [dZ_B_at_z_zero]
  simp only [dsA, A]
  have hc := cs_ne_zero t
  field_simp

/-! ## The flat half-space and its outward-normal derivative

`dZ_B_at_z_zero` above is a derivative in the `z` coordinate direction and carries no
orientation.  To speak of an *outward*-normal derivative one must first fix a side of the
reflecting hyperplane.  We fix the upper half-space, verify that it is open with frontier
exactly `{z = 0}`, verify that `ν = (0,0,-1)` really points out of it, and then compute
`∂_ν = ν ⬝ ∇` on the boundary. -/

/-- The flat spatial half-space `Ω = {(x₁,x₂,z) : z > 0}`, whose boundary is the reflecting
hyperplane `{z = 0}`. -/
def Omega : Set (ℝ × ℝ × ℝ) := {p | 0 < p.2.2}

/-- The lower half-space `Ω' = {(x₁,x₂,z) : z < 0}`, the other side of the same hyperplane. -/
def OmegaLower : Set (ℝ × ℝ × ℝ) := {p | p.2.2 < 0}

theorem continuous_zcoord : Continuous fun p : ℝ × ℝ × ℝ => p.2.2 :=
  continuous_snd.snd

theorem isOpenMap_zcoord : IsOpenMap fun p : ℝ × ℝ × ℝ => p.2.2 :=
  isOpenMap_snd.comp isOpenMap_snd

theorem isOpen_Omega : IsOpen Omega :=
  isOpen_Ioi.preimage continuous_zcoord

/-- The frontier of `Ω` is exactly the reflecting hyperplane `{z = 0}`. -/
theorem frontier_Omega : frontier Omega = {p : ℝ × ℝ × ℝ | p.2.2 = 0} := by
  have h := isOpenMap_zcoord.preimage_frontier_eq_frontier_preimage continuous_zcoord
    (Set.Ioi (0 : ℝ))
  rw [frontier_Ioi] at h
  exact h.symm

/-- Boundary points of `Ω` are exactly the points with `z = 0`. -/
theorem mem_frontier_Omega_iff (p : ℝ × ℝ × ℝ) : p ∈ frontier Omega ↔ p.2.2 = 0 := by
  rw [frontier_Omega]; rfl

/-- The outward unit normal of `Ω = {z > 0}` along `∂Ω = {z = 0}`. -/
def nu : ℝ × ℝ × ℝ := (0, 0, -1)

theorem norm_nu : ‖nu‖ = 1 := by
  simp [nu, Prod.norm_def]

/-- **`ν` really points out of `Ω`.**  From a boundary point, moving along `ν` leaves `Ω`,
and moving against `ν` enters `Ω`.  This is what makes `ν`, rather than `-ν`, the *outward*
normal of the upper half-space. -/
theorem nu_outward (x₁ x₂ ε : ℝ) (hε : 0 < ε) :
    ((x₁, x₂, (0 : ℝ)) + ε • nu) ∉ Omega ∧ ((x₁, x₂, (0 : ℝ)) - ε • nu) ∈ Omega := by
  have h1 : ((x₁, x₂, (0 : ℝ)) + ε • nu).2.2 = -ε := by simp [nu]
  have h2 : ((x₁, x₂, (0 : ℝ)) - ε • nu).2.2 = ε := by simp [nu]
  refine ⟨?_, ?_⟩
  · simp only [Omega, Set.mem_setOf_eq, h1, not_lt]
    linarith
  · simp only [Omega, Set.mem_setOf_eq, h2]
    exact hε

/-- For the *lower* half-space the outward normal is `-ν = (0,0,1)`. -/
theorem neg_nu_outward_lower (x₁ x₂ ε : ℝ) (hε : 0 < ε) :
    ((x₁, x₂, (0 : ℝ)) - ε • nu) ∉ OmegaLower ∧ ((x₁, x₂, (0 : ℝ)) + ε • nu) ∈ OmegaLower := by
  have h1 : ((x₁, x₂, (0 : ℝ)) - ε • nu).2.2 = ε := by simp [nu]
  have h2 : ((x₁, x₂, (0 : ℝ)) + ε • nu).2.2 = -ε := by simp [nu]
  refine ⟨?_, ?_⟩
  · simp only [OmegaLower, Set.mem_setOf_eq, h1, not_lt]
    linarith
  · simp only [OmegaLower, Set.mem_setOf_eq, h2]
    linarith

/-- The outward-normal derivative on `∂Ω = {z = 0}` for the **upper** half-space
`Ω = {z > 0}`, written literally as `ν ⬝ ∇`. -/
def dNuOmega (F : ℝ → ℝ → ℝ → ℝ → ℂ) : ℝ → ℝ → ℝ → ℂ :=
  fun t x₁ x₂ =>
    ((nu.1 : ℝ) : ℂ) * dX1 F t x₁ x₂ 0
      + ((nu.2.1 : ℝ) : ℂ) * dX2 F t x₁ x₂ 0
      + ((nu.2.2 : ℝ) : ℂ) * dZ F t x₁ x₂ 0

/-- The outward-normal derivative for the **lower** half-space `Ω' = {z < 0}`, whose outward
normal is `-ν`. -/
def dNuOmegaLower (F : ℝ → ℝ → ℝ → ℝ → ℂ) : ℝ → ℝ → ℝ → ℂ :=
  fun t x₁ x₂ => -dNuOmega F t x₁ x₂

/-- Because `ν = (0,0,-1)`, the outward-normal derivative for `Ω = {z > 0}` is `-∂_z`. -/
theorem dNuOmega_eq (F : ℝ → ℝ → ℝ → ℝ → ℂ) (t x₁ x₂ : ℝ) :
    dNuOmega F t x₁ x₂ = -(dZ F t x₁ x₂ 0) := by
  simp [dNuOmega, nu]

/-- **The outward-normal derivative of the packet on `∂Ω`, upper half-space.**
For `Ω = {z > 0}` the outward normal is `ν = (0,0,-1)`, so
`∂_ν B|_{z=0} = -2 e^{iρt} (∂_s Aρ(t,x) - iρ Aρ(t,x))`. -/
theorem dNuOmega_B (ρ t x₁ x₂ : ℝ) :
    dNuOmega (B ρ) t x₁ x₂
      = -(2 * Complex.exp (Complex.I * ((ρ * t : ℝ) : ℂ)) *
            (dsA ρ t x₁ x₂ - Complex.I * (ρ : ℂ) * A ρ t x₁ x₂)) := by
  rw [dNuOmega_eq, dZ_B_at_z_zero]

/-- **The outward-normal derivative of the packet on `∂Ω'`, lower half-space.**
The two half-spaces give opposite signs; this is exactly the orientation content that a
bare `∂_z` statement omits. -/
theorem dNuOmegaLower_B (ρ t x₁ x₂ : ℝ) :
    dNuOmegaLower (B ρ) t x₁ x₂
      = 2 * Complex.exp (Complex.I * ((ρ * t : ℝ) : ℂ)) *
          (dsA ρ t x₁ x₂ - Complex.I * (ρ : ℂ) * A ρ t x₁ x₂) := by
  rw [dNuOmegaLower, dNuOmega_B, neg_neg]

/-- The two outward-normal derivatives differ by a sign. -/
theorem dNuOmega_add_dNuOmegaLower (F : ℝ → ℝ → ℝ → ℝ → ℂ) (t x₁ x₂ : ℝ) :
    dNuOmega F t x₁ x₂ + dNuOmegaLower F t x₁ x₂ = 0 := by
  simp [dNuOmegaLower]

/-! ## The cutoff (product-rule) identity for `□` -/

/-- Slice-wise `C²` regularity: each coordinate slice is differentiable and so is its
derivative.  This is exactly what the product rule for `□` needs. -/
structure SliceC2 (F : ℝ → ℝ → ℝ → ℝ → ℂ) : Prop where
  ht : ∀ x₁ x₂ z, Differentiable ℝ (fun T : ℝ => F T x₁ x₂ z)
  ht' : ∀ x₁ x₂ z, Differentiable ℝ (deriv fun T : ℝ => F T x₁ x₂ z)
  hx1 : ∀ t x₂ z, Differentiable ℝ (fun X : ℝ => F t X x₂ z)
  hx1' : ∀ t x₂ z, Differentiable ℝ (deriv fun X : ℝ => F t X x₂ z)
  hx2 : ∀ t x₁ z, Differentiable ℝ (fun X : ℝ => F t x₁ X z)
  hx2' : ∀ t x₁ z, Differentiable ℝ (deriv fun X : ℝ => F t x₁ X z)
  hz : ∀ t x₁ x₂, Differentiable ℝ (fun Z : ℝ => F t x₁ x₂ Z)
  hz' : ∀ t x₁ x₂, Differentiable ℝ (deriv fun Z : ℝ => F t x₁ x₂ Z)

/-- The one-variable second-order product rule, from `HasDerivAt`. -/
theorem deriv2_mul {f g : ℝ → ℂ} (hf : Differentiable ℝ f) (hf' : Differentiable ℝ (deriv f))
    (hg : Differentiable ℝ g) (hg' : Differentiable ℝ (deriv g)) (x : ℝ) :
    deriv (deriv fun y : ℝ => f y * g y) x
      = deriv (deriv f) x * g x + 2 * (deriv f x * deriv g x) + f x * deriv (deriv g) x := by
  have h1 : (deriv fun y : ℝ => f y * g y) = fun y : ℝ => deriv f y * g y + f y * deriv g y := by
    funext y
    exact ((hf y).hasDerivAt.fun_mul (hg y).hasDerivAt).deriv
  rw [h1]
  have h2 : HasDerivAt (fun y : ℝ => deriv f y * g y + f y * deriv g y)
      (deriv (deriv f) x * g x + deriv f x * deriv g x
        + (deriv f x * deriv g x + f x * deriv (deriv g) x)) x :=
    (((hf' x).hasDerivAt).fun_mul ((hg x).hasDerivAt)).add
      (((hf x).hasDerivAt).fun_mul ((hg' x).hasDerivAt))
  rw [h2.deriv]
  ring

/-- The Minkowski-signature cutoff commutator `⟨dχ, dF⟩`:
`∂_tχ ∂_tF - ∂_{x₁}χ ∂_{x₁}F - ∂_{x₂}χ ∂_{x₂}F - ∂_zχ ∂_zF`. -/
def cutoffBracket (χ F : ℝ → ℝ → ℝ → ℝ → ℂ) : ℝ → ℝ → ℝ → ℝ → ℂ :=
  fun t x₁ x₂ z =>
    dT χ t x₁ x₂ z * dT F t x₁ x₂ z
      - dX1 χ t x₁ x₂ z * dX1 F t x₁ x₂ z
      - dX2 χ t x₁ x₂ z * dX2 F t x₁ x₂ z
      - dZ χ t x₁ x₂ z * dZ F t x₁ x₂ z

/-- **The product-rule cutoff identity**, with the two commutator contributions explicit:
`□(χF) = (□χ)F + χ(□F) + 2⟨dχ, dF⟩`. -/
theorem dAlembert_mul (χ F : ℝ → ℝ → ℝ → ℝ → ℂ) (hχ : SliceC2 χ) (hF : SliceC2 F) :
    dAlembert (fun t x₁ x₂ z => χ t x₁ x₂ z * F t x₁ x₂ z)
      = fun t x₁ x₂ z =>
          dAlembert χ t x₁ x₂ z * F t x₁ x₂ z
            + χ t x₁ x₂ z * dAlembert F t x₁ x₂ z
            + 2 * cutoffBracket χ F t x₁ x₂ z := by
  funext t x₁ x₂ z
  have e1 : deriv (deriv fun T : ℝ => χ T x₁ x₂ z * F T x₁ x₂ z) t
      = deriv (deriv fun T : ℝ => χ T x₁ x₂ z) t * F t x₁ x₂ z
        + 2 * (deriv (fun T : ℝ => χ T x₁ x₂ z) t * deriv (fun T : ℝ => F T x₁ x₂ z) t)
        + χ t x₁ x₂ z * deriv (deriv fun T : ℝ => F T x₁ x₂ z) t :=
    deriv2_mul (hχ.ht x₁ x₂ z) (hχ.ht' x₁ x₂ z) (hF.ht x₁ x₂ z) (hF.ht' x₁ x₂ z) t
  have e2 : deriv (deriv fun X : ℝ => χ t X x₂ z * F t X x₂ z) x₁
      = deriv (deriv fun X : ℝ => χ t X x₂ z) x₁ * F t x₁ x₂ z
        + 2 * (deriv (fun X : ℝ => χ t X x₂ z) x₁ * deriv (fun X : ℝ => F t X x₂ z) x₁)
        + χ t x₁ x₂ z * deriv (deriv fun X : ℝ => F t X x₂ z) x₁ :=
    deriv2_mul (hχ.hx1 t x₂ z) (hχ.hx1' t x₂ z) (hF.hx1 t x₂ z) (hF.hx1' t x₂ z) x₁
  have e3 : deriv (deriv fun X : ℝ => χ t x₁ X z * F t x₁ X z) x₂
      = deriv (deriv fun X : ℝ => χ t x₁ X z) x₂ * F t x₁ x₂ z
        + 2 * (deriv (fun X : ℝ => χ t x₁ X z) x₂ * deriv (fun X : ℝ => F t x₁ X z) x₂)
        + χ t x₁ x₂ z * deriv (deriv fun X : ℝ => F t x₁ X z) x₂ :=
    deriv2_mul (hχ.hx2 t x₁ z) (hχ.hx2' t x₁ z) (hF.hx2 t x₁ z) (hF.hx2' t x₁ z) x₂
  have e4 : deriv (deriv fun Z : ℝ => χ t x₁ x₂ Z * F t x₁ x₂ Z) z
      = deriv (deriv fun Z : ℝ => χ t x₁ x₂ Z) z * F t x₁ x₂ z
        + 2 * (deriv (fun Z : ℝ => χ t x₁ x₂ Z) z * deriv (fun Z : ℝ => F t x₁ x₂ Z) z)
        + χ t x₁ x₂ z * deriv (deriv fun Z : ℝ => F t x₁ x₂ Z) z :=
    deriv2_mul (hχ.hz t x₁ x₂) (hχ.hz' t x₁ x₂) (hF.hz t x₁ x₂) (hF.hz' t x₁ x₂) z
  simp only [dAlembert, dT, dX1, dX2, dZ, cutoffBracket]
  rw [e1, e2, e3, e4]
  ring

/-! ### `B` satisfies the regularity hypothesis -/

theorem sliceC2_beam (ρ σ τ : ℝ) : SliceC2 (beam ρ σ τ) where
  ht x₁ x₂ z := fun t => (hasDerivAt_beam_t ρ σ τ t x₁ x₂ z).differentiableAt
  ht' x₁ x₂ z := by
    have e : (deriv fun T : ℝ => beam ρ σ τ T x₁ x₂ z) = fun T : ℝ => dTbeam ρ σ τ T x₁ x₂ z := by
      funext T; exact (hasDerivAt_beam_t ρ σ τ T x₁ x₂ z).deriv
    rw [e]
    exact fun t => (hasDerivAt_dTbeam_t ρ σ τ t x₁ x₂ z).differentiableAt
  hx1 t x₂ z := fun x₁ => (hasDerivAt_beam_x1 ρ σ τ t x₁ x₂ z).differentiableAt
  hx1' t x₂ z := by
    have e : (deriv fun X : ℝ => beam ρ σ τ t X x₂ z) = fun X : ℝ => dX1beam ρ σ τ t X x₂ z := by
      funext X; exact (hasDerivAt_beam_x1 ρ σ τ t X x₂ z).deriv
    rw [e]
    exact fun x₁ => (hasDerivAt_dX1beam_x1 ρ σ τ t x₁ x₂ z).differentiableAt
  hx2 t x₁ z := fun x₂ => (hasDerivAt_beam_x2 ρ σ τ t x₁ x₂ z).differentiableAt
  hx2' t x₁ z := by
    have e : (deriv fun X : ℝ => beam ρ σ τ t x₁ X z) = fun X : ℝ => dX2beam ρ σ τ t x₁ X z := by
      funext X; exact (hasDerivAt_beam_x2 ρ σ τ t x₁ X z).deriv
    rw [e]
    exact fun x₂ => (hasDerivAt_dX2beam_x2 ρ σ τ t x₁ x₂ z).differentiableAt
  hz t x₁ x₂ := fun z => (hasDerivAt_beam_z ρ σ τ t x₁ x₂ z).differentiableAt
  hz' t x₁ x₂ := by
    have e : (deriv fun Z : ℝ => beam ρ σ τ t x₁ x₂ Z) = fun Z : ℝ => dZbeam ρ σ τ t x₁ x₂ Z := by
      funext Z; exact (hasDerivAt_beam_z ρ σ τ t x₁ x₂ Z).deriv
    rw [e]
    exact fun z => (hasDerivAt_dZbeam_z ρ σ τ t x₁ x₂ z).differentiableAt

theorem SliceC2.sub {F G : ℝ → ℝ → ℝ → ℝ → ℂ} (hF : SliceC2 F) (hG : SliceC2 G) :
    SliceC2 (fun t x₁ x₂ z => F t x₁ x₂ z - G t x₁ x₂ z) where
  ht x₁ x₂ z := (hF.ht x₁ x₂ z).sub (hG.ht x₁ x₂ z)
  ht' x₁ x₂ z := by
    have e : (deriv fun T : ℝ => F T x₁ x₂ z - G T x₁ x₂ z)
        = fun T : ℝ => deriv (fun T' : ℝ => F T' x₁ x₂ z) T
            - deriv (fun T' : ℝ => G T' x₁ x₂ z) T := by
      funext T; exact deriv_fun_sub (hF.ht x₁ x₂ z T) (hG.ht x₁ x₂ z T)
    rw [e]
    exact (hF.ht' x₁ x₂ z).sub (hG.ht' x₁ x₂ z)
  hx1 t x₂ z := (hF.hx1 t x₂ z).sub (hG.hx1 t x₂ z)
  hx1' t x₂ z := by
    have e : (deriv fun X : ℝ => F t X x₂ z - G t X x₂ z)
        = fun X : ℝ => deriv (fun X' : ℝ => F t X' x₂ z) X
            - deriv (fun X' : ℝ => G t X' x₂ z) X := by
      funext X; exact deriv_fun_sub (hF.hx1 t x₂ z X) (hG.hx1 t x₂ z X)
    rw [e]
    exact (hF.hx1' t x₂ z).sub (hG.hx1' t x₂ z)
  hx2 t x₁ z := (hF.hx2 t x₁ z).sub (hG.hx2 t x₁ z)
  hx2' t x₁ z := by
    have e : (deriv fun X : ℝ => F t x₁ X z - G t x₁ X z)
        = fun X : ℝ => deriv (fun X' : ℝ => F t x₁ X' z) X
            - deriv (fun X' : ℝ => G t x₁ X' z) X := by
      funext X; exact deriv_fun_sub (hF.hx2 t x₁ z X) (hG.hx2 t x₁ z X)
    rw [e]
    exact (hF.hx2' t x₁ z).sub (hG.hx2' t x₁ z)
  hz t x₁ x₂ := (hF.hz t x₁ x₂).sub (hG.hz t x₁ x₂)
  hz' t x₁ x₂ := by
    have e : (deriv fun Z : ℝ => F t x₁ x₂ Z - G t x₁ x₂ Z)
        = fun Z : ℝ => deriv (fun Z' : ℝ => F t x₁ x₂ Z') Z
            - deriv (fun Z' : ℝ => G t x₁ x₂ Z') Z := by
      funext Z; exact deriv_fun_sub (hF.hz t x₁ x₂ Z) (hG.hz t x₁ x₂ Z)
    rw [e]
    exact (hF.hz' t x₁ x₂).sub (hG.hz' t x₁ x₂)

theorem sliceC2_B (ρ : ℝ) : SliceC2 (B ρ) := by
  rw [B_eq_beamSub]
  exact (sliceC2_beam ρ (-1) 1).sub (sliceC2_beam ρ 1 (-1))

/-- **The cutoff identity for the reflected beam.**  Because `□B = 0`, only the cutoff
commutator terms survive:
`□(χ B) = (□χ) B + 2 (∂_tχ ∂_tB - ∂_{x₁}χ ∂_{x₁}B - ∂_{x₂}χ ∂_{x₂}B - ∂_zχ ∂_zB)`. -/
theorem dAlembert_cutoff_B (ρ : ℝ) (χ : ℝ → ℝ → ℝ → ℝ → ℂ) (hχ : SliceC2 χ) :
    dAlembert (fun t x₁ x₂ z => χ t x₁ x₂ z * B ρ t x₁ x₂ z)
      = fun t x₁ x₂ z =>
          dAlembert χ t x₁ x₂ z * B ρ t x₁ x₂ z + 2 * cutoffBracket χ (B ρ) t x₁ x₂ z := by
  rw [dAlembert_mul χ (B ρ) hχ (sliceC2_B ρ)]
  funext t x₁ x₂ z
  rw [show dAlembert (B ρ) t x₁ x₂ z = 0 from
    congrFun (congrFun (congrFun (congrFun (dAlembert_B ρ) t) x₁) x₂) z]
  ring

end

end LiuWang2025SemilinearWaveFlatBeam
