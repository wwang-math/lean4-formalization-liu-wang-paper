/-
# A flat 1+3-dimensional null-Fermi Gaussian-beam model  (packet version 0.3)

This module upgrades the two-transverse calibration of versions 0.1/0.2 to a genuine
**three-dimensional** transverse model, by introducing null Fermi coordinates along the
null geodesic

  `γ(s) = (t, x₁, x₂, z) = (s, 0, 0, s)`

of flat `1+3` Minkowski space and a **complex symmetric quadratic phase matrix** `H(s)`
acting on the three coordinates transverse to `γ` inside the coordinate chart.

Contents.

* **§1** the Fermi chart `(s, z₀, z₁, z₂) = ((t+z)/2, t-z, x₁, x₂)` and its inverse;
* **§2** the Jacobian `K` of the chart, *proved* to consist of the actual partial
  derivatives of the chart maps, and the **derivation of the Fermi metric coefficients**
  `ĝ = K g K^T` for `g = diag(1,-1,-1,-1)`;
* **§3** the Fermi partial derivatives, the Fermi wave operator `□_F = ĝ^{ab} ∂_a ∂_b`
  *defined by the derived coefficients*, and the matching statement that the Cartesian
  `dAlembert` of version 0.1 is `g^{ab} ∂_a ∂_b`;
* **§4** the amplitude factor `c_F(s) = 1 - i s`, the phase matrix
  `H(s) = diag(i λ, i/c_F(s), i/c_F(s))`, its symmetry, and the **Riccati system**
  `H' = H P H`, `P = diag(0,1,1)`, verified from actual derivatives;
* **§5** the quadratic phase `φ(s,z') = z₀ + ½ z'ᵀ H(s) z'`, its exact imaginary part,
  and the **uniform coercivity estimate** `Im φ(s,z') ≥ c ‖z'‖²` on `|s| ≤ S` for `λ > 0`;
* **§6** the **negative regression theorem**: the version 0.2 two-transverse phase
  `phaseIn` is *exactly* `φ` with `λ = 0`, and no such phase admits any coercivity
  constant, because it does not control the omitted third direction `z₀`.

**Scope.**  Everything here is flat.  The metric coefficients derived in §2 are the flat
Minkowski coefficients written in a null Fermi chart; no curvature, no connection
coefficients, and no curved-manifold statement appears or is claimed.  The Riccati system
of §4 is the flat one.  Nothing in this packet verifies a curved Lorentzian
`reflectedGaussianBeamConstruction`.
-/
import LiuWang.LiuWang2025SemilinearWaveFlatReflectedBeam
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Symmetric

namespace LiuWang2025SemilinearWaveFlatBeam
namespace Fermi

noncomputable section

open scoped Matrix

/-! ## §1  The null Fermi chart -/

/-- The Fermi chart `(t, x₁, x₂, z) ↦ (s, z₀, z₁, z₂) = ((t+z)/2, t-z, x₁, x₂)`.

The null geodesic `γ(s) = (s,0,0,s)` is exactly `{z₀ = z₁ = z₂ = 0}`, parameterised by `s`. -/
def toFermi (t x₁ x₂ z : ℝ) : Fin 4 → ℝ := ![(t + z) / 2, t - z, x₁, x₂]

/-- The inverse chart `(s, z₀, z₁, z₂) ↦ (t, x₁, x₂, z) = (s + z₀/2, z₁, z₂, s - z₀/2)`. -/
def ofFermi (s z₀ z₁ z₂ : ℝ) : Fin 4 → ℝ := ![s + z₀ / 2, z₁, z₂, s - z₀ / 2]

theorem ofFermi_toFermi (t x₁ x₂ z : ℝ) :
    ofFermi ((t + z) / 2) (t - z) x₁ x₂ = ![t, x₁, x₂, z] := by
  funext i
  fin_cases i <;> simp [ofFermi] <;> ring

theorem toFermi_ofFermi (s z₀ z₁ z₂ : ℝ) :
    toFermi (s + z₀ / 2) z₁ z₂ (s - z₀ / 2) = ![s, z₀, z₁, z₂] := by
  funext i
  fin_cases i <;> simp [toFermi]

/-- The null geodesic `γ(s) = (s, 0, 0, s)` is the axis `z' = 0` of the chart. -/
theorem toFermi_on_geodesic (s : ℝ) : toFermi s 0 0 s = ![s, 0, 0, 0] := by
  funext i
  fin_cases i <;> simp [toFermi]

/-- `γ` is a null curve: `(dt/ds)² - (dz/ds)² = 0` with `dt/ds = dz/ds = 1`. -/
theorem geodesic_is_null : (1 : ℝ) ^ 2 - (0 : ℝ) ^ 2 - (0 : ℝ) ^ 2 - (1 : ℝ) ^ 2 = 0 := by
  norm_num

/-! ## §2  The Jacobian and the derived Fermi metric coefficients -/

/-- The `s` coordinate of the Fermi chart, as a function of the Cartesian coordinates. -/
def sCoord (t _x₁ _x₂ z : ℝ) : ℝ := (t + z) / 2

/-- The `z₀` coordinate of the Fermi chart. -/
def z0Coord (t _x₁ _x₂ z : ℝ) : ℝ := t - z

/-- The `z₁` coordinate of the Fermi chart. -/
def z1Coord (_t x₁ _x₂ _z : ℝ) : ℝ := x₁

/-- The `z₂` coordinate of the Fermi chart. -/
def z2Coord (_t _x₁ x₂ _z : ℝ) : ℝ := x₂

theorem sCoord_apply (t x₁ x₂ z : ℝ) : sCoord t x₁ x₂ z = (t + z) / 2 := rfl
theorem z0Coord_apply (t x₁ x₂ z : ℝ) : z0Coord t x₁ x₂ z = t - z := rfl
theorem z1Coord_apply (t x₁ x₂ z : ℝ) : z1Coord t x₁ x₂ z = x₁ := rfl
theorem z2Coord_apply (t x₁ x₂ z : ℝ) : z2Coord t x₁ x₂ z = x₂ := rfl

theorem toFermi_eq_coords (t x₁ x₂ z : ℝ) :
    toFermi t x₁ x₂ z
      = ![sCoord t x₁ x₂ z, z0Coord t x₁ x₂ z, z1Coord t x₁ x₂ z, z2Coord t x₁ x₂ z] := rfl

/-- `∂_t` for real-valued functions of the Cartesian coordinates. -/
def dRT (F : ℝ → ℝ → ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ → ℝ → ℝ :=
  fun t x₁ x₂ z => deriv (fun T : ℝ => F T x₁ x₂ z) t

/-- `∂_{x₁}` for real-valued functions. -/
def dRX1 (F : ℝ → ℝ → ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ → ℝ → ℝ :=
  fun t x₁ x₂ z => deriv (fun X : ℝ => F t X x₂ z) x₁

/-- `∂_{x₂}` for real-valued functions. -/
def dRX2 (F : ℝ → ℝ → ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ → ℝ → ℝ :=
  fun t x₁ x₂ z => deriv (fun X : ℝ => F t x₁ X z) x₂

/-- `∂_z` for real-valued functions. -/
def dRZ (F : ℝ → ℝ → ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ → ℝ → ℝ :=
  fun t x₁ x₂ z => deriv (fun Z : ℝ => F t x₁ x₂ Z) z

/-- Derivative of an affine real function, in the exact shape needed below. -/
theorem deriv_affine_eq {f : ℝ → ℝ} (a b : ℝ) (hf : ∀ y, f y = a + b * y) (y : ℝ) :
    deriv f y = b := by
  have hfe : f = fun Y : ℝ => a + b * Y := funext hf
  rw [hfe, (hasDerivAt_affine a b y).deriv]

/-! ### The sixteen partial derivatives of the four chart maps -/

theorem dRT_sCoord (t x₁ x₂ z : ℝ) : dRT sCoord t x₁ x₂ z = 1 / 2 :=
  deriv_affine_eq (z / 2) (1 / 2) (fun Y => by rw [sCoord_apply]; ring) t
theorem dRX1_sCoord (t x₁ x₂ z : ℝ) : dRX1 sCoord t x₁ x₂ z = 0 :=
  deriv_affine_eq ((t + z) / 2) 0 (fun Y => by rw [sCoord_apply]; ring) x₁
theorem dRX2_sCoord (t x₁ x₂ z : ℝ) : dRX2 sCoord t x₁ x₂ z = 0 :=
  deriv_affine_eq ((t + z) / 2) 0 (fun Y => by rw [sCoord_apply]; ring) x₂
theorem dRZ_sCoord (t x₁ x₂ z : ℝ) : dRZ sCoord t x₁ x₂ z = 1 / 2 :=
  deriv_affine_eq (t / 2) (1 / 2) (fun Y => by rw [sCoord_apply]; ring) z

theorem dRT_z0Coord (t x₁ x₂ z : ℝ) : dRT z0Coord t x₁ x₂ z = 1 :=
  deriv_affine_eq (-z) 1 (fun Y => by rw [z0Coord_apply]; ring) t
theorem dRX1_z0Coord (t x₁ x₂ z : ℝ) : dRX1 z0Coord t x₁ x₂ z = 0 :=
  deriv_affine_eq (t - z) 0 (fun Y => by rw [z0Coord_apply]; ring) x₁
theorem dRX2_z0Coord (t x₁ x₂ z : ℝ) : dRX2 z0Coord t x₁ x₂ z = 0 :=
  deriv_affine_eq (t - z) 0 (fun Y => by rw [z0Coord_apply]; ring) x₂
theorem dRZ_z0Coord (t x₁ x₂ z : ℝ) : dRZ z0Coord t x₁ x₂ z = -1 :=
  deriv_affine_eq t (-1) (fun Y => by rw [z0Coord_apply]; ring) z

theorem dRT_z1Coord (t x₁ x₂ z : ℝ) : dRT z1Coord t x₁ x₂ z = 0 :=
  deriv_affine_eq x₁ 0 (fun Y => by rw [z1Coord_apply]; ring) t
theorem dRX1_z1Coord (t x₁ x₂ z : ℝ) : dRX1 z1Coord t x₁ x₂ z = 1 :=
  deriv_affine_eq 0 1 (fun Y => by rw [z1Coord_apply]; ring) x₁
theorem dRX2_z1Coord (t x₁ x₂ z : ℝ) : dRX2 z1Coord t x₁ x₂ z = 0 :=
  deriv_affine_eq x₁ 0 (fun Y => by rw [z1Coord_apply]; ring) x₂
theorem dRZ_z1Coord (t x₁ x₂ z : ℝ) : dRZ z1Coord t x₁ x₂ z = 0 :=
  deriv_affine_eq x₁ 0 (fun Y => by rw [z1Coord_apply]; ring) z

theorem dRT_z2Coord (t x₁ x₂ z : ℝ) : dRT z2Coord t x₁ x₂ z = 0 :=
  deriv_affine_eq x₂ 0 (fun Y => by rw [z2Coord_apply]; ring) t
theorem dRX1_z2Coord (t x₁ x₂ z : ℝ) : dRX1 z2Coord t x₁ x₂ z = 0 :=
  deriv_affine_eq x₂ 0 (fun Y => by rw [z2Coord_apply]; ring) x₁
theorem dRX2_z2Coord (t x₁ x₂ z : ℝ) : dRX2 z2Coord t x₁ x₂ z = 1 :=
  deriv_affine_eq 0 1 (fun Y => by rw [z2Coord_apply]; ring) x₂
theorem dRZ_z2Coord (t x₁ x₂ z : ℝ) : dRZ z2Coord t x₁ x₂ z = 0 :=
  deriv_affine_eq x₂ 0 (fun Y => by rw [z2Coord_apply]; ring) z

/-- `Z ↦ (t + Z)/2` has derivative `1/2` — the `HasDerivAt` form of `dRZ_sCoord`. -/
theorem deriv_affine_eq_hasDerivAt (t z : ℝ) :
    HasDerivAt (fun Z : ℝ => (t + Z) / 2) (1 / 2 : ℝ) z := by
  have h := hasDerivAt_affine (t / 2) (1 / 2) z
  refine h.congr_of_eventuallyEq ?_
  filter_upwards with Y
  ring

/-- The Jacobian `K = ∂(s, z₀, z₁, z₂)/∂(t, x₁, x₂, z)` of the Fermi chart. -/
def fermiK : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1 / 2, 0, 0, 1 / 2;
     1, 0, 0, -1;
     0, 1, 0, 0;
     0, 0, 1, 0]

/-- **`fermiK` is the matrix of actual partial derivatives of the chart maps.**
Nothing about the Jacobian is postulated: each of the sixteen entries is produced by
`deriv` applied to the corresponding chart coordinate. -/
theorem fermiK_eq_deriv (t x₁ x₂ z : ℝ) :
    fermiK = !![dRT sCoord t x₁ x₂ z, dRX1 sCoord t x₁ x₂ z,
                  dRX2 sCoord t x₁ x₂ z, dRZ sCoord t x₁ x₂ z;
                dRT z0Coord t x₁ x₂ z, dRX1 z0Coord t x₁ x₂ z,
                  dRX2 z0Coord t x₁ x₂ z, dRZ z0Coord t x₁ x₂ z;
                dRT z1Coord t x₁ x₂ z, dRX1 z1Coord t x₁ x₂ z,
                  dRX2 z1Coord t x₁ x₂ z, dRZ z1Coord t x₁ x₂ z;
                dRT z2Coord t x₁ x₂ z, dRX1 z2Coord t x₁ x₂ z,
                  dRX2 z2Coord t x₁ x₂ z, dRZ z2Coord t x₁ x₂ z] := by
  rw [dRT_sCoord, dRX1_sCoord, dRX2_sCoord, dRZ_sCoord,
      dRT_z0Coord, dRX1_z0Coord, dRX2_z0Coord, dRZ_z0Coord,
      dRT_z1Coord, dRX1_z1Coord, dRX2_z1Coord, dRZ_z1Coord,
      dRT_z2Coord, dRX1_z2Coord, dRX2_z2Coord, dRZ_z2Coord]
  rfl

/-- The Minkowski inverse metric in Cartesian coordinates `(t, x₁, x₂, z)`,
signature `(+,-,-,-)`. -/
noncomputable def minkGinv : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, 0, 0, 0;
     0, -1, 0, 0;
     0, 0, -1, 0;
     0, 0, 0, -1]

theorem minkGinv_eq_diagonal : minkGinv = Matrix.diagonal ![1, -1, -1, -1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [minkGinv]

/-- The inverse metric in the Fermi chart `(s, z₀, z₁, z₂)`.  Note the null pairing of
`s` with `z₀` and the Euclidean `-1`'s in the two genuinely spatial transverse slots. -/
noncomputable def fermiGinv : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, 1, 0, 0;
     1, 0, 0, 0;
     0, 0, -1, 0;
     0, 0, 0, -1]

/-- **The Fermi metric coefficients are derived, not posited**: `ĝ = K g Kᵀ`. -/
theorem fermiGinv_derived : fermiK * minkGinv * fermiKᵀ = fermiGinv := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_four]
  fin_cases i <;> fin_cases j <;>
    norm_num [fermiK, minkGinv, fermiGinv, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, Matrix.head_cons]

/-- The Fermi inverse metric is symmetric. -/
theorem fermiGinv_isSymm : fermiGinv.IsSymm := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [fermiGinv]

/-- The Fermi inverse metric is non-degenerate: it squares to the identity, hence is its
own inverse.  (Both `ĝ` and `g` are involutions in these normalisations.) -/
theorem fermiGinv_mul_self : fermiGinv * fermiGinv = (1 : Matrix (Fin 4) (Fin 4) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [fermiGinv, Matrix.mul_apply, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, Matrix.head_cons]

/-! ## §3  Fermi partial derivatives and the Fermi wave operator -/

/-- `∂_s`, the derivative along the null geodesic parameter. -/
def dS (F : ℝ → ℝ → ℝ → ℝ → ℂ) : ℝ → ℝ → ℝ → ℝ → ℂ :=
  fun s z₀ z₁ z₂ => deriv (fun S : ℝ => F S z₀ z₁ z₂) s

/-- `∂_{z₀}`, the derivative along the conjugate null direction. -/
def dZ0 (F : ℝ → ℝ → ℝ → ℝ → ℂ) : ℝ → ℝ → ℝ → ℝ → ℂ :=
  fun s z₀ z₁ z₂ => deriv (fun Z : ℝ => F s Z z₁ z₂) z₀

/-- `∂_{z₁}`, the first spatial transverse direction. -/
def dZ1 (F : ℝ → ℝ → ℝ → ℝ → ℂ) : ℝ → ℝ → ℝ → ℝ → ℂ :=
  fun s z₀ z₁ z₂ => deriv (fun Z : ℝ => F s z₀ Z z₂) z₁

/-- `∂_{z₂}`, the second spatial transverse direction. -/
def dZ2 (F : ℝ → ℝ → ℝ → ℝ → ℂ) : ℝ → ℝ → ℝ → ℝ → ℂ :=
  fun s z₀ z₁ z₂ => deriv (fun Z : ℝ => F s z₀ z₁ Z) z₂

theorem dS_eq_dT : dS = dT := rfl
theorem dZ0_eq_dX1 : dZ0 = dX1 := rfl
theorem dZ1_eq_dX2 : dZ1 = dX2 := rfl
theorem dZ2_eq_dZ : dZ2 = dZ := rfl

/-- The four Fermi partial derivatives, indexed by `Fin 4`. -/
def dFermi : Fin 4 → (ℝ → ℝ → ℝ → ℝ → ℂ) → (ℝ → ℝ → ℝ → ℝ → ℂ) := ![dS, dZ0, dZ1, dZ2]

/-- The four Cartesian partial derivatives, indexed by `Fin 4`. -/
def dCart : Fin 4 → (ℝ → ℝ → ℝ → ℝ → ℂ) → (ℝ → ℝ → ℝ → ℝ → ℂ) := ![dT, dX1, dX2, dZ]

/-- **The Fermi wave operator, defined by the derived coefficients**:
`□_F F = ĝ^{ab} ∂_a ∂_b F`.

The definition is the raw double sum, with **no** symmetry of mixed partials assumed:
the two off-diagonal terms `∂_s ∂_{z₀}` and `∂_{z₀} ∂_s` both appear separately. -/
def boxF (F : ℝ → ℝ → ℝ → ℝ → ℂ) : ℝ → ℝ → ℝ → ℝ → ℂ :=
  fun s z₀ z₁ z₂ => ∑ a, ∑ b, ((fermiGinv a b : ℝ) : ℂ) * dFermi a (dFermi b F) s z₀ z₁ z₂

/-- The explicit form of `□_F`. -/
theorem boxF_apply (F : ℝ → ℝ → ℝ → ℝ → ℂ) (s z₀ z₁ z₂ : ℝ) :
    boxF F s z₀ z₁ z₂ =
      dS (dZ0 F) s z₀ z₁ z₂ + dZ0 (dS F) s z₀ z₁ z₂
        - dZ1 (dZ1 F) s z₀ z₁ z₂ - dZ2 (dZ2 F) s z₀ z₁ z₂ := by
  simp only [boxF, Fin.sum_univ_four]
  norm_num [dFermi, fermiGinv, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, Matrix.head_cons]
  ring

/-- **The Cartesian d'Alembertian of version 0.1 is `g^{ab} ∂_a ∂_b`**, with the same
Minkowski coefficients used in the derivation `ĝ = K g Kᵀ`. -/
theorem dAlembert_eq_metric_sum (F : ℝ → ℝ → ℝ → ℝ → ℂ) (t x₁ x₂ z : ℝ) :
    dAlembert F t x₁ x₂ z
      = ∑ a, ∑ b, ((minkGinv a b : ℝ) : ℂ) * dCart a (dCart b F) t x₁ x₂ z := by
  simp only [dAlembert, Fin.sum_univ_four]
  norm_num [dCart, minkGinv, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, Matrix.head_cons]
  ring

/-! ## §4  The complex symmetric phase matrix and the Riccati system -/

/-- `c_F(s) = 1 - i s`: the version-0.1 factor `c(σ) = 1 - iσ/2` evaluated at `σ = 2s`. -/
def cF (s : ℝ) : ℂ := 1 - Complex.I * (s : ℂ)

theorem cF_eq_cs (s : ℝ) : cF s = cs (2 * s) := by
  simp only [cF, cs]
  push_cast
  ring

theorem cF_ne_zero (s : ℝ) : cF s ≠ 0 := by
  rw [cF_eq_cs]; exact cs_ne_zero _

theorem norm_cF (s : ℝ) : ‖cF s‖ = Real.sqrt (1 + s ^ 2) := by
  rw [cF_eq_cs, norm_cs]
  congr 1
  ring

theorem one_le_norm_cF (s : ℝ) : 1 ≤ ‖cF s‖ := by
  rw [norm_cF]
  calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
    _ ≤ Real.sqrt (1 + s ^ 2) := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg s])

theorem hasDerivAt_cF (s : ℝ) : HasDerivAt cF (-Complex.I) s := by
  have h : HasDerivAt (fun y : ℝ => (y : ℂ)) ((1 : ℝ) : ℂ) s := (hasDerivAt_id s).ofReal_comp
  have h2 : HasDerivAt (fun y : ℝ => (1 : ℂ) - Complex.I * (y : ℂ))
      (-(Complex.I * ((1 : ℝ) : ℂ))) s := (h.const_mul Complex.I).const_sub 1
  exact h2.congr_deriv (by push_cast; ring)

/-- `d/ds (i / c_F(s)) = -1 / c_F(s)²`, from the actual derivative of `c_F`. -/
theorem hasDerivAt_I_div_cF (s : ℝ) :
    HasDerivAt (fun σ : ℝ => Complex.I / cF σ) (-(1 / cF s ^ 2)) s := by
  have h : HasDerivAt (fun σ : ℝ => Complex.I / cF σ)
      ((0 * cF s - Complex.I * (-Complex.I)) / cF s ^ 2) s :=
    (hasDerivAt_const s Complex.I).fun_div (hasDerivAt_cF s) (cF_ne_zero s)
  refine h.congr_deriv ?_
  have hnum : (0 : ℂ) * cF s - Complex.I * (-Complex.I) = -1 := by
    linear_combination Complex.I_mul_I
  rw [hnum]
  ring

/-- The **complex symmetric quadratic phase matrix**
`H(s) = diag(i λ, i / c_F(s), i / c_F(s))`.

The `(0,0)` entry carries the longitudinal (null `z₀`) direction with a *free positive*
focusing rate `λ`; the two remaining entries carry the classical Gaussian-beam phase of
the spatial transverse directions. -/
noncomputable def Hmat (lam : ℝ) (s : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  Matrix.diagonal ![Complex.I * (lam : ℂ), Complex.I / cF s, Complex.I / cF s]

/-- The transverse projector `P = diag(0,1,1)` appearing in the Riccati system. -/
noncomputable def Pmat : Matrix (Fin 3) (Fin 3) ℂ := Matrix.diagonal ![0, 1, 1]

/-- **`H(s)` is complex symmetric.** -/
theorem Hmat_isSymm (lam s : ℝ) : (Hmat lam s).IsSymm :=
  Matrix.isSymm_diagonal _

theorem Hmat_transpose (lam s : ℝ) : (Hmat lam s)ᵀ = Hmat lam s :=
  Matrix.diagonal_transpose _

theorem Hmat_apply_diag (lam s : ℝ) (i : Fin 3) :
    Hmat lam s i i = ![Complex.I * (lam : ℂ), Complex.I / cF s, Complex.I / cF s] i :=
  Matrix.diagonal_apply_eq _ i

theorem Hmat_apply_ne (lam s : ℝ) {i j : Fin 3} (h : i ≠ j) : Hmat lam s i j = 0 := by
  simp [Hmat, Matrix.diagonal_apply_ne _ h]

/-- The Riccati right-hand side, computed in closed form. -/
theorem Hmat_riccati_rhs (lam s : ℝ) :
    Hmat lam s * Pmat * Hmat lam s
      = Matrix.diagonal ![0, -(1 / cF s ^ 2), -(1 / cF s ^ 2)] := by
  have hc : cF s ≠ 0 := cF_ne_zero s
  simp only [Hmat, Pmat, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  fin_cases i <;> simp
  · field_simp
    linear_combination Complex.I_mul_I
  · field_simp
    linear_combination Complex.I_mul_I

/-- **The Riccati system `H'(s) = H(s) P H(s)`**, entrywise, from actual derivatives.

This is the flat-space Riccati equation governing the Gaussian-beam phase matrix in the
null Fermi chart.  Every entry of the derivative is produced by `HasDerivAt`. -/
theorem hasDerivAt_Hmat (lam : ℝ) (s : ℝ) (i j : Fin 3) :
    HasDerivAt (fun σ : ℝ => Hmat lam σ i j) ((Hmat lam s * Pmat * Hmat lam s) i j) s := by
  rw [Hmat_riccati_rhs]
  by_cases h : i = j
  · subst h
    rw [Matrix.diagonal_apply_eq]
    have hfun : (fun σ : ℝ => Hmat lam σ i i)
        = fun σ : ℝ => ![Complex.I * (lam : ℂ), Complex.I / cF σ, Complex.I / cF σ] i := by
      funext σ; exact Hmat_apply_diag lam σ i
    rw [hfun]
    fin_cases i
    · exact hasDerivAt_const s _
    · exact hasDerivAt_I_div_cF s
    · exact hasDerivAt_I_div_cF s
  · rw [Matrix.diagonal_apply_ne _ h]
    have hfun : (fun σ : ℝ => Hmat lam σ i j) = fun _ : ℝ => (0 : ℂ) := by
      funext σ; exact Hmat_apply_ne lam σ h
    rw [hfun]
    exact hasDerivAt_const s 0

/-- The `deriv` form of the Riccati system. -/
theorem deriv_Hmat (lam : ℝ) (s : ℝ) (i j : Fin 3) :
    deriv (fun σ : ℝ => Hmat lam σ i j) s = (Hmat lam s * Pmat * Hmat lam s) i j :=
  (hasDerivAt_Hmat lam s i j).deriv

/-! ## §5  The quadratic phase and uniform coercivity -/

/-- The squared Euclidean length of a genuine three-dimensional transverse vector. -/
def nsq (z : Fin 3 → ℝ) : ℝ := ∑ i, z i ^ 2

theorem nsq_apply (z : Fin 3 → ℝ) : nsq z = z 0 ^ 2 + z 1 ^ 2 + z 2 ^ 2 := by
  simp [nsq, Fin.sum_univ_three]

theorem nsq_nonneg (z : Fin 3 → ℝ) : 0 ≤ nsq z := by
  rw [nsq_apply]; positivity

/-- The complex quadratic form `z' ↦ z'ᵀ H z'` of a `3×3` complex matrix. -/
def quad (H : Matrix (Fin 3) (Fin 3) ℂ) (z : Fin 3 → ℝ) : ℂ :=
  ∑ i, ∑ j, H i j * ((z i : ℝ) : ℂ) * ((z j : ℝ) : ℂ)

theorem quad_diagonal (d : Fin 3 → ℂ) (z : Fin 3 → ℝ) :
    quad (Matrix.diagonal d) z = ∑ i, d i * ((z i : ℝ) : ℂ) ^ 2 := by
  simp only [quad, Fin.sum_univ_three]
  norm_num [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_ne, Fin.ext_iff, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, Matrix.head_cons]
  ring

/-- The **Gaussian-beam phase** `φ(s, z') = z₀ + ½ z'ᵀ H(s) z'`. -/
noncomputable def phiF (lam : ℝ) (s : ℝ) (z : Fin 3 → ℝ) : ℂ :=
  ((z 0 : ℝ) : ℂ) + quad (Hmat lam s) z / 2

/-- The closed form of the phase, with the two spatial transverse directions grouped. -/
theorem phiF_apply (lam s : ℝ) (z : Fin 3 → ℝ) :
    phiF lam s z = ((z 0 : ℝ) : ℂ)
      + Complex.I * ((lam * z 0 ^ 2 / 2 : ℝ) : ℂ)
      + Complex.I * ((z 1 ^ 2 + z 2 ^ 2 : ℝ) : ℂ) / (2 * cF s) := by
  have hc : cF s ≠ 0 := cF_ne_zero s
  simp only [phiF, Hmat, quad_diagonal, Fin.sum_univ_three]
  norm_num [Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, Matrix.head_cons]
  field_simp
  ring

theorem two_cF_re (s : ℝ) : ((2 : ℂ) * cF s).re = 2 := by simp [cF]

theorem two_cF_im (s : ℝ) : ((2 : ℂ) * cF s).im = -(2 * s) := by
  simp [cF]

theorem normSq_two_cF (s : ℝ) : Complex.normSq ((2 : ℂ) * cF s) = 4 * (1 + s ^ 2) := by
  rw [Complex.normSq_apply, two_cF_re, two_cF_im]
  ring

/-- The imaginary part of the transverse phase term. -/
theorem I_mul_div_two_cF_im (w s : ℝ) :
    (Complex.I * ((w : ℝ) : ℂ) / (2 * cF s)).im = w / (2 * (1 + s ^ 2)) := by
  have hpos : (0 : ℝ) < 1 + s ^ 2 := by positivity
  rw [Complex.div_im, normSq_two_cF, two_cF_re, two_cF_im]
  simp only [Complex.mul_im, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im]
  field_simp
  ring

/-- The real part of the transverse phase term: the wavefront-curvature contribution. -/
theorem I_mul_div_two_cF_re (w s : ℝ) :
    (Complex.I * ((w : ℝ) : ℂ) / (2 * cF s)).re = -(w * s / (2 * (1 + s ^ 2))) := by
  have hpos : (0 : ℝ) < 1 + s ^ 2 := by positivity
  rw [Complex.div_re, normSq_two_cF, two_cF_re, two_cF_im]
  simp only [Complex.mul_im, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im]
  field_simp
  ring

/-- **The exact imaginary part of the phase.**

`Im φ(s, z') = ½ λ z₀² + (z₁² + z₂²) / (2(1+s²))`.

Both the longitudinal (null) direction `z₀` and the two spatial transverse directions carry a
*strictly positive* Gaussian weight as soon as `λ > 0`. -/
theorem phiF_im (lam s : ℝ) (z : Fin 3 → ℝ) :
    (phiF lam s z).im = lam * z 0 ^ 2 / 2 + (z 1 ^ 2 + z 2 ^ 2) / (2 * (1 + s ^ 2)) := by
  rw [phiF_apply, Complex.add_im, Complex.add_im, I_mul_div_two_cF_im]
  have h1 : (((z 0 : ℝ) : ℂ)).im = 0 := Complex.ofReal_im _
  have h2 : (Complex.I * ((lam * z 0 ^ 2 / 2 : ℝ) : ℂ)).im = lam * z 0 ^ 2 / 2 := by
    rw [Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [h1, h2]
  ring

/-- **The exact real part of the phase**: the null coordinate `z₀` together with the classical
Gaussian-beam wavefront-curvature term `-(z₁²+z₂²) s / (2(1+s²))`.  The `λ`-term contributes
nothing to the real part, so it changes only the localisation, never the oscillation. -/
theorem phiF_re (lam s : ℝ) (z : Fin 3 → ℝ) :
    (phiF lam s z).re = z 0 - (z 1 ^ 2 + z 2 ^ 2) * s / (2 * (1 + s ^ 2)) := by
  rw [phiF_apply, Complex.add_re, Complex.add_re, I_mul_div_two_cF_re]
  have h1 : (((z 0 : ℝ) : ℂ)).re = z 0 := Complex.ofReal_re _
  have h2 : (Complex.I * ((lam * z 0 ^ 2 / 2 : ℝ) : ℂ)).re = 0 := by
    rw [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [h1, h2]
  ring

/-! ### Uniform coercivity of the imaginary part -/

/-- `m(S) = 1 + S²`, the uniform bound for `|c_F(s)|²` on `|s| ≤ S`. -/
def mS (S : ℝ) : ℝ := 1 + S ^ 2

theorem one_le_mS (S : ℝ) : 1 ≤ mS S := by
  unfold mS; nlinarith [sq_nonneg S]

theorem mS_pos (S : ℝ) : 0 < mS S := lt_of_lt_of_le one_pos (one_le_mS S)

/-- The coercivity constant `β(λ,S) = min(λ, 1/m(S))`. -/
def betS (lam S : ℝ) : ℝ := min lam (1 / mS S)

theorem betS_pos {lam : ℝ} (hlam : 0 < lam) (S : ℝ) : 0 < betS lam S :=
  lt_min hlam (one_div_pos.mpr (mS_pos S))

theorem betS_le_lam (lam S : ℝ) : betS lam S ≤ lam := min_le_left _ _

theorem betS_le_inv_mS (lam S : ℝ) : betS lam S ≤ 1 / mS S := min_le_right _ _

/-- **Uniform coercivity of the phase.**

For `λ > 0` and every `s` with `|s| ≤ S`,

  `Im φ(s, z') ≥ (β(λ,S)/2) ‖z'‖²`,   `β(λ,S) = min(λ, 1/(1+S²)) > 0`,

with `‖z'‖² = z₀² + z₁² + z₂²` the **full three-dimensional** squared length.  The constant
is uniform in `s` on the slab and independent of `ρ`. -/
theorem phiF_im_coercive {lam : ℝ} (hlam : 0 < lam) {S s : ℝ} (hs : |s| ≤ S)
    (z : Fin 3 → ℝ) :
    betS lam S / 2 * nsq z ≤ (phiF lam s z).im := by
  have hS : 0 ≤ S := le_trans (abs_nonneg s) hs
  have hsq : s ^ 2 ≤ S ^ 2 := by nlinarith [sq_abs s, abs_nonneg s]
  have hm : (0 : ℝ) < 1 + s ^ 2 := by positivity
  have hmS : (0 : ℝ) < mS S := mS_pos S
  have hbet : 0 < betS lam S := betS_pos hlam S
  rw [phiF_im, nsq_apply]
  have h0 : betS lam S / 2 * z 0 ^ 2 ≤ lam * z 0 ^ 2 / 2 := by
    have := betS_le_lam lam S
    nlinarith [sq_nonneg (z 0)]
  have hkey : betS lam S ≤ 1 / (1 + s ^ 2) := by
    refine le_trans (betS_le_inv_mS lam S) ?_
    refine one_div_le_one_div_of_le hm ?_
    unfold mS
    linarith
  have h12 : betS lam S / 2 * (z 1 ^ 2 + z 2 ^ 2) ≤ (z 1 ^ 2 + z 2 ^ 2) / (2 * (1 + s ^ 2)) := by
    have hnn : (0 : ℝ) ≤ (z 1 ^ 2 + z 2 ^ 2) / 2 := by positivity
    have h := mul_le_mul_of_nonneg_right hkey hnn
    have e1 : betS lam S * ((z 1 ^ 2 + z 2 ^ 2) / 2)
        = betS lam S / 2 * (z 1 ^ 2 + z 2 ^ 2) := by ring
    have e2 : 1 / (1 + s ^ 2) * ((z 1 ^ 2 + z 2 ^ 2) / 2)
        = (z 1 ^ 2 + z 2 ^ 2) / (2 * (1 + s ^ 2)) := by
      field_simp
    rw [e1, e2] at h
    exact h
  have hsplit : betS lam S / 2 * (z 0 ^ 2 + z 1 ^ 2 + z 2 ^ 2)
      = betS lam S / 2 * z 0 ^ 2 + betS lam S / 2 * (z 1 ^ 2 + z 2 ^ 2) := by ring
  rw [hsplit]
  linarith

/-! ## §6  Negative regression: the two-transverse phase is not coercive -/

/-- The older two-transverse incident phase, reproduced locally so this
calibration does not import the superseded bare-integral `L2` layer. -/
def phaseIn : ℝ → ℝ → ℝ → ℝ → ℂ :=
  fun t x₁ x₂ z =>
    ((t - z : ℝ) : ℂ) +
      Complex.I * ((rsq x₁ x₂ : ℝ) : ℂ) / (2 * cs (t + z))

/-- **The version-0.2 phase is exactly the `λ = 0` Fermi phase.**

The two-transverse incident phase, written in the Fermi chart, is `φ` with
`λ = 0`: it carries *no* quadratic term in the third (null) direction `z₀`. -/
theorem phaseIn_eq_phiF_zero (t x₁ x₂ z : ℝ) :
    phaseIn t x₁ x₂ z = phiF 0 ((t + z) / 2) ![t - z, x₁, x₂] := by
  have hc : cs (t + z) ≠ 0 := cs_ne_zero _
  have hcF : cF ((t + z) / 2) = cs (t + z) := by
    rw [cF_eq_cs]; congr 1; ring
  rw [phiF_apply, hcF, phaseIn]
  norm_num [rsq, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, Matrix.head_cons]

/-- With `λ = 0` the imaginary part of the phase is blind to `z₀`. -/
theorem phiF_zero_im (s : ℝ) (z : Fin 3 → ℝ) :
    (phiF 0 s z).im = (z 1 ^ 2 + z 2 ^ 2) / (2 * (1 + s ^ 2)) := by
  rw [phiF_im]; ring

/-- **Negative regression theorem.**

There is *no* positive constant `c` for which the two-transverse phase satisfies the
three-dimensional coercivity estimate `Im φ ≥ c ‖z'‖²`, not even at the single point `s = 0`
and not even after shrinking `c`.  The omitted third direction `z₀` is uncontrolled: the
phase's imaginary part vanishes identically along it.

This is exactly what makes the version-0.2 two-transverse calibration insufficient as a
1+3-dimensional Gaussian-beam model, and it is what the `λ`-term of `Hmat` repairs. -/
theorem two_transverse_not_coercive :
    ¬ ∃ c : ℝ, 0 < c ∧ ∀ (s : ℝ) (z : Fin 3 → ℝ), c * nsq z ≤ (phiF 0 s z).im := by
  rintro ⟨c, hc, h⟩
  have hz := h 0 ![1, 0, 0]
  rw [phiF_zero_im] at hz
  norm_num [nsq_apply, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, Matrix.head_cons] at hz
  linarith

/-- The same failure, stated directly for the version-0.2 Cartesian phase `phaseIn`:
no `c > 0` controls `Im Φin` by the full squared Fermi length `(t-z)² + x₁² + x₂²`. -/
theorem phaseIn_not_coercive :
    ¬ ∃ c : ℝ, 0 < c ∧ ∀ t x₁ x₂ z : ℝ,
        c * ((t - z) ^ 2 + x₁ ^ 2 + x₂ ^ 2) ≤ (phaseIn t x₁ x₂ z).im := by
  rintro ⟨c, hc, h⟩
  have hz := h (1 / 2) 0 0 (-(1 / 2))
  rw [phaseIn_eq_phiF_zero, phiF_zero_im] at hz
  norm_num [Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, Matrix.head_cons] at hz
  linarith

/-- By contrast, with `λ > 0` a coercivity constant *does* exist on every bounded slab.
This is the positive counterpart of `two_transverse_not_coercive`. -/
theorem exists_coercivity_constant {lam : ℝ} (hlam : 0 < lam) (S : ℝ) :
    ∃ c : ℝ, 0 < c ∧ ∀ (s : ℝ), |s| ≤ S → ∀ z : Fin 3 → ℝ, c * nsq z ≤ (phiF lam s z).im :=
  ⟨betS lam S / 2, half_pos (betS_pos hlam S), fun _ hs z => phiF_im_coercive hlam hs z⟩

end

end Fermi
end LiuWang2025SemilinearWaveFlatBeam
