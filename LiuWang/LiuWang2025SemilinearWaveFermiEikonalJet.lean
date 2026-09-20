import LiuWang.LiuWang2025SemilinearWaveRiccatiFlow
import LiuWang.LiuWang2025SemilinearWaveLeadingAmplitudeTransport
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Liu--Wang 2025: the Fermi-coordinate transverse jet of the eikonal equation

Source: Boya Liu and Weinan Wang, *On a partial data inverse problem for the
semi-linear wave equation*, arXiv:2511.08794v1, Section 3.

The paper's Gaussian-beam phase is built in null Fermi coordinates
`(tau, z^1, ..., z^n)` along a null geodesic, with the ansatz

`phi = phi_1 + phi_2 + ...`,  `phi_1 = z^1`,
`phi_2(tau, z) = sum_{i,j} M_{ij}(tau) z^i z^j`,

and the requirement that the eikonal symbol

`S phi = <d phi, d phi>_g`

vanishes to second order in the transverse variables on the geodesic.  The
paper then *states* that this forces the matrix Riccati equation

`d/dtau M + M C M + D = 0`,   `C_{11} = 0`, `C_{ii} = 2` (`i >= 2`),
`C_{ij} = 0` (`i != j`),      `D_{ij} = (1/4) d^2_{ij} g^{11}`.

The existing `RiccatiPhase`/`RiccatiFlow` modules verify everything *after*
that equation: the linearization `Y' = CZ`, `Z' = -DY`, `H = Z Y^{-1}`, the
Wronskian invariants, positivity of `Im M`, and the determinant identity.
What was missing --- and is supplied here --- is the geometric step that
*produces* equation (3.8) from the metric, i.e. the identification of the
paper's coefficients `C` and `D` with actual data of the inverse metric in
the Fermi chart.

## What this module proves

Fix a transverse direction `w` and restrict the inverse metric components to
the transverse line `z = t w` inside the Fermi chart.  With the phase gradient

`d_tau phi = z^T M'(tau) z`,  `d_{z^i} phi = delta_{i1} + 2 (M(tau) z)_i`,

the eikonal `S phi` restricted to that line is a genuine `C^2` function of
`t`, and Lean computes all three coefficients of its second-order Taylor jet
at `t = 0` from actual derivatives:

* `eikonal_center_eq_zero`   : `S phi = 0` on the geodesic (null geodesic);
* `eikonal_firstJet_eq_zero` : the first transverse derivative vanishes;
* `eikonal_secondJet_eq`     : the second transverse derivative equals
  `4 * w^T (M' + M C M + D) w`.

Consequently:

* `eikonal_secondJet_eq_zero_of_riccati` : equation (3.8) makes the transverse
  second jet of the eikonal vanish in *every* direction;
* `riccati_of_eikonal_secondJet_eq_zero` : conversely, vanishing of the
  transverse second jet in every real direction forces equation (3.8).

So on the Fermi chart the paper's Riccati equation is *exactly* the
second-order transverse eikonal condition, with the paper's own `C` and `D`.

A second section performs the corresponding computation for the transport
operator

`T a = 2 <d phi, d a>_g - (Box_g phi) a`

at the beam centre, and proves

`T a |_{z = 0} = 2 a'(tau) - (Tr(C M(tau)) + beta_1(tau)) a(tau)`,

where `beta` is the first-order coefficient of `Box_g` in the Fermi chart.
The resulting scalar coefficient is fed into the existing integrating-factor
solution of `2 b' + q b = 0`, which gives a nonvanishing leading amplitude
along the geodesic.

## Scope

The normalization of the Fermi chart along the geodesic is a hypothesis, not
a theorem: constructing the chart from a Lorentzian metric and proving the
normalization `g^{tau z^1} = 1`, `g^{z^1 z^i} = 0`, `d g^{z^1 z^i} = 0`,
`(g^{z^i z^j}) = C/2` is the differential-geometric content of the source's
Section 3 and is *not* proved here.  Everything downstream of those
normalizations --- the entire passage from the metric jet to equation (3.8)
and to the transport coefficient --- is proved from actual derivatives.  No
flat or finite-dimensional surrogate is used: the metric components are
arbitrary `C^2` functions along the transverse line.
-/

noncomputable section

open scoped BigOperators
open Matrix

namespace LiuWang2025SemilinearWaveFermiEikonalJet

variable {iota : Type*} [Fintype iota] [DecidableEq iota]

/-! ## Bilinear and quadratic forms

The eikonal symbol is the *bilinear* form of the inverse metric applied to
`d phi`, not the sesquilinear form used for positivity of `Im M`. -/

/-- The bilinear form `x^T A y`. -/
def bilinForm (A : Matrix iota iota Complex) (x y : iota -> Complex) : Complex :=
  x ⬝ᵥ (A *ᵥ y)

/-- The bilinear quadratic form `x^T A x`. -/
def quadForm (A : Matrix iota iota Complex) (x : iota -> Complex) : Complex :=
  bilinForm A x x

omit [DecidableEq iota] in
theorem bilinForm_eq_sum (A : Matrix iota iota Complex) (x y : iota -> Complex) :
    bilinForm A x y = ∑ i, ∑ j, A i j * x i * y j := by
  simp only [bilinForm, dotProduct, Matrix.mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

omit [DecidableEq iota] in
theorem quadForm_eq_sum (A : Matrix iota iota Complex) (x : iota -> Complex) :
    quadForm A x = ∑ i, ∑ j, A i j * x i * x j := bilinForm_eq_sum A x x

omit [DecidableEq iota] in
theorem bilinForm_add_matrix (A B : Matrix iota iota Complex) (x y : iota -> Complex) :
    bilinForm (A + B) x y = bilinForm A x y + bilinForm B x y := by
  simp [bilinForm, add_mulVec, dotProduct_add]

omit [DecidableEq iota] in
theorem quadForm_add_matrix (A B : Matrix iota iota Complex) (x : iota -> Complex) :
    quadForm (A + B) x = quadForm A x + quadForm B x := bilinForm_add_matrix A B x x

omit [DecidableEq iota] in
theorem bilinForm_add_left (A : Matrix iota iota Complex) (x y z : iota -> Complex) :
    bilinForm A (x + y) z = bilinForm A x z + bilinForm A y z := by
  simp [bilinForm, add_dotProduct]

omit [DecidableEq iota] in
theorem bilinForm_add_right (A : Matrix iota iota Complex) (x y z : iota -> Complex) :
    bilinForm A x (y + z) = bilinForm A x y + bilinForm A x z := by
  simp [bilinForm, mulVec_add, dotProduct_add]

omit [DecidableEq iota] in
/-- Congruence of the bilinear quadratic form, used to identify the paper's
`M C M` term. -/
theorem quadForm_mulVec (A M : Matrix iota iota Complex) (x : iota -> Complex) :
    quadForm A (M *ᵥ x) = quadForm (Mᵀ * A * M) x := by
  simp only [quadForm, bilinForm]
  rw [mulVec_mulVec, dotProduct_mulVec, ← vecMul_transpose,
    vecMul_vecMul, ← dotProduct_mulVec, Matrix.mul_assoc]

omit [DecidableEq iota] in
/-- Homogeneity of the quadratic form in the vector slot. -/
theorem quadForm_const_mul (A : Matrix iota iota Complex) (c : Complex)
    (x : iota -> Complex) :
    quadForm A (fun i => c * x i) = c ^ 2 * quadForm A x := by
  simp only [quadForm_eq_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- The coordinate vector `e_k`. -/
def basisVector (k : iota) : iota -> Complex := Pi.single k 1

theorem bilinForm_basisVector (A : Matrix iota iota Complex) (k l : iota) :
    bilinForm A (basisVector k) (basisVector l) = A k l := by
  simp [bilinForm, basisVector, single_dotProduct, mulVec_single]

/-- A complex symmetric matrix whose bilinear quadratic form vanishes on all
vectors is zero. -/
theorem eq_zero_of_quadForm_eq_zero {A : Matrix iota iota Complex}
    (hsymm : ∀ i j, A i j = A j i)
    (h : ∀ x : iota -> Complex, quadForm A x = 0) : A = 0 := by
  have hdiag : ∀ k : iota, A k k = 0 := by
    intro k
    have hk := h (basisVector k)
    rwa [quadForm, bilinForm_basisVector] at hk
  ext i j
  have hexpand := h (basisVector i + basisVector j)
  rw [quadForm, bilinForm_add_left, bilinForm_add_right, bilinForm_add_right,
    bilinForm_basisVector, bilinForm_basisVector, bilinForm_basisVector,
    bilinForm_basisVector, hdiag i, hdiag j, hsymm j i] at hexpand
  have htwo : (2 : Complex) * A i j = 0 := by linear_combination hexpand
  have h2 : (2 : Complex) ≠ 0 := two_ne_zero
  simpa using (mul_eq_zero.mp htwo).resolve_left h2

/-! ## `C^2` jets of the inverse metric and of the phase gradient along a
transverse line -/

/-- The restriction to a transverse line `z = t w` of the inverse-metric
components in the Fermi chart, together with their first and second
derivatives.  Spacetime indices are `Option iota`: `none` is the geodesic
parameter `tau`, `some i` is the transverse coordinate `z^i`. -/
structure MetricLineJet (iota : Type*) where
  G : Real -> Option iota -> Option iota -> Complex
  G₁ : Real -> Option iota -> Option iota -> Complex
  G₂ : Real -> Option iota -> Option iota -> Complex
  symm : ∀ t a b, G t a b = G t b a
  hasDerivG : ∀ t a b, HasDerivAt (fun s => G s a b) (G₁ t a b) t
  hasDerivG₁ : ∀ t a b, HasDerivAt (fun s => G₁ s a b) (G₂ t a b) t

namespace MetricLineJet

variable (L : MetricLineJet iota)

omit [Fintype iota] [DecidableEq iota] in
/-- Symmetry of the inverse metric is inherited by its first derivative. -/
theorem symm₁ (t : Real) (a b : Option iota) : L.G₁ t a b = L.G₁ t b a := by
  have h1 := L.hasDerivG t a b
  have h2 := L.hasDerivG t b a
  have hfun : (fun s => L.G s a b) = fun s => L.G s b a :=
    funext fun s => L.symm s a b
  rw [hfun] at h1
  exact h1.unique h2

end MetricLineJet

/-- The restriction to the same transverse line of the gradient `d phi`,
with its first and second derivatives. -/
structure GradLineJet (iota : Type*) where
  g : Option iota -> Real -> Complex
  g₁ : Option iota -> Real -> Complex
  g₂ : Option iota -> Real -> Complex
  hasDerivg : ∀ a t, HasDerivAt (g a) (g₁ a t) t
  hasDerivg₁ : ∀ a t, HasDerivAt (g₁ a) (g₂ a t) t

/-! ## The eikonal symbol along the line and its two derivatives -/

/-- `S phi = <d phi, d phi>_g` restricted to the transverse line. -/
def eikonal (L : MetricLineJet iota) (P : GradLineJet iota) (t : Real) : Complex :=
  ∑ a, ∑ b, L.G t a b * P.g a t * P.g b t

/-- The exact first `t`-derivative of the eikonal symbol. -/
def eikonalDeriv (L : MetricLineJet iota) (P : GradLineJet iota) (t : Real) : Complex :=
  ∑ a, ∑ b, (L.G₁ t a b * P.g a t * P.g b t
    + L.G t a b * P.g₁ a t * P.g b t
    + L.G t a b * P.g a t * P.g₁ b t)

/-- The exact second `t`-derivative of the eikonal symbol. -/
def eikonalDeriv₂ (L : MetricLineJet iota) (P : GradLineJet iota) (t : Real) : Complex :=
  ∑ a, ∑ b, (L.G₂ t a b * P.g a t * P.g b t
    + 2 * L.G₁ t a b * P.g₁ a t * P.g b t
    + 2 * L.G₁ t a b * P.g a t * P.g₁ b t
    + L.G t a b * P.g₂ a t * P.g b t
    + 2 * L.G t a b * P.g₁ a t * P.g₁ b t
    + L.G t a b * P.g a t * P.g₂ b t)

omit [DecidableEq iota] in
theorem hasDerivAt_eikonal (L : MetricLineJet iota) (P : GradLineJet iota) (t : Real) :
    HasDerivAt (eikonal L P) (eikonalDeriv L P t) t := by
  show HasDerivAt
      (fun s : Real => ∑ a : Option iota, ∑ b : Option iota, L.G s a b * P.g a s * P.g b s)
      (∑ a : Option iota, ∑ b : Option iota,
        (L.G₁ t a b * P.g a t * P.g b t
          + L.G t a b * P.g₁ a t * P.g b t
          + L.G t a b * P.g a t * P.g₁ b t)) t
  refine HasDerivAt.fun_sum fun a _ => HasDerivAt.fun_sum fun b _ => ?_
  have h := ((L.hasDerivG t a b).mul (P.hasDerivg a t)).mul (P.hasDerivg b t)
  convert h using 1
  simp only [Pi.mul_apply]
  ring

omit [DecidableEq iota] in
theorem hasDerivAt_eikonalDeriv (L : MetricLineJet iota) (P : GradLineJet iota) (t : Real) :
    HasDerivAt (eikonalDeriv L P) (eikonalDeriv₂ L P t) t := by
  show HasDerivAt
      (fun s : Real => ∑ a : Option iota, ∑ b : Option iota,
        (L.G₁ s a b * P.g a s * P.g b s
          + L.G s a b * P.g₁ a s * P.g b s
          + L.G s a b * P.g a s * P.g₁ b s))
      (∑ a : Option iota, ∑ b : Option iota,
        (L.G₂ t a b * P.g a t * P.g b t
          + 2 * L.G₁ t a b * P.g₁ a t * P.g b t
          + 2 * L.G₁ t a b * P.g a t * P.g₁ b t
          + L.G t a b * P.g₂ a t * P.g b t
          + 2 * L.G t a b * P.g₁ a t * P.g₁ b t
          + L.G t a b * P.g a t * P.g₂ b t)) t
  refine HasDerivAt.fun_sum fun a _ => HasDerivAt.fun_sum fun b _ => ?_
  have h1 := ((L.hasDerivG₁ t a b).mul (P.hasDerivg a t)).mul (P.hasDerivg b t)
  have h2 := ((L.hasDerivG t a b).mul (P.hasDerivg₁ a t)).mul (P.hasDerivg b t)
  have h3 := ((L.hasDerivG t a b).mul (P.hasDerivg a t)).mul (P.hasDerivg₁ b t)
  have h := (h1.fun_add h2).fun_add h3
  convert h using 1
  simp only [Pi.mul_apply]
  ring


/-! ## The paper's quadratic Fermi phase restricted to a transverse line -/

/-- Gaussian-beam phase data of the source on one transverse line.  `i1` is
the paper's distinguished transverse index `z^1`, `M` the symmetric phase
Hessian `M(tau)` of `phi_2 = sum_{ij} M_{ij} z^i z^j`, `dM` its
`tau`-derivative, and `w` a real transverse direction; the line is `z = t w`. -/
structure FermiPhaseLine (iota : Type*) [Fintype iota] [DecidableEq iota] where
  i1 : iota
  M : Matrix iota iota Complex
  dM : Matrix iota iota Complex
  w : iota -> Real

namespace FermiPhaseLine

variable (F : FermiPhaseLine iota)

/-- The complexified transverse direction. -/
def dir : iota -> Complex := fun i => (F.w i : Complex)

/-- `d_tau phi(tau, t w) = t^2 * w^T M'(tau) w`. -/
def longitudinal : Complex := quadForm F.dM F.dir

/-- `d_{z^i} phi(tau, t w) = delta_{i,i1} + t * 2 (M(tau) w)_i`. -/
def transverse (i : iota) : Complex := 2 * (F.M *ᵥ F.dir) i

/-- The restricted gradient of `phi = z^{i1} + z^T M z` with its first and
second `t`-derivatives, all verified from actual derivatives. -/
def gradJet : GradLineJet iota where
  g := fun a t => a.elim ((t : Complex) ^ 2 * F.longitudinal)
    (fun i => (if i = F.i1 then (1 : Complex) else 0) + (t : Complex) * F.transverse i)
  g₁ := fun a t => a.elim (2 * (t : Complex) * F.longitudinal) (fun i => F.transverse i)
  g₂ := fun a _ => a.elim (2 * F.longitudinal) (fun _ => 0)
  hasDerivg := by
    intro a t
    have hid : HasDerivAt (fun y : Real => (y : Complex)) 1 t := by
      simpa using (hasDerivAt_id t).ofReal_comp
    cases a with
    | none =>
      show HasDerivAt (fun s : Real => (s : Complex) ^ 2 * F.longitudinal)
        (2 * (t : Complex) * F.longitudinal) t
      have h := (hid.pow 2).mul_const F.longitudinal
      convert h using 1
      push_cast
      ring
    | some i =>
      show HasDerivAt (fun s : Real =>
          (if i = F.i1 then (1 : Complex) else 0) + (s : Complex) * F.transverse i)
        (F.transverse i) t
      have h := (hid.mul_const (F.transverse i)).const_add
        (if i = F.i1 then (1 : Complex) else 0)
      convert h using 1
      ring
  hasDerivg₁ := by
    intro a t
    have hid : HasDerivAt (fun y : Real => (y : Complex)) 1 t := by
      simpa using (hasDerivAt_id t).ofReal_comp
    cases a with
    | none =>
      show HasDerivAt (fun s : Real => 2 * (s : Complex) * F.longitudinal)
        (2 * F.longitudinal) t
      have h := (hid.const_mul (2 : Complex)).mul_const F.longitudinal
      convert h using 1
      ring
    | some i =>
      show HasDerivAt (fun _ : Real => F.transverse i) 0 t
      exact hasDerivAt_const t _

@[simp] theorem gradJet_g_none (t : Real) :
    F.gradJet.g none t = (t : Complex) ^ 2 * F.longitudinal := rfl

@[simp] theorem gradJet_g_some (i : iota) (t : Real) :
    F.gradJet.g (some i) t =
      (if i = F.i1 then (1 : Complex) else 0) + (t : Complex) * F.transverse i := rfl

@[simp] theorem gradJet_g₁_none (t : Real) :
    F.gradJet.g₁ none t = 2 * (t : Complex) * F.longitudinal := rfl

@[simp] theorem gradJet_g₁_some (i : iota) (t : Real) :
    F.gradJet.g₁ (some i) t = F.transverse i := rfl

@[simp] theorem gradJet_g₂_none (t : Real) :
    F.gradJet.g₂ none t = 2 * F.longitudinal := rfl

@[simp] theorem gradJet_g₂_some (i : iota) (t : Real) :
    F.gradJet.g₂ (some i) t = 0 := rfl

/-! ### Contractions against the centre values of `d phi` -/

theorem sum_mul_g_zero (f : Option iota -> Complex) :
    ∑ b : Option iota, f b * F.gradJet.g b 0 = f (some F.i1) := by
  rw [Fintype.sum_option]
  simp [Finset.sum_ite_eq', mul_ite]

theorem sum_mul_g₁_zero (f : Option iota -> Complex) :
    ∑ b : Option iota, f b * F.gradJet.g₁ b 0 = ∑ i, f (some i) * F.transverse i := by
  rw [Fintype.sum_option]
  simp

theorem sum_mul_g₂_zero (f : Option iota -> Complex) :
    ∑ b : Option iota, f b * F.gradJet.g₂ b 0 = f none * (2 * F.longitudinal) := by
  rw [Fintype.sum_option]
  simp

end FermiPhaseLine

/-! ## The transverse 2-jet of the eikonal symbol, before normalization -/

theorem eikonal_center_raw (L : MetricLineJet iota) (F : FermiPhaseLine iota) :
    eikonal L F.gradJet 0 = L.G 0 (some F.i1) (some F.i1) := by
  have inner : ∀ a : Option iota,
      (∑ b : Option iota, L.G 0 a b * F.gradJet.g a 0 * F.gradJet.g b 0)
        = L.G 0 a (some F.i1) * F.gradJet.g a 0 := fun a =>
    F.sum_mul_g_zero (fun b => L.G 0 a b * F.gradJet.g a 0)
  calc eikonal L F.gradJet 0
      = ∑ a : Option iota, L.G 0 a (some F.i1) * F.gradJet.g a 0 :=
        Finset.sum_congr rfl fun a _ => inner a
    _ = L.G 0 (some F.i1) (some F.i1) := F.sum_mul_g_zero _

theorem eikonalDeriv_center_raw (L : MetricLineJet iota) (F : FermiPhaseLine iota) :
    eikonalDeriv L F.gradJet 0 =
      L.G₁ 0 (some F.i1) (some F.i1)
        + (∑ i, L.G 0 (some i) (some F.i1) * F.transverse i)
        + (∑ i, L.G 0 (some F.i1) (some i) * F.transverse i) := by
  have hS1 : (∑ a : Option iota, ∑ b : Option iota,
      L.G₁ 0 a b * F.gradJet.g a 0 * F.gradJet.g b 0)
        = L.G₁ 0 (some F.i1) (some F.i1) := by
    calc (∑ a : Option iota, ∑ b : Option iota,
          L.G₁ 0 a b * F.gradJet.g a 0 * F.gradJet.g b 0)
        = ∑ a : Option iota, L.G₁ 0 a (some F.i1) * F.gradJet.g a 0 :=
          Finset.sum_congr rfl fun a _ =>
            F.sum_mul_g_zero (fun b => L.G₁ 0 a b * F.gradJet.g a 0)
      _ = L.G₁ 0 (some F.i1) (some F.i1) := F.sum_mul_g_zero _
  have hS2 : (∑ a : Option iota, ∑ b : Option iota,
      L.G 0 a b * F.gradJet.g₁ a 0 * F.gradJet.g b 0)
        = ∑ i, L.G 0 (some i) (some F.i1) * F.transverse i := by
    calc (∑ a : Option iota, ∑ b : Option iota,
          L.G 0 a b * F.gradJet.g₁ a 0 * F.gradJet.g b 0)
        = ∑ a : Option iota, L.G 0 a (some F.i1) * F.gradJet.g₁ a 0 :=
          Finset.sum_congr rfl fun a _ =>
            F.sum_mul_g_zero (fun b => L.G 0 a b * F.gradJet.g₁ a 0)
      _ = ∑ i, L.G 0 (some i) (some F.i1) * F.transverse i := F.sum_mul_g₁_zero _
  have hS3 : (∑ a : Option iota, ∑ b : Option iota,
      L.G 0 a b * F.gradJet.g a 0 * F.gradJet.g₁ b 0)
        = ∑ i, L.G 0 (some F.i1) (some i) * F.transverse i := by
    rw [Finset.sum_comm]
    calc (∑ b : Option iota, ∑ a : Option iota,
          L.G 0 a b * F.gradJet.g a 0 * F.gradJet.g₁ b 0)
        = ∑ b : Option iota, L.G 0 (some F.i1) b * F.gradJet.g₁ b 0 := by
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [← Finset.sum_mul, F.sum_mul_g_zero (fun a => L.G 0 a b)]
      _ = ∑ i, L.G 0 (some F.i1) (some i) * F.transverse i := F.sum_mul_g₁_zero _
  simp only [eikonalDeriv, Finset.sum_add_distrib]
  rw [hS1, hS2, hS3]

theorem eikonalDeriv₂_center_raw (L : MetricLineJet iota) (F : FermiPhaseLine iota) :
    eikonalDeriv₂ L F.gradJet 0 =
      L.G₂ 0 (some F.i1) (some F.i1)
        + (∑ i, 2 * L.G₁ 0 (some i) (some F.i1) * F.transverse i)
        + (∑ i, 2 * L.G₁ 0 (some F.i1) (some i) * F.transverse i)
        + L.G 0 none (some F.i1) * (2 * F.longitudinal)
        + (∑ j, (∑ i, 2 * L.G 0 (some i) (some j) * F.transverse i) * F.transverse j)
        + L.G 0 (some F.i1) none * (2 * F.longitudinal) := by
  have hS1 : (∑ a : Option iota, ∑ b : Option iota,
      L.G₂ 0 a b * F.gradJet.g a 0 * F.gradJet.g b 0)
        = L.G₂ 0 (some F.i1) (some F.i1) := by
    calc (∑ a : Option iota, ∑ b : Option iota,
          L.G₂ 0 a b * F.gradJet.g a 0 * F.gradJet.g b 0)
        = ∑ a : Option iota, L.G₂ 0 a (some F.i1) * F.gradJet.g a 0 :=
          Finset.sum_congr rfl fun a _ =>
            F.sum_mul_g_zero (fun b => L.G₂ 0 a b * F.gradJet.g a 0)
      _ = L.G₂ 0 (some F.i1) (some F.i1) := F.sum_mul_g_zero _
  have hS2 : (∑ a : Option iota, ∑ b : Option iota,
      2 * L.G₁ 0 a b * F.gradJet.g₁ a 0 * F.gradJet.g b 0)
        = ∑ i, 2 * L.G₁ 0 (some i) (some F.i1) * F.transverse i := by
    calc (∑ a : Option iota, ∑ b : Option iota,
          2 * L.G₁ 0 a b * F.gradJet.g₁ a 0 * F.gradJet.g b 0)
        = ∑ a : Option iota, 2 * L.G₁ 0 a (some F.i1) * F.gradJet.g₁ a 0 :=
          Finset.sum_congr rfl fun a _ =>
            F.sum_mul_g_zero (fun b => 2 * L.G₁ 0 a b * F.gradJet.g₁ a 0)
      _ = ∑ i, 2 * L.G₁ 0 (some i) (some F.i1) * F.transverse i := F.sum_mul_g₁_zero _
  have hS3 : (∑ a : Option iota, ∑ b : Option iota,
      2 * L.G₁ 0 a b * F.gradJet.g a 0 * F.gradJet.g₁ b 0)
        = ∑ i, 2 * L.G₁ 0 (some F.i1) (some i) * F.transverse i := by
    rw [Finset.sum_comm]
    calc (∑ b : Option iota, ∑ a : Option iota,
          2 * L.G₁ 0 a b * F.gradJet.g a 0 * F.gradJet.g₁ b 0)
        = ∑ b : Option iota, 2 * L.G₁ 0 (some F.i1) b * F.gradJet.g₁ b 0 := by
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [← Finset.sum_mul, F.sum_mul_g_zero (fun a => 2 * L.G₁ 0 a b)]
      _ = ∑ i, 2 * L.G₁ 0 (some F.i1) (some i) * F.transverse i := F.sum_mul_g₁_zero _
  have hS4 : (∑ a : Option iota, ∑ b : Option iota,
      L.G 0 a b * F.gradJet.g₂ a 0 * F.gradJet.g b 0)
        = L.G 0 none (some F.i1) * (2 * F.longitudinal) := by
    calc (∑ a : Option iota, ∑ b : Option iota,
          L.G 0 a b * F.gradJet.g₂ a 0 * F.gradJet.g b 0)
        = ∑ a : Option iota, L.G 0 a (some F.i1) * F.gradJet.g₂ a 0 :=
          Finset.sum_congr rfl fun a _ =>
            F.sum_mul_g_zero (fun b => L.G 0 a b * F.gradJet.g₂ a 0)
      _ = L.G 0 none (some F.i1) * (2 * F.longitudinal) := F.sum_mul_g₂_zero _
  have hS5 : (∑ a : Option iota, ∑ b : Option iota,
      2 * L.G 0 a b * F.gradJet.g₁ a 0 * F.gradJet.g₁ b 0)
        = ∑ j, (∑ i, 2 * L.G 0 (some i) (some j) * F.transverse i) * F.transverse j := by
    rw [Finset.sum_comm]
    calc (∑ b : Option iota, ∑ a : Option iota,
          2 * L.G 0 a b * F.gradJet.g₁ a 0 * F.gradJet.g₁ b 0)
        = ∑ b : Option iota,
            (∑ a : Option iota, 2 * L.G 0 a b * F.gradJet.g₁ a 0) * F.gradJet.g₁ b 0 := by
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [← Finset.sum_mul]
      _ = ∑ b : Option iota,
            (∑ i, 2 * L.G 0 (some i) b * F.transverse i) * F.gradJet.g₁ b 0 := by
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [F.sum_mul_g₁_zero (fun a => 2 * L.G 0 a b)]
      _ = ∑ j, (∑ i, 2 * L.G 0 (some i) (some j) * F.transverse i) * F.transverse j :=
          F.sum_mul_g₁_zero _
  have hS6 : (∑ a : Option iota, ∑ b : Option iota,
      L.G 0 a b * F.gradJet.g a 0 * F.gradJet.g₂ b 0)
        = L.G 0 (some F.i1) none * (2 * F.longitudinal) := by
    rw [Finset.sum_comm]
    calc (∑ b : Option iota, ∑ a : Option iota,
          L.G 0 a b * F.gradJet.g a 0 * F.gradJet.g₂ b 0)
        = ∑ b : Option iota, L.G 0 (some F.i1) b * F.gradJet.g₂ b 0 := by
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [← Finset.sum_mul, F.sum_mul_g_zero (fun a => L.G 0 a b)]
      _ = L.G 0 (some F.i1) none * (2 * F.longitudinal) := F.sum_mul_g₂_zero _
  simp only [eikonalDeriv₂, Finset.sum_add_distrib]
  rw [hS1, hS2, hS3, hS4, hS5, hS6]

/-! ## The source's Fermi normalization and equation (3.8)

These are the normalizations of the null Fermi chart used in Section 3 of the
source (and in the references it follows): on the geodesic the inverse metric
pairs `tau` with `z^1`, the whole `z^1` row vanishes to first order, the
transverse block is the paper's `C/2`, and the transverse Hessian of `g^{11}`
is the paper's `4 D`. -/

structure FermiNormalization (L : MetricLineJet iota) (F : FermiPhaseLine iota)
    (C D : Matrix iota iota Complex) : Prop where
  /-- `g^{tau z^1}(tau, 0) = 1`. -/
  pairingNormalized : L.G 0 none (some F.i1) = 1
  /-- `g^{z^1 z^i}(tau, 0) = 0`: the geodesic is null and `z^1` is conjugate
  to `tau`. -/
  nullRow : ∀ i, L.G 0 (some F.i1) (some i) = 0
  /-- `d_w g^{z^1 z^i}(tau, 0) = 0`. -/
  nullRowDeriv : ∀ i, L.G₁ 0 (some F.i1) (some i) = 0
  /-- `(g^{z^i z^j}(tau,0)) = C/2` with the paper's `C_{11} = 0`,
  `C_{ii} = 2`, `C_{ij} = 0`. -/
  transverseMetric : ∀ i j, L.G 0 (some i) (some j) = C i j / 2
  /-- `d^2_w g^{z^1 z^1}(tau, 0) = 4 w^T D w`, the paper's
  `D_{ij} = (1/4) d^2_{ij} g^{11}`. -/
  hessianOfG11 : L.G₂ 0 (some F.i1) (some F.i1) = 4 * quadForm D F.dir
  /-- The phase Hessian is symmetric. -/
  phaseSymmetric : F.Mᵀ = F.M

/-- The eikonal symbol vanishes on the geodesic: the beam centre is a null
curve. -/
theorem eikonal_center_eq_zero {L : MetricLineJet iota} {F : FermiPhaseLine iota}
    {C D : Matrix iota iota Complex} (hN : FermiNormalization L F C D) :
    eikonal L F.gradJet 0 = 0 := by
  rw [eikonal_center_raw, hN.nullRow F.i1]

/-- The first transverse derivative of the eikonal symbol vanishes. -/
theorem eikonal_firstJet_eq_zero {L : MetricLineJet iota} {F : FermiPhaseLine iota}
    {C D : Matrix iota iota Complex} (hN : FermiNormalization L F C D) :
    eikonalDeriv L F.gradJet 0 = 0 := by
  rw [eikonalDeriv_center_raw]
  have h1 : L.G₁ 0 (some F.i1) (some F.i1) = 0 := hN.nullRowDeriv F.i1
  have h2 : (∑ i, L.G 0 (some i) (some F.i1) * F.transverse i) = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [L.symm 0 (some i) (some F.i1), hN.nullRow i, zero_mul]
  have h3 : (∑ i, L.G 0 (some F.i1) (some i) * F.transverse i) = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [hN.nullRow i, zero_mul]
  rw [h1, h2, h3]
  ring

/-- **Equation (3.8) from the metric.**  The second transverse derivative of
the eikonal symbol at the beam centre is `4 w^T (M' + M C M + D) w`, with
the paper's own `C` and `D`.  Everything on the right is the Riccati
expression of the source's equation (3.8). -/
theorem eikonal_secondJet_eq {L : MetricLineJet iota} {F : FermiPhaseLine iota}
    {C D : Matrix iota iota Complex} (hN : FermiNormalization L F C D) :
    eikonalDeriv₂ L F.gradJet 0 =
      4 * quadForm (F.dM + F.M * C * F.M + D) F.dir := by
  rw [eikonalDeriv₂_center_raw]
  have h2 : (∑ i, 2 * L.G₁ 0 (some i) (some F.i1) * F.transverse i) = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [L.symm₁ 0 (some i) (some F.i1), hN.nullRowDeriv i, mul_zero, zero_mul]
  have h3 : (∑ i, 2 * L.G₁ 0 (some F.i1) (some i) * F.transverse i) = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [hN.nullRowDeriv i, mul_zero, zero_mul]
  have h6 : L.G 0 (some F.i1) none = 1 := by
    rw [L.symm 0 (some F.i1) none, hN.pairingNormalized]
  have h5 : (∑ j, (∑ i, 2 * L.G 0 (some i) (some j) * F.transverse i) * F.transverse j)
      = 4 * quadForm (F.M * C * F.M) F.dir := by
    have hstep : ∀ j : iota,
        (∑ i, 2 * L.G 0 (some i) (some j) * F.transverse i) * F.transverse j
          = ∑ i, C i j * F.transverse i * F.transverse j := by
      intro j
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hN.transverseMetric i j]
      ring
    rw [Finset.sum_congr rfl fun j _ => hstep j, Finset.sum_comm]
    have hquad : (∑ i, ∑ j, C i j * F.transverse i * F.transverse j)
        = quadForm C F.transverse := (quadForm_eq_sum C F.transverse).symm
    rw [hquad]
    have hscale : F.transverse = fun i => 2 * (F.M *ᵥ F.dir) i := rfl
    rw [hscale, quadForm_const_mul, quadForm_mulVec, hN.phaseSymmetric]
    ring
  rw [h2, h3, h5, h6, hN.pairingNormalized, hN.hessianOfG11]
  rw [quadForm_add_matrix, quadForm_add_matrix]
  show _ = 4 * (quadForm F.dM F.dir + quadForm (F.M * C * F.M) F.dir + quadForm D F.dir)
  simp only [FermiPhaseLine.longitudinal]
  ring

/-- If the paper's Riccati equation (3.8) holds, the transverse second jet of
the eikonal symbol vanishes in the chosen direction. -/
theorem eikonal_secondJet_eq_zero_of_riccati {L : MetricLineJet iota}
    {F : FermiPhaseLine iota} {C D : Matrix iota iota Complex}
    (hN : FermiNormalization L F C D)
    (hriccati : F.dM + F.M * C * F.M + D = 0) :
    eikonalDeriv₂ L F.gradJet 0 = 0 := by
  rw [eikonal_secondJet_eq hN, hriccati]
  simp [quadForm, bilinForm]

/-! ## Converse: the Riccati equation is forced by the eikonal condition -/

theorem eq_zero_of_quadForm_real_eq_zero {A : Matrix iota iota Complex}
    (hsymm : ∀ i j, A i j = A j i)
    (h : ∀ w : iota -> Real, quadForm A (fun i => ((w i : Real) : Complex)) = 0) :
    A = 0 := by
  have hbasis : ∀ k : iota,
      (fun i => (((if i = k then (1 : Real) else 0) : Real) : Complex)) = basisVector k := by
    intro k
    funext i
    by_cases hik : i = k <;> simp [basisVector, Pi.single_apply, hik]
  have hdiag : ∀ k : iota, A k k = 0 := by
    intro k
    have hk := h (fun i => if i = k then (1 : Real) else 0)
    rw [hbasis k, quadForm, bilinForm_basisVector] at hk
    exact hk
  ext i j
  have hsum := h (fun l => (if l = i then (1 : Real) else 0) + (if l = j then (1 : Real) else 0))
  have hrw : (fun l => ((((if l = i then (1 : Real) else 0)
        + (if l = j then (1 : Real) else 0)) : Real) : Complex))
      = basisVector i + basisVector j := by
    funext l
    have h1 := congrFun (hbasis i) l
    have h2 := congrFun (hbasis j) l
    simp only [Complex.ofReal_add, Pi.add_apply]
    rw [h1, h2]
  rw [hrw, quadForm, bilinForm_add_left, bilinForm_add_right, bilinForm_add_right,
    bilinForm_basisVector, bilinForm_basisVector, bilinForm_basisVector,
    bilinForm_basisVector, hdiag i, hdiag j, hsymm j i] at hsum
  have htwo : (2 : Complex) * A i j = 0 := by linear_combination hsum
  have h2 : (2 : Complex) ≠ 0 := two_ne_zero
  simpa using (mul_eq_zero.mp htwo).resolve_left h2

/-- A family of transverse lines through one beam point: one `C^2` metric
line jet per real direction, all normalized by the same paper coefficients
`C` and `D`. -/
structure FermiEikonalFamily (iota : Type*) [Fintype iota] [DecidableEq iota] where
  i1 : iota
  M : Matrix iota iota Complex
  dM : Matrix iota iota Complex
  C : Matrix iota iota Complex
  D : Matrix iota iota Complex
  line : (iota -> Real) -> MetricLineJet iota
  Msymm : Mᵀ = M
  dMsymm : dMᵀ = dM
  Csymm : Cᵀ = C
  Dsymm : Dᵀ = D
  normalized : ∀ w : iota -> Real,
    FermiNormalization (line w) ⟨i1, M, dM, w⟩ C D

namespace FermiEikonalFamily

variable (fam : FermiEikonalFamily iota)

/-- The phase line in direction `w`. -/
def phaseLine (w : iota -> Real) : FermiPhaseLine iota := ⟨fam.i1, fam.M, fam.dM, w⟩

/-- The Riccati expression of equation (3.8). -/
def riccatiDefect : Matrix iota iota Complex :=
  fam.dM + fam.M * fam.C * fam.M + fam.D

theorem riccatiDefect_transpose : fam.riccatiDefectᵀ = fam.riccatiDefect := by
  simp only [riccatiDefect, Matrix.transpose_add, Matrix.transpose_mul, fam.dMsymm,
    fam.Dsymm, fam.Csymm, fam.Msymm]
  rw [Matrix.mul_assoc]

theorem riccatiDefect_symm (i j : iota) :
    fam.riccatiDefect i j = fam.riccatiDefect j i := by
  have h := congrFun (congrFun fam.riccatiDefect_transpose i) j
  simpa [Matrix.transpose_apply] using h.symm

/-- **The eikonal condition forces equation (3.8).**  If the transverse
second jet of the eikonal symbol vanishes in every real direction, then the
phase Hessian satisfies the paper's matrix Riccati equation. -/
theorem riccati_of_eikonal_secondJet_eq_zero
    (hzero : ∀ w : iota -> Real,
      eikonalDeriv₂ (fam.line w) (fam.phaseLine w).gradJet 0 = 0) :
    fam.dM + fam.M * fam.C * fam.M + fam.D = 0 := by
  refine eq_zero_of_quadForm_real_eq_zero fam.riccatiDefect_symm fun w => ?_
  have hjet := eikonal_secondJet_eq (fam.normalized w)
  have hz : eikonalDeriv₂ (fam.line w)
      (FermiPhaseLine.mk fam.i1 fam.M fam.dM w).gradJet 0 = 0 := hzero w
  rw [hz] at hjet
  have hfour : (4 : Complex) ≠ 0 := by norm_num
  have hq : quadForm (fam.dM + fam.M * fam.C * fam.M + fam.D)
      (FermiPhaseLine.dir ⟨fam.i1, fam.M, fam.dM, w⟩) = 0 := by
    have := hjet.symm
    exact (mul_eq_zero.mp this).resolve_left hfour
  simpa [riccatiDefect, FermiPhaseLine.dir] using hq

end FermiEikonalFamily

/-! ## Bridges to the existing Riccati modules -/

open LiuWang2025SemilinearWaveRiccatiPhase LiuWang2025SemilinearWaveRiccatiFlow

/-- The pointwise linearized Riccati packet supplies the eikonal condition:
for the phase Hessian `H = Z Y^{-1}` of the source's linearization, the
transverse second jet of the eikonal symbol vanishes. -/
theorem eikonal_secondJet_eq_zero_of_riccatiPoint
    {L : MetricLineJet iota} {F : FermiPhaseLine iota}
    {C D : Matrix iota iota Complex} (hN : FermiNormalization L F C D)
    (data : RiccatiPointData iota)
    (hM : F.M = data.H) (hdM : F.dM = data.dH)
    (hC : C = data.C) (hD : D = data.D) :
    eikonalDeriv₂ L F.gradJet 0 = 0 := by
  refine eikonal_secondJet_eq_zero_of_riccati hN ?_
  rw [hM, hdM, hC, hD]
  exact data.equation38

/-- Interval version: the propagated Riccati flow supplies the eikonal
condition at every point of the geodesic interval. -/
theorem eikonal_secondJet_eq_zero_of_riccatiFlow
    {L : MetricLineJet iota} {F : FermiPhaseLine iota}
    {C D : Matrix iota iota Complex} (hN : FermiNormalization L F C D)
    (flow : RiccatiFlow iota) {t : Real}
    (ht : t ∈ Set.uIcc flow.startTime flow.endTime)
    (hM : F.M = flow.H t) (hdM : F.dM = flow.dH t)
    (hC : C = flow.C t) (hD : D = flow.D t) :
    eikonalDeriv₂ L F.gradJet 0 = 0 := by
  refine eikonal_secondJet_eq_zero_of_riccati hN ?_
  rw [hM, hdM, hC, hD]
  exact flow.equation38 ht

/-! ## The transport operator at the beam centre

The source's WKB expansion is

`Box_g (a e^{i rho phi}) = e^{i rho phi} (rho^2 (S phi) a - i rho (T a) + Box_g a)`,
`S phi = <d phi, d phi>_g`,  `T a = 2 <d phi, d a>_g - (Box_g phi) a`.

The previous sections handled `S phi`.  This section evaluates `T a` on the
geodesic itself, where `d phi = dz^1`.  The result is the scalar transport ODE
consumed by the existing integrating-factor module. -/

/-- Geometric data at the beam centre.  `G` is the inverse metric on the
geodesic, `beta` the first-order coefficient of `Box_g` in the Fermi chart
(so that `Box_g F = sum_{ab} g^{ab} d_a d_b F + sum_b beta^b d_b F`), `M` the
phase Hessian and `C` the paper's transverse coefficient matrix. -/
structure TransportCenterGeometry (iota : Type*) [Fintype iota] [DecidableEq iota] where
  i1 : iota
  C : Matrix iota iota Complex
  M : Matrix iota iota Complex
  G : Option iota -> Option iota -> Complex
  beta : Option iota -> Complex
  Gsymm : ∀ a b, G a b = G b a
  pairingNormalized : G none (some i1) = 1
  nullRow : ∀ i, G (some i1) (some i) = 0
  transverseMetric : ∀ i j, G (some i) (some j) = C i j / 2
  phaseSymmetric : ∀ i j, M i j = M j i

namespace TransportCenterGeometry

variable (g : TransportCenterGeometry iota)

/-- `d phi` at the beam centre is the covector `dz^1`. -/
def gradPhase : Option iota -> Complex := fun a => if a = some g.i1 then 1 else 0

/-- `d^2 phi` at the beam centre: `2 M_{ij}` on the transverse block, zero in
the `tau` slots. -/
def hessPhase : Option iota -> Option iota -> Complex := fun a b =>
  a.elim 0 (fun i => b.elim 0 (fun j => 2 * g.M i j))

/-- `Box_g phi` at the beam centre. -/
def boxPhase : Complex :=
  (∑ a : Option iota, ∑ b : Option iota, g.G a b * g.hessPhase a b)
    + ∑ b : Option iota, g.beta b * g.gradPhase b

/-- The source's transport operator `T a = 2 <d phi, d a>_g - (Box_g phi) a`
at the beam centre, for an amplitude of value `amp` with chart derivatives
`dAmp`. -/
def transport (amp : Complex) (dAmp : Option iota -> Complex) : Complex :=
  2 * (∑ a : Option iota, ∑ b : Option iota, g.G a b * g.gradPhase a * dAmp b)
    - g.boxPhase * amp

/-- The paper's scalar transport coefficient on the geodesic. -/
def transportCoefficient : Complex :=
  -(Matrix.trace (g.C * g.M) + g.beta (some g.i1))

theorem boxPhase_eq :
    g.boxPhase = Matrix.trace (g.C * g.M) + g.beta (some g.i1) := by
  have hhess : (∑ a : Option iota, ∑ b : Option iota, g.G a b * g.hessPhase a b)
      = Matrix.trace (g.C * g.M) := by
    have hinner : ∀ a : Option iota,
        (∑ b : Option iota, g.G a b * g.hessPhase a b)
          = a.elim 0 (fun i => ∑ j, g.G (some i) (some j) * (2 * g.M i j)) := by
      intro a
      cases a with
      | none => simp [hessPhase]
      | some i => simp [hessPhase]
    rw [Finset.sum_congr rfl fun a _ => hinner a, Fintype.sum_option]
    simp only [Option.elim_none, Option.elim_some, zero_add]
    rw [Matrix.trace]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.diag_apply, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [g.transverseMetric i j, g.phaseSymmetric j i]
    ring
  have hbeta : (∑ b : Option iota, g.beta b * g.gradPhase b) = g.beta (some g.i1) := by
    simp [gradPhase, mul_ite, Finset.sum_ite_eq']
  rw [boxPhase, hhess, hbeta]

theorem pairing_eq (dAmp : Option iota -> Complex) :
    (∑ a : Option iota, ∑ b : Option iota, g.G a b * g.gradPhase a * dAmp b)
      = dAmp none := by
  have hinner : ∀ a : Option iota,
      (∑ b : Option iota, g.G a b * g.gradPhase a * dAmp b)
        = g.gradPhase a * ∑ b : Option iota, g.G a b * dAmp b := by
    intro a
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ => by ring
  rw [Finset.sum_congr rfl fun a _ => hinner a]
  have hdelta : (∑ a : Option iota, g.gradPhase a * ∑ b : Option iota, g.G a b * dAmp b)
      = ∑ b : Option iota, g.G (some g.i1) b * dAmp b := by
    simp [gradPhase, ite_mul, Finset.sum_ite_eq']
  rw [hdelta, Fintype.sum_option]
  have hzero : (∑ i, g.G (some g.i1) (some i) * dAmp (some i)) = 0 :=
    Finset.sum_eq_zero fun i _ => by rw [g.nullRow i, zero_mul]
  rw [hzero, g.Gsymm (some g.i1) none, g.pairingNormalized, add_zero, one_mul]

/-- **The source transport equation on the geodesic.**  With the Fermi
normalization, `T a` at the beam centre is the scalar expression
`2 a' - (Tr(C M) + beta_1) a`. -/
theorem transport_eq (amp : Complex) (dAmp : Option iota -> Complex) :
    g.transport amp dAmp
      = 2 * dAmp none - (Matrix.trace (g.C * g.M) + g.beta (some g.i1)) * amp := by
  rw [transport, g.pairing_eq dAmp, g.boxPhase_eq]

theorem transport_eq_zero_iff (amp : Complex) (dAmp : Option iota -> Complex) :
    g.transport amp dAmp = 0 ↔ 2 * dAmp none + g.transportCoefficient * amp = 0 := by
  rw [transport_eq, transportCoefficient]
  constructor <;> intro h <;> linear_combination h

end TransportCenterGeometry

/-! ## The geometric transport coefficient drives the existing amplitude -/

open LiuWang2025SemilinearWaveLeadingAmplitudeTransport

/-- Everything the source needs from the leading amplitude along one geodesic:
the scalar coefficient is the geometric one, the explicit integrating-factor
amplitude has the stated derivative, it solves the Fermi transport equation at
the beam centre for every choice of transverse amplitude derivatives, and it
never vanishes. -/
structure FermiTransportCertificate
    (geom : Real -> TransportCenterGeometry iota) (q : Real -> Complex)
    (tau0 : Real) (initial : Complex) : Prop where
  coefficientIsGeometric : ∀ tau, q tau = (geom tau).transportCoefficient
  hasDerivative : ∀ tau, HasDerivAt (leadingAmplitude q tau0 initial)
    (-((2 : Complex)⁻¹) * q tau * leadingAmplitude q tau0 initial tau) tau
  solvesTransport : ∀ (tau : Real) (dAmp : Option iota -> Complex),
    dAmp none = -((2 : Complex)⁻¹) * q tau * leadingAmplitude q tau0 initial tau ->
    (geom tau).transport (leadingAmplitude q tau0 initial tau) dAmp = 0
  neverVanishes : ∀ tau, leadingAmplitude q tau0 initial tau ≠ 0

/-- Construction of the certificate.  Only continuity of the geometric
coefficient and nonvanishing of the initial amplitude are required. -/
def fermiTransportCertificate
    (geom : Real -> TransportCenterGeometry iota) (q : Real -> Complex)
    (hq : Continuous q) (tau0 : Real) {initial : Complex} (hinitial : initial ≠ 0)
    (hcoef : ∀ tau, q tau = (geom tau).transportCoefficient) :
    FermiTransportCertificate geom q tau0 initial where
  coefficientIsGeometric := hcoef
  hasDerivative := fun tau => leadingAmplitude_hasDerivAt q hq tau0 initial tau
  solvesTransport := by
    intro tau dAmp hd
    rw [(geom tau).transport_eq_zero_iff, hd, ← hcoef tau]
    ring
  neverVanishes := fun tau => leadingAmplitude_ne_zero q tau0 hinitial tau

end LiuWang2025SemilinearWaveFermiEikonalJet



