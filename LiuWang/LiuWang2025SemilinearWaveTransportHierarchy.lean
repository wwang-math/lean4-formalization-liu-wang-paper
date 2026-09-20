import LiuWang.LiuWang2025SemilinearWaveFermiEikonalJet

/-!
# Liu--Wang 2025: the full WKB amplitude hierarchy on the geodesic

Source: Boya Liu and Weinan Wang, *On a partial data inverse problem for the
semi-linear wave equation*, arXiv:2511.08794v1, Section 3.

The source's Gaussian beam is built from the expansion

`Box_g (a_rho e^{i rho phi}) = e^{i rho phi}
   (rho^2 (S phi) a_rho - i rho (T a_rho) + Box_g a_rho)`

together with the requirements, on the geodesic and to the required jet order,

`S phi = 0`,  `T a_0 = 0`,  `- i T a_k + Box_g a_{k-1} = 0`  (`k >= 1`).

`LiuWang2025SemilinearWaveFermiEikonalJet` derives the first two from the
Fermi-chart metric: the eikonal condition becomes the paper's Riccati
equation (3.8), and `T a |_{z=0} = 2 a' - (Tr(C M) + beta_1) a`, so that
`T a_0 = 0` is the scalar homogeneous transport equation `2 a_0' + q a_0 = 0`
solved by the existing integrating-factor amplitude.

This module closes the *recursive* part.  For a continuous coefficient `q` and
a continuous right-hand side, Lean constructs the explicit variation-of-
constants solution of the inhomogeneous transport equation

`2 a' + q a = f`,

verifies from actual derivatives that it solves that equation and takes the
prescribed value at the initial parameter, and iterates the construction to
produce the whole source hierarchy `a_0, a_1, a_2, ...` with

`2 a_0' + q a_0 = 0`,   `2 a_k' + q a_k = -i (Box_g a_{k-1})|_{z=0}`,

which is exactly the displayed recursion, written through the beam-centre
transport operator of the Fermi module.

## Scope

The data `boxSource k` records the value on the geodesic of `Box_g a_k`, the
chart wave operator applied to the previous amplitude.  Computing it from the
constructed amplitudes and the chart is geometric work and is not done here;
everything else in the recursion -- existence, the explicit solution formula,
the initial value, the differential equation, and nonvanishing of the leading
amplitude -- is proved.
-/

noncomputable section

open Filter Topology MeasureTheory

namespace LiuWang2025SemilinearWaveTransportHierarchy

open LiuWang2025SemilinearWaveLeadingAmplitudeTransport
open LiuWang2025SemilinearWaveFermiEikonalJet

/-! ## The integrating factor -/

/-- `s |-> integral_{s0}^{s} q` is differentiable with derivative `q`. -/
theorem hasDerivAt_primitive {q : Real -> Complex} (hq : Continuous q)
    (s0 s : Real) : HasDerivAt (fun u => ∫ t in s0..u, q t) (q s) s :=
  intervalIntegral.integral_hasDerivAt_right (hq.intervalIntegrable _ _)
    hq.aestronglyMeasurable.stronglyMeasurableAtFilter hq.continuousAt

theorem continuous_primitive {q : Real -> Complex} (hq : Continuous q)
    (s0 : Real) : Continuous (fun u => ∫ t in s0..u, q t) :=
  continuous_iff_continuousAt.mpr fun s => (hasDerivAt_primitive hq s0 s).continuousAt

/-- The homogeneous solution normalized to `1` at `s0`. -/
def homogeneousFactor (q : Real -> Complex) (s0 s : Real) : Complex :=
  Complex.exp (-((2 : Complex))⁻¹ * ∫ t in s0..s, q t)

/-- Its reciprocal, the integrating factor. -/
def inverseFactor (q : Real -> Complex) (s0 s : Real) : Complex :=
  Complex.exp (((2 : Complex))⁻¹ * ∫ t in s0..s, q t)

@[simp] theorem homogeneousFactor_self (q : Real -> Complex) (s0 : Real) :
    homogeneousFactor q s0 s0 = 1 := by
  simp [homogeneousFactor]

@[simp] theorem inverseFactor_self (q : Real -> Complex) (s0 : Real) :
    inverseFactor q s0 s0 = 1 := by
  simp [inverseFactor]

theorem homogeneousFactor_ne_zero (q : Real -> Complex) (s0 s : Real) :
    homogeneousFactor q s0 s ≠ 0 := Complex.exp_ne_zero _

@[simp] theorem homogeneousFactor_mul_inverseFactor
    (q : Real -> Complex) (s0 s : Real) :
    homogeneousFactor q s0 s * inverseFactor q s0 s = 1 := by
  rw [homogeneousFactor, inverseFactor, ← Complex.exp_add]
  simp

/-- The homogeneous factor is the normalized leading amplitude of the existing
transport module. -/
theorem homogeneousFactor_eq_leadingAmplitude
    (q : Real -> Complex) (s0 s : Real) :
    homogeneousFactor q s0 s = leadingAmplitude q s0 1 s := by
  simp [homogeneousFactor, leadingAmplitude]

theorem hasDerivAt_homogeneousFactor {q : Real -> Complex} (hq : Continuous q)
    (s0 s : Real) :
    HasDerivAt (homogeneousFactor q s0)
      (-((2 : Complex))⁻¹ * q s * homogeneousFactor q s0 s) s := by
  have hExponent : HasDerivAt (fun u => -((2 : Complex))⁻¹ * ∫ t in s0..u, q t)
      (-((2 : Complex))⁻¹ * q s) s :=
    (hasDerivAt_primitive hq s0 s).const_mul _
  have h := hExponent.cexp
  refine h.congr_deriv ?_
  rw [homogeneousFactor]
  ring

theorem continuous_inverseFactor {q : Real -> Complex} (hq : Continuous q)
    (s0 : Real) : Continuous (inverseFactor q s0) := by
  refine Complex.continuous_exp.comp ?_
  exact continuous_const.mul (continuous_primitive hq s0)

/-! ## Variation of constants for `2 a' + q a = f` -/

/-- Explicit variation-of-constants solution of the source's inhomogeneous
transport equation `2 a' + q a = f` with `a(s0) = initial`. -/
def hierarchyAmplitude (q f : Real -> Complex) (s0 : Real)
    (initial : Complex) (s : Real) : Complex :=
  homogeneousFactor q s0 s *
    (initial + ((2 : Complex))⁻¹ * ∫ t in s0..s, inverseFactor q s0 t * f t)

@[simp] theorem hierarchyAmplitude_at_initial (q f : Real -> Complex)
    (s0 : Real) (initial : Complex) :
    hierarchyAmplitude q f s0 initial s0 = initial := by
  simp [hierarchyAmplitude]

theorem hierarchyAmplitude_hasDerivAt {q f : Real -> Complex}
    (hq : Continuous q) (hf : Continuous f) (s0 : Real) (initial : Complex)
    (s : Real) :
    HasDerivAt (hierarchyAmplitude q f s0 initial)
      (-((2 : Complex))⁻¹ * q s * hierarchyAmplitude q f s0 initial s
        + ((2 : Complex))⁻¹ * f s) s := by
  have hint : Continuous (fun t => inverseFactor q s0 t * f t) :=
    (continuous_inverseFactor hq s0).mul hf
  have hJ : HasDerivAt (fun u => ∫ t in s0..u, inverseFactor q s0 t * f t)
      (inverseFactor q s0 s * f s) s :=
    intervalIntegral.integral_hasDerivAt_right (hint.intervalIntegrable _ _)
      hint.aestronglyMeasurable.stronglyMeasurableAtFilter hint.continuousAt
  have hInner : HasDerivAt
      (fun u => initial + ((2 : Complex))⁻¹ * ∫ t in s0..u, inverseFactor q s0 t * f t)
      (((2 : Complex))⁻¹ * (inverseFactor q s0 s * f s)) s :=
    (hJ.const_mul _).const_add _
  have hprod := (hasDerivAt_homogeneousFactor hq s0 s).mul hInner
  refine hprod.congr_deriv ?_
  have hEinv : homogeneousFactor q s0 s * inverseFactor q s0 s = 1 :=
    homogeneousFactor_mul_inverseFactor q s0 s
  rw [hierarchyAmplitude]
  have hexpand : homogeneousFactor q s0 s *
      (((2 : Complex))⁻¹ * (inverseFactor q s0 s * f s))
        = ((2 : Complex))⁻¹ * f s := by
    calc homogeneousFactor q s0 s * (((2 : Complex))⁻¹ * (inverseFactor q s0 s * f s))
        = (homogeneousFactor q s0 s * inverseFactor q s0 s) * (((2 : Complex))⁻¹ * f s) := by
          ring
      _ = ((2 : Complex))⁻¹ * f s := by rw [hEinv, one_mul]
  rw [hexpand]
  ring

/-- **The inhomogeneous transport equation is solved exactly.** -/
theorem hierarchyAmplitude_solves {q f : Real -> Complex}
    (_hq : Continuous q) (_hf : Continuous f) (s0 : Real) (initial : Complex)
    (s : Real) :
    2 * (-((2 : Complex))⁻¹ * q s * hierarchyAmplitude q f s0 initial s
        + ((2 : Complex))⁻¹ * f s)
      + q s * hierarchyAmplitude q f s0 initial s = f s := by
  ring

theorem continuous_hierarchyAmplitude {q f : Real -> Complex}
    (hq : Continuous q) (hf : Continuous f) (s0 : Real) (initial : Complex) :
    Continuous (hierarchyAmplitude q f s0 initial) :=
  continuous_iff_continuousAt.mpr fun s =>
    (hierarchyAmplitude_hasDerivAt hq hf s0 initial s).continuousAt

/-! ## The source hierarchy -/

/-- The source's WKB amplitude hierarchy on the geodesic.  `a_0` solves the
homogeneous transport equation and each `a_{k+1}` solves
`2 a' + q a = -i (Box_g a_k)|_{z=0}`. -/
def amplitude (q : Real -> Complex) (s0 : Real) (initial : Nat -> Complex)
    (boxSource : Nat -> Real -> Complex) : Nat -> Real -> Complex
  | 0 => leadingAmplitude q s0 (initial 0)
  | (k + 1) =>
      hierarchyAmplitude q (fun s => -Complex.I * boxSource k s) s0 (initial (k + 1))

@[simp] theorem amplitude_zero (q : Real -> Complex) (s0 : Real)
    (initial : Nat -> Complex) (boxSource : Nat -> Real -> Complex) :
    amplitude q s0 initial boxSource 0 = leadingAmplitude q s0 (initial 0) := rfl

@[simp] theorem amplitude_succ (q : Real -> Complex) (s0 : Real)
    (initial : Nat -> Complex) (boxSource : Nat -> Real -> Complex) (k : Nat) :
    amplitude q s0 initial boxSource (k + 1)
      = hierarchyAmplitude q (fun s => -Complex.I * boxSource k s) s0
          (initial (k + 1)) := rfl

/-- The leading amplitude solves the homogeneous transport equation. -/
theorem amplitude_zero_solves {q : Real -> Complex} (hq : Continuous q)
    (s0 : Real) (initial : Nat -> Complex)
    (boxSource : Nat -> Real -> Complex) (s : Real) :
    HasDerivAt (amplitude q s0 initial boxSource 0)
        (-((2 : Complex))⁻¹ * q s * amplitude q s0 initial boxSource 0 s) s ∧
      2 * (-((2 : Complex))⁻¹ * q s * amplitude q s0 initial boxSource 0 s)
          + q s * amplitude q s0 initial boxSource 0 s = 0 :=
  leadingAmplitude_solves_transport q hq s0 (initial 0) s

/-- **The source's recursion `-i T a_{k+1} + Box_g a_k = 0` on the geodesic.**
The constructed amplitude has the stated derivative and satisfies the
inhomogeneous transport equation with right-hand side `-i (Box_g a_k)`. -/
theorem amplitude_succ_solves {q : Real -> Complex} (hq : Continuous q)
    {boxSource : Nat -> Real -> Complex} (k : Nat)
    (hbox : Continuous (boxSource k)) (s0 : Real) (initial : Nat -> Complex)
    (s : Real) :
    HasDerivAt (amplitude q s0 initial boxSource (k + 1))
        (-((2 : Complex))⁻¹ * q s * amplitude q s0 initial boxSource (k + 1) s
          + ((2 : Complex))⁻¹ * (-Complex.I * boxSource k s)) s ∧
      2 * (-((2 : Complex))⁻¹ * q s * amplitude q s0 initial boxSource (k + 1) s
            + ((2 : Complex))⁻¹ * (-Complex.I * boxSource k s))
          + q s * amplitude q s0 initial boxSource (k + 1) s
        = -Complex.I * boxSource k s := by
  have hf : Continuous (fun s => -Complex.I * boxSource k s) :=
    continuous_const.mul hbox
  exact ⟨hierarchyAmplitude_hasDerivAt hq hf s0 (initial (k + 1)) s,
    hierarchyAmplitude_solves hq hf s0 (initial (k + 1)) s⟩

theorem amplitude_initial_value (q : Real -> Complex) (s0 : Real)
    (initial : Nat -> Complex) (boxSource : Nat -> Real -> Complex) (k : Nat) :
    amplitude q s0 initial boxSource k s0 = initial k := by
  cases k with
  | zero => simp
  | succ k => simp

/-- The leading amplitude never vanishes when its initial value does not. -/
theorem amplitude_zero_ne_zero {q : Real -> Complex} (s0 : Real)
    {initial : Nat -> Complex} (hinitial : initial 0 ≠ 0)
    (boxSource : Nat -> Real -> Complex) (s : Real) :
    amplitude q s0 initial boxSource 0 s ≠ 0 :=
  leadingAmplitude_ne_zero q s0 hinitial s

theorem continuous_amplitude {q : Real -> Complex} (hq : Continuous q)
    {boxSource : Nat -> Real -> Complex} (s0 : Real) (initial : Nat -> Complex)
    (k : Nat) (hbox : ∀ j, Continuous (boxSource j)) :
    Continuous (amplitude q s0 initial boxSource k) := by
  cases k with
  | zero =>
      simpa [amplitude_zero, leadingAmplitude, homogeneousFactor_eq_leadingAmplitude]
        using (continuous_const.mul
          (Complex.continuous_exp.comp
            (continuous_const.mul (continuous_primitive hq s0))))
  | succ k =>
      exact continuous_hierarchyAmplitude hq (continuous_const.mul (hbox k)) s0 _

/-! ## The hierarchy through the Fermi beam-centre transport operator -/

variable {iota : Type*} [Fintype iota] [DecidableEq iota]

/-- Expressed through the beam-centre transport operator of the Fermi module:
the leading amplitude is annihilated by `T`. -/
theorem transport_amplitude_zero {q : Real -> Complex} (_hq : Continuous q)
    (geom : Real -> TransportCenterGeometry iota)
    (hcoef : ∀ tau, q tau = (geom tau).transportCoefficient)
    (s0 : Real) (initial : Nat -> Complex)
    (boxSource : Nat -> Real -> Complex) (tau : Real)
    (dAmp : Option iota -> Complex)
    (hd : dAmp none =
      -((2 : Complex))⁻¹ * q tau * amplitude q s0 initial boxSource 0 tau) :
    (geom tau).transport (amplitude q s0 initial boxSource 0 tau) dAmp = 0 := by
  rw [(geom tau).transport_eq_zero_iff, hd, ← hcoef tau]
  ring

/-- Expressed through the beam-centre transport operator: each higher
amplitude satisfies the paper's recursion `T a_{k+1} = -i (Box_g a_k)`. -/
theorem transport_amplitude_succ {q : Real -> Complex} (_hq : Continuous q)
    (geom : Real -> TransportCenterGeometry iota)
    (hcoef : ∀ tau, q tau = (geom tau).transportCoefficient)
    (s0 : Real) (initial : Nat -> Complex)
    (boxSource : Nat -> Real -> Complex) (k : Nat) (tau : Real)
    (dAmp : Option iota -> Complex)
    (hd : dAmp none =
      -((2 : Complex))⁻¹ * q tau * amplitude q s0 initial boxSource (k + 1) tau
        + ((2 : Complex))⁻¹ * (-Complex.I * boxSource k tau)) :
    (geom tau).transport (amplitude q s0 initial boxSource (k + 1) tau) dAmp
      = -Complex.I * boxSource k tau := by
  rw [(geom tau).transport_eq, hd]
  have hq' : Matrix.trace ((geom tau).C * (geom tau).M)
      + (geom tau).beta (some (geom tau).i1) = -q tau := by
    rw [hcoef tau, TransportCenterGeometry.transportCoefficient]
    ring
  rw [hq']
  ring

/-- One reviewable object collecting the constructed hierarchy. -/
structure Certificate (q : Real -> Complex) (s0 : Real)
    (initial : Nat -> Complex) (boxSource : Nat -> Real -> Complex) : Prop where
  initialValues : ∀ k, amplitude q s0 initial boxSource k s0 = initial k
  leadingTransport : ∀ s,
    2 * (-((2 : Complex))⁻¹ * q s * amplitude q s0 initial boxSource 0 s)
        + q s * amplitude q s0 initial boxSource 0 s = 0
  recursiveTransport : ∀ (k : Nat) (s : Real),
    2 * (-((2 : Complex))⁻¹ * q s * amplitude q s0 initial boxSource (k + 1) s
          + ((2 : Complex))⁻¹ * (-Complex.I * boxSource k s))
        + q s * amplitude q s0 initial boxSource (k + 1) s
      = -Complex.I * boxSource k s
  leadingNonvanishing : ∀ s, amplitude q s0 initial boxSource 0 s ≠ 0

/-- The hierarchy certificate is generated from continuity of the transport
coefficient and of every wave source, plus a nonzero leading initial value. -/
def certificate {q : Real -> Complex} (hq : Continuous q) (s0 : Real)
    {initial : Nat -> Complex} (hinitial : initial 0 ≠ 0)
    {boxSource : Nat -> Real -> Complex} (hbox : ∀ k, Continuous (boxSource k)) :
    Certificate q s0 initial boxSource where
  initialValues := amplitude_initial_value q s0 initial boxSource
  leadingTransport := fun s => (amplitude_zero_solves hq s0 initial boxSource s).2
  recursiveTransport := fun k s =>
    (amplitude_succ_solves hq k (hbox k) s0 initial s).2
  leadingNonvanishing := amplitude_zero_ne_zero s0 hinitial boxSource

end LiuWang2025SemilinearWaveTransportHierarchy
