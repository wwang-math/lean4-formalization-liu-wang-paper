import LiuWang.LiuWang2025SemilinearWaveRiccatiPhase
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Liu--Wang 2025: interval Riccati flow and propagated phase invariants

The pointwise Riccati module checks equation (3.8) and the algebraic
consequences of the symmetric and Hermitian Wronskians.  This module removes
those Wronskians as pointwise assumptions.  For a matrix Hamiltonian flow on a
geodesic interval, it proves directly that both Wronskians have zero
derivative, applies the Banach-valued fundamental theorem of calculus, and
propagates their initial values to every point of the interval.

For a flow initialized by `Y(t0)=1`, `Z(t0)=H0` with positive initial
imaginary Hessian, Lean proves that the conserved Hermitian Wronskian forces
`Y(t)` to be invertible at every interval point.  It then differentiates the
actual quotient `H=Z Y^-1`, constructs equation (3.8) at every time, and
generates the positive-imaginary-phase and determinant certificates consumed
by the WKB hierarchy.

The remaining source-facing analytic inputs are existence of this flow for
the concrete Fermi-coordinate coefficients and the geometric uniform action
bound used for quantitative coercivity.  Invertibility and the conserved
Wronskians are theorems rather than fields.
-/

noncomputable section

open Matrix MeasureTheory Set
open scoped Matrix.Norms.L2Operator

namespace LiuWang2025SemilinearWaveRiccatiFlow

open LiuWang2025SemilinearWaveRiccatiPhase

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Symmetric Wronskian along a matrix path. -/
def symmetricWronskianPath
    (Y Z : Real -> Matrix n n Complex) (t : Real) : Matrix n n Complex :=
  (Y t)ᵀ * Z t - (Z t)ᵀ * Y t

/-- Hermitian Wronskian along a matrix path, before the `-i/2` normalization. -/
def hermitianWronskianPath
    (Y Z : Real -> Matrix n n Complex) (t : Real) : Matrix n n Complex :=
  (Y t)ᴴ * Z t - (Z t)ᴴ * Y t

/-- Matrix transpose as a continuous real-linear equivalence. -/
def transposeContinuousLinearEquiv :
    Matrix n n Complex ≃L[Real] Matrix n n Complex :=
  (Matrix.transposeLinearEquiv n n Real Complex).toContinuousLinearEquiv

theorem hasDerivAt_transpose
    {Y : Real -> Matrix n n Complex} {dY : Matrix n n Complex} {t : Real}
    (hY : HasDerivAt Y dY t) :
    HasDerivAt (fun s => (Y s)ᵀ) dYᵀ t := by
  have hlinear :
      HasFDerivAt (transposeContinuousLinearEquiv (n := n))
        (transposeContinuousLinearEquiv (n := n)).toContinuousLinearMap
        (Y t) :=
    (transposeContinuousLinearEquiv (n := n)).toContinuousLinearMap.hasFDerivAt
  have hcomp := (hlinear.comp t hY.hasFDerivAt).hasDerivAt
  simpa [transposeContinuousLinearEquiv, Function.comp_def] using hcomp

theorem hasDerivAt_conjTranspose
    {Y : Real -> Matrix n n Complex} {dY : Matrix n n Complex} {t : Real}
    (hY : HasDerivAt Y dY t) :
    HasDerivAt (fun s => (Y s)ᴴ) dYᴴ t := by
  simpa only [Matrix.star_eq_conjTranspose] using hY.star

/-- Product-rule derivative of the symmetric Wronskian. -/
theorem hasDerivAt_symmetricWronskianPath
    {Y Z : Real -> Matrix n n Complex}
    {dY dZ : Matrix n n Complex} {t : Real}
    (hY : HasDerivAt Y dY t) (hZ : HasDerivAt Z dZ t) :
    HasDerivAt (symmetricWronskianPath Y Z)
      (symmetricWronskianDerivative (Y t) (Z t) dY dZ) t := by
  have hYt := hasDerivAt_transpose hY
  have hZt := hasDerivAt_transpose hZ
  have hderiv := (hYt.mul hZ).sub (hZt.mul hY)
  convert hderiv using 1
  simp only [symmetricWronskianDerivative]
  noncomm_ring

/-- Product-rule derivative of the Hermitian Wronskian. -/
theorem hasDerivAt_hermitianWronskianPath
    {Y Z : Real -> Matrix n n Complex}
    {dY dZ : Matrix n n Complex} {t : Real}
    (hY : HasDerivAt Y dY t) (hZ : HasDerivAt Z dZ t) :
    HasDerivAt (hermitianWronskianPath Y Z)
      (hermitianWronskianDerivative (Y t) (Z t) dY dZ) t := by
  have hYh := hasDerivAt_conjTranspose hY
  have hZh := hasDerivAt_conjTranspose hZ
  have hderiv := (hYh.mul hZ).sub (hZh.mul hY)
  convert hderiv using 1
  simp only [hermitianWronskianDerivative]
  noncomm_ring

/-- A matrix Hamiltonian flow on one (unordered) geodesic interval. -/
structure LinearHamiltonianFlow (n : Type*) [Fintype n] [DecidableEq n] where
  startTime : Real
  endTime : Real
  C : Real -> Matrix n n Complex
  D : Real -> Matrix n n Complex
  Y : Real -> Matrix n n Complex
  Z : Real -> Matrix n n Complex
  hasDerivY : forall t, t ∈ uIcc startTime endTime ->
    HasDerivAt Y (C t * Z t) t
  hasDerivZ : forall t, t ∈ uIcc startTime endTime ->
    HasDerivAt Z (-D t * Y t) t
  C_symmetric : forall t, t ∈ uIcc startTime endTime -> (C t).IsSymm
  D_symmetric : forall t, t ∈ uIcc startTime endTime -> (D t).IsSymm
  C_hermitian : forall t, t ∈ uIcc startTime endTime -> (C t).IsHermitian
  D_hermitian : forall t, t ∈ uIcc startTime endTime -> (D t).IsHermitian

namespace LinearHamiltonianFlow

theorem symmetricWronskian_hasDerivAt_zero
    (flow : LinearHamiltonianFlow n) {t : Real}
    (ht : t ∈ uIcc flow.startTime flow.endTime) :
    HasDerivAt (symmetricWronskianPath flow.Y flow.Z) 0 t := by
  have hderiv := hasDerivAt_symmetricWronskianPath
    (flow.hasDerivY t ht) (flow.hasDerivZ t ht)
  have hzero := symmetricWronskianDerivative_eq_zero
    (flow.C t) (flow.D t) (flow.Y t) (flow.Z t)
    (flow.C t * flow.Z t) (-flow.D t * flow.Y t)
    (flow.C_symmetric t ht) (flow.D_symmetric t ht) rfl rfl
  rw [hzero] at hderiv
  exact hderiv

theorem hermitianWronskian_hasDerivAt_zero
    (flow : LinearHamiltonianFlow n) {t : Real}
    (ht : t ∈ uIcc flow.startTime flow.endTime) :
    HasDerivAt (hermitianWronskianPath flow.Y flow.Z) 0 t := by
  have hderiv := hasDerivAt_hermitianWronskianPath
    (flow.hasDerivY t ht) (flow.hasDerivZ t ht)
  have hzero := hermitianWronskianDerivative_eq_zero
    (flow.C t) (flow.D t) (flow.Y t) (flow.Z t)
    (flow.C t * flow.Z t) (-flow.D t * flow.Y t)
    (flow.C_hermitian t ht) (flow.D_hermitian t ht) rfl rfl
  rw [hzero] at hderiv
  exact hderiv

/-- The symmetric Wronskian is constant on the whole geodesic interval. -/
theorem symmetricWronskian_eq_start
    (flow : LinearHamiltonianFlow n) {t : Real}
    (ht : t ∈ uIcc flow.startTime flow.endTime) :
    symmetricWronskianPath flow.Y flow.Z t =
      symmetricWronskianPath flow.Y flow.Z flow.startTime := by
  have hsubset : uIcc flow.startTime t ⊆
      uIcc flow.startTime flow.endTime :=
    uIcc_subset_uIcc_left ht
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := flow.startTime) (b := t)
    (f := symmetricWronskianPath flow.Y flow.Z) (f' := fun _ => 0)
    (fun s hs => flow.symmetricWronskian_hasDerivAt_zero (hsubset hs))
    IntervalIntegrable.zero
  have hsub :
      symmetricWronskianPath flow.Y flow.Z t -
        symmetricWronskianPath flow.Y flow.Z flow.startTime = 0 := by
    simpa using hFTC.symm
  exact sub_eq_zero.mp hsub

/-- The Hermitian Wronskian is constant on the whole geodesic interval. -/
theorem hermitianWronskian_eq_start
    (flow : LinearHamiltonianFlow n) {t : Real}
    (ht : t ∈ uIcc flow.startTime flow.endTime) :
    hermitianWronskianPath flow.Y flow.Z t =
      hermitianWronskianPath flow.Y flow.Z flow.startTime := by
  have hsubset : uIcc flow.startTime t ⊆
      uIcc flow.startTime flow.endTime :=
    uIcc_subset_uIcc_left ht
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := flow.startTime) (b := t)
    (f := hermitianWronskianPath flow.Y flow.Z) (f' := fun _ => 0)
    (fun s hs => flow.hermitianWronskian_hasDerivAt_zero (hsubset hs))
    IntervalIntegrable.zero
  have hsub :
      hermitianWronskianPath flow.Y flow.Z t -
        hermitianWronskianPath flow.Y flow.Z flow.startTime = 0 := by
    simpa using hFTC.symm
  exact sub_eq_zero.mp hsub

end LinearHamiltonianFlow

/- A vector in the kernel of `Y` annihilates the normalized Hermitian
Wronskian quadratic form. -/
omit [DecidableEq n] in
theorem quadratic_normalizedWronskian_eq_zero_of_mulVec_eq_zero
    (Y Z : Matrix n n Complex) (x : n -> Complex)
    (hx : Y *ᵥ x = 0) :
    complexQuadratic ((-Complex.I / 2) • (Yᴴ * Z - Zᴴ * Y)) x = 0 := by
  rw [complexQuadratic_smul, complexQuadratic_sub]
  have hleft : complexQuadratic (Yᴴ * Z) x = 0 := by
    unfold complexQuadratic
    rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
      ← Matrix.star_mulVec, hx]
    simp
  have hright : complexQuadratic (Zᴴ * Y) x = 0 := by
    unfold complexQuadratic
    rw [← Matrix.mulVec_mulVec, hx]
    simp
  rw [hleft, hright]
  simp

/-- Positive normalized Hermitian Wronskian data force `Y` to be invertible.
This is the no-caustic algebra underlying the complex Gaussian-beam phase. -/
theorem isUnit_of_positive_normalizedWronskian
    (Y Z H0 : Matrix n n Complex)
    (hWronskian :
      (-Complex.I / 2) • (Yᴴ * Z - Zᴴ * Y) =
        hermitianImaginaryPart H0)
    (hH0 : ComplexPosDef (hermitianImaginaryPart H0)) :
    IsUnit Y := by
  rw [← Matrix.mulVec_injective_iff_isUnit]
  intro x y hxy
  have hkernel : Y *ᵥ (x - y) = 0 := by
    rw [Matrix.mulVec_sub, hxy, sub_self]
  have hsub : x - y = 0 := by
    by_contra hne
    have hpos := hH0.2 hne
    have hzero :=
      quadratic_normalizedWronskian_eq_zero_of_mulVec_eq_zero
        Y Z (x - y) hkernel
    rw [← hWronskian, hzero] at hpos
    exact (lt_irrefl 0) hpos
  exact sub_eq_zero.mp hsub

/-- Source-initialized Riccati flow.  Both Wronskian identities and
invertibility of `Y` are generated from the ODE and positive initial phase. -/
structure RiccatiFlow (n : Type*) [Fintype n] [DecidableEq n]
    extends LinearHamiltonianFlow n where
  H0 : Matrix n n Complex
  H0_symmetric : H0.IsSymm
  H0_imaginaryPositive : ComplexPosDef (hermitianImaginaryPart H0)
  initialY : Y startTime = 1
  initialZ : Z startTime = H0

namespace LinearHamiltonianFlow

/-- Promote an initialized Hamiltonian flow with positive imaginary phase to
a Riccati flow.  No interval invertibility witness is supplied. -/
def toRiccatiFlow
    (flow : LinearHamiltonianFlow n) (H0 : Matrix n n Complex)
    (H0_symmetric : H0.IsSymm)
    (H0_imaginaryPositive : ComplexPosDef (hermitianImaginaryPart H0))
    (initialY : flow.Y flow.startTime = 1)
    (initialZ : flow.Z flow.startTime = H0) : RiccatiFlow n where
  toLinearHamiltonianFlow := flow
  H0 := H0
  H0_symmetric := H0_symmetric
  H0_imaginaryPositive := H0_imaginaryPositive
  initialY := initialY
  initialZ := initialZ

end LinearHamiltonianFlow

namespace RiccatiFlow

def H (flow : RiccatiFlow n) (t : Real) : Matrix n n Complex :=
  flow.Z t * (flow.Y t)⁻¹

def dH (flow : RiccatiFlow n) (t : Real) : Matrix n n Complex :=
  (-flow.D t * flow.Y t) * (flow.Y t)⁻¹ -
    flow.H t * (flow.C t * flow.Z t) * (flow.Y t)⁻¹

theorem symmetricWronskian
    (flow : RiccatiFlow n) {t : Real}
    (ht : t ∈ uIcc flow.startTime flow.endTime) :
    (flow.Y t)ᵀ * flow.Z t = (flow.Z t)ᵀ * flow.Y t := by
  have hconst := flow.toLinearHamiltonianFlow.symmetricWronskian_eq_start ht
  have hstart : symmetricWronskianPath flow.Y flow.Z flow.startTime = 0 := by
    rw [symmetricWronskianPath, flow.initialY, flow.initialZ]
    exact sub_eq_zero.mpr (symmetricWronskian_initial flow.H0 flow.H0_symmetric)
  have hzero : symmetricWronskianPath flow.Y flow.Z t = 0 :=
    hconst.trans hstart
  exact sub_eq_zero.mp hzero

theorem normalizedHermitianWronskian
    (flow : RiccatiFlow n) {t : Real}
    (ht : t ∈ uIcc flow.startTime flow.endTime) :
    (-Complex.I / 2) •
        ((flow.Y t)ᴴ * flow.Z t - (flow.Z t)ᴴ * flow.Y t) =
      hermitianImaginaryPart flow.H0 := by
  have hconst :
      (flow.Y t)ᴴ * flow.Z t - (flow.Z t)ᴴ * flow.Y t =
        (flow.Y flow.startTime)ᴴ * flow.Z flow.startTime -
          (flow.Z flow.startTime)ᴴ * flow.Y flow.startTime := by
    simpa [hermitianWronskianPath] using
      flow.toLinearHamiltonianFlow.hermitianWronskian_eq_start ht
  rw [hconst, flow.initialY, flow.initialZ]
  exact normalizedHermitianWronskian_initial flow.H0

/-- The complex positive initial phase prevents `Y(t)` from developing a
kernel anywhere on the geodesic interval. -/
theorem Y_isUnit
    (flow : RiccatiFlow n) (t : Real)
    (ht : t ∈ uIcc flow.startTime flow.endTime) :
    IsUnit (flow.Y t) :=
  isUnit_of_positive_normalizedWronskian
    (flow.Y t) (flow.Z t) flow.H0
    (flow.normalizedHermitianWronskian ht) flow.H0_imaginaryPositive

/-- Determinant form of interval invertibility, derived rather than supplied. -/
theorem YdetUnit
    (flow : RiccatiFlow n) (t : Real)
    (ht : t ∈ uIcc flow.startTime flow.endTime) :
    IsUnit (flow.Y t).det :=
  (flow.Y t).isUnit_iff_isUnit_det.mp (flow.Y_isUnit t ht)

theorem hasDerivAt_inverse
    (flow : RiccatiFlow n) {t : Real}
    (ht : t ∈ uIcc flow.startTime flow.endTime) :
    HasDerivAt (fun s => (flow.Y s)⁻¹)
      (-((flow.Y t)⁻¹ * (flow.C t * flow.Z t) * (flow.Y t)⁻¹)) t := by
  have hyUnit : IsUnit (flow.Y t) :=
    (flow.Y t).isUnit_iff_isUnit_det.mpr (flow.YdetUnit t ht)
  obtain ⟨u, hu⟩ := hyUnit
  have houter := hasFDerivAt_ringInverse (𝕜 := Real) u
  rw [hu] at houter
  have hinv :=
    (houter.comp t (flow.hasDerivY t ht).hasFDerivAt).hasDerivAt
  convert hinv using 1
  · funext s
    simp only [Function.comp_apply, Matrix.nonsing_inv_eq_ringInverse]
  · simp only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.toSpanSingleton_apply, one_smul,
      ContinuousLinearMap.neg_apply, ContinuousLinearMap.mulLeftRight_apply,
      Matrix.nonsing_inv_eq_ringInverse]
    rw [← hu, Ring.inverse_unit]

theorem H_hasDerivAt
    (flow : RiccatiFlow n) {t : Real}
    (ht : t ∈ uIcc flow.startTime flow.endTime) :
    HasDerivAt flow.H (flow.dH t) t := by
  have hproduct := (flow.hasDerivZ t ht).mul (flow.hasDerivAt_inverse ht)
  convert hproduct using 1
  simp only [H, dH]
  noncomm_ring

/-- Pointwise equation-(3.8) data generated from the actual interval flow. -/
def pointData (flow : RiccatiFlow n) (t : Real)
    (ht : t ∈ uIcc flow.startTime flow.endTime) : RiccatiPointData n where
  C := flow.C t
  D := flow.D t
  Y := flow.Y t
  Z := flow.Z t
  dY := flow.C t * flow.Z t
  dZ := -flow.D t * flow.Y t
  H := flow.H t
  dH := flow.dH t
  YdetUnit := flow.YdetUnit t ht
  linearY := rfl
  linearZ := rfl
  quotient := rfl
  quotientDerivative := rfl

theorem pointData_H_hasDerivAt
    (flow : RiccatiFlow n) {t : Real}
    (ht : t ∈ uIcc flow.startTime flow.endTime) :
    HasDerivAt flow.H (flow.pointData t ht).dH t :=
  flow.H_hasDerivAt ht

/-- Phase data at every point, with both Wronskians derived from the initial
conditions and Hamiltonian ODE. -/
def phaseData (flow : RiccatiFlow n) (t : Real)
    (ht : t ∈ uIcc flow.startTime flow.endTime) : RiccatiPhaseData n where
  point := flow.pointData t ht
  H0 := flow.H0
  H0Symmetric := flow.H0_symmetric
  H0ImaginaryPositive := flow.H0_imaginaryPositive
  symmetricWronskian := flow.symmetricWronskian ht
  normalizedHermitianWronskian := flow.normalizedHermitianWronskian ht

/-- Interval-level source certificate: equation (3.8), symmetry, positive
imaginary Hessian, phase positivity, and determinant transport hold at every
point of the geodesic interval. -/
theorem phase_certificate
    (flow : RiccatiFlow n) {t : Real}
    (ht : t ∈ uIcc flow.startTime flow.endTime) :
    RiccatiPhaseData.Certificate (flow.phaseData t ht) :=
  (flow.phaseData t ht).certificate

theorem equation38
    (flow : RiccatiFlow n) {t : Real}
    (ht : t ∈ uIcc flow.startTime flow.endTime) :
    flow.dH t + flow.H t * flow.C t * flow.H t + flow.D t = 0 :=
  (flow.phase_certificate ht).equation38

theorem phaseImaginaryPositive
    (flow : RiccatiFlow n) {t : Real}
    (ht : t ∈ uIcc flow.startTime flow.endTime)
    {x : n -> Complex} (hx : x ≠ 0) :
    0 < (complexQuadratic (flow.H t) x).im :=
  (flow.phase_certificate ht).phaseImaginaryPositive hx

theorem determinant_transport
    (flow : RiccatiFlow n) {t : Real}
    (ht : t ∈ uIcc flow.startTime flow.endTime) :
    (Complex.normSq (flow.Y t).det : Complex) *
        (hermitianImaginaryPart (flow.H t)).det =
      (hermitianImaginaryPart flow.H0).det :=
  (flow.phase_certificate ht).determinantIdentity

theorem imaginaryPart_congruence
    (flow : RiccatiFlow n) {t : Real}
    (ht : t ∈ uIcc flow.startTime flow.endTime) :
    (flow.Y t)ᴴ * hermitianImaginaryPart (flow.H t) * flow.Y t =
      hermitianImaginaryPart flow.H0 :=
  LiuWang2025SemilinearWaveRiccatiPhase.imaginaryPart_congruence
    (flow.H t) flow.H0 (flow.Y t) (flow.Z t)
    (flow.YdetUnit t ht) rfl (flow.normalizedHermitianWronskian ht)

/-- One interval certificate packages the propagated invariants, the actual
quotient derivative, and the pointwise phase certificate. -/
structure IntervalCertificate (flow : RiccatiFlow n) : Prop where
  symmetricWronskian : forall t,
    t ∈ uIcc flow.startTime flow.endTime ->
      (flow.Y t)ᵀ * flow.Z t = (flow.Z t)ᵀ * flow.Y t
  normalizedHermitianWronskian : forall t,
    t ∈ uIcc flow.startTime flow.endTime ->
      (-Complex.I / 2) •
          ((flow.Y t)ᴴ * flow.Z t - (flow.Z t)ᴴ * flow.Y t) =
        hermitianImaginaryPart flow.H0
  YIsUnit : forall t,
    t ∈ uIcc flow.startTime flow.endTime -> IsUnit (flow.Y t)
  YDetIsUnit : forall t,
    t ∈ uIcc flow.startTime flow.endTime -> IsUnit (flow.Y t).det
  quotientHasDerivative : forall t,
    t ∈ uIcc flow.startTime flow.endTime ->
      HasDerivAt flow.H (flow.dH t) t
  phaseCertificate : forall t (ht : t ∈ uIcc flow.startTime flow.endTime),
    RiccatiPhaseData.Certificate (flow.phaseData t ht)

def intervalCertificate (flow : RiccatiFlow n) : IntervalCertificate flow where
  symmetricWronskian := fun _ ht => flow.symmetricWronskian ht
  normalizedHermitianWronskian := fun _ ht =>
    flow.normalizedHermitianWronskian ht
  YIsUnit := fun t ht => flow.Y_isUnit t ht
  YDetIsUnit := fun t ht => flow.YdetUnit t ht
  quotientHasDerivative := fun _ ht => flow.H_hasDerivAt ht
  phaseCertificate := fun _ ht => flow.phase_certificate ht

open LiuWang2025SemilinearWaveWKBResidual

variable {Jet : Type*} [AddCommGroup Jet] [Module Complex Jet]

/-- Interval-flow-to-WKB theorem.  The eikonal coefficient is generated by
the propagated Riccati flow; only the displayed amplitude transport
recursions remain as hypotheses. -/
theorem factorizedWaveResidual_truncatedAmplitude_eq_terminal
    (flow : RiccatiFlow n) {t : Real}
    (ht : t ∈ uIcc flow.startTime flow.endTime)
    (eikonalReadout : Matrix n n Complex →ₗ[Complex] Complex)
    (transport wave : Jet →ₗ[Complex] Jet)
    (amplitude : Nat -> Jet) (N : Nat)
    (leadingTransport : transport (amplitude 0) = 0)
    (recursiveTransport : ∀ k < N,
      (-Complex.I) • transport (amplitude (k + 1)) +
        wave (amplitude k) = 0)
    {rho q : Complex} (hinverse : rho * q = 1) :
    ((flow.pointData t ht).toWKBJetOperators
        eikonalReadout transport wave).factorizedWaveResidual
        rho (truncatedAmplitude amplitude q N) =
      q ^ N • wave (amplitude N) :=
  (flow.pointData t ht).factorizedWaveResidual_truncatedAmplitude_eq_terminal
    eikonalReadout transport wave amplitude N leadingTransport
      recursiveTransport hinverse

end RiccatiFlow

/-- A real lower bound for a complex Hermitian quadratic form. -/
def RealCoercive (A : Matrix n n Complex) (constant : Real) : Prop :=
  forall x : n -> Complex,
    constant * ‖x‖ ^ 2 <= (complexQuadratic A x).re

/-- Quantitative interval packet.  A concrete flow supplies a uniform action
bound for `Y`; Lean converts it to a uniform positive lower bound for the
imaginary quadratic phase. -/
structure UniformRiccatiFlow (n : Type*) [Fintype n] [DecidableEq n]
    extends RiccatiFlow n where
  initialCoercivity : Real
  initialCoercivity_pos : 0 < initialCoercivity
  H0_coercive : RealCoercive (hermitianImaginaryPart H0) initialCoercivity
  YActionBound : Real
  YActionBound_pos : 0 < YActionBound
  Y_mulVec_bound : forall t, t ∈ uIcc startTime endTime -> forall x : n -> Complex,
    ‖Y t *ᵥ x‖ <= YActionBound * ‖x‖

namespace UniformRiccatiFlow

/-- Explicit uniform lower-bound constant for the imaginary phase Hessian. -/
def phaseCoercivityConstant (flow : UniformRiccatiFlow n) : Real :=
  flow.initialCoercivity / flow.YActionBound ^ 2

theorem phaseCoercivityConstant_pos (flow : UniformRiccatiFlow n) :
    0 < flow.phaseCoercivityConstant := by
  exact div_pos flow.initialCoercivity_pos
    (sq_pos_of_pos flow.YActionBound_pos)

/-- Uniform form of the source estimate `Im phi >= C |z'|^2`, at the
quadratic Hessian level.  The constant is generated explicitly as `c0/M^2`. -/
theorem phase_uniform_coercivity
    (flow : UniformRiccatiFlow n) {t : Real}
    (ht : t ∈ uIcc flow.startTime flow.endTime)
    (x : n -> Complex) :
    flow.phaseCoercivityConstant * ‖x‖ ^ 2 <=
      (complexQuadratic (flow.H t) x).im := by
  let y : n -> Complex := (flow.Y t)⁻¹ *ᵥ x
  have hyRecover : flow.Y t *ᵥ y = x := by
    dsimp [y]
    rw [Matrix.mulVec_mulVec]
    rw [Matrix.mul_nonsing_inv (flow.Y t) (flow.YdetUnit t ht),
      Matrix.one_mulVec]
  have hnorm : ‖x‖ <= flow.YActionBound * ‖y‖ := by
    rw [← hyRecover]
    exact flow.Y_mulVec_bound t ht y
  have hrightNonnegative : 0 <= flow.YActionBound * ‖y‖ :=
    mul_nonneg flow.YActionBound_pos.le (norm_nonneg y)
  have hsquare : ‖x‖ ^ 2 <= flow.YActionBound ^ 2 * ‖y‖ ^ 2 := by
    have h := (sq_le_sq₀ (norm_nonneg x) hrightNonnegative).2 hnorm
    simpa [mul_pow] using h
  have hcoefficientNonnegative :
      0 <= flow.initialCoercivity / flow.YActionBound ^ 2 :=
    (flow.phaseCoercivityConstant_pos).le
  have hscaled :
      flow.initialCoercivity / flow.YActionBound ^ 2 * ‖x‖ ^ 2 <=
        flow.initialCoercivity * ‖y‖ ^ 2 := by
    calc
      flow.initialCoercivity / flow.YActionBound ^ 2 * ‖x‖ ^ 2 <=
          flow.initialCoercivity / flow.YActionBound ^ 2 *
            (flow.YActionBound ^ 2 * ‖y‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hsquare hcoefficientNonnegative
      _ = flow.initialCoercivity * ‖y‖ ^ 2 := by
        field_simp [flow.YActionBound_pos.ne']
  have hbase := flow.H0_coercive y
  have htransport :
      complexQuadratic (hermitianImaginaryPart (flow.H t)) x =
        complexQuadratic (hermitianImaginaryPart flow.H0) y := by
    calc
      complexQuadratic (hermitianImaginaryPart (flow.H t)) x =
          complexQuadratic (hermitianImaginaryPart (flow.H t))
            (flow.Y t *ᵥ y) := by rw [hyRecover]
      _ = complexQuadratic
          ((flow.Y t)ᴴ * hermitianImaginaryPart (flow.H t) * flow.Y t) y := by
        rw [complexQuadratic_congruence]
      _ = complexQuadratic (hermitianImaginaryPart flow.H0) y := by
        rw [flow.imaginaryPart_congruence ht]
  have himaginary :
      (complexQuadratic (hermitianImaginaryPart (flow.H t)) x).re =
        (complexQuadratic (flow.H t) x).im := by
    rw [complexQuadratic_hermitianImaginaryPart]
    simp
  change flow.initialCoercivity / flow.YActionBound ^ 2 * ‖x‖ ^ 2 <= _
  rw [← himaginary, htransport]
  exact hscaled.trans hbase

/-- Quantitative interval certificate for every transverse vector. -/
structure Certificate (flow : UniformRiccatiFlow n) : Prop where
  interval : RiccatiFlow.IntervalCertificate flow.toRiccatiFlow
  coercivityConstantPositive : 0 < flow.phaseCoercivityConstant
  uniformPhaseCoercivity : forall t,
    t ∈ uIcc flow.startTime flow.endTime -> forall x : n -> Complex,
      flow.phaseCoercivityConstant * ‖x‖ ^ 2 <=
        (complexQuadratic (flow.H t) x).im

def certificate (flow : UniformRiccatiFlow n) : Certificate flow where
  interval := flow.toRiccatiFlow.intervalCertificate
  coercivityConstantPositive := flow.phaseCoercivityConstant_pos
  uniformPhaseCoercivity := fun _ ht x => flow.phase_uniform_coercivity ht x

end UniformRiccatiFlow

end LiuWang2025SemilinearWaveRiccatiFlow
