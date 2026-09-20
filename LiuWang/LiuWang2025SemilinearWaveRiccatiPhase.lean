import LiuWang.LiuWang2025SemilinearWaveWKBResidual
import Mathlib.LinearAlgebra.Matrix.Hermitian

/-!
# Liu--Wang 2025: Riccati phase and positive imaginary Hessian

Section 3.1.2 of Liu--Wang constructs the quadratic Gaussian-beam phase from

`H' + H C H + D = 0`,

and linearizes that Riccati equation by

`Y' = C Z`, `Z' = -D Y`, `H = Z Y^-1`.

This module checks the finite-dimensional matrix mechanism behind equation
(3.8).  It proves the Riccati identity from the linear system and quotient
rule, proves the symmetric and Hermitian Wronskian derivative cancellations,
transports symmetry and strict positivity of the imaginary Hessian through
`H = Z Y^-1`, and derives the determinant identity

`det(Im H) * |det Y|^2 = det(Im H0)`.

The resulting quadratic phase has strictly positive imaginary part away from
the beam center.  An adapter sends the zero quadratic eikonal defect into the
existing finite-jet WKB hierarchy, so the Riccati calculation supplies rather
than assumes that hierarchy's eikonal field.

The global ODE existence theorem, invertibility of `Y` along the full
geodesic, derivation of the conserved Wronskians from initial data, concrete
Fermi coordinates, higher phase jets, and the uniform lower bound
`Im phi >= C |z'|^2` remain analytic realization obligations.
-/

noncomputable section

open Matrix

namespace LiuWang2025SemilinearWaveRiccatiPhase

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Hermitian imaginary part `(H - H^*) / (2i)`. -/
def hermitianImaginaryPart (H : Matrix n n Complex) : Matrix n n Complex :=
  (-Complex.I / 2) • (H - Hᴴ)

omit [Fintype n] [DecidableEq n] in
theorem hermitianImaginaryPart_isHermitian (H : Matrix n n Complex) :
    (hermitianImaginaryPart H).IsHermitian := by
  unfold Matrix.IsHermitian
  ext i j
  simp [hermitianImaginaryPart, Matrix.conjTranspose, map_ofNat]
  ring

/-- The Hermitian Wronskian has the required normalization at `Y0 = 1`,
`Z0 = H0`. -/
theorem normalizedHermitianWronskian_initial
    (H0 : Matrix n n Complex) :
    (-Complex.I / 2) • ((1 : Matrix n n Complex)ᴴ * H0 -
        H0ᴴ * (1 : Matrix n n Complex)) =
      hermitianImaginaryPart H0 := by
  simp [hermitianImaginaryPart]

/-- The symmetric Wronskian vanishes initially when `H0` is symmetric. -/
theorem symmetricWronskian_initial
    (H0 : Matrix n n Complex) (hH0 : H0.IsSymm) :
    (1 : Matrix n n Complex)ᵀ * H0 =
      H0ᵀ * (1 : Matrix n n Complex) := by
  simp [hH0.eq]

/-- Algebraic identity converting the skew-Hermitian part of `H = ZY^-1`
to the Hermitian Wronskian. -/
theorem quotient_skew_congruence
    (H Y Z : Matrix n n Complex)
    (hy : IsUnit Y.det)
    (hH : H = Z * Y⁻¹) :
    Yᴴ * (H - Hᴴ) * Y = Yᴴ * Z - Zᴴ * Y := by
  rw [hH]
  have hyUnit : IsUnit Y := Y.isUnit_iff_isUnit_det.mpr hy
  have hyHUnit : IsUnit Yᴴ := by simpa using hyUnit.star
  have hyH : IsUnit (Yᴴ).det :=
    (Yᴴ).isUnit_iff_isUnit_det.mp hyHUnit
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv,
    Matrix.mul_sub, Matrix.sub_mul]
  have hfirst : Yᴴ * (Z * Y⁻¹) * Y = Yᴴ * Z := by
    calc
      Yᴴ * (Z * Y⁻¹) * Y = (Yᴴ * Z) * (Y⁻¹ * Y) := by
        noncomm_ring
      _ = Yᴴ * Z := by
        rw [Matrix.nonsing_inv_mul Y hy, Matrix.mul_one]
  have hsecond : Yᴴ * ((Yᴴ)⁻¹ * Zᴴ) * Y = Zᴴ * Y := by
    calc
      Yᴴ * ((Yᴴ)⁻¹ * Zᴴ) * Y =
          (Yᴴ * (Yᴴ)⁻¹) * (Zᴴ * Y) := by
        noncomm_ring
      _ = Zᴴ * Y := by
        rw [Matrix.mul_nonsing_inv (Yᴴ) hyH, Matrix.one_mul]
  rw [hfirst, hsecond]

/-- Congruence formula for the imaginary Hessian. -/
theorem imaginaryPart_congruence
    (H H0 Y Z : Matrix n n Complex)
    (hy : IsUnit Y.det)
    (hH : H = Z * Y⁻¹)
    (hWronskian :
      (-Complex.I / 2) • (Yᴴ * Z - Zᴴ * Y) =
        hermitianImaginaryPart H0) :
    Yᴴ * hermitianImaginaryPart H * Y =
      hermitianImaginaryPart H0 := by
  rw [hermitianImaginaryPart]
  rw [Matrix.mul_smul, Matrix.smul_mul]
  rw [quotient_skew_congruence H Y Z hy hH]
  exact hWronskian

/-- The symmetric Wronskian implies symmetry of `H = ZY^-1`. -/
theorem quotient_isSymm
    (H Y Z : Matrix n n Complex)
    (hy : IsUnit Y.det)
    (hH : H = Z * Y⁻¹)
    (hSymplectic : Yᵀ * Z = Zᵀ * Y) :
    H.IsSymm := by
  unfold Matrix.IsSymm
  rw [hH, Matrix.transpose_mul, Matrix.transpose_nonsing_inv]
  have hyT : IsUnit (Yᵀ).det := Matrix.isUnit_det_transpose Y hy
  have hleft : (Yᵀ)⁻¹ * Yᵀ = 1 :=
    Matrix.nonsing_inv_mul (Yᵀ) hyT
  have hright : Y * Y⁻¹ = 1 := Matrix.mul_nonsing_inv Y hy
  calc
    (Yᵀ)⁻¹ * Zᵀ = ((Yᵀ)⁻¹ * Zᵀ) * (Y * Y⁻¹) := by
      rw [hright, Matrix.mul_one]
    _ = (Yᵀ)⁻¹ * (Zᵀ * Y) * Y⁻¹ := by noncomm_ring
    _ = (Yᵀ)⁻¹ * (Yᵀ * Z) * Y⁻¹ := by rw [hSymplectic]
    _ = ((Yᵀ)⁻¹ * Yᵀ) * (Z * Y⁻¹) := by noncomm_ring
    _ = Z * Y⁻¹ := by rw [hleft, Matrix.one_mul]

/-- Complex quadratic form `x^* A x`. -/
def complexQuadratic (A : Matrix n n Complex) (x : n → Complex) : Complex :=
  star x ⬝ᵥ (A *ᵥ x)

/-- Positive definiteness for complex Hermitian matrices, stated through the
real part of `x^* A x` because `Complex` has no ambient linear order. -/
def ComplexPosDef (A : Matrix n n Complex) : Prop :=
  A.IsHermitian ∧ ∀ {x : n → Complex}, x ≠ 0 →
    0 < (complexQuadratic A x).re

omit [DecidableEq n] in
theorem complexQuadratic_congruence
    (A B : Matrix n n Complex) (x : n → Complex) :
    complexQuadratic (Bᴴ * A * B) x = complexQuadratic A (B *ᵥ x) := by
  simp [complexQuadratic, Matrix.mulVec_mulVec, Matrix.star_mulVec,
    Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, Matrix.mul_assoc]

omit [DecidableEq n] in
theorem complexQuadratic_conjTranspose
    (A : Matrix n n Complex) (x : n → Complex) :
    complexQuadratic Aᴴ x = star (complexQuadratic A x) := by
  simp [complexQuadratic, Matrix.mulVec_conjTranspose,
    Matrix.dotProduct_mulVec, Matrix.dotProduct_star]

omit [DecidableEq n] in
theorem complexQuadratic_sub
    (A B : Matrix n n Complex) (x : n → Complex) :
    complexQuadratic (A - B) x =
      complexQuadratic A x - complexQuadratic B x := by
  simp [complexQuadratic, Matrix.sub_mulVec, dotProduct_sub]

omit [DecidableEq n] in
theorem complexQuadratic_smul
    (c : Complex) (A : Matrix n n Complex) (x : n → Complex) :
    complexQuadratic (c • A) x = c * complexQuadratic A x := by
  simp [complexQuadratic, Matrix.smul_mulVec, dotProduct_smul]

-- The Hermitian imaginary part evaluates to the scalar phase imaginary part.
omit [DecidableEq n] in
theorem complexQuadratic_hermitianImaginaryPart
    (H : Matrix n n Complex) (x : n → Complex) :
    complexQuadratic (hermitianImaginaryPart H) x =
      ((complexQuadratic H x).im : Complex) := by
  rw [hermitianImaginaryPart, complexQuadratic_smul,
    complexQuadratic_sub, complexQuadratic_conjTranspose]
  apply Complex.ext <;> simp
  ring

/-- Positive imaginary Hessian is preserved by the Riccati factorization. -/
theorem imaginaryPart_complexPosDef
    (H H0 Y Z : Matrix n n Complex)
    (hy : IsUnit Y.det)
    (hH : H = Z * Y⁻¹)
    (hWronskian :
      (-Complex.I / 2) • (Yᴴ * Z - Zᴴ * Y) =
        hermitianImaginaryPart H0)
    (hH0 : ComplexPosDef (hermitianImaginaryPart H0)) :
    ComplexPosDef (hermitianImaginaryPart H) := by
  refine ⟨hermitianImaginaryPart_isHermitian H, ?_⟩
  intro x hx
  have hyInvDet : IsUnit (Y⁻¹).det := Y.isUnit_nonsing_inv_det hy
  have hyInvUnit : IsUnit Y⁻¹ :=
    (Y⁻¹).isUnit_iff_isUnit_det.mpr hyInvDet
  let y : n → Complex := Y⁻¹ *ᵥ x
  have hyNonzero : y ≠ 0 := by
    intro hyZero
    apply hx
    apply Matrix.mulVec_injective_of_isUnit hyInvUnit
    simpa [y] using hyZero
  have hpositive := hH0.2 hyNonzero
  have hcongruence := imaginaryPart_congruence H H0 Y Z hy hH hWronskian
  have hyRecover : Y *ᵥ y = x := by
    dsimp [y]
    rw [Matrix.mulVec_mulVec]
    rw [Matrix.mul_nonsing_inv Y hy, Matrix.one_mulVec]
  rw [← hyRecover]
  rw [← complexQuadratic_congruence]
  rw [hcongruence]
  exact hpositive

-- Strict positivity of the imaginary part away from the beam center.
omit [DecidableEq n] in
theorem quadraticPhase_im_pos
    (H : Matrix n n Complex)
    (hH : ComplexPosDef (hermitianImaginaryPart H))
    {x : n → Complex} (hx : x ≠ 0) :
    0 < (complexQuadratic H x).im := by
  have hpositive := hH.2 hx
  rw [complexQuadratic_hermitianImaginaryPart] at hpositive
  simpa using hpositive

/-- Determinant transport identity from Lemma 3.2. -/
theorem determinant_imaginaryPart_transport
    (H H0 Y Z : Matrix n n Complex)
    (hy : IsUnit Y.det)
    (hH : H = Z * Y⁻¹)
    (hWronskian :
      (-Complex.I / 2) • (Yᴴ * Z - Zᴴ * Y) =
        hermitianImaginaryPart H0) :
    (Complex.normSq Y.det : Complex) *
        (hermitianImaginaryPart H).det =
      (hermitianImaginaryPart H0).det := by
  have hdet := congrArg Matrix.det
    (imaginaryPart_congruence H H0 Y Z hy hH hWronskian)
  simp only [Matrix.det_mul, Matrix.det_conjTranspose] at hdet
  rw [Complex.normSq_eq_conj_mul_self]
  rw [← hdet]
  rw [starRingEnd_apply]
  ring

/-- One source point of the linearized Riccati system, with `dY`, `dZ`, and
`dH` representing derivatives at that point. -/
structure RiccatiPointData (n : Type*) [Fintype n] [DecidableEq n] where
  C : Matrix n n Complex
  D : Matrix n n Complex
  Y : Matrix n n Complex
  Z : Matrix n n Complex
  dY : Matrix n n Complex
  dZ : Matrix n n Complex
  H : Matrix n n Complex
  dH : Matrix n n Complex
  YdetUnit : IsUnit Y.det
  linearY : dY = C * Z
  linearZ : dZ = -D * Y
  quotient : H = Z * Y⁻¹
  quotientDerivative : dH = dZ * Y⁻¹ - H * dY * Y⁻¹

namespace RiccatiPointData

/-- Quadratic transverse eikonal coefficient in equation (3.8). -/
def quadraticEikonalDefect (data : RiccatiPointData n) :
    Matrix n n Complex :=
  data.dH + data.H * data.C * data.H + data.D

/-- Equation (3.8) generated from the linear system and quotient rule. -/
theorem equation38 (data : RiccatiPointData n) :
    data.dH + data.H * data.C * data.H + data.D = 0 := by
  rw [data.quotientDerivative, data.linearY, data.linearZ, data.quotient]
  have hcancel : data.Y * data.Y⁻¹ = 1 :=
    Matrix.mul_nonsing_inv data.Y data.YdetUnit
  noncomm_ring [hcancel]

theorem quadraticEikonalDefect_eq_zero (data : RiccatiPointData n) :
    data.quadraticEikonalDefect = 0 :=
  data.equation38

end RiccatiPointData

/-- Riccati phase packet after propagation of the two Wronskian invariants. -/
structure RiccatiPhaseData (n : Type*) [Fintype n] [DecidableEq n] where
  point : RiccatiPointData n
  H0 : Matrix n n Complex
  H0Symmetric : H0.IsSymm
  H0ImaginaryPositive : ComplexPosDef (hermitianImaginaryPart H0)
  symmetricWronskian : point.Yᵀ * point.Z = point.Zᵀ * point.Y
  normalizedHermitianWronskian :
    (-Complex.I / 2) • (point.Yᴴ * point.Z - point.Zᴴ * point.Y) =
      hermitianImaginaryPart H0

namespace RiccatiPhaseData

def quadraticPhase (data : RiccatiPhaseData n) (x : n → Complex) : Complex :=
  complexQuadratic data.point.H x

theorem equation38 (data : RiccatiPhaseData n) :
    data.point.dH + data.point.H * data.point.C * data.point.H +
      data.point.D = 0 :=
  data.point.equation38

theorem phaseHessian_isSymm (data : RiccatiPhaseData n) :
    data.point.H.IsSymm :=
  quotient_isSymm data.point.H data.point.Y data.point.Z
    data.point.YdetUnit data.point.quotient data.symmetricWronskian

theorem phaseHessian_imaginaryPart_complexPosDef
    (data : RiccatiPhaseData n) :
    ComplexPosDef (hermitianImaginaryPart data.point.H) :=
  imaginaryPart_complexPosDef data.point.H data.H0 data.point.Y data.point.Z
    data.point.YdetUnit data.point.quotient
    data.normalizedHermitianWronskian data.H0ImaginaryPositive

theorem quadraticPhase_im_pos
    (data : RiccatiPhaseData n) {x : n → Complex} (hx : x ≠ 0) :
    0 < (data.quadraticPhase x).im :=
  LiuWang2025SemilinearWaveRiccatiPhase.quadraticPhase_im_pos
    data.point.H data.phaseHessian_imaginaryPart_complexPosDef hx

theorem determinant_transport (data : RiccatiPhaseData n) :
    (Complex.normSq data.point.Y.det : Complex) *
        (hermitianImaginaryPart data.point.H).det =
      (hermitianImaginaryPart data.H0).det :=
  determinant_imaginaryPart_transport data.point.H data.H0 data.point.Y
    data.point.Z data.point.YdetUnit data.point.quotient
    data.normalizedHermitianWronskian

/-- Product certificate for the source Riccati and quadratic-phase layer. -/
structure Certificate (data : RiccatiPhaseData n) : Prop where
  equation38 :
    data.point.dH + data.point.H * data.point.C * data.point.H +
      data.point.D = 0
  phaseHessianSymmetric : data.point.H.IsSymm
  phaseHessianImaginaryPositive :
    ComplexPosDef (hermitianImaginaryPart data.point.H)
  phaseImaginaryPositive : ∀ {x : n → Complex}, x ≠ 0 →
    0 < (data.quadraticPhase x).im
  determinantIdentity :
    (Complex.normSq data.point.Y.det : Complex) *
        (hermitianImaginaryPart data.point.H).det =
      (hermitianImaginaryPart data.H0).det

def certificate (data : RiccatiPhaseData n) : Certificate data where
  equation38 := data.equation38
  phaseHessianSymmetric := data.phaseHessian_isSymm
  phaseHessianImaginaryPositive :=
    data.phaseHessian_imaginaryPart_complexPosDef
  phaseImaginaryPositive := data.quadraticPhase_im_pos
  determinantIdentity := data.determinant_transport

end RiccatiPhaseData

namespace RiccatiPointData

open LiuWang2025SemilinearWaveWKBResidual

variable {Jet : Type*} [AddCommGroup Jet] [Module Complex Jet]

/-- WKB operators whose quadratic eikonal entry is read from equation (3.8). -/
def toWKBJetOperators (data : RiccatiPointData n)
    (eikonalReadout : Matrix n n Complex →ₗ[Complex] Complex)
    (transport wave : Jet →ₗ[Complex] Jet) : WKBJetOperators Jet where
  eikonalJet := eikonalReadout data.quadraticEikonalDefect
  transport := transport
  wave := wave

theorem toWKBJetOperators_eikonal_eq_zero (data : RiccatiPointData n)
    (eikonalReadout : Matrix n n Complex →ₗ[Complex] Complex)
    (transport wave : Jet →ₗ[Complex] Jet) :
    (data.toWKBJetOperators eikonalReadout transport wave).eikonalJet = 0 := by
  simp [toWKBJetOperators, data.quadraticEikonalDefect_eq_zero]

/-- Equation (3.8) supplies the eikonal field; only the transport relations
remain as inputs to the finite WKB hierarchy. -/
def toWKBJetHierarchy (data : RiccatiPointData n)
    (eikonalReadout : Matrix n n Complex →ₗ[Complex] Complex)
    (transport wave : Jet →ₗ[Complex] Jet)
    (amplitude : Nat → Jet) (N : Nat)
    (leadingTransport : transport (amplitude 0) = 0)
    (recursiveTransport : ∀ k < N,
      (-Complex.I) • transport (amplitude (k + 1)) +
        wave (amplitude k) = 0) :
    WKBJetHierarchy
      (data.toWKBJetOperators eikonalReadout transport wave) amplitude N where
  eikonal := data.toWKBJetOperators_eikonal_eq_zero
    eikonalReadout transport wave
  leadingTransport := leadingTransport
  recursiveTransport := recursiveTransport

/-- End-to-end quadratic-Riccati-to-WKB terminal residual theorem. -/
theorem factorizedWaveResidual_truncatedAmplitude_eq_terminal
    (data : RiccatiPointData n)
    (eikonalReadout : Matrix n n Complex →ₗ[Complex] Complex)
    (transport wave : Jet →ₗ[Complex] Jet)
    (amplitude : Nat → Jet) (N : Nat)
    (leadingTransport : transport (amplitude 0) = 0)
    (recursiveTransport : ∀ k < N,
      (-Complex.I) • transport (amplitude (k + 1)) +
        wave (amplitude k) = 0)
    {rho q : Complex} (hinverse : rho * q = 1) :
    (data.toWKBJetOperators eikonalReadout transport wave).factorizedWaveResidual
        rho (truncatedAmplitude amplitude q N) =
      q ^ N • wave (amplitude N) :=
  (data.toWKBJetHierarchy eikonalReadout transport wave amplitude N
    leadingTransport recursiveTransport).factorizedWaveResidual_truncatedAmplitude_eq_terminal
      hinverse

end RiccatiPointData

/-- Formal derivative of the Hermitian Wronskian. -/
def hermitianWronskianDerivative
    (Y Z dY dZ : Matrix n n Complex) : Matrix n n Complex :=
  dYᴴ * Z + Yᴴ * dZ - dZᴴ * Y - Zᴴ * dY

-- Hermitian Wronskian conservation at the derivative level.
omit [DecidableEq n] in
theorem hermitianWronskianDerivative_eq_zero
    (C D Y Z dY dZ : Matrix n n Complex)
    (hC : C.IsHermitian) (hD : D.IsHermitian)
    (hY : dY = C * Z) (hZ : dZ = -D * Y) :
    hermitianWronskianDerivative Y Z dY dZ = 0 := by
  rw [hY, hZ]
  unfold hermitianWronskianDerivative
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_neg, hC.eq, hD.eq]
  noncomm_ring

/-- Formal derivative of the symmetric Wronskian. -/
def symmetricWronskianDerivative
    (Y Z dY dZ : Matrix n n Complex) : Matrix n n Complex :=
  dYᵀ * Z + Yᵀ * dZ - dZᵀ * Y - Zᵀ * dY

-- Symmetric Wronskian conservation at the derivative level.
omit [DecidableEq n] in
theorem symmetricWronskianDerivative_eq_zero
    (C D Y Z dY dZ : Matrix n n Complex)
    (hC : C.IsSymm) (hD : D.IsSymm)
    (hY : dY = C * Z) (hZ : dZ = -D * Y) :
    symmetricWronskianDerivative Y Z dY dZ = 0 := by
  rw [hY, hZ]
  unfold symmetricWronskianDerivative
  simp only [Matrix.transpose_mul, Matrix.transpose_neg, hC.eq, hD.eq]
  noncomm_ring

end LiuWang2025SemilinearWaveRiccatiPhase
