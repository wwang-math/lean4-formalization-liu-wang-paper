import LiuWang.LiuWang2025SemilinearWaveFlatFermiL2

/-!
# Liu--Wang flat null-Fermi reflected-beam calibration

This module packages an explicit flat `1+3` dimensional reference model for
the reflected Gaussian-beam part of Liu--Wang.  It checks the transformed
Minkowski metric, the matrix Riccati equation, full transverse coercivity,
the exact wave residual, specular reflection, exact Dirichlet cancellation,
and genuine `L2` membership and bounds.

This is a calibration result only.  The metric and reflecting boundary are
flat, and the first-order beam has relative residual of order
`rho^(1/2)`, not a vanishing relative residual.  Thus this certificate does
not close the curved reflected-beam or higher-order WKB stages.
-/

noncomputable section

open MeasureTheory
open scoped Matrix

namespace LiuWang2025SemilinearWaveFlatBeam.Fermi

/-- One reviewable object collecting the positive and negative checks of the
flat null-Fermi model. -/
structure FlatFermiCalibrationCertificate : Prop where
  transformedMetric : fermiK * minkGinv * fermiKᵀ = fermiGinv
  riccatiEquation : forall (lam s : Real) (i j : Fin 3),
    HasDerivAt (fun sigma : Real => Hmat lam sigma i j)
      ((Hmat lam s * Pmat * Hmat lam s) i j) s
  fullTransverseCoercivity : forall {lam : Real}, 0 < lam ->
    forall {S s : Real}, |s| <= S -> forall z : Fin 3 -> Real,
      betS lam S / 2 * nsq z <= (phiF lam s z).im
  twoTransverseFailure :
    ¬ ∃ c : Real, 0 < c ∧
      ∀ (s : Real) (z : Fin 3 -> Real), c * nsq z <= (phiF 0 s z).im
  exactInteriorResidual : forall (rho lam s z0 z1 z2 : Real),
    boxF (UF rho lam) s z0 z1 z2 = resF rho lam s z0 z1 z2
  exactDirichletCancellation : forall (rho lam t x1 x2 : Real),
    Udiff rho lam t x1 x2 0 = 0
  specularNormalPhase : forall (lam t x1 x2 : Real),
    deriv (fun z : Real => PhiRef lam t x1 x2 z) 0 =
      -deriv (fun z : Real => PhiIn lam t x1 x2 z) 0
  beamMemLp : forall {rho lam : Real}, 0 < rho -> 0 < lam ->
    forall {S s : Real}, |s| <= S ->
      MemLp (fun z : Fin 3 -> Real => beamF rho lam s z) 2 volume
  residualMemLp : forall {rho lam : Real}, 0 < rho -> 0 < lam ->
    forall {S s : Real}, |s| <= S ->
      MemLp (fun z : Fin 3 -> Real => resFv rho lam s z) 2 volume
  honestRelativeResidual : forall {rho lam : Real}, 0 < rho -> 0 < lam ->
    forall {S s : Real}, |s| <= S ->
      (∫ z : Fin 3 -> Real, ‖resFv rho lam s z‖ ^ 2) <=
        (Cres lam S / cbeam lam S) * rho *
          (∫ z : Fin 3 -> Real, ‖beamF rho lam s z‖ ^ 2)
  boundaryMismatchNormZero : forall (rho lam : Real),
    eLpNorm
      (fun p : Real × Real × Real => Udiff rho lam p.1 p.2.1 p.2.2 0)
      2 volume = 0
  undampedBeamNotMemLp : forall (rho s z1 z2 : Real),
    ¬ MemLp (fun z0 : Real => beamF rho 0 s ![z0, z1, z2]) 2 volume

def flatFermiCalibrationCertificate : FlatFermiCalibrationCertificate where
  transformedMetric := fermiGinv_derived
  riccatiEquation := hasDerivAt_Hmat
  fullTransverseCoercivity :=
    fun {lam} hlam {S s} hs z => phiF_im_coercive hlam hs z
  twoTransverseFailure := two_transverse_not_coercive
  exactInteriorResidual := boxF_UF
  exactDirichletCancellation := Udiff_zero_at_z_zero
  specularNormalPhase := dZ_PhiRef_eq_neg_dZ_PhiIn
  beamMemLp :=
    fun {rho lam} hρ hlam {S s} hs => memLp_beamF hρ hlam hs
  residualMemLp :=
    fun {rho lam} hρ hlam {S s} hs => memLp_resFv hρ hlam hs
  honestRelativeResidual :=
    fun {rho lam} hρ hlam {S s} hs => residual_relative_bound hρ hlam hs
  boundaryMismatchNormZero := eLpNorm_boundary_mismatch
  undampedBeamNotMemLp := not_memLp_beamF_zero_lam

end LiuWang2025SemilinearWaveFlatBeam.Fermi
