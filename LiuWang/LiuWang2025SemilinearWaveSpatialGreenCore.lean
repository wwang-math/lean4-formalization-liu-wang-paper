import LiuWang.LiuWang2025SemilinearWaveTemporalGreen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Liu--Wang 2025: the concrete spatial Green formula with lateral normal trace

Source: Boya Liu and Weinan Wang, *On a partial data inverse problem for the
semi-linear wave equation*, arXiv:2511.08794v1, Section 4 (equations
(4.2)--(4.4)).

The abstract Green engine `DirectedWaveGreenModel` of
`LiuWang2025SemilinearWaveDirectedGreenRealization` derives the Lorentzian
Green identity from two analytic inputs: time integration by parts, supplied
concretely by `LiuWang2025SemilinearWaveTemporalGreen`, and the

  **spatial Green formula carrying the lateral normal-trace term**,

which until now had no concrete realization.  This module supplies it.

## The concrete model

The spatial domain is a slab `xMin <= x <= xMax` in the variable normal to the
boundary, separated over a finite set of tangential modes with tangential
eigenvalues `mu k`, so that the spatial Laplacian acts on mode `k` as

`Delta_k w = w'' - mu k * w`.

Nothing here is a surrogate for a differential operator: `w''` is an actual
second derivative and the integrals are actual interval integrals.  Both faces
`{x = xMin}` and `{x = xMax}` of the lateral boundary are kept, so the source's
split of `partial Omega` into the accessible piece `Gamma` and its inaccessible
complement is represented exactly.

## Contents

* `green_secondIdentity` : Green's second identity in the normal variable, with
  the *exact* boundary flux `[u' v - u v']` at both ends;
* `green_secondIdentity_tangentialMode` : the same for `Delta_k`, the
  tangential eigenvalue cancelling as in the source's separation;
* `lateralFlux_of_zeroDirichletTrace` : under the source's homogeneous lateral
  Dirichlet condition `u = 0` on `Sigma`, the flux collapses to the normal
  derivative pairing `u'(xMax) v(xMax) - u'(xMin) v(xMin)`;
* `lateralFlux_of_accessibleCancellation` : if in addition the accessible-face
  normal derivative vanishes -- which is exactly what equality of the two
  partial Dirichlet-to-Neumann maps supplies after differentiation -- only the
  inaccessible-face term survives, the structure of equation (4.3);
* `spacetimeGreenDefect_eq_lateralFlux` and
  `spacetimeGreenDefect_eq_inaccessibleFlux` : the time-integrated,
  finite-mode-summed forms in which the identity enters equations (4.3), (4.4).

## Scope

Only the *spatial* half of the Lorentzian Green identity is treated here; the
temporal half is the existing weighted temporal core.  Combining the two into a
single spacetime identity requires exchanging the order of the `t` and `x`
integrations, which is not performed here.  The tangential directions are
represented by their spectral decomposition rather than by charts on a general
boundary.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory Set

namespace LiuWang2025SemilinearWaveSpatialGreenCore

/-! ## Green's second identity in the normal variable -/

/-- The source's lateral flux `[u' v - u v']` evaluated between the two faces
of the slab. -/
def lateralFlux (u du v dv : Real -> Complex) (xMin xMax : Real) : Complex :=
  (du xMax * v xMax - u xMax * dv xMax) - (du xMin * v xMin - u xMin * dv xMin)

/-- **Green's second identity in the normal variable.**  Both boundary terms
are kept; nothing is assumed to vanish. -/
theorem green_secondIdentity
    {u du ddu v dv ddv : Real -> Complex} {xMin xMax : Real}
    (hu : ∀ x ∈ uIcc xMin xMax, HasDerivAt u (du x) x)
    (hdu : ∀ x ∈ uIcc xMin xMax, HasDerivAt du (ddu x) x)
    (hv : ∀ x ∈ uIcc xMin xMax, HasDerivAt v (dv x) x)
    (hdv : ∀ x ∈ uIcc xMin xMax, HasDerivAt dv (ddv x) x)
    (hduInt : IntervalIntegrable du volume xMin xMax)
    (hdduInt : IntervalIntegrable ddu volume xMin xMax)
    (hdvInt : IntervalIntegrable dv volume xMin xMax)
    (hddvInt : IntervalIntegrable ddv volume xMin xMax) :
    (∫ x in xMin..xMax, ddu x * v x) - (∫ x in xMin..xMax, u x * ddv x)
      = lateralFlux u du v dv xMin xMax := by
  have hA : (∫ x in xMin..xMax, du x * dv x)
      = du xMax * v xMax - du xMin * v xMin - ∫ x in xMin..xMax, ddu x * v x :=
    intervalIntegral.integral_mul_deriv_eq_deriv_mul hdu hv hdduInt hdvInt
  have hB : (∫ x in xMin..xMax, u x * ddv x)
      = u xMax * dv xMax - u xMin * dv xMin - ∫ x in xMin..xMax, du x * dv x :=
    intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hdv hduInt hddvInt
  rw [lateralFlux]
  linear_combination hA - hB

/-! ## The tangential eigenvalue cancels -/

/-- The spatial Laplacian on one separated tangential mode. -/
def tangentialLaplacian (mu : Complex) (w ddw : Real -> Complex) :
    Real -> Complex := fun x => ddw x - mu * w x

/-- **Green's second identity for `Delta_k = d_x^2 - mu k`.**  The tangential
eigenvalue cancels exactly, so the lateral flux is unchanged. -/
theorem green_secondIdentity_tangentialMode
    {u du ddu v dv ddv : Real -> Complex} {mu : Complex} {xMin xMax : Real}
    (hu : ∀ x ∈ uIcc xMin xMax, HasDerivAt u (du x) x)
    (hdu : ∀ x ∈ uIcc xMin xMax, HasDerivAt du (ddu x) x)
    (hv : ∀ x ∈ uIcc xMin xMax, HasDerivAt v (dv x) x)
    (hdv : ∀ x ∈ uIcc xMin xMax, HasDerivAt dv (ddv x) x)
    (hduInt : IntervalIntegrable du volume xMin xMax)
    (hdduInt : IntervalIntegrable ddu volume xMin xMax)
    (hdvInt : IntervalIntegrable dv volume xMin xMax)
    (hddvInt : IntervalIntegrable ddv volume xMin xMax)
    (hUV : IntervalIntegrable (fun x => u x * v x) volume xMin xMax)
    (hDdUV : IntervalIntegrable (fun x => ddu x * v x) volume xMin xMax)
    (hUDdV : IntervalIntegrable (fun x => u x * ddv x) volume xMin xMax) :
    (∫ x in xMin..xMax, tangentialLaplacian mu u ddu x * v x)
        - (∫ x in xMin..xMax, u x * tangentialLaplacian mu v ddv x)
      = lateralFlux u du v dv xMin xMax := by
  have hleftCongr : (∫ x in xMin..xMax, tangentialLaplacian mu u ddu x * v x)
      = ∫ x in xMin..xMax, (ddu x * v x - mu * (u x * v x)) := by
    refine intervalIntegral.integral_congr fun x _ => ?_
    simp only [tangentialLaplacian]
    ring
  have hleftSub : (∫ x in xMin..xMax, (ddu x * v x - mu * (u x * v x)))
      = (∫ x in xMin..xMax, ddu x * v x) - ∫ x in xMin..xMax, mu * (u x * v x) :=
    intervalIntegral.integral_sub hDdUV (hUV.const_mul mu)
  have hleftConst : (∫ x in xMin..xMax, mu * (u x * v x))
      = mu * ∫ x in xMin..xMax, u x * v x :=
    intervalIntegral.integral_const_mul mu _
  have hrightCongr : (∫ x in xMin..xMax, u x * tangentialLaplacian mu v ddv x)
      = ∫ x in xMin..xMax, (u x * ddv x - mu * (u x * v x)) := by
    refine intervalIntegral.integral_congr fun x _ => ?_
    simp only [tangentialLaplacian]
    ring
  have hrightSub : (∫ x in xMin..xMax, (u x * ddv x - mu * (u x * v x)))
      = (∫ x in xMin..xMax, u x * ddv x) - ∫ x in xMin..xMax, mu * (u x * v x) :=
    intervalIntegral.integral_sub hUDdV (hUV.const_mul mu)
  have hcore := green_secondIdentity hu hdu hv hdv hduInt hdduInt hdvInt hddvInt
  rw [hleftCongr, hleftSub, hleftConst, hrightCongr, hrightSub, hleftConst]
  linear_combination hcore

/-! ## The source's homogeneous lateral Dirichlet condition -/

/-- With the source's condition `u = 0` on the lateral boundary, the flux is
the pairing of the normal derivative of `u` with the probe. -/
theorem lateralFlux_of_zeroDirichletTrace
    (u du v dv : Real -> Complex) (xMin xMax : Real)
    (hmin : u xMin = 0) (hmax : u xMax = 0) :
    lateralFlux u du v dv xMin xMax = du xMax * v xMax - du xMin * v xMin := by
  simp [lateralFlux, hmin, hmax]

/-- If in addition the accessible-face normal derivative vanishes, only the
inaccessible face contributes.  This is the exact structure of the source's
equation (4.3): after differentiating equality of the two partial
Dirichlet-to-Neumann maps the accessible pairing cancels and a single
inaccessible-boundary term remains. -/
theorem lateralFlux_of_accessibleCancellation
    (u du v dv : Real -> Complex) (xMin xMax : Real)
    (hmin : u xMin = 0) (hmax : u xMax = 0) (haccessible : du xMax = 0) :
    lateralFlux u du v dv xMin xMax = -(du xMin * v xMin) := by
  rw [lateralFlux_of_zeroDirichletTrace u du v dv xMin xMax hmin hmax, haccessible]
  ring

/-! ## Time-integrated, finite-mode form -/

/-- The time-integrated, mode-summed Green defect
`sum_k int_0^T ( int (Delta u) v - int u (Delta v) ) dt` of equations (4.3)
and (4.4). -/
def spacetimeGreenDefect {Mode : Type*} (modes : Finset Mode)
    (timeHorizon xMin xMax : Real) (mu : Mode -> Complex)
    (u ddu v ddv : Mode -> Real -> Real -> Complex) : Complex :=
  ∑ k ∈ modes, ∫ t in (0 : Real)..timeHorizon,
    ((∫ x in xMin..xMax, tangentialLaplacian (mu k) (u k t) (ddu k t) x * v k t x)
      - (∫ x in xMin..xMax,
          u k t x * tangentialLaplacian (mu k) (v k t) (ddv k t) x))

/-- The time-integrated, mode-summed lateral flux. -/
def spacetimeLateralFlux {Mode : Type*} (modes : Finset Mode)
    (timeHorizon xMin xMax : Real)
    (u du v dv : Mode -> Real -> Real -> Complex) : Complex :=
  ∑ k ∈ modes, ∫ t in (0 : Real)..timeHorizon,
    lateralFlux (u k t) (du k t) (v k t) (dv k t) xMin xMax

/-- The time-integrated, mode-summed inaccessible-face pairing of the source's
equation (4.3). -/
def spacetimeInaccessibleFlux {Mode : Type*} (modes : Finset Mode)
    (timeHorizon xMin : Real)
    (du v : Mode -> Real -> Real -> Complex) : Complex :=
  ∑ k ∈ modes, ∫ t in (0 : Real)..timeHorizon, du k t xMin * v k t xMin

/-- **The concrete spatial Green formula in spacetime form.** -/
theorem spacetimeGreenDefect_eq_lateralFlux {Mode : Type*} (modes : Finset Mode)
    (timeHorizon xMin xMax : Real) (mu : Mode -> Complex)
    (u du ddu v dv ddv : Mode -> Real -> Real -> Complex)
    (hpointwise : ∀ k ∈ modes, ∀ t ∈ uIcc (0 : Real) timeHorizon,
      (∫ x in xMin..xMax, tangentialLaplacian (mu k) (u k t) (ddu k t) x * v k t x)
          - (∫ x in xMin..xMax,
              u k t x * tangentialLaplacian (mu k) (v k t) (ddv k t) x)
        = lateralFlux (u k t) (du k t) (v k t) (dv k t) xMin xMax) :
    spacetimeGreenDefect modes timeHorizon xMin xMax mu u ddu v ddv
      = spacetimeLateralFlux modes timeHorizon xMin xMax u du v dv := by
  refine Finset.sum_congr rfl fun k hk => ?_
  exact intervalIntegral.integral_congr fun t ht => hpointwise k hk t ht

/-- **Equation (4.3) on the concrete slab core.**  With the source's zero
lateral Dirichlet trace and the accessible-face cancellation coming from
equality of the two partial Dirichlet-to-Neumann maps, the whole spatial Green
defect is the single inaccessible-boundary term. -/
theorem spacetimeGreenDefect_eq_inaccessibleFlux {Mode : Type*}
    (modes : Finset Mode) (timeHorizon xMin xMax : Real) (mu : Mode -> Complex)
    (u du ddu v dv ddv : Mode -> Real -> Real -> Complex)
    (hpointwise : ∀ k ∈ modes, ∀ t ∈ uIcc (0 : Real) timeHorizon,
      (∫ x in xMin..xMax, tangentialLaplacian (mu k) (u k t) (ddu k t) x * v k t x)
          - (∫ x in xMin..xMax,
              u k t x * tangentialLaplacian (mu k) (v k t) (ddv k t) x)
        = lateralFlux (u k t) (du k t) (v k t) (dv k t) xMin xMax)
    (hDirichletMin : ∀ k ∈ modes, ∀ t, u k t xMin = 0)
    (hDirichletMax : ∀ k ∈ modes, ∀ t, u k t xMax = 0)
    (hAccessible : ∀ k ∈ modes, ∀ t, du k t xMax = 0) :
    spacetimeGreenDefect modes timeHorizon xMin xMax mu u ddu v ddv
      = -spacetimeInaccessibleFlux modes timeHorizon xMin du v := by
  rw [spacetimeGreenDefect_eq_lateralFlux modes timeHorizon xMin xMax mu
    u du ddu v dv ddv hpointwise]
  rw [spacetimeLateralFlux, spacetimeInaccessibleFlux, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [← intervalIntegral.integral_neg]
  refine intervalIntegral.integral_congr fun t _ => ?_
  exact lateralFlux_of_accessibleCancellation (u k t) (du k t) (v k t) (dv k t)
    xMin xMax (hDirichletMin k hk t) (hDirichletMax k hk t) (hAccessible k hk t)

/-- One reviewable object collecting the concrete spatial Green inputs. -/
structure Certificate {Mode : Type*} (modes : Finset Mode)
    (timeHorizon xMin xMax : Real) (mu : Mode -> Complex)
    (u du ddu v dv ddv : Mode -> Real -> Real -> Complex) : Prop where
  pointwiseGreen : ∀ k ∈ modes, ∀ t ∈ uIcc (0 : Real) timeHorizon,
    (∫ x in xMin..xMax, tangentialLaplacian (mu k) (u k t) (ddu k t) x * v k t x)
        - (∫ x in xMin..xMax,
            u k t x * tangentialLaplacian (mu k) (v k t) (ddv k t) x)
      = lateralFlux (u k t) (du k t) (v k t) (dv k t) xMin xMax
  spacetimeGreen :
    spacetimeGreenDefect modes timeHorizon xMin xMax mu u ddu v ddv
      = spacetimeLateralFlux modes timeHorizon xMin xMax u du v dv

/-- The certificate is generated from the one-dimensional differentiability and
integrability data at every time and mode. -/
def certificate {Mode : Type*} (modes : Finset Mode)
    (timeHorizon xMin xMax : Real) (mu : Mode -> Complex)
    (u du ddu v dv ddv : Mode -> Real -> Real -> Complex)
    (hu : ∀ k ∈ modes, ∀ t, ∀ x ∈ uIcc xMin xMax,
      HasDerivAt (u k t) (du k t x) x)
    (hdu : ∀ k ∈ modes, ∀ t, ∀ x ∈ uIcc xMin xMax,
      HasDerivAt (du k t) (ddu k t x) x)
    (hv : ∀ k ∈ modes, ∀ t, ∀ x ∈ uIcc xMin xMax,
      HasDerivAt (v k t) (dv k t x) x)
    (hdv : ∀ k ∈ modes, ∀ t, ∀ x ∈ uIcc xMin xMax,
      HasDerivAt (dv k t) (ddv k t x) x)
    (hduInt : ∀ k ∈ modes, ∀ t, IntervalIntegrable (du k t) volume xMin xMax)
    (hdduInt : ∀ k ∈ modes, ∀ t, IntervalIntegrable (ddu k t) volume xMin xMax)
    (hdvInt : ∀ k ∈ modes, ∀ t, IntervalIntegrable (dv k t) volume xMin xMax)
    (hddvInt : ∀ k ∈ modes, ∀ t, IntervalIntegrable (ddv k t) volume xMin xMax)
    (hUV : ∀ k ∈ modes, ∀ t,
      IntervalIntegrable (fun x => u k t x * v k t x) volume xMin xMax)
    (hDdUV : ∀ k ∈ modes, ∀ t,
      IntervalIntegrable (fun x => ddu k t x * v k t x) volume xMin xMax)
    (hUDdV : ∀ k ∈ modes, ∀ t,
      IntervalIntegrable (fun x => u k t x * ddv k t x) volume xMin xMax) :
    Certificate modes timeHorizon xMin xMax mu u du ddu v dv ddv where
  pointwiseGreen := by
    intro k hk t _
    exact green_secondIdentity_tangentialMode (hu k hk t) (hdu k hk t)
      (hv k hk t) (hdv k hk t) (hduInt k hk t) (hdduInt k hk t)
      (hdvInt k hk t) (hddvInt k hk t) (hUV k hk t) (hDdUV k hk t) (hUDdV k hk t)
  spacetimeGreen := by
    refine spacetimeGreenDefect_eq_lateralFlux modes timeHorizon xMin xMax mu
      u du ddu v dv ddv fun k hk t _ => ?_
    exact green_secondIdentity_tangentialMode (hu k hk t) (hdu k hk t)
      (hv k hk t) (hdv k hk t) (hduInt k hk t) (hdduInt k hk t)
      (hdvInt k hk t) (hddvInt k hk t) (hUV k hk t) (hDdUV k hk t) (hUDdV k hk t)

end LiuWang2025SemilinearWaveSpatialGreenCore
