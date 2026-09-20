import LiuWang.LiuWang2025SemilinearWaveSpatialGreenCore
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Liu--Wang 2025: the full spacetime Green identity on the slab core

Source: Boya Liu and Weinan Wang, *On a partial data inverse problem for the
semi-linear wave equation*, arXiv:2511.08794v1, Section 4, equations
(4.2)--(4.3).

`LiuWang2025SemilinearWaveTemporalGreen` supplies the temporal half of the
Lorentzian Green identity on a directed Cauchy core, and
`LiuWang2025SemilinearWaveSpatialGreenCore` the spatial half with the lateral
normal-trace flux.  Fusing them requires exchanging the order of the `t` and
`x` integrations, which neither module performs.

This module performs it, and assembles the full identity.  For a pair of
smooth functions on the spacetime slab `[0, T] x [xMin, xMax]`, with `u`
carrying the source's zero initial Cauchy data and `v` the zero terminal
Cauchy data, Lean proves

`int_0^T int_{xMin}^{xMax} ( (Box u) v - u (Box v) ) dx dt
    = - int_0^T [ u_x v - u v_x ]_{xMin}^{xMax} dt`,

with `Box w = w_tt - w_xx + mu w` the separated wave operator of one
tangential mode.  Combined with the homogeneous lateral Dirichlet condition
and the accessible-face cancellation, this is exactly the shape of equation
(4.3): the spacetime source pairing equals a single inaccessible-boundary
term.

## Contents

* `swap_intervalIntegral` : Fubini for a jointly continuous integrand on a
  spacetime rectangle, in interval-integral form;
* `SlabWavePair` : the smooth data of the two directed solutions;
* `temporalCancellation` : the source's directed Cauchy data kills the
  temporal pairing at every `x`;
* `spatialFlux` : the spatial pairing at every `t` is the lateral flux;
* `greenIdentity` : the full spacetime identity;
* `greenIdentity_inaccessible` : its equation-(4.3) form after the lateral
  Dirichlet condition and the accessible-face cancellation.

## Scope

The slab is one normal variable together with one separated tangential mode,
and the data are the smoothness and directed Cauchy conditions that a smooth
solution has.  Producing such solutions from the initial boundary value
problem is the well-posedness obligation and is not addressed here.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory Set

namespace LiuWang2025SemilinearWaveSpacetimeGreenCore

open LiuWang2025SemilinearWaveSpatialGreenCore

/-! ## Fubini on a spacetime rectangle -/

/-- Exchange of the two interval integrations for a jointly continuous
integrand. -/
theorem swap_intervalIntegral {F : Real -> Real -> Complex}
    (hF : Continuous (Function.uncurry F))
    {a b c d : Real} (hab : a <= b) (hcd : c <= d) :
    (∫ t in a..b, ∫ x in c..d, F t x) = ∫ x in c..d, ∫ t in a..b, F t x := by
  have hcompact : IsCompact (Icc a b ×ˢ Icc c d) := isCompact_Icc.prod isCompact_Icc
  have hIcc : IntegrableOn (Function.uncurry F) (Icc a b ×ˢ Icc c d) volume :=
    hF.continuousOn.integrableOn_compact hcompact
  have hsubset : Ioc a b ×ˢ Ioc c d ⊆ Icc a b ×ˢ Icc c d :=
    Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self
  have hIoc : IntegrableOn (Function.uncurry F) (Ioc a b ×ˢ Ioc c d) volume :=
    hIcc.mono_set hsubset
  have hprod : Integrable (Function.uncurry F)
      ((volume.restrict (uIoc a b)).prod (volume.restrict (uIoc c d))) := by
    rw [Set.uIoc_of_le hab, Set.uIoc_of_le hcd, Measure.prod_restrict]
    rw [← MeasureTheory.Measure.volume_eq_prod]
    exact hIoc
  have hswap := MeasureTheory.intervalIntegral_integral_swap
    (f := F) (a := a) (b := b) (μ := volume.restrict (uIoc c d)) hprod
  rw [Set.uIoc_of_le hcd] at hswap
  simpa [intervalIntegral.integral_of_le hcd] using hswap

/-! ## Slices of a jointly continuous function -/

theorem continuous_sliceT {f : Real -> Real -> Complex}
    (h : Continuous (Function.uncurry f)) (x : Real) :
    Continuous (fun t => f t x) := by
  have hmap : Continuous (fun t : Real => (t, x)) := by fun_prop
  exact h.comp hmap

theorem continuous_sliceX {f : Real -> Real -> Complex}
    (h : Continuous (Function.uncurry f)) (t : Real) :
    Continuous (f t) := by
  have hmap : Continuous (fun x : Real => (t, x)) := by fun_prop
  exact h.comp hmap

/-! ## The directed smooth pair on the slab -/

/-- Two smooth functions on the spacetime slab, `u` with the source's zero
initial Cauchy data and `v` with the zero terminal Cauchy data. -/
structure SlabWavePair (timeHorizon xMin xMax : Real) where
  u : Real -> Real -> Complex
  ut : Real -> Real -> Complex
  utt : Real -> Real -> Complex
  ux : Real -> Real -> Complex
  uxx : Real -> Real -> Complex
  v : Real -> Real -> Complex
  vt : Real -> Real -> Complex
  vtt : Real -> Real -> Complex
  vx : Real -> Real -> Complex
  vxx : Real -> Real -> Complex
  cont_u : Continuous (Function.uncurry u)
  cont_ut : Continuous (Function.uncurry ut)
  cont_utt : Continuous (Function.uncurry utt)
  cont_ux : Continuous (Function.uncurry ux)
  cont_uxx : Continuous (Function.uncurry uxx)
  cont_v : Continuous (Function.uncurry v)
  cont_vt : Continuous (Function.uncurry vt)
  cont_vtt : Continuous (Function.uncurry vtt)
  cont_vx : Continuous (Function.uncurry vx)
  cont_vxx : Continuous (Function.uncurry vxx)
  deriv_u_t : ∀ t x, HasDerivAt (fun s => u s x) (ut t x) t
  deriv_ut_t : ∀ t x, HasDerivAt (fun s => ut s x) (utt t x) t
  deriv_v_t : ∀ t x, HasDerivAt (fun s => v s x) (vt t x) t
  deriv_vt_t : ∀ t x, HasDerivAt (fun s => vt s x) (vtt t x) t
  deriv_u_x : ∀ t x, HasDerivAt (u t) (ux t x) x
  deriv_ux_x : ∀ t x, HasDerivAt (ux t) (uxx t x) x
  deriv_v_x : ∀ t x, HasDerivAt (v t) (vx t x) x
  deriv_vx_x : ∀ t x, HasDerivAt (vx t) (vxx t x) x
  u_initial : ∀ x, u 0 x = 0
  ut_initial : ∀ x, ut 0 x = 0
  v_terminal : ∀ x, v timeHorizon x = 0
  vt_terminal : ∀ x, vt timeHorizon x = 0
  timeHorizon_nonneg : 0 <= timeHorizon
  slab_le : xMin <= xMax

namespace SlabWavePair

variable {timeHorizon xMin xMax : Real} (P : SlabWavePair timeHorizon xMin xMax)

/-- The separated wave operator `Box w = w_tt - w_xx + mu w` acting on `u`. -/
def boxU (mu : Complex) (t x : Real) : Complex :=
  P.utt t x - P.uxx t x + mu * P.u t x

/-- The same operator acting on `v`. -/
def boxV (mu : Complex) (t x : Real) : Complex :=
  P.vtt t x - P.vxx t x + mu * P.v t x

/-- The spacetime integrand of equation (4.2). -/
def greenIntegrand (mu : Complex) (t x : Real) : Complex :=
  P.boxU mu t x * P.v t x - P.u t x * P.boxV mu t x

/-- The temporal pairing. -/
def temporalIntegrand (t x : Real) : Complex :=
  P.utt t x * P.v t x - P.u t x * P.vtt t x

/-- The spatial pairing. -/
def spatialIntegrand (t x : Real) : Complex :=
  P.uxx t x * P.v t x - P.u t x * P.vxx t x

theorem greenIntegrand_eq (mu : Complex) (t x : Real) :
    P.greenIntegrand mu t x = P.temporalIntegrand t x - P.spatialIntegrand t x := by
  simp only [greenIntegrand, temporalIntegrand, spatialIntegrand, boxU, boxV]
  ring

theorem continuous_temporalIntegrand :
    Continuous (Function.uncurry P.temporalIntegrand) := by
  have h1 : Continuous (Function.uncurry P.utt) := P.cont_utt
  have h2 : Continuous (Function.uncurry P.v) := P.cont_v
  have h3 : Continuous (Function.uncurry P.u) := P.cont_u
  have h4 : Continuous (Function.uncurry P.vtt) := P.cont_vtt
  exact (h1.mul h2).sub (h3.mul h4)

theorem continuous_spatialIntegrand :
    Continuous (Function.uncurry P.spatialIntegrand) := by
  exact (P.cont_uxx.mul P.cont_v).sub (P.cont_u.mul P.cont_vxx)

theorem continuous_greenIntegrand (mu : Complex) :
    Continuous (Function.uncurry (P.greenIntegrand mu)) := by
  have hfun : Function.uncurry (P.greenIntegrand mu)
      = fun p : Real × Real =>
        Function.uncurry P.temporalIntegrand p
          - Function.uncurry P.spatialIntegrand p := by
    funext p
    exact P.greenIntegrand_eq mu p.1 p.2
  rw [hfun]
  exact P.continuous_temporalIntegrand.sub P.continuous_spatialIntegrand

/-! ### The temporal half -/

/-- **The directed Cauchy data cancel the temporal pairing at every `x`.** -/
theorem temporalCancellation (x : Real) :
    (∫ t in (0 : Real)..timeHorizon, P.temporalIntegrand t x) = 0 := by
  have hbyparts :=
    LiuWang2025SemilinearWaveTemporalGreen.secondDerivative_timeIntegrationByParts_zeroCauchy
      (u := fun t => P.u t x) (du := fun t => P.ut t x) (ddu := fun t => P.utt t x)
      (v := fun t => P.v t x) (dv := fun t => P.vt t x) (ddv := fun t => P.vtt t x)
      (timeHorizon := timeHorizon)
      (fun t _ => P.deriv_u_t t x) (fun t _ => P.deriv_ut_t t x)
      (fun t _ => P.deriv_v_t t x) (fun t _ => P.deriv_vt_t t x)
      ((continuous_sliceT P.cont_ut x).intervalIntegrable _ _)
      ((continuous_sliceT P.cont_utt x).intervalIntegrable _ _)
      ((continuous_sliceT P.cont_vt x).intervalIntegrable _ _)
      ((continuous_sliceT P.cont_vtt x).intervalIntegrable _ _)
      (P.u_initial x) (P.ut_initial x) (P.v_terminal x) (P.vt_terminal x)
  have hsub : (∫ t in (0 : Real)..timeHorizon, P.temporalIntegrand t x)
      = (∫ t in (0 : Real)..timeHorizon, P.utt t x * P.v t x)
        - ∫ t in (0 : Real)..timeHorizon, P.u t x * P.vtt t x :=
    intervalIntegral.integral_sub
      (((continuous_sliceT P.cont_utt x).mul (continuous_sliceT P.cont_v x)).intervalIntegrable _ _)
      (((continuous_sliceT P.cont_u x).mul (continuous_sliceT P.cont_vtt x)).intervalIntegrable _ _)
  rw [hsub, hbyparts, sub_self]

/-! ### The spatial half -/

/-- **The spatial pairing is the lateral flux at every `t`.** -/
theorem spatialFlux (t : Real) :
    (∫ x in xMin..xMax, P.spatialIntegrand t x)
      = lateralFlux (P.u t) (P.ux t) (P.v t) (P.vx t) xMin xMax := by
  have hcore := green_secondIdentity
    (u := P.u t) (du := P.ux t) (ddu := P.uxx t)
    (v := P.v t) (dv := P.vx t) (ddv := P.vxx t)
    (xMin := xMin) (xMax := xMax)
    (fun x _ => P.deriv_u_x t x) (fun x _ => P.deriv_ux_x t x)
    (fun x _ => P.deriv_v_x t x) (fun x _ => P.deriv_vx_x t x)
    ((continuous_sliceX P.cont_ux t).intervalIntegrable _ _)
    ((continuous_sliceX P.cont_uxx t).intervalIntegrable _ _)
    ((continuous_sliceX P.cont_vx t).intervalIntegrable _ _)
    ((continuous_sliceX P.cont_vxx t).intervalIntegrable _ _)
  have hsub : (∫ x in xMin..xMax, P.spatialIntegrand t x)
      = (∫ x in xMin..xMax, P.uxx t x * P.v t x)
        - ∫ x in xMin..xMax, P.u t x * P.vxx t x :=
    intervalIntegral.integral_sub
      (((continuous_sliceX P.cont_uxx t).mul (continuous_sliceX P.cont_v t)).intervalIntegrable _ _)
      (((continuous_sliceX P.cont_u t).mul (continuous_sliceX P.cont_vxx t)).intervalIntegrable _ _)
  rw [hsub]
  exact hcore

/-! ### The full spacetime identity -/

/-- **The Lorentzian Green identity of equation (4.2)--(4.3) on the slab
core.**  Both halves are genuine calculus: the temporal one integrates by
parts twice against the directed Cauchy data, the spatial one carries the
lateral normal-trace flux, and the two are fused by Fubini. -/
theorem greenIdentity (mu : Complex) :
    (∫ t in (0 : Real)..timeHorizon, ∫ x in xMin..xMax, P.greenIntegrand mu t x)
      = -∫ t in (0 : Real)..timeHorizon,
          lateralFlux (P.u t) (P.ux t) (P.v t) (P.vx t) xMin xMax := by
  have hswapGreen := swap_intervalIntegral (P.continuous_greenIntegrand mu)
    P.timeHorizon_nonneg P.slab_le
  have hswapSpatial := swap_intervalIntegral P.continuous_spatialIntegrand
    P.timeHorizon_nonneg P.slab_le
  have hinner : ∀ x : Real,
      (∫ t in (0 : Real)..timeHorizon, P.greenIntegrand mu t x)
        = -∫ t in (0 : Real)..timeHorizon, P.spatialIntegrand t x := by
    intro x
    have hcongr : (∫ t in (0 : Real)..timeHorizon, P.greenIntegrand mu t x)
        = ∫ t in (0 : Real)..timeHorizon,
            (P.temporalIntegrand t x - P.spatialIntegrand t x) :=
      intervalIntegral.integral_congr fun t _ => P.greenIntegrand_eq mu t x
    have hsub : (∫ t in (0 : Real)..timeHorizon,
          (P.temporalIntegrand t x - P.spatialIntegrand t x))
        = (∫ t in (0 : Real)..timeHorizon, P.temporalIntegrand t x)
          - ∫ t in (0 : Real)..timeHorizon, P.spatialIntegrand t x :=
      intervalIntegral.integral_sub
        ((continuous_sliceT P.continuous_temporalIntegrand x).intervalIntegrable _ _)
        ((continuous_sliceT P.continuous_spatialIntegrand x).intervalIntegrable _ _)
    rw [hcongr, hsub, P.temporalCancellation x, zero_sub]
  calc (∫ t in (0 : Real)..timeHorizon, ∫ x in xMin..xMax, P.greenIntegrand mu t x)
      = ∫ x in xMin..xMax, ∫ t in (0 : Real)..timeHorizon, P.greenIntegrand mu t x :=
        hswapGreen
    _ = ∫ x in xMin..xMax,
          -∫ t in (0 : Real)..timeHorizon, P.spatialIntegrand t x :=
        intervalIntegral.integral_congr fun x _ => hinner x
    _ = -∫ x in xMin..xMax, ∫ t in (0 : Real)..timeHorizon, P.spatialIntegrand t x := by
        rw [intervalIntegral.integral_neg]
    _ = -∫ t in (0 : Real)..timeHorizon, ∫ x in xMin..xMax, P.spatialIntegrand t x := by
        rw [hswapSpatial]
    _ = -∫ t in (0 : Real)..timeHorizon,
          lateralFlux (P.u t) (P.ux t) (P.v t) (P.vx t) xMin xMax := by
        congr 1
        exact intervalIntegral.integral_congr fun t _ => P.spatialFlux t

/-- **Equation (4.3) on the slab core.**  With the source's homogeneous
lateral Dirichlet condition and the accessible-face cancellation coming from
equality of the two partial Dirichlet-to-Neumann maps, the whole spacetime
pairing is a single inaccessible-boundary term. -/
theorem greenIdentity_inaccessible (mu : Complex)
    (hDirichletMin : ∀ t, P.u t xMin = 0) (hDirichletMax : ∀ t, P.u t xMax = 0)
    (hAccessible : ∀ t, P.ux t xMax = 0) :
    (∫ t in (0 : Real)..timeHorizon, ∫ x in xMin..xMax, P.greenIntegrand mu t x)
      = ∫ t in (0 : Real)..timeHorizon, P.ux t xMin * P.v t xMin := by
  rw [P.greenIdentity mu]
  rw [← intervalIntegral.integral_neg]
  refine intervalIntegral.integral_congr fun t _ => ?_
  rw [lateralFlux_of_accessibleCancellation (P.u t) (P.ux t) (P.v t) (P.vx t)
    xMin xMax (hDirichletMin t) (hDirichletMax t) (hAccessible t)]
  ring

/-- One reviewable object collecting the full spacetime Green identity. -/
structure Certificate (mu : Complex) : Prop where
  temporalHalf : ∀ x : Real,
    (∫ t in (0 : Real)..timeHorizon, P.temporalIntegrand t x) = 0
  spatialHalf : ∀ t : Real,
    (∫ x in xMin..xMax, P.spatialIntegrand t x)
      = lateralFlux (P.u t) (P.ux t) (P.v t) (P.vx t) xMin xMax
  spacetimeGreen :
    (∫ t in (0 : Real)..timeHorizon, ∫ x in xMin..xMax, P.greenIntegrand mu t x)
      = -∫ t in (0 : Real)..timeHorizon,
          lateralFlux (P.u t) (P.ux t) (P.v t) (P.vx t) xMin xMax

/-- The certificate is generated from the smoothness and directed Cauchy
data. -/
def certificate (mu : Complex) : Certificate P mu where
  temporalHalf := P.temporalCancellation
  spatialHalf := P.spatialFlux
  spacetimeGreen := P.greenIdentity mu

end SlabWavePair

end LiuWang2025SemilinearWaveSpacetimeGreenCore
