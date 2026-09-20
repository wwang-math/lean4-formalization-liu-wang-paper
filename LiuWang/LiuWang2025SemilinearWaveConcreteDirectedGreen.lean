import LiuWang.LiuWang2025SemilinearWaveSpacetimeGreenCore
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Liu--Wang 2025: a concrete directed wave Green model

Source: Boya Liu and Weinan Wang, *On a partial data inverse problem for the
semi-linear wave equation*, arXiv:2511.08794v1, Section 4.

`LiuWang2025SemilinearWaveDirectedGreenRealization.DirectedWaveGreenModel` is
the abstract engine that turns time integration by parts and the spatial Green
formula into the Lorentzian Green identity feeding equations (4.2)--(4.3).  Its
carriers were abstract `Complex`-modules and its two analytic fields were
inputs.

This module builds an *instance* of that engine out of genuine function
spaces and genuine integrals on the spacetime slab `[0,T] x [xMin,xMax]`:

* the forward carrier is the space of five-component jets
  `(u, u_t, u_tt, u_x, u_xx)` of jointly continuous functions on the slab, for
  which the four derivative relations hold, together with the source's zero
  initial Cauchy data and zero lateral Dirichlet trace -- all linear
  conditions, so the carrier is a genuine `Complex`-submodule;
* the backward carrier is the same with zero *terminal* Cauchy data and no
  lateral condition, as the paper's probe `w_0` requires;
* the residual space is the space of jointly continuous functions;
* the bulk pairings are honest integrals over the spacetime rectangle against
  the product measure;
* the boundary carriers are the normal derivative traces of `u` and the
  Dirichlet traces of `v` on the two faces, and the boundary pairing is the
  honest time integral of the source's lateral flux.

Both analytic fields are then *theorems*: `timeIntegrationByParts` is two
integrations by parts against the directed Cauchy data, and
`spatialGreenFormula` is Green's second identity in the normal variable, the
two being connected to the product-measure pairings by Fubini.

## Scope

The slab is one normal variable with one separated tangential mode, and the
carriers consist of classically smooth jets rather than Sobolev graph spaces.
Producing members of the forward carrier from the initial boundary value
problem is the well-posedness obligation, which is not addressed here.
-/

noncomputable section

open MeasureTheory Set

namespace LiuWang2025SemilinearWaveConcreteDirectedGreen

open LiuWang2025SemilinearWaveSpatialGreenCore
open LiuWang2025SemilinearWaveSpacetimeGreenCore

/-! ## Jointly continuous functions on the slab and on the time axis -/

/-- Jointly continuous complex functions of `(t, x)`. -/
def slabFunctions : Submodule Complex (Real -> Real -> Complex) where
  carrier := {F | Continuous (Function.uncurry F)}
  zero_mem' := by
    show Continuous (Function.uncurry (0 : Real -> Real -> Complex))
    exact continuous_const
  add_mem' := by
    intro F G hF hG
    exact hF.add hG
  smul_mem' := by
    intro c F hF
    exact hF.const_smul c

/-- Continuous complex functions of `t`. -/
def lineFunctions : Submodule Complex (Real -> Complex) where
  carrier := {f | Continuous f}
  zero_mem' := continuous_const
  add_mem' := by
    intro f g hf hg
    exact hf.add hg
  smul_mem' := by
    intro c f hf
    exact hf.const_smul c

@[simp] theorem mem_slabFunctions {F : Real -> Real -> Complex} :
    F ∈ slabFunctions ↔ Continuous (Function.uncurry F) := Iff.rfl

@[simp] theorem mem_lineFunctions {f : Real -> Complex} :
    f ∈ lineFunctions ↔ Continuous f := Iff.rfl

/-! ## Slab jets -/

/-- A five-component jet `(w, w_t, w_tt, w_x, w_xx)`. -/
abbrev Jet : Type := Fin 5 -> (Real -> Real -> Complex)

namespace Jet

/-- The state. -/
abbrev st (j : Jet) : Real -> Real -> Complex := j 0
/-- The time derivative. -/
abbrev dt (j : Jet) : Real -> Real -> Complex := j 1
/-- The second time derivative. -/
abbrev dtt (j : Jet) : Real -> Real -> Complex := j 2
/-- The normal derivative. -/
abbrev dx (j : Jet) : Real -> Real -> Complex := j 3
/-- The second normal derivative. -/
abbrev dxx (j : Jet) : Real -> Real -> Complex := j 4

end Jet

/-- The smoothness and derivative relations shared by both carriers. -/
def SmoothJet (j : Jet) : Prop :=
  (∀ i, Continuous (Function.uncurry (j i))) ∧
  (∀ t x, HasDerivAt (fun s => j 0 s x) (j 1 t x) t) ∧
  (∀ t x, HasDerivAt (fun s => j 1 s x) (j 2 t x) t) ∧
  (∀ t x, HasDerivAt (j 0 t) (j 3 t x) x) ∧
  (∀ t x, HasDerivAt (j 3 t) (j 4 t x) x)

theorem SmoothJet.zero : SmoothJet (0 : Jet) := by
  refine ⟨fun i => continuous_const, ?_, ?_, ?_, ?_⟩ <;>
    intro t x <;> simpa using (hasDerivAt_const _ (0 : Complex))

theorem SmoothJet.add {j k : Jet} (hj : SmoothJet j) (hk : SmoothJet k) :
    SmoothJet (j + k) := by
  refine ⟨fun i => (hj.1 i).add (hk.1 i), ?_, ?_, ?_, ?_⟩
  · intro t x; exact (hj.2.1 t x).add (hk.2.1 t x)
  · intro t x; exact (hj.2.2.1 t x).add (hk.2.2.1 t x)
  · intro t x; exact (hj.2.2.2.1 t x).add (hk.2.2.2.1 t x)
  · intro t x; exact (hj.2.2.2.2 t x).add (hk.2.2.2.2 t x)

theorem SmoothJet.smul (c : Complex) {j : Jet} (hj : SmoothJet j) :
    SmoothJet (c • j) := by
  refine ⟨fun i => (hj.1 i).const_smul c, ?_, ?_, ?_, ?_⟩
  · intro t x; exact (hj.2.1 t x).const_smul c
  · intro t x; exact (hj.2.2.1 t x).const_smul c
  · intro t x; exact (hj.2.2.2.1 t x).const_smul c
  · intro t x; exact (hj.2.2.2.2 t x).const_smul c

/-- The source's forward carrier: smooth jets with zero initial Cauchy data
and zero lateral Dirichlet trace. -/
def forwardCarrier (xMin xMax : Real) : Submodule Complex Jet where
  carrier := {j | SmoothJet j ∧ (∀ x, j 0 0 x = 0) ∧ (∀ x, j 1 0 x = 0) ∧
    (∀ t, j 0 t xMin = 0) ∧ (∀ t, j 0 t xMax = 0)}
  zero_mem' := ⟨SmoothJet.zero, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩
  add_mem' := by
    rintro j k ⟨hjs, hj1, hj2, hj3, hj4⟩ ⟨hks, hk1, hk2, hk3, hk4⟩
    refine ⟨hjs.add hks, ?_, ?_, ?_, ?_⟩
    · intro x; show j 0 0 x + k 0 0 x = 0; rw [hj1 x, hk1 x, add_zero]
    · intro x; show j 1 0 x + k 1 0 x = 0; rw [hj2 x, hk2 x, add_zero]
    · intro t; show j 0 t xMin + k 0 t xMin = 0; rw [hj3 t, hk3 t, add_zero]
    · intro t; show j 0 t xMax + k 0 t xMax = 0; rw [hj4 t, hk4 t, add_zero]
  smul_mem' := by
    rintro c j ⟨hjs, hj1, hj2, hj3, hj4⟩
    refine ⟨hjs.smul c, ?_, ?_, ?_, ?_⟩
    · intro x; show c * j 0 0 x = 0; rw [hj1 x, mul_zero]
    · intro x; show c * j 1 0 x = 0; rw [hj2 x, mul_zero]
    · intro t; show c * j 0 t xMin = 0; rw [hj3 t, mul_zero]
    · intro t; show c * j 0 t xMax = 0; rw [hj4 t, mul_zero]

/-- The source's backward carrier: smooth jets with zero terminal Cauchy
data. -/
def backwardCarrier (timeHorizon : Real) : Submodule Complex Jet where
  carrier := {j | SmoothJet j ∧ (∀ x, j 0 timeHorizon x = 0) ∧
    (∀ x, j 1 timeHorizon x = 0)}
  zero_mem' := ⟨SmoothJet.zero, fun _ => rfl, fun _ => rfl⟩
  add_mem' := by
    rintro j k ⟨hjs, hj1, hj2⟩ ⟨hks, hk1, hk2⟩
    refine ⟨hjs.add hks, ?_, ?_⟩
    · intro x; show j 0 timeHorizon x + k 0 timeHorizon x = 0; rw [hj1 x, hk1 x, add_zero]
    · intro x; show j 1 timeHorizon x + k 1 timeHorizon x = 0; rw [hj2 x, hk2 x, add_zero]
  smul_mem' := by
    rintro c j ⟨hjs, hj1, hj2⟩
    refine ⟨hjs.smul c, ?_, ?_⟩
    · intro x; show c * j 0 timeHorizon x = 0; rw [hj1 x, mul_zero]
    · intro x; show c * j 1 timeHorizon x = 0; rw [hj2 x, mul_zero]

/-! ## The spacetime rectangle and its pairings -/

/-- The spacetime rectangle carrying the bulk pairings. -/
def rect (timeHorizon xMin xMax : Real) : Set (Real × Real) :=
  Set.Ioc 0 timeHorizon ×ˢ Set.Ioc xMin xMax

theorem integrableOn_rect {F : Real × Real -> Complex} (hF : Continuous F)
    (timeHorizon xMin xMax : Real) :
    IntegrableOn F (rect timeHorizon xMin xMax) volume := by
  have hcompact : IsCompact (Icc 0 timeHorizon ×ˢ Icc xMin xMax) :=
    isCompact_Icc.prod isCompact_Icc
  have h : IntegrableOn F (Icc 0 timeHorizon ×ˢ Icc xMin xMax) volume :=
    hF.continuousOn.integrableOn_compact hcompact
  exact h.mono_set (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)

/-- The bulk pairing: an honest integral over the spacetime rectangle. -/
def slabPairing (timeHorizon xMin xMax : Real)
    (F G : Real -> Real -> Complex) : Complex :=
  ∫ p in rect timeHorizon xMin xMax, F p.1 p.2 * G p.1 p.2

theorem integrableOn_slabProduct {F G : Real -> Real -> Complex}
    (hF : Continuous (Function.uncurry F)) (hG : Continuous (Function.uncurry G))
    (timeHorizon xMin xMax : Real) :
    IntegrableOn (fun p : Real × Real => F p.1 p.2 * G p.1 p.2)
      (rect timeHorizon xMin xMax) volume :=
  integrableOn_rect (hF.mul hG) timeHorizon xMin xMax

theorem slabPairing_add_left {F₁ F₂ G : Real -> Real -> Complex}
    (hF₁ : Continuous (Function.uncurry F₁)) (hF₂ : Continuous (Function.uncurry F₂))
    (hG : Continuous (Function.uncurry G)) (timeHorizon xMin xMax : Real) :
    slabPairing timeHorizon xMin xMax (F₁ + F₂) G
      = slabPairing timeHorizon xMin xMax F₁ G
        + slabPairing timeHorizon xMin xMax F₂ G := by
  have h : (fun p : Real × Real => (F₁ + F₂) p.1 p.2 * G p.1 p.2)
      = fun p : Real × Real => F₁ p.1 p.2 * G p.1 p.2 + F₂ p.1 p.2 * G p.1 p.2 := by
    funext p
    show (F₁ p.1 p.2 + F₂ p.1 p.2) * G p.1 p.2 = _
    ring
  simp only [slabPairing, h]
  exact integral_add (integrableOn_slabProduct hF₁ hG _ _ _)
    (integrableOn_slabProduct hF₂ hG _ _ _)

theorem slabPairing_add_right {F G₁ G₂ : Real -> Real -> Complex}
    (hF : Continuous (Function.uncurry F)) (hG₁ : Continuous (Function.uncurry G₁))
    (hG₂ : Continuous (Function.uncurry G₂)) (timeHorizon xMin xMax : Real) :
    slabPairing timeHorizon xMin xMax F (G₁ + G₂)
      = slabPairing timeHorizon xMin xMax F G₁
        + slabPairing timeHorizon xMin xMax F G₂ := by
  have h : (fun p : Real × Real => F p.1 p.2 * (G₁ + G₂) p.1 p.2)
      = fun p : Real × Real => F p.1 p.2 * G₁ p.1 p.2 + F p.1 p.2 * G₂ p.1 p.2 := by
    funext p
    show F p.1 p.2 * (G₁ p.1 p.2 + G₂ p.1 p.2) = _
    ring
  simp only [slabPairing, h]
  exact integral_add (integrableOn_slabProduct hF hG₁ _ _ _)
    (integrableOn_slabProduct hF hG₂ _ _ _)

theorem slabPairing_smul_left (c : Complex) (F G : Real -> Real -> Complex)
    (timeHorizon xMin xMax : Real) :
    slabPairing timeHorizon xMin xMax (c • F) G
      = c * slabPairing timeHorizon xMin xMax F G := by
  have h : (fun p : Real × Real => (c • F) p.1 p.2 * G p.1 p.2)
      = fun p : Real × Real => c * (F p.1 p.2 * G p.1 p.2) := by
    funext p
    show c * F p.1 p.2 * G p.1 p.2 = _
    ring
  simp only [slabPairing, h]
  exact integral_const_mul c _

theorem slabPairing_smul_right (c : Complex) (F G : Real -> Real -> Complex)
    (timeHorizon xMin xMax : Real) :
    slabPairing timeHorizon xMin xMax F (c • G)
      = c * slabPairing timeHorizon xMin xMax F G := by
  have h : (fun p : Real × Real => F p.1 p.2 * (c • G) p.1 p.2)
      = fun p : Real × Real => c * (F p.1 p.2 * G p.1 p.2) := by
    funext p
    show F p.1 p.2 * (c * G p.1 p.2) = _
    ring
  simp only [slabPairing, h]
  exact integral_const_mul c _

/-! ## The boundary pairing -/

/-- The time pairing on one face of the lateral boundary. -/
def linePairing (timeHorizon : Real) (f g : Real -> Complex) : Complex :=
  ∫ t in Set.Ioc (0 : Real) timeHorizon, f t * g t

theorem integrableOn_lineProduct {f g : Real -> Complex}
    (hf : Continuous f) (hg : Continuous g) (timeHorizon : Real) :
    IntegrableOn (fun t => f t * g t) (Set.Ioc (0 : Real) timeHorizon) volume := by
  have h : IntegrableOn (fun t => f t * g t) (Icc (0 : Real) timeHorizon) volume :=
    (hf.mul hg).continuousOn.integrableOn_compact isCompact_Icc
  exact h.mono_set Ioc_subset_Icc_self

/-- The full lateral boundary pairing of equation (4.3): accessible face minus
inaccessible face. -/
def boundaryPairing (timeHorizon : Real)
    (fMin fMax gMin gMax : Real -> Complex) : Complex :=
  linePairing timeHorizon fMax gMax - linePairing timeHorizon fMin gMin

/-! ## From the product-measure pairing to iterated interval integrals -/

theorem rectIntegral_eq_iterated {H : Real × Real -> Complex} (hH : Continuous H)
    {timeHorizon xMin xMax : Real} (hT : 0 <= timeHorizon) (hx : xMin <= xMax) :
    (∫ p in rect timeHorizon xMin xMax, H p)
      = ∫ t in (0 : Real)..timeHorizon, ∫ x in xMin..xMax, H (t, x) := by
  have hint : IntegrableOn H (Ioc 0 timeHorizon ×ˢ Ioc xMin xMax)
      (volume.prod volume) := by
    rw [← MeasureTheory.Measure.volume_eq_prod]
    exact integrableOn_rect hH timeHorizon xMin xMax
  have h := MeasureTheory.setIntegral_prod H hint
  rw [rect, MeasureTheory.Measure.volume_eq_prod, h,
    intervalIntegral.integral_of_le hT]
  refine setIntegral_congr_fun measurableSet_Ioc fun t _ => ?_
  rw [intervalIntegral.integral_of_le hx]

theorem slabPairing_eq_iterated {F G : Real -> Real -> Complex}
    (hF : Continuous (Function.uncurry F)) (hG : Continuous (Function.uncurry G))
    {timeHorizon xMin xMax : Real} (hT : 0 <= timeHorizon) (hx : xMin <= xMax) :
    slabPairing timeHorizon xMin xMax F G
      = ∫ t in (0 : Real)..timeHorizon, ∫ x in xMin..xMax, F t x * G t x :=
  rectIntegral_eq_iterated (hF.mul hG) hT hx

/-! ## The two analytic fields, as theorems on the concrete carriers -/

/-- **Time integration by parts on the concrete carriers.**  The forward jet's
zero initial Cauchy data and the backward jet's zero terminal Cauchy data
eliminate all four endpoint terms. -/
theorem concrete_timeIntegrationByParts
    {timeHorizon xMin xMax : Real} (hT : 0 <= timeHorizon) (hx : xMin <= xMax)
    {j k : Jet} (hj : SmoothJet j) (hk : SmoothJet k)
    (hj0 : ∀ x, j 0 0 x = 0) (hj1 : ∀ x, j 1 0 x = 0)
    (hk0 : ∀ x, k 0 timeHorizon x = 0) (hk1 : ∀ x, k 1 timeHorizon x = 0) :
    slabPairing timeHorizon xMin xMax (j 2) (k 0)
      = slabPairing timeHorizon xMin xMax (j 0) (k 2) := by
  have hswapL := swap_intervalIntegral
    (F := fun t x => j 2 t x * k 0 t x) ((hj.1 2).mul (hk.1 0)) hT hx
  have hswapR := swap_intervalIntegral
    (F := fun t x => j 0 t x * k 2 t x) ((hj.1 0).mul (hk.1 2)) hT hx
  have hslice : ∀ x : Real,
      (∫ t in (0 : Real)..timeHorizon, j 2 t x * k 0 t x)
        = ∫ t in (0 : Real)..timeHorizon, j 0 t x * k 2 t x := by
    intro x
    exact
      LiuWang2025SemilinearWaveTemporalGreen.secondDerivative_timeIntegrationByParts_zeroCauchy
        (u := fun t => j 0 t x) (du := fun t => j 1 t x) (ddu := fun t => j 2 t x)
        (v := fun t => k 0 t x) (dv := fun t => k 1 t x) (ddv := fun t => k 2 t x)
        (timeHorizon := timeHorizon)
        (fun t _ => hj.2.1 t x) (fun t _ => hj.2.2.1 t x)
        (fun t _ => hk.2.1 t x) (fun t _ => hk.2.2.1 t x)
        ((continuous_sliceT (hj.1 1) x).intervalIntegrable _ _)
        ((continuous_sliceT (hj.1 2) x).intervalIntegrable _ _)
        ((continuous_sliceT (hk.1 1) x).intervalIntegrable _ _)
        ((continuous_sliceT (hk.1 2) x).intervalIntegrable _ _)
        (hj0 x) (hj1 x) (hk0 x) (hk1 x)
  rw [slabPairing_eq_iterated (hj.1 2) (hk.1 0) hT hx,
    slabPairing_eq_iterated (hj.1 0) (hk.1 2) hT hx, hswapL, hswapR]
  exact intervalIntegral.integral_congr fun x _ => hslice x

/-- **The spatial Green formula on the concrete carriers.**  The tangential
eigenvalue cancels, the forward jet's zero lateral Dirichlet trace removes the
`u v_x` terms, and only the normal-derivative pairing on the two faces
survives. -/
theorem concrete_spatialGreenFormula
    {timeHorizon xMin xMax : Real} (hT : 0 <= timeHorizon) (hx : xMin <= xMax)
    (mu : Complex) {j k : Jet} (hj : SmoothJet j) (hk : SmoothJet k)
    (hjMin : ∀ t, j 0 t xMin = 0) (hjMax : ∀ t, j 0 t xMax = 0) :
    slabPairing timeHorizon xMin xMax (fun t x => j 4 t x - mu * j 0 t x) (k 0)
        - slabPairing timeHorizon xMin xMax (j 0)
            (fun t x => k 4 t x - mu * k 0 t x)
      = boundaryPairing timeHorizon (fun t => j 3 t xMin) (fun t => j 3 t xMax)
          (fun t => k 0 t xMin) (fun t => k 0 t xMax) := by
  have hcontLeft : Continuous
      (Function.uncurry fun t x => j 4 t x - mu * j 0 t x) :=
    (hj.1 4).sub (continuous_const.mul (hj.1 0))
  have hcontRight : Continuous
      (Function.uncurry fun t x => k 4 t x - mu * k 0 t x) :=
    (hk.1 4).sub (continuous_const.mul (hk.1 0))
  have hsub : slabPairing timeHorizon xMin xMax
        (fun t x => j 4 t x - mu * j 0 t x) (k 0)
      - slabPairing timeHorizon xMin xMax (j 0)
          (fun t x => k 4 t x - mu * k 0 t x)
      = ∫ p in rect timeHorizon xMin xMax,
          ((j 4 p.1 p.2 - mu * j 0 p.1 p.2) * k 0 p.1 p.2
            - j 0 p.1 p.2 * (k 4 p.1 p.2 - mu * k 0 p.1 p.2)) := by
    rw [slabPairing, slabPairing]
    exact (integral_sub (integrableOn_slabProduct hcontLeft (hk.1 0) _ _ _)
      (integrableOn_slabProduct (hj.1 0) hcontRight _ _ _)).symm
  have hcontDiff : Continuous
      (fun p : Real × Real =>
        (j 4 p.1 p.2 - mu * j 0 p.1 p.2) * k 0 p.1 p.2
          - j 0 p.1 p.2 * (k 4 p.1 p.2 - mu * k 0 p.1 p.2)) :=
    (hcontLeft.mul (hk.1 0)).sub ((hj.1 0).mul hcontRight)
  have hslice : ∀ t : Real,
      (∫ x in xMin..xMax,
          ((j 4 t x - mu * j 0 t x) * k 0 t x
            - j 0 t x * (k 4 t x - mu * k 0 t x)))
        = j 3 t xMax * k 0 t xMax - j 3 t xMin * k 0 t xMin := by
    intro t
    have hcongr : (∫ x in xMin..xMax,
          ((j 4 t x - mu * j 0 t x) * k 0 t x
            - j 0 t x * (k 4 t x - mu * k 0 t x)))
        = ∫ x in xMin..xMax, (j 4 t x * k 0 t x - j 0 t x * k 4 t x) := by
      refine intervalIntegral.integral_congr fun x _ => ?_
      ring
    have hsplit : (∫ x in xMin..xMax, (j 4 t x * k 0 t x - j 0 t x * k 4 t x))
        = (∫ x in xMin..xMax, j 4 t x * k 0 t x)
          - ∫ x in xMin..xMax, j 0 t x * k 4 t x :=
      intervalIntegral.integral_sub
        (((continuous_sliceX (hj.1 4) t).mul (continuous_sliceX (hk.1 0) t)).intervalIntegrable _ _)
        (((continuous_sliceX (hj.1 0) t).mul (continuous_sliceX (hk.1 4) t)).intervalIntegrable _ _)
    have hgreen := green_secondIdentity
      (u := j 0 t) (du := j 3 t) (ddu := j 4 t)
      (v := k 0 t) (dv := k 3 t) (ddv := k 4 t)
      (xMin := xMin) (xMax := xMax)
      (fun x _ => hj.2.2.2.1 t x) (fun x _ => hj.2.2.2.2 t x)
      (fun x _ => hk.2.2.2.1 t x) (fun x _ => hk.2.2.2.2 t x)
      ((continuous_sliceX (hj.1 3) t).intervalIntegrable _ _)
      ((continuous_sliceX (hj.1 4) t).intervalIntegrable _ _)
      ((continuous_sliceX (hk.1 3) t).intervalIntegrable _ _)
      ((continuous_sliceX (hk.1 4) t).intervalIntegrable _ _)
    rw [hcongr, hsplit, hgreen,
      lateralFlux_of_zeroDirichletTrace (j 0 t) (j 3 t) (k 0 t) (k 3 t)
        xMin xMax (hjMin t) (hjMax t)]
  rw [hsub, rectIntegral_eq_iterated hcontDiff hT hx]
  rw [intervalIntegral.integral_congr (g := fun t =>
    j 3 t xMax * k 0 t xMax - j 3 t xMin * k 0 t xMin) fun t _ => hslice t]
  rw [boundaryPairing, linePairing, linePairing,
    ← intervalIntegral.integral_of_le hT, ← intervalIntegral.integral_of_le hT]
  exact intervalIntegral.integral_sub
    (((continuous_sliceT (hj.1 3) xMax).mul (continuous_sliceT (hk.1 0) xMax)).intervalIntegrable _ _)
    (((continuous_sliceT (hj.1 3) xMin).mul (continuous_sliceT (hk.1 0) xMin)).intervalIntegrable _ _)

/-! ## Bilinearity of the boundary pairing -/

theorem linePairing_add_left {f₁ f₂ g : Real -> Complex}
    (hf₁ : Continuous f₁) (hf₂ : Continuous f₂) (hg : Continuous g)
    (timeHorizon : Real) :
    linePairing timeHorizon (f₁ + f₂) g
      = linePairing timeHorizon f₁ g + linePairing timeHorizon f₂ g := by
  have h : (fun t => (f₁ + f₂) t * g t)
      = fun t => f₁ t * g t + f₂ t * g t := by
    funext t
    show (f₁ t + f₂ t) * g t = _
    ring
  simp only [linePairing, h]
  exact integral_add (integrableOn_lineProduct hf₁ hg _)
    (integrableOn_lineProduct hf₂ hg _)

theorem linePairing_add_right {f g₁ g₂ : Real -> Complex}
    (hf : Continuous f) (hg₁ : Continuous g₁) (hg₂ : Continuous g₂)
    (timeHorizon : Real) :
    linePairing timeHorizon f (g₁ + g₂)
      = linePairing timeHorizon f g₁ + linePairing timeHorizon f g₂ := by
  have h : (fun t => f t * (g₁ + g₂) t)
      = fun t => f t * g₁ t + f t * g₂ t := by
    funext t
    show f t * (g₁ t + g₂ t) = _
    ring
  simp only [linePairing, h]
  exact integral_add (integrableOn_lineProduct hf hg₁ _)
    (integrableOn_lineProduct hf hg₂ _)

theorem linePairing_smul_left (c : Complex) (f g : Real -> Complex)
    (timeHorizon : Real) :
    linePairing timeHorizon (c • f) g = c * linePairing timeHorizon f g := by
  have h : (fun t => (c • f) t * g t) = fun t => c * (f t * g t) := by
    funext t
    show c * f t * g t = _
    ring
  simp only [linePairing, h]
  exact integral_const_mul c _

theorem linePairing_smul_right (c : Complex) (f g : Real -> Complex)
    (timeHorizon : Real) :
    linePairing timeHorizon f (c • g) = c * linePairing timeHorizon f g := by
  have h : (fun t => f t * (c • g) t) = fun t => c * (f t * g t) := by
    funext t
    show f t * (c * g t) = _
    ring
  simp only [linePairing, h]
  exact integral_const_mul c _

/-! ## The concrete directed wave Green model -/

/-- The residual space: jointly continuous functions on the slab. -/
abbrev Residual : Type := slabFunctions

/-- Normal-derivative traces on the two faces, inaccessible first. -/
abbrev BoundaryFlux : Type := lineFunctions × lineFunctions

/-- Dirichlet traces of the probe on the two faces, inaccessible first. -/
abbrev BoundaryValue : Type := lineFunctions × lineFunctions

/-- The slab geometry and the separated tangential eigenvalue. -/
structure SlabGeometry where
  timeHorizon : Real
  xMin : Real
  xMax : Real
  timeHorizon_nonneg : 0 <= timeHorizon
  slab_le : xMin <= xMax
  tangentialEigenvalue : Complex

namespace SlabGeometry

variable (S : SlabGeometry)

/-- The forward carrier: zero initial Cauchy data and zero lateral trace. -/
abbrev ForwardGraph : Type := (forwardCarrier S.xMin S.xMax)

/-- The backward carrier: zero terminal Cauchy data. -/
abbrev BackwardGraph : Type := (backwardCarrier S.timeHorizon)

/-- `u |-> u_tt`. -/
def forwardTimeSecondMap : S.ForwardGraph →ₗ[Complex] Residual where
  toFun := fun j => ⟨j.val 2, j.property.1.1 2⟩
  map_add' := by intro a b; rfl
  map_smul' := by intro c a; rfl

/-- `u |-> u_xx - mu u`, the separated spatial Laplacian. -/
def forwardSpatialMap : S.ForwardGraph →ₗ[Complex] Residual where
  toFun := fun j =>
    ⟨fun t x => j.val 4 t x - S.tangentialEigenvalue * j.val 0 t x,
      (j.property.1.1 4).sub (continuous_const.mul (j.property.1.1 0))⟩
  map_add' := by
    intro a b
    refine Subtype.ext ?_
    funext t x
    show a.val 4 t x + b.val 4 t x
        - S.tangentialEigenvalue * (a.val 0 t x + b.val 0 t x) = _
    show _ = (a.val 4 t x - S.tangentialEigenvalue * a.val 0 t x)
        + (b.val 4 t x - S.tangentialEigenvalue * b.val 0 t x)
    ring
  map_smul' := by
    intro c a
    refine Subtype.ext ?_
    funext t x
    show c * a.val 4 t x - S.tangentialEigenvalue * (c * a.val 0 t x) = _
    show _ = c * (a.val 4 t x - S.tangentialEigenvalue * a.val 0 t x)
    ring

/-- `v |-> v_tt`. -/
def backwardTimeSecondMap : S.BackwardGraph →ₗ[Complex] Residual where
  toFun := fun j => ⟨j.val 2, j.property.1.1 2⟩
  map_add' := by intro a b; rfl
  map_smul' := by intro c a; rfl

/-- `v |-> v_xx - mu v`. -/
def backwardSpatialMap : S.BackwardGraph →ₗ[Complex] Residual where
  toFun := fun j =>
    ⟨fun t x => j.val 4 t x - S.tangentialEigenvalue * j.val 0 t x,
      (j.property.1.1 4).sub (continuous_const.mul (j.property.1.1 0))⟩
  map_add' := by
    intro a b
    refine Subtype.ext ?_
    funext t x
    show a.val 4 t x + b.val 4 t x
        - S.tangentialEigenvalue * (a.val 0 t x + b.val 0 t x) = _
    show _ = (a.val 4 t x - S.tangentialEigenvalue * a.val 0 t x)
        + (b.val 4 t x - S.tangentialEigenvalue * b.val 0 t x)
    ring
  map_smul' := by
    intro c a
    refine Subtype.ext ?_
    funext t x
    show c * a.val 4 t x - S.tangentialEigenvalue * (c * a.val 0 t x) = _
    show _ = c * (a.val 4 t x - S.tangentialEigenvalue * a.val 0 t x)
    ring

/-- The accessible/inaccessible normal-derivative trace of the forward
state. -/
def normalTraceMap : S.ForwardGraph →ₗ[Complex] BoundaryFlux where
  toFun := fun j =>
    (⟨fun t => j.val 3 t S.xMin, continuous_sliceT (j.property.1.1 3) S.xMin⟩,
     ⟨fun t => j.val 3 t S.xMax, continuous_sliceT (j.property.1.1 3) S.xMax⟩)
  map_add' := by intro a b; rfl
  map_smul' := by intro c a; rfl

/-- The accessible/inaccessible Dirichlet trace of the probe. -/
def probeTraceMap : S.BackwardGraph →ₗ[Complex] BoundaryValue where
  toFun := fun j =>
    (⟨fun t => j.val 0 t S.xMin, continuous_sliceT (j.property.1.1 0) S.xMin⟩,
     ⟨fun t => j.val 0 t S.xMax, continuous_sliceT (j.property.1.1 0) S.xMax⟩)
  map_add' := by intro a b; rfl
  map_smul' := by intro c a; rfl

/-- The bulk pairing, an honest integral over the spacetime rectangle. -/
def bulkPairingMap : Residual →ₗ[Complex] S.BackwardGraph →ₗ[Complex] Complex :=
  LinearMap.mk₂ Complex
    (fun F v => slabPairing S.timeHorizon S.xMin S.xMax F.val (v.val 0))
    (by
      intro F₁ F₂ v
      exact slabPairing_add_left F₁.property F₂.property (v.property.1.1 0) _ _ _)
    (by
      intro c F v
      simpa using slabPairing_smul_left c F.val (v.val 0) S.timeHorizon S.xMin S.xMax)
    (by
      intro F v₁ v₂
      exact slabPairing_add_right F.property (v₁.property.1.1 0) (v₂.property.1.1 0) _ _ _)
    (by
      intro c F v
      simpa using slabPairing_smul_right c F.val (v.val 0) S.timeHorizon S.xMin S.xMax)

/-- The adjoint bulk pairing. -/
def adjointBulkPairingMap :
    S.ForwardGraph →ₗ[Complex] Residual →ₗ[Complex] Complex :=
  LinearMap.mk₂ Complex
    (fun u G => slabPairing S.timeHorizon S.xMin S.xMax (u.val 0) G.val)
    (by
      intro u₁ u₂ G
      exact slabPairing_add_left (u₁.property.1.1 0) (u₂.property.1.1 0) G.property _ _ _)
    (by
      intro c u G
      simpa using slabPairing_smul_left c (u.val 0) G.val S.timeHorizon S.xMin S.xMax)
    (by
      intro u G₁ G₂
      exact slabPairing_add_right (u.property.1.1 0) G₁.property G₂.property _ _ _)
    (by
      intro c u G
      simpa using slabPairing_smul_right c (u.val 0) G.val S.timeHorizon S.xMin S.xMax)

/-- The lateral boundary pairing of equation (4.3). -/
def fullBoundaryPairingMap :
    BoundaryFlux →ₗ[Complex] BoundaryValue →ₗ[Complex] Complex :=
  LinearMap.mk₂ Complex
    (fun phi psi =>
      boundaryPairing S.timeHorizon phi.1.val phi.2.val psi.1.val psi.2.val)
    (by
      intro phi₁ phi₂ psi
      simp only [boundaryPairing, Prod.fst_add, Prod.snd_add, Submodule.coe_add]
      rw [linePairing_add_left phi₁.2.property phi₂.2.property psi.2.property,
        linePairing_add_left phi₁.1.property phi₂.1.property psi.1.property]
      ring)
    (by
      intro c phi psi
      simp only [boundaryPairing, Prod.smul_fst, Prod.smul_snd, Submodule.coe_smul]
      rw [linePairing_smul_left, linePairing_smul_left]
      simp only [smul_eq_mul]
      ring)
    (by
      intro phi psi₁ psi₂
      simp only [boundaryPairing, Prod.fst_add, Prod.snd_add, Submodule.coe_add]
      rw [linePairing_add_right phi.2.property psi₁.2.property psi₂.2.property,
        linePairing_add_right phi.1.property psi₁.1.property psi₂.1.property]
      ring)
    (by
      intro c phi psi
      simp only [boundaryPairing, Prod.smul_fst, Prod.smul_snd, Submodule.coe_smul]
      rw [linePairing_smul_right, linePairing_smul_right]
      simp only [smul_eq_mul]
      ring)

/-- **The concrete directed wave Green model.**  Both analytic fields of the
abstract engine are theorems here: time integration by parts against the
directed Cauchy data, and Green's second identity in the normal variable with
the lateral normal-trace flux. -/
def directedWaveGreenModel :
    LiuWang2025SemilinearWaveDirectedGreenRealization.DirectedWaveGreenModel
      (ForwardGraph := S.ForwardGraph) (BackwardGraph := S.BackwardGraph)
      (ForwardResidual := Residual) (BackwardResidual := Residual)
      (BoundaryFlux := BoundaryFlux) (BoundaryValue := BoundaryValue) where
  forwardTimeSecond := S.forwardTimeSecondMap
  forwardSpatial := S.forwardSpatialMap
  forwardWave := S.forwardTimeSecondMap - S.forwardSpatialMap
  backwardTimeSecond := S.backwardTimeSecondMap
  backwardSpatial := S.backwardSpatialMap
  backwardWave := S.backwardTimeSecondMap - S.backwardSpatialMap
  bulkPairing := S.bulkPairingMap
  adjointBulkPairing := S.adjointBulkPairingMap
  normalTrace := S.normalTraceMap
  probeTrace := S.probeTraceMap
  fullBoundaryPairing := S.fullBoundaryPairingMap
  forwardWave_decomposition := rfl
  backwardWave_decomposition := rfl
  timeIntegrationByParts := by
    intro u v
    exact concrete_timeIntegrationByParts S.timeHorizon_nonneg S.slab_le
      u.property.1 v.property.1 u.property.2.1 u.property.2.2.1
      v.property.2.1 v.property.2.2
  spatialGreenFormula := by
    intro u v
    exact concrete_spatialGreenFormula S.timeHorizon_nonneg S.slab_le
      S.tangentialEigenvalue u.property.1 v.property.1
      u.property.2.2.2.1 u.property.2.2.2.2

/-- **The Lorentzian Green identity on the concrete model.**  For a backward
jet solving the homogeneous separated wave equation, the source pairing is the
lateral boundary pairing. -/
theorem generated_greenIdentity (u : S.ForwardGraph) (v : S.BackwardGraph)
    (hv : (S.backwardTimeSecondMap - S.backwardSpatialMap) v = 0) :
    -(S.bulkPairingMap
        ((S.forwardTimeSecondMap - S.forwardSpatialMap) u) v)
      = S.fullBoundaryPairingMap (S.normalTraceMap u) (S.probeTraceMap v) :=
  S.directedWaveGreenModel.greenIdentity u v hv

/-- The same identity written out in terms of the actual integrals. -/
theorem generated_greenIdentity_explicit (u : S.ForwardGraph)
    (v : S.BackwardGraph)
    (hv : (S.backwardTimeSecondMap - S.backwardSpatialMap) v = 0) :
    -slabPairing S.timeHorizon S.xMin S.xMax
        (fun t x => u.val 2 t x
          - (u.val 4 t x - S.tangentialEigenvalue * u.val 0 t x)) (v.val 0)
      = boundaryPairing S.timeHorizon
          (fun t => u.val 3 t S.xMin) (fun t => u.val 3 t S.xMax)
          (fun t => v.val 0 t S.xMin) (fun t => v.val 0 t S.xMax) :=
  S.generated_greenIdentity u v hv

/-- The generated engine consumed by the source-ordered equation-(4.2)-to-(4.3)
machinery. -/
def waveGreenIdentityEngine :
    LiuWang2025SemilinearWaveThirdOrderGreen.WaveGreenIdentityEngine
      (State := S.ForwardGraph) (Residual := Residual)
      (Probe := S.BackwardGraph) (BoundaryFlux := BoundaryFlux)
      (BoundaryValue := BoundaryValue) :=
  S.directedWaveGreenModel.toWaveGreenIdentityEngine

end SlabGeometry

/-! ## Non-vacuity: explicit nonzero members of both carriers -/

/-- `t |-> t^2`, the forward time factor. -/
def witnessA : Real -> Complex := fun t => ((t ^ 2 : Real) : Complex)
/-- Its derivative. -/
def witnessA' : Real -> Complex := fun t => ((2 * t : Real) : Complex)
/-- Its second derivative. -/
def witnessA'' : Real -> Complex := fun _ => ((2 : Real) : Complex)

/-- `x |-> (x - xMin)(x - xMax)`, vanishing on both faces. -/
def witnessB (xMin xMax : Real) : Real -> Complex :=
  fun x => (((x - xMin) * (x - xMax) : Real) : Complex)
/-- Its derivative. -/
def witnessB' (xMin xMax : Real) : Real -> Complex :=
  fun x => (((x - xMin) + (x - xMax) : Real) : Complex)
/-- Its second derivative. -/
def witnessB'' : Real -> Complex := fun _ => ((2 : Real) : Complex)

theorem hasDerivAt_witnessA (t : Real) : HasDerivAt witnessA (witnessA' t) t := by
  have hid : HasDerivAt (fun s : Real => s) 1 t := hasDerivAt_id t
  have hreal : HasDerivAt (fun s : Real => s ^ 2)
      ((2 : Nat) * t ^ (2 - 1) * 1) t := hid.pow 2
  have h : HasDerivAt (fun s : Real => ((s ^ 2 : Real) : Complex))
      ((((2 : Nat) * t ^ (2 - 1) * 1 : Real)) : Complex) t := hreal.ofReal_comp
  refine h.congr_deriv ?_
  simp only [witnessA']
  push_cast
  ring

theorem hasDerivAt_witnessA' (t : Real) : HasDerivAt witnessA' (witnessA'' t) t := by
  have hid : HasDerivAt (fun s : Real => s) 1 t := hasDerivAt_id t
  have hreal : HasDerivAt (fun s : Real => 2 * s) (2 * 1) t := hid.const_mul 2
  have h : HasDerivAt (fun s : Real => ((2 * s : Real) : Complex))
      (((2 * 1 : Real)) : Complex) t := hreal.ofReal_comp
  refine h.congr_deriv ?_
  simp only [witnessA'']
  push_cast
  ring

theorem hasDerivAt_witnessB (xMin xMax x : Real) :
    HasDerivAt (witnessB xMin xMax) (witnessB' xMin xMax x) x := by
  have hid : HasDerivAt (fun s : Real => s) 1 x := hasDerivAt_id x
  have hreal : HasDerivAt (fun y : Real => (y - xMin) * (y - xMax))
      (1 * (x - xMax) + (x - xMin) * 1) x :=
    (hid.sub_const xMin).mul (hid.sub_const xMax)
  have h : HasDerivAt (fun y : Real => (((y - xMin) * (y - xMax) : Real) : Complex))
      (((1 * (x - xMax) + (x - xMin) * 1 : Real)) : Complex) x := hreal.ofReal_comp
  refine h.congr_deriv ?_
  simp only [witnessB']
  push_cast
  ring

theorem hasDerivAt_witnessB' (xMin xMax x : Real) :
    HasDerivAt (witnessB' xMin xMax) (witnessB'' x) x := by
  have hid : HasDerivAt (fun s : Real => s) 1 x := hasDerivAt_id x
  have hreal : HasDerivAt (fun y : Real => (y - xMin) + (y - xMax)) (1 + 1) x :=
    (hid.sub_const xMin).add (hid.sub_const xMax)
  have h : HasDerivAt (fun y : Real => (((y - xMin) + (y - xMax) : Real) : Complex))
      (((1 + 1 : Real)) : Complex) x := hreal.ofReal_comp
  refine h.congr_deriv ?_
  simp only [witnessB'']
  push_cast
  ring

theorem continuous_witnessA : Continuous witnessA := by
  unfold witnessA; fun_prop
theorem continuous_witnessA' : Continuous witnessA' := by
  unfold witnessA'; fun_prop
theorem continuous_witnessA'' : Continuous witnessA'' := by
  unfold witnessA''; fun_prop
theorem continuous_witnessB (xMin xMax : Real) : Continuous (witnessB xMin xMax) := by
  unfold witnessB; fun_prop
theorem continuous_witnessB' (xMin xMax : Real) : Continuous (witnessB' xMin xMax) := by
  unfold witnessB'; fun_prop
theorem continuous_witnessB'' : Continuous witnessB'' := by
  unfold witnessB''; fun_prop

/-- The explicit forward jet `u(t,x) = t^2 (x - xMin)(x - xMax)`. -/
def forwardWitnessJet (xMin xMax : Real) : Jet :=
  ![fun t x => witnessA t * witnessB xMin xMax x,
    fun t x => witnessA' t * witnessB xMin xMax x,
    fun t x => witnessA'' t * witnessB xMin xMax x,
    fun t x => witnessA t * witnessB' xMin xMax x,
    fun t x => witnessA t * witnessB'' x]

theorem forwardWitnessJet_mem (xMin xMax : Real) :
    forwardWitnessJet xMin xMax ∈ forwardCarrier xMin xMax := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact (continuous_witnessA.comp continuous_fst).mul
        ((continuous_witnessB xMin xMax).comp continuous_snd)
    · exact (continuous_witnessA'.comp continuous_fst).mul
        ((continuous_witnessB xMin xMax).comp continuous_snd)
    · exact (continuous_witnessA''.comp continuous_fst).mul
        ((continuous_witnessB xMin xMax).comp continuous_snd)
    · exact (continuous_witnessA.comp continuous_fst).mul
        ((continuous_witnessB' xMin xMax).comp continuous_snd)
    · exact (continuous_witnessA.comp continuous_fst).mul
        (continuous_witnessB''.comp continuous_snd)
  · intro t x
    exact (hasDerivAt_witnessA t).mul_const _
  · intro t x
    exact (hasDerivAt_witnessA' t).mul_const _
  · intro t x
    exact (hasDerivAt_witnessB xMin xMax x).const_mul _
  · intro t x
    exact (hasDerivAt_witnessB' xMin xMax x).const_mul _
  · intro x
    show witnessA 0 * witnessB xMin xMax x = 0
    simp [witnessA]
  · intro x
    show witnessA' 0 * witnessB xMin xMax x = 0
    simp [witnessA']
  · intro t
    show witnessA t * witnessB xMin xMax xMin = 0
    simp [witnessB]
  · intro t
    show witnessA t * witnessB xMin xMax xMax = 0
    simp [witnessB]

/-- The forward carrier is not the zero module. -/
theorem forwardWitnessJet_ne_zero {xMin xMax : Real} (hlt : xMin < xMax) :
    forwardWitnessJet xMin xMax ≠ 0 := by
  intro hzero
  have h := congrFun (congrFun (congrFun hzero 0) 1) ((xMin + xMax) / 2)
  have hval : witnessA 1 * witnessB xMin xMax ((xMin + xMax) / 2) = 0 := h
  rw [witnessA, witnessB] at hval
  have hreal : ((1 : Real) ^ 2) * (((xMin + xMax) / 2 - xMin)
      * ((xMin + xMax) / 2 - xMax)) = 0 := by
    have : (((1 : Real) ^ 2 * (((xMin + xMax) / 2 - xMin)
        * ((xMin + xMax) / 2 - xMax)) : Real) : Complex) = 0 := by
      push_cast at hval ⊢
      linear_combination hval
    exact_mod_cast this
  nlinarith [hreal, sq_nonneg (xMax - xMin), sub_pos.mpr hlt]

/-- `t |-> (t - T)^2`, the backward time factor. -/
def witnessC (timeHorizon : Real) : Real -> Complex :=
  fun t => (((t - timeHorizon) ^ 2 : Real) : Complex)
/-- Its derivative. -/
def witnessC' (timeHorizon : Real) : Real -> Complex :=
  fun t => ((2 * (t - timeHorizon) : Real) : Complex)
/-- Its second derivative. -/
def witnessC'' : Real -> Complex := fun _ => ((2 : Real) : Complex)

theorem hasDerivAt_witnessC (timeHorizon t : Real) :
    HasDerivAt (witnessC timeHorizon) (witnessC' timeHorizon t) t := by
  have hid : HasDerivAt (fun s : Real => s) 1 t := hasDerivAt_id t
  have hreal : HasDerivAt (fun s : Real => (s - timeHorizon) ^ 2)
      ((2 : Nat) * (t - timeHorizon) ^ (2 - 1) * 1) t :=
    (hid.sub_const timeHorizon).pow 2
  have h : HasDerivAt (fun s : Real => (((s - timeHorizon) ^ 2 : Real) : Complex))
      ((((2 : Nat) * (t - timeHorizon) ^ (2 - 1) * 1 : Real)) : Complex) t :=
    hreal.ofReal_comp
  refine h.congr_deriv ?_
  simp only [witnessC']
  push_cast
  ring

theorem hasDerivAt_witnessC' (timeHorizon t : Real) :
    HasDerivAt (witnessC' timeHorizon) (witnessC'' t) t := by
  have hid : HasDerivAt (fun s : Real => s) 1 t := hasDerivAt_id t
  have hreal : HasDerivAt (fun s : Real => 2 * (s - timeHorizon)) (2 * 1) t :=
    (hid.sub_const timeHorizon).const_mul 2
  have h : HasDerivAt (fun s : Real => ((2 * (s - timeHorizon) : Real) : Complex))
      (((2 * 1 : Real)) : Complex) t := hreal.ofReal_comp
  refine h.congr_deriv ?_
  simp only [witnessC'']
  push_cast
  ring

theorem continuous_witnessC (timeHorizon : Real) :
    Continuous (witnessC timeHorizon) := by unfold witnessC; fun_prop
theorem continuous_witnessC' (timeHorizon : Real) :
    Continuous (witnessC' timeHorizon) := by unfold witnessC'; fun_prop
theorem continuous_witnessC'' : Continuous witnessC'' := by
  unfold witnessC''; fun_prop

/-- The explicit backward jet `v(t,x) = (t - T)^2`. -/
def backwardWitnessJet (timeHorizon : Real) : Jet :=
  ![fun t _ => witnessC timeHorizon t,
    fun t _ => witnessC' timeHorizon t,
    fun t _ => witnessC'' t,
    fun _ _ => (0 : Complex),
    fun _ _ => (0 : Complex)]

theorem backwardWitnessJet_mem (timeHorizon : Real) :
    backwardWitnessJet timeHorizon ∈ backwardCarrier timeHorizon := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact (continuous_witnessC timeHorizon).comp continuous_fst
    · exact (continuous_witnessC' timeHorizon).comp continuous_fst
    · exact continuous_witnessC''.comp continuous_fst
    · exact continuous_const
    · exact continuous_const
  · intro t x
    exact hasDerivAt_witnessC timeHorizon t
  · intro t x
    exact hasDerivAt_witnessC' timeHorizon t
  · intro t x
    exact hasDerivAt_const x _
  · intro t x
    exact hasDerivAt_const x _
  · intro x
    show witnessC timeHorizon timeHorizon = 0
    simp [witnessC]
  · intro x
    show witnessC' timeHorizon timeHorizon = 0
    simp [witnessC']

/-- The backward carrier is not the zero module. -/
theorem backwardWitnessJet_ne_zero {timeHorizon : Real} (hT : timeHorizon ≠ 0) :
    backwardWitnessJet timeHorizon ≠ 0 := by
  intro hzero
  have h := congrFun (congrFun (congrFun hzero 0) 0) 0
  have hval : witnessC timeHorizon 0 = 0 := h
  rw [witnessC] at hval
  have hreal : ((0 : Real) - timeHorizon) ^ 2 = 0 := by exact_mod_cast hval
  have hzeroT : timeHorizon = 0 := by nlinarith [hreal]
  exact hT hzeroT

end LiuWang2025SemilinearWaveConcreteDirectedGreen



