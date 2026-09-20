import LiuWang.LiuWang2025SemilinearWaveFourNullCovectors
import Mathlib.Analysis.Calculus.FDeriv.Star
import Mathlib.Analysis.Complex.RealDeriv

/-!
# Liu--Wang 2025: the four-beam summed-phase lemma

Source: Boya Liu and Weinan Wang, *On a partial data inverse problem for the
semi-linear wave equation*, arXiv:2511.08794v1, Section on the determination
of `V_3`.

The source quotes the following lemma of Feizmohammadi--Oksanen.  For formal
Gaussian beams along the four geodesics `gamma^(k)`, `k = 0,1,2,3`, meeting at
the interaction point `p`, the function

`S = kappa_0 phi^(0) + kappa_1 phi^(1) + kappa_2 conj(phi^(2))
      + kappa_3 conj(phi^(3))`

is well defined near `p` and satisfies

* (i)   `S(p) = 0`;
* (ii)  `grad S(p) = 0`;
* (iii) `Im S(q) >= m d(q, p)^2` near `p`, for some `m > 0`.

This module proves all three from the data actually available in the dossier:

* each beam phase vanishes at the interaction point and has, at that point,
  a *real* differential -- the null covector `xi^(j)` of
  `LiuWang2025SemilinearWaveFourNullCovectors`;
* the weighted covector balance `sum_j kappa_j xi^(j) = 0`, which that module
  already proves for the explicit Lorentz frame;
* the quadratic lower bound `Im phi^(j)(q) >= m_j d(q,p)^2`, which is the
  transported positivity of `Im M` supplied by the Riccati modules.

The signs are the paper's: the two conjugated beams carry negative weights, so
that all four contributions to `Im S` are nonnegative.  Lean produces the
explicit coercivity constant `m = sum_j |kappa_j| m_j` and proves it positive.

## Scope

The geometric construction of the four broken null geodesics through a
reachable interaction point, and the identification of the beam phases with
the ones produced by the Riccati/transport hierarchy, remain source-facing
geometric inputs; they are the data of `FourBeamPhaseConfiguration`.  The
lemma itself is proved.
-/

noncomputable section

open scoped BigOperators
open Complex

namespace LiuWang2025SemilinearWaveFourBeamPhaseLemma

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]

/-- The four Gaussian-beam phases at a common interaction point, with the
paper's weights and conjugations. -/
structure FourBeamPhaseConfiguration (E : Type*) [NormedAddCommGroup E]
    [NormedSpace Real E] where
  center : E
  radius : Real
  radius_pos : 0 < radius
  phase : Fin 4 -> E -> Complex
  covector : Fin 4 -> (E →L[Real] Real)
  weight : Fin 4 -> Real
  coercivity : Fin 4 -> Real
  conjugated : Fin 4 -> Bool
  /-- The beams meet at the interaction point. -/
  phase_center : ∀ j, phase j center = 0
  /-- At the interaction point the differential of the phase is the real null
  covector `xi^(j)`. -/
  hasFDeriv : ∀ j,
    HasFDerivAt (phase j) (Complex.ofRealCLM.comp (covector j)) center
  coercivity_pos : ∀ j, 0 < coercivity j
  /-- Transported positivity of `Im M`. -/
  imaginary_lower : ∀ j, ∀ q ∈ Metric.ball center radius,
    coercivity j * dist q center ^ 2 <= (phase j q).im
  /-- The conjugated beams carry negative weights, the others positive. -/
  weight_neg : ∀ j, conjugated j = true -> weight j < 0
  weight_pos : ∀ j, conjugated j = false -> 0 < weight j
  /-- The source's weighted null-covector balance. -/
  balance : ∑ j, weight j • covector j = 0

namespace FourBeamPhaseConfiguration

variable (C : FourBeamPhaseConfiguration E)

/-- One weighted, possibly conjugated, beam phase. -/
def beamTerm (j : Fin 4) (q : E) : Complex :=
  C.weight j •
    (if C.conjugated j then (starRingEnd Complex) (C.phase j q) else C.phase j q)

/-- The source's summed phase `S`. -/
def summedPhase (q : E) : Complex := ∑ j, C.beamTerm j q

/-- The generated coercivity constant `m = sum_j |kappa_j| m_j`. -/
def totalCoercivity : Real := ∑ j, |C.weight j| * C.coercivity j

theorem weight_ne_zero (j : Fin 4) : C.weight j ≠ 0 := by
  cases h : C.conjugated j
  · exact ne_of_gt (C.weight_pos j h)
  · exact ne_of_lt (C.weight_neg j h)

theorem totalCoercivity_pos : 0 < C.totalCoercivity := by
  refine Finset.sum_pos (fun j _ => ?_) ⟨0, Finset.mem_univ 0⟩
  exact mul_pos (abs_pos.mpr (C.weight_ne_zero j)) (C.coercivity_pos j)

/-- **(i)** The summed phase vanishes at the interaction point. -/
@[simp] theorem summedPhase_center : C.summedPhase C.center = 0 := by
  refine Finset.sum_eq_zero fun j _ => ?_
  simp [beamTerm, C.phase_center j]

/-- The imaginary part of a weighted term is `|kappa_j| Im phi^(j)`. -/
theorem beamTerm_im (j : Fin 4) (q : E) :
    (C.beamTerm j q).im = |C.weight j| * (C.phase j q).im := by
  cases h : C.conjugated j
  · have hw : 0 < C.weight j := C.weight_pos j h
    simp [beamTerm, h, abs_of_pos hw]
  · have hw : C.weight j < 0 := C.weight_neg j h
    simp [beamTerm, h, abs_of_neg hw]

/-- **(iii)** The imaginary part of the summed phase is coercive, with the
explicit constant `sum_j |kappa_j| m_j > 0`. -/
theorem summedPhase_im_lower {q : E} (hq : q ∈ Metric.ball C.center C.radius) :
    C.totalCoercivity * dist q C.center ^ 2 <= (C.summedPhase q).im := by
  have hsum : (C.summedPhase q).im = ∑ j, (C.beamTerm j q).im := by
    simp [summedPhase, Complex.im_sum]
  rw [hsum, totalCoercivity, Finset.sum_mul]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [C.beamTerm_im j q, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg (C.weight j))
  exact C.imaginary_lower j q hq

/-- Each conjugated beam term is differentiable at the interaction point with
the same real covector. -/
theorem hasFDerivAt_beamTerm (j : Fin 4) :
    HasFDerivAt (C.beamTerm j)
      (C.weight j • (Complex.ofRealCLM.comp (C.covector j))) C.center := by
  cases h : C.conjugated j
  · have hfun : C.beamTerm j = fun q => C.weight j • C.phase j q := by
      funext q
      simp [beamTerm, h]
    rw [hfun]
    exact (C.hasFDeriv j).const_smul (C.weight j)
  · have hfun : C.beamTerm j
        = fun q => C.weight j • (starRingEnd Complex) (C.phase j q) := by
      funext q
      simp [beamTerm, h]
    rw [hfun]
    have hstar := (C.hasFDeriv j).star
    have hcomp : (starL' (R := Real) (A := Complex)).toContinuousLinearMap.comp
        (Complex.ofRealCLM.comp (C.covector j))
          = Complex.ofRealCLM.comp (C.covector j) := by
      ext v
      simp
    have hstar' : HasFDerivAt (fun q => (starRingEnd Complex) (C.phase j q))
        (Complex.ofRealCLM.comp (C.covector j)) C.center := by
      simpa [hcomp] using hstar
    exact hstar'.const_smul (C.weight j)

/-- **(ii)** The differential of the summed phase vanishes at the interaction
point: this is exactly the weighted null-covector balance. -/
theorem hasFDerivAt_summedPhase :
    HasFDerivAt C.summedPhase (0 : E →L[Real] Complex) C.center := by
  have hsum : HasFDerivAt (fun q => ∑ j, C.beamTerm j q)
      (∑ j : Fin 4, C.weight j • (Complex.ofRealCLM.comp (C.covector j))) C.center :=
    HasFDerivAt.fun_sum fun j _ => C.hasFDerivAt_beamTerm j
  have hstep : ∀ j : Fin 4,
      C.weight j • (Complex.ofRealCLM.comp (C.covector j))
        = Complex.ofRealCLM.comp (C.weight j • C.covector j) := by
    intro j
    ext v
    simp
  have hcomp : (∑ j : Fin 4, Complex.ofRealCLM.comp (C.weight j • C.covector j))
      = Complex.ofRealCLM.comp (∑ j : Fin 4, C.weight j • C.covector j) := by
    ext v
    simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply,
      ContinuousLinearMap.coe_comp', Function.comp_apply, Complex.ofRealCLM_apply,
      ContinuousLinearMap.coe_smul', Pi.smul_apply, Complex.ofReal_sum]
  have hzero : (∑ j, C.weight j • (Complex.ofRealCLM.comp (C.covector j)))
      = (0 : E →L[Real] Complex) := by
    simp only [hstep]
    rw [hcomp, C.balance]
    ext v
    simp
  simpa [hzero] using hsum

/-- One reviewable object carrying the paper's lemma. -/
structure Certificate (data : FourBeamPhaseConfiguration E) : Prop where
  vanishesAtInteractionPoint : data.summedPhase data.center = 0
  differentialVanishes :
    HasFDerivAt data.summedPhase (0 : E →L[Real] Complex) data.center
  coercivityConstantPositive : 0 < data.totalCoercivity
  imaginaryPartCoercive : ∀ q ∈ Metric.ball data.center data.radius,
    data.totalCoercivity * dist q data.center ^ 2 <= (data.summedPhase q).im

/-- The lemma is generated from the beam data. -/
def certificate (data : FourBeamPhaseConfiguration E) : Certificate data where
  vanishesAtInteractionPoint := data.summedPhase_center
  differentialVanishes := data.hasFDerivAt_summedPhase
  coercivityConstantPositive := data.totalCoercivity_pos
  imaginaryPartCoercive := fun _ hq => data.summedPhase_im_lower hq

end FourBeamPhaseConfiguration

/-! ## Construction from the explicit Lorentz-frame covector balance -/

open LiuWang2025SemilinearWaveFourNullCovectors

/-- The paper's conjugation pattern: the last two beams enter conjugated. -/
def sourceConjugation : Fin 4 -> Bool := ![false, false, true, true]

/-- The configuration built from the explicit four future null covectors of
`LiuWang2025SemilinearWaveFourNullCovectors`.  The weighted balance is not a
hypothesis here: it is the theorem `weighted_covector_sum_eq_zero`. -/
def ofLorentzFrame (frame : LorentzOrthonormalTwoFrame E)
    (center : E) (radius : Real) (radius_pos : 0 < radius)
    (phase : Fin 4 -> E -> Complex) (coercivity : Fin 4 -> Real)
    (phase_center : ∀ j, phase j center = 0)
    (hasFDeriv : ∀ j,
      HasFDerivAt (phase j) (Complex.ofRealCLM.comp (frame.covector j)) center)
    (coercivity_pos : ∀ j, 0 < coercivity j)
    (imaginary_lower : ∀ j, ∀ q ∈ Metric.ball center radius,
      coercivity j * dist q center ^ 2 <= (phase j q).im) :
    FourBeamPhaseConfiguration E where
  center := center
  radius := radius
  radius_pos := radius_pos
  phase := phase
  covector := frame.covector
  weight := frame.weight
  coercivity := coercivity
  conjugated := sourceConjugation
  phase_center := phase_center
  hasFDeriv := hasFDeriv
  coercivity_pos := coercivity_pos
  imaginary_lower := imaginary_lower
  weight_neg := by
    intro j hj
    fin_cases j <;> revert hj <;>
      norm_num [sourceConjugation, LorentzOrthonormalTwoFrame.weight]
  weight_pos := by
    intro j hj
    fin_cases j <;> revert hj <;>
      norm_num [sourceConjugation, LorentzOrthonormalTwoFrame.weight]
  balance := frame.weighted_covector_sum_eq_zero

@[simp] theorem ofLorentzFrame_weight (frame : LorentzOrthonormalTwoFrame E)
    (center : E) (radius : Real) (radius_pos : 0 < radius)
    (phase : Fin 4 -> E -> Complex) (coercivity : Fin 4 -> Real)
    (phase_center : ∀ j, phase j center = 0)
    (hasFDeriv : ∀ j,
      HasFDerivAt (phase j) (Complex.ofRealCLM.comp (frame.covector j)) center)
    (coercivity_pos : ∀ j, 0 < coercivity j)
    (imaginary_lower : ∀ j, ∀ q ∈ Metric.ball center radius,
      coercivity j * dist q center ^ 2 <= (phase j q).im) :
    (ofLorentzFrame frame center radius radius_pos phase coercivity phase_center
      hasFDeriv coercivity_pos imaginary_lower).weight = frame.weight := rfl

/-- The paper's lemma for the configuration generated by the explicit Lorentz
frame. -/
def lorentzFrameCertificate (frame : LorentzOrthonormalTwoFrame E)
    (center : E) (radius : Real) (radius_pos : 0 < radius)
    (phase : Fin 4 -> E -> Complex) (coercivity : Fin 4 -> Real)
    (phase_center : ∀ j, phase j center = 0)
    (hasFDeriv : ∀ j,
      HasFDerivAt (phase j) (Complex.ofRealCLM.comp (frame.covector j)) center)
    (coercivity_pos : ∀ j, 0 < coercivity j)
    (imaginary_lower : ∀ j, ∀ q ∈ Metric.ball center radius,
      coercivity j * dist q center ^ 2 <= (phase j q).im) :
    FourBeamPhaseConfiguration.Certificate
      (ofLorentzFrame frame center radius radius_pos phase coercivity
        phase_center hasFDeriv coercivity_pos imaginary_lower) :=
  FourBeamPhaseConfiguration.certificate _

/-! ## The source's higher-order beam configuration

Subsection 4.3 recovers `V_m` for `m >= 4` by replacing the fourth beam of the
cubic configuration with `m - 2` beams that share its weight equally: their
phases carry `kappa_3 / (m - 2)` in place of `kappa_3`.  The covector balance
`sum_j kappa_j theta_j = 0`, which is what makes the summed phase stationary at
the interaction point, is unchanged by that replacement.  The corresponding
statements for the phases and for the replicated amplitude product
`a^0 a^1 a^2 (a^3)^{m-2}` are already proved in
`LiuWang2025SemilinearWaveHigherOrderPolarization`; what is added here is the
same cancellation at the level of the explicit Lorentz-frame covectors.
-/

/-- **Splitting one beam weight into `p` equal parts leaves the weighted
covector unchanged.**  This is the covector-valued companion of
`LiuWang2025SemilinearWaveHigherOrderPolarization.sum_replicatedFourthWeight_smul`,
which records the same cancellation for the complex-valued phases; the
replicated amplitude product is likewise already available there as
`replicatedAmplitudeProduct_eq_pow`. -/
theorem sum_split_weight {p : Nat} (hp : 0 < p) (kappa : Real)
    (theta : E →L[Real] Real) :
    (∑ _j : Fin p, (kappa / (p : Real)) • theta) = kappa • theta := by
  have hpR : (p : Real) ≠ 0 := Nat.cast_ne_zero.2 hp.ne'
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    ← Nat.cast_smul_eq_nsmul Real, smul_smul]
  congr 1
  field_simp

/-- **The source's higher-order configuration still balances.**  Three beams
carry the original weights and `m - 2` beams share the fourth weight equally;
the weighted covector sum still vanishes, so the summed phase of the
higher-order configuration is stationary exactly as in the cubic case. -/
theorem higherOrder_weighted_sum_eq_zero (frame : LorentzOrthonormalTwoFrame E)
    {m : Nat} (hm : 3 ≤ m) :
    frame.weight 0 • frame.covector 0 + frame.weight 1 • frame.covector 1
        + frame.weight 2 • frame.covector 2
        + (∑ _j : Fin (m - 2),
            (frame.weight 3 / ((m - 2 : Nat) : Real)) • frame.covector 3)
      = 0 := by
  have hp : 0 < m - 2 := by omega
  rw [sum_split_weight hp]
  have hbal := frame.weighted_covector_sum_eq_zero
  rw [Fin.sum_univ_four] at hbal
  exact hbal

/-- Each split weight is still nonzero, so no beam degenerates. -/
theorem higherOrder_split_weight_ne_zero
    (frame : LorentzOrthonormalTwoFrame E) {m : Nat} (hm : 3 ≤ m) :
    frame.weight 3 / ((m - 2 : Nat) : Real) ≠ 0 := by
  have hp : 0 < m - 2 := by omega
  have hpR : ((m - 2 : Nat) : Real) ≠ 0 := Nat.cast_ne_zero.2 hp.ne'
  exact div_ne_zero (frame.weight_ne_zero 3) hpR

end LiuWang2025SemilinearWaveFourBeamPhaseLemma
