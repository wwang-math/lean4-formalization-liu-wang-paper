/-
Copyright (c) 2026.  Released under Apache 2.0.

# Local coordinates: the chart Jacobian is absorbed into the amplitude

In Liu–Wang the oscillatory integral is taken against the Lorentzian volume element
`dV_g dt` of the manifold `(0,T) × M`, **not** against a Haar measure.  In a local chart
around the interaction point `p̃` one has

  `dV_g dt = J(x) dx`,   `J = |g|^{1/2} > 0` smooth,

and `dx` is (the coordinate expression of) a Haar measure.  All the stationary-phase theory in
`LiuWangComplexStationaryPhase` is stated for an **additive Haar measure**, so it may not be
applied to `dV_g dt` directly.

This file supplies the missing step, and only that step:

* `ChartDensity` packages the hypotheses on `J` (positivity, boundedness, Lipschitz
  regularity, continuity) that are needed;
* `ChartDensity.measure μ` is the chart measure `J · μ`, which is *not* assumed to be Haar;
* `integral_chartMeasure` is the change-of-density formula;
* `AmplitudeFamily.mulDensity` shows that `aρ · J` is again an admissible amplitude family —
  this is the sense in which "the Jacobian is absorbed into the amplitude";
* `oscIntegral_chartMeasure` is the resulting **adapter**, and
  `chartOscIntegral_tendsto` is the leading asymptotic in the chart, whose leading constant
  carries the factor `J(p)`.

Nothing here assumes that `J · μ` is translation invariant, and no theorem of this packet
identifies a manifold volume measure with a Haar measure.
-/
import LiuWang.LiuWang2025SemilinearWaveComplexStationaryPhase
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

noncomputable section

open MeasureTheory Complex Filter Set
open scoped Real Topology ENNReal NNReal

namespace LiuWang2025SemilinearWaveComplexStationaryPhase

/-! ## 1.  Chart densities -/

/-- The **density of a local-coordinate volume element** with respect to a Haar measure.

In the application `J = |det g|^{1/2}` read in the chart; the hypotheses are exactly those
needed to keep the amplitude hypotheses of `AmplitudeFamily` stable under multiplication
by `J`.  Note that no invariance of any kind is assumed of `J`. -/
structure ChartDensity (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] where
  /-- The density. -/
  J : V → ℝ
  /-- Uniform upper bound for `J`. -/
  B : ℝ
  /-- Lipschitz constant of `J`. -/
  Lip : ℝ
  hB : 0 ≤ B
  hLip : 0 ≤ Lip
  /-- A volume density is non-negative. -/
  nonneg : ∀ x, 0 ≤ J x
  cont : Continuous J
  bound : ∀ x, J x ≤ B
  lip : ∀ x y, |J x - J y| ≤ Lip * ‖x - y‖

namespace ChartDensity

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The `ℝ≥0`-valued density. -/
def density (Jd : ChartDensity V) : V → ℝ≥0 := fun x => (Jd.J x).toNNReal

lemma coe_density (Jd : ChartDensity V) (x : V) : ((Jd.density x : ℝ≥0) : ℝ) = Jd.J x :=
  Real.coe_toNNReal _ (Jd.nonneg x)

lemma measurable_density [MeasurableSpace V] [OpensMeasurableSpace V] (Jd : ChartDensity V) :
    Measurable Jd.density :=
  (Jd.cont.measurable).real_toNNReal

/-- The **chart measure** `dV_g = J · dμ`.

This is in general *not* an additive Haar measure — it is translation invariant only when `J`
is constant — which is precisely why the adapter of §3 is needed. -/
def measure [MeasurableSpace V] (Jd : ChartDensity V) (μ : Measure V) : Measure V :=
  μ.withDensity (fun x => (Jd.density x : ℝ≥0∞))

variable [MeasurableSpace V] [OpensMeasurableSpace V]

/-- **Change of density.**  Integration against the chart measure is integration against the
Haar measure with the integrand multiplied by `J`. -/
theorem integral_chartMeasure (Jd : ChartDensity V) (μ : Measure V) (g : V → ℂ) :
    ∫ x, g x ∂(Jd.measure μ) = ∫ x, (Jd.J x) • g x ∂μ := by
  rw [measure, integral_withDensity_eq_integral_smul Jd.measurable_density]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [NNReal.smul_def, Jd.coe_density]
  rfl

/-- **Change of density, integrability form.** -/
theorem integrable_chartMeasure_iff (Jd : ChartDensity V) (μ : Measure V) (g : V → ℂ) :
    Integrable g (Jd.measure μ) ↔ Integrable (fun x => (Jd.J x) • g x) μ := by
  rw [measure, integrable_withDensity_iff_integrable_smul Jd.measurable_density]
  refine integrable_congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [NNReal.smul_def, Jd.coe_density]
  rfl

end ChartDensity

/-! ## 2.  Absorbing the Jacobian into the amplitude -/

namespace AmplitudeFamily

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {p : V} {r : ℝ}

/-- **The chart Jacobian is absorbed into the amplitude.**

If `aρ` is an admissible amplitude family and `J` an admissible chart density, then
`x ↦ J x · aρ x` is again an admissible amplitude family, with

* domination constant `B · A`,
* Lipschitz constant `B · L + Lip · A`,
* leading value `J p · lead`.

This is the content of the local-coordinate reduction: it is a statement about the
*hypotheses*, and it is what makes the adapter of §3 legitimate. -/
def mulDensity (F : AmplitudeFamily V p r) (Jd : ChartDensity V) : AmplitudeFamily V p r where
  a := fun ρ x => (Jd.J x : ℂ) * F.a ρ x
  A := Jd.B * F.A
  L := Jd.B * F.L + Jd.Lip * F.A
  lead := (Jd.J p : ℂ) * F.lead
  hA := mul_nonneg Jd.hB F.hA
  hL := by
    have h1 : (0 : ℝ) ≤ Jd.B * F.L := mul_nonneg Jd.hB F.hL
    have h2 : (0 : ℝ) ≤ Jd.Lip * F.A := mul_nonneg Jd.hLip F.hA
    linarith
  cont := fun ρ => (Complex.continuous_ofReal.comp Jd.cont).mul (F.cont ρ)
  bound := by
    intro ρ x
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Jd.nonneg x)]
    exact mul_le_mul (Jd.bound x) (F.bound ρ x) (norm_nonneg _) Jd.hB
  lip := by
    intro ρ x y
    have hsplit : (Jd.J x : ℂ) * F.a ρ x - (Jd.J y : ℂ) * F.a ρ y
        = (Jd.J x : ℂ) * (F.a ρ x - F.a ρ y)
          + ((Jd.J x : ℂ) - (Jd.J y : ℂ)) * F.a ρ y := by ring
    rw [hsplit]
    refine le_trans (norm_add_le _ _) ?_
    have h1 : ‖(Jd.J x : ℂ) * (F.a ρ x - F.a ρ y)‖ ≤ (Jd.B * F.L) * ‖x - y‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Jd.nonneg x)]
      calc Jd.J x * ‖F.a ρ x - F.a ρ y‖
          ≤ Jd.B * (F.L * ‖x - y‖) :=
            mul_le_mul (Jd.bound x) (F.lip ρ x y) (norm_nonneg _) Jd.hB
        _ = (Jd.B * F.L) * ‖x - y‖ := by ring
    have h2 : ‖((Jd.J x : ℂ) - (Jd.J y : ℂ)) * F.a ρ y‖ ≤ (Jd.Lip * F.A) * ‖x - y‖ := by
      rw [norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      calc |Jd.J x - Jd.J y| * ‖F.a ρ y‖
          ≤ (Jd.Lip * ‖x - y‖) * F.A :=
            mul_le_mul (Jd.lip x y) (F.bound ρ y) (norm_nonneg _)
              (mul_nonneg Jd.hLip (norm_nonneg _))
        _ = (Jd.Lip * F.A) * ‖x - y‖ := by ring
    have h3 : (Jd.B * F.L) * ‖x - y‖ + (Jd.Lip * F.A) * ‖x - y‖
        = (Jd.B * F.L + Jd.Lip * F.A) * ‖x - y‖ := by ring
    linarith
  supp := by
    intro ρ h hh
    rw [F.supp ρ h hh, mul_zero]
  tendsto_lead := F.tendsto_lead.const_mul _

@[simp] lemma mulDensity_a (F : AmplitudeFamily V p r) (Jd : ChartDensity V) (ρ : ℝ) (x : V) :
    (F.mulDensity Jd).a ρ x = (Jd.J x : ℂ) * F.a ρ x := rfl

@[simp] lemma mulDensity_lead (F : AmplitudeFamily V p r) (Jd : ChartDensity V) :
    (F.mulDensity Jd).lead = (Jd.J p : ℂ) * F.lead := rfl

end AmplitudeFamily

/-! ## 3.  The adapter -/

section Adapter

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] (μ : Measure V) (P : PhaseData V)
  (F : AmplitudeFamily V P.p P.r) (Jd : ChartDensity V)

omit [FiniteDimensional ℝ V] [BorelSpace V] in
lemma oscIntegrand_mulDensity (ρ : ℝ) (x : V) :
    (Jd.J x) • oscIntegrand P F ρ x = oscIntegrand P (F.mulDensity Jd) ρ x := by
  rw [oscIntegrand, oscIntegrand, AmplitudeFamily.mulDensity_a]
  rw [show (Jd.J x) • (Complex.exp (Complex.I * ρ * P.S x) * F.a ρ x)
      = ((Jd.J x : ℝ) : ℂ) * (Complex.exp (Complex.I * ρ * P.S x) * F.a ρ x) from
    Complex.real_smul]
  ring

omit [FiniteDimensional ℝ V] in
/-- **The local-coordinate adapter.**

The normalized oscillatory integral taken against the *chart measure* `J · μ` equals the one
taken against the *Haar measure* `μ` with the Jacobian absorbed into the amplitude.

This is the only bridge between a manifold volume element and a Haar measure used anywhere in
this packet. -/
theorem oscIntegral_chartMeasure (ρ : ℝ) :
    oscIntegral (Jd.measure μ) P F ρ = oscIntegral μ P (F.mulDensity Jd) ρ := by
  rw [oscIntegral, oscIntegral, Jd.integral_chartMeasure μ]
  congr 1
  exact integral_congr_ae (Filter.Eventually.of_forall
    fun x => oscIntegrand_mulDensity P F Jd ρ x)

/-- Integrability against the chart measure, proved rather than assumed. -/
theorem integrable_oscIntegrand_chartMeasure [μ.IsAddHaarMeasure] {ρ : ℝ} (hρ : 0 < ρ) :
    Integrable (oscIntegrand P F ρ) (Jd.measure μ) := by
  rw [Jd.integrable_chartMeasure_iff μ]
  refine (integrable_oscIntegrand μ P (F.mulDensity Jd) hρ).congr
    (Filter.Eventually.of_forall fun x => ?_)
  exact (oscIntegrand_mulDensity P F Jd ρ x).symm

/-- **The leading complex-Gaussian asymptotic in a local chart.**

The limit picks up the value of the chart Jacobian at the stationary point.  The measure on
the left is the chart measure `J · μ`, which is *not* a Haar measure; the Gaussian constant on
the right is computed against the Haar measure `μ`. -/
theorem chartOscIntegral_tendsto [μ.IsAddHaarMeasure] :
    Tendsto (fun ρ : ℝ => oscIntegral (Jd.measure μ) P F ρ) atTop
      (𝓝 (((Jd.J P.p : ℂ) * F.lead) * gaussConst μ P.H)) := by
  have h : (fun ρ : ℝ => oscIntegral (Jd.measure μ) P F ρ)
      = fun ρ : ℝ => oscIntegral μ P (F.mulDensity Jd) ρ := by
    funext ρ
    exact oscIntegral_chartMeasure μ P F Jd ρ
  rw [h]
  have := oscIntegral_tendsto μ P (F.mulDensity Jd)
  rwa [AmplitudeFamily.mulDensity_lead] at this

/-- **Coefficient recovery in a local chart.**

If the chart oscillatory integral tends to `0` and the Jacobian is non-zero at the stationary
point, then the limiting leading amplitude vanishes.  This is the form in which the
`(4.4) ⇒ V₃(p̃) = 0` inference is used on a manifold. -/
theorem chart_lead_eq_zero_of_tendsto_zero [μ.IsAddHaarMeasure] (hJ : Jd.J P.p ≠ 0)
    (h0 : Tendsto (fun ρ : ℝ => oscIntegral (Jd.measure μ) P F ρ) atTop (𝓝 0)) :
    F.lead = 0 := by
  have h : (fun ρ : ℝ => oscIntegral (Jd.measure μ) P F ρ)
      = fun ρ : ℝ => oscIntegral μ P (F.mulDensity Jd) ρ := by
    funext ρ
    exact oscIntegral_chartMeasure μ P F Jd ρ
  rw [h] at h0
  have h1 := lead_eq_zero_of_tendsto_zero μ P (F.mulDensity Jd) h0
  rw [AmplitudeFamily.mulDensity_lead] at h1
  rcases mul_eq_zero.1 h1 with h2 | h2
  · exact absurd (Complex.ofReal_eq_zero.1 h2) hJ
  · exact h2

end Adapter

end LiuWang2025SemilinearWaveComplexStationaryPhase
