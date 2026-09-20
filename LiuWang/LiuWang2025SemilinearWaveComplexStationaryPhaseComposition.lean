/-
Copyright (c) 2026.  Released under Apache 2.0.

# Composition with the Gaussian-beam remainder

Liu–Wang's quantity

  `𝓘 = ρ^((n+1)/2) ∫₀ᵀ ∫_M V₃ e^{iρS} a⁽⁰⁾a⁽¹⁾a⁽²⁾a⁽³⁾ dV_g dt + 𝒪(ρ⁻²)`

is the normalized oscillatory integral **plus** a remainder.  That remainder is produced by the
Gaussian-beam construction of their Section 3 (the estimate (3.12) for the terms `r_{ρ,j}` and
the expansion of the beam amplitudes), and it is *not* an object of complex stationary phase.

This packet does **not** prove any bound on that remainder.  Instead this file supplies
**conditional composition theorems**: they accept the beam remainder — with whatever rate the
Gaussian-beam analysis supplies, `𝒪(ρ⁻²)` in the paper — as an *input hypothesis*, and compose
it with the stationary-phase results of `LiuWangComplexStationaryPhase`.

The last theorem, `composed_isBigO_of_stationaryPhase_bigO`, isolates precisely the *one*
further input that would be needed to obtain equation (4.4) with its stated `𝒪(ρ⁻²)` error,
namely an `𝒪(ρ⁻²)` bound on the stationary-phase remainder itself.  That bound requires the
exact amplitude expansion and jet cancellations, which are not proved here; see the README.
-/
import LiuWang.LiuWang2025SemilinearWaveComplexStationaryPhaseCoordinates

noncomputable section

open MeasureTheory Complex Filter Set Asymptotics
open scoped Real Topology

namespace LiuWang2025SemilinearWaveComplexStationaryPhase

/-! ## 1.  The `ρ⁻²` scale -/

/-- The scale `ρ ↦ ρ⁻²` at which the Gaussian-beam product remainder of Liu–Wang (4.4) is
claimed to vanish. -/
def beamScale (ρ : ℝ) : ℝ := (ρ ^ 2)⁻¹

theorem tendsto_beamScale : Tendsto beamScale atTop (𝓝 0) :=
  Filter.Tendsto.inv_tendsto_atTop (tendsto_pow_atTop two_ne_zero)

/-- The beam scale `ρ⁻²` is subordinate to the stationary-phase scale `ρ^(-1/2)`. -/
theorem beamScale_isBigO_invSqrt :
    beamScale =O[atTop] fun ρ : ℝ => (Real.sqrt ρ)⁻¹ := by
  refine Asymptotics.IsBigO.of_bound 1 ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with ρ hρ
  have hρ0 : (0 : ℝ) < ρ := lt_of_lt_of_le zero_lt_one hρ
  have hs : (0 : ℝ) < Real.sqrt ρ := Real.sqrt_pos.2 hρ0
  have hle : Real.sqrt ρ ≤ ρ ^ 2 := by
    have h4 : ρ ≤ (ρ ^ 2) ^ 2 := by
      have hfac : (ρ ^ 2) ^ 2 - ρ = ρ * ((ρ - 1) * (ρ ^ 2 + ρ + 1)) := by ring
      have hnn : (0 : ℝ) ≤ ρ * ((ρ - 1) * (ρ ^ 2 + ρ + 1)) := by
        refine mul_nonneg hρ0.le (mul_nonneg (by linarith) ?_)
        nlinarith [sq_nonneg ρ]
      linarith [hfac, hnn]
    have h5 : Real.sqrt ρ ≤ Real.sqrt ((ρ ^ 2) ^ 2) := Real.sqrt_le_sqrt h4
    rwa [Real.sqrt_sq (by positivity)] at h5
  have hmain : (ρ ^ 2)⁻¹ ≤ (Real.sqrt ρ)⁻¹ := by gcongr
  rw [beamScale, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (by positivity : (0:ℝ) < (ρ ^ 2)⁻¹),
    abs_of_pos (by positivity : (0:ℝ) < (Real.sqrt ρ)⁻¹), one_mul]
  exact hmain

end LiuWang2025SemilinearWaveComplexStationaryPhase

namespace LiuWang2025SemilinearWaveComplexStationaryPhase

/-! ## 2.  Conditional composition -/

section Compose

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure]
  (P : PhaseData V) (F : AmplitudeFamily V P.p P.r) (I R : ℝ → ℂ)

/-- **Conditional composition, convergence form.**

If the measured quantity `I` differs from the normalized oscillatory integral by a remainder
`R` that tends to `0`, then `I` has the same complex-Gaussian limit.  The hypothesis on `R` is
an *input*: it is what the Gaussian-beam analysis has to supply. -/
theorem composed_tendsto
    (hdecomp : ∀ ρ : ℝ, I ρ = oscIntegral μ P F ρ + R ρ)
    (hR : Tendsto R atTop (𝓝 0)) :
    Tendsto I atTop (𝓝 (F.lead * gaussConst μ P.H)) := by
  have h : Tendsto (fun ρ : ℝ => oscIntegral μ P F ρ + R ρ) atTop
      (𝓝 (F.lead * gaussConst μ P.H + 0)) := (oscIntegral_tendsto μ P F).add hR
  rw [add_zero] at h
  exact h.congr fun ρ => (hdecomp ρ).symm

/-- **Conditional composition with the `𝒪(ρ⁻²)` beam remainder of (4.4).** -/
theorem composed_tendsto_of_beam_bigO
    (hdecomp : ∀ ρ : ℝ, I ρ = oscIntegral μ P F ρ + R ρ)
    (hR : R =O[atTop] beamScale) :
    Tendsto I atTop (𝓝 (F.lead * gaussConst μ P.H)) :=
  composed_tendsto μ P F I R hdecomp (hR.trans_tendsto tendsto_beamScale)

/-- **Conditional composition, rate form.**

Because `ρ⁻²` is subordinate to `ρ^(-1/2)`, adding the beam remainder does not change the rate
that this packet can certify: the composed error is `𝒪(ρ^(-1/2))`, measured against the
same-`ρ` amplitude value. -/
theorem composed_isBigO
    (hdecomp : ∀ ρ : ℝ, I ρ = oscIntegral μ P F ρ + R ρ)
    (hR : R =O[atTop] beamScale) :
    (fun ρ : ℝ => I ρ - F.a ρ P.p * gaussConst μ P.H)
      =O[atTop] fun ρ : ℝ => (Real.sqrt ρ)⁻¹ := by
  have hsplit : (fun ρ : ℝ => I ρ - F.a ρ P.p * gaussConst μ P.H)
      = (fun ρ : ℝ => (oscIntegral μ P F ρ - F.a ρ P.p * gaussConst μ P.H) + R ρ) := by
    funext ρ
    rw [hdecomp ρ]
    ring
  rw [hsplit]
  exact (remainder_isBigO μ P F).add (hR.trans beamScale_isBigO_invSqrt)

/-- **Coefficient recovery with the beam remainder supplied as an input.**

This is exactly the inference Liu–Wang make from (4.4) and (4.5): the left-hand side of the
integral identity tends to `0`, therefore the leading beam-amplitude product vanishes at the
interaction point.  The `𝒪(ρ⁻²)` beam remainder enters only as the hypothesis `hR`. -/
theorem composed_lead_eq_zero
    (hdecomp : ∀ ρ : ℝ, I ρ = oscIntegral μ P F ρ + R ρ)
    (hR : R =O[atTop] beamScale)
    (h0 : Tendsto I atTop (𝓝 0)) :
    F.lead = 0 := by
  have h1 := composed_tendsto_of_beam_bigO μ P F I R hdecomp hR
  have h2 : F.lead * gaussConst μ P.H = 0 := tendsto_nhds_unique h1 h0
  rcases mul_eq_zero.1 h2 with h | h
  · exact h
  · exact absurd h (gaussConst_phase_ne_zero μ P)

omit [FiniteDimensional ℝ V] [BorelSpace V] [μ.IsAddHaarMeasure] in
/-- **The exact missing input for equation (4.4)'s stated rate.**

Liu–Wang assert `𝓘 = c · (leading amplitude) + 𝒪(ρ⁻²)`.  This packet proves the identification
of the leading constant together with an `𝒪(ρ^(-1/2))` error.  Upgrading the error to
`𝒪(ρ⁻²)` needs *one* further input, `hSP` below: an `𝒪(ρ⁻²)` bound on the stationary-phase
remainder itself, which in turn requires the exact expansion of the Gaussian-beam amplitudes
and the jet cancellations it produces.  That input is **not** proved anywhere in this packet;
stated as a hypothesis, it composes as follows. -/
theorem composed_isBigO_of_stationaryPhase_bigO
    (hdecomp : ∀ ρ : ℝ, I ρ = oscIntegral μ P F ρ + R ρ)
    (hR : R =O[atTop] beamScale)
    (hSP : (fun ρ : ℝ => oscIntegral μ P F ρ - F.lead * gaussConst μ P.H)
      =O[atTop] beamScale) :
    (fun ρ : ℝ => I ρ - F.lead * gaussConst μ P.H) =O[atTop] beamScale := by
  have hsplit : (fun ρ : ℝ => I ρ - F.lead * gaussConst μ P.H)
      = (fun ρ : ℝ => (oscIntegral μ P F ρ - F.lead * gaussConst μ P.H) + R ρ) := by
    funext ρ
    rw [hdecomp ρ]
    ring
  rw [hsplit]
  exact hSP.add hR

end Compose

/-! ## 3.  The same, in a local chart -/

section ChartCompose

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure]
  (P : PhaseData V) (F : AmplitudeFamily V P.p P.r) (Jd : ChartDensity V) (I R : ℝ → ℂ)

/-- **The full chain, convergence form.**

`I` is the measured quantity; it decomposes as the normalized oscillatory integral against the
manifold volume element read in a chart, plus a Gaussian-beam remainder that is `𝒪(ρ⁻²)` by
hypothesis.  Then `I` converges, and the limit carries the chart Jacobian at the interaction
point. -/
theorem chart_composed_tendsto
    (hdecomp : ∀ ρ : ℝ, I ρ = oscIntegral (Jd.measure μ) P F ρ + R ρ)
    (hR : R =O[atTop] beamScale) :
    Tendsto I atTop (𝓝 (((Jd.J P.p : ℂ) * F.lead) * gaussConst μ P.H)) := by
  have hdec' : ∀ ρ : ℝ, I ρ = oscIntegral μ P (F.mulDensity Jd) ρ + R ρ := by
    intro ρ
    rw [hdecomp ρ, oscIntegral_chartMeasure μ P F Jd ρ]
  have h := composed_tendsto_of_beam_bigO μ P (F.mulDensity Jd) I R hdec' hR
  rwa [AmplitudeFamily.mulDensity_lead] at h

/-- **The full chain, in the form Liu–Wang use it.**

`I` is the measured quantity; it decomposes as the normalized oscillatory integral *against the
manifold volume element in a chart* plus a Gaussian-beam remainder that is `𝒪(ρ⁻²)` by
hypothesis.  If `I → 0` and the chart Jacobian does not vanish at the interaction point, then
the limiting leading amplitude vanishes there. -/
theorem chart_composed_lead_eq_zero (hJ : Jd.J P.p ≠ 0)
    (hdecomp : ∀ ρ : ℝ, I ρ = oscIntegral (Jd.measure μ) P F ρ + R ρ)
    (hR : R =O[atTop] beamScale)
    (h0 : Tendsto I atTop (𝓝 0)) :
    F.lead = 0 := by
  have hdec' : ∀ ρ : ℝ, I ρ = oscIntegral μ P (F.mulDensity Jd) ρ + R ρ := by
    intro ρ
    rw [hdecomp ρ, oscIntegral_chartMeasure μ P F Jd ρ]
  have h1 := composed_lead_eq_zero μ P (F.mulDensity Jd) I R hdec' hR h0
  rw [AmplitudeFamily.mulDensity_lead] at h1
  rcases mul_eq_zero.1 h1 with h2 | h2
  · exact absurd (Complex.ofReal_eq_zero.1 h2) hJ
  · exact h2

end ChartCompose

end LiuWang2025SemilinearWaveComplexStationaryPhase
