/-
Copyright (c) 2026.  Released under Apache 2.0.

# ρ-indexed amplitude families

Liu–Wang's equation (4.4) is an asymptotic statement about

  `𝓘 = ρ^((n+1)/2) ∫ V₃ e^{iρS} a⁽⁰⁾_{κ₀,ρ} a⁽¹⁾_{κ₁,ρ} a⁽²⁾_{κ₂,ρ} a⁽³⁾_{κ₃,ρ} dV_g dt`,

in which the amplitude is **not** a fixed function: the Gaussian-beam amplitudes
`a⁽ʲ⁾_{κⱼ,ρ}` depend on the large parameter `ρ`.  This file isolates the hypotheses that such
a family has to satisfy for the complex stationary-phase localization to apply, namely

* a **uniform localization** radius (`supp`),
* a **uniform domination** bound (`bound`),
* a **uniform regularity** bound (`lip`) together with continuity (`cont`), and
* **convergence** of the value at the stationary point (`tendsto_lead`).

All four are uniform in `ρ`; the fourth is the only place where `ρ → ∞` enters.

Nothing here refers to Gaussian beams: an `AmplitudeFamily` is a purely analytic object.
-/
import LiuWang.LiuWang2025SemilinearWaveComplexGaussianNormalForm

noncomputable section

open MeasureTheory Complex Filter Set
open scoped Real Topology

namespace LiuWang2025SemilinearWaveComplexStationaryPhase

/-! ## 1.  Phase data -/

/-- Hypotheses on the **phase** alone, at a nondegenerate interaction point `p`.

Compare Liu–Wang Lemma 4.1: parts (i) and (ii) of that lemma are *derived* from these fields
(see `LiuWangComplexStationaryPhase`), and part (iii) is derived in the sharpened form
`c/4 * ‖h‖² ≤ (S (p + h)).im` on the localization ball. -/
structure PhaseData (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [MeasurableSpace V] where
  /-- The interaction point `p̃`. -/
  p : V
  /-- The complex phase `S`. -/
  S : V → ℂ
  /-- The complex Hessian of `S` at `p`, as a continuous bilinear form. -/
  H : V →L[ℝ] V →L[ℝ] ℂ
  /-- Coercivity constant of the imaginary part of the Hessian. -/
  c : ℝ
  /-- Localization radius. -/
  r : ℝ
  /-- Cubic Taylor-remainder constant of the phase. -/
  CR : ℝ
  hc : 0 < c
  hr : 0 < r
  hCR : 0 ≤ CR
  /-- Regularity of the phase.  Measurability suffices: the amplitude is compactly supported,
  so only the values of `S` on the localization ball matter. -/
  measS : Measurable S
  /-- **Nondegeneracy**: the imaginary part of the Hessian is positive definite, with an
  explicit constant.  This is the infinitesimal form of Liu–Wang Lemma 4.1 (iii). -/
  coercive : ∀ h : V, c * ‖h‖ ^ 2 ≤ (H h h).im
  /-- **Explicit second-order Taylor remainder** of the phase on the localization ball. -/
  taylor : ∀ h : V, ‖h‖ ≤ r → ‖S (p + h) - H h h / 2‖ ≤ CR * ‖h‖ ^ 3
  /-- The localization radius is small compared with the coercivity constant.  This is not a
  restriction: shrinking `r` always achieves it, and shrinking `r` is harmless because the
  amplitude may be multiplied by a cut-off. -/
  radiusSmall : CR * r ≤ c / 4

/-! ## 2.  Amplitude families -/

/-- A **ρ-indexed family of amplitudes** localized at `p` within radius `r`.

Every field is a hypothesis on the family; none of them asserts any part of a stationary-phase
conclusion.  The four analytic hypotheses are uniform in `ρ`; only `tendsto_lead` involves the
limit `ρ → ∞`. -/
structure AmplitudeFamily (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]
    (p : V) (r : ℝ) where
  /-- The family itself: `a ρ` is the amplitude at parameter `ρ`. -/
  a : ℝ → V → ℂ
  /-- Uniform domination constant. -/
  A : ℝ
  /-- Uniform Lipschitz constant. -/
  L : ℝ
  /-- The limit of the amplitude at the stationary point. -/
  lead : ℂ
  hA : 0 ≤ A
  hL : 0 ≤ L
  /-- **Regularity**, part 1: each member is continuous. -/
  cont : ∀ ρ : ℝ, Continuous (a ρ)
  /-- **Uniform domination**: a single bound valid for every `ρ`. -/
  bound : ∀ (ρ : ℝ) (x : V), ‖a ρ x‖ ≤ A
  /-- **Regularity**, part 2: a single Lipschitz bound valid for every `ρ`. -/
  lip : ∀ (ρ : ℝ) (x y : V), ‖a ρ x - a ρ y‖ ≤ L * ‖x - y‖
  /-- **Uniform localization**: every member vanishes outside the closed ball `B̄(p, r)`. -/
  supp : ∀ (ρ : ℝ) (h : V), r < ‖h‖ → a ρ (p + h) = 0
  /-- **Convergence** of the amplitude at the stationary point. -/
  tendsto_lead : Tendsto (fun ρ : ℝ => a ρ p) atTop (𝓝 lead)

namespace AmplitudeFamily

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {p : V} {r : ℝ}

/-- The leading value is dominated by the uniform bound. -/
theorem norm_lead_le (F : AmplitudeFamily V p r) : ‖F.lead‖ ≤ F.A := by
  refine le_of_tendsto F.tendsto_lead.norm ?_
  exact Filter.Eventually.of_forall fun ρ => F.bound ρ p

theorem measurable [MeasurableSpace V] [OpensMeasurableSpace V]
    (F : AmplitudeFamily V p r) (ρ : ℝ) : Measurable (F.a ρ) :=
  (F.cont ρ).measurable

/-- A constant family: the `ρ`-independent case, recovering the fixed-amplitude theory. -/
def const (a₀ : V → ℂ) (A L : ℝ) (hA : 0 ≤ A) (hL : 0 ≤ L)
    (cont : Continuous a₀) (bound : ∀ x, ‖a₀ x‖ ≤ A)
    (lip : ∀ x y, ‖a₀ x - a₀ y‖ ≤ L * ‖x - y‖)
    (supp : ∀ h : V, r < ‖h‖ → a₀ (p + h) = 0) : AmplitudeFamily V p r where
  a := fun _ => a₀
  A := A
  L := L
  lead := a₀ p
  hA := hA
  hL := hL
  cont := fun _ => cont
  bound := fun _ => bound
  lip := fun _ => lip
  supp := fun _ => supp
  tendsto_lead := tendsto_const_nhds

@[simp] lemma const_a (a₀ : V → ℂ) (A L : ℝ) (hA hL cont bound lip supp) (ρ : ℝ) :
    (const (p := p) (r := r) a₀ A L hA hL cont bound lip supp).a ρ = a₀ := rfl

@[simp] lemma const_lead (a₀ : V → ℂ) (A L : ℝ) (hA hL cont bound lip supp) :
    (const (p := p) (r := r) a₀ A L hA hL cont bound lip supp).lead = a₀ p := rfl

end AmplitudeFamily

end LiuWang2025SemilinearWaveComplexStationaryPhase
