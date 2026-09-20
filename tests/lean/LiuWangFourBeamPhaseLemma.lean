import LiuWang.LiuWang2025SemilinearWaveFourBeamPhaseLemma

open LiuWang2025SemilinearWaveFourBeamPhaseLemma
open LiuWang2025SemilinearWaveFourNullCovectors

#check @FourBeamPhaseConfiguration.summedPhase_center
#check @FourBeamPhaseConfiguration.hasFDerivAt_summedPhase
#check @FourBeamPhaseConfiguration.summedPhase_im_lower
#check @FourBeamPhaseConfiguration.totalCoercivity_pos
#check @ofLorentzFrame
#check @lorentzFrameCertificate

/-- Lemma (i)-(iii) of the source, for any four-beam configuration. -/
example {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (C : FourBeamPhaseConfiguration E) :
    C.summedPhase C.center = 0 ∧
      HasFDerivAt C.summedPhase (0 : E →L[ℝ] ℂ) C.center ∧
      0 < C.totalCoercivity ∧
      ∀ q ∈ Metric.ball C.center C.radius,
        C.totalCoercivity * dist q C.center ^ 2 ≤ (C.summedPhase q).im :=
  ⟨C.summedPhase_center, C.hasFDerivAt_summedPhase, C.totalCoercivity_pos,
    fun _ hq => C.summedPhase_im_lower hq⟩

#print axioms FourBeamPhaseConfiguration.summedPhase_center
#print axioms FourBeamPhaseConfiguration.hasFDerivAt_summedPhase
#print axioms FourBeamPhaseConfiguration.summedPhase_im_lower
#print axioms FourBeamPhaseConfiguration.certificate
#print axioms lorentzFrameCertificate

/-! Source Subsection 4.3: the higher-order split-weight configuration. -/

#check @LiuWang2025SemilinearWaveFourBeamPhaseLemma.sum_split_weight
#check @LiuWang2025SemilinearWaveFourBeamPhaseLemma.higherOrder_weighted_sum_eq_zero
#check @LiuWang2025SemilinearWaveFourBeamPhaseLemma.higherOrder_split_weight_ne_zero

#print axioms LiuWang2025SemilinearWaveFourBeamPhaseLemma.higherOrder_weighted_sum_eq_zero
