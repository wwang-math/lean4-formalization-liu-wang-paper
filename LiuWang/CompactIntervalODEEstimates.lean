import Mathlib.Analysis.ODE.Gronwall

/-!
# Quantitative ODE bounds in either time direction

The input is an actual derivative bound on an unordered compact interval.
Time reversal reduces the backward estimate to Mathlib's forward Gronwall
inequality. No continuation or solution-existence hypothesis is hidden here.
-/

noncomputable section

open Set

namespace CompactIntervalODEEstimates

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]

theorem norm_le_gronwallBound_uIcc
    {f f' : Real → E} {a b δ K ε : Real}
    (hf : ∀ t ∈ uIcc a b, HasDerivAt f (f' t) t)
    (ha : ‖f a‖ ≤ δ)
    (hbound : ∀ t ∈ uIcc a b, ‖f' t‖ ≤ K * ‖f t‖ + ε) :
    ‖f b‖ ≤ gronwallBound δ K ε |b - a| := by
  rcases le_total a b with hab | hba
  · rw [uIcc_of_le hab] at hf hbound
    rw [abs_of_nonneg (sub_nonneg.mpr hab)]
    exact norm_le_gronwallBound_of_norm_deriv_right_le
      (HasDerivAt.continuousOn hf)
      (fun t ht => (hf t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
      ha (fun t ht => hbound t (Ico_subset_Icc_self ht)) b ⟨hab, le_rfl⟩
  · rw [uIcc_of_ge hba] at hf hbound
    have hmem {t : Real} (ht : t ∈ Icc (-a) (-b)) : -t ∈ Icc b a := by
      constructor <;> linarith [ht.1, ht.2]
    have hrev (t : Real) (ht : t ∈ Icc (-a) (-b)) :
        HasDerivAt (fun s => f (-s)) (-(f' (-t))) t := by
      simpa using (hf (-t) (hmem ht)).scomp t (hasDerivAt_id t).neg
    have h := norm_le_gronwallBound_of_norm_deriv_right_le
      (HasDerivAt.continuousOn hrev)
      (fun t ht => (hrev t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
      (by simpa using ha)
      (fun t ht => by simpa using hbound (-t) (hmem (Ico_subset_Icc_self ht)))
      (-b) (show -b ∈ Icc (-a) (-b) from ⟨neg_le_neg hba, le_rfl⟩)
    rw [abs_of_nonpos (sub_nonpos.mpr hba)]
    simpa only [neg_neg, show -b - -a = -(b - a) by ring] using h

theorem norm_le_exp_uIcc {f f' : Real → E} {a b δ K : Real}
    (hf : ∀ t ∈ uIcc a b, HasDerivAt f (f' t) t)
    (ha : ‖f a‖ ≤ δ)
    (hbound : ∀ t ∈ uIcc a b, ‖f' t‖ ≤ K * ‖f t‖) :
    ‖f b‖ ≤ δ * Real.exp (K * |b - a|) := by
  simpa [gronwallBound_ε0] using
    norm_le_gronwallBound_uIcc (K := K) (ε := 0) hf ha
      (fun t ht => by simpa using hbound t ht)

end CompactIntervalODEEstimates
