import LiuWang.LiuWang2025SemilinearWaveGaussianPhaseCoercivity

/-!
Regression audit for the compactness step converting pointwise Riccati
positivity into a uniform Gaussian coercivity constant.
-/

open LiuWang2025SemilinearWaveGaussianPhaseCoercivity

#check @radiusSq_eq_zero_iff
#check @exists_coercivity_of_pos
#check @phaseValue_eq_sum
#check @phaseValue_im
#check @phaseIm_smul
#check @continuous_phaseIm
#check @phaseIm_pos
#check @exists_riccatiPhase_coercivity
#check @riccatiBeam_L2_rate
#check @reflectedRiccatiBeam_L2_rate
#check @posDef_one
#check @hermitianImaginaryPart_I_smul_one
#check @model_exists_coercivity
#check @norm_ofReal_vec
#check @quantitative_coercivity_of_normCoercive
#check @quantitativeBeam_L2_rate
#check @quantitativeBeam_interaction_bound
#check @uniformFlowBeam_L2_rate
#check @uniformFlowBeam_interaction_bound
#check @norm_phaseValue_le
#check @hasFDerivAt_phaseValue_zero
#check @sourcePhase
#check @hasFDerivAt_sourcePhase
#check @sourcePhase_im_lower
#check @exists_riccatiFourBeamConfiguration
#check @phaseValue_smul
#check @continuous_phaseValue
#check @quadraticKernel
#check @rescaled_quadratic_integral
#check @tendsto_normalized_quadratic_integral
#check @quadraticConstant_ne_zero
#check @amplitude_eq_zero_of_quadratic_identity
#check @riccatiRecovery_coefficient_eq_zero
#check @phaseValue_model
#check @modelQuadraticConstant
#check @modelQuadraticConstant_ne_zero
#check @certificate

noncomputable example (d : Nat) : Certificate d := certificate d

#print axioms exists_coercivity_of_pos
#print axioms exists_riccatiPhase_coercivity
#print axioms riccatiBeam_L2_rate
#print axioms reflectedRiccatiBeam_L2_rate
#print axioms model_exists_coercivity
#print axioms quantitative_coercivity_of_normCoercive
#print axioms quantitativeBeam_L2_rate
#print axioms uniformFlowBeam_L2_rate
#print axioms hasFDerivAt_phaseValue_zero
#print axioms exists_riccatiFourBeamConfiguration
#print axioms rescaled_quadratic_integral
#print axioms tendsto_normalized_quadratic_integral
#print axioms amplitude_eq_zero_of_quadratic_identity
#print axioms quadraticConstant_ne_zero
#print axioms riccatiRecovery_coefficient_eq_zero
#print axioms modelQuadraticConstant
#print axioms certificate
