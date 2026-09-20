import LiuWang.LiuWang2025SemilinearWaveGaussianL2Bridge

/-!
Regression audit for the pointwise-Gaussian to `L^2` bridge used by the
Liu-Wang reflected-beam boundary estimate.
-/

open LiuWang2025SemilinearWaveGaussianL2Bridge

#check @pow_le_const_mul_exp
#check @moment_le_gaussian
#check @integrable_gaussian_pi
#check @integrable_moment_pi
#check @integral_comp_smul_pi
#check @integral_moment_scaledGaussian_pi
#check @gaussianMoment_zero
#check @gaussianMoment_zero_pos
#check @normSq_le_of_profileBound
#check @integral_normSq_le_of_profileBound
#check @sqrt_integral_normSq_le_of_profileBound
#check @beamProfile_L2_rate
#check @profileBound_of_beam
#check @beamProfile_L2_rate_of_beam
#check @gaussianWitness_L2_rate
#check @gaussianWitness_constant_pos
#check @GaussianProfileBound.add
#check @GaussianProfileBound.const_mul
#check @GaussianProfileBound.mul
#check @profileBound_finsetProd
#check @profileBound_prod_L2_rate
#check @fourBeamProduct_L2_rate
#check @norm_sq_le_radiusSq
#check @radiusSq_le_dim_mul_norm_sq
#check @profileBound_of_normBound
#check @integral_norm_le_of_profileBound
#check @norm_integral_le_of_profileBound
#check @fourBeamInteraction_bound
#check @weightedFourBeamInteraction_bound
#check @reflect
#check @radiusSq_reflect
#check @reflectedDifference_eq_zero_on_face
#check @reflectedDifference_L2_rate
#check @beamRemainder_L2_rate
#check @tendsto_zero_of_rpow_bound
#check @weightedFourBeamInteraction_tendsto_zero
#check @sobolevSum_L2_rate
#check @radius
#check @RadiusProfileBound
#check @sqrt_integral_normSq_le_of_radiusProfileBound
#check @reflectedBoundaryTerm_L2_rate
#check @reflectedBoundary_summed_L2_rate
#check @reflectedBoundary_source_rate
#check @mul_le_half_sq_add
#check @norm_integral_mul_le_balanced
#check @norm_integral_mul_le_rate
#check @inaccessiblePairing_tendsto_zero
#check @normalized_interaction_bounded
#check @ReflectedBeamPointRecovery
#check @ReflectedBeamPointRecovery.boundary_tendsto_zero
#check @ReflectedBeamPointRecovery.coefficient_eq_zero
#check @witnessPointRecovery
#check @witnessPointRecovery_trace_ne_zero
#check @integral_const_mul_ofReal
#check @rescaled_gaussian_integral
#check @integral_gaussian_pi_eq
#check @tendsto_rescaled_gaussian
#check @tendsto_normalized_gaussian_integral
#check @gaussianStationaryLimit_eq_zero_iff
#check @amplitude_eq_zero_of_gaussian_identity
#check @coefficient_eq_zero_of_gaussian_identity
#check @certificate

/-- The transverse `L^2` exponent produced by the bridge is the source's
`-(m + d/4)`. -/
example (m d : Nat) :
    -((m : Real) + (d : Real) / 4) = -(m : Real) - (d : Real) / 4 := by ring

/-- With no transverse weight the exponent is exactly the source's `-d/4`. -/
example (d : Nat) : -((0 : Real) + (d : Real) / 4) = -((d : Real) / 4) := by ring

noncomputable example (d : Nat) (b rho : Real) : Certificate d b rho := certificate d b rho

#print axioms integral_moment_scaledGaussian_pi
#print axioms sqrt_integral_normSq_le_of_profileBound
#print axioms beamProfile_L2_rate
#print axioms beamProfile_L2_rate_of_beam
#print axioms gaussianWitness_L2_rate
#print axioms gaussianWitness_constant_pos
#print axioms profileBound_finsetProd
#print axioms fourBeamProduct_L2_rate
#print axioms profileBound_of_normBound
#print axioms weightedFourBeamInteraction_bound
#print axioms reflectedDifference_L2_rate
#print axioms beamRemainder_L2_rate
#print axioms weightedFourBeamInteraction_tendsto_zero
#print axioms sobolevSum_L2_rate
#print axioms sqrt_integral_normSq_le_of_radiusProfileBound
#print axioms reflectedBoundary_source_rate
#print axioms norm_integral_mul_le_rate
#print axioms inaccessiblePairing_tendsto_zero
#print axioms normalized_interaction_bounded
#print axioms ReflectedBeamPointRecovery.coefficient_eq_zero
#print axioms rescaled_gaussian_integral
#print axioms tendsto_normalized_gaussian_integral
#print axioms amplitude_eq_zero_of_gaussian_identity
#print axioms coefficient_eq_zero_of_gaussian_identity
#print axioms witnessPointRecovery
#print axioms certificate
