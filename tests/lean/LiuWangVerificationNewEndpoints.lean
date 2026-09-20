import LiuWang.LiuWang2025SemilinearWaveVerification

open LiuWang2025SemilinearWaveVerification

/-! Consolidated axiom audit of the endpoints added in this pass, at the level
of the verification dossier itself. -/

#check @holomorphicExpansionVerificationBundle_tail
#check @fermiEikonalVerificationBundle_secondJet
#check @fermiEikonalVerificationBundle_riccatiFromEikonal
#check @fermiTransportVerificationBundle_centerEquation
#check @transportHierarchyVerificationBundle_recursion
#check @fourBeamPhaseVerificationBundle_coercivity
#check @spatialGreenVerificationBundle_inaccessibleFlux
#check @spacetimeGreenVerificationBundle_identity
#check @spacetimeGreenVerificationBundle_inaccessible
#check @inaccessibleBoundaryVerificationBundle_superpolynomial
#check @gaussianMassVerificationBundle_normScaling
#check @gaussianMassVerificationBundle_transverseL2Rate
#check @boundaryReflectionVerificationBundle_specular
#check @fermiNormalizationVerificationBundle_model
#check @concreteDirectedGreenVerificationBundle_identity
#check @concreteDirectedGreenVerificationBundle_nonVacuous
#check @concreteWaveGreenIdentityEngine
#check @gaussianL2BridgeVerificationBundle_momentScaling
#check @gaussianL2BridgeVerificationBundle_pointwiseToL2
#check @gaussianL2BridgeVerificationBundle_beamRate
#check @gaussianL2BridgeVerificationBundle_widthsAdd
#check @gaussianL2BridgeVerificationBundle_fourBeamProduct
#check @gaussianL2BridgeVerificationBundle_reflectedRate
#check @gaussianL2BridgeVerificationBundle_remainderRate
#check @gaussianPhaseCoercivityVerificationBundle_homogeneous
#check @gaussianPhaseCoercivityVerificationBundle_riccati
#check @gaussianPhaseCoercivityVerificationBundle_beamRate
#check @gaussianPhaseCoercivityVerificationBundle_explicitWidth
#check @gaussianPhaseCoercivityVerificationBundle_uniformFlowRate
#check @gaussianL2BridgeVerificationBundle_normComparison
#check @gaussianL2BridgeVerificationBundle_interactionRate
#check @gaussianL2BridgeVerificationBundle_weightedInteraction
#check @gaussianL2BridgeVerificationBundle_remainderVanishes
#check @gaussianL2BridgeVerificationBundle_sobolevOrder
#check @gaussianL2BridgeVerificationBundle_arbitraryWeight
#check @gaussianL2BridgeVerificationBundle_sourceReflectedBoundary
#check @gaussianL2BridgeVerificationBundle_inaccessibleBoundary
#check @fourBeamPhaseVerificationBundle_higherOrderBalance
#check @gaussianL2BridgeVerificationBundle_normalizedInteraction
#check @gaussianL2BridgeVerificationBundle_pointRecovery
#check @gaussianL2BridgeVerificationBundle_pointRecoveryBoundary
#check @gaussianL2BridgeVerificationBundle_pointRecoveryNonVacuous
#check @holomorphicExpansionVerificationBundle_orderInduction
#check @holomorphicExpansionVerificationBundle_fullRecovery
#check @gaussianL2BridgeVerificationBundle_rescaling
#check @gaussianL2BridgeVerificationBundle_stationaryPhase
#check @gaussianL2BridgeVerificationBundle_pointwiseVanishing
#check @gaussianL2BridgeVerificationBundle_coefficientVanishing
#check @gaussianPhaseCoercivityVerificationBundle_fourBeamRealization
#check @gaussianPhaseCoercivityVerificationBundle_quadraticRescaling
#check @gaussianPhaseCoercivityVerificationBundle_quadraticLimit
#check @gaussianPhaseCoercivityVerificationBundle_quadraticVanishing
#check @gaussianPhaseCoercivityVerificationBundle_assembledRecovery
#check @gaussianPhaseCoercivityVerificationBundle_modelConstant

example : concreteAnalyticObligations.length = 11 := rfl

example : stageStatus .holomorphicTaylorExpansion = .verified := rfl
example : stageStatus .fermiEikonalTransverseJetFromMetric = .verified := rfl
example : stageStatus .fermiEikonalRiccatiEquivalence = .verified := rfl
example : stageStatus .fermiNormalizationNonVacuity = .verified := rfl
example : stageStatus .fermiCenterTransportCoefficient = .verified := rfl
example : stageStatus .fermiGeneratedTransportHierarchy = .verified := rfl
example : stageStatus .fourBeamSummedPhaseLemma = .verified := rfl
example : stageStatus .concreteSpatialGreenLateralFlux = .verified := rfl
example : stageStatus .concreteSpatialGreenAccessibleCancellation = .verified := rfl
example : stageStatus .concreteSpacetimeGreenIdentity = .verified := rfl
example : stageStatus .inaccessibleBoundaryGaussianEstimate = .verified := rfl
example : stageStatus .inaccessibleBoundarySuperpolynomialDecay = .verified := rfl
example : stageStatus .gaussianGeneratedInaccessibleBoundaryRecovery = .verified := rfl
example : stageStatus .computedTransverseGaussianMass = .verified := rfl
example : stageStatus .variableGeometrySpecularReflection = .verified := rfl
example : stageStatus .concreteSlabDirectedGreenModel = .verified := rfl
example : stageStatus .concreteGreenCarrierNonVacuity = .verified := rfl
example : stageStatus .transverseMomentScalingInDimension = .verified := rfl
example : stageStatus .pointwiseGaussianToTransverseL2Bridge = .verified := rfl
example : stageStatus .gaussianBeamTransverseL2Rate = .verified := rfl
example : stageStatus .fourBeamProductTransverseL2Rate = .verified := rfl
example : stageStatus .specularReflectionPreservesGaussianProfile = .verified := rfl
example : stageStatus .reflectedBeamTransverseL2Rate = .verified := rfl
example : stageStatus .gaussianBeamRemainderTransverseRate = .verified := rfl
example : stageStatus .homogeneousQuadraticUniformCoercivity = .verified := rfl
example : stageStatus .riccatiPhaseUniformCoercivity = .verified := rfl
example : stageStatus .riccatiBeamTransverseL2Rate = .verified := rfl
example : stageStatus .explicitRiccatiFlowGaussianWidth = .verified := rfl
example : stageStatus .uniformFlowBeamTransverseRate = .verified := rfl
example : stageStatus .ambientNormProfileComparison = .verified := rfl
example : stageStatus .sobolevOrderTransverseRate = .verified := rfl
example : stageStatus .arbitraryWeightTransverseL2Rate = .verified := rfl
example : stageStatus .sourceReflectedBoundaryDisplayedRate = .verified := rfl
example : stageStatus .inaccessibleBoundaryPairingVanishes = .verified := rfl
example : stageStatus .higherOrderSplitBeamBalance = .verified := rfl
example : stageStatus .sourceNormalizedInteractionBounded = .verified := rfl
example : stageStatus .reflectedBeamPointRecoveryFromBoundaryRate = .verified := rfl
example : stageStatus .reflectedBeamPointRecoveryNonVacuity = .verified := rfl
example : stageStatus .sourceOrderInduction = .verified := rfl
example : stageStatus .fullNonlinearityFromCubicAndInduction = .verified := rfl
example : stageStatus .gaussianRescalingIdentity = .verified := rfl
example : stageStatus .gaussianStationaryPhaseLimit = .verified := rfl
example : stageStatus .gaussianPointwiseVanishing = .verified := rfl
example : stageStatus .interactionCoefficientExtraction = .verified := rfl
example : stageStatus .riccatiRealizedFourBeamPhase = .verified := rfl
example : stageStatus .quadraticPhaseRescalingIdentity = .verified := rfl
example : stageStatus .complexQuadraticStationaryPhaseLimit = .verified := rfl
example : stageStatus .quadraticPhasePointwiseVanishing = .verified := rfl
example : stageStatus .riccatiCubicRecoveryAssembled = .verified := rfl
example : stageStatus .modelQuadraticConstantComputed = .verified := rfl
example : stageStatus .transverseL1ProfileBound = .verified := rfl
example : stageStatus .weightedFourBeamInteractionDecay = .verified := rfl
example : stageStatus .fourBeamInteractionRemainderVanishes = .verified := rfl

/-- The obligations that remain are still not labelled verified. -/
example : concreteAnalyticObligations.map stageStatus =
    [LiuWangVerification.VerificationStatus.assumptionTracked,
     LiuWangVerification.VerificationStatus.assumptionTracked,
     LiuWangVerification.VerificationStatus.assumptionTracked,
     LiuWangVerification.VerificationStatus.assumptionTracked,
     LiuWangVerification.VerificationStatus.assumptionTracked,
     LiuWangVerification.VerificationStatus.assumptionTracked,
     LiuWangVerification.VerificationStatus.assumptionTracked,
     LiuWangVerification.VerificationStatus.assumptionTracked,
     LiuWangVerification.VerificationStatus.openBridge,
     LiuWangVerification.VerificationStatus.assumptionTracked,
     LiuWangVerification.VerificationStatus.assumptionTracked] := rfl

#print axioms holomorphicExpansionVerificationBundle_tail
#print axioms fermiEikonalVerificationBundle_secondJet
#print axioms fermiEikonalVerificationBundle_riccatiFromEikonal
#print axioms fermiTransportVerificationBundle_centerEquation
#print axioms transportHierarchyVerificationBundle_recursion
#print axioms fourBeamPhaseVerificationBundle_coercivity
#print axioms spatialGreenVerificationBundle_inaccessibleFlux
#print axioms spacetimeGreenVerificationBundle_identity
#print axioms spacetimeGreenVerificationBundle_inaccessible
#print axioms inaccessibleBoundaryVerificationBundle_superpolynomial
#print axioms gaussianMassVerificationBundle_normScaling
#print axioms gaussianMassVerificationBundle_transverseL2Rate
#print axioms boundaryReflectionVerificationBundle_specular
#print axioms fermiNormalizationVerificationBundle_model
#print axioms concreteDirectedGreenVerificationBundle_identity
#print axioms concreteDirectedGreenVerificationBundle_nonVacuous
#print axioms gaussianL2BridgeVerificationBundle_pointwiseToL2
#print axioms gaussianL2BridgeVerificationBundle_beamRate
#print axioms gaussianL2BridgeVerificationBundle_fourBeamProduct
#print axioms gaussianL2BridgeVerificationBundle_reflectedRate
#print axioms gaussianL2BridgeVerificationBundle_remainderRate
#print axioms gaussianPhaseCoercivityVerificationBundle_riccati
#print axioms gaussianPhaseCoercivityVerificationBundle_beamRate
#print axioms gaussianPhaseCoercivityVerificationBundle_uniformFlowRate
#print axioms gaussianL2BridgeVerificationBundle_interactionRate
#print axioms gaussianL2BridgeVerificationBundle_weightedInteraction
#print axioms gaussianL2BridgeVerificationBundle_remainderVanishes
#print axioms gaussianL2BridgeVerificationBundle_sobolevOrder
#print axioms gaussianL2BridgeVerificationBundle_sourceReflectedBoundary
#print axioms gaussianL2BridgeVerificationBundle_inaccessibleBoundary
#print axioms fourBeamPhaseVerificationBundle_higherOrderBalance
#print axioms gaussianL2BridgeVerificationBundle_normalizedInteraction
#print axioms gaussianL2BridgeVerificationBundle_pointRecovery
#print axioms holomorphicExpansionVerificationBundle_orderInduction
#print axioms holomorphicExpansionVerificationBundle_fullRecovery
#print axioms gaussianL2BridgeVerificationBundle_stationaryPhase
#print axioms gaussianL2BridgeVerificationBundle_pointwiseVanishing
#print axioms gaussianL2BridgeVerificationBundle_coefficientVanishing
#print axioms gaussianPhaseCoercivityVerificationBundle_fourBeamRealization
#print axioms gaussianPhaseCoercivityVerificationBundle_quadraticLimit
#print axioms gaussianPhaseCoercivityVerificationBundle_quadraticVanishing
#print axioms gaussianPhaseCoercivityVerificationBundle_assembledRecovery
#print axioms gaussianPhaseCoercivityVerificationBundle_modelConstant

/-! Section 3 constructed local Gaussian beam: dossier endpoints. -/
#check @chartBeamVerificationBundle_wkbIdentity
#check @chartBeamVerificationBundle_residual
#check @chartBeamVerificationBundle_remainderRate
#check @chartBeamVerificationBundle_traceCancellation
#check @chartBeamVerificationBundle_reflectedBoundaryRate
#check @chartBeamVerificationBundle_quadraticPhaseJet
#check @chartBeamVerificationBundle_constructedPhaseCoercivity

example : stageStatus .GaussianBeamRemainderEstimate = .verified := rfl
example : stageStatus .reflectedGaussianBeamConstruction = .assumptionTracked := rfl
example : stageStatus .eikonalRiccatiAndTransportHierarchy = .openBridge := rfl
example : stageStatus .reflectedBeamBoundaryNormEstimate = .assumptionTracked := rfl

#print axioms chartBeamVerificationBundle_wkbIdentity
#print axioms chartBeamVerificationBundle_residual
#print axioms chartBeamVerificationBundle_remainderRate
#print axioms chartBeamVerificationBundle_traceCancellation
#print axioms chartBeamVerificationBundle_reflectedBoundaryRate
#print axioms chartBeamVerificationBundle_quadraticPhaseJet
#print axioms chartBeamVerificationBundle_constructedPhaseCoercivity

/-! Section 3 finite-order construction: dossier endpoints. -/
#check @chartBeamVerificationBundle_unconditionalExpansion
#check @chartBeamVerificationBundle_taylorRemainder
#check @chartBeamVerificationBundle_finiteOrderEquation311
#check @chartBeamVerificationBundle_equation311Exponent
#check @chartBeamVerificationBundle_terminalDominated
#check @chartBeamVerificationBundle_transverseJetTail
#check @chartBeamVerificationBundle_phaseAnsatzJet

example : concreteAnalyticObligations.length = 11 := rfl
example : stageStatus .GaussianBeamRemainderEstimate = .verified := rfl
example : stageStatus .eikonalRiccatiAndTransportHierarchy = .openBridge := rfl

#print axioms chartBeamVerificationBundle_unconditionalExpansion
#print axioms chartBeamVerificationBundle_taylorRemainder
#print axioms chartBeamVerificationBundle_finiteOrderEquation311
#print axioms chartBeamVerificationBundle_equation311Exponent
#print axioms chartBeamVerificationBundle_terminalDominated
#print axioms chartBeamVerificationBundle_transverseJetTail
#print axioms chartBeamVerificationBundle_phaseAnsatzJet

/-! Section 3 triangular longitudinal recursion: dossier endpoints. -/
#check @jetRecursionVerificationBundle_towerHasDerivAt
#check @jetRecursionVerificationBundle_phaseCancellation
#check @jetRecursionVerificationBundle_amplitudeCancellation
#check @jetRecursionVerificationBundle_degreeZeroEikonal
#check @jetRecursionVerificationBundle_realizationDerivative
#check @jetRecursionVerificationBundle_firstJetCoefficient

example : concreteAnalyticObligations.length = 11 := rfl
example : stageStatus .eikonalRiccatiAndTransportHierarchy = .openBridge := rfl

#print axioms jetRecursionVerificationBundle_towerHasDerivAt
#print axioms jetRecursionVerificationBundle_phaseCancellation
#print axioms jetRecursionVerificationBundle_amplitudeCancellation
#print axioms jetRecursionVerificationBundle_degreeZeroEikonal
#print axioms jetRecursionVerificationBundle_realizationDerivative
#print axioms jetRecursionVerificationBundle_firstJetCoefficient

#check @jetRecursionVerificationBundle_degreeOneEikonal
#check @jetRecursionVerificationBundle_gradedConvolution
#print axioms jetRecursionVerificationBundle_degreeOneEikonal
#print axioms jetRecursionVerificationBundle_gradedConvolution

/-! Section 3 Fermi metric jet: dossier endpoints. -/
#check @jetNormalizationVerificationBundle_jderivCorrespondence
#check @jetNormalizationVerificationBundle_eikonalLocality
#check @metricJetVerificationBundle_derivedLowOrder
#check @metricJetVerificationBundle_degreeZero
#check @metricJetVerificationBundle_degreeOne

example : concreteAnalyticObligations.length = 11 := rfl
example : stageStatus .eikonalRiccatiAndTransportHierarchy = .openBridge := rfl

#print axioms jetNormalizationVerificationBundle_jderivCorrespondence
#print axioms jetNormalizationVerificationBundle_eikonalLocality
#print axioms metricJetVerificationBundle_derivedLowOrder
#print axioms metricJetVerificationBundle_degreeZero
#print axioms metricJetVerificationBundle_degreeOne

#check @metricJetVerificationBundle_triangularity
#check @metricJetVerificationBundle_longitudinalCoefficient
#print axioms metricJetVerificationBundle_triangularity
#print axioms metricJetVerificationBundle_longitudinalCoefficient

#check @degreeBlockVerificationBundle_riccatiNormalization
#check @degreeBlockVerificationBundle_insertion
#check @degreeBlockVerificationBundle_blockLipschitz
#check @degreeBlockVerificationBundle_blockODE
#check @degreeBlockVerificationBundle_sameDegreeLinearity

example : stageStatus .eikonalRiccatiAndTransportHierarchy = .openBridge := rfl
example : concreteAnalyticObligations.length = 11 := rfl

#print axioms degreeBlockVerificationBundle_riccatiNormalization
#print axioms degreeBlockVerificationBundle_insertion
#print axioms degreeBlockVerificationBundle_blockLipschitz
#print axioms degreeBlockVerificationBundle_blockODE
#print axioms degreeBlockVerificationBundle_sameDegreeLinearity

#check @degreeBlockVerificationBundle_matrixRepresentation
#check @degreeBlockVerificationBundle_eikonalBlockForm
#check @degreeBlockVerificationBundle_recursionStep
#print axioms degreeBlockVerificationBundle_matrixRepresentation
#print axioms degreeBlockVerificationBundle_eikonalBlockForm
#print axioms degreeBlockVerificationBundle_recursionStep
