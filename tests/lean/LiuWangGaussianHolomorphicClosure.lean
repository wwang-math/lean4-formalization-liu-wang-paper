import LiuWang.LiuWang2025SemilinearWaveVerification

open LiuWang2025SemilinearWaveGaussianHolomorphicClosure

variable {V : Type*}
variable [NormedAddCommGroup V] [InnerProductSpace Real V]
variable [MeasurableSpace V] [BorelSpace V] [FiniteDimensional Real V]
variable {reachable : Set V}

example (data : ReachableGaussianCoefficientData (reachable := reachable))
    (p : V) (hp : p ∈ reachable) (m : Nat) :
    data.expansions.coefficients1 p m =
      data.expansions.coefficients2 p m :=
  data.coefficients_eq p hp m

example (data : ReachableGaussianCoefficientData (reachable := reachable))
    (p : V) (hp : p ∈ reachable) (z : Complex) :
    data.expansions.nonlinearity1 p z =
      data.expansions.nonlinearity2 p z :=
  LiuWang2025SemilinearWaveVerification.gaussianHolomorphicClosureVerificationBundle_endpoint
    data p hp z

example :
    LiuWang2025SemilinearWaveVerification.stageStatus
        .gaussianCoefficientFamilyToHolomorphicRecovery =
      LiuWangVerification.VerificationStatus.verified :=
  LiuWang2025SemilinearWaveVerification.gaussianCoefficientFamilyToHolomorphicRecovery_is_verified

#print axioms LiuWang2025SemilinearWaveGaussianHolomorphicClosure.ReachableGaussianCoefficientData.coefficients_eq
#print axioms LiuWang2025SemilinearWaveGaussianHolomorphicClosure.ReachableGaussianCoefficientData.nonlinearities_eq
#print axioms LiuWang2025SemilinearWaveVerification.gaussianHolomorphicClosureVerificationBundle_endpoint
