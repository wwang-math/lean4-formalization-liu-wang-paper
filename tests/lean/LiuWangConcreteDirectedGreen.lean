import LiuWang.LiuWang2025SemilinearWaveConcreteDirectedGreen

open MeasureTheory
open LiuWang2025SemilinearWaveConcreteDirectedGreen
open LiuWang2025SemilinearWaveDirectedGreenRealization

#check @concrete_timeIntegrationByParts
#check @concrete_spatialGreenFormula
#check @SlabGeometry.directedWaveGreenModel
#check @SlabGeometry.generated_greenIdentity
#check @SlabGeometry.waveGreenIdentityEngine
#check @forwardWitnessJet_mem
#check @forwardWitnessJet_ne_zero
#check @backwardWitnessJet_mem
#check @backwardWitnessJet_ne_zero

/-- The abstract directed Green engine is instantiated on genuine function
spaces with genuine integrals. -/
noncomputable example (S : SlabGeometry) :
    DirectedWaveGreenModel
      (ForwardGraph := S.ForwardGraph) (BackwardGraph := S.BackwardGraph)
      (ForwardResidual := Residual) (BackwardResidual := Residual)
      (BoundaryFlux := BoundaryFlux) (BoundaryValue := BoundaryValue) :=
  S.directedWaveGreenModel

/-- Its Green identity, written out with the actual integrals. -/
example (S : SlabGeometry) (u : S.ForwardGraph) (v : S.BackwardGraph)
    (hv : (S.backwardTimeSecondMap - S.backwardSpatialMap) v = 0) :
    -slabPairing S.timeHorizon S.xMin S.xMax
        (fun t x => u.val 2 t x
          - (u.val 4 t x - S.tangentialEigenvalue * u.val 0 t x)) (v.val 0)
      = boundaryPairing S.timeHorizon
          (fun t => u.val 3 t S.xMin) (fun t => u.val 3 t S.xMax)
          (fun t => v.val 0 t S.xMin) (fun t => v.val 0 t S.xMax) :=
  S.generated_greenIdentity_explicit u v hv

/-- Both carriers are nonzero submodules. -/
example {xMin xMax T : ℝ} (hlt : xMin < xMax) (hT : T ≠ 0) :
    forwardWitnessJet xMin xMax ∈ forwardCarrier xMin xMax ∧
      forwardWitnessJet xMin xMax ≠ 0 ∧
      backwardWitnessJet T ∈ backwardCarrier T ∧
      backwardWitnessJet T ≠ 0 :=
  ⟨forwardWitnessJet_mem xMin xMax, forwardWitnessJet_ne_zero hlt,
   backwardWitnessJet_mem T, backwardWitnessJet_ne_zero hT⟩

#print axioms concrete_timeIntegrationByParts
#print axioms concrete_spatialGreenFormula
#print axioms SlabGeometry.directedWaveGreenModel
#print axioms SlabGeometry.generated_greenIdentity_explicit
#print axioms forwardWitnessJet_mem
#print axioms forwardWitnessJet_ne_zero
#print axioms backwardWitnessJet_mem
