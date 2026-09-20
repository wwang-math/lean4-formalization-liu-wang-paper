import LiuWang.LiuWang2025SemilinearWaveSpacetimeGreenCore

open MeasureTheory Set
open LiuWang2025SemilinearWaveSpatialGreenCore
open LiuWang2025SemilinearWaveSpacetimeGreenCore

#check @swap_intervalIntegral
#check @SlabWavePair.temporalCancellation
#check @SlabWavePair.spatialFlux
#check @SlabWavePair.greenIdentity
#check @SlabWavePair.greenIdentity_inaccessible
#check @SlabWavePair.certificate

/-- The full Lorentzian Green identity on the slab core. -/
example {T a b : ℝ} (P : SlabWavePair T a b) (mu : ℂ) :
    (∫ t in (0 : ℝ)..T, ∫ x in a..b, P.greenIntegrand mu t x)
      = -∫ t in (0 : ℝ)..T, lateralFlux (P.u t) (P.ux t) (P.v t) (P.vx t) a b :=
  P.greenIdentity mu

/-- Equation (4.3): a single inaccessible-boundary term remains. -/
example {T a b : ℝ} (P : SlabWavePair T a b) (mu : ℂ)
    (h1 : ∀ t, P.u t a = 0) (h2 : ∀ t, P.u t b = 0) (h3 : ∀ t, P.ux t b = 0) :
    (∫ t in (0 : ℝ)..T, ∫ x in a..b, P.greenIntegrand mu t x)
      = ∫ t in (0 : ℝ)..T, P.ux t a * P.v t a :=
  P.greenIdentity_inaccessible mu h1 h2 h3

#print axioms swap_intervalIntegral
#print axioms SlabWavePair.temporalCancellation
#print axioms SlabWavePair.spatialFlux
#print axioms SlabWavePair.greenIdentity
#print axioms SlabWavePair.greenIdentity_inaccessible
#print axioms SlabWavePair.certificate
