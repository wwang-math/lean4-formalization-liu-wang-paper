import LiuWang.LiuWang2025SemilinearWaveRiccatiPhaseExample

/-!
# Non-vacuity of the generated-phase endpoint

Checks that the explicit transverse dimension three example really instantiates
the bridge, that its `C` is literally `diag(0,2,2)`, and that its `D` is not
zero.
-/

noncomputable section

open scoped Matrix.Norms.L2Operator
open Set
open LiuWang2025SemilinearWaveTransverseJet
open LiuWang2025SemilinearWaveRiccatiPhaseBridge
open LiuWang2025SemilinearWaveRiccatiPhaseExample

namespace LiuWangRiccatiPhaseExampleTests

/-- `C = diag(0, 2, 2)`, literally. -/
example (s : Real) : metricC exMetric s 0 0 = 0 := by
  rw [exMetric_C, exC, if_pos rfl, if_pos rfl]

example (s : Real) : metricC exMetric s 1 1 = 2 := by
  rw [exMetric_C, exC, if_pos rfl, if_neg (by decide : ¬(1 : Fin 3) = 0)]

example (s : Real) : metricC exMetric s 2 2 = 2 := by
  rw [exMetric_C, exC, if_pos rfl, if_neg (by decide : ¬(2 : Fin 3) = 0)]

example (s : Real) : metricC exMetric s 0 1 = 0 := by
  rw [exMetric_C, exC, if_neg (by decide : ¬(0 : Fin 3) = 1)]

example (s : Real) : metricC exMetric s 1 2 = 0 := by
  rw [exMetric_C, exC, if_neg (by decide : ¬(1 : Fin 3) = 2)]

/-- `D` is not the zero matrix, so the example carries genuine curvature. -/
example (s : Real) : metricD exMetric s 0 0 ≠ 0 := exMetric_D_ne_zero s

/-- The Fermi first-order normalization really holds for this jet. -/
example (i j k : Fin 3) (s : Real) :
    (exMetric.Att i j).c (Pi.single k 1) s = 0 :=
  exFermiData.firstOrderVanishing i j k s

/-- The base phase is the source's `phi_1 = z^{i1}`. -/
example (s : Real) : exBasePhase.phi.c (Pi.single 0 1) s = 1 := by
  have := exBasePhase.phi_one 0 s
  rw [exMetric_i1, if_pos rfl] at this
  exact this

example (s : Real) : exBasePhase.phi.c (Pi.single 1 1) s = 0 := by
  have := exBasePhase.phi_one 1 s
  rw [exMetric_i1, if_neg (by decide : ¬(1 : Fin 3) = 0)] at this
  exact this

#print axioms LiuWang2025SemilinearWaveRiccatiPhaseExample.exMetric_C
#print axioms LiuWang2025SemilinearWaveRiccatiPhaseExample.exMetric_D
#print axioms LiuWang2025SemilinearWaveRiccatiPhaseExample.exFermiData
#print axioms LiuWang2025SemilinearWaveRiccatiPhaseExample.exC1Data
#print axioms LiuWang2025SemilinearWaveRiccatiPhaseExample.exH0_pos
#print axioms LiuWang2025SemilinearWaveRiccatiPhaseExample.exH0_coercive
#print axioms LiuWang2025SemilinearWaveRiccatiPhaseExample.exists_example_phase
#print axioms LiuWang2025SemilinearWaveRiccatiPhaseExample.exists_example_phase_order_four

end LiuWangRiccatiPhaseExampleTests
