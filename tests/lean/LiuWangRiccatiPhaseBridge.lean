import LiuWang.LiuWang2025SemilinearWaveRiccatiPhaseBridge

/-!
# Focused tests for the Riccati / transverse-jet phase bridge

These check the normalization factors that the bridge depends on, at concrete
indices, and record the axiom footprint of the principal endpoints.
-/

noncomputable section

open scoped BigOperators
open scoped Matrix.Norms.L2Operator
open Set

open LiuWang2025SemilinearWaveTransverseJet
open LiuWang2025SemilinearWaveLongitudinalJet
open LiuWang2025SemilinearWaveLongitudinalJet.LongJet
open LiuWang2025SemilinearWaveJetOperators
open LiuWang2025SemilinearWaveDegreeBlock
open LiuWang2025SemilinearWaveRiccatiPhaseBridge

namespace LiuWangRiccatiPhaseBridgeTests

/-- A constant symmetric test matrix: `1` on the diagonal, `3` off it. -/
def tstM : Real -> Fin 2 -> Fin 2 -> Complex :=
  fun _ p q => if p = q then 1 else 3

def tstM' : Real -> Fin 2 -> Fin 2 -> Complex := fun _ _ _ => 0

theorem tstM_hasDeriv (p q : Fin 2) (s : Real) :
    HasDerivAt (fun t => tstM t p q) (tstM' s p q) s := by
  simpa [tstM, tstM'] using
    (hasDerivAt_const s (if p = q then (1 : Complex) else 3))

theorem tstM_symm (s : Real) (p q : Fin 2) : tstM s p q = tstM s q p := by
  by_cases h : p = q
  · rw [h]
  · rw [tstM, tstM, if_neg h, if_neg (Ne.symm h)]

/-! ## Ordinary-monomial normalization at degree two -/

/-- `z_0^2` receives exactly `M_{00}`. -/
example : quadCoeff (tstM 0) ((Pi.single 0 1 : Multiindex 2) + Pi.single 0 1)
    = 1 := by
  rw [quadCoeff_diag]
  simp [tstM]

/-- `z_0 z_1` receives `M_{01} + M_{10}`, which for this matrix is `6`. -/
example : quadCoeff (tstM 0) ((Pi.single 0 1 : Multiindex 2) + Pi.single 1 1)
    = 6 := by
  rw [quadCoeff_offDiag _ (by decide : (0 : Fin 2) ≠ 1)]
  norm_num [tstM]

/-- **Diagonal gradient normalization**: the derivative contributes `2` and
`quadCoeff` contributes `1`. -/
example (s : Real) :
    (transverseDeriv 0 (quadJet tstM tstM' tstM_hasDeriv)).c
      (Pi.single 0 1) s = 2 * tstM s 0 0 :=
  transverseDeriv_quadJet_single tstM tstM' tstM_hasDeriv (tstM_symm s) 0 0

/-- **Off-diagonal gradient normalization**: the derivative contributes `1` and
`quadCoeff` contributes `2`.  Both cases agree at `2 M_{k i}`. -/
example (s : Real) :
    (transverseDeriv 1 (quadJet tstM tstM' tstM_hasDeriv)).c
      (Pi.single 0 1) s = 2 * tstM s 0 1 :=
  transverseDeriv_quadJet_single tstM tstM' tstM_hasDeriv (tstM_symm s) 1 0

/-- Both normalizations produce the same closed form, here `2 * 3 = 6`. -/
example (s : Real) :
    (transverseDeriv 1 (quadJet tstM tstM' tstM_hasDeriv)).c
      (Pi.single 0 1) s = 6 := by
  rw [transverseDeriv_quadJet_single tstM tstM' tstM_hasDeriv (tstM_symm s) 1 0]
  norm_num [tstM]

/-! ## `D = (1/4) d_p d_q g^{11}` -/

/-- The degree-two coefficient family of `A^{i1 i1}` is `quadCoeff (2 D)`; on
the diagonal `D` carries `1/2` of the coefficient, off the diagonal `1/4`. -/
example (G : LiuWang2025SemilinearWaveMetricJetPhaseHierarchy.FermiMetricJet 2)
    (s : Real) :
    (G.Att G.i1 G.i1).c ((Pi.single 0 1 : Multiindex 2) + Pi.single 1 1) s
      = 2 * quadCoeff (metricD G s)
        ((Pi.single 0 1 : Multiindex 2) + Pi.single 1 1) :=
  metricD_spec G (by rw [deg_add_single, deg_single]) s

example (G : LiuWang2025SemilinearWaveMetricJetPhaseHierarchy.FermiMetricJet 2)
    (s : Real) :
    metricD G s 0 1 = (4 : Complex)⁻¹ *
      (G.Att G.i1 G.i1).c ((Pi.single 0 1 : Multiindex 2) + Pi.single 1 1) s := by
  rw [metricD, if_neg (by decide : (0 : Fin 2) ≠ 1)]

example (G : LiuWang2025SemilinearWaveMetricJetPhaseHierarchy.FermiMetricJet 2)
    (s : Real) :
    metricD G s 0 0 = (2 : Complex)⁻¹ *
      (G.Att G.i1 G.i1).c ((Pi.single 0 1 : Multiindex 2) + Pi.single 0 1) s := by
  rw [metricD, if_pos rfl]

/-! ## Axiom footprint of the principal endpoints -/

#print axioms LiuWang2025SemilinearWaveRiccatiPhaseBridge.metricD_spec
#print axioms LiuWang2025SemilinearWaveRiccatiPhaseBridge.transverseDeriv_quadJet_single
#print axioms LiuWang2025SemilinearWaveRiccatiPhaseBridge.quadraticSelfTerm_quadJet
#print axioms LiuWang2025SemilinearWaveRiccatiPhaseBridge.phaseEikonalMatrix_base_eq_zero
#print axioms LiuWang2025SemilinearWaveRiccatiPhaseBridge.jetEikonal_base_deg_two
#print axioms LiuWang2025SemilinearWaveRiccatiPhaseBridge.hric_of_riccati
#print axioms LiuWang2025SemilinearWaveRiccatiPhaseBridge.exists_c2_extension
#print axioms LiuWang2025SemilinearWaveRiccatiPhaseBridge.exists_global_riccati
#print axioms LiuWang2025SemilinearWaveRiccatiPhaseBridge.exists_phase_from_riccati
#print axioms LiuWang2025SemilinearWaveRiccatiPhaseBridge.generated_quadratic_coercivity

end LiuWangRiccatiPhaseBridgeTests
