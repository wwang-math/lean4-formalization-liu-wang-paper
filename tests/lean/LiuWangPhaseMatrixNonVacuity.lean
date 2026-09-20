import LiuWang.LiuWang2025SemilinearWavePhaseUpdate
import LiuWang.LiuWang2025SemilinearWaveRiccatiODE

/-!
# Non-vacuity of the degree-`r` eikonal matrix

`phaseEikonalMatrix` is the coefficient of the genuine degree-`r` block
equation.  This file exhibits an explicit Fermi metric jet and an explicit
quadratic phase for which one *off-diagonal* entry of that matrix -- an entry
at `alpha = z_0^3`, `beta = z_0^2 z_1`, two distinct multi-indices of the same
total degree three -- is nonzero, and proves its value.

The mixing comes from the cross term `z_0 z_1` in the quadratic phase, exactly
as the source's `4 (A M z) . grad_z` predicts: the block operator is diagonal on
monomials only when `A M` is.
-/

noncomputable section

open scoped BigOperators

open LiuWang2025SemilinearWaveTransverseJet
open LiuWang2025SemilinearWaveLongitudinalJet
open LiuWang2025SemilinearWaveLongitudinalJet.LongJet
open LiuWang2025SemilinearWaveJetOperators
open LiuWang2025SemilinearWaveDegreeBlock
open LiuWang2025SemilinearWaveMetricJetPhaseHierarchy
open LiuWang2025SemilinearWaveSameDegreeMatrix

namespace LiuWangPhaseMatrixNonVacuity

/-- Two transverse multi-indices in dimension two agree when their two entries
do. -/
theorem index_ext {b c : Multiindex 2} (h0 : b 0 = c 0) (h1 : b 1 = c 1) :
    b = c := by
  funext i
  fin_cases i
  · exact h0
  · exact h1

/-- `z_0^3`. -/
def alphaIdx : Multiindex 2 := fun i => if i = 0 then 3 else 0
/-- `z_0^2 z_1`. -/
def betaIdx : Multiindex 2 := fun i => if i = 0 then 2 else 1
/-- `z_0^2`, the support of the transverse gradient of the basis jet at `beta`. -/
def gammaIdx : Multiindex 2 := fun i => if i = 0 then 2 else 0
/-- `z_0 z_1`, the cross term of the quadratic phase. -/
def crossIdx : Multiindex 2 := fun _ => 1
/-- `z_0`, the linear phase index. -/
def oneIdx : Multiindex 2 := fun i => if i = 0 then 1 else 0

theorem deg_alpha : deg alphaIdx = 3 := by
  show alphaIdx 0 + alphaIdx 1 = 3
  simp [alphaIdx]
theorem deg_beta : deg betaIdx = 3 := by
  show betaIdx 0 + betaIdx 1 = 3
  simp [betaIdx]
theorem deg_cross : deg crossIdx = 2 := by
  show crossIdx 0 + crossIdx 1 = 2
  simp [crossIdx]

theorem alpha_ne_beta : alphaIdx ≠ betaIdx := by
  intro h
  have := congrFun h 1
  simp [alphaIdx, betaIdx] at this

/-- The unit longitudinal pairing jet. -/
def unitJet : LongJet 2 :=
  singleJet 0 (fun _ => 1) (fun _ => 0) (fun s => hasDerivAt_const s (1 : Complex))

/-- A Fermi metric jet whose only nonzero transverse entry is `A^{11} = 1`. -/
def xMetric : FermiMetricJet 2 where
  Ass := zeroJet 2
  Bs := fun i => if i = 0 then unitJet else zeroJet 2
  Att := fun i j => if i = 0 then zeroJet 2 else if j = 0 then zeroJet 2
    else basisJet 0
  i1 := 0
  nullRow := by intro j s; simp
  nullCol := by
    intro i s
    by_cases h : i = 0 <;> simp [h]
  nullSecondOrder := by intro k s; simp
  longitudinalNormalization := by
    intro s
    show (if (0 : Fin 2) = 0 then unitJet else zeroJet 2).c 0 s = 1
    simp [unitJet]

theorem xAtt11 : xMetric.Att 1 1 = basisJet (0 : Multiindex 2) := by
  show (if (1 : Fin 2) = 0 then zeroJet 2 else if (1 : Fin 2) = 0 then zeroJet 2
    else basisJet 0) = _
  simp

theorem xAtt_zero {i j : Fin 2} (h : i = 0 ∨ j = 0) :
    xMetric.Att i j = zeroJet 2 := by
  show (if i = 0 then zeroJet 2 else if j = 0 then zeroJet 2 else basisJet 0) = _
  rcases h with h | h <;> simp [h]

/-- The phase: the source's linear term `z_0` plus a `z_0 z_1` cross term. -/
def xPhiJet : LongJet 2 where
  c := fun a _ => if a = oneIdx then 1 else if a = crossIdx then 1 else 0
  dc := fun _ _ => 0
  hasDeriv := by
    intro a s
    by_cases h1 : a = oneIdx
    · simpa [h1] using hasDerivAt_const s (1 : Complex)
    · by_cases h2 : a = crossIdx
      · simpa [h1, h2] using hasDerivAt_const s (1 : Complex)
      · simpa [h1, h2] using hasDerivAt_const s (0 : Complex)

theorem single_zero_eq : (Pi.single (0 : Fin 2) 1 : Multiindex 2) = oneIdx := by
  refine index_ext ?_ ?_ <;> simp [oneIdx]

theorem single_one_ne_one : (Pi.single (1 : Fin 2) 1 : Multiindex 2) ≠ oneIdx := by
  intro h
  have := congrFun h 0
  simp [oneIdx] at this

theorem single_one_ne_cross :
    (Pi.single (1 : Fin 2) 1 : Multiindex 2) ≠ crossIdx := by
  intro h
  have := congrFun h 0
  simp [crossIdx] at this

theorem zero_ne_one_idx : (0 : Multiindex 2) ≠ oneIdx := by
  intro h
  have := congrFun h 0
  simp [oneIdx] at this

theorem zero_ne_cross : (0 : Multiindex 2) ≠ crossIdx := by
  intro h
  have := congrFun h 0
  simp [crossIdx] at this

/-- It is a genuine source phase jet for `xMetric`. -/
def xPhase : SourcePhaseJet xMetric where
  phi := xPhiJet
  dphi := zeroJet 2
  dphi_is_deriv := xPhiJet.hasDeriv
  phi_zero := by
    intro s
    show (if (0 : Multiindex 2) = oneIdx then (1 : Complex)
      else if (0 : Multiindex 2) = crossIdx then 1 else 0) = 0
    rw [if_neg zero_ne_one_idx, if_neg zero_ne_cross]
  phi_one := by
    intro i s
    show (if (Pi.single i 1 : Multiindex 2) = oneIdx then (1 : Complex)
      else if (Pi.single i 1 : Multiindex 2) = crossIdx then 1 else 0)
      = if i = xMetric.i1 then 1 else 0
    by_cases hi : i = 0
    · subst hi
      rw [if_pos single_zero_eq]
      show (1 : Complex) = if (0 : Fin 2) = xMetric.i1 then 1 else 0
      simp [xMetric]
    · have hi1 : i = 1 := by omega
      subst hi1
      rw [if_neg single_one_ne_one, if_neg single_one_ne_cross]
      show (0 : Complex) = if (1 : Fin 2) = xMetric.i1 then 1 else 0
      simp [xMetric]

/-- The quadratic phase really carries the cross term. -/
theorem xPhase_cross (s : Real) : xPhase.phi.c crossIdx s = 1 := by
  show (if crossIdx = oneIdx then (1 : Complex)
    else if crossIdx = crossIdx then 1 else 0) = 1
  rw [if_neg (fun h => by simpa [crossIdx, oneIdx] using congrFun h 1), if_pos rfl]

/-! ## Index arithmetic -/

theorem gamma_add : (gammaIdx + Pi.single 1 1 : Multiindex 2) = betaIdx := by
  refine index_ext ?_ ?_ <;> simp [gammaIdx, betaIdx]

theorem one_add : (oneIdx + Pi.single 1 1 : Multiindex 2) = crossIdx := by
  refine index_ext ?_ ?_ <;> simp [oneIdx, crossIdx]

theorem alpha_sub_gamma : alphaIdx - gammaIdx = oneIdx := by
  refine index_ext ?_ ?_ <;> simp [alphaIdx, gammaIdx, oneIdx]

theorem alpha_sub_one : alphaIdx - oneIdx = gammaIdx := by
  refine index_ext ?_ ?_ <;> simp [alphaIdx, oneIdx, gammaIdx]

theorem alpha_sub_zero : alphaIdx - 0 = alphaIdx := by
  refine index_ext ?_ ?_ <;> simp

theorem gamma_mem : gammaIdx ∈ below alphaIdx := by
  refine mem_below.2 fun i => ?_
  fin_cases i <;> simp [gammaIdx, alphaIdx]

theorem one_mem : oneIdx ∈ below alphaIdx := by
  refine mem_below.2 fun i => ?_
  fin_cases i <;> simp [oneIdx, alphaIdx]

theorem zero_mem : (0 : Multiindex 2) ∈ below alphaIdx :=
  mem_below.2 fun _ => Nat.zero_le _

/-! ## The two gradients are each supported at a single index -/

theorem dbj_support (b : Multiindex 2) (s : Real) (hb : b ≠ gammaIdx) :
    (transverseDeriv 1 (basisJet betaIdx)).c b s = 0 := by
  show ((b 1 + 1 : Nat) : Complex)
    * (basisJet betaIdx).c (b + Pi.single 1 1) s = 0
  rw [basisJet_c, if_neg, mul_zero]
  intro hcon
  refine hb (index_ext ?_ ?_)
  · have h := congrFun hcon 0
    simpa [betaIdx, gammaIdx, Pi.single_apply] using h
  · have h := congrFun hcon 1
    simp [betaIdx] at h
    simpa [gammaIdx] using h

theorem dbj_value (s : Real) :
    (transverseDeriv 1 (basisJet betaIdx)).c gammaIdx s = 1 := by
  show ((gammaIdx 1 + 1 : Nat) : Complex)
    * (basisJet betaIdx).c (gammaIdx + Pi.single 1 1) s = 1
  rw [gamma_add, basisJet_c, if_pos rfl]
  simp [gammaIdx]

theorem dphi_support (b : Multiindex 2) (s : Real) (hb : b ≠ oneIdx) :
    (transverseDeriv 1 xPhase.phi).c b s = 0 := by
  have h1 : (b + Pi.single 1 1 : Multiindex 2) ≠ oneIdx := by
    intro hcon
    have h := congrFun hcon 1
    simp [oneIdx] at h
  have h2 : (b + Pi.single 1 1 : Multiindex 2) ≠ crossIdx := by
    intro hcon
    refine hb (index_ext ?_ ?_)
    · have h := congrFun hcon 0
      simpa [crossIdx, oneIdx, Pi.single_apply] using h
    · have h := congrFun hcon 1
      simp [crossIdx] at h
      simpa [oneIdx] using h
  show ((b 1 + 1 : Nat) : Complex)
    * (if (b + Pi.single 1 1 : Multiindex 2) = oneIdx then (1 : Complex)
        else if (b + Pi.single 1 1 : Multiindex 2) = crossIdx then 1 else 0) = 0
  rw [if_neg h1, if_neg h2, mul_zero]

theorem dphi_value (s : Real) :
    (transverseDeriv 1 xPhase.phi).c oneIdx s = 1 := by
  have h1 : (oneIdx + Pi.single 1 1 : Multiindex 2) ≠ oneIdx := by
    rw [one_add]
    intro hcon
    have h := congrFun hcon 1
    simp [crossIdx, oneIdx] at h
  show ((oneIdx 1 + 1 : Nat) : Complex)
    * (if (oneIdx + Pi.single 1 1 : Multiindex 2) = oneIdx then (1 : Complex)
        else if (oneIdx + Pi.single 1 1 : Multiindex 2) = crossIdx then 1 else 0)
    = 1
  rw [if_neg h1, one_add, if_pos rfl]
  simp [oneIdx]

/-! ## The off-diagonal entry -/

theorem mul_zeroJet_c (X : LongJet 2) (a : Multiindex 2) (s : Real) :
    (mul (zeroJet 2) X).c a s = 0 :=
  mul_c_vanish (p := deg a + 1) (q := 0) (fun _ _ => rfl) vanish_below_zero
    (by omega)

/-- The identity action of `A^{11} = 1` on the convolution. -/
theorem basis_mul (X : LongJet 2) (s : Real) :
    (mul (basisJet (0 : Multiindex 2)) X).c alphaIdx s = X.c alphaIdx s := by
  rw [mul_c_of_left_single _ _ alphaIdx 0 s zero_mem
    (fun b _ hb => by rw [basisJet_c, if_neg hb]), basisJet_c, if_pos rfl,
    alpha_sub_zero, one_mul]

/-- **The off-diagonal entry, computed.**  At `alpha = z_0^3` and
`beta = z_0^2 z_1`, two *distinct* multi-indices of degree three, the actual
`phaseEikonalMatrix` of this metric and quadratic phase equals `2`. -/
theorem phaseEikonalMatrix_offDiagonal (s : Real) :
    phaseEikonalMatrix xPhase 3 s ⟨alphaIdx, mem_degreeEq.2 deg_alpha⟩
        ⟨betaIdx, mem_degreeEq.2 deg_beta⟩ = 2 := by
  show sameDegreeOp xMetric.Att xPhase.phi xPhase.phi (basisJet betaIdx)
    alphaIdx s = 2
  rw [sameDegreeOp]
  simp only [Fin.sum_univ_two]
  rw [xAtt_zero (Or.inl rfl), xAtt_zero (Or.inl rfl), xAtt_zero (Or.inr rfl),
    xAtt11]
  rw [mul_zeroJet_c, mul_zeroJet_c, mul_zeroJet_c, mul_zeroJet_c,
    mul_zeroJet_c, mul_zeroJet_c]
  rw [basis_mul, basis_mul]
  rw [mul_c_of_left_single _ _ alphaIdx gammaIdx s gamma_mem
      (fun b _ hb => dbj_support b s hb),
    mul_c_of_left_single _ _ alphaIdx oneIdx s one_mem
      (fun b _ hb => dphi_support b s hb),
    alpha_sub_gamma, alpha_sub_one, dbj_value, dphi_value]
  norm_num

/-- The entry sits genuinely off the diagonal. -/
theorem offDiagonal_indices_distinct :
    (⟨alphaIdx, mem_degreeEq.2 deg_alpha⟩ : DegreeIndex 2 3)
      ≠ ⟨betaIdx, mem_degreeEq.2 deg_beta⟩ := by
  intro h
  exact alpha_ne_beta (congrArg Subtype.val h)

/-- ... and is nonzero, so the block operator really does mix distinct
multi-indices of the same total degree. -/
theorem phaseEikonalMatrix_offDiagonal_ne_zero (s : Real) :
    phaseEikonalMatrix xPhase 3 s ⟨alphaIdx, mem_degreeEq.2 deg_alpha⟩
      ⟨betaIdx, mem_degreeEq.2 deg_beta⟩ ≠ 0 := by
  rw [phaseEikonalMatrix_offDiagonal]
  norm_num

#print axioms phaseEikonalMatrix_offDiagonal
#print axioms phaseEikonalMatrix_offDiagonal_ne_zero

/-! ## Axiom checks for the corrected degree-`r` block -/

#print axioms LiuWang2025SemilinearWaveSameDegreeMatrix.selfInteraction_vanishes
#print axioms LiuWang2025SemilinearWaveSameDegreeMatrix.sameDegreeOp_base_of_supported
#print axioms LiuWang2025SemilinearWaveSameDegreeMatrix.eikonal_block_fixed_matrix
#print axioms LiuWang2025SemilinearWaveSameDegreeMatrix.phaseEikonalMatrix_local
#print axioms LiuWang2025SemilinearWaveSameDegreeMatrix.phaseSource_stable
#print axioms LiuWang2025SemilinearWaveSameDegreeMatrix.eikonal_deg_eq_zero_of_paperBlockEquation
#print axioms LiuWang2025SemilinearWaveDegreeBlockODE.exists_c2_blockSolution
#print axioms LiuWang2025SemilinearWaveDegreeBlockODE.exists_global_blockSolution
#print axioms LiuWang2025SemilinearWaveDegreeBlockODE.exists_rowSum_bound
#print axioms LiuWang2025SemilinearWavePhaseUpdate.exists_phase_update
#print axioms LiuWang2025SemilinearWavePhaseUpdate.exists_phase_cancelling_upto
#print axioms LiuWang2025SemilinearWaveSameDegreeMatrix.sameDegreeOp_split
#print axioms LiuWang2025SemilinearWaveSameDegreeMatrix.eikonal_deg_two_riccati_form
#print axioms LiuWang2025SemilinearWaveSameDegreeMatrix.eikonal_deg_two_eq_zero_of_riccatiEquation
#print axioms LiuWang2025SemilinearWaveSameDegreeMatrix.quadraticSelfTerm_eq_zero_of_three_le
#print axioms LiuWang2025SemilinearWaveSameDegreeMatrix.quadraticSelfTerm_matrix
#print axioms LiuWang2025SemilinearWaveDegreeBlock.hasDerivAt_quadCoeff
#print axioms LiuWang2025SemilinearWavePhaseUpdate.exists_quadratic_phase_update
#print axioms LiuWang2025SemilinearWavePhaseUpdate.exists_phase_cancelling_upto_of_riccati
#print axioms LiuWang2025SemilinearWaveSameDegreeMatrix.eikonal_deg_two_eq_zero_of_blockRiccatiEquation
#print axioms LiuWang2025SemilinearWaveRiccatiODE.lipschitz_riccatiField
#print axioms LiuWang2025SemilinearWaveRiccatiODE.norm_riccatiField_le
#print axioms LiuWang2025SemilinearWaveRiccatiODE.exists_riccatiSolution

end LiuWangPhaseMatrixNonVacuity
