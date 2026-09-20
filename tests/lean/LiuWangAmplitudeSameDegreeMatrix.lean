import LiuWang.LiuWang2025SemilinearWaveAmplitudeSameDegreeMatrix

/-!
# Focused tests for the same-degree amplitude transport matrix

Exercises the block identity, the coefficient-2 extraction of the longitudinal
derivative, the cancellation theorem, and -- the point of the exercise -- an
explicit *nondiagonal* entry coupling two distinct monomials of the same total
degree.
-/

noncomputable section

open scoped BigOperators
open Set

open LiuWang2025SemilinearWaveTransverseJet
open LiuWang2025SemilinearWaveLongitudinalJet
open LiuWang2025SemilinearWaveLongitudinalJet.LongJet
open LiuWang2025SemilinearWaveJetOperators
open LiuWang2025SemilinearWaveDegreeBlock
open LiuWang2025SemilinearWaveMetricJetPhaseHierarchy
open LiuWang2025SemilinearWaveAmplitudeJetOperators
open LiuWang2025SemilinearWaveAmplitudeJetOperators.WaveJetData
open LiuWang2025SemilinearWaveAmplitudeSameDegreeMatrix

namespace LiuWangAmplitudeSameDegreeMatrixTests

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

/-! ## The wave-operator data for the example -/

def xWave : WaveJetData 2 where
  G := xMetric
  betaS := zeroJet 2
  betaT := fun _ => zeroJet 2

theorem mul_zero_right (u X : LongJet 2) (a : Multiindex 2) (s : Real)
    (hX : ∀ b, X.c b s = 0) : (mul u X).c a s = 0 :=
  mul_c_vanish (p := 0) (q := deg a + 1) vanish_below_zero
    (fun b _ => hX b) (by omega)

/-- **A genuinely nondiagonal entry of the amplitude transport matrix.**  At
`alpha = z_0^3` and `beta = z_0^2 z_1`, two distinct multi-indices of degree
three, the matrix entry is `2`.  A scalar per-index ODE cannot represent this. -/
theorem transportMatrix_offDiagonal (s : Real) :
    transportMatrix xWave xPhase 3 s ⟨alphaIdx, mem_degreeEq.2 deg_alpha⟩
        ⟨betaIdx, mem_degreeEq.2 deg_beta⟩ = 2 := by
  show 2 * ((∑ i, (mul (xMetric.Bs i)
        (mul xPhase.dphi (transverseDeriv i (basisJet betaIdx)))).c alphaIdx s)
      + ∑ i, ∑ j, (mul (xMetric.Att i j)
          (mul (transverseDeriv i xPhase.phi)
            (transverseDeriv j (basisJet betaIdx)))).c alphaIdx s)
    - convRaw (basisJet betaIdx)
        (fun b t => xWave.jetBox (ofSourcePhase xPhase) b t) alphaIdx s = 2
  have hdphiZero : ∀ b, xPhase.dphi.c b s = 0 := fun b => rfl
  have hBterm : ∀ i : Fin 2, (mul (xMetric.Bs i)
      (mul xPhase.dphi (transverseDeriv i (basisJet betaIdx)))).c alphaIdx s
      = 0 := by
    intro i
    refine mul_zero_right _ _ _ s fun b => ?_
    exact mul_c_vanish (p := deg b + 1) (q := 0) (fun e _ => hdphiZero e)
      vanish_below_zero (by omega)
  have hconv : convRaw (basisJet betaIdx)
      (fun b t => xWave.jetBox (ofSourcePhase xPhase) b t) alphaIdx s = 0 := by
    refine Finset.sum_eq_zero fun b hb => ?_
    rw [basisJet_c, if_neg, zero_mul]
    intro hcon
    have h1 := mem_below.1 hb 1
    rw [hcon] at h1
    simp [alphaIdx, betaIdx] at h1
  have hAtt : ∀ i j : Fin 2, (mul (xMetric.Att i j)
      (mul (transverseDeriv i xPhase.phi)
        (transverseDeriv j (basisJet betaIdx)))).c alphaIdx s
      = if i = 1 ∧ j = 1 then 1 else 0 := by
    intro i j
    by_cases hi : i = 0
    · rw [xAtt_zero (Or.inl hi), if_neg (by simp [hi]), mul_zeroJet_c]
    · by_cases hj : j = 0
      · rw [xAtt_zero (Or.inr hj), if_neg (by simp [hj]), mul_zeroJet_c]
      · have hi1 : i = 1 := by omega
        have hj1 : j = 1 := by omega
        rw [hi1, hj1, if_pos ⟨rfl, rfl⟩, xAtt11, basis_mul,
          mul_c_of_left_single _ _ alphaIdx oneIdx s one_mem
            (fun b _ hb => dphi_support b s hb),
          alpha_sub_one, dphi_value, dbj_value, one_mul]
  rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hBterm i,
    Finset.sum_const_zero,
    Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) =>
      Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) => hAtt i j,
    hconv]
  simp only [Fin.sum_univ_two]
  norm_num

/-- The two indices are genuinely different. -/
theorem offDiagonal_distinct :
    (⟨alphaIdx, mem_degreeEq.2 deg_alpha⟩ : DegreeIndex 2 3)
      ≠ ⟨betaIdx, mem_degreeEq.2 deg_beta⟩ := fun h =>
  alpha_ne_beta (congrArg Subtype.val h)

/-! ## Abstract endpoints -/

/-- The block identity, with the coefficient `2` on the longitudinal
derivative. -/
example {d : Nat} (W : WaveJetData d) (P : SourcePhaseJet W.G)
    (u u' : LongJet2 d) (r : Nat) (s : Real) (alpha : DegreeIndex d r)
    (hjet : ∀ b, deg b ≠ r -> u.jet.c b s = u'.jet.c b s)
    (hdjet : ∀ b, deg b ≠ r -> u.djet.c b s = u'.djet.c b s) :
    W.jetTransport P u alpha.1 s - W.jetTransport P u' alpha.1 s
      = 2 * (u.djet.c alpha.1 s - u'.djet.c alpha.1 s)
        + ∑ beta : DegreeIndex d r,
            transportMatrix W P r s alpha beta
              * (u.jet.c beta.1 s - u'.jet.c beta.1 s) :=
  jetTransport_block_matrix_form W P u u' r s alpha hjet hdjet

#print axioms LiuWang2025SemilinearWaveAmplitudeSameDegreeMatrix.sameDegreeTransport_matrix
#print axioms LiuWang2025SemilinearWaveAmplitudeSameDegreeMatrix.jetTransport_block_matrix_form
#print axioms LiuWang2025SemilinearWaveAmplitudeSameDegreeMatrix.jetTransport_eq_zero_of_blockEquation
#print axioms LiuWang2025SemilinearWaveAmplitudeSameDegreeMatrix.continuous_transportMatrix
#print axioms LiuWang2025SemilinearWaveAmplitudeSameDegreeMatrix.exists_transportMatrix_rowSum_bound
#print axioms LiuWangAmplitudeSameDegreeMatrixTests.transportMatrix_offDiagonal

end LiuWangAmplitudeSameDegreeMatrixTests
