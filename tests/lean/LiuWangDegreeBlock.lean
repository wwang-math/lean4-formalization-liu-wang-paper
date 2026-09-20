import LiuWang.LiuWang2025SemilinearWaveDegreeBlockODE
import LiuWang.LiuWang2025SemilinearWaveSameDegreeMatrix

/-! Focused regression file for the homogeneous degree blocks, the block ODE,
and the same-degree operator of the actual variable-metric eikonal. -/

open scoped BigOperators
open Set
open LiuWang2025SemilinearWaveTransverseJet
open LiuWang2025SemilinearWaveLongitudinalJet
open LiuWang2025SemilinearWaveLongitudinalJet.LongJet
open LiuWang2025SemilinearWaveJetOperators
open LiuWang2025SemilinearWaveDegreeBlock
open LiuWang2025SemilinearWaveDegreeBlockODE
open LiuWang2025SemilinearWaveMetricJetPhaseHierarchy
open LiuWang2025SemilinearWaveSameDegreeMatrix

-- The block layer.
#check @LiuWang2025SemilinearWaveDegreeBlock.degreeEq
#check @LiuWang2025SemilinearWaveDegreeBlock.mem_degreeEq
#check @LiuWang2025SemilinearWaveDegreeBlock.DegreeIndex
#check @LiuWang2025SemilinearWaveDegreeBlock.DegreeBlock
#check @LiuWang2025SemilinearWaveDegreeBlock.block_ext
#check @LiuWang2025SemilinearWaveDegreeBlock.restrictBlock_ofBlock
#check @LiuWang2025SemilinearWaveDegreeBlock.insertBlock
#check @LiuWang2025SemilinearWaveDegreeBlock.insertBlock_c_of_deg_ne
#check @LiuWang2025SemilinearWaveDegreeBlock.insertBlock_c_index
#check @LiuWang2025SemilinearWaveDegreeBlock.quadCoeff
#check @LiuWang2025SemilinearWaveDegreeBlock.quadCoeff_diag
#check @LiuWang2025SemilinearWaveDegreeBlock.quadCoeff_offDiag

-- The block ODE.
#check @LiuWang2025SemilinearWaveDegreeBlockODE.blockField
#check @LiuWang2025SemilinearWaveDegreeBlockODE.continuous_blockField
#check @LiuWang2025SemilinearWaveDegreeBlockODE.lipschitz_blockField
#check @LiuWang2025SemilinearWaveDegreeBlockODE.exists_blockSolution
#check @LiuWang2025SemilinearWaveDegreeBlockODE.blockField_equation

-- The same-degree operator of the actual eikonal.
#check @LiuWang2025SemilinearWaveMetricJetPhaseHierarchy.sameDegreeOp
#check @LiuWang2025SemilinearWaveMetricJetPhaseHierarchy.eikonal_block_decomposition
#check @LiuWang2025SemilinearWaveMetricJetPhaseHierarchy.sameDegreeOp_add
#check @LiuWang2025SemilinearWaveMetricJetPhaseHierarchy.sameDegreeOp_smul
#check @LiuWang2025SemilinearWaveMetricJetPhaseHierarchy.sameDegreeOp_congr

/-! ## A degree with more than one multi-index

In two transverse variables the degree-two block has three distinct
multi-indices, so the same-degree system is genuinely a system. -/

/-- `z_0^2`. -/
def idx20 : Multiindex 2 := Pi.single 0 2
/-- `z_0 z_1`. -/
def idx11 : Multiindex 2 := Pi.single 0 1 + Pi.single 1 1
/-- `z_1^2`. -/
def idx02 : Multiindex 2 := Pi.single 1 2

example : deg idx20 = 2 := by simp [deg, idx20, Pi.single_apply]
example : deg idx02 = 2 := by simp [deg, idx02, Pi.single_apply]
example : deg idx11 = 2 := by
  show (idx11 0 + (idx11 1 + 0)) = 2
  simp [idx11]

example : idx20 ∈ degreeEq 2 2 := by
  rw [mem_degreeEq]
  simp [deg, idx20, Pi.single_apply]
example : idx02 ∈ degreeEq 2 2 := by
  rw [mem_degreeEq]
  simp [deg, idx02, Pi.single_apply]

/-- The two indices really are different, so the block has dimension at least
two and a diagonal treatment is not available. -/
example : idx20 ≠ idx02 := by decide

/-- The degree-two block of two transverse variables has exactly three
multi-indices. -/
example : (degreeEq 2 2).card = 3 := by decide

/-! ## Riccati-to-monomial normalization -/

example (M : Fin 2 -> Fin 2 -> Complex) :
    quadCoeff M ((Pi.single 0 1 : Multiindex 2) + Pi.single 0 1) = M 0 0 :=
  quadCoeff_diag M 0

/-- The off-diagonal monomial collects both matrix entries. -/
example (M : Fin 2 -> Fin 2 -> Complex) :
    quadCoeff M ((Pi.single 0 1 : Multiindex 2) + Pi.single 1 1)
      = M 0 1 + M 1 0 :=
  quadCoeff_offDiag M (by decide)

/-! ## A genuinely non-diagonal, non-constant block ODE

`K s a b = s` for *every* pair, so the matrix is non-diagonal at every
parameter and depends on the parameter. -/

/-- The all-ones matrix scaled by the geodesic parameter. -/
def demoK (s : Real) (_a _b : DegreeIndex 2 2) : Complex := ((s : Real) : Complex)

/-- A non-zero source. -/
def demoSource (_s : Real) (_a : DegreeIndex 2 2) : Complex := 1

theorem demoK_continuous (a b : DegreeIndex 2 2) :
    Continuous fun s => demoK s a b := by
  simpa [demoK] using Complex.continuous_ofReal

theorem demoSource_continuous (a : DegreeIndex 2 2) :
    Continuous fun s => demoSource s a := continuous_const

/-- The field genuinely mixes coordinates: at index `a` it reads every
coordinate of the state, with a nonzero coefficient whenever `s /= 0`. -/
example (s : Real) (x : DegreeBlock 2 2) (a : DegreeIndex 2 2) :
    blockField demoK demoSource s x a
      = ((2 : Complex))⁻¹ * (1 - ∑ b, ((s : Real) : Complex) * x b) := rfl

/-- The row sums are bounded on the unit interval. -/
theorem demoK_rowSum (s : Real) (hs : s ∈ Icc (0 : Real) 1)
    (a : DegreeIndex 2 2) :
    ∑ b, ‖demoK s a b‖ ≤ (Fintype.card (DegreeIndex 2 2) : Real) := by
  have hterm : ∀ b ∈ (Finset.univ : Finset (DegreeIndex 2 2)),
      ‖demoK s a b‖ ≤ 1 := by
    intro b _
    rw [demoK, Complex.norm_real, Real.norm_of_nonneg hs.1]
    exact hs.2
  calc (∑ b, ‖demoK s a b‖) ≤ ∑ _b : DegreeIndex 2 2, (1 : Real) :=
        Finset.sum_le_sum hterm
    _ = (Fintype.card (DegreeIndex 2 2) : Real) := by
        simp

/-- **A non-constant, non-diagonal block ODE is solved.**  The path, its
continuity, its initial value and its derivative equation are all produced by
the compact-interval construction. -/
example (t0 : Icc (0 : Real) 1) (x0 : DegreeBlock 2 2) :
    ∃ c : Real -> DegreeBlock 2 2,
      c t0 = x0 ∧ Continuous c ∧
        ∀ t ∈ Icc (0 : Real) 1,
          HasDerivWithinAt c (blockField demoK demoSource t (c t))
            (Icc (0 : Real) 1) t :=
  exists_blockSolution demoK demoSource demoK_continuous demoSource_continuous
    (by positivity) demoK_rowSum t0 x0

/-- The block equation the constructed path satisfies, coordinatewise. -/
example (s : Real) (x : DegreeBlock 2 2) (a : DegreeIndex 2 2) :
    2 * blockField demoK demoSource s x a + ∑ b, demoK s a b * x b
      = demoSource s a :=
  blockField_equation demoK demoSource s x a

-- The matrix representation of the same-degree operator.
#check @LiuWang2025SemilinearWaveMetricJetPhaseHierarchy.sameDegreeOp_sum
#check @LiuWang2025SemilinearWaveMetricJetPhaseHierarchy.basisJet
#check @LiuWang2025SemilinearWaveSameDegreeMatrix.sumSingle_c
#check @LiuWang2025SemilinearWaveSameDegreeMatrix.eikonalMatrix
#check @LiuWang2025SemilinearWaveSameDegreeMatrix.sameDegreeOp_matrix
#check @LiuWang2025SemilinearWaveSameDegreeMatrix.eikonal_block_matrix_form
#check @LiuWang2025SemilinearWaveSameDegreeMatrix.eikonal_deg_eq_zero_of_blockEquation

/-- The basis jet really is the standard basis vector of the block. -/
example (a0 b : Multiindex 2) (s : Real) :
    (basisJet a0).c b s = if b = a0 then 1 else 0 := basisJet_c a0 b s

/-- A perturbation supported in one degree is recovered from its block
components. -/
example (delta : LongJet 2) (s : Real)
    (hsupp : ∀ b, deg b ≠ 2 -> delta.c b s = 0) (b : Multiindex 2) :
    (sumJet (fun beta : DegreeIndex 2 2 =>
        singleJet beta.1 (delta.c beta.1) (delta.dc beta.1)
          (delta.hasDeriv beta.1))).c b s = delta.c b s :=
  sumSingle_c delta 2 s hsupp b

/-- **The block form of the actual eikonal difference** in the degree-two block
of two transverse variables, which has three multi-indices: the whole block
moves together through the computed matrix. -/
example (G : FermiMetricJet 2) (P P' : SourcePhaseJet G) (s : Real)
    (alpha : DegreeIndex 2 2)
    (hphi : ∀ b, deg b < 2 -> P.phi.c b s = P'.phi.c b s)
    (hdphi : ∀ b, deg b < 2 -> P.dphi.c b s = P'.dphi.c b s)
    (hoff : ∀ b, 2 < deg b -> P.phi.c b s = P'.phi.c b s) :
    jetEikonal G.Ass G.Bs G.Att P.phi P.dphi alpha.1 s
        - jetEikonal G.Ass G.Bs G.Att P'.phi P'.dphi alpha.1 s
      = 2 * (P.dphi.c alpha.1 s - P'.dphi.c alpha.1 s)
        + ∑ beta : DegreeIndex 2 2,
            eikonalMatrix G.Att P.phi P'.phi 2 s alpha beta
              * (P.phi.c beta.1 s - P'.phi.c beta.1 s) :=
  eikonal_block_matrix_form P P' 2 (by norm_num) s alpha hphi hdphi hoff

#print axioms LiuWang2025SemilinearWaveMetricJetPhaseHierarchy.sameDegreeOp_sum
#print axioms LiuWang2025SemilinearWaveSameDegreeMatrix.sumSingle_c
#print axioms LiuWang2025SemilinearWaveSameDegreeMatrix.sameDegreeOp_matrix
#print axioms LiuWang2025SemilinearWaveSameDegreeMatrix.eikonal_block_matrix_form
#print axioms LiuWang2025SemilinearWaveSameDegreeMatrix.eikonal_deg_eq_zero_of_blockEquation
#print axioms LiuWang2025SemilinearWaveDegreeBlock.mem_degreeEq
#print axioms LiuWang2025SemilinearWaveDegreeBlock.insertBlock
#print axioms LiuWang2025SemilinearWaveDegreeBlock.insertBlock_c_of_deg_ne
#print axioms LiuWang2025SemilinearWaveDegreeBlock.quadCoeff_diag
#print axioms LiuWang2025SemilinearWaveDegreeBlock.quadCoeff_offDiag
#print axioms LiuWang2025SemilinearWaveDegreeBlockODE.continuous_blockField
#print axioms LiuWang2025SemilinearWaveDegreeBlockODE.lipschitz_blockField
#print axioms LiuWang2025SemilinearWaveDegreeBlockODE.exists_blockSolution
#print axioms LiuWang2025SemilinearWaveDegreeBlockODE.blockField_equation
#print axioms LiuWang2025SemilinearWaveMetricJetPhaseHierarchy.eikonal_block_decomposition
#print axioms LiuWang2025SemilinearWaveMetricJetPhaseHierarchy.sameDegreeOp_add
#print axioms LiuWang2025SemilinearWaveMetricJetPhaseHierarchy.sameDegreeOp_smul
#print axioms LiuWang2025SemilinearWaveMetricJetPhaseHierarchy.sameDegreeOp_congr
