import LiuWang.LiuWang2025SemilinearWaveHigherOrderPolarization
import Mathlib.Tactic.FinCases

/-!
# Liu--Wang 2025: an explicit four-null-covector balance

Section 4.2 of Liu--Wang uses four future light-like covectors at the
interaction point and real weights whose weighted sum is zero.  The paper
refers to an earlier Lorentzian construction for this choice.  This module
checks the pointwise algebra from the smallest geometric input that is needed:
a time covector and two spacelike covectors forming a Lorentz-orthonormal
two-frame.

The four covectors are

`tau + e1`, `tau - e1`, `tau + e2`, `tau - e2`,

with weights `1, 1, -1, -1`.  Lean proves that all four are nonzero future
null covectors, that they are pairwise distinct, and that their weighted sum
is exactly zero.  Complexifying the resulting real continuous covectors
produces the balanced Frechet covectors used by the existing four-beam phase
module.  Consequently Lemma 4.1(i)--(ii), and the replicated higher-order
critical phase, are generated from this concrete witness.

This is a pointwise Lorentz-frame theorem.  The global construction of an
orthonormal frame compatible with the selected broken null geodesics, their
boundary reachability and transversality, and the Gaussian beam phases remain
the source-facing geometric inputs.
-/

noncomputable section

open scoped BigOperators

namespace LiuWang2025SemilinearWaveFourNullCovectors

open LiuWang2025SemilinearWavePhaseBalance
open LiuWang2025SemilinearWaveHigherOrderPolarization

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace Real X]

/-- A Lorentz-orthonormal time/two-space frame in one cotangent space.  The
continuous bilinear form represents the inverse Lorentz metric on covectors.
The two spacelike directions are the dimension-`n >= 2` content used by the
paper's four-beam interaction. -/
structure LorentzOrthonormalTwoFrame (X : Type*)
    [NormedAddCommGroup X] [NormedSpace Real X] where
  inverseMetric :
    (X →L[Real] Real) →L[Real] (X →L[Real] Real) →L[Real] Real
  symmetric : forall x y, inverseMetric x y = inverseMetric y x
  time : X →L[Real] Real
  spatialOne : X →L[Real] Real
  spatialTwo : X →L[Real] Real
  time_time : inverseMetric time time = -1
  time_spatialOne : inverseMetric time spatialOne = 0
  time_spatialTwo : inverseMetric time spatialTwo = 0
  spatialOne_spatialOne : inverseMetric spatialOne spatialOne = 1
  spatialOne_spatialTwo : inverseMetric spatialOne spatialTwo = 0
  spatialTwo_spatialTwo : inverseMetric spatialTwo spatialTwo = 1

namespace LorentzOrthonormalTwoFrame

@[simp] theorem spatialOne_time (frame : LorentzOrthonormalTwoFrame X) :
    frame.inverseMetric frame.spatialOne frame.time = 0 := by
  rw [frame.symmetric, frame.time_spatialOne]

@[simp] theorem spatialTwo_time (frame : LorentzOrthonormalTwoFrame X) :
    frame.inverseMetric frame.spatialTwo frame.time = 0 := by
  rw [frame.symmetric, frame.time_spatialTwo]

@[simp] theorem spatialTwo_spatialOne
    (frame : LorentzOrthonormalTwoFrame X) :
    frame.inverseMetric frame.spatialTwo frame.spatialOne = 0 := by
  rw [frame.symmetric, frame.spatialOne_spatialTwo]

/-- The source-compatible four future null covectors in the selected local
Lorentz frame. -/
def covector (frame : LorentzOrthonormalTwoFrame X) :
    Fin 4 -> X →L[Real] Real :=
  ![frame.time + frame.spatialOne,
    frame.time - frame.spatialOne,
    frame.time + frame.spatialTwo,
    frame.time - frame.spatialTwo]

/-- Signed beam weights giving exact phase cancellation. -/
def weight (_frame : LorentzOrthonormalTwoFrame X) : Fin 4 -> Real :=
  ![1, 1, -1, -1]

/-- Every beam weight in the explicit balance is nonzero. -/
@[simp] theorem weight_ne_zero
    (frame : LorentzOrthonormalTwoFrame X) (j : Fin 4) :
    frame.weight j ≠ 0 := by
  fin_cases j <;> norm_num [weight]

/-- Future orientation relative to the selected time covector. -/
def FutureDirected (frame : LorentzOrthonormalTwoFrame X)
    (xi : X →L[Real] Real) : Prop :=
  frame.inverseMetric frame.time xi < 0

/-- Nullity for the inverse Lorentz form. -/
def Null (frame : LorentzOrthonormalTwoFrame X)
    (xi : X →L[Real] Real) : Prop :=
  frame.inverseMetric xi xi = 0

@[simp] theorem time_pair_covector
    (frame : LorentzOrthonormalTwoFrame X) (j : Fin 4) :
    frame.inverseMetric frame.time (frame.covector j) = -1 := by
  fin_cases j <;>
    simp [covector, frame.time_time, frame.time_spatialOne,
      frame.time_spatialTwo]

@[simp] theorem covector_pair_self
    (frame : LorentzOrthonormalTwoFrame X) (j : Fin 4) :
    frame.inverseMetric (frame.covector j) (frame.covector j) = 0 := by
  fin_cases j <;>
    simp [covector, frame.time_time, frame.time_spatialOne,
      frame.time_spatialTwo, frame.spatialOne_spatialOne,
      frame.spatialTwo_spatialTwo]

theorem covector_futureDirected
    (frame : LorentzOrthonormalTwoFrame X) (j : Fin 4) :
    frame.FutureDirected (frame.covector j) := by
  rw [FutureDirected, frame.time_pair_covector]
  norm_num

theorem covector_null
    (frame : LorentzOrthonormalTwoFrame X) (j : Fin 4) :
    frame.Null (frame.covector j) :=
  frame.covector_pair_self j

theorem covector_ne_zero
    (frame : LorentzOrthonormalTwoFrame X) (j : Fin 4) :
    frame.covector j ≠ 0 := by
  intro hzero
  have hfuture := frame.covector_futureDirected j
  simp [FutureDirected, hzero] at hfuture

/-- The first spacelike coordinate separates the first pair of null
covectors. -/
@[simp] theorem spatialOne_pair_covector
    (frame : LorentzOrthonormalTwoFrame X) (j : Fin 4) :
    frame.inverseMetric frame.spatialOne (frame.covector j) =
      ![(1 : Real), -1, 0, 0] j := by
  fin_cases j <;>
    simp [covector, frame.spatialOne_spatialOne,
      frame.spatialOne_spatialTwo]

/-- The second spacelike coordinate separates the second pair of null
covectors. -/
@[simp] theorem spatialTwo_pair_covector
    (frame : LorentzOrthonormalTwoFrame X) (j : Fin 4) :
    frame.inverseMetric frame.spatialTwo (frame.covector j) =
      ![(0 : Real), 0, 1, -1] j := by
  fin_cases j <;>
    simp [covector, frame.spatialTwo_spatialTwo]

/-- The four null directions are genuinely distinct. -/
theorem covector_injective (frame : LorentzOrthonormalTwoFrame X) :
    Function.Injective frame.covector := by
  intro i j hij
  have hOne := congrArg
    (fun xi => frame.inverseMetric frame.spatialOne xi) hij
  have hTwo := congrArg
    (fun xi => frame.inverseMetric frame.spatialTwo xi) hij
  change frame.inverseMetric frame.spatialOne (frame.covector i) =
    frame.inverseMetric frame.spatialOne (frame.covector j) at hOne
  change frame.inverseMetric frame.spatialTwo (frame.covector i) =
    frame.inverseMetric frame.spatialTwo (frame.covector j) at hTwo
  fin_cases i <;> fin_cases j
  all_goals try rfl
  all_goals try
    (exfalso
     norm_num [covector, frame.spatialOne_spatialOne,
       frame.spatialOne_spatialTwo] at hOne)
  all_goals
    norm_num [covector, frame.spatialTwo_spatialTwo] at hTwo

/-- Exact source balance `sum_j kappa_j theta_j = 0`. -/
theorem weighted_covector_sum_eq_zero
    (frame : LorentzOrthonormalTwoFrame X) :
    (∑ j, frame.weight j • frame.covector j) = 0 := by
  rw [Fin.sum_univ_four]
  simp [weight, covector]
  abel

/-- Canonical complexification of each real phase covector. -/
def phaseCovector (frame : LorentzOrthonormalTwoFrame X) (j : Fin 4) :
    X →L[Real] Complex :=
  Complex.ofRealCLM.comp (frame.covector j)

/-- The real-covector balance induces exactly the complexified balance
consumed by `FourBeamPhaseBalanceData`. -/
theorem weightedPhaseCovector_eq_zero
    (frame : LorentzOrthonormalTwoFrame X) :
    weightedCovector frame.weight frame.phaseCovector = 0 := by
  ext x
  rw [weightedCovector, Fin.sum_univ_four]
  simp [weight, phaseCovector, covector]
  ring

/-- Local phase jets whose differentials are the four explicitly generated
null covectors.  Constructing these phases along the paper's broken null
geodesics remains geometric work. -/
structure FourBeamPhaseJetData (frame : LorentzOrthonormalTwoFrame X) where
  point : X
  phase : Fin 4 -> X -> Complex
  phase_zero : forall j, phase j point = 0
  phase_hasFDerivAt : forall j,
    HasFDerivAt (phase j) (frame.phaseCovector j) point

namespace FourBeamPhaseJetData

/-- Feed the explicit null-covector construction into the paper's checked
phase-balance API. -/
def toFourBeamPhaseBalanceData
    {frame : LorentzOrthonormalTwoFrame X}
    (data : FourBeamPhaseJetData frame) :
    FourBeamPhaseBalanceData X where
  point := data.point
  phase := data.phase
  weight := frame.weight
  covector := frame.phaseCovector
  phase_zero := data.phase_zero
  phase_hasFDerivAt := data.phase_hasFDerivAt
  weightedCovectorBalance := frame.weightedPhaseCovector_eq_zero

/-- Every higher Taylor order reuses the same explicit balanced frame by
splitting the fourth weight among `m-2` repeated beams. -/
def toHigherOrderPhaseReplicationData
    {frame : LorentzOrthonormalTwoFrame X}
    (data : FourBeamPhaseJetData frame)
    (order : Nat) (horder : 3 ≤ order) :
    HigherOrderPhaseReplicationData X where
  order := order
  order_ge_three := horder
  base := data.toFourBeamPhaseBalanceData

/-- One auditable certificate joins pointwise Lorentz geometry, the cubic
critical phase, and the arbitrary-order replicated phase. -/
structure Certificate
    {frame : LorentzOrthonormalTwoFrame X}
    (data : FourBeamPhaseJetData frame) : Prop where
  futureNull : forall j,
    frame.FutureDirected (frame.covector j) /\
      frame.Null (frame.covector j) /\ frame.covector j ≠ 0
  weightsNonzero : forall j, frame.weight j ≠ 0
  pairwiseDistinct : Function.Injective frame.covector
  vectorBalance : (∑ j, frame.weight j • frame.covector j) = 0
  phaseCovectorBalance :
    weightedCovector frame.weight frame.phaseCovector = 0
  phaseBalance : FourBeamPhaseBalanceData.Certificate
    data.toFourBeamPhaseBalanceData
  replicatedPhase : forall order (horder : 3 ≤ order)
      (amplitude : Fin 4 -> Complex),
    HigherOrderPhaseReplicationData.ReplicationCertificate
      (data.toHigherOrderPhaseReplicationData order horder) amplitude

def certificate
    {frame : LorentzOrthonormalTwoFrame X}
    (data : FourBeamPhaseJetData frame) : Certificate data where
  futureNull := fun j =>
    ⟨frame.covector_futureDirected j, frame.covector_null j,
      frame.covector_ne_zero j⟩
  weightsNonzero := frame.weight_ne_zero
  pairwiseDistinct := frame.covector_injective
  vectorBalance := frame.weighted_covector_sum_eq_zero
  phaseCovectorBalance := frame.weightedPhaseCovector_eq_zero
  phaseBalance := data.toFourBeamPhaseBalanceData.certificate
  replicatedPhase := fun order horder amplitude =>
    (data.toHigherOrderPhaseReplicationData order horder).replicationCertificate
      amplitude

end FourBeamPhaseJetData

end LorentzOrthonormalTwoFrame

end LiuWang2025SemilinearWaveFourNullCovectors
