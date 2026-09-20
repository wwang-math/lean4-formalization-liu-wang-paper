import LiuWang.LiuWang2025SemilinearWaveLinearization
import LiuWang.LiuWang2025SemilinearWavePhaseBalance
import Mathlib.Data.Fintype.Perm
import Mathlib.Tactic.FieldSimp

/-!
# Liu--Wang arbitrary-order zero-background polarization

The higher-order step after equation (4.5) of Liu--Wang differentiates
`V_m u^m / m!` once in each of `m` independent boundary parameters.  At the
zero background, every surviving product-rule term assigns one derivative to
each of the `m` factors.  Such assignments are permutations, so there are
exactly `m!` identical products.  This module checks that factorial
cancellation for every order and records the cancellation of the lower-order
remainder in the two-candidate difference equation.

The analytic differentiability of the nonlinear solution map remains a
separate source-facing hypothesis.  The result here verifies the exact
combinatorial coefficient that this differentiation must produce.
-/

noncomputable section

open scoped BigOperators

namespace LiuWang2025SemilinearWaveHigherOrderPolarization

open LiuWang2025SemilinearWavePhaseBalance

/-- The zero-background product-rule numerator for the mixed `m`-th
derivative of `u^m`: one term for every assignment of the `m` derivatives to
the `m` factors that survives at `u=0`. -/
def topOrderProductRuleNumerator
    (m : Nat) (firstVariation : Fin m -> Complex) : Complex :=
  ∑ permutation : Equiv.Perm (Fin m),
    ∏ i : Fin m, firstVariation (permutation i)

/-- Every surviving term is the same product, and the set of surviving
assignments has cardinality `m!`. -/
theorem topOrderProductRuleNumerator_eq_factorial_mul
    (m : Nat) (firstVariation : Fin m -> Complex) :
    topOrderProductRuleNumerator m firstVariation =
      (Nat.factorial m : Complex) * ∏ i, firstVariation i := by
  unfold topOrderProductRuleNumerator
  calc
    (∑ permutation : Equiv.Perm (Fin m),
        ∏ i : Fin m, firstVariation (permutation i)) =
        ∑ _permutation : Equiv.Perm (Fin m),
          ∏ i : Fin m, firstVariation i := by
      apply Finset.sum_congr rfl
      intro permutation _
      exact Equiv.prod_comp permutation firstVariation
    _ = (Fintype.card (Equiv.Perm (Fin m)) : Complex) *
        ∏ i : Fin m, firstVariation i := by
      simp
    _ = (Nat.factorial m : Complex) *
        ∏ i : Fin m, firstVariation i := by
      rw [Fintype.card_perm, Fintype.card_fin]

/-- The source normalization `1/m!` removes exactly the product-rule
multiplicity for every order, including `m=3`. -/
theorem topOrder_factorial_normalization
    (m : Nat) (firstVariation : Fin m -> Complex) :
    topOrderProductRuleNumerator m firstVariation /
        (Nat.factorial m : Complex) =
      ∏ i, firstVariation i := by
  rw [topOrderProductRuleNumerator_eq_factorial_mul]
  have hfactorial : (Nat.factorial m : Complex) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero m
  field_simp

/-- Coefficient-bearing arbitrary-order form of the term displayed in
equation (4.5). -/
theorem topCoefficient_mixed_response
    (m : Nat) (coefficient : Complex)
    (firstVariation : Fin m -> Complex) :
    coefficient *
        (topOrderProductRuleNumerator m firstVariation /
          (Nat.factorial m : Complex)) =
      coefficient * ∏ i, firstVariation i := by
  rw [topOrder_factorial_normalization]

/-- Algebraic source in the `m`-th linearized equation: the already-known
lower-order polynomial remainder plus the new top coefficient. -/
def higherOrderLinearizedSource
    (m : Nat) (lowerOrderRemainder topCoefficient : Complex)
    (firstVariation : Fin m -> Complex) : Complex :=
  lowerOrderRemainder +
    topCoefficient * ∏ i, firstVariation i

/-- Once the induction hypothesis identifies the lower-order remainder, the
difference of the two `m`-th linearized equations contains only
`(V_m^(1)-V_m^(2)) prod_i w_i`. -/
theorem higherOrderLinearizedSource_sub
    (m : Nat) {remainder1 remainder2 : Complex}
    (topCoefficient1 topCoefficient2 : Complex)
    (firstVariation : Fin m -> Complex)
    (hremainder : remainder1 = remainder2) :
    higherOrderLinearizedSource m remainder1 topCoefficient1 firstVariation -
        higherOrderLinearizedSource m remainder2 topCoefficient2 firstVariation =
      (topCoefficient1 - topCoefficient2) *
        ∏ i, firstVariation i := by
  simp [higherOrderLinearizedSource, hremainder]
  ring

/-- Auditable arbitrary-order certificate for the induction step. -/
structure Certificate (m : Nat) : Prop where
  factorialMultiplicity : forall firstVariation : Fin m -> Complex,
    topOrderProductRuleNumerator m firstVariation =
      (Nat.factorial m : Complex) * ∏ i, firstVariation i
  factorialNormalization : forall firstVariation : Fin m -> Complex,
    topOrderProductRuleNumerator m firstVariation /
        (Nat.factorial m : Complex) =
      ∏ i, firstVariation i
  remainderCancellation :
    forall (remainder1 remainder2 topCoefficient1 topCoefficient2 : Complex)
      (firstVariation : Fin m -> Complex),
      remainder1 = remainder2 ->
      higherOrderLinearizedSource m remainder1 topCoefficient1 firstVariation -
          higherOrderLinearizedSource m remainder2 topCoefficient2 firstVariation =
        (topCoefficient1 - topCoefficient2) *
          ∏ i, firstVariation i

/-- Canonical arbitrary-order source certificate. -/
def certificate (m : Nat) : Certificate m where
  factorialMultiplicity := topOrderProductRuleNumerator_eq_factorial_mul m
  factorialNormalization := topOrder_factorial_normalization m
  remainderCancellation := fun _remainder1 _remainder2 topCoefficient1
    topCoefficient2 firstVariation hremainder =>
      higherOrderLinearizedSource_sub m topCoefficient1 topCoefficient2
        firstVariation hremainder

/-! ## Replication of the fourth beam in the higher-order recovery step -/

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace Real X]

/-- Splitting the fourth beam weight equally among `m-2` identical copies,
as in the source's higher-order construction. -/
def replicatedFourthWeight
    (m : Nat) (weight : Fin 4 -> Real) : Real :=
  weight 3 / (m - 2 : Nat)

/-- The phase of the three distinguished beams and `m-2` copies of the
fourth beam.  Altogether this is the backward beam and the `m` forward beams
in the coefficient-`V_m` interaction. -/
def replicatedWeightedPhase
    (m : Nat) (weight : Fin 4 -> Real)
    (phase : Fin 4 -> X -> Complex) : X -> Complex :=
  fun x =>
    weight 0 • phase 0 x +
      weight 1 • phase 1 x +
      weight 2 • phase 2 x +
      ∑ _copy : Fin (m - 2),
        replicatedFourthWeight m weight • phase 3 x

/-- `m-2` copies of weight `kappa_3/(m-2)` recombine to `kappa_3`. -/
theorem sum_replicatedFourthWeight_smul
    (m : Nat) (hm : 3 ≤ m) (kappa : Real) (z : Complex) :
    (∑ _copy : Fin (m - 2),
        (kappa / (m - 2 : Nat)) • z) =
      kappa • z := by
  have hpositive : 0 < m - 2 := by omega
  have hnonzeroNat : m - 2 ≠ 0 := Nat.ne_of_gt hpositive
  have hnonzeroReal : ((m - 2 : Nat) : Real) ≠ 0 := by
    exact_mod_cast hnonzeroNat
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  have hscalar :
      ((m - 2 : Nat) : Real) * (kappa / (m - 2 : Nat)) = kappa := by
    field_simp
  calc
    (m - 2) • ((kappa / (m - 2 : Nat)) • z) =
        ((m - 2 : Nat) : Real) •
          ((kappa / (m - 2 : Nat)) • z) :=
      (Nat.cast_smul_eq_nsmul Real (m - 2)
        ((kappa / (m - 2 : Nat)) • z)).symm
    _ = (((m - 2 : Nat) : Real) * (kappa / (m - 2 : Nat))) • z := by
      simp only [Complex.real_smul]
      push_cast
      ring
    _ = kappa • z := by rw [hscalar]

omit [NormedAddCommGroup X] [NormedSpace Real X] in
/-- The higher-order replicated phase is exactly the original four-beam
phase; the split introduces no phase error. -/
theorem replicatedWeightedPhase_eq_weightedPhase
    (m : Nat) (hm : 3 ≤ m) (weight : Fin 4 -> Real)
    (phase : Fin 4 -> X -> Complex) :
    replicatedWeightedPhase m weight phase =
      weightedPhase weight phase := by
  funext x
  rw [weightedPhase, Fin.sum_univ_four]
  unfold replicatedWeightedPhase replicatedFourthWeight
  rw [sum_replicatedFourthWeight_smul m hm]

/-- Source-facing packet for the higher-order reuse of the four-beam
critical phase. -/
structure HigherOrderPhaseReplicationData (X : Type*)
    [NormedAddCommGroup X] [NormedSpace Real X] where
  order : Nat
  order_ge_three : 3 ≤ order
  base : FourBeamPhaseBalanceData X

namespace HigherOrderPhaseReplicationData

/-- The replicated higher-order phase still vanishes at the interaction
point. -/
theorem replicatedPhase_at_eq_zero
    (data : HigherOrderPhaseReplicationData X) :
    replicatedWeightedPhase data.order data.base.weight data.base.phase
        data.base.point = 0 := by
  rw [replicatedWeightedPhase_eq_weightedPhase data.order
    data.order_ge_three]
  exact data.base.weightedPhase_at_eq_zero

/-- The replicated higher-order phase retains the zero differential needed
for stationary localization. -/
theorem replicatedPhase_hasFDerivAt_zero
    (data : HigherOrderPhaseReplicationData X) :
    HasFDerivAt
      (replicatedWeightedPhase data.order data.base.weight data.base.phase)
      (0 : X →L[Real] Complex) data.base.point := by
  rw [replicatedWeightedPhase_eq_weightedPhase data.order
    data.order_ge_three]
  exact data.base.weightedPhase_hasFDerivAt_zero

/-- Product of the three distinguished amplitudes and the `m-2` repeated
fourth amplitudes. -/
def replicatedAmplitudeProduct
    (data : HigherOrderPhaseReplicationData X)
    (amplitude : Fin 4 -> Complex) : Complex :=
  amplitude 0 * amplitude 1 * amplitude 2 *
    ∏ _copy : Fin (data.order - 2), amplitude 3

/-- The repeated-beam product is exactly the power displayed in the source's
higher-order coefficient endpoint. -/
theorem replicatedAmplitudeProduct_eq_pow
    (data : HigherOrderPhaseReplicationData X)
    (amplitude : Fin 4 -> Complex) :
    data.replicatedAmplitudeProduct amplitude =
      amplitude 0 * amplitude 1 * amplitude 2 *
        amplitude 3 ^ (data.order - 2) := by
  simp [replicatedAmplitudeProduct]

/-- Auditable phase-and-amplitude certificate for every order `m >= 3`. -/
structure ReplicationCertificate
    (data : HigherOrderPhaseReplicationData X)
    (amplitude : Fin 4 -> Complex) : Prop where
  phaseEqualsFourBeam :
    replicatedWeightedPhase data.order data.base.weight data.base.phase =
      weightedPhase data.base.weight data.base.phase
  phaseValueZero :
    replicatedWeightedPhase data.order data.base.weight data.base.phase
      data.base.point = 0
  phaseHasZeroDifferential :
    HasFDerivAt
      (replicatedWeightedPhase data.order data.base.weight data.base.phase)
      (0 : X →L[Real] Complex) data.base.point
  amplitudePower :
    data.replicatedAmplitudeProduct amplitude =
      amplitude 0 * amplitude 1 * amplitude 2 *
        amplitude 3 ^ (data.order - 2)

/-- Canonical higher-order replicated-beam certificate. -/
def replicationCertificate
    (data : HigherOrderPhaseReplicationData X)
    (amplitude : Fin 4 -> Complex) :
    ReplicationCertificate data amplitude where
  phaseEqualsFourBeam :=
    replicatedWeightedPhase_eq_weightedPhase data.order
      data.order_ge_three data.base.weight data.base.phase
  phaseValueZero := data.replicatedPhase_at_eq_zero
  phaseHasZeroDifferential := data.replicatedPhase_hasFDerivAt_zero
  amplitudePower := data.replicatedAmplitudeProduct_eq_pow amplitude

end HigherOrderPhaseReplicationData

end LiuWang2025SemilinearWaveHigherOrderPolarization
