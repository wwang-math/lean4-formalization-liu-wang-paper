import LiuWang.LiuWang2025SemilinearWaveActualSourceDerivative
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.FaaDiBruno

/-!
# Liu--Wang solution-map Faà di Bruno decomposition

The arbitrary-order Liu--Wang coefficient equation differentiates the
semilinear source after inserting the nonlinear wave solution.  This file
upgrades the verified scalar source derivative to that composition step.

For a genuinely `C^m` point-evaluation solution map `u`, Mathlib's Banach-
space Faà di Bruno theorem writes the `m`-th derivative of

`x ↦ sum_{k=0}^m V_k u(x)^k / k!`

as a finite sum over ordered partitions of the `m` boundary directions.  The
atomic partition consists of `m` singleton blocks.  At the zero background,
its contribution is exactly

`V_m * product_i D u(0)[h_i]`.

Every other partition is collected into an explicit, inspectable lower-order
composition remainder.  Thus the paper's top coefficient is no longer joined
to an arbitrary remainder variable: the remainder is generated from the
actual derivatives of the source and solution map.  Concrete semilinear-wave
well-posedness, `C^m` regularity in the source's Lorentzian graph spaces, and
the passage from point evaluation to the spacetime residual remain
source-facing analytic work.
-/

noncomputable section

open scoped BigOperators

namespace LiuWang2025SemilinearWaveSolutionMapFaaDiBruno

open LiuWang2025SemilinearWaveActualSourceDerivative

variable {Parameter : Type*}
variable [NormedAddCommGroup Parameter] [NormedSpace Complex Parameter]

/-! ## Ordered-partition facts needed by coefficient induction -/

/-- The block sizes of an ordered partition of `Fin n` sum to `n`. -/
theorem orderedFinpartition_sum_partSize_eq
    {n : Nat} (partition : OrderedFinpartition n) :
    (∑ i, partition.partSize i) = n := by
  have h := Fintype.card_congr partition.equivSigma
  simpa [Fintype.card_sigma] using h

/-- An ordered partition of `Fin n` with `n` nonempty blocks has singleton
blocks. -/
theorem orderedFinpartition_partSize_eq_one_of_length_eq
    {n : Nat} (partition : OrderedFinpartition n)
    (hlength : partition.length = n) :
    forall i, partition.partSize i = 1 := by
  intro i
  have hsum := orderedFinpartition_sum_partSize_eq partition
  have hsum' : (∑ j, partition.partSize j) = partition.length :=
    hsum.trans hlength.symm
  have herase := Finset.sum_erase_add Finset.univ partition.partSize
    (Finset.mem_univ i)
  have hge :
      (∑ _j ∈
          (Finset.univ : Finset (Fin partition.length)).erase i, (1 : Nat)) <=
        ∑ j ∈ (Finset.univ : Finset (Fin partition.length)).erase i,
          partition.partSize j := by
    exact Finset.sum_le_sum fun j hj => partition.partSize_pos j
  have hpositive := partition.partSize_pos i
  have hsplit :
      (∑ j ∈ (Finset.univ : Finset (Fin partition.length)).erase i,
          partition.partSize j) + partition.partSize i = partition.length :=
    herase.trans hsum'
  have hlengthPositive : 0 < partition.length :=
    lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
  have hlengthOne : 1 <= partition.length := hlengthPositive
  have hlengthSub : partition.length - 1 + 1 = partition.length :=
    Nat.sub_add_cancel hlengthOne
  simp only [Finset.sum_const, Finset.card_erase_of_mem,
    Finset.mem_univ, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one] at hge
  have hsumLe :
      partition.length - 1 + partition.partSize i <= partition.length := by
    calc
      partition.length - 1 + partition.partSize i <=
          (∑ j ∈ (Finset.univ : Finset (Fin partition.length)).erase i,
            partition.partSize j) + partition.partSize i :=
        Nat.add_le_add_right hge (partition.partSize i)
      _ = partition.length := hsplit
  have hpartLe : partition.partSize i <= 1 := by
    apply Nat.le_of_add_le_add_left
    rw [hlengthSub]
    exact hsumLe
  exact Nat.le_antisymm hpartLe hpositive

/-- The atomic singleton partition is the unique ordered partition with the
maximum possible number of blocks. -/
theorem orderedFinpartition_eq_atomic_of_length_eq
    {n : Nat} (partition : OrderedFinpartition n)
    (hlength : partition.length = n) :
    partition = OrderedFinpartition.atomic n := by
  have hpart :
      partition.partSize ≍ (OrderedFinpartition.atomic n).partSize := by
    apply Function.hfunext
    · exact congrArg Fin hlength
    · intro i j hij
      simp only [OrderedFinpartition.atomic_partSize]
      exact heq_of_eq
        (orderedFinpartition_partSize_eq_one_of_length_eq partition hlength i)
  let maximum : Fin n -> Fin n := fun i =>
    partition.emb (Fin.cast hlength.symm i)
      ⟨partition.partSize (Fin.cast hlength.symm i) - 1,
        Nat.sub_one_lt_of_lt
          (partition.partSize_pos (Fin.cast hlength.symm i))⟩
  have hmaximum : StrictMono maximum := by
    exact partition.parts_strictMono.comp (Fin.cast_strictMono hlength.symm)
  have hmaximum_id : forall i, maximum i = i := by
    intro i
    exact le_antisymm hmaximum.apply_le hmaximum.le_apply
  apply OrderedFinpartition.ext hlength hpart
  apply Function.hfunext
  · exact congrArg Fin hlength
  · intro i j hij
    apply Function.hfunext
    · have hi :=
        orderedFinpartition_partSize_eq_one_of_length_eq partition hlength i
      simpa only [OrderedFinpartition.atomic_partSize] using congrArg Fin hi
    · intro a b hab
      have ha : a =
          ⟨partition.partSize i - 1,
            Nat.sub_one_lt_of_lt (partition.partSize_pos i)⟩ := by
        apply Fin.ext
        have habValue := Fin.val_eq_val_of_heq hab
        have hi :=
          orderedFinpartition_partSize_eq_one_of_length_eq partition hlength i
        omega
      have hij' : Fin.cast hlength i = j := by
        apply Fin.ext
        have hijValue : i.val = j.val := Fin.val_eq_val_of_heq hij
        exact hijValue
      have hvalue : partition.emb i a = Fin.cast hlength i := by
        rw [ha]
        have h := hmaximum_id (Fin.cast hlength i)
        simpa [maximum] using h
      rw [hvalue, hij']
      exact HEq.rfl

/-- Every non-atomic ordered partition has strictly fewer than `n` blocks.
This is the combinatorial reason its outer source derivative depends only on
a previously recovered coefficient. -/
theorem orderedFinpartition_length_lt_of_ne_atomic
    {n : Nat} (partition : OrderedFinpartition n)
    (hne : partition ≠ OrderedFinpartition.atomic n) :
    partition.length < n := by
  apply lt_of_le_of_ne partition.length_le
  intro hlength
  exact hne (orderedFinpartition_eq_atomic_of_length_eq partition hlength)

/-- If an ordered partition has at least two blocks, every block is smaller
than the full derivative order. -/
theorem orderedFinpartition_partSize_lt_of_two_le_length
    {n : Nat} (partition : OrderedFinpartition n)
    (hlength : 2 <= partition.length) (i : Fin partition.length) :
    partition.partSize i < n := by
  classical
  letI : Nontrivial (Fin partition.length) :=
    Fin.nontrivial_iff_two_le.mpr hlength
  obtain ⟨j, hji⟩ := exists_ne i
  have hjmem :
      j ∈ (Finset.univ : Finset (Fin partition.length)).erase i := by
    exact Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩
  have hsumPositive :
      0 < ∑ k ∈ (Finset.univ : Finset (Fin partition.length)).erase i,
        partition.partSize k := by
    apply Finset.sum_pos'
    · intro k hk
      exact Nat.zero_le _
    · exact ⟨j, hjmem, partition.partSize_pos j⟩
  have hsum := orderedFinpartition_sum_partSize_eq partition
  have herase := Finset.sum_erase_add Finset.univ partition.partSize
    (Finset.mem_univ i)
  have hsplit :
      (∑ k ∈ (Finset.univ : Finset (Fin partition.length)).erase i,
        partition.partSize k) + partition.partSize i = n :=
    herase.trans hsum
  omega

/-- The first solution variation in one boundary direction, written using
the actual first iterated Fréchet derivative. -/
def firstSolutionVariation
    (solutionMap : Parameter -> Complex) (base direction : Parameter) : Complex :=
  iteratedFDeriv Complex 1 solutionMap base (fun _ => direction)

/-- The factorial-normalized semilinear source after insertion of a nonlinear
point-evaluation solution map. -/
def composedTruncatedSource
    (order : Nat) (coefficient : Nat -> Complex)
    (solutionMap : Parameter -> Complex) : Parameter -> Complex :=
  truncatedNormalizedSource order coefficient ∘ solutionMap

/-- One exact Faà di Bruno partition term in the `order`-th derivative of the
composed semilinear source. -/
def sourceCompositionPartitionTerm
    (order : Nat) (coefficient : Nat -> Complex)
    (solutionMap : Parameter -> Complex) (base : Parameter)
    (partition : OrderedFinpartition order) :
    Parameter [×order]→L[Complex] Complex :=
  (ftaylorSeries Complex (truncatedNormalizedSource order coefficient)
      (solutionMap base)).compAlongOrderedFinpartition
    (ftaylorSeries Complex solutionMap base) partition

/-- The lower-order composition remainder is the finite Faà di Bruno sum over
all partitions except the atomic partition into singletons. -/
def sourceCompositionRemainder
    (order : Nat) (coefficient : Nat -> Complex)
    (solutionMap : Parameter -> Complex) (base : Parameter) :
    Parameter [×order]→L[Complex] Complex :=
  ∑ partition ∈
      (Finset.univ : Finset (OrderedFinpartition order)).erase
        (OrderedFinpartition.atomic order),
    sourceCompositionPartitionTerm order coefficient solutionMap base partition

/-- The truncated factorial source is smooth to every finite order. -/
theorem truncatedNormalizedSource_contDiff
    (order differentiabilityOrder : Nat) (coefficient : Nat -> Complex) :
    ContDiff Complex differentiabilityOrder
      (truncatedNormalizedSource order coefficient) := by
  unfold truncatedNormalizedSource
  fun_prop

/-- The actual derivative of the composed source is the full finite Faà di
Bruno partition sum. -/
theorem iteratedFDeriv_composedTruncatedSource_eq_partitionSum
    (order : Nat) (coefficient : Nat -> Complex)
    (solutionMap : Parameter -> Complex) (base : Parameter)
    (hsolution : ContDiffAt Complex order solutionMap base) :
    iteratedFDeriv Complex order
        (composedTruncatedSource order coefficient solutionMap) base =
      ∑ partition : OrderedFinpartition order,
        sourceCompositionPartitionTerm order coefficient solutionMap base
          partition := by
  rw [composedTruncatedSource]
  rw [iteratedFDeriv_comp
    (truncatedNormalizedSource_contDiff order order coefficient).contDiffAt
    hsolution le_rfl]
  rfl

/-- The atomic partition term is the top source coefficient times the product
of the actual first solution variations. -/
theorem atomicPartitionTerm_eq_topCoefficientProduct
    (order : Nat) (coefficient : Nat -> Complex)
    (solutionMap : Parameter -> Complex) (base : Parameter)
    (hbase : solutionMap base = 0)
    (direction : Fin order -> Parameter) :
    sourceCompositionPartitionTerm order coefficient solutionMap base
        (OrderedFinpartition.atomic order) direction =
      coefficient order *
        ∏ i, firstSolutionVariation solutionMap base (direction i) := by
  unfold sourceCompositionPartitionTerm firstSolutionVariation ftaylorSeries
  simp only [FormalMultilinearSeries.compAlongOrderedFinpartition_apply,
    OrderedFinpartition.atomic_length,
    OrderedFinpartition.applyOrderedFinpartition_apply,
    OrderedFinpartition.atomic_partSize,
    OrderedFinpartition.atomic_emb, iteratedFDeriv_one_apply]
  rw [hbase]
  have h := iteratedFDeriv_truncatedNormalizedSource order coefficient
    (fun i =>
      iteratedFDeriv Complex 1 solutionMap base
        (direction ∘ fun _ => i))
  convert h using 1
  all_goals simp

/-- Exact continuous-multilinear decomposition into the atomic partition and
the generated non-atomic Faà di Bruno remainder. -/
theorem iteratedFDeriv_composedTruncatedSource_eq_atomic_add_remainder
    (order : Nat) (coefficient : Nat -> Complex)
    (solutionMap : Parameter -> Complex) (base : Parameter)
    (hsolution : ContDiffAt Complex order solutionMap base) :
    iteratedFDeriv Complex order
        (composedTruncatedSource order coefficient solutionMap) base =
      sourceCompositionPartitionTerm order coefficient solutionMap base
          (OrderedFinpartition.atomic order) +
        sourceCompositionRemainder order coefficient solutionMap base := by
  rw [iteratedFDeriv_composedTruncatedSource_eq_partitionSum
    order coefficient solutionMap base hsolution]
  unfold sourceCompositionRemainder
  rw [(Finset.sum_erase_add Finset.univ
      (fun partition =>
        sourceCompositionPartitionTerm order coefficient solutionMap base
          partition)
      (Finset.mem_univ (OrderedFinpartition.atomic order))).symm]
  ac_rfl

/-- Evaluated on `m` boundary directions, the exact Faà di Bruno formula is
the paper's new coefficient term plus the generated lower-order remainder. -/
theorem iteratedFDeriv_composedTruncatedSource_eq_top_add_remainder
    (order : Nat) (coefficient : Nat -> Complex)
    (solutionMap : Parameter -> Complex) (base : Parameter)
    (hsolution : ContDiffAt Complex order solutionMap base)
    (hbase : solutionMap base = 0)
    (direction : Fin order -> Parameter) :
    iteratedFDeriv Complex order
        (composedTruncatedSource order coefficient solutionMap) base direction =
      coefficient order *
          ∏ i, firstSolutionVariation solutionMap base (direction i) +
        sourceCompositionRemainder order coefficient solutionMap base direction := by
  rw [iteratedFDeriv_composedTruncatedSource_eq_atomic_add_remainder
    order coefficient solutionMap base hsolution]
  rw [ContinuousMultilinearMap.add_apply]
  rw [atomicPartitionTerm_eq_topCoefficientProduct
    order coefficient solutionMap base hbase direction]

/-! ## Generated lower-order remainder agreement -/

/-- Exact induction data used to compare two nonlinear wave solution maps.
Coefficients below cubic order vanish, coefficients already recovered below
`order` agree, and all positive solution jets below `order` agree at the
zero boundary background. -/
structure LowerOrderJetAgreement
    (order : Nat) (coefficient1 coefficient2 : Nat -> Complex)
    (solutionMap1 solutionMap2 : Parameter -> Complex)
    (base : Parameter) : Prop where
  coefficient1_vanishes_below_cubic : forall k, k < 3 -> coefficient1 k = 0
  coefficient2_vanishes_below_cubic : forall k, k < 3 -> coefficient2 k = 0
  lowerCoefficientAgreement : forall k, 3 <= k -> k < order ->
    coefficient1 k = coefficient2 k
  lowerSolutionJetAgreement : forall derivativeOrder,
    1 <= derivativeOrder -> derivativeOrder < order ->
    iteratedFDeriv Complex derivativeOrder solutionMap1 base =
      iteratedFDeriv Complex derivativeOrder solutionMap2 base

namespace LowerOrderJetAgreement

/-- A partition term vanishes whenever its outer source derivative vanishes;
no agreement of the inner solution derivatives is needed. -/
theorem sourceCompositionPartitionTerm_eq_zero_of_outerDerivative_eq_zero
    (order : Nat) (coefficient : Nat -> Complex)
    (solutionMap : Parameter -> Complex) (base : Parameter)
    (partition : OrderedFinpartition order)
    (houter :
      iteratedFDeriv Complex partition.length
          (truncatedNormalizedSource order coefficient) (solutionMap base) = 0) :
    sourceCompositionPartitionTerm order coefficient solutionMap base partition = 0 := by
  unfold sourceCompositionPartitionTerm ftaylorSeries
  unfold FormalMultilinearSeries.compAlongOrderedFinpartition
  change partition.compAlongOrderedFinpartition
      (iteratedFDeriv Complex partition.length
        (truncatedNormalizedSource order coefficient) (solutionMap base))
      (fun block => iteratedFDeriv Complex (partition.partSize block)
        solutionMap base) = 0
  rw [houter]
  apply ContinuousMultilinearMap.ext
  intro direction
  simp [OrderedFinpartition.compAlongOrderFinpartition_apply]

/-- If the relevant outer source derivative and all blockwise solution
derivatives agree, then the corresponding Faà di Bruno partition terms
agree. -/
theorem sourceCompositionPartitionTerm_eq_of_jets_eq
    (order : Nat) (coefficient1 coefficient2 : Nat -> Complex)
    (solutionMap1 solutionMap2 : Parameter -> Complex)
    (base : Parameter) (partition : OrderedFinpartition order)
    (hbase1 : solutionMap1 base = 0)
    (hbase2 : solutionMap2 base = 0)
    (houter :
      iteratedFDeriv Complex partition.length
          (truncatedNormalizedSource order coefficient1) 0 =
        iteratedFDeriv Complex partition.length
          (truncatedNormalizedSource order coefficient2) 0)
    (hinner : forall block,
      iteratedFDeriv Complex (partition.partSize block) solutionMap1 base =
        iteratedFDeriv Complex (partition.partSize block) solutionMap2 base) :
    sourceCompositionPartitionTerm order coefficient1 solutionMap1 base partition =
      sourceCompositionPartitionTerm order coefficient2 solutionMap2 base partition := by
  unfold sourceCompositionPartitionTerm ftaylorSeries
  rw [hbase1, hbase2]
  unfold FormalMultilinearSeries.compAlongOrderedFinpartition
  change partition.compAlongOrderedFinpartition
      (iteratedFDeriv Complex partition.length
        (truncatedNormalizedSource order coefficient1) 0)
      (fun block => iteratedFDeriv Complex (partition.partSize block)
        solutionMap1 base) =
    partition.compAlongOrderedFinpartition
      (iteratedFDeriv Complex partition.length
        (truncatedNormalizedSource order coefficient2) 0)
      (fun block => iteratedFDeriv Complex (partition.partSize block)
        solutionMap2 base)
  rw [houter]
  congr 1
  funext block
  exact hinner block

/-- Every non-atomic partition term agrees from the lower-order induction
data.  Small outer derivatives vanish because the nonlinearity starts at
cubic order; all remaining outer and inner derivatives are strictly below
`order`. -/
theorem nonAtomicPartitionTerm_eq
    {order : Nat} {coefficient1 coefficient2 : Nat -> Complex}
    {solutionMap1 solutionMap2 : Parameter -> Complex}
    {base : Parameter}
    (agreement : LowerOrderJetAgreement order coefficient1 coefficient2
      solutionMap1 solutionMap2 base)
    (hbase1 : solutionMap1 base = 0)
    (hbase2 : solutionMap2 base = 0)
    (partition : OrderedFinpartition order)
    (hne : partition ≠ OrderedFinpartition.atomic order) :
    sourceCompositionPartitionTerm order coefficient1 solutionMap1 base partition =
      sourceCompositionPartitionTerm order coefficient2 solutionMap2 base partition := by
  have hlengthLt : partition.length < order :=
    orderedFinpartition_length_lt_of_ne_atomic partition hne
  by_cases hsmall : partition.length < 3
  · have houter1 :
        iteratedFDeriv Complex partition.length
            (truncatedNormalizedSource order coefficient1) 0 = 0 := by
      rw [iteratedFDeriv_truncatedNormalizedSource_eq_smul_productCMM_of_le
        order partition.length partition.length_le coefficient1]
      rw [agreement.coefficient1_vanishes_below_cubic partition.length hsmall]
      simp
    have houter2 :
        iteratedFDeriv Complex partition.length
            (truncatedNormalizedSource order coefficient2) 0 = 0 := by
      rw [iteratedFDeriv_truncatedNormalizedSource_eq_smul_productCMM_of_le
        order partition.length partition.length_le coefficient2]
      rw [agreement.coefficient2_vanishes_below_cubic partition.length hsmall]
      simp
    have hterm1 :=
      sourceCompositionPartitionTerm_eq_zero_of_outerDerivative_eq_zero
        order coefficient1 solutionMap1 base partition
        (by simpa [hbase1] using houter1)
    have hterm2 :=
      sourceCompositionPartitionTerm_eq_zero_of_outerDerivative_eq_zero
        order coefficient2 solutionMap2 base partition
        (by simpa [hbase2] using houter2)
    rw [hterm1, hterm2]
  · have hthree : 3 <= partition.length := Nat.le_of_not_gt hsmall
    have houter :
        iteratedFDeriv Complex partition.length
            (truncatedNormalizedSource order coefficient1) 0 =
          iteratedFDeriv Complex partition.length
            (truncatedNormalizedSource order coefficient2) 0 :=
      iteratedFDeriv_truncatedNormalizedSource_eq_of_coefficient_eq
        order partition.length partition.length_le coefficient1 coefficient2
        (agreement.lowerCoefficientAgreement partition.length hthree hlengthLt)
    apply sourceCompositionPartitionTerm_eq_of_jets_eq
      order coefficient1 coefficient2 solutionMap1 solutionMap2 base partition
      hbase1 hbase2 houter
    intro block
    exact agreement.lowerSolutionJetAgreement (partition.partSize block)
      (partition.partSize_pos block)
      (orderedFinpartition_partSize_lt_of_two_le_length partition
        (le_trans (by decide) hthree) block)

/-- The generated non-atomic Faà di Bruno remainders of the two candidate
models agree under the lower-order coefficient and solution-jet induction
hypotheses. -/
theorem sourceCompositionRemainder_eq
    {order : Nat} {coefficient1 coefficient2 : Nat -> Complex}
    {solutionMap1 solutionMap2 : Parameter -> Complex}
    {base : Parameter}
    (agreement : LowerOrderJetAgreement order coefficient1 coefficient2
      solutionMap1 solutionMap2 base)
    (hbase1 : solutionMap1 base = 0)
    (hbase2 : solutionMap2 base = 0) :
    sourceCompositionRemainder order coefficient1 solutionMap1 base =
      sourceCompositionRemainder order coefficient2 solutionMap2 base := by
  unfold sourceCompositionRemainder
  apply Finset.sum_congr rfl
  intro partition hpartition
  apply agreement.nonAtomicPartitionTerm_eq hbase1 hbase2 partition
  exact (Finset.mem_erase.mp hpartition).1

/-- The actual first solution variations agree as a consequence of the
lower-jet agreement packet at order one. -/
theorem firstSolutionVariation_eq
    {order : Nat} {coefficient1 coefficient2 : Nat -> Complex}
    {solutionMap1 solutionMap2 : Parameter -> Complex}
    {base : Parameter}
    (agreement : LowerOrderJetAgreement order coefficient1 coefficient2
      solutionMap1 solutionMap2 base)
    (horder : 3 <= order) (direction : Parameter) :
    firstSolutionVariation solutionMap1 base direction =
      firstSolutionVariation solutionMap2 base direction := by
  unfold firstSolutionVariation
  rw [agreement.lowerSolutionJetAgreement 1 (by omega) (by omega)]

/-- Actual higher-order coefficient isolation for two locally `C^m`
solution maps at the base datum.  Faà di Bruno generates both remainders, lower-order induction
proves those remainders equal, and subtraction leaves exactly the paper's
`(V_m^1-V_m^2) product_i w_i` source. -/
theorem iteratedFDeriv_composedTruncatedSource_sub_eq_coefficientDifference
    {order : Nat} {coefficient1 coefficient2 : Nat -> Complex}
    {solutionMap1 solutionMap2 : Parameter -> Complex}
    {base : Parameter}
    (agreement : LowerOrderJetAgreement order coefficient1 coefficient2
      solutionMap1 solutionMap2 base)
    (horder : 3 <= order)
    (hsolution1 : ContDiffAt Complex order solutionMap1 base)
    (hsolution2 : ContDiffAt Complex order solutionMap2 base)
    (hbase1 : solutionMap1 base = 0)
    (hbase2 : solutionMap2 base = 0)
    (direction : Fin order -> Parameter) :
    iteratedFDeriv Complex order
          (composedTruncatedSource order coefficient1 solutionMap1) base direction -
        iteratedFDeriv Complex order
          (composedTruncatedSource order coefficient2 solutionMap2) base direction =
      (coefficient1 order - coefficient2 order) *
        ∏ i, firstSolutionVariation solutionMap1 base (direction i) := by
  rw [iteratedFDeriv_composedTruncatedSource_eq_top_add_remainder
      order coefficient1 solutionMap1 base hsolution1 hbase1 direction,
    iteratedFDeriv_composedTruncatedSource_eq_top_add_remainder
      order coefficient2 solutionMap2 base hsolution2 hbase2 direction]
  have hremainder := agreement.sourceCompositionRemainder_eq hbase1 hbase2
  have hproduct :
      (∏ i, firstSolutionVariation solutionMap2 base (direction i)) =
        ∏ i, firstSolutionVariation solutionMap1 base (direction i) := by
    apply Finset.prod_congr rfl
    intro i hi
    exact (agreement.firstSolutionVariation_eq horder (direction i)).symm
  rw [hremainder, hproduct]
  ring

/-- Auditable certificate for the solution-map Faà di Bruno interface used
by the Liu--Wang coefficient induction. -/
structure Certificate
    (order : Nat) (coefficient1 coefficient2 : Nat -> Complex)
    (solutionMap1 solutionMap2 : Parameter -> Complex)
    (base : Parameter)
    (agreement : LowerOrderJetAgreement order coefficient1 coefficient2
      solutionMap1 solutionMap2 base)
    (horder : 3 <= order)
    (hsolution1 : ContDiffAt Complex order solutionMap1 base)
    (hsolution2 : ContDiffAt Complex order solutionMap2 base)
    (hbase1 : solutionMap1 base = 0)
    (hbase2 : solutionMap2 base = 0) : Prop where
  partitionFormula1 :
    iteratedFDeriv Complex order
        (composedTruncatedSource order coefficient1 solutionMap1) base =
      ∑ partition : OrderedFinpartition order,
        sourceCompositionPartitionTerm order coefficient1 solutionMap1 base
          partition
  partitionFormula2 :
    iteratedFDeriv Complex order
        (composedTruncatedSource order coefficient2 solutionMap2) base =
      ∑ partition : OrderedFinpartition order,
        sourceCompositionPartitionTerm order coefficient2 solutionMap2 base
          partition
  remainderAgreement :
    sourceCompositionRemainder order coefficient1 solutionMap1 base =
      sourceCompositionRemainder order coefficient2 solutionMap2 base
  coefficientIsolation : forall direction,
    iteratedFDeriv Complex order
          (composedTruncatedSource order coefficient1 solutionMap1) base direction -
        iteratedFDeriv Complex order
          (composedTruncatedSource order coefficient2 solutionMap2) base direction =
      (coefficient1 order - coefficient2 order) *
        ∏ i, firstSolutionVariation solutionMap1 base (direction i)

/-- The full solution-map certificate is generated from the named analytic
inputs; its partition expansion, remainder agreement, and coefficient
isolation are derived conclusions. -/
def certificate
    (order : Nat) (coefficient1 coefficient2 : Nat -> Complex)
    (solutionMap1 solutionMap2 : Parameter -> Complex)
    (base : Parameter)
    (agreement : LowerOrderJetAgreement order coefficient1 coefficient2
      solutionMap1 solutionMap2 base)
    (horder : 3 <= order)
    (hsolution1 : ContDiffAt Complex order solutionMap1 base)
    (hsolution2 : ContDiffAt Complex order solutionMap2 base)
    (hbase1 : solutionMap1 base = 0)
    (hbase2 : solutionMap2 base = 0) :
    Certificate order coefficient1 coefficient2 solutionMap1 solutionMap2 base
      agreement horder hsolution1 hsolution2 hbase1 hbase2 where
  partitionFormula1 :=
    iteratedFDeriv_composedTruncatedSource_eq_partitionSum
      order coefficient1 solutionMap1 base hsolution1
  partitionFormula2 :=
    iteratedFDeriv_composedTruncatedSource_eq_partitionSum
      order coefficient2 solutionMap2 base hsolution2
  remainderAgreement := agreement.sourceCompositionRemainder_eq hbase1 hbase2
  coefficientIsolation :=
    agreement.iteratedFDeriv_composedTruncatedSource_sub_eq_coefficientDifference
      horder hsolution1 hsolution2 hbase1 hbase2

end LowerOrderJetAgreement

end LiuWang2025SemilinearWaveSolutionMapFaaDiBruno
