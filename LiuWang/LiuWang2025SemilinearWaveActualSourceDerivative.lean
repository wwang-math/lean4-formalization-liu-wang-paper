import LiuWang.LiuWang2025SemilinearWaveHigherOrderPolarization
import Mathlib.Analysis.Analytic.IteratedFDeriv

/-!
# Liu--Wang actual arbitrary-order source derivatives

The Liu--Wang higher-order recovery step differentiates the normalized source
term `V_m u^m / m!` in `m` independent boundary directions.  The preceding
polarization module verifies the permutation count algebraically.  This file
connects that count to Mathlib's actual `iteratedFDeriv` and then proves a
finite factorial-series coefficient-extraction theorem at the zero
background.

These are derivatives of the scalar source nonlinearity.  Arbitrary-order
differentiability of the nonlinear PDE solution map and the Faà di Bruno
composition with that map remain separate source-facing analytic work.
-/

noncomputable section

open scoped BigOperators

namespace LiuWang2025SemilinearWaveActualSourceDerivative

open LiuWang2025SemilinearWaveHigherOrderPolarization

/-- The bounded `m`-linear product map on the complex scalar fibre. -/
def productCMM (m : Nat) :
    Complex [×m]→L[Complex] Complex :=
  ContinuousMultilinearMap.mkPiAlgebra Complex (Fin m) Complex

@[simp] theorem productCMM_apply
    (m : Nat) (v : Fin m -> Complex) :
    productCMM m v = ∏ i, v i := by
  simp [productCMM]

@[simp] theorem productCMM_diagonal
    (m : Nat) (z : Complex) :
    productCMM m (fun _ => z) = z ^ m := by
  simp [productCMM]

/-- The permutation numerator is the value of the actual `m`-th iterated
Fréchet derivative of `u ↦ u^m`, at every base point. -/
theorem iteratedFDeriv_pow_eq_productRuleNumerator
    (m : Nat) (z : Complex) (firstVariation : Fin m -> Complex) :
    iteratedFDeriv Complex m (fun u : Complex => u ^ m) z firstVariation =
      topOrderProductRuleNumerator m firstVariation := by
  have h := ContinuousMultilinearMap.iteratedFDeriv_comp_diagonal
    (productCMM m) z firstVariation
  have hdiagonal :
      (fun u : Complex => productCMM m (fun _ => u)) =
        fun u : Complex => u ^ m := by
    funext u
    exact productCMM_diagonal m u
  rw [hdiagonal] at h
  rw [topOrderProductRuleNumerator]
  simpa only [productCMM_apply] using h

/-- Actual derivative form of the factorial cancellation: the `m`-th
derivative of `u^m`, divided by `m!`, is the product of the `m` independent
directions. -/
theorem iteratedFDeriv_pow_factorial_normalization
    (m : Nat) (z : Complex) (firstVariation : Fin m -> Complex) :
    iteratedFDeriv Complex m (fun u : Complex => u ^ m)
        z firstVariation / (Nat.factorial m : Complex) =
      ∏ i, firstVariation i := by
  rw [iteratedFDeriv_pow_eq_productRuleNumerator]
  exact topOrder_factorial_normalization m firstVariation

/-- The bounded multilinear coefficient of the normalized source monomial
`V_m u^m / m!`. -/
def normalizedTopSourceCMM
    (m : Nat) (coefficient : Complex) :
    Complex [×m]→L[Complex] Complex :=
  (coefficient / (Nat.factorial m : Complex)) • productCMM m

@[simp] theorem normalizedTopSourceCMM_apply
    (m : Nat) (coefficient : Complex) (v : Fin m -> Complex) :
    normalizedTopSourceCMM m coefficient v =
      coefficient * (∏ i, v i) / (Nat.factorial m : Complex) := by
  change (coefficient / (Nat.factorial m : Complex)) * productCMM m v = _
  rw [productCMM_apply]
  ring

/-- The normalized scalar source monomial occurring in the paper. -/
def normalizedTopSource
    (m : Nat) (coefficient u : Complex) : Complex :=
  coefficient * u ^ m / (Nat.factorial m : Complex)

@[simp] theorem normalizedTopSourceCMM_diagonal
    (m : Nat) (coefficient u : Complex) :
    normalizedTopSourceCMM m coefficient (fun _ => u) =
      normalizedTopSource m coefficient u := by
  simp [normalizedTopSource]

/-- The actual arbitrary-order source derivative used in the coefficient
equation: differentiating `V_m u^m / m!` in `m` directions produces
`V_m ∏ i, w_i`. -/
theorem iteratedFDeriv_normalizedTopSource
    (m : Nat) (coefficient z : Complex)
    (firstVariation : Fin m -> Complex) :
    iteratedFDeriv Complex m (normalizedTopSource m coefficient)
        z firstVariation =
      coefficient * ∏ i, firstVariation i := by
  have h := ContinuousMultilinearMap.iteratedFDeriv_comp_diagonal
    (normalizedTopSourceCMM m coefficient) z firstVariation
  have hdiagonal :
      (fun u : Complex =>
          normalizedTopSourceCMM m coefficient (fun _ => u)) =
        normalizedTopSource m coefficient := by
    funext u
    exact normalizedTopSourceCMM_diagonal m coefficient u
  rw [hdiagonal] at h
  rw [h]
  simp only [normalizedTopSourceCMM_apply]
  rw [← Finset.sum_div]
  rw [← Finset.mul_sum]
  change coefficient * topOrderProductRuleNumerator m firstVariation /
      (Nat.factorial m : Complex) = _
  rw [topOrderProductRuleNumerator_eq_factorial_mul]
  have hfactorial : (Nat.factorial m : Complex) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero m
  field_simp

/-- Every source monomial of degree below the differentiation order has zero
`m`-th derivative at the zero background. -/
theorem lowerOrder_iteratedFDeriv_at_zero
    {k m : Nat} (hkm : k < m) (coefficient : Complex)
    (firstVariation : Fin m -> Complex) :
    iteratedFDeriv Complex m
        (fun u : Complex => coefficient * u ^ k) 0 firstVariation = 0 := by
  rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod]
  rw [iteratedDeriv_const_mul_field]
  rw [iteratedDeriv_fun_pow_zero]
  simp [ne_of_gt hkm]

/-- The finite source expansion through order `m`, with the exact factorial
normalization used in Liu--Wang. -/
def truncatedNormalizedSource
    (m : Nat) (coefficient : Nat -> Complex) (u : Complex) : Complex :=
  ∑ k ∈ Finset.range (m + 1),
    coefficient k * u ^ k / (Nat.factorial k : Complex)

/-- The actual `m`-th derivative at zero of the truncated factorial source
expansion extracts exactly its `m`-th coefficient and the product of the
independent directions.  All lower source monomials vanish automatically. -/
theorem iteratedFDeriv_truncatedNormalizedSource_of_le
    (order derivativeOrder : Nat) (hderivativeOrder : derivativeOrder <= order)
    (coefficient : Nat -> Complex)
    (variation : Fin derivativeOrder -> Complex) :
    iteratedFDeriv Complex derivativeOrder
        (truncatedNormalizedSource order coefficient) 0 variation =
      coefficient derivativeOrder * ∏ i, variation i := by
  rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod]
  unfold truncatedNormalizedSource
  rw [iteratedDeriv_fun_sum (by
    intro k hk
    fun_prop)]
  simp only [iteratedDeriv_div_const, iteratedDeriv_const_mul_field,
    iteratedDeriv_fun_pow_zero]
  have hsum :
      (∑ x ∈ Finset.range (order + 1),
        coefficient x *
            ((if derivativeOrder = x then Nat.factorial x else 0 : Nat) : Complex) /
          (Nat.factorial x : Complex)) = coefficient derivativeOrder := by
    rw [Finset.sum_eq_single derivativeOrder]
    · have hfactorial : (Nat.factorial derivativeOrder : Complex) ≠ 0 := by
        exact_mod_cast Nat.factorial_ne_zero derivativeOrder
      simp [hfactorial]
    · intro b hb hbm
      simp [Ne.symm hbm]
    · intro hnot
      exact (hnot (by simpa using hderivativeOrder)).elim
  rw [hsum]
  ring

/-- Continuous-multilinear form of coefficient extraction at every order
inside the finite factorial source expansion. -/
theorem iteratedFDeriv_truncatedNormalizedSource_eq_smul_productCMM_of_le
    (order derivativeOrder : Nat) (hderivativeOrder : derivativeOrder <= order)
    (coefficient : Nat -> Complex) :
    iteratedFDeriv Complex derivativeOrder
        (truncatedNormalizedSource order coefficient) 0 =
      coefficient derivativeOrder • productCMM derivativeOrder := by
  apply ContinuousMultilinearMap.ext
  intro variation
  rw [iteratedFDeriv_truncatedNormalizedSource_of_le order derivativeOrder
    hderivativeOrder coefficient variation]
  change coefficient derivativeOrder * ∏ i, variation i =
    coefficient derivativeOrder * productCMM derivativeOrder variation
  rw [productCMM_apply]

/-- At a fixed derivative order inside the truncation, equality of the one
relevant Taylor coefficient gives equality of the complete multilinear
source derivatives. -/
theorem iteratedFDeriv_truncatedNormalizedSource_eq_of_coefficient_eq
    (order derivativeOrder : Nat) (hderivativeOrder : derivativeOrder <= order)
    (coefficient1 coefficient2 : Nat -> Complex)
    (hcoefficient : coefficient1 derivativeOrder = coefficient2 derivativeOrder) :
    iteratedFDeriv Complex derivativeOrder
        (truncatedNormalizedSource order coefficient1) 0 =
      iteratedFDeriv Complex derivativeOrder
        (truncatedNormalizedSource order coefficient2) 0 := by
  rw [iteratedFDeriv_truncatedNormalizedSource_eq_smul_productCMM_of_le
      order derivativeOrder hderivativeOrder coefficient1,
    iteratedFDeriv_truncatedNormalizedSource_eq_smul_productCMM_of_le
      order derivativeOrder hderivativeOrder coefficient2,
    hcoefficient]

/-- The actual `m`-th derivative at zero of the truncation through `m`
extracts its top coefficient. -/
theorem iteratedFDeriv_truncatedNormalizedSource
    (m : Nat) (coefficient : Nat -> Complex)
    (firstVariation : Fin m -> Complex) :
    iteratedFDeriv Complex m
        (truncatedNormalizedSource m coefficient) 0 firstVariation =
      coefficient m * ∏ i, firstVariation i :=
  iteratedFDeriv_truncatedNormalizedSource_of_le m m le_rfl coefficient
    firstVariation

/-- Subtracting the actual `m`-th source derivatives of two truncated
factorial expansions leaves exactly the top coefficient difference. -/
theorem iteratedFDeriv_truncatedNormalizedSource_sub
    (m : Nat) (coefficient1 coefficient2 : Nat -> Complex)
    (firstVariation : Fin m -> Complex) :
    iteratedFDeriv Complex m
          (truncatedNormalizedSource m coefficient1) 0 firstVariation -
        iteratedFDeriv Complex m
          (truncatedNormalizedSource m coefficient2) 0 firstVariation =
      (coefficient1 m - coefficient2 m) *
        ∏ i, firstVariation i := by
  rw [iteratedFDeriv_truncatedNormalizedSource,
    iteratedFDeriv_truncatedNormalizedSource]
  ring

/-- Auditable certificate linking the source's factorial convention to
actual iterated Fréchet derivatives. -/
structure Certificate (m : Nat) : Prop where
  monomialDerivative : forall z firstVariation,
    iteratedFDeriv Complex m (fun u : Complex => u ^ m)
        z firstVariation =
      topOrderProductRuleNumerator m firstVariation
  normalizedTopDerivative : forall coefficient z firstVariation,
    iteratedFDeriv Complex m (normalizedTopSource m coefficient)
        z firstVariation =
      coefficient * ∏ i, firstVariation i
  truncatedCoefficientExtraction : forall coefficient firstVariation,
    iteratedFDeriv Complex m
        (truncatedNormalizedSource m coefficient) 0 firstVariation =
      coefficient m * ∏ i, firstVariation i
  truncatedDifference : forall coefficient1 coefficient2 firstVariation,
    iteratedFDeriv Complex m
          (truncatedNormalizedSource m coefficient1) 0 firstVariation -
        iteratedFDeriv Complex m
          (truncatedNormalizedSource m coefficient2) 0 firstVariation =
      (coefficient1 m - coefficient2 m) * ∏ i, firstVariation i

/-- Canonical actual-source-derivative certificate for every order. -/
def certificate (m : Nat) : Certificate m where
  monomialDerivative := iteratedFDeriv_pow_eq_productRuleNumerator m
  normalizedTopDerivative := iteratedFDeriv_normalizedTopSource m
  truncatedCoefficientExtraction :=
    iteratedFDeriv_truncatedNormalizedSource m
  truncatedDifference :=
    iteratedFDeriv_truncatedNormalizedSource_sub m

end LiuWang2025SemilinearWaveActualSourceDerivative
