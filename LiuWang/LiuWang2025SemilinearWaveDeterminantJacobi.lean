import LiuWang.LiuWang2025SemilinearWaveRiccatiExistence
import Mathlib.Analysis.Calculus.FDeriv.ContinuousAlternatingMap
import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.LinearAlgebra.Complex.Module

/-!
# Liu--Wang 2025: Jacobi formula for the Gaussian-beam matrix flow

This module closes the determinant step in the leading-amplitude calculation.
For a differentiable path of invertible complex matrices, it proves the
Jacobi identity

`(det Y)' = trace (Y' Y⁻¹) det Y`.

It then applies the identity to the Hamiltonian system in the Liu--Wang beam
construction.  Since `Y' = C Z` and `H = Z Y⁻¹`, the generated path obeys

`(det Y)' = trace (C H) det Y`.

Thus the determinant equation consumed by the branch-free amplitude invariant
is derived from the verified Riccati flow rather than supplied as a separate
paper-facing hypothesis.
-/

noncomputable section

open scoped BigOperators Matrix.Norms.L2Operator
open Equiv Matrix

namespace LiuWang2025SemilinearWaveDeterminantJacobi

open LiuWang2025SemilinearWaveRiccatiExistence
open LiuWang2025SemilinearWaveRiccatiFlow

variable {n : Type*} [Fintype n] [decN : DecidableEq n]

/-! ## Determinant as a continuous alternating map -/

/-- Leibniz's formula gives the product bound needed to bundle the complex
determinant as a continuous alternating map in its rows. -/
theorem detRowAlternating_norm_le
    (M : n -> n -> Complex) :
    ‖(Matrix.detRowAlternating : (n -> Complex) [⋀^n]→ₗ[Complex] Complex) M‖ ≤
      (Nat.factorial (Fintype.card n) : Real) * ∏ i, ‖M i‖ := by
  rw [show (Matrix.detRowAlternating :
      (n -> Complex) [⋀^n]→ₗ[Complex] Complex) M = Matrix.det M from rfl,
    Matrix.det_apply]
  calc
    ‖∑ sigma : Perm n, Perm.sign sigma • ∏ i, M (sigma i) i‖ ≤
        ∑ sigma : Perm n, ‖Perm.sign sigma • ∏ i, M (sigma i) i‖ :=
      norm_sum_le _ _
    _ = ∑ sigma : Perm n, ∏ i, ‖M (sigma i) i‖ := by simp
    _ ≤ ∑ sigma : Perm n, ∏ i, ‖M (sigma i)‖ := by
      apply Finset.sum_le_sum
      intro sigma _
      apply Finset.prod_le_prod
      · intro i _
        exact norm_nonneg _
      · intro i _
        exact norm_le_pi_norm (M (sigma i)) i
    _ = ∑ _sigma : Perm n, ∏ i, ‖M i‖ := by
      apply Finset.sum_congr rfl
      intro sigma _
      exact Equiv.prod_comp sigma (fun i => ‖M i‖)
    _ = (Nat.factorial (Fintype.card n) : Real) * ∏ i, ‖M i‖ := by
      simp [Fintype.card_perm, nsmul_eq_mul]

/-- The determinant, bundled as a continuous complex-alternating map. -/
def continuousDetRowAlternating :
    (n -> Complex) [⋀^n]→L[Complex] Complex :=
  (Matrix.detRowAlternating :
    (n -> Complex) [⋀^n]→ₗ[Complex] Complex).mkContinuous
      (Nat.factorial (Fintype.card n) : Real) detRowAlternating_norm_le

@[simp] theorem continuousDetRowAlternating_apply
    (M : Matrix n n Complex) :
    continuousDetRowAlternating M = M.det := rfl

/-- The same determinant map viewed as real multilinear, which is the scalar
structure used by real-time matrix paths. -/
def realContinuousDetRowAlternating :
    (n -> Complex) [⋀^n]→L[Real] Complex where
  toFun := continuousDetRowAlternating (n := n)
  map_update_add' := by
    intro inst M i x y
    cases Subsingleton.elim inst decN
    exact ContinuousAlternatingMap.map_update_add
      (f := continuousDetRowAlternating (n := n)) M i x y
  map_update_smul' := by
    intro inst M i c x
    cases Subsingleton.elim inst decN
    simpa only [Complex.coe_smul] using
      (ContinuousAlternatingMap.map_update_smul
        (f := continuousDetRowAlternating (n := n)) M i (c : Complex) x)
  map_eq_zero_of_eq' := by
    intro M i j hij hne
    exact (continuousDetRowAlternating (n := n)).map_eq_zero_of_eq' M i j hij hne
  cont := (continuousDetRowAlternating (n := n)).cont

@[simp] theorem realContinuousDetRowAlternating_apply
    (M : Matrix n n Complex) :
    realContinuousDetRowAlternating M = M.det := rfl

/-! ## Algebraic Jacobi identity -/

/-- A row of `B` is a linear combination of the rows of `A`, with
coefficients given by `B A⁻¹`, whenever `A` is invertible. -/
theorem row_eq_sum_inv_coeff_smul
    (A B : Matrix n n Complex) (hA : IsUnit A.det) (i : n) :
    B i = ∑ k, ((B * A⁻¹) i k) • A k := by
  have hmatrix : B * A⁻¹ * A = B :=
    Matrix.nonsing_inv_mul_cancel_right A B hA
  ext j
  simpa only [Matrix.mul_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    using (congrArg (fun M : Matrix n n Complex => M i j) hmatrix).symm

/-- The row-replacement sum appearing in the derivative of the determinant is
`trace (B A⁻¹) det A`. -/
theorem sum_det_updateRow_eq_trace_mul_det
    (A B : Matrix n n Complex) (hA : IsUnit A.det) :
    (∑ i, (A.updateRow i (B i)).det) =
      Matrix.trace (B * A⁻¹) * A.det := by
  calc
    (∑ i, (A.updateRow i (B i)).det) =
        ∑ i, (A.updateRow i
          (∑ k, ((B * A⁻¹) i k) • A k)).det := by
      apply Finset.sum_congr rfl
      intro i _
      rw [row_eq_sum_inv_coeff_smul A B hA i]
    _ = ∑ i, ((B * A⁻¹) i i) • A.det := by
      apply Finset.sum_congr rfl
      intro i _
      exact Matrix.det_updateRow_sum A i (fun k => (B * A⁻¹) i k)
    _ = Matrix.trace (B * A⁻¹) * A.det := by
      simp only [smul_eq_mul, ← Finset.sum_mul, Matrix.trace, Matrix.diag]

/-- Jacobi's determinant formula for a real-time path of complex matrices.
The proof differentiates the determinant as a continuous alternating map and
then evaluates its row-replacement derivative using invertibility. -/
theorem det_path_hasDerivAt
    (Y : Real -> Matrix n n Complex) (dY : Matrix n n Complex)
    {t : Real} (hY : HasDerivAt Y dY t)
    (hYunit : IsUnit (Y t).det) :
    HasDerivAt (fun s => (Y s).det)
      (Matrix.trace (dY * (Y t)⁻¹) * (Y t).det) t := by
  have hdet :=
    (realContinuousDetRowAlternating (n := n)).hasFDerivAt (Y t)
  have hcomp := (hdet.comp t hY.hasFDerivAt).hasDerivAt
  convert hcomp using 1
  simp only [ContinuousLinearMap.comp_apply]
  let L := (realContinuousDetRowAlternating (n := n)).linearDeriv (Y t)
  calc
    Matrix.trace (dY * (Y t)⁻¹) * (Y t).det = L dY := by
      dsimp only [L]
      rw [ContinuousMultilinearMap.linearDeriv_apply]
      change _ = ∑ i, Matrix.det ((Y t).updateRow i (dY i))
      exact (sum_det_updateRow_eq_trace_mul_det (Y t) dY hYunit).symm
    _ = L ((ContinuousLinearMap.toSpanSingleton Real dY) 1) := by
      rw [ContinuousLinearMap.toSpanSingleton_apply_one]

/-! ## Generated Liu--Wang flow -/

/-- The determinant of the generated Hamiltonian `Y` path satisfies the
source-correct Jacobi equation with coefficient `trace (C H)`. -/
theorem generated_detY_hasDerivAt
    (d : Coefficients n) {t : Real}
    (ht : t ∈ Set.uIcc d.startTime d.endTime) :
    HasDerivAt (fun s => (d.toRiccatiFlow.Y s).det)
      (Matrix.trace (d.C t * d.toRiccatiFlow.H t) *
        (d.toRiccatiFlow.Y t).det) t := by
  have hdet := det_path_hasDerivAt
    d.toRiccatiFlow.Y (d.C t * d.toRiccatiFlow.Z t)
    (d.toRiccatiFlow.hasDerivY t ht) (d.toRiccatiFlow.YdetUnit t ht)
  simpa only [RiccatiFlow.H, Matrix.mul_assoc] using hdet

/-- Interval form of the generated determinant equation. -/
theorem generated_detY_jacobiEquation
    (d : Coefficients n) :
    forall t, t ∈ Set.uIcc d.startTime d.endTime ->
      HasDerivAt (fun s => (d.toRiccatiFlow.Y s).det)
        (Matrix.trace (d.C t * d.toRiccatiFlow.H t) *
          (d.toRiccatiFlow.Y t).det) t :=
  fun _ ht => generated_detY_hasDerivAt d ht

end LiuWang2025SemilinearWaveDeterminantJacobi
