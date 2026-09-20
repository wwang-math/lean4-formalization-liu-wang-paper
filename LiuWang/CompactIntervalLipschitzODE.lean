import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Analysis.ODE.Gronwall

/-!
# Existence on a whole compact interval for a globally Lipschitz vector field

The local Picard--Lindelof theorem uses a bounded state ball. For the linear
Hamiltonian system behind Liu--Wang's Gaussian beams, the Lipschitz bound is
global in the state. Working on all continuous paths removes the restriction
on interval length. A factorial estimate makes an iterate of the Picard map
contractive, so no pre-existing solution or continuation bound is assumed.

The factorial estimate adapts the proof in Mathlib's PicardLindelof.lean
(Yury Kudryashov and Winston Yin, Apache 2.0).
-/

noncomputable section

open Function MeasureTheory Metric Set
open scoped Nat NNReal Topology

namespace CompactIntervalLipschitzODE

variable {E : Type*} [NormedAddCommGroup E]
variable {a b : Real} (t0 : Icc a b)

abbrev Path := C(Icc a b, E)

def extend (u : Path (E := E) (a := a) (b := b)) (t : Real) : E :=
  u (projIcc a b (le_trans t0.2.1 t0.2.2) t)

theorem extend_of_mem (u : Path (E := E) (a := a) (b := b))
    {t : Real} (ht : t ∈ Icc a b) : extend t0 u t = u ⟨t, ht⟩ := by
  simp [extend, projIcc_of_mem _ ht]

theorem continuous_extend (u : Path (E := E) (a := a) (b := b)) :
    Continuous (extend t0 u) := u.continuous.comp continuous_projIcc

variable [NormedSpace Real E] [CompleteSpace E] (f : Real → E → E)
variable (hf : ContinuousOn (uncurry f) ((Icc a b) ×ˢ (univ : Set E)))

include hf

omit [CompleteSpace E] in
theorem continuousOn_integrand (u : Path (E := E) (a := a) (b := b)) :
    ContinuousOn (fun t => f t (extend t0 u t)) (Icc a b) :=
  ODE.continuousOn_comp hf (continuous_extend t0 u).continuousOn
    (fun _ _ => mem_univ _)

theorem integrand_intervalIntegrable (u : Path (E := E) (a := a) (b := b))
    (t : Icc a b) : IntervalIntegrable (fun s => f s (extend t0 u s)) volume t0 t :=
  ((continuousOn_integrand t0 f hf u).mono (uIcc_subset_Icc t0.2 t.2)).intervalIntegrable

def next (x0 : E) (u : Path (E := E) (a := a) (b := b)) :
    Path (E := E) (a := a) (b := b) where
  toFun t := ODE.picard f t0 x0 (extend t0 u) t
  continuous_toFun := continuousOn_iff_continuous_restrict.mp <|
    HasDerivWithinAt.continuousOn fun _ ht =>
      ODE.hasDerivWithinAt_picard_Icc t0.2 hf
        (continuous_extend t0 u).continuousOn (fun _ _ => mem_univ _) x0 ht

@[simp] theorem next_apply (x0 : E)
    (u : Path (E := E) (a := a) (b := b)) (t : Icc a b) :
    next t0 f hf x0 u t = x0 + ∫ s in (t0 : Real)..(t : Real), f s (extend t0 u s) := rfl

variable (K : NNReal) (hK : ∀ t ∈ Icc a b, LipschitzWith K (f t))

include hK

theorem dist_iterate_next_apply_le (x0 : E)
    (u v : Path (E := E) (a := a) (b := b)) (n : Nat) (t : Icc a b) :
    dist ((next t0 f hf x0)^[n] u t) ((next t0 f hf x0)^[n] v t) ≤
      (K * |t.1 - t0.1|) ^ n / n ! * dist u v := by
  induction n generalizing t with
  | zero => simpa using ContinuousMap.dist_apply_le_dist (f := u) (g := v) t
  | succ n hn =>
    rw [iterate_succ_apply', iterate_succ_apply', dist_eq_norm, next_apply,
      next_apply, add_sub_add_left_eq_sub,
      ← intervalIntegral.integral_sub (integrand_intervalIntegrable t0 f hf _ t)
        (integrand_intervalIntegrable t0 f hf _ t)]
    calc
      _ ≤ ∫ s in uIoc (t0 : Real) (t : Real),
          K ^ (n + 1) * |s - t0| ^ n / n ! * dist u v := by
        rw [intervalIntegral.norm_intervalIntegral_eq]
        apply MeasureTheory.norm_integral_le_of_norm_le
          (Continuous.integrableOn_uIoc (by fun_prop))
        apply (ae_restrict_mem measurableSet_Ioc).mono
        intro s hs
        have hs' : s ∈ Icc a b :=
          (uIoc_subset_uIcc.trans (uIcc_subset_Icc t0.2 t.2)) hs
        rw [← dist_eq_norm, extend_of_mem t0 _ hs', extend_of_mem t0 _ hs']
        calc
          _ ≤ K * dist ((next t0 f hf x0)^[n] u ⟨s, hs'⟩)
              ((next t0 f hf x0)^[n] v ⟨s, hs'⟩) := (hK s hs').dist_le_mul _ _
          _ ≤ K ^ (n + 1) * |s - t0| ^ n / n ! * dist u v := by
            rw [pow_succ', mul_assoc, mul_div_assoc, mul_assoc]
            gcongr
            simpa only [mul_pow] using hn ⟨s, hs'⟩
      _ ≤ (K * |t.1 - t0.1|) ^ (n + 1) / (n + 1) ! * dist u v := by
        apply le_of_abs_le
        rw [← intervalIntegral.abs_intervalIntegral_eq, intervalIntegral.integral_mul_const,
          intervalIntegral.integral_div, intervalIntegral.integral_const_mul, abs_mul, abs_div,
          abs_mul, intervalIntegral.abs_intervalIntegral_eq, integral_pow_abs_sub_uIoc, abs_div,
          abs_pow, abs_pow, abs_dist, NNReal.abs_eq, abs_abs, mul_div, div_div, ← abs_mul,
          ← Nat.cast_succ, ← Nat.cast_mul, ← Nat.factorial_succ, Nat.abs_cast, ← mul_pow]

theorem dist_iterate_next_le (x0 : E)
    (u v : Path (E := E) (a := a) (b := b)) (n : Nat) :
    dist ((next t0 f hf x0)^[n] u) ((next t0 f hf x0)^[n] v) ≤
      (K * max (b - t0) (t0 - a)) ^ n / n ! * dist u v := by
  rw [ContinuousMap.dist_le]
  · intro t
    apply (dist_iterate_next_apply_le t0 f hf K hK x0 u v n t).trans
    gcongr
    exact abs_sub_le_max_sub t.2.1 t.2.2 _
  · have : 0 ≤ max (b - t0) (t0 - a) := le_max_of_le_left (sub_nonneg.mpr t0.2.2)
    positivity

theorem exists_fixedPoint (x0 : E) :
    ∃ u : Path (E := E) (a := a) (b := b), IsFixedPt (next t0 f hf x0) u := by
  obtain ⟨n, hn⟩ :=
    (FloorSemiring.tendsto_pow_div_factorial_atTop (K * max (b - t0) (t0 - a))).eventually
      (gt_mem_nhds zero_lt_one) |>.exists
  have hnonneg : (0 : Real) ≤ (K * max (b - t0) (t0 - a)) ^ n / n ! := by
    have : 0 ≤ max (b - t0) (t0 - a) := le_max_of_le_left (sub_nonneg.mpr t0.2.2)
    positivity
  let q : NNReal := ⟨_, hnonneg⟩
  have hcontract : ContractingWith q ((next t0 f hf x0)^[n]) :=
    ⟨hn, LipschitzWith.of_dist_le_mul fun u v =>
      dist_iterate_next_le t0 f hf K hK x0 u v n⟩
  exact ⟨_, hcontract.isFixedPt_fixedPoint_iterate⟩

/-- No smallness of the time interval, Lipschitz constant, or initial state
is required. The derivative is one-sided at the interval endpoints. -/
theorem exists_solution (x0 : E) :
    ∃ u : Real → E, u t0 = x0 ∧ Continuous u ∧
      ∀ t ∈ Icc a b, HasDerivWithinAt u (f t (u t)) (Icc a b) t := by
  obtain ⟨u, hu⟩ := exists_fixedPoint t0 f hf K hK x0
  have heq : ∀ t ∈ Icc a b,
      extend t0 u t = ODE.picard f t0 x0 (extend t0 u) t := by
    intro t ht
    rw [extend_of_mem t0 u ht]
    nth_rw 1 [← hu]
    rfl
  refine ⟨extend t0 u, ?_, continuous_extend t0 u, fun t ht => ?_⟩
  · rw [heq t0 t0.2, ODE.picard_apply₀]
  · exact (ODE.hasDerivWithinAt_picard_Icc t0.2 hf
      (continuous_extend t0 u).continuousOn (fun _ _ => mem_univ _) x0 ht).congr_of_mem
      heq ht

end CompactIntervalLipschitzODE
