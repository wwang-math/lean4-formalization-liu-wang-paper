import LiuWang.LiuWang2025SemilinearWaveContractionRadius
import Mathlib.Topology.MetricSpace.Contracting

/-! # Banach-ball closure for Liu--Wang Section 2

Section 2 of Liu--Wang reduces the semilinear forward problem to a Picard map
on the closed state ball `Z(rho, T)`.  The paper obtains two analytic estimates:
one bounds the image of the map, and the other bounds its Lipschitz factor.

This file keeps those PDE estimates as explicit inputs and verifies the entire
functional-analytic handoff.  The explicit radius certificate makes the map
forward invariant and strictly contracting; Mathlib's Banach fixed-point
theorem then supplies a solution, uniqueness inside the state ball, and
convergence of every Picard iteration started in that ball.

The concrete Lorentzian energy estimate, extension operator, Sobolev product
estimate, and Nemytskii estimate remain source-facing analytic obligations.
-/

noncomputable section

open Filter Function Set
open scoped Topology

namespace LiuWang2025SemilinearWaveBanachBall

open LiuWang2025SemilinearWaveContractionRadius

variable {X : Type*} [NormedAddCommGroup X] [CompleteSpace X]

/-- Abstract version of the paper's closed state ball `Z(rho, T)`. -/
def stateBall (rho : Real) : Set X :=
  Metric.closedBall 0 rho

omit [CompleteSpace X] in
@[simp] theorem mem_stateBall_iff {rho : Real} {x : X} :
    x ∈ stateBall rho ↔ ‖x‖ ≤ rho := by
  simp [stateBall, dist_eq_norm]

/-- The right-hand side of the paper's ball-invariance estimate (2.5). -/
def selfMapBudget (C K T rho : Real) : Real :=
  C * (boundaryDataRadius C K T rho +
    boundaryDataRadius C K T rho * rho + rho ^ 2) * Real.exp (K * T)

/-- The Lipschitz factor appearing immediately after equation (2.5). -/
def contractionFactor (C K T rho : Real) : Real :=
  C * (boundaryDataRadius C K T rho + rho) * Real.exp (K * T)

theorem selfMapBudget_lt_radius {C K T rho : Real} (hC : 0 < C) (hrho : 0 < rho)
    (hrhoSmall : rho < stateRadiusCeiling C K T) :
    selfMapBudget C K T rho < rho := by
  exact selfMap_inequality hC hrho hrhoSmall

theorem contractionFactor_nonneg {C K T rho : Real} (hC : 0 < C) (hrho : 0 < rho) :
    0 ≤ contractionFactor C K T rho := by
  unfold contractionFactor
  exact mul_nonneg
    (mul_nonneg hC.le (add_nonneg (boundaryDataRadius_pos hC hrho).le hrho.le))
    (Real.exp_pos _).le

theorem contractionFactor_lt_one {C K T rho : Real} (hC : 0 < C)
    (hrhoSmall : rho < stateRadiusCeiling C K T) :
    contractionFactor C K T rho < 1 := by
  exact contraction_inequality hC hrhoSmall

/-- The paper-facing analytic estimates for the Section 2 solution map.

For the concrete map `T`, `selfMapBound` is the energy/Sobolev estimate used
in (2.5), while `differenceBound` is the estimate obtained from the fundamental
theorem of calculus applied to the nonlinearity. -/
structure PicardEstimates (C K T rho : Real) (map : X → X) : Prop where
  selfMapBound : ∀ x : X, ‖x‖ ≤ rho → ‖map x‖ ≤ selfMapBudget C K T rho
  differenceBound : ∀ x y : X, ‖x‖ ≤ rho → ‖y‖ ≤ rho →
    ‖map x - map y‖ ≤ contractionFactor C K T rho * ‖x - y‖

omit [CompleteSpace X] in
/-- The checked scalar radius turns the analytic image estimate into a genuine
forward-invariance statement for the closed state ball. -/
theorem mapsTo_stateBall {C K T rho : Real} {map : X → X}
    (hC : 0 < C) (hrho : 0 < rho)
    (hrhoSmall : rho < stateRadiusCeiling C K T)
    (hmap : PicardEstimates C K T rho map) :
    MapsTo map (stateBall rho) (stateBall rho) := by
  intro x hx
  rw [mem_stateBall_iff] at hx ⊢
  exact (hmap.selfMapBound x hx).trans
    (selfMapBudget_lt_radius hC hrho hrhoSmall).le

omit [CompleteSpace X] in
/-- The restricted Picard map is a contraction in Mathlib's precise sense. -/
theorem restrictedMap_contractingWith {C K T rho : Real} {map : X → X}
    (hC : 0 < C) (hrho : 0 < rho)
    (hrhoSmall : rho < stateRadiusCeiling C K T)
    (hmap : PicardEstimates C K T rho map) :
    ContractingWith
      ⟨contractionFactor C K T rho, contractionFactor_nonneg hC hrho⟩
      ((mapsTo_stateBall hC hrho hrhoSmall hmap).restrict map
        (stateBall rho) (stateBall rho)) := by
  constructor
  · exact_mod_cast contractionFactor_lt_one hC hrhoSmall
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    change dist (map (x : X)) (map (y : X)) ≤
      contractionFactor C K T rho * dist (x : X) (y : X)
    simpa only [dist_eq_norm] using
      hmap.differenceBound x y
        (mem_stateBall_iff.mp x.property) (mem_stateBall_iff.mp y.property)

/-- The exact Banach fixed-point conclusion used at the end of Liu--Wang
Theorem 2.1.

Every Picard iteration starting in `Z(rho, T)` converges to the same fixed
point.  Uniqueness is asserted only inside this state ball, exactly matching
the contraction argument. -/
theorem exists_unique_fixedPoint_and_picard_converges
    {C K T rho : Real} {map : X → X}
    (hC : 0 < C) (hrho : 0 < rho)
    (hrhoSmall : rho < stateRadiusCeiling C K T)
    (hmap : PicardEstimates C K T rho map) :
    ∃ u : X,
      ‖u‖ ≤ rho ∧
      IsFixedPt map u ∧
      (∀ v : X, ‖v‖ ≤ rho → IsFixedPt map v → v = u) ∧
      (∀ x : X, ‖x‖ ≤ rho →
        Tendsto (fun n : Nat => map^[n] x) atTop (nhds u)) := by
  let q : NNReal :=
    ⟨contractionFactor C K T rho, contractionFactor_nonneg hC hrho⟩
  let s : Set X := stateBall rho
  have hsComplete : IsComplete s := by
    dsimp [s, stateBall]
    exact Metric.isClosed_closedBall.isComplete
  have hsMap : MapsTo map s s := by
    simpa only [s] using mapsTo_stateBall hC hrho hrhoSmall hmap
  have hcontract : ContractingWith q (hsMap.restrict map s s) := by
    simpa only [q, s] using restrictedMap_contractingWith hC hrho hrhoSmall hmap
  have hzero : (0 : X) ∈ s := by
    change (0 : X) ∈ stateBall rho
    exact mem_stateBall_iff.mpr (by simpa using hrho.le)
  rcases hcontract.exists_fixedPoint' hsComplete hsMap hzero (edist_ne_top _ _) with
    ⟨u, hu, hfixed, _hzeroConverges, _hgeometric⟩
  have huNorm : ‖u‖ ≤ rho := by
    apply mem_stateBall_iff.mp
    simpa only [s] using hu
  refine ⟨u, huNorm, hfixed, ?_, ?_⟩
  · intro v hv hfixedv
    have hvMem : v ∈ s := by
      change v ∈ stateBall rho
      exact mem_stateBall_iff.mpr hv
    have huSub : IsFixedPt (hsMap.restrict map s s) (⟨u, hu⟩ : s) := by
      apply Subtype.ext
      exact hfixed
    have hvSub : IsFixedPt (hsMap.restrict map s s) (⟨v, hvMem⟩ : s) := by
      apply Subtype.ext
      exact hfixedv
    exact congrArg Subtype.val (hcontract.fixedPoint_unique' hvSub huSub)
  · intro x hx
    have hxMem : x ∈ s := by
      change x ∈ stateBall rho
      exact mem_stateBall_iff.mpr hx
    rcases hcontract.exists_fixedPoint' hsComplete hsMap hxMem (edist_ne_top _ _) with
      ⟨y, hy, hfixedy, hyConverges, _hyGeometric⟩
    have hyu : y = u := by
      have hySub : IsFixedPt (hsMap.restrict map s s) (⟨y, hy⟩ : s) := by
        apply Subtype.ext
        exact hfixedy
      have huSub : IsFixedPt (hsMap.restrict map s s) (⟨u, hu⟩ : s) := by
        apply Subtype.ext
        exact hfixed
      exact congrArg Subtype.val (hcontract.fixedPoint_unique' hySub huSub)
    simpa only [hyu] using hyConverges

/-- A compact certificate exposing the exact verified and source-facing pieces
of the Section 2 fixed-point argument. -/
structure BanachBallCertificate (C K T rho : Real) (map : X → X) where
  sourceRadiusPositive : 0 < boundaryDataRadius C K T rho
  radiusSelfMap : selfMapBudget C K T rho < rho
  radiusContracts : contractionFactor C K T rho < 1
  existsUniqueAndPicard :
    ∃ u : X,
      ‖u‖ ≤ rho ∧
      IsFixedPt map u ∧
      (∀ v : X, ‖v‖ ≤ rho → IsFixedPt map v → v = u) ∧
      (∀ x : X, ‖x‖ ≤ rho →
        Tendsto (fun n : Nat => map^[n] x) atTop (nhds u))

/-- Build the complete Section 2 Banach-ball certificate from the two concrete
PDE estimates and the explicit state-radius condition. -/
def banachBallCertificate {C K T rho : Real} {map : X → X}
    (hC : 0 < C) (hrho : 0 < rho)
    (hrhoSmall : rho < stateRadiusCeiling C K T)
    (hmap : PicardEstimates C K T rho map) :
    BanachBallCertificate C K T rho map where
  sourceRadiusPositive := boundaryDataRadius_pos hC hrho
  radiusSelfMap := selfMapBudget_lt_radius hC hrho hrhoSmall
  radiusContracts := contractionFactor_lt_one hC hrhoSmall
  existsUniqueAndPicard :=
    exists_unique_fixedPoint_and_picard_converges hC hrho hrhoSmall hmap

end LiuWang2025SemilinearWaveBanachBall
