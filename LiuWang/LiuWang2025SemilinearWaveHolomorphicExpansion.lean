import LiuWang.LiuWang2025SemilinearWaveHolomorphicRecovery
import Mathlib.Analysis.Complex.TaylorSeries

/-!
# Liu--Wang 2025: the factorial Taylor expansion of the source nonlinearity

Source: Boya Liu and Weinan Wang, *On a partial data inverse problem for the
semi-linear wave equation*, arXiv:2511.08794v1, Section 1.

The paper imposes on `V : bar(Omega) x C -> C` the two conditions

* (i)  `C ∋ z ↦ V(., z)` is holomorphic with values in `C^alpha(bar Omega)`;
* (ii) `V(x, 0) = d_z V(x, 0) = 0` for every `x`,

and then asserts the convergent expansion

`V(x, t, z) = sum_{k >= 2} V_k(x, t) z^k / k!`,  `V_k := d_z^k V(x, t, 0)`,

the series converging in the `C^alpha` topology.

Until now the dossier consumed that expansion as an input field
(`HolomorphicRecovery.PointwiseExpansion.hasSum_factorialExpansion`).  This
module *derives* it.  For an arbitrary complex Banach space `E` of coefficient
functions -- `C^alpha(bar Omega)` is one such space, and nothing below uses any
further property of it -- Lean proves:

* `SourceNonlinearity.coeff_zero`, `coeff_one` : condition (ii) makes the
  zeroth and first Taylor coefficients vanish;
* `SourceNonlinearity.hasSum_taylor` : condition (i) makes the factorial
  series `sum_k (k!)^{-1} z^k V_k` converge to `V z` in `E`, for *every*
  complex `z` (the expansion is global, as in the source);
* `SourceNonlinearity.hasSum_tail` : combining the two, the series may be
  started at `k = 2`, which is the displayed formula of the paper;
* `SourceNonlinearity.hasSum_eval` : applying any continuous linear
  functional -- in particular evaluation at a point `x` of `bar Omega` --
  gives the scalar display `V(x, z) = sum_{k >= 2} V_k(x) z^k / k!`;
* `SourceNonlinearity.toPointwiseExpansion` : the scalar case constructs the
  `PointwiseExpansion` packet consumed by the recovery module, so the
  expansion is no longer an assumption there;
* `SourceNonlinearity.eq_of_coeff_eq` : equality of all Taylor coefficients
  forces equality of the nonlinearities at every complex parameter.

A local version on a ball is also proved, for the small-data regime.

## Scope

`E` is an arbitrary complete complex normed space.  Building the Hölder space
`C^alpha(bar Omega)` as a Lean normed space is not needed for any statement
here and is not done; every theorem holds for that space once it is
constructed, and for every other complex Banach space.
-/

noncomputable section

open Complex

namespace LiuWang2025SemilinearWaveHolomorphicExpansion

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Complex E] [CompleteSpace E]

/-- The source's nonlinearity as a function of the complex parameter, with the
paper's conditions (i) and (ii).  Values are taken in an arbitrary complex
Banach space of coefficient functions on the spacetime cylinder. -/
structure SourceNonlinearity (E : Type*) [NormedAddCommGroup E]
    [NormedSpace Complex E] [CompleteSpace E] where
  /-- `z ↦ V(., z)`. -/
  V : Complex -> E
  /-- Condition (i): holomorphy in the complex parameter. -/
  entire : Differentiable Complex V
  /-- Condition (ii), first half: `V(x, 0) = 0`. -/
  valueAtZero : V 0 = 0
  /-- Condition (ii), second half: `d_z V(x, 0) = 0`. -/
  derivAtZero : deriv V 0 = 0

namespace SourceNonlinearity

variable (S : SourceNonlinearity E)

/-- The paper's Taylor coefficient `V_k = d_z^k V(., 0)`. -/
def coeff (k : Nat) : E := iteratedDeriv k S.V 0

@[simp] theorem coeff_zero : S.coeff 0 = 0 := by
  simpa [coeff, iteratedDeriv_zero] using S.valueAtZero

@[simp] theorem coeff_one : S.coeff 1 = 0 := by
  simpa [coeff, iteratedDeriv_one] using S.derivAtZero

/-- **The convergent factorial expansion of the source.**  Condition (i)
alone gives, for every complex `z`, convergence of `sum_k V_k z^k / k!` to
`V(z)` in the norm of the coefficient space. -/
theorem hasSum_taylor (z : Complex) :
    HasSum (fun k : Nat => ((Nat.factorial k : Complex))⁻¹ • (z ^ k • S.coeff k))
      (S.V z) := by
  simpa [coeff] using Complex.hasSum_taylorSeries_of_entire S.entire 0 z

/-- **The displayed expansion of the paper**: by condition (ii) the series may
be started at `k = 2`. -/
theorem hasSum_tail (z : Complex) :
    HasSum
      (fun k : Nat =>
        ((Nat.factorial (k + 2) : Complex))⁻¹ • (z ^ (k + 2) • S.coeff (k + 2)))
      (S.V z) := by
  have hmain := S.hasSum_taylor z
  have h :=
    (hasSum_nat_add_iff'
        (f := fun k : Nat =>
          ((Nat.factorial k : Complex))⁻¹ • (z ^ k • S.coeff k)) 2).mpr hmain
  simpa [Finset.sum_range_succ] using h

/-- Any continuous linear functional on the coefficient space -- in
particular evaluation at a point `x` of the closure of `Omega` -- turns the
expansion into the scalar display of the paper. -/
theorem hasSum_eval (L : E →L[Complex] Complex) (z : Complex) :
    HasSum (fun k : Nat => L (S.coeff k) * z ^ k / (Nat.factorial k : Complex))
      (L (S.V z)) := by
  have h := (S.hasSum_taylor z).map L L.continuous
  have hfun : (fun k : Nat => L (S.coeff k) * z ^ k / (Nat.factorial k : Complex))
      = fun k : Nat => L (((Nat.factorial k : Complex))⁻¹ • (z ^ k • S.coeff k)) := by
    funext k
    simp only [map_smul, smul_eq_mul]
    ring
  rw [hfun]
  exact h

/-- The same, started at `k = 2`. -/
theorem hasSum_eval_tail (L : E →L[Complex] Complex) (z : Complex) :
    HasSum
      (fun k : Nat =>
        L (S.coeff (k + 2)) * z ^ (k + 2) / (Nat.factorial (k + 2) : Complex))
      (L (S.V z)) := by
  have h := (S.hasSum_tail z).map L L.continuous
  have hfun : (fun k : Nat =>
        L (S.coeff (k + 2)) * z ^ (k + 2) / (Nat.factorial (k + 2) : Complex))
      = fun k : Nat =>
        L (((Nat.factorial (k + 2) : Complex))⁻¹ • (z ^ (k + 2) • S.coeff (k + 2))) := by
    funext k
    simp only [map_smul, smul_eq_mul]
    ring
  rw [hfun]
  exact h

/-- Equality of all Taylor coefficients forces equality of the
nonlinearities.  This is the analytic-continuation step of the source's final
argument, here a theorem rather than an assumption. -/
theorem eq_of_coeff_eq (S T : SourceNonlinearity E)
    (hcoeff : ∀ k, S.coeff k = T.coeff k) (z : Complex) : S.V z = T.V z := by
  have hS := S.hasSum_taylor z
  have hT := T.hasSum_taylor z
  have hfun : (fun k : Nat => ((Nat.factorial k : Complex))⁻¹ • (z ^ k • S.coeff k))
      = fun k : Nat => ((Nat.factorial k : Complex))⁻¹ • (z ^ k • T.coeff k) := by
    funext k
    rw [hcoeff k]
  rw [hfun] at hS
  exact hS.unique hT

/-- **The source's closure of the recovery.**  Condition (ii) forces the zeroth
and first Taylor coefficients to vanish, the source assumes the second vanishes,
and the induction of Subsection 4.3 supplies every coefficient from the third
on.  Hence the two nonlinearities agree at every complex parameter -- which is
the paper's final sentence, that the `C^alpha`-convergent power series
determines `V(t,x,z)` for all `z`. -/
theorem eq_of_coeff_eq_from_three (S T : SourceNonlinearity E)
    (hS2 : S.coeff 2 = 0) (hT2 : T.coeff 2 = 0)
    (hcoeff : ∀ k, 3 ≤ k -> S.coeff k = T.coeff k) (z : Complex) :
    S.V z = T.V z := by
  refine eq_of_coeff_eq S T (fun k => ?_) z
  rcases k with _ | _ | _ | n
  · simp
  · simp
  · simp [hS2, hT2]
  · exact hcoeff (n + 3) (by omega)

end SourceNonlinearity

/-! ## The source's induction on the order

Subsection 4.3 recovers `V_m` for `m >= 4` from the assumption that
`V_3, ..., V_{m-1}` are already recovered, the base case `m = 3` being the
cubic recovery of Subsection 4.2.  The statement below is that induction
skeleton: the per-order step is the input -- it is what the point-recovery
packet supplies -- and the conclusion for every order is the theorem.
-/

/-- **The source's induction.**  If every order from the third on is determined
once all strictly lower orders are, then every order from the third on is
determined. -/
theorem forall_eq_of_inductive_step {alpha : Type*} {S T : Nat -> alpha}
    (hstep : ∀ m, 3 ≤ m -> (∀ k, 3 ≤ k -> k < m -> S k = T k) -> S m = T m) :
    ∀ m, 3 ≤ m -> S m = T m := by
  have key : ∀ n : Nat, ∀ k : Nat, k ≤ n -> 3 ≤ k -> S k = T k := by
    intro n
    induction n with
    | zero =>
        intro k hk hk3
        omega
    | succ n ih =>
        intro k hk hk3
        rcases Nat.lt_or_ge k (n + 1) with hlt | hge
        · exact ih k (by omega) hk3
        · have hkeq : k = n + 1 := by omega
          subst hkeq
          exact hstep (n + 1) hk3 (fun j hj3 hjk => ih j (by omega) hj3)
  intro m hm
  exact key m m le_rfl hm

/-- **The full recovery, assembled.**  The cubic recovery of Subsection 4.2 and
the inductive step of Subsection 4.3 together determine the nonlinearity at
every complex parameter. -/
theorem eq_of_cubic_and_inductive_step (S T : SourceNonlinearity E)
    (hS2 : S.coeff 2 = 0) (hT2 : T.coeff 2 = 0)
    (hstep : ∀ m, 3 ≤ m ->
      (∀ k, 3 ≤ k -> k < m -> S.coeff k = T.coeff k) -> S.coeff m = T.coeff m)
    (z : Complex) : S.V z = T.V z :=
  SourceNonlinearity.eq_of_coeff_eq_from_three S T hS2 hT2
    (forall_eq_of_inductive_step hstep) z


/-! ## The scalar case: construction of the recovery module's input -/

open LiuWang2025SemilinearWaveHolomorphicRecovery

/-- For a scalar-valued holomorphic nonlinearity satisfying the paper's two
conditions, Lean constructs the convergent factorial expansion packet used by
the recovery module.  Its `hasSum_factorialExpansion` field is now a theorem. -/
def SourceNonlinearity.toPointwiseExpansion (S : SourceNonlinearity Complex) :
    PointwiseExpansion where
  nonlinearity := S.V
  coefficients := S.coeff
  hasSum_factorialExpansion := by
    intro z
    have h := S.hasSum_taylor z
    have hfun : (fun m : Nat => factorialWeightedTerm S.coeff z m)
        = fun m : Nat => ((Nat.factorial m : Complex))⁻¹ • (z ^ m • S.coeff m) := by
      funext m
      simp only [factorialWeightedTerm, smul_eq_mul]
      ring
    rw [hfun]
    exact h

@[simp] theorem SourceNonlinearity.toPointwiseExpansion_nonlinearity
    (S : SourceNonlinearity Complex) :
    S.toPointwiseExpansion.nonlinearity = S.V := rfl

@[simp] theorem SourceNonlinearity.toPointwiseExpansion_coefficients
    (S : SourceNonlinearity Complex) :
    S.toPointwiseExpansion.coefficients = S.coeff := rfl

/-- Two scalar source nonlinearities whose recovered Taylor coefficients agree
have the same nonlinearity at every complex parameter. -/
theorem nonlinearity_eq_of_coefficients_eq
    (S T : SourceNonlinearity Complex)
    (hcoeff : ∀ m, S.coeff m = T.coeff m) (z : Complex) :
    S.V z = T.V z :=
  SourceNonlinearity.eq_of_coeff_eq S T hcoeff z

/-! ## Local version on a ball -/

/-- Small-data version: holomorphy on a ball suffices for the expansion
inside that ball. -/
theorem hasSum_taylor_on_ball {V : Complex -> E} {r : Real}
    (hV : DifferentiableOn Complex V (Metric.ball 0 r))
    {z : Complex} (hz : z ∈ Metric.ball (0 : Complex) r) :
    HasSum
      (fun k : Nat =>
        ((Nat.factorial k : Complex))⁻¹ • (z ^ k • iteratedDeriv k V 0)) (V z) := by
  simpa using Complex.hasSum_taylorSeries_on_ball hV hz

/-- One reviewable object collecting everything the source's conditions (i)
and (ii) give. -/
structure Certificate (S : SourceNonlinearity E) : Prop where
  zerothCoefficientVanishes : S.coeff 0 = 0
  firstCoefficientVanishes : S.coeff 1 = 0
  globalFactorialExpansion : ∀ z : Complex,
    HasSum (fun k : Nat => ((Nat.factorial k : Complex))⁻¹ • (z ^ k • S.coeff k))
      (S.V z)
  expansionStartsAtTwo : ∀ z : Complex,
    HasSum
      (fun k : Nat =>
        ((Nat.factorial (k + 2) : Complex))⁻¹ • (z ^ (k + 2) • S.coeff (k + 2)))
      (S.V z)
  pointwiseDisplay : ∀ (L : E →L[Complex] Complex) (z : Complex),
    HasSum (fun k : Nat => L (S.coeff k) * z ^ k / (Nat.factorial k : Complex))
      (L (S.V z))

/-- The certificate is generated from conditions (i) and (ii). -/
def certificate (S : SourceNonlinearity E) : Certificate S where
  zerothCoefficientVanishes := S.coeff_zero
  firstCoefficientVanishes := S.coeff_one
  globalFactorialExpansion := S.hasSum_taylor
  expansionStartsAtTwo := S.hasSum_tail
  pointwiseDisplay := S.hasSum_eval

end LiuWang2025SemilinearWaveHolomorphicExpansion
