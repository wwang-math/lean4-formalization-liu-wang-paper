import LiuWang.LiuWang2025SemilinearWaveFourBeamPhaseLemma
import Mathlib.Analysis.Calculus.FDeriv.Comp

/-!
# Liu--Wang 2025: specular boundary reflection in arbitrary geometry

Source: Boya Liu and Weinan Wang, *On a partial data inverse problem for the
semi-linear wave equation*, arXiv:2511.08794v1, Section 3.2.

To make the Gaussian beams admissible for the initial boundary value problem,
the source reflects the incident beam in the lateral boundary and subtracts
it, so that the Dirichlet trace cancels while the normal derivative doubles.
The existing flat model `LiuWang2025SemilinearWaveFlatBeam` realizes this for
the explicit reflection `z |-> -z` of Minkowski space.

This module removes the flatness.  All that the reflection argument needs is a
smooth involution `R` of the chart which fixes the boundary pointwise and whose
differential at the boundary point is the identity on the tangent space of the
boundary and minus the identity on a transversal normal vector.  For *any* such
`R` Lean proves:

* `difference_eq_zero_on_boundary` : the reflected difference `u - u o R`
  vanishes at every boundary point -- the exact Dirichlet cancellation;
* `differential_comp_differential` : the differential of the reflection is an
  involution of the tangent space, derived from `R o R = id` by the chain rule
  rather than assumed;
* `difference_tangential_derivative_eq_zero` : all tangential derivatives of the
  difference vanish at the boundary point;
* `difference_normal_derivative` : the normal derivative of the difference is
  *twice* the incident normal derivative -- the source's specular doubling;
* `sum_normal_derivative_eq_zero` and `sum_at_point` : the negative test.  The
  *sum* has vanishing normal derivative and a non-vanishing trace, so the
  difference, not the sum, is the admissible combination.

## Scope

Constructing the involution from a Lorentzian metric near a boundary point --
that is, producing boundary normal coordinates -- is geometric work and is the
data of `BoundaryReflection`.  Given that data, the reflection argument itself
is proved here with no flatness assumption on the metric or the boundary.
-/

noncomputable section

namespace LiuWang2025SemilinearWaveBoundaryReflection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]

/-- A smooth boundary reflection near a boundary point. -/
structure BoundaryReflection (E : Type*) [NormedAddCommGroup E]
    [NormedSpace Real E] where
  /-- The lateral boundary, locally. -/
  boundary : Set E
  /-- The distinguished boundary point where the beam meets the boundary. -/
  point : E
  point_mem : point ∈ boundary
  /-- The reflection map. -/
  reflect : E -> E
  /-- Its differential at the boundary point. -/
  differential : E →L[Real] E
  hasFDeriv : HasFDerivAt reflect differential point
  /-- `R` is an involution. -/
  involutive : ∀ x, reflect (reflect x) = x
  /-- `R` fixes the boundary pointwise. -/
  fixesBoundary : ∀ x ∈ boundary, reflect x = x
  /-- The tangent space of the boundary at the point. -/
  tangent : Submodule Real E
  /-- A transversal normal vector. -/
  normal : E
  /-- The differential is the identity on the boundary tangent space. -/
  differential_tangent : ∀ v ∈ tangent, differential v = v
  /-- ... and minus the identity on the normal. -/
  differential_normal : differential normal = -normal

namespace BoundaryReflection

variable (R : BoundaryReflection E)

@[simp] theorem reflect_point : R.reflect R.point = R.point :=
  R.fixesBoundary R.point R.point_mem

/-- **The differential of an involution is an involution.**  Derived from
`R o R = id` by the chain rule, not assumed. -/
theorem differential_comp_differential :
    R.differential.comp R.differential = ContinuousLinearMap.id Real E := by
  have hcomp : HasFDerivAt (fun x => R.reflect (R.reflect x))
      (R.differential.comp R.differential) R.point := by
    have h1 : HasFDerivAt R.reflect R.differential (R.reflect R.point) := by
      rw [R.reflect_point]
      exact R.hasFDeriv
    exact h1.comp R.point R.hasFDeriv
  have hid : HasFDerivAt (fun x => R.reflect (R.reflect x))
      (ContinuousLinearMap.id Real E) R.point := by
    have hfun : (fun x => R.reflect (R.reflect x)) = id := funext R.involutive
    rw [hfun]
    exact hasFDerivAt_id R.point
  exact hcomp.unique hid

/-- The reflected function `u o R`. -/
def reflected (u : E -> Complex) : E -> Complex := fun x => u (R.reflect x)

/-- The reflected difference used by the source. -/
def difference (u : E -> Complex) : E -> Complex :=
  fun x => u x - R.reflected u x

/-- The reflected sum, used only as a negative test. -/
def reflectedSum (u : E -> Complex) : E -> Complex :=
  fun x => u x + R.reflected u x

/-- **Exact Dirichlet cancellation on the whole boundary.** -/
theorem difference_eq_zero_on_boundary (u : E -> Complex)
    {x : E} (hx : x ∈ R.boundary) : R.difference u x = 0 := by
  simp [difference, reflected, R.fixesBoundary x hx]

/-- The sum doubles the trace instead of cancelling it. -/
theorem reflectedSum_on_boundary (u : E -> Complex)
    {x : E} (hx : x ∈ R.boundary) : R.reflectedSum u x = 2 * u x := by
  simp [reflectedSum, reflected, R.fixesBoundary x hx]
  ring

theorem hasFDerivAt_reflected {u : E -> Complex} {Du : E →L[Real] Complex}
    (hu : HasFDerivAt u Du R.point) :
    HasFDerivAt (R.reflected u) (Du.comp R.differential) R.point := by
  have hu' : HasFDerivAt u Du (R.reflect R.point) := by
    rw [R.reflect_point]; exact hu
  exact hu'.comp R.point R.hasFDeriv

theorem hasFDerivAt_difference {u : E -> Complex} {Du : E →L[Real] Complex}
    (hu : HasFDerivAt u Du R.point) :
    HasFDerivAt (R.difference u) (Du - Du.comp R.differential) R.point :=
  hu.sub (R.hasFDerivAt_reflected hu)

theorem hasFDerivAt_reflectedSum {u : E -> Complex} {Du : E →L[Real] Complex}
    (hu : HasFDerivAt u Du R.point) :
    HasFDerivAt (R.reflectedSum u) (Du + Du.comp R.differential) R.point :=
  hu.add (R.hasFDerivAt_reflected hu)

/-- **All tangential derivatives of the reflected difference vanish.** -/
theorem difference_tangential_derivative_eq_zero
    {Du : E →L[Real] Complex} {v : E} (hv : v ∈ R.tangent) :
    (Du - Du.comp R.differential) v = 0 := by
  simp [R.differential_tangent v hv]

/-- **The specular doubling of the normal derivative.** -/
theorem difference_normal_derivative
    (Du : E →L[Real] Complex) :
    (Du - Du.comp R.differential) R.normal = 2 * Du R.normal := by
  simp [R.differential_normal]
  ring

/-- Negative test: the *sum* has vanishing normal derivative, so it cannot
carry the measured Neumann data. -/
theorem reflectedSum_normal_derivative_eq_zero
    (Du : E →L[Real] Complex) :
    (Du + Du.comp R.differential) R.normal = 0 := by
  simp [R.differential_normal]

/-- One reviewable object collecting the reflection argument in arbitrary
geometry. -/
structure Certificate (R : BoundaryReflection E) (u : E -> Complex)
    (Du : E →L[Real] Complex) : Prop where
  differentialInvolution :
    R.differential.comp R.differential = ContinuousLinearMap.id Real E
  dirichletCancellation : ∀ x ∈ R.boundary, R.difference u x = 0
  tangentialDerivativesVanish : ∀ v ∈ R.tangent,
    (Du - Du.comp R.differential) v = 0
  specularDoubling :
    (Du - Du.comp R.differential) R.normal = 2 * Du R.normal
  sumNormalDerivativeVanishes :
    (Du + Du.comp R.differential) R.normal = 0
  sumTraceDoubles : ∀ x ∈ R.boundary, R.reflectedSum u x = 2 * u x

/-- The reflection certificate is generated from the involution data alone. -/
def certificate (R : BoundaryReflection E) (u : E -> Complex)
    (Du : E →L[Real] Complex) : Certificate R u Du where
  differentialInvolution := R.differential_comp_differential
  dirichletCancellation := fun _ hx => R.difference_eq_zero_on_boundary u hx
  tangentialDerivativesVanish := fun _ hv =>
    R.difference_tangential_derivative_eq_zero hv
  specularDoubling := R.difference_normal_derivative Du
  sumNormalDerivativeVanishes := R.reflectedSum_normal_derivative_eq_zero Du
  sumTraceDoubles := fun _ hx => R.reflectedSum_on_boundary u hx

end BoundaryReflection

/-! ## Non-vacuity: the flat half-space reflection is an instance

The structure above is not an empty abstraction.  The reflection `z |-> -z` in
the last coordinate of a `1+3` chart, which is the map used by the flat model
`LiuWang2025SemilinearWaveFlatBeam`, satisfies every field. -/

/-- The flat coordinate reflection in the last variable. -/
def flatReflectCLM : (Fin 4 -> Real) →L[Real] (Fin 4 -> Real) :=
  ContinuousLinearMap.pi fun i =>
    (if i = 3 then (-1 : Real) else 1) • ContinuousLinearMap.proj i

@[simp] theorem flatReflectCLM_apply (x : Fin 4 -> Real) (i : Fin 4) :
    flatReflectCLM x i = (if i = 3 then (-1 : Real) else 1) * x i := by
  by_cases hi : i = 3 <;> simp [flatReflectCLM, hi]

/-- The flat half-space reflection as a `BoundaryReflection`. -/
def flatBoundaryReflection : BoundaryReflection (Fin 4 -> Real) where
  boundary := {x : Fin 4 -> Real | x 3 = 0}
  point := 0
  point_mem := by simp
  reflect := fun x => flatReflectCLM x
  differential := flatReflectCLM
  hasFDeriv := flatReflectCLM.hasFDerivAt
  involutive := by
    intro x
    funext i
    by_cases hi : i = 3 <;> simp [hi]
  fixesBoundary := by
    intro x hx
    have hx3 : x 3 = 0 := hx
    funext i
    by_cases hi : i = 3
    · subst hi
      simp [hx3]
    · simp [hi]
  tangent := LinearMap.ker (LinearMap.proj (3 : Fin 4) : (Fin 4 -> Real) →ₗ[Real] Real)
  normal := Pi.single (3 : Fin 4) (1 : Real)
  differential_tangent := by
    intro v hv
    have hv3 : v 3 = 0 := by simpa using hv
    funext i
    by_cases hi : i = 3
    · subst hi
      simp [hv3]
    · simp [hi]
  differential_normal := by
    funext i
    by_cases hi : i = 3
    · subst hi
      simp
    · simp [hi]

/-- The flat reflection's normal vector is transversal to its tangent space,
so the instance is genuinely non-degenerate. -/
theorem flatBoundaryReflection_normal_notMem_tangent :
    flatBoundaryReflection.normal ∉ flatBoundaryReflection.tangent := by
  intro hmem
  simp [flatBoundaryReflection] at hmem

/-- The generated reflection certificate at the flat instance. -/
def flatBoundaryReflectionCertificate (u : (Fin 4 -> Real) -> Complex)
    (Du : (Fin 4 -> Real) →L[Real] Complex) :
    BoundaryReflection.Certificate flatBoundaryReflection u Du :=
  BoundaryReflection.certificate flatBoundaryReflection u Du

end LiuWang2025SemilinearWaveBoundaryReflection
