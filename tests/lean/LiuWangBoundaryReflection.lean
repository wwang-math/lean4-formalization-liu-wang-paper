import LiuWang.LiuWang2025SemilinearWaveBoundaryReflection

open LiuWang2025SemilinearWaveBoundaryReflection
open BoundaryReflection

#check @BoundaryReflection.differential_comp_differential
#check @BoundaryReflection.difference_eq_zero_on_boundary
#check @BoundaryReflection.difference_normal_derivative
#check @BoundaryReflection.reflectedSum_normal_derivative_eq_zero
#check @BoundaryReflection.certificate

/-- The reflection argument in arbitrary geometry: exact Dirichlet
cancellation and specular doubling of the normal derivative. -/
example {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (R : BoundaryReflection E) (u : E → ℂ) (Du : E →L[ℝ] ℂ) :
    (∀ x ∈ R.boundary, R.difference u x = 0) ∧
      (Du - Du.comp R.differential) R.normal = 2 * Du R.normal :=
  ⟨fun _ hx => R.difference_eq_zero_on_boundary u hx,
   R.difference_normal_derivative Du⟩

#print axioms BoundaryReflection.differential_comp_differential
#print axioms BoundaryReflection.difference_eq_zero_on_boundary
#print axioms BoundaryReflection.difference_normal_derivative
#print axioms BoundaryReflection.certificate
