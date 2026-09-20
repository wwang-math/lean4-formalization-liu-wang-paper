import LiuWang.LiuWang2025SemilinearWaveGaussianMassScaling

open Real MeasureTheory
open LiuWang2025SemilinearWaveGaussianMassScaling

#check @integral_scaledGaussian
#check @integral_scaledGaussian_pi
#check @integral_scaledGaussian_rpow
#check @sqrt_integral_scaledGaussian
#check @integral_moment_scaledGaussian_rpow
#check @certificate

/-- Each transverse direction contributes one factor `(sqrt rho)⁻¹`. -/
example {b rho : ℝ} (hb : 0 < b) (hrho : 0 < rho) :
    (∫ x : ℝ, Real.exp (-(b * rho) * x ^ 2))
      = Real.sqrt (Real.pi / b) / Real.sqrt rho :=
  integral_scaledGaussian hb hrho

/-- The squared transverse mass carries `rho^{-d/2}`, the `L^2` norm
`rho^{-d/4}`. -/
example {d : ℕ} {b rho : ℝ} (hb : 0 < b) (hrho : 0 < rho) :
    Real.sqrt (∫ z : Fin d → ℝ, Real.exp (-(b * rho) * radiusSq z))
      = Real.sqrt (Real.sqrt (Real.pi / b) ^ d) * rho ^ (-(d : ℝ) / 4) :=
  sqrt_integral_scaledGaussian hb hrho

#print axioms integral_scaledGaussian
#print axioms integral_scaledGaussian_pi
#print axioms integral_scaledGaussian_rpow
#print axioms sqrt_integral_scaledGaussian
/-- Each transverse coordinate factor costs one half-power of the frequency. -/
example (m : ℕ) {b rho : ℝ} (hb : 0 < b) (hrho : 0 < rho) :
    (∫ x : ℝ, x ^ (2 * m) * Real.exp (-(b * rho) * x ^ 2))
      = rho ^ (-((m : ℝ) + 1 / 2))
        * ∫ y : ℝ, y ^ (2 * m) * Real.exp (-b * y ^ 2) :=
  integral_moment_scaledGaussian_rpow m hb hrho

#print axioms integral_moment_scaledGaussian_rpow
#print axioms certificate
