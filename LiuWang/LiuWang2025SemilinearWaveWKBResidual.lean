import LiuWang.LiuWang2025SemilinearWaveEquation312EnergyClosure

/-!
# Liu--Wang 2025: WKB hierarchy and equation-(3.11) residual assembly

Section 3.1 of Liu--Wang uses

`v_rho = exp(i rho phi) a_rho`

and, after removing the nonzero exponential factor, expands the wave residual
as

`rho^2 (S phi) a_rho - i rho T(a_rho) + Box_g(a_rho)`.

The phase and amplitude jets satisfy equations (3.4)--(3.6): the eikonal jet
vanishes, the leading transport jet vanishes, and

`-i T(b_k) + Box_g(b_(k-1)) = 0`.

This module formalizes the finite WKB coefficient calculation.  In the
transverse-jet quotient in which equations (3.4)--(3.6) hold exactly, every
coefficient through order `N` cancels and only

`rho^(-N) Box_g(b_N)`

remains.  A second packet then separates the actual residual into that checked
terminal term and the eikonal Taylor, transport Taylor, and cutoff defects.
Individual paper-specific estimates for those four terms generate the full
equation-(3.11) estimate and hence instantiate the previously checked
equation-(3.11)-to-(3.12) energy/Sobolev closure.

The construction of Fermi coordinates, the positive-imaginary Riccati
solution, the phase and amplitude Taylor jets, and the Gaussian Sobolev bounds
remain geometric/analytic inputs.  The WKB coefficient cancellation and the
assembly of their separately tracked estimates are theorems.
-/

noncomputable section

open Filter Topology
open scoped BigOperators

namespace LiuWang2025SemilinearWaveWKBResidual

open LiuWang2025SemilinearWaveEquation312EnergyClosure

variable {Jet : Type*} [AddCommGroup Jet] [Module Complex Jet]

/-- Operators induced on a finite transverse Taylor-jet carrier.  The scalar
`eikonalJet` represents `S phi`, while `transport` and `wave` represent `T`
and `Box_g` on amplitude jets. -/
structure WKBJetOperators (Jet : Type*) [AddCommGroup Jet]
    [Module Complex Jet] where
  eikonalJet : Complex
  transport : Jet →ₗ[Complex] Jet
  wave : Jet →ₗ[Complex] Jet

namespace WKBJetOperators

/-- The factorized transport/wave part `-i rho T(a) + Box_g(a)`. -/
def transportWaveResidual (ops : WKBJetOperators Jet)
    (rho : Complex) (amplitude : Jet) : Jet :=
  (-Complex.I * rho) • ops.transport amplitude + ops.wave amplitude

/-- The complete factorized WKB residual
`rho^2 (S phi) a - i rho T(a) + Box_g(a)`. -/
def factorizedWaveResidual (ops : WKBJetOperators Jet)
    (rho : Complex) (amplitude : Jet) : Jet :=
  (rho ^ 2 * ops.eikonalJet) • amplitude +
    ops.transportWaveResidual rho amplitude

theorem transportWaveResidual_add (ops : WKBJetOperators Jet)
    (rho : Complex) (u v : Jet) :
    ops.transportWaveResidual rho (u + v) =
      ops.transportWaveResidual rho u +
        ops.transportWaveResidual rho v := by
  simp only [transportWaveResidual, LinearMap.map_add, smul_add]
  abel

theorem transportWaveResidual_smul (ops : WKBJetOperators Jet)
    (rho scalar : Complex) (u : Jet) :
    ops.transportWaveResidual rho (scalar • u) =
      scalar • ops.transportWaveResidual rho u := by
  simp only [transportWaveResidual, LinearMap.map_smul, smul_add, smul_smul]
  rw [mul_comm (-Complex.I * rho) scalar]

end WKBJetOperators

/-- The order-`N` amplitude
`b_0 + q b_1 + ... + q^N b_N`, where later `q = rho^-1`. -/
def truncatedAmplitude (amplitude : Nat → Jet) (q : Complex)
    (N : Nat) : Jet :=
  ∑ k ∈ Finset.range (N + 1), (q ^ k) • amplitude k

@[simp] theorem truncatedAmplitude_zero
    (amplitude : Nat → Jet) (q : Complex) :
    truncatedAmplitude amplitude q 0 = amplitude 0 := by
  simp [truncatedAmplitude]

theorem truncatedAmplitude_succ
    (amplitude : Nat → Jet) (q : Complex) (N : Nat) :
    truncatedAmplitude amplitude q (N + 1) =
      truncatedAmplitude amplitude q N +
        q ^ (N + 1) • amplitude (N + 1) := by
  simp only [truncatedAmplitude, Nat.add_assoc, Nat.reduceAdd,
    Finset.sum_range_succ]

/-- Equation-(3.4)--(3.6) data after passage to the finite transverse-jet
quotient. -/
structure WKBJetHierarchy (ops : WKBJetOperators Jet)
    (amplitude : Nat → Jet) (N : Nat) : Prop where
  eikonal : ops.eikonalJet = 0
  leadingTransport : ops.transport (amplitude 0) = 0
  recursiveTransport : ∀ k < N,
    (-Complex.I) • ops.transport (amplitude (k + 1)) +
      ops.wave (amplitude k) = 0

/-- The source transport coefficient at level zero. -/
def wkbCoefficient (ops : WKBJetOperators Jet)
    (amplitude : Nat → Jet) : Nat → Jet
  | 0 => (-Complex.I) • ops.transport (amplitude 0)
  | k + 1 =>
      (-Complex.I) • ops.transport (amplitude (k + 1)) +
        ops.wave (amplitude k)

namespace WKBJetHierarchy

variable {ops : WKBJetOperators Jet} {amplitude : Nat → Jet} {N : Nat}

theorem coefficient_zero
    (hierarchy : WKBJetHierarchy ops amplitude N)
    {k : Nat} (hk : k <= N) :
    wkbCoefficient ops amplitude k = 0 := by
  cases k with
  | zero =>
      simp [wkbCoefficient, hierarchy.leadingTransport]
  | succ k =>
      exact hierarchy.recursiveTransport k (Nat.succ_le_iff.mp hk)

private theorem shifted_transport_scalar
    (rho q : Complex) (N : Nat) (hinverse : rho * q = 1) :
    q ^ (N + 1) * (-Complex.I * rho) =
      q ^ N * (-Complex.I) := by
  have hcomm : q * rho = 1 := by
    simpa [mul_comm] using hinverse
  rw [pow_succ]
  calc
    q ^ N * q * (-Complex.I * rho) =
        q ^ N * (-Complex.I) * (q * rho) := by ring
    _ = q ^ N * (-Complex.I) := by rw [hcomm, mul_one]

/-- Exact telescoping of the transport/wave hierarchy.  This is the finite
coefficient calculation behind equations (3.5)--(3.6). -/
theorem transportWaveResidual_truncatedAmplitude_eq_terminal
    (hierarchy : WKBJetHierarchy ops amplitude N)
    {rho q : Complex} (hinverse : rho * q = 1) :
    ops.transportWaveResidual rho
        (truncatedAmplitude amplitude q N) =
      q ^ N • ops.wave (amplitude N) := by
  induction N with
  | zero =>
      simp [truncatedAmplitude_zero,
        WKBJetOperators.transportWaveResidual,
        hierarchy.leadingTransport]
  | succ N ih =>
      have prefixHierarchy : WKBJetHierarchy ops amplitude N := {
        eikonal := hierarchy.eikonal
        leadingTransport := hierarchy.leadingTransport
        recursiveTransport := fun k hk =>
          hierarchy.recursiveTransport k (Nat.lt_succ_of_lt hk)
      }
      have hpair :
          ops.wave (amplitude N) +
              (-Complex.I) • ops.transport (amplitude (N + 1)) = 0 := by
        simpa [add_comm] using
          hierarchy.recursiveTransport N (Nat.lt_succ_self N)
      have hshift :
          q ^ (N + 1) •
              ((-Complex.I * rho) •
                ops.transport (amplitude (N + 1))) =
            q ^ N •
              ((-Complex.I) •
                ops.transport (amplitude (N + 1))) := by
        simp only [smul_smul]
        rw [shifted_transport_scalar rho q N hinverse]
      rw [truncatedAmplitude_succ]
      rw [ops.transportWaveResidual_add]
      rw [ih prefixHierarchy]
      rw [ops.transportWaveResidual_smul]
      unfold WKBJetOperators.transportWaveResidual
      rw [smul_add, hshift]
      calc
        q ^ N • ops.wave (amplitude N) +
              (q ^ N • ((-Complex.I) •
                  ops.transport (amplitude (N + 1))) +
                q ^ (N + 1) • ops.wave (amplitude (N + 1))) =
            q ^ N •
                (ops.wave (amplitude N) +
                  (-Complex.I) •
                    ops.transport (amplitude (N + 1))) +
              q ^ (N + 1) • ops.wave (amplitude (N + 1)) := by
                simp only [smul_add]
                abel
        _ = q ^ (N + 1) • ops.wave (amplitude (N + 1)) := by
              rw [hpair, smul_zero, zero_add]

/-- Full source-sign WKB residual after eikonal and transport cancellation. -/
theorem factorizedWaveResidual_truncatedAmplitude_eq_terminal
    (hierarchy : WKBJetHierarchy ops amplitude N)
    {rho q : Complex} (hinverse : rho * q = 1) :
    ops.factorizedWaveResidual rho
        (truncatedAmplitude amplitude q N) =
      q ^ N • ops.wave (amplitude N) := by
  rw [WKBJetOperators.factorizedWaveResidual, hierarchy.eikonal]
  simp only [mul_zero, zero_smul, zero_add]
  exact hierarchy.transportWaveResidual_truncatedAmplitude_eq_terminal
    hinverse

end WKBJetHierarchy

variable {ForcingSpace : Type*}
  [NormedAddCommGroup ForcingSpace] [NormedSpace Complex ForcingSpace]

/-- Source-facing decomposition of the actual cutoff Gaussian-beam residual.
The WKB core is generated from the hierarchy above.  The remaining three
families make the finite Taylor and cutoff losses explicit rather than hiding
them inside one equation-(3.11) hypothesis. -/
structure Equation311ResidualAssemblyData
    (spatialDimension beamOrder residualDerivativeOrder : Nat) where
  operators : WKBJetOperators Jet
  amplitude : Nat → Jet
  hierarchy : WKBJetHierarchy operators amplitude beamOrder
  orderCondition : Equation312OrderCondition spatialDimension beamOrder
    residualDerivativeOrder
  coreToForcing : Nat → Jet →ₗ[Complex] ForcingSpace
  forcing : Nat → ForcingSpace
  eikonalTaylorDefect : Nat → ForcingSpace
  transportTaylorDefect : Nat → ForcingSpace
  cutoffDefect : Nat → ForcingSpace
  forcing_decomposition : ∀ rho,
    forcing rho =
      coreToForcing rho
          (operators.factorizedWaveResidual (rho : Complex)
            (truncatedAmplitude amplitude ((rho : Complex)⁻¹) beamOrder)) +
        eikonalTaylorDefect rho + transportTaylorDefect rho + cutoffDefect rho
  terminalConstant : Real
  eikonalConstant : Real
  transportConstant : Real
  cutoffConstant : Real
  terminalConstant_nonneg : 0 <= terminalConstant
  eikonalConstant_nonneg : 0 <= eikonalConstant
  transportConstant_nonneg : 0 <= transportConstant
  cutoffConstant_nonneg : 0 <= cutoffConstant
  terminalEstimate : ∀ᶠ rho in atTop,
    ‖coreToForcing rho
        (((rho : Complex)⁻¹) ^ beamOrder •
          operators.wave (amplitude beamOrder))‖ <=
      terminalConstant *
        equation311ResidualRate spatialDimension beamOrder
          residualDerivativeOrder rho
  eikonalTaylorEstimate : ∀ᶠ rho in atTop,
    ‖eikonalTaylorDefect rho‖ <=
      eikonalConstant *
        equation311ResidualRate spatialDimension beamOrder
          residualDerivativeOrder rho
  transportTaylorEstimate : ∀ᶠ rho in atTop,
    ‖transportTaylorDefect rho‖ <=
      transportConstant *
        equation311ResidualRate spatialDimension beamOrder
          residualDerivativeOrder rho
  cutoffEstimate : ∀ᶠ rho in atTop,
    ‖cutoffDefect rho‖ <=
      cutoffConstant *
        equation311ResidualRate spatialDimension beamOrder
          residualDerivativeOrder rho

namespace Equation311ResidualAssemblyData

variable {spatialDimension beamOrder residualDerivativeOrder : Nat}

/-- The residual constant generated by the four named source estimates. -/
def residualConstant
    (data : Equation311ResidualAssemblyData
      (Jet := Jet) (ForcingSpace := ForcingSpace)
      spatialDimension beamOrder residualDerivativeOrder) : Real :=
  data.terminalConstant + data.eikonalConstant +
    data.transportConstant + data.cutoffConstant

theorem residualConstant_nonneg
    (data : Equation311ResidualAssemblyData
      (Jet := Jet) (ForcingSpace := ForcingSpace)
      spatialDimension beamOrder residualDerivativeOrder) :
    0 <= data.residualConstant := by
  unfold residualConstant
  exact add_nonneg
    (add_nonneg
      (add_nonneg data.terminalConstant_nonneg
        data.eikonalConstant_nonneg)
      data.transportConstant_nonneg)
    data.cutoffConstant_nonneg

/-- For every positive integer frequency, the abstract WKB core is exactly
the terminal `rho^-N Box_g b_N` contribution. -/
theorem factorizedCore_eq_terminal
    (data : Equation311ResidualAssemblyData
      (Jet := Jet) (ForcingSpace := ForcingSpace)
      spatialDimension beamOrder residualDerivativeOrder)
    {rho : Nat} (hrho : 1 <= rho) :
    data.coreToForcing rho
        (data.operators.factorizedWaveResidual (rho : Complex)
          (truncatedAmplitude data.amplitude ((rho : Complex)⁻¹)
            beamOrder)) =
      data.coreToForcing rho
        (((rho : Complex)⁻¹) ^ beamOrder •
          data.operators.wave (data.amplitude beamOrder)) := by
  have hrhoZero : (rho : Complex) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hrho))
  apply congrArg (data.coreToForcing rho)
  exact data.hierarchy.factorizedWaveResidual_truncatedAmplitude_eq_terminal
    (by simp [hrhoZero])

/-- Equation (3.11) assembled from the checked WKB cancellation and the four
separately named analytic estimates. -/
theorem equation311ResidualEstimate
    (data : Equation311ResidualAssemblyData
      (Jet := Jet) (ForcingSpace := ForcingSpace)
      spatialDimension beamOrder residualDerivativeOrder) :
    ∀ᶠ rho in atTop,
      ‖data.forcing rho‖ <=
        data.residualConstant *
          equation311ResidualRate spatialDimension beamOrder
            residualDerivativeOrder rho := by
  have hrhoLarge : ∀ᶠ rho : Nat in atTop, 1 <= rho :=
    eventually_ge_atTop 1
  filter_upwards [hrhoLarge, data.terminalEstimate,
    data.eikonalTaylorEstimate, data.transportTaylorEstimate,
    data.cutoffEstimate]
      with rho hrho hterminal heikonal htransport hcutoff
  rw [data.forcing_decomposition rho]
  rw [data.factorizedCore_eq_terminal hrho]
  calc
    ‖data.coreToForcing rho
          (((rho : Complex)⁻¹) ^ beamOrder •
            data.operators.wave (data.amplitude beamOrder)) +
        data.eikonalTaylorDefect rho + data.transportTaylorDefect rho +
          data.cutoffDefect rho‖ <=
      (‖data.coreToForcing rho
          (((rho : Complex)⁻¹) ^ beamOrder •
            data.operators.wave (data.amplitude beamOrder))‖ +
        ‖data.eikonalTaylorDefect rho‖ +
          ‖data.transportTaylorDefect rho‖) +
        ‖data.cutoffDefect rho‖ := by
          calc
            ‖data.coreToForcing rho
                  (((rho : Complex)⁻¹) ^ beamOrder •
                    data.operators.wave (data.amplitude beamOrder)) +
                data.eikonalTaylorDefect rho +
                  data.transportTaylorDefect rho +
                    data.cutoffDefect rho‖ <=
                ‖data.coreToForcing rho
                    (((rho : Complex)⁻¹) ^ beamOrder •
                      data.operators.wave (data.amplitude beamOrder)) +
                    data.eikonalTaylorDefect rho +
                      data.transportTaylorDefect rho‖ +
                  ‖data.cutoffDefect rho‖ := norm_add_le _ _
            _ <=
                (‖data.coreToForcing rho
                    (((rho : Complex)⁻¹) ^ beamOrder •
                      data.operators.wave (data.amplitude beamOrder)) +
                    data.eikonalTaylorDefect rho‖ +
                  ‖data.transportTaylorDefect rho‖) +
                    ‖data.cutoffDefect rho‖ := by
              gcongr
              exact norm_add_le _ _
            _ <=
                (‖data.coreToForcing rho
                    (((rho : Complex)⁻¹) ^ beamOrder •
                      data.operators.wave (data.amplitude beamOrder))‖ +
                  ‖data.eikonalTaylorDefect rho‖ +
                    ‖data.transportTaylorDefect rho‖) +
                  ‖data.cutoffDefect rho‖ := by
              gcongr
              exact norm_add_le _ _
    _ <=
      (data.terminalConstant *
          equation311ResidualRate spatialDimension beamOrder
            residualDerivativeOrder rho +
        data.eikonalConstant *
          equation311ResidualRate spatialDimension beamOrder
            residualDerivativeOrder rho +
        data.transportConstant *
          equation311ResidualRate spatialDimension beamOrder
            residualDerivativeOrder rho) +
        data.cutoffConstant *
          equation311ResidualRate spatialDimension beamOrder
            residualDerivativeOrder rho := by
          exact add_le_add
            (add_le_add (add_le_add hterminal heikonal) htransport)
            hcutoff
    _ = data.residualConstant *
        equation311ResidualRate spatialDimension beamOrder
          residualDerivativeOrder rho := by
      unfold residualConstant
      ring

/-- The WKB assembly directly instantiates the existing equation-(3.12)
operator packet; no monolithic equation-(3.11) estimate is requested. -/
def toEquation312RemainderData
    {Omega EnergySpace ContinuousSpace : Type*}
    [NormedAddCommGroup EnergySpace] [NormedSpace Complex EnergySpace]
    [NormedAddCommGroup ContinuousSpace]
    [NormedSpace Complex ContinuousSpace]
    (data : Equation311ResidualAssemblyData
      (Jet := Jet) (ForcingSpace := ForcingSpace)
      spatialDimension beamOrder residualDerivativeOrder)
    (waveSolution : ForcingSpace →L[Complex] EnergySpace)
    (sobolevEmbedding : EnergySpace →L[Complex] ContinuousSpace)
    (pointEvaluation : Omega → ContinuousSpace →L[Complex] Complex)
    (pointEvaluation_norm_le_one : ∀ x, ‖pointEvaluation x‖ <= 1) :
    Equation312RemainderData
      (Omega := Omega) (ForcingSpace := ForcingSpace)
      (EnergySpace := EnergySpace) (ContinuousSpace := ContinuousSpace)
      spatialDimension beamOrder residualDerivativeOrder where
  orderCondition := data.orderCondition
  forcing := data.forcing
  waveSolution := waveSolution
  sobolevEmbedding := sobolevEmbedding
  pointEvaluation := pointEvaluation
  pointEvaluation_norm_le_one := pointEvaluation_norm_le_one
  residualConstant := data.residualConstant
  residualConstant_nonneg := data.residualConstant_nonneg
  equation311ResidualEstimate := data.equation311ResidualEstimate

/-- Product certificate for the WKB cancellation and residual assembly. -/
structure Certificate
    (data : Equation311ResidualAssemblyData
      (Jet := Jet) (ForcingSpace := ForcingSpace)
      spatialDimension beamOrder residualDerivativeOrder) : Prop where
  allWkbCoefficientsCancel : ∀ {k}, k <= beamOrder ->
    wkbCoefficient data.operators data.amplitude k = 0
  factorizedCoreIsTerminal : ∀ {rho : Nat}, 1 <= rho ->
    data.coreToForcing rho
        (data.operators.factorizedWaveResidual (rho : Complex)
          (truncatedAmplitude data.amplitude ((rho : Complex)⁻¹)
            beamOrder)) =
      data.coreToForcing rho
        (((rho : Complex)⁻¹) ^ beamOrder •
          data.operators.wave (data.amplitude beamOrder))
  assembledConstantNonnegative : 0 <= data.residualConstant
  equation311 : ∀ᶠ rho in atTop,
    ‖data.forcing rho‖ <=
      data.residualConstant *
        equation311ResidualRate spatialDimension beamOrder
          residualDerivativeOrder rho

def certificate
    (data : Equation311ResidualAssemblyData
      (Jet := Jet) (ForcingSpace := ForcingSpace)
      spatialDimension beamOrder residualDerivativeOrder) :
    Certificate data where
  allWkbCoefficientsCancel := fun hk => data.hierarchy.coefficient_zero hk
  factorizedCoreIsTerminal := fun hrho => data.factorizedCore_eq_terminal hrho
  assembledConstantNonnegative := data.residualConstant_nonneg
  equation311 := data.equation311ResidualEstimate

end Equation311ResidualAssemblyData

end LiuWang2025SemilinearWaveWKBResidual
