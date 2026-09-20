import LiuWang.LiuWang2025SemilinearWaveTransportHierarchy

open LiuWang2025SemilinearWaveTransportHierarchy
open LiuWang2025SemilinearWaveFermiEikonalJet

#check @hierarchyAmplitude_hasDerivAt
#check @hierarchyAmplitude_solves
#check @amplitude_zero_solves
#check @amplitude_succ_solves
#check @transport_amplitude_succ
#check @certificate

/-- The constructed amplitude solves `2 a' + q a = f` exactly. -/
example {q f : ℝ → ℂ} (hq : Continuous q) (hf : Continuous f)
    (s0 : ℝ) (initial : ℂ) (s : ℝ) :
    HasDerivAt (hierarchyAmplitude q f s0 initial)
        (-((2 : ℂ))⁻¹ * q s * hierarchyAmplitude q f s0 initial s
          + ((2 : ℂ))⁻¹ * f s) s ∧
      2 * (-((2 : ℂ))⁻¹ * q s * hierarchyAmplitude q f s0 initial s
            + ((2 : ℂ))⁻¹ * f s)
        + q s * hierarchyAmplitude q f s0 initial s = f s :=
  ⟨hierarchyAmplitude_hasDerivAt hq hf s0 initial s,
   hierarchyAmplitude_solves hq hf s0 initial s⟩

/-- The paper's recursion at the beam centre. -/
example {iota : Type} [Fintype iota] [DecidableEq iota]
    {q : ℝ → ℂ} (hq : Continuous q)
    (geom : ℝ → TransportCenterGeometry iota)
    (hcoef : ∀ tau, q tau = (geom tau).transportCoefficient)
    (s0 : ℝ) (initial : ℕ → ℂ) (boxSource : ℕ → ℝ → ℂ) (k : ℕ) (tau : ℝ)
    (dAmp : Option iota → ℂ)
    (hd : dAmp none =
      -((2 : ℂ))⁻¹ * q tau * amplitude q s0 initial boxSource (k + 1) tau
        + ((2 : ℂ))⁻¹ * (-Complex.I * boxSource k tau)) :
    (geom tau).transport (amplitude q s0 initial boxSource (k + 1) tau) dAmp
      = -Complex.I * boxSource k tau :=
  transport_amplitude_succ hq geom hcoef s0 initial boxSource k tau dAmp hd

#print axioms hierarchyAmplitude_hasDerivAt
#print axioms amplitude_succ_solves
#print axioms transport_amplitude_succ
#print axioms certificate
