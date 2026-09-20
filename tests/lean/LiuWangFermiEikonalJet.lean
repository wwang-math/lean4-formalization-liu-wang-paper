import LiuWang.LiuWang2025SemilinearWaveFermiEikonalJet

open LiuWang2025SemilinearWaveFermiEikonalJet
open LiuWang2025SemilinearWaveRiccatiFlow

#check @eikonal_center_eq_zero
#check @eikonal_firstJet_eq_zero
#check @eikonal_secondJet_eq
#check @eikonal_secondJet_eq_zero_of_riccati
#check @eikonal_secondJet_eq_zero_of_riccatiFlow
#check @FermiEikonalFamily.riccati_of_eikonal_secondJet_eq_zero
#check @TransportCenterGeometry.transport_eq
#check @fermiTransportCertificate

/-- The transverse 2-jet of the eikonal symbol is the paper's Riccati
expression, contracted with the chosen direction. -/
example {iota : Type} [Fintype iota] [DecidableEq iota]
    {L : MetricLineJet iota} {F : FermiPhaseLine iota}
    {C D : Matrix iota iota Complex} (hN : FermiNormalization L F C D) :
    eikonalDeriv₂ L F.gradJet 0 =
      4 * quadForm (F.dM + F.M * C * F.M + D) F.dir :=
  eikonal_secondJet_eq hN

/-- The transverse jet is a jet of genuine derivatives of the eikonal
symbol along the transverse line. -/
example {iota : Type} [Fintype iota] [DecidableEq iota]
    (L : MetricLineJet iota) (F : FermiPhaseLine iota) (t : Real) :
    HasDerivAt (eikonal L F.gradJet) (eikonalDeriv L F.gradJet t) t ∧
      HasDerivAt (eikonalDeriv L F.gradJet) (eikonalDeriv₂ L F.gradJet t) t :=
  ⟨hasDerivAt_eikonal L F.gradJet t, hasDerivAt_eikonalDeriv L F.gradJet t⟩

/-- A Riccati flow supplies the eikonal condition at every interval point. -/
example {iota : Type} [Fintype iota] [DecidableEq iota]
    {L : MetricLineJet iota} {F : FermiPhaseLine iota}
    {C D : Matrix iota iota Complex} (hN : FermiNormalization L F C D)
    (flow : RiccatiFlow iota) {t : Real}
    (ht : t ∈ Set.uIcc flow.startTime flow.endTime)
    (hM : F.M = flow.H t) (hdM : F.dM = flow.dH t)
    (hC : C = flow.C t) (hD : D = flow.D t) :
    eikonalDeriv₂ L F.gradJet 0 = 0 :=
  eikonal_secondJet_eq_zero_of_riccatiFlow hN flow ht hM hdM hC hD

/-- The transport operator at the beam centre is the scalar transport ODE
with the paper's coefficient `Tr(C M) + beta_1`. -/
example {iota : Type} [Fintype iota] [DecidableEq iota]
    (g : TransportCenterGeometry iota) (amp : Complex)
    (dAmp : Option iota → Complex) :
    g.transport amp dAmp
      = 2 * dAmp none - (Matrix.trace (g.C * g.M) + g.beta (some g.i1)) * amp :=
  g.transport_eq amp dAmp

#print axioms eikonal_center_eq_zero
#print axioms eikonal_firstJet_eq_zero
#print axioms eikonal_secondJet_eq
#print axioms eikonal_secondJet_eq_zero_of_riccatiFlow
#print axioms FermiEikonalFamily.riccati_of_eikonal_secondJet_eq_zero
#print axioms TransportCenterGeometry.transport_eq
#print axioms fermiTransportCertificate
