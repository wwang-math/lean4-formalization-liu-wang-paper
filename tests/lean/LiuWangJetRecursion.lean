import LiuWang.LiuWang2025SemilinearWaveJetAmplitudeHierarchy
import LiuWang.LiuWang2025SemilinearWaveJetOperators
import LiuWang.LiuWang2025SemilinearWaveMetricJetPhaseHierarchy

/-! Focused regression file for the triangular longitudinal recursion: the
longitudinal jet layer, the jet-level operators, the constructed phase tower and
amplitude hierarchy, and the realization of the constructed coefficients as
chart polynomials. -/

open LiuWang2025SemilinearWaveTransverseJet
open LiuWang2025SemilinearWaveLongitudinalJet
open LiuWang2025SemilinearWaveLongitudinalJet.LongJet
open LiuWang2025SemilinearWaveJetTowerRecursion
open LiuWang2025SemilinearWaveJetTowerRecursion.TowerData
open LiuWang2025SemilinearWaveJetAmplitudeHierarchy
open LiuWang2025SemilinearWaveJetOperators
open LiuWang2025SemilinearWaveTransportHierarchy
open LiuWang2025SemilinearWaveMetricJetPhaseHierarchy

-- The longitudinal jet layer and its operations.
#check @LiuWang2025SemilinearWaveLongitudinalJet.LongJet
#check @LiuWang2025SemilinearWaveLongitudinalJet.LongJet.mul
#check @LiuWang2025SemilinearWaveLongitudinalJet.LongJet.mul_dc
#check @LiuWang2025SemilinearWaveLongitudinalJet.LongJet.transverseDeriv
#check @LiuWang2025SemilinearWaveLongitudinalJet.LongJet.truncate
#check @LiuWang2025SemilinearWaveLongitudinalJet.monomial_mul_sub
#check @LiuWang2025SemilinearWaveLongitudinalJet.jmul_coeff_eq
#check @LiuWang2025SemilinearWaveLongitudinalJet.hasDerivAt_monomial
#check @LiuWang2025SemilinearWaveLongitudinalJet.hasDerivAt_chartValue_longitudinal
#check @LiuWang2025SemilinearWaveLongitudinalJet.hasDerivAt_realize_transverse
#check @LiuWang2025SemilinearWaveLongitudinalJet.realize_at_origin
#check @LiuWang2025SemilinearWaveLongitudinalJet.realize_transverse_deriv_at_origin

-- The recursion.
#check @LiuWang2025SemilinearWaveJetTowerRecursion.TowerData
#check @LiuWang2025SemilinearWaveJetTowerRecursion.TowerData.tower
#check @LiuWang2025SemilinearWaveJetTowerRecursion.TowerData.tower_stable
#check @LiuWang2025SemilinearWaveJetTowerRecursion.TowerData.tower_continuous
#check @LiuWang2025SemilinearWaveJetTowerRecursion.TowerData.tower_hasDerivAt
#check @LiuWang2025SemilinearWaveJetTowerRecursion.TowerData.tower_src_stable
#check @LiuWang2025SemilinearWaveJetTowerRecursion.TowerData.towerDeriv_hasDerivAt
#check @LiuWang2025SemilinearWaveJetTowerRecursion.towerCoefficient_eq_zero
#check @LiuWang2025SemilinearWaveJetTowerRecursion.towerCoefficient_eq_zero_of_le_base
#check @LiuWang2025SemilinearWaveJetTowerRecursion.towerCoefficient_eq_zero_of_le

-- The amplitude hierarchy.
#check @LiuWang2025SemilinearWaveJetAmplitudeHierarchy.HierarchyData
#check @LiuWang2025SemilinearWaveJetAmplitudeHierarchy.HierarchyData.amplitude
#check @LiuWang2025SemilinearWaveJetAmplitudeHierarchy.HierarchyData.amplitude_hasDerivAt
#check @LiuWang2025SemilinearWaveJetAmplitudeHierarchy.HierarchyData.amplitude_coefficient_eq_zero

-- The jet-level operators.
#check @LiuWang2025SemilinearWaveJetOperators.jetEikonal
#check @LiuWang2025SemilinearWaveJetOperators.below_zero
#check @LiuWang2025SemilinearWaveJetOperators.jetEikonal_coeff_zero
#check @LiuWang2025SemilinearWaveJetOperators.jetEikonal_coeff_zero_eq_zero
#check @LiuWang2025SemilinearWaveJetOperators.deg_add_deg_sub
#check @LiuWang2025SemilinearWaveJetOperators.mul_c_eq_zero_of_deg_lt
#check @LiuWang2025SemilinearWaveJetOperators.below_single
#check @LiuWang2025SemilinearWaveJetOperators.mul_c_single
#check @LiuWang2025SemilinearWaveJetOperators.jetEikonal_coeff_one
#check @LiuWang2025SemilinearWaveJetOperators.jetEikonal_coeff_one_eq_zero

/-! ## Non-vacuity

These are witnesses that the recursion data is inhabited by systems with a
*non-zero* longitudinal coefficient and a *non-zero* source, and that the
constructed coefficient is not the zero function.  They are not claimed to be
the paper's eikonal or transport system. -/

/-- A triangular system with non-zero longitudinal coefficient and non-zero
source: `2 c' + c = 1`. -/
def demoTower : TowerData 1 where
  q := fun _ _ => 1
  hq := fun _ => continuous_const
  src := fun _ _ _ _ => 1
  hsrc := fun _ _ _ _ => continuous_const
  src_lower := fun _ _ _ _ _ => rfl

/-- The multi-index of total degree one in one transverse variable. -/
def demoIndex : Multiindex 1 := fun _ => 1

example : deg demoIndex = 1 := by
  simp [deg, demoIndex]

/-- The constructed degree-one coefficient is the integrating-factor solution,
not zero: at the initial parameter it takes the prescribed value `1`. -/
example (s0 : Real) :
    TowerData.tower demoTower s0 (fun _ => 1) (fun _ _ => 0) 0 1 demoIndex s0 = 1 := by
  have hd : deg demoIndex = 0 + 0 + 1 := by simp [deg, demoIndex]
  rw [TowerData.tower_succ, if_pos hd, hierarchyAmplitude_at_initial]

/-- The prescribed degrees really are kept by the recursion. -/
example (s0 : Real) (base : Multiindex 1 -> Real -> Complex) (R : Nat) :
    TowerData.tower demoTower s0 (fun _ => 1) base 0 R (0 : Multiindex 1) = base 0 :=
  TowerData.tower_of_deg_le_base demoTower s0 (fun _ => 1) base 0 R (by simp [deg])

/-- An amplitude hierarchy whose source genuinely reads the previous frequency
order, so the double recursion is not degenerate. -/
def demoHierarchy : HierarchyData 1 where
  q := fun _ _ => 1
  hq := fun _ => continuous_const
  src := fun _ prev _ a s => prev a s + 1
  hsrc := fun _ _ _ a hprev _ => (hprev a).add continuous_const
  src_lower := fun _ _ _ _ _ _ => rfl

example (s0 : Real) : ∀ a, Continuous
    (demoHierarchy.amplitude s0 (fun _ _ => 1) (fun _ _ _ => 0)
      (fun _ _ => continuous_const) 0 2 3 a) :=
  demoHierarchy.amplitude_continuous s0 (fun _ _ => 1) (fun _ _ _ => 0)
    (fun _ _ => continuous_const) 0 2 3

/-- The jet-level eikonal really collapses at the beam centre to a single
metric coefficient. -/
example (Ass : LongJet 1) (Bs : Fin 1 -> LongJet 1)
    (Att : Fin 1 -> Fin 1 -> LongJet 1) (phi dphi : LongJet 1) (s : Real)
    (h0 : dphi.c 0 s = 0)
    (h1 : ∀ i, phi.c (Pi.single i 1) s = if i = (0 : Fin 1) then 1 else 0) :
    jetEikonal Ass Bs Att phi dphi 0 s = (Att 0 0).c 0 s :=
  jetEikonal_coeff_zero Ass Bs Att phi dphi 0 s h0 h1

#print axioms LiuWang2025SemilinearWaveLongitudinalJet.LongJet.mul_dc
#print axioms LiuWang2025SemilinearWaveLongitudinalJet.monomial_mul_sub
#print axioms LiuWang2025SemilinearWaveLongitudinalJet.jmul_coeff_eq
#print axioms LiuWang2025SemilinearWaveLongitudinalJet.hasDerivAt_monomial
#print axioms LiuWang2025SemilinearWaveLongitudinalJet.hasDerivAt_chartValue_longitudinal
#print axioms LiuWang2025SemilinearWaveLongitudinalJet.realize_at_origin
#print axioms LiuWang2025SemilinearWaveLongitudinalJet.realize_transverse_deriv_at_origin
#print axioms LiuWang2025SemilinearWaveJetTowerRecursion.TowerData.tower
#print axioms LiuWang2025SemilinearWaveJetTowerRecursion.TowerData.tower_stable
#print axioms LiuWang2025SemilinearWaveJetTowerRecursion.TowerData.tower_hasDerivAt
#print axioms LiuWang2025SemilinearWaveJetTowerRecursion.TowerData.towerDeriv_hasDerivAt
#print axioms LiuWang2025SemilinearWaveJetTowerRecursion.towerCoefficient_eq_zero_of_le
#print axioms LiuWang2025SemilinearWaveJetAmplitudeHierarchy.HierarchyData.amplitude
#print axioms LiuWang2025SemilinearWaveJetAmplitudeHierarchy.HierarchyData.amplitude_hasDerivAt
#print axioms LiuWang2025SemilinearWaveJetAmplitudeHierarchy.HierarchyData.amplitude_coefficient_eq_zero
#print axioms LiuWang2025SemilinearWaveJetOperators.jetEikonal_coeff_zero
#print axioms LiuWang2025SemilinearWaveJetOperators.jetEikonal_coeff_zero_eq_zero

#print axioms LiuWang2025SemilinearWaveJetOperators.deg_add_deg_sub
#print axioms LiuWang2025SemilinearWaveJetOperators.mul_c_eq_zero_of_deg_lt
#print axioms LiuWang2025SemilinearWaveJetOperators.below_single
#print axioms LiuWang2025SemilinearWaveJetOperators.mul_c_single
#print axioms LiuWang2025SemilinearWaveJetOperators.jetEikonal_coeff_one
#print axioms LiuWang2025SemilinearWaveJetOperators.jetEikonal_coeff_one_eq_zero

/-! ## The normalization audit and locality -/

#check @LiuWang2025SemilinearWaveLongitudinalJet.degreeLE
#check @LiuWang2025SemilinearWaveLongitudinalJet.mem_degreeLE
#check @LiuWang2025SemilinearWaveLongitudinalJet.deg_add_single
#check @LiuWang2025SemilinearWaveLongitudinalJet.deg_sub_single
#check @LiuWang2025SemilinearWaveLongitudinalJet.monomial_sub_single
#check @LiuWang2025SemilinearWaveLongitudinalJet.hasDerivAt_realize_jderiv
#check @LiuWang2025SemilinearWaveJetOperators.mul_c_congr
#check @LiuWang2025SemilinearWaveJetOperators.transverseDeriv_c_congr
#check @LiuWang2025SemilinearWaveJetOperators.jetEikonal_congr

/-! ## The Fermi metric jet -/

#check @LiuWang2025SemilinearWaveMetricJetPhaseHierarchy.FermiMetricJet
#check @LiuWang2025SemilinearWaveMetricJetPhaseHierarchy.SourcePhaseJet
#check @LiuWang2025SemilinearWaveMetricJetPhaseHierarchy.SourcePhaseJet.dphi_zero
#check @LiuWang2025SemilinearWaveMetricJetPhaseHierarchy.SourcePhaseJet.dphi_one
#check @LiuWang2025SemilinearWaveMetricJetPhaseHierarchy.SourcePhaseJet.eikonal_deg_zero
#check @LiuWang2025SemilinearWaveMetricJetPhaseHierarchy.SourcePhaseJet.eikonal_deg_one
#check @LiuWang2025SemilinearWaveMetricJetPhaseHierarchy.SourcePhaseJet.eikonal_local

/-! ## Non-vacuity: a genuinely non-constant, off-diagonal metric jet

The transverse block carries an `s`-dependent coefficient, the
longitudinal-transverse block carries a nonzero degree-one coefficient off the
distinguished direction, and the phase carries a nonzero `s`-dependent
degree-two coefficient.  None of the three is constant or zero. -/

/-- `s |-> s`, complexified, with its derivative. -/
theorem hasDerivAt_ofRealId (s : Real) :
    HasDerivAt (fun u : Real => ((u : Real) : Complex)) 1 s := by
  simpa using (hasDerivAt_id s).ofReal_comp

/-- A transverse block coefficient that genuinely varies along the geodesic. -/
def demoVarying : LongJet 2 :=
  singleJet 0 (fun s => ((s : Real) : Complex)) (fun _ => 1) hasDerivAt_ofRealId

/-- A longitudinal-transverse coefficient with a nonzero *degree-one* entry. -/
def demoOffDiagonal : LongJet 2 :=
  singleJet (Pi.single 0 1) (fun _ => 1) (fun _ => 0)
    (fun s => hasDerivAt_const s (1 : Complex))

/-- The unit longitudinal pairing. -/
def demoUnit : LongJet 2 :=
  singleJet 0 (fun _ => 1) (fun _ => 0) (fun s => hasDerivAt_const s (1 : Complex))

/-- A Fermi metric jet that is neither zero nor constant. -/
def demoMetric : FermiMetricJet 2 where
  Ass := zeroJet 2
  Bs := fun i => if i = 0 then demoUnit else demoOffDiagonal
  Att := fun i j => if i = 0 then zeroJet 2 else if j = 0 then zeroJet 2 else demoVarying
  i1 := 0
  nullRow := by intro j s; simp
  nullCol := by
    intro i s
    by_cases h : i = 0 <;> simp [h]
  nullSecondOrder := by intro k s; simp
  longitudinalNormalization := by intro s; simp [demoUnit]

/-- The transverse block really varies along the geodesic. -/
example : (demoMetric.Att 1 1).c 0 1 ≠ (demoMetric.Att 1 1).c 0 0 := by
  simp [demoMetric, demoVarying]

/-- The longitudinal-transverse block really has a nonzero degree-one
coefficient off the distinguished direction. -/
example (s : Real) : (demoMetric.Bs 1).c (Pi.single 0 1) s = 1 := by
  simp [demoMetric, demoOffDiagonal]

/-- The degree-two multi-index `z_1^2`. -/
def demoQuadIndex : Multiindex 2 := Pi.single 1 2

example : deg demoQuadIndex = 2 := by
  simp [deg, demoQuadIndex, Pi.single_apply]

/-- A phase jet with the source's prescribed low degrees and a genuinely
`s`-dependent degree-two coefficient. -/
def demoPhiJet : LongJet 2 where
  c := fun a s =>
    if a = (Pi.single 0 1 : Multiindex 2) then 1
    else if a = demoQuadIndex then ((s : Real) : Complex) else 0
  dc := fun a s =>
    if a = (Pi.single 0 1 : Multiindex 2) then 0
    else if a = demoQuadIndex then 1 else 0
  hasDeriv := by
    intro a s
    by_cases h1 : a = (Pi.single 0 1 : Multiindex 2)
    · simpa [h1] using hasDerivAt_const s (1 : Complex)
    · by_cases h2 : a = demoQuadIndex
      · simpa [h1, h2] using hasDerivAt_ofRealId s
      · simpa [h1, h2] using hasDerivAt_const s (0 : Complex)

/-- It satisfies the source's low-order prescription, so `SourcePhaseJet` is
inhabited by something that is not the zero jet. -/
def demoPhase : SourcePhaseJet demoMetric where
  phi := demoPhiJet
  dphi := { c := demoPhiJet.dc
            dc := fun _ _ => 0
            hasDeriv := by
              intro a s
              by_cases h1 : a = (Pi.single 0 1 : Multiindex 2)
              · simpa [demoPhiJet, h1] using hasDerivAt_const s (0 : Complex)
              · by_cases h2 : a = demoQuadIndex
                · simpa [demoPhiJet, h1, h2] using hasDerivAt_const s (1 : Complex)
                · simpa [demoPhiJet, h1, h2] using hasDerivAt_const s (0 : Complex) }
  dphi_is_deriv := demoPhiJet.hasDeriv
  phi_zero := by
    intro s
    have h1 : (0 : Multiindex 2) ≠ (Pi.single 0 1 : Multiindex 2) := by decide
    have h2 : (0 : Multiindex 2) ≠ demoQuadIndex := by decide
    simp [demoPhiJet, h1, h2]
  phi_one := by
    intro i s
    by_cases hi : i = 0
    · subst hi
      simp [demoPhiJet, demoMetric]
    · have hi1 : i = 1 := by omega
      subst hi1
      have h1 : (Pi.single (1 : Fin 2) 1 : Multiindex 2)
          ≠ (Pi.single 0 1 : Multiindex 2) := by decide
      have h2 : (Pi.single (1 : Fin 2) 1 : Multiindex 2) ≠ demoQuadIndex := by decide
      simp [demoPhiJet, demoMetric, h1, h2]

/-- The phase really carries a nonzero, `s`-dependent degree-two coefficient. -/
example : demoPhase.phi.c demoQuadIndex 1 ≠ demoPhase.phi.c demoQuadIndex 0 := by
  have h1 : demoQuadIndex ≠ (Pi.single 0 1 : Multiindex 2) := by decide
  simp [demoPhase, demoPhiJet, h1]

/-- The degree-zero and degree-one eikonal cancellations hold for this genuinely
non-constant metric jet. -/
example (s : Real) :
    jetEikonal demoMetric.Ass demoMetric.Bs demoMetric.Att demoPhase.phi
      demoPhase.dphi 0 s = 0 :=
  demoPhase.eikonal_deg_zero s

example (k : Fin 2) (s : Real) :
    jetEikonal demoMetric.Ass demoMetric.Bs demoMetric.Att demoPhase.phi
      demoPhase.dphi (Pi.single k 1) s = 0 :=
  demoPhase.eikonal_deg_one k s

#print axioms LiuWang2025SemilinearWaveLongitudinalJet.hasDerivAt_realize_jderiv
#print axioms LiuWang2025SemilinearWaveLongitudinalJet.deg_add_single
#print axioms LiuWang2025SemilinearWaveLongitudinalJet.deg_sub_single
#print axioms LiuWang2025SemilinearWaveJetOperators.mul_c_congr
#print axioms LiuWang2025SemilinearWaveJetOperators.jetEikonal_congr
#print axioms LiuWang2025SemilinearWaveMetricJetPhaseHierarchy.SourcePhaseJet.dphi_zero
#print axioms LiuWang2025SemilinearWaveMetricJetPhaseHierarchy.SourcePhaseJet.dphi_one
#print axioms LiuWang2025SemilinearWaveMetricJetPhaseHierarchy.SourcePhaseJet.eikonal_deg_zero
#print axioms LiuWang2025SemilinearWaveMetricJetPhaseHierarchy.SourcePhaseJet.eikonal_deg_one
#print axioms LiuWang2025SemilinearWaveMetricJetPhaseHierarchy.SourcePhaseJet.eikonal_local
#check @LiuWang2025SemilinearWaveJetOperators.deg_lt_of_mem_below_ne
#check @LiuWang2025SemilinearWaveJetOperators.mul_c_vanish
#check @LiuWang2025SemilinearWaveJetOperators.mul_c_top
#check @LiuWang2025SemilinearWaveJetOperators.mul_c_bot
#check @LiuWang2025SemilinearWaveJetOperators.eq_single_of_deg_eq_one
#check @LiuWang2025SemilinearWaveJetOperators.transverseDeriv_vanish
#check @LiuWang2025SemilinearWaveJetOperators.jetEikonal_congr_of_deg_le
#check @LiuWang2025SemilinearWaveJetOperators.jetEikonal_longitudinal_extraction
#check @LiuWang2025SemilinearWaveMetricJetPhaseHierarchy.eikonal_triangular
#check @LiuWang2025SemilinearWaveMetricJetPhaseHierarchy.eikonal_longitudinal
#check @LiuWang2025SemilinearWaveMetricJetPhaseHierarchy.eikonal_longitudinal_normalized

/-- Triangularity applies to the genuinely non-constant demo metric. -/
example (P P' : SourcePhaseJet demoMetric) (a : Multiindex 2) (s : Real)
    (ha : 1 ≤ deg a)
    (hphi : ∀ b, deg b ≤ deg a -> P.phi.c b s = P'.phi.c b s)
    (hdphi : ∀ b, deg b ≤ deg a -> P.dphi.c b s = P'.dphi.c b s) :
    jetEikonal demoMetric.Ass demoMetric.Bs demoMetric.Att P.phi P.dphi a s
      = jetEikonal demoMetric.Ass demoMetric.Bs demoMetric.Att P'.phi P'.dphi a s :=
  LiuWang2025SemilinearWaveMetricJetPhaseHierarchy.eikonal_triangular P P' ha
    hphi hdphi

#print axioms LiuWang2025SemilinearWaveJetOperators.mul_c_top
#print axioms LiuWang2025SemilinearWaveJetOperators.mul_c_bot
#print axioms LiuWang2025SemilinearWaveJetOperators.eq_single_of_deg_eq_one
#print axioms LiuWang2025SemilinearWaveJetOperators.jetEikonal_congr_of_deg_le
#print axioms LiuWang2025SemilinearWaveJetOperators.jetEikonal_longitudinal_extraction
#print axioms LiuWang2025SemilinearWaveMetricJetPhaseHierarchy.eikonal_triangular
#print axioms LiuWang2025SemilinearWaveMetricJetPhaseHierarchy.eikonal_longitudinal
#print axioms LiuWang2025SemilinearWaveMetricJetPhaseHierarchy.eikonal_longitudinal_normalized
#print axioms demoMetric
#print axioms demoPhase
