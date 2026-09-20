import LiuWang.LiuWang2025SemilinearWaveRiccatiPhaseBridge

/-!
# An explicit paper-style instance of the Riccati phase bridge

`LiuWang2025SemilinearWaveRiccatiPhaseBridge.exists_phase_from_riccati` produces
a phase from metric and Riccati input alone.  This file exhibits an explicit
transverse-dimension-three instance of *all* of its hypotheses, so the endpoint
is not vacuous.

The data is the source's own normal form: the distinguished direction is
`i1 = 0`, the paper matrix is `C = diag(0, 2, 2)` (so the degree-zero transverse
block is `C/2 = diag(0,1,1)`, which is exactly the Fermi null row and column
together with a flat transverse metric), all first transverse derivatives of the
metric vanish, and the degree-two coefficients of `A^{i1 i1}` encode a *nonzero*
real symmetric `D`.  The example therefore has genuine curvature: `D = 0` would
make it a flat toy, and `metricD` is proved to be the chosen nonzero `D`.
-/

noncomputable section

open scoped BigOperators
open scoped Matrix.Norms.L2Operator
open Set

namespace LiuWang2025SemilinearWaveRiccatiPhaseExample

open LiuWang2025SemilinearWaveTransverseJet
open LiuWang2025SemilinearWaveLongitudinalJet
open LiuWang2025SemilinearWaveLongitudinalJet.LongJet
open LiuWang2025SemilinearWaveJetOperators
open LiuWang2025SemilinearWaveDegreeBlock
open LiuWang2025SemilinearWaveMetricJetPhaseHierarchy
open LiuWang2025SemilinearWaveRiccatiPhase
open LiuWang2025SemilinearWaveRiccatiPhaseBridge

/-! ## Constant jets -/

/-- A jet whose coefficients do not vary along the geodesic. -/
def constJet {d : Nat} (f : Multiindex d -> Complex) : LongJet d where
  c := fun a _ => f a
  dc := fun _ _ => 0
  hasDeriv := fun a s => hasDerivAt_const s (f a)

@[simp] theorem constJet_c {d : Nat} (f : Multiindex d -> Complex)
    (a : Multiindex d) (s : Real) : (constJet f).c a s = f a := rfl

theorem constJet_C1 {d : Nat} (f : Multiindex d -> Complex) :
    (constJet f).C1 := fun _ => continuous_const

/-! ## The example data -/

/-- The paper matrix `C = diag(0, 2, 2)`. -/
def exC (p q : Fin 3) : Complex := if p = q then (if p = 0 then 0 else 2) else 0

/-- A nonzero real symmetric `D`. -/
def exD (p q : Fin 3) : Complex := if p = q then 1 else 0

theorem exD_symm (p q : Fin 3) : exD p q = exD q p := by
  by_cases h : p = q
  · rw [h]
  · rw [exD, exD, if_neg h, if_neg (Ne.symm h)]

theorem exD_ne_zero : exD 0 0 ≠ 0 := by
  rw [exD, if_pos rfl]
  exact one_ne_zero

/-- The degree-zero transverse block, `C / 2 = diag(0,1,1)`. -/
def exC0 (p q : Fin 3) : Complex := if p = q then (if p = 0 then 0 else 1) else 0

theorem exC0_symm (p q : Fin 3) : exC0 p q = exC0 q p := by
  by_cases h : p = q
  · rw [h]
  · rw [exC0, exC0, if_neg h, if_neg (Ne.symm h)]

/-- The transverse metric block.  Off `(0,0)` it is the constant `C/2`; at
`(0,0)` it vanishes to second order and its degree-two coefficients are
`quadCoeff (2 D)`. -/
def exAtt (i j : Fin 3) : LongJet 3 :=
  if i = 0 ∧ j = 0 then
    constJet fun b => if deg b = 2 then 2 * quadCoeff exD b else 0
  else constJet fun b => if b = 0 then exC0 i j else 0

theorem exAtt_c_zero (i j : Fin 3) (s : Real) :
    (exAtt i j).c 0 s = exC0 i j := by
  by_cases h : i = 0 ∧ j = 0
  · rw [exAtt, if_pos h, constJet_c, if_neg (by rw [deg_zero_index]; omega),
      exC0, h.1, h.2, if_pos rfl, if_pos rfl]
  · rw [exAtt, if_neg h, constJet_c, if_pos rfl]

theorem exAtt_c_deg_one (i j : Fin 3) {b : Multiindex 3} (hb : deg b = 1)
    (s : Real) : (exAtt i j).c b s = 0 := by
  have hbne : b ≠ 0 := by
    intro hcon
    rw [hcon, deg_zero_index] at hb
    omega
  by_cases h : i = 0 ∧ j = 0
  · rw [exAtt, if_pos h, constJet_c, if_neg (by omega)]
  · rw [exAtt, if_neg h, constJet_c, if_neg hbne]

theorem exAtt_c_deg_two (i j : Fin 3) {b : Multiindex 3} (hb : deg b = 2)
    (s : Real) :
    (exAtt i j).c b s = if i = 0 ∧ j = 0 then 2 * quadCoeff exD b else 0 := by
  have hbne : b ≠ 0 := by
    intro hcon
    rw [hcon, deg_zero_index] at hb
    omega
  by_cases h : i = 0 ∧ j = 0
  · rw [exAtt, if_pos h, constJet_c, if_pos hb, if_pos h]
  · rw [exAtt, if_neg h, constJet_c, if_neg hbne, if_neg h]

theorem exAtt_symm (i j : Fin 3) (b : Multiindex 3) (s : Real) :
    (exAtt i j).c b s = (exAtt j i).c b s := by
  by_cases h : i = 0 ∧ j = 0
  · rw [h.1, h.2]
  · have h' : ¬(j = 0 ∧ i = 0) := fun hc => h ⟨hc.2, hc.1⟩
    rw [exAtt, exAtt, if_neg h, if_neg h', constJet_c, constJet_c]
    by_cases hb : b = 0
    · rw [if_pos hb, if_pos hb, exC0_symm]
    · rw [if_neg hb, if_neg hb]

theorem exAtt_real (i j : Fin 3) (b : Multiindex 3) (s : Real) :
    (starRingEnd Complex) ((exAtt i j).c b s) = (exAtt i j).c b s := by
  have hC0 : ∀ p q : Fin 3, (starRingEnd Complex) (exC0 p q) = exC0 p q := by
    intro p q
    by_cases h : p = q
    · rw [exC0, if_pos h]
      by_cases h0 : p = 0 <;> simp [h0]
    · rw [exC0, if_neg h]
      simp
  have hD : ∀ a : Multiindex 3,
      (starRingEnd Complex) (2 * quadCoeff exD a) = 2 * quadCoeff exD a := by
    intro a
    have hreal : ∀ p q : Fin 3, (starRingEnd Complex) (exD p q) = exD p q := by
      intro p q
      by_cases h : p = q <;> simp [exD, h]
    rw [quadCoeff, map_mul, show (starRingEnd Complex) 2 = 2 from map_ofNat _ _]
    congr 1
    rw [map_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    by_cases h : (Pi.single p 1 + Pi.single q 1 : Multiindex 3) = a
    · rw [if_pos h]
      exact hreal p q
    · rw [if_neg h, map_zero]
  by_cases h : i = 0 ∧ j = 0
  · rw [exAtt, if_pos h, constJet_c]
    by_cases hb : deg b = 2
    · rw [if_pos hb]
      exact hD b
    · rw [if_neg hb, map_zero]
  · rw [exAtt, if_neg h, constJet_c]
    by_cases hb : b = 0
    · rw [if_pos hb]
      exact hC0 i j
    · rw [if_neg hb, map_zero]

/-- The longitudinal-transverse block: the unit pairing in the distinguished
direction, zero otherwise. -/
def exBs (i : Fin 3) : LongJet 3 :=
  if i = 0 then constJet (fun b => if b = 0 then 1 else 0)
  else constJet (fun _ => 0)

/-- The example Fermi metric jet. -/
def exMetric : FermiMetricJet 3 where
  Ass := constJet fun _ => 0
  Bs := exBs
  Att := exAtt
  i1 := 0
  nullRow := by
    intro j s
    rw [exAtt_c_zero, exC0]
    by_cases h : (0 : Fin 3) = j <;> simp [h]
  nullCol := by
    intro i s
    rw [exAtt_c_zero, exC0]
    by_cases h : i = (0 : Fin 3) <;> simp [h]
  nullSecondOrder := by
    intro k s
    exact exAtt_c_deg_one 0 0 (deg_single k) s
  longitudinalNormalization := by
    intro s
    rw [exBs, if_pos rfl, constJet_c, if_pos rfl]

theorem exMetric_i1 : exMetric.i1 = 0 := rfl

theorem exMetric_Att (i j : Fin 3) : exMetric.Att i j = exAtt i j := rfl

/-- **The example satisfies the bridge's metric hypotheses.** -/
theorem exFermiData : FermiQuadraticData exMetric where
  firstOrderVanishing := fun i j k s =>
    exAtt_c_deg_one i j (deg_single k) s
  attSymm := fun i j b s => exAtt_symm i j b s
  attReal := fun i j b s => exAtt_real i j b s
  attC1 := by
    intro i j
    rw [exMetric_Att, exAtt]
    by_cases h : i = 0 ∧ j = 0
    · rw [if_pos h]
      exact constJet_C1 _
    · rw [if_neg h]
      exact constJet_C1 _

/-! ## `C` and `D` for the example -/

/-- **`metricC` is literally `diag(0, 2, 2)`.** -/
theorem exMetric_C (s : Real) (p q : Fin 3) : metricC exMetric s p q = exC p q := by
  rw [metricC, exMetric_Att, exAtt_c_zero, exC0, exC]
  by_cases h : p = q
  · rw [if_pos h, if_pos h]
    by_cases h0 : p = 0 <;> simp [h0]
  · rw [if_neg h, if_neg h]
    ring

/-- **`metricD` is the chosen nonzero real symmetric `D`.**  The example is not
a flat toy: `D 0 0 = 1`. -/
theorem exMetric_D (s : Real) (p q : Fin 3) : metricD exMetric s p q = exD p q := by
  by_cases h : p = q
  · rw [metricD, if_pos h, exMetric_Att, exMetric_i1,
      exAtt_c_deg_two 0 0 (by rw [deg_add_single, deg_single]) s,
      if_pos ⟨rfl, rfl⟩, quadCoeff_diag, h]
    ring
  · rw [metricD, if_neg h, exMetric_Att, exMetric_i1,
      exAtt_c_deg_two 0 0 (by rw [deg_add_single, deg_single]) s,
      if_pos ⟨rfl, rfl⟩, quadCoeff_offDiag _ h, exD_symm q p]
    ring

theorem exMetric_D_ne_zero (s : Real) : metricD exMetric s 0 0 ≠ 0 := by
  rw [exMetric_D]
  exact exD_ne_zero

/-! ## The base phase -/

/-- The source's prescribed low-order phase: `phi_0 = 0`, `phi_1 = z^{i1}`, and
nothing else. -/
def exPhiJet : LongJet 3 :=
  constJet fun a => if a = (Pi.single 0 1 : Multiindex 3) then 1 else 0

def exBasePhase : SourcePhaseJet exMetric where
  phi := exPhiJet
  dphi := constJet fun _ => 0
  dphi_is_deriv := exPhiJet.hasDeriv
  phi_zero := fun s => by
    rw [exPhiJet, constJet_c, if_neg]
    intro hcon
    have := congrFun hcon 0
    rw [Pi.single_eq_same] at this
    exact zero_ne_one this
  phi_one := fun i s => by
    rw [exPhiJet, constJet_c]
    show (if (Pi.single i 1 : Multiindex 3) = Pi.single 0 1 then (1 : Complex)
      else 0) = if i = exMetric.i1 then 1 else 0
    rw [exMetric_i1]
    by_cases h : i = 0
    · rw [if_pos h, if_pos (by rw [h])]
    · rw [if_neg h, if_neg (fun hcon => h (single_inj hcon))]

theorem exQuadFree : QuadFree exBasePhase := by
  intro b s hb
  show (if b = (Pi.single 0 1 : Multiindex 3) then (1 : Complex) else 0) = 0
  rw [if_neg]
  intro hcon
  rw [hcon, deg_single] at hb
  omega

theorem exC1Data : LiuWang2025SemilinearWavePhaseUpdate.C1Data exMetric exBasePhase where
  Ass := constJet_C1 _
  Bs := by
    intro i
    show (exBs i).C1
    rw [exBs]
    by_cases h : i = 0
    · rw [if_pos h]
      exact constJet_C1 _
    · rw [if_neg h]
      exact constJet_C1 _
  Att := exFermiData.attC1
  phi := constJet_C1 _
  dphi := constJet_C1 _

/-! ## The initial Hessian `H0 = i I` -/

def exH0 : Matrix (Fin 3) (Fin 3) Complex := Complex.I • 1

theorem exH0_symm : exH0.IsSymm := by
  rw [Matrix.IsSymm, exH0, Matrix.transpose_smul, Matrix.transpose_one]

theorem exH0_imPart : hermitianImaginaryPart exH0 = 1 := by
  ext p q
  by_cases h : p = q
  · simp [hermitianImaginaryPart, exH0, Matrix.one_apply, h, Complex.ext_iff]
    norm_num
  · simp [hermitianImaginaryPart, exH0, h]

theorem complexQuadratic_one (x : Fin 3 -> Complex) :
    complexQuadratic (1 : Matrix (Fin 3) (Fin 3) Complex) x
      = ∑ i, star (x i) * x i := by
  rw [complexQuadratic, Matrix.one_mulVec]
  rfl

theorem re_star_mul (z : Complex) : (star z * z).re = Complex.normSq z := by
  simp [Complex.mul_re, Complex.normSq_apply]

theorem re_complexQuadratic_one (x : Fin 3 -> Complex) :
    (complexQuadratic (1 : Matrix (Fin 3) (Fin 3) Complex) x).re
      = ∑ i, Complex.normSq (x i) := by
  rw [complexQuadratic_one, Complex.re_sum]
  exact Finset.sum_congr rfl fun i _ => re_star_mul (x i)

theorem complexPosDef_one : ComplexPosDef (1 : Matrix (Fin 3) (Fin 3) Complex) := by
  refine ⟨Matrix.isHermitian_one, ?_⟩
  intro x hx
  rw [re_complexQuadratic_one]
  obtain ⟨j, hj⟩ : ∃ j, x j ≠ 0 := Function.ne_iff.1 hx
  refine Finset.sum_pos' (fun i _ => Complex.normSq_nonneg _) ⟨j, Finset.mem_univ j, ?_⟩
  exact Complex.normSq_pos.2 hj

theorem exH0_pos : ComplexPosDef (hermitianImaginaryPart exH0) := by
  rw [exH0_imPart]
  exact complexPosDef_one

theorem exH0_coercive :
    LiuWang2025SemilinearWaveRiccatiFlow.RealCoercive
      (hermitianImaginaryPart exH0) 1 := by
  intro x
  rw [exH0_imPart, re_complexQuadratic_one]
  have hS : (0 : Real) ≤ ∑ i, Complex.normSq (x i) :=
    Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _
  have hb : ‖x‖ ≤ Real.sqrt (∑ i, Complex.normSq (x i)) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun i => ?_
    rw [show ‖x i‖ = Real.sqrt (Complex.normSq (x i)) from by
      rw [Complex.norm_def]]
    exact Real.sqrt_le_sqrt
      (Finset.single_le_sum (f := fun j => Complex.normSq (x j))
        (fun j _ => Complex.normSq_nonneg _) (Finset.mem_univ i))
  calc (1 : Real) * ‖x‖ ^ 2 = ‖x‖ ^ 2 := one_mul _
    _ ≤ (Real.sqrt (∑ i, Complex.normSq (x i))) ^ 2 := by
        have hsq := mul_self_le_mul_self (norm_nonneg x) hb
        simpa [pow_two] using hsq
    _ = ∑ i, Complex.normSq (x i) := Real.sq_sqrt hS

/-! ## Interval data -/

theorem ex_start_mem : (0 : Real) ∈ Ioo (-1 : Real) 2 := by
  constructor <;> norm_num

theorem ex_end_mem : (1 : Real) ∈ Ioo (-1 : Real) 2 := by
  constructor <;> norm_num

def exT0 : Icc (min (0 : Real) 1) (max (0 : Real) 1) :=
  ⟨0, by constructor <;> norm_num⟩

/-- The generated Riccati coefficient data for the example. -/
def exCoefficients : LiuWang2025SemilinearWaveRiccatiExistence.Coefficients (Fin 3) :=
  toCoefficients exMetric exFermiData (-1) 2 0 1 ex_start_mem ex_end_mem exH0
    exH0_symm exH0_pos

/-! ## The endpoint, instantiated -/

set_option maxHeartbeats 1000000 in
/-- **The phase endpoint is non-vacuous.**  For the explicit transverse
dimension three Fermi jet above, with `C = diag(0,2,2)` and a nonzero real
symmetric `D`, there is a generated symmetric and uniformly coercive degree-two
matrix and a source phase jet whose *actual* `jetEikonal` coefficients vanish
through any prescribed finite transverse order. -/
theorem exists_example_phase (N : Nat) :
    ∃ (M : Real -> Fin 3 -> Fin 3 -> Complex)
      (P : SourcePhaseJet exMetric),
      (∀ s ∈ uIcc (0 : Real) 1, M s = exCoefficients.toRiccatiFlow.H s) ∧
      (∀ s ∈ uIcc (0 : Real) 1, Matrix.IsSymm (M s)) ∧
      (∀ s ∈ uIcc (0 : Real) 1, ∀ x : Fin 3 -> Complex,
        (1 / exCoefficients.actionBound ^ 2) * ‖x‖ ^ 2
          ≤ (complexQuadratic (M s) x).im) ∧
      (∀ (a : Multiindex 3) (s : Real), deg a = 2 ->
        P.phi.c a s = exBasePhase.phi.c a s + quadCoeff (M s) a) ∧
      (∀ s ∈ uIcc (0 : Real) 1, ∀ a : Multiindex 3, deg a ≤ N ->
        jetEikonal exMetric.Ass exMetric.Bs exMetric.Att P.phi P.dphi a s = 0) := by
  obtain ⟨M, P, hMmat, hMsymm, hPC1, hPlow, hPquad, hPcancel⟩ :=
    exists_phase_from_riccati exMetric exFermiData exBasePhase exC1Data exQuadFree
      ex_start_mem ex_end_mem exH0 exH0_symm exH0_pos exT0 N
  refine ⟨M, P, hMmat, hMsymm, ?_, hPquad, hPcancel⟩
  intro s hs x
  exact generated_quadratic_coercivity exMetric exFermiData ex_start_mem
    ex_end_mem exH0 exH0_symm exH0_pos hMmat 1 one_pos exH0_coercive hs x

/-- The same statement at a concrete beam order. -/
theorem exists_example_phase_order_four :
    ∃ (M : Real -> Fin 3 -> Fin 3 -> Complex) (P : SourcePhaseJet exMetric),
      (∀ s ∈ uIcc (0 : Real) 1, Matrix.IsSymm (M s)) ∧
      (∀ s ∈ uIcc (0 : Real) 1, ∀ a : Multiindex 3, deg a ≤ 4 ->
        jetEikonal exMetric.Ass exMetric.Bs exMetric.Att P.phi P.dphi a s = 0) := by
  obtain ⟨M, P, _, hsymm, _, _, hcancel⟩ := exists_example_phase 4
  exact ⟨M, P, hsymm, hcancel⟩

end LiuWang2025SemilinearWaveRiccatiPhaseExample
