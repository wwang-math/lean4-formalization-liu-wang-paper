import LiuWang.LiuWang2025SemilinearWaveAmplitudeJetOperators

/-!
# Liu-Wang semilinear wave: the same-degree amplitude transport matrix

`WaveJetData.jetTransport` is the actual transport operator.  This file isolates
the part of it that acts on a perturbation of the amplitude *inside a single
transverse degree*, and shows that this part is a genuine finite matrix on
`DegreeBlock d r`, not a family of independent scalars.

The decomposition proved here is, for `u` and `u'` agreeing away from degree `r`
and `deg alpha = r`,

  `T_phi(u)_alpha - T_phi(u')_alpha
     = 2 (d_s u_alpha - d_s u'_alpha)
       + sum_beta K_r(s)_{alpha beta} (u_beta - u'_beta)`,

with the coefficient `2` coming from the Fermi normalization `A^{s i1}(s,0) = 1`
together with the source's `phi_1 = z^{i1}`, and with

  `K_r(s)_{alpha beta} = sameDegreeTransport W P (basisJet beta) alpha s`

built from the metric jet, the already constructed phase, and the first-order
wave coefficients only.  `K` is *not* assumed diagonal: its off-diagonal entries
are exactly the repository's form of `4 (A M z) . grad_z`, and a nondiagonal
instance is exhibited in the focused tests.
-/

noncomputable section

open scoped BigOperators
open Set

namespace LiuWang2025SemilinearWaveAmplitudeSameDegreeMatrix

open LiuWang2025SemilinearWaveTransverseJet
open LiuWang2025SemilinearWaveLongitudinalJet
open LiuWang2025SemilinearWaveLongitudinalJet.LongJet
open LiuWang2025SemilinearWaveJetOperators
open LiuWang2025SemilinearWaveDegreeBlock
open LiuWang2025SemilinearWaveMetricJetPhaseHierarchy
open LiuWang2025SemilinearWaveSameDegreeMatrix
open LiuWang2025SemilinearWaveAmplitudeJetOperators
open LiuWang2025SemilinearWaveAmplitudeJetOperators.WaveJetData

variable {d : Nat}

/-! ## Convolution linearity in the left slot -/

theorem convRaw_sum_left {iota : Type*} [Fintype iota] (f : iota -> LongJet d)
    (v : Multiindex d -> Real -> Complex) (a : Multiindex d) (s : Real) :
    convRaw (sumJet f) v a s = ∑ k, convRaw (f k) v a s := by
  show (∑ b ∈ below a, (∑ k, (f k).c b s) * v (a - b) s)
    = ∑ k, ∑ b ∈ below a, (f k).c b s * v (a - b) s
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun b _ => by rw [Finset.sum_mul]

theorem convRaw_smul_left (k : Complex) (u : LongJet d)
    (v : Multiindex d -> Real -> Complex) (a : Multiindex d) (s : Real) :
    convRaw (smul k u) v a s = k * convRaw u v a s := by
  show (∑ b ∈ below a, (k * u.c b s) * v (a - b) s)
    = k * ∑ b ∈ below a, u.c b s * v (a - b) s
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun b _ => by ring

theorem convRaw_congr_left {u u' : LongJet d}
    {v : Multiindex d -> Real -> Complex} {a : Multiindex d} {s : Real}
    (h : ∀ b, deg b ≤ deg a -> u.c b s = u'.c b s) :
    convRaw u v a s = convRaw u' v a s := by
  refine Finset.sum_congr rfl fun b hb => ?_
  have hd := deg_add_deg_sub hb
  rw [h b (by omega)]

/-! ## The part of the transport operator acting on the amplitude itself -/

variable (W : WaveJetData d)

/-- The part of `jetTransport` that reads only the amplitude's coefficients,
not its longitudinal derivative.  It is manifestly linear in `delta`. -/
def sameDegreeTransport (P : SourcePhaseJet W.G) (delta : LongJet d)
    (a : Multiindex d) (s : Real) : Complex :=
  2 * ((∑ i, (mul (W.G.Bs i)
        (mul P.dphi (transverseDeriv i delta))).c a s)
      + ∑ i, ∑ j,
          (mul (W.G.Att i j)
            (mul (transverseDeriv i P.phi) (transverseDeriv j delta))).c a s)
    - convRaw delta (fun b t => W.jetBox (ofSourcePhase P) b t) a s

/-- **Regrouping of the actual transport operator.**  Everything that touches
the longitudinal derivative of the amplitude is displayed, and the rest is
`sameDegreeTransport`. -/
theorem jetTransport_apply (P : SourcePhaseJet W.G) (u : LongJet2 d)
    (a : Multiindex d) (s : Real) :
    W.jetTransport P u a s
      = 2 * ((mul W.G.Ass (mul P.dphi u.djet)).c a s
            + ∑ i, (mul (W.G.Bs i)
                (mul (transverseDeriv i P.phi) u.djet)).c a s)
        + sameDegreeTransport W P u.jet a s := by
  rw [jetTransport, sameDegreeTransport,
    Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => rfl, Finset.sum_add_distrib]
  ring

/-! ## Linearity of the same-degree part -/

theorem sameDegreeTransport_congr (P : SourcePhaseJet W.G)
    {delta delta' : LongJet d} {a : Multiindex d} {s : Real}
    (h : ∀ b, deg b ≤ deg a + 1 -> delta.c b s = delta'.c b s) :
    sameDegreeTransport W P delta a s = sameDegreeTransport W P delta' a s := by
  have hgrad : ∀ (i : Fin d) b, deg b ≤ deg a ->
      (transverseDeriv i delta).c b s = (transverseDeriv i delta').c b s := by
    intro i b hb
    exact transverseDeriv_c_congr (h _ (by rw [deg_add_single]; omega))
  rw [sameDegreeTransport, sameDegreeTransport]
  congr 1
  · congr 1
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      exact mul_c_congr (fun _ _ => rfl)
        (fun b hb => mul_c_congr (fun _ _ => rfl) (fun e he => hgrad i e (by omega)))
    · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      exact mul_c_congr (fun _ _ => rfl)
        (fun b hb => mul_c_congr (fun _ _ => rfl) (fun e he => hgrad j e (by omega)))
  · exact convRaw_congr_left (fun b hb => h b (by omega))

theorem sameDegreeTransport_sum {iota : Type*} [Fintype iota]
    (P : SourcePhaseJet W.G) (f : iota -> LongJet d) (a : Multiindex d)
    (s : Real) :
    sameDegreeTransport W P (sumJet f) a s
      = ∑ k, sameDegreeTransport W P (f k) a s := by
  have hA : ∀ i : Fin d, (mul (W.G.Bs i)
        (mul P.dphi (transverseDeriv i (sumJet f)))).c a s
      = ∑ k, (mul (W.G.Bs i)
        (mul P.dphi (transverseDeriv i (f k)))).c a s := by
    intro i
    have h1 : ∀ b, deg b ≤ deg a ->
        (mul P.dphi (transverseDeriv i (sumJet f))).c b s
          = (sumJet fun k => mul P.dphi (transverseDeriv i (f k))).c b s := by
      intro b _
      calc (mul P.dphi (transverseDeriv i (sumJet f))).c b s
          = (mul P.dphi (sumJet fun k => transverseDeriv i (f k))).c b s :=
            mul_c_congr (fun _ _ => rfl) (fun e _ => transverseDeriv_c_sum i f e s)
        _ = ∑ k, (mul P.dphi (transverseDeriv i (f k))).c b s :=
            mul_c_sum_right _ _ b s
        _ = (sumJet fun k => mul P.dphi (transverseDeriv i (f k))).c b s := rfl
    rw [mul_c_congr (fun _ _ => rfl) h1, mul_c_sum_right]
  have hB : ∀ i j : Fin d, (mul (W.G.Att i j)
        (mul (transverseDeriv i P.phi) (transverseDeriv j (sumJet f)))).c a s
      = ∑ k, (mul (W.G.Att i j)
        (mul (transverseDeriv i P.phi) (transverseDeriv j (f k)))).c a s := by
    intro i j
    have h1 : ∀ b, deg b ≤ deg a ->
        (mul (transverseDeriv i P.phi) (transverseDeriv j (sumJet f))).c b s
          = (sumJet fun k =>
              mul (transverseDeriv i P.phi) (transverseDeriv j (f k))).c b s := by
      intro b _
      calc (mul (transverseDeriv i P.phi) (transverseDeriv j (sumJet f))).c b s
          = (mul (transverseDeriv i P.phi)
              (sumJet fun k => transverseDeriv j (f k))).c b s :=
            mul_c_congr (fun _ _ => rfl) (fun e _ => transverseDeriv_c_sum j f e s)
        _ = ∑ k, (mul (transverseDeriv i P.phi) (transverseDeriv j (f k))).c b s :=
            mul_c_sum_right _ _ b s
        _ = (sumJet fun k =>
              mul (transverseDeriv i P.phi) (transverseDeriv j (f k))).c b s := rfl
    rw [mul_c_congr (fun _ _ => rfl) h1, mul_c_sum_right]
  have hRHS : (∑ k, sameDegreeTransport W P (f k) a s)
      = 2 * ((∑ k, ∑ i, (mul (W.G.Bs i)
              (mul P.dphi (transverseDeriv i (f k)))).c a s)
            + ∑ k, ∑ i, ∑ j, (mul (W.G.Att i j)
              (mul (transverseDeriv i P.phi) (transverseDeriv j (f k)))).c a s)
        - ∑ k, convRaw (f k)
            (fun b t => W.jetBox (ofSourcePhase P) b t) a s := by
    simp only [sameDegreeTransport]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_add_distrib]
  have hswapA : (∑ i : Fin d, ∑ k : iota, (mul (W.G.Bs i)
        (mul P.dphi (transverseDeriv i (f k)))).c a s)
      = ∑ k : iota, ∑ i : Fin d, (mul (W.G.Bs i)
        (mul P.dphi (transverseDeriv i (f k)))).c a s := Finset.sum_comm
  have hswapB : (∑ i : Fin d, ∑ j : Fin d, ∑ k : iota, (mul (W.G.Att i j)
        (mul (transverseDeriv i P.phi) (transverseDeriv j (f k)))).c a s)
      = ∑ k : iota, ∑ i : Fin d, ∑ j : Fin d, (mul (W.G.Att i j)
        (mul (transverseDeriv i P.phi) (transverseDeriv j (f k)))).c a s := by
    calc (∑ i : Fin d, ∑ j : Fin d, ∑ k : iota, (mul (W.G.Att i j)
          (mul (transverseDeriv i P.phi) (transverseDeriv j (f k)))).c a s)
        = ∑ i : Fin d, ∑ k : iota, ∑ j : Fin d, (mul (W.G.Att i j)
          (mul (transverseDeriv i P.phi) (transverseDeriv j (f k)))).c a s :=
          Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = ∑ k : iota, ∑ i : Fin d, ∑ j : Fin d, (mul (W.G.Att i j)
          (mul (transverseDeriv i P.phi) (transverseDeriv j (f k)))).c a s :=
          Finset.sum_comm
  rw [sameDegreeTransport,
    Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hA i,
    Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) =>
      Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) => hB i j,
    convRaw_sum_left, hswapA, hswapB, hRHS]

theorem sameDegreeTransport_smul (P : SourcePhaseJet W.G) (k : Complex)
    (delta : LongJet d) (a : Multiindex d) (s : Real) :
    sameDegreeTransport W P (smul k delta) a s
      = k * sameDegreeTransport W P delta a s := by
  have hA : ∀ i : Fin d, (mul (W.G.Bs i)
        (mul P.dphi (transverseDeriv i (smul k delta)))).c a s
      = k * (mul (W.G.Bs i)
        (mul P.dphi (transverseDeriv i delta))).c a s := by
    intro i
    rw [← mul_c_smul_right]
    refine mul_c_congr (fun _ _ => rfl) fun b _ => ?_
    exact (mul_c_congr (fun _ _ => rfl)
      (fun e _ => transverseDeriv_c_smul i k delta e s)).trans
      (mul_c_smul_right k _ _ b s)
  have hB : ∀ i j : Fin d, (mul (W.G.Att i j)
        (mul (transverseDeriv i P.phi) (transverseDeriv j (smul k delta)))).c a s
      = k * (mul (W.G.Att i j)
        (mul (transverseDeriv i P.phi) (transverseDeriv j delta))).c a s := by
    intro i j
    rw [← mul_c_smul_right]
    refine mul_c_congr (fun _ _ => rfl) fun b _ => ?_
    exact (mul_c_congr (fun _ _ => rfl)
      (fun e _ => transverseDeriv_c_smul j k delta e s)).trans
      (mul_c_smul_right k _ _ b s)
  rw [sameDegreeTransport, sameDegreeTransport,
    Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hA i,
    Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) =>
      Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) => hB i j,
    convRaw_smul_left]
  have hsum1 : (∑ i, k * (mul (W.G.Bs i)
        (mul P.dphi (transverseDeriv i delta))).c a s)
      = k * ∑ i, (mul (W.G.Bs i)
        (mul P.dphi (transverseDeriv i delta))).c a s :=
    (Finset.mul_sum _ _ _).symm
  have hsum2 : (∑ i, ∑ j, k * (mul (W.G.Att i j)
        (mul (transverseDeriv i P.phi) (transverseDeriv j delta))).c a s)
      = k * ∑ i, ∑ j, (mul (W.G.Att i j)
        (mul (transverseDeriv i P.phi) (transverseDeriv j delta))).c a s := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => (Finset.mul_sum _ _ _).symm
  rw [hsum1, hsum2]
  ring

theorem convRaw_sub_left (u u' : LongJet d)
    (v : Multiindex d -> Real -> Complex) (a : Multiindex d) (s : Real) :
    convRaw u v a s - convRaw u' v a s = convRaw (sub u u') v a s := by
  show (∑ b ∈ below a, u.c b s * v (a - b) s)
      - ∑ b ∈ below a, u'.c b s * v (a - b) s
    = ∑ b ∈ below a, (u.c b s - u'.c b s) * v (a - b) s
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun b _ => by ring

theorem sameDegreeTransport_sub (P : SourcePhaseJet W.G)
    (delta delta' : LongJet d) (a : Multiindex d) (s : Real) :
    sameDegreeTransport W P delta a s - sameDegreeTransport W P delta' a s
      = sameDegreeTransport W P (sub delta delta') a s := by
  have hA : ∀ i : Fin d,
      (mul (W.G.Bs i) (mul P.dphi (transverseDeriv i delta))).c a s
      - (mul (W.G.Bs i) (mul P.dphi (transverseDeriv i delta'))).c a s
      = (mul (W.G.Bs i)
          (mul P.dphi (transverseDeriv i (sub delta delta')))).c a s := by
    intro i
    rw [mul_c_sub_right]
    refine mul_c_congr (fun _ _ => rfl) fun b _ => ?_
    show (mul P.dphi (transverseDeriv i delta)).c b s
      - (mul P.dphi (transverseDeriv i delta')).c b s = _
    rw [mul_c_sub_right]
    exact mul_c_congr (fun _ _ => rfl)
      (fun e _ => (transverseDeriv_c_sub i delta delta' e s).symm)
  have hB : ∀ i j : Fin d,
      (mul (W.G.Att i j)
        (mul (transverseDeriv i P.phi) (transverseDeriv j delta))).c a s
      - (mul (W.G.Att i j)
        (mul (transverseDeriv i P.phi) (transverseDeriv j delta'))).c a s
      = (mul (W.G.Att i j)
          (mul (transverseDeriv i P.phi)
            (transverseDeriv j (sub delta delta')))).c a s := by
    intro i j
    rw [mul_c_sub_right]
    refine mul_c_congr (fun _ _ => rfl) fun b _ => ?_
    show (mul (transverseDeriv i P.phi) (transverseDeriv j delta)).c b s
      - (mul (transverseDeriv i P.phi) (transverseDeriv j delta')).c b s = _
    rw [mul_c_sub_right]
    exact mul_c_congr (fun _ _ => rfl)
      (fun e _ => (transverseDeriv_c_sub j delta delta' e s).symm)
  rw [sameDegreeTransport, sameDegreeTransport, sameDegreeTransport,
    ← convRaw_sub_left]
  have hAs : (∑ i, (mul (W.G.Bs i)
        (mul P.dphi (transverseDeriv i (sub delta delta')))).c a s)
      = (∑ i, (mul (W.G.Bs i) (mul P.dphi (transverseDeriv i delta))).c a s)
        - ∑ i, (mul (W.G.Bs i)
            (mul P.dphi (transverseDeriv i delta'))).c a s := by
    rw [← Finset.sum_sub_distrib]
    exact (Finset.sum_congr rfl fun i _ => hA i).symm
  have hBs : (∑ i, ∑ j, (mul (W.G.Att i j)
        (mul (transverseDeriv i P.phi)
          (transverseDeriv j (sub delta delta')))).c a s)
      = (∑ i, ∑ j, (mul (W.G.Att i j)
          (mul (transverseDeriv i P.phi) (transverseDeriv j delta))).c a s)
        - ∑ i, ∑ j, (mul (W.G.Att i j)
            (mul (transverseDeriv i P.phi) (transverseDeriv j delta'))).c a s := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => (hB i j).symm
  rw [hAs, hBs]
  ring

/-! ## The matrix -/

/-- **The degree-`r` amplitude transport matrix**, obtained by applying the
actual same-degree transport action to the standard basis jets.  It is built
from the metric jet, the already constructed phase, and the first-order wave
coefficients only. -/
def transportMatrix (P : SourcePhaseJet W.G) (r : Nat) (s : Real)
    (alpha beta : DegreeIndex d r) : Complex :=
  sameDegreeTransport W P (basisJet beta.1) alpha.1 s

/-- **The same-degree transport action is that matrix acting on the block.**
No diagonality is assumed anywhere. -/
theorem sameDegreeTransport_matrix (P : SourcePhaseJet W.G) (delta : LongJet d)
    (r : Nat) (s : Real) (hsupp : ∀ b, deg b ≠ r -> delta.c b s = 0)
    (alpha : DegreeIndex d r) :
    sameDegreeTransport W P delta alpha.1 s
      = ∑ beta : DegreeIndex d r,
          transportMatrix W P r s alpha beta * delta.c beta.1 s := by
  classical
  have hcongr : sameDegreeTransport W P delta alpha.1 s
      = sameDegreeTransport W P (sumJet (fun beta : DegreeIndex d r =>
          singleJet beta.1 (delta.c beta.1) (delta.dc beta.1)
            (delta.hasDeriv beta.1))) alpha.1 s :=
    sameDegreeTransport_congr W P
      (fun b _ => (sumSingle_c delta r s hsupp b).symm)
  rw [hcongr, sameDegreeTransport_sum]
  refine Finset.sum_congr rfl fun beta _ => ?_
  have hb : sameDegreeTransport W P
        (singleJet beta.1 (delta.c beta.1) (delta.dc beta.1)
          (delta.hasDeriv beta.1)) alpha.1 s
      = sameDegreeTransport W P
        (smul (delta.c beta.1 s) (basisJet beta.1)) alpha.1 s := by
    refine sameDegreeTransport_congr W P fun b _ => ?_
    show (if b = beta.1 then delta.c beta.1 s else 0)
      = delta.c beta.1 s * (if b = beta.1 then (1 : Complex) else 0)
    by_cases hbb : b = beta.1 <;> simp [hbb]
  rw [hb, sameDegreeTransport_smul, transportMatrix]
  ring

/-! ## The block identity -/

theorem index_eq_zero_of_deg_eq_zero {a : Multiindex d} (ha : deg a = 0) :
    a = 0 := by
  funext i
  exact (Finset.sum_eq_zero_iff.1 ha) i (Finset.mem_univ i)

/-- The source's low-order phase makes the longitudinal derivative of the phase
vanish below transverse degree two. -/
theorem dphi_vanish_below_two {G : FermiMetricJet d} (P : SourcePhaseJet G)
    (s : Real) : ∀ b, deg b < 2 -> P.dphi.c b s = 0 := by
  intro b hb
  rcases Nat.lt_or_ge (deg b) 1 with h0 | h1
  · rw [index_eq_zero_of_deg_eq_zero (a := b) (by omega)]
    exact P.dphi_zero s
  · obtain ⟨k, hk⟩ := eq_single_of_deg_eq_one (by omega : deg b = 1)
    rw [hk]
    exact P.dphi_one k s

/-- **The full same-degree block identity for the actual transport operator.**
For amplitudes agreeing away from transverse degree `r`, the difference of the
actual `jetTransport` coefficients is twice the difference of the longitudinal
derivatives plus the finite matrix acting on the whole degree-`r` block.  The
coefficient `2` comes from `A^{s i1}(s,0) = 1` and `phi_1 = z^{i1}`, not from a
normalization convention. -/
theorem jetTransport_block_matrix_form (P : SourcePhaseJet W.G)
    (u u' : LongJet2 d) (r : Nat) (s : Real)
    (alpha : DegreeIndex d r)
    (hjet : ∀ b, deg b ≠ r -> u.jet.c b s = u'.jet.c b s)
    (hdjet : ∀ b, deg b ≠ r -> u.djet.c b s = u'.djet.c b s) :
    W.jetTransport P u alpha.1 s - W.jetTransport P u' alpha.1 s
      = 2 * (u.djet.c alpha.1 s - u'.djet.c alpha.1 s)
        + ∑ beta : DegreeIndex d r,
            transportMatrix W P r s alpha beta
              * (u.jet.c beta.1 s - u'.jet.c beta.1 s) := by
  classical
  have hdeg : deg alpha.1 = r := mem_degreeEq.1 alpha.2
  have hsuppD : ∀ b, deg b ≠ r -> (sub u.djet u'.djet).c b s = 0 := by
    intro b hb
    show u.djet.c b s - u'.djet.c b s = 0
    rw [hdjet b hb, sub_self]
  have hsuppJ : ∀ b, deg b ≠ r -> (sub u.jet u'.jet).c b s = 0 := by
    intro b hb
    show u.jet.c b s - u'.jet.c b s = 0
    rw [hjet b hb, sub_self]
  -- the longitudinal-longitudinal block contributes nothing
  have hA1 : (mul W.G.Ass (mul P.dphi u.djet)).c alpha.1 s
      - (mul W.G.Ass (mul P.dphi u'.djet)).c alpha.1 s = 0 := by
    rw [mul_c_sub_right]
    have hcong : (mul W.G.Ass (sub (mul P.dphi u.djet) (mul P.dphi u'.djet))).c
          alpha.1 s
        = (mul W.G.Ass (mul P.dphi (sub u.djet u'.djet))).c alpha.1 s :=
      mul_c_congr (fun _ _ => rfl) fun b _ => mul_c_sub_right _ _ _ b s
    rw [hcong]
    refine mul_c_vanish (p := 0) (q := 2 + r) vanish_below_zero ?_ (by omega)
    intro b hb
    exact mul_c_vanish (p := 2) (q := r) (dphi_vanish_below_two P s)
      (fun e he => hsuppD e (by omega)) (by omega)
  -- the mixed block extracts the longitudinal derivative with coefficient one
  have hA2 : (∑ i, (mul (W.G.Bs i)
        (mul (transverseDeriv i P.phi) u.djet)).c alpha.1 s)
      - (∑ i, (mul (W.G.Bs i)
        (mul (transverseDeriv i P.phi) u'.djet)).c alpha.1 s)
      = u.djet.c alpha.1 s - u'.djet.c alpha.1 s := by
    have hstep : ∀ i : Fin d,
        (mul (W.G.Bs i) (mul (transverseDeriv i P.phi) u.djet)).c alpha.1 s
        - (mul (W.G.Bs i) (mul (transverseDeriv i P.phi) u'.djet)).c alpha.1 s
        = (W.G.Bs i).c 0 s
          * ((if i = W.G.i1 then 1 else 0)
            * (u.djet.c alpha.1 s - u'.djet.c alpha.1 s)) := by
      intro i
      rw [mul_c_sub_right]
      have hcong : (mul (W.G.Bs i)
            (sub (mul (transverseDeriv i P.phi) u.djet)
              (mul (transverseDeriv i P.phi) u'.djet))).c alpha.1 s
          = (mul (W.G.Bs i)
            (mul (transverseDeriv i P.phi) (sub u.djet u'.djet))).c alpha.1 s :=
        mul_c_congr (fun _ _ => rfl) fun b _ => mul_c_sub_right _ _ _ b s
      rw [hcong,
        mul_c_bot (u := W.G.Bs i) (by
          intro b hb
          exact mul_c_vanish (p := 0) (q := r) vanish_below_zero
            (fun e he => hsuppD e (by omega)) (by omega)),
        mul_c_bot (u := transverseDeriv i P.phi)
          (fun b hb => hsuppD b (by omega)),
        transverseDeriv_c_zero_eq P.phi i s, P.phi_one i s]
      rfl
    rw [← Finset.sum_sub_distrib,
      Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hstep i,
      Finset.sum_eq_single_of_mem W.G.i1 (Finset.mem_univ _)]
    · rw [if_pos rfl, W.G.longitudinalNormalization s]
      ring
    · intro i _ hi
      rw [if_neg hi, zero_mul, mul_zero]
  -- the remaining part is the matrix acting on the block
  have hA3 : sameDegreeTransport W P u.jet alpha.1 s
      - sameDegreeTransport W P u'.jet alpha.1 s
      = ∑ beta : DegreeIndex d r, transportMatrix W P r s alpha beta
          * (u.jet.c beta.1 s - u'.jet.c beta.1 s) := by
    rw [sameDegreeTransport_sub,
      sameDegreeTransport_matrix W P (sub u.jet u'.jet) r s hsuppJ alpha]
    rfl
  rw [jetTransport_apply, jetTransport_apply]
  linear_combination 2 * hA1 + 2 * hA2 + hA3

/-- **The block equation forces the actual transport coefficient to vanish.** -/
theorem jetTransport_eq_zero_of_blockEquation (P : SourcePhaseJet W.G)
    (u u' : LongJet2 d) (r : Nat) (s : Real)
    (alpha : DegreeIndex d r)
    (hjet : ∀ b, deg b ≠ r -> u.jet.c b s = u'.jet.c b s)
    (hdjet : ∀ b, deg b ≠ r -> u.djet.c b s = u'.djet.c b s)
    (hblock : 2 * (u.djet.c alpha.1 s - u'.djet.c alpha.1 s)
        + ∑ beta : DegreeIndex d r,
            transportMatrix W P r s alpha beta
              * (u.jet.c beta.1 s - u'.jet.c beta.1 s)
      = - W.jetTransport P u' alpha.1 s) :
    W.jetTransport P u alpha.1 s = 0 := by
  have h := jetTransport_block_matrix_form W P u u' r s alpha hjet hdjet
  linear_combination h + hblock

/-! ## Regularity of the matrix entries -/

theorem continuous_transportMatrix (P : SourcePhaseJet W.G) (hP : P.dphi.C1)
    (r : Nat) (alpha beta : DegreeIndex d r) :
    Continuous fun s => transportMatrix W P r s alpha beta := by
  refine Continuous.sub (continuous_const.mul (Continuous.add ?_ ?_)) ?_
  · exact continuous_finset_sum _ fun i _ =>
      (mul (W.G.Bs i)
        (mul P.dphi (transverseDeriv i (basisJet beta.1)))).continuous_c alpha.1
  · exact continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ =>
      (mul (W.G.Att i j)
        (mul (transverseDeriv i P.phi)
          (transverseDeriv j (basisJet beta.1)))).continuous_c alpha.1
  · refine continuous_finset_sum _ fun b _ => ?_
    exact ((basisJet beta.1).continuous_c b).mul
      (W.continuous_jetBox (ofSourcePhase P) hP (alpha.1 - b))

/-- **A uniform nonnegative row-sum bound for the amplitude matrix is
automatic** on a compact interval, so the block ODE's hypotheses are met. -/
theorem exists_transportMatrix_rowSum_bound (P : SourcePhaseJet W.G)
    (hP : P.dphi.C1) (r : Nat) (lo hi : Real) :
    ∃ B : Real, 0 ≤ B ∧ ∀ s ∈ Icc lo hi, ∀ alpha : DegreeIndex d r,
      ∑ beta, ‖transportMatrix W P r s alpha beta‖ ≤ B :=
  LiuWang2025SemilinearWaveDegreeBlockODE.exists_rowSum_bound
    (fun a b => continuous_transportMatrix W P hP r a b) lo hi

end LiuWang2025SemilinearWaveAmplitudeSameDegreeMatrix
