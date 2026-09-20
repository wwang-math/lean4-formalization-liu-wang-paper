import LiuWang.LiuWang2025SemilinearWaveSameDegreeMatrix

/-!
# Liu-Wang semilinear wave: one constructive phase update

This file performs a single step of the source's phase recursion at a
homogeneous transverse degree `r >= 3`, and it does so *constructively*: nothing
about the block equation is assumed.

Given the already constructed phase `base` and an initial degree-`r` block, the
matrix and the source of the degree-`r` equation are both read off from `base`
(`phaseEikonalMatrix`, `phaseSource`); their continuity, differentiability and
uniform row-sum bound are theorems, not hypotheses; the block equation is then
solved by the repository's Picard iteration and promoted to a twice
differentiable path on all of `Real`; the solution is inserted into the phase;
and the conclusion is that *every* degree-`r` coefficient of the actual
`jetEikonal` vanishes on the paper interval, with all other degrees untouched.

The `C1` regularity of the metric and phase jets is the only input beyond the
structures themselves, it is a property of the paper's smooth data, and the
theorem reproduces it for the updated phase so that the step can be iterated.
-/

noncomputable section

open scoped BigOperators
open Set

namespace LiuWang2025SemilinearWavePhaseUpdate

open LiuWang2025SemilinearWaveTransverseJet
open LiuWang2025SemilinearWaveLongitudinalJet
open LiuWang2025SemilinearWaveLongitudinalJet.LongJet
open LiuWang2025SemilinearWaveJetOperators
open LiuWang2025SemilinearWaveDegreeBlock
open LiuWang2025SemilinearWaveDegreeBlockODE
open LiuWang2025SemilinearWaveMetricJetPhaseHierarchy
open LiuWang2025SemilinearWaveSameDegreeMatrix

variable {d : Nat}

/-- The regularity carried by the paper's smooth metric and by every phase this
development constructs: the certified derivative families are continuous. -/
structure C1Data (G : FermiMetricJet d) (P : SourcePhaseJet G) : Prop where
  /-- The longitudinal metric coefficient is `C1`. -/
  Ass : G.Ass.C1
  /-- The mixed metric coefficients are `C1`. -/
  Bs : ∀ i, (G.Bs i).C1
  /-- The transverse metric coefficients are `C1`. -/
  Att : ∀ i j, (G.Att i j).C1
  /-- The phase is `C1`. -/
  phi : P.phi.C1
  /-- Its longitudinal derivative is `C1`. -/
  dphi : P.dphi.C1

/-- **One phase update, constructed.**  No block equation is assumed anywhere:
the equation is solved, the solution inserted, and the cancellation proved. -/
theorem exists_phase_update {G : FermiMetricJet d} (base : SourcePhaseJet G)
    (hbase : C1Data G base) (r : Nat) (hr : 3 ≤ r) {lo hi : Real}
    (t0 : Icc lo hi) (x0 : DegreeBlock d r) :
    ∃ P : SourcePhaseJet G,
      (∀ (a : Multiindex d) (s : Real), deg a ≠ r ->
        P.phi.c a s = base.phi.c a s) ∧
      (∀ (a : Multiindex d) (s : Real), deg a ≠ r ->
        P.dphi.c a s = base.dphi.c a s) ∧
      (∀ a : DegreeIndex d r,
        P.phi.c a.1 (t0 : Real) = base.phi.c a.1 (t0 : Real) + x0 a) ∧
      C1Data G P ∧
      (∀ s ∈ Icc lo hi, ∀ a : Multiindex d, deg a = r ->
        jetEikonal G.Ass G.Bs G.Att P.phi P.dphi a s = 0) := by
  -- every analytic input of the ODE is derived
  obtain ⟨B, hBnn, hKb⟩ := exists_rowSum_bound
    (K := fun s (a b : DegreeIndex d r) => phaseEikonalMatrix base r s a b)
    (fun a b => continuous_phaseEikonalMatrix base r a b) lo hi
  obtain ⟨c, c', c'', hc0, hcd, hc'd, hc''cont, hceq⟩ :=
    exists_c2_blockSolution
      (fun s (a b : DegreeIndex d r) => phaseEikonalMatrix base r s a b)
      (fun s (a b : DegreeIndex d r) => phaseEikonalMatrixDeriv base r s a b)
      (fun s (a : DegreeIndex d r) => phaseSource base r s a)
      (fun s (a : DegreeIndex d r) => phaseSourceDeriv base r s a)
      (fun a b s => hasDerivAt_phaseEikonalMatrix base r a b s)
      (fun a b => continuous_phaseEikonalMatrixDeriv base hbase.Att hbase.phi r a b)
      (fun a s => hasDerivAt_phaseSource base r a s)
      (fun a => continuous_phaseSourceDeriv base hbase.Ass hbase.Bs hbase.Att
        hbase.phi hbase.dphi r a)
      hBnn hKb t0 x0
  have hc'cont : ∀ a : DegreeIndex d r, Continuous fun t => c' t a := fun a =>
    continuous_iff_continuousAt.2 fun t => (hc'd a t).continuousAt
  -- the two inserted blocks, with their derivative certificates
  have hblk : ∀ (a : DegreeIndex d r) (s : Real),
      HasDerivAt (fun t : Real => base.phi.c a.1 t + c t a)
        (base.dphi.c a.1 s + c' s a) s :=
    fun a s => (base.dphi_is_deriv a.1 s).add (hcd a s)
  have hdblk : ∀ (a : DegreeIndex d r) (s : Real),
      HasDerivAt (fun t : Real => base.dphi.c a.1 t + c' t a)
        (base.dphi.dc a.1 s + c'' s a) s :=
    fun a s => (base.dphi.hasDeriv a.1 s).add (hc'd a s)
  obtain ⟨Phi, hPhi⟩ : ∃ Phi : LongJet d, Phi = insertBlock base.phi r
      (fun s a => base.phi.c a.1 s + c s a)
      (fun s a => base.dphi.c a.1 s + c' s a) hblk := ⟨_, rfl⟩
  obtain ⟨DPhi, hDPhi⟩ : ∃ DPhi : LongJet d, DPhi = insertBlock base.dphi r
      (fun s a => base.dphi.c a.1 s + c' s a)
      (fun s a => base.dphi.dc a.1 s + c'' s a) hdblk := ⟨_, rfl⟩
  -- off the inserted degree nothing moves
  have hPhi_off : ∀ (a : Multiindex d) (s : Real), deg a ≠ r ->
      Phi.c a s = base.phi.c a s := by
    intro a s ha
    rw [hPhi, insertBlock_c_of_deg_ne _ _ _ _ _ ha]
  have hDPhi_off : ∀ (a : Multiindex d) (s : Real), deg a ≠ r ->
      DPhi.c a s = base.dphi.c a s := by
    intro a s ha
    rw [hDPhi, insertBlock_c_of_deg_ne _ _ _ _ _ ha]
  have hPhidc_off : ∀ (a : Multiindex d) (s : Real), deg a ≠ r ->
      Phi.dc a s = base.dphi.c a s := by
    intro a s ha
    rw [hPhi, insertBlock_dc_of_deg_ne _ _ _ _ _ ha]
    exact ((base.phi.hasDeriv a s).unique (base.dphi_is_deriv a s))
  -- on the inserted degree the block is written verbatim
  have hPhi_idx : ∀ (a : DegreeIndex d r) (s : Real),
      Phi.c a.1 s = base.phi.c a.1 s + c s a := by
    intro a s
    rw [hPhi]
    exact insertBlock_c_index base.phi r _ _ hblk a s
  have hDPhi_idx : ∀ (a : DegreeIndex d r) (s : Real),
      DPhi.c a.1 s = base.dphi.c a.1 s + c' s a := by
    intro a s
    rw [hDPhi]
    exact insertBlock_c_index base.dphi r _ _ hdblk a s
  have hPhidc_idx : ∀ (a : DegreeIndex d r) (s : Real),
      Phi.dc a.1 s = base.dphi.c a.1 s + c' s a := by
    intro a s
    rw [hPhi]
    exact insertBlock_dc_index base.phi r _ _ hblk a s
  -- `DPhi` is the derivative family of `Phi`
  have hdc : ∀ (a : Multiindex d) (s : Real), DPhi.c a s = Phi.dc a s := by
    intro a s
    by_cases ha : deg a = r
    · have hidx : a ∈ degreeEq d r := mem_degreeEq.2 ha
      rw [hDPhi_idx ⟨a, hidx⟩ s, hPhidc_idx ⟨a, hidx⟩ s]
    · rw [hDPhi_off a s ha, hPhidc_off a s ha]
  have hdeg0 : deg (0 : Multiindex d) = 0 := by
    show ∑ i, (0 : Multiindex d) i = 0
    simp
  obtain ⟨P, hPp, hPd⟩ : ∃ P : SourcePhaseJet G, P.phi = Phi ∧ P.dphi = DPhi :=
    ⟨{ phi := Phi
       dphi := DPhi
       dphi_is_deriv := fun a s => by
         rw [hdc a s]
         exact Phi.hasDeriv a s
       phi_zero := fun s => by
         rw [hPhi_off 0 s (by rw [hdeg0]; omega)]
         exact base.phi_zero s
       phi_one := fun i s => by
         rw [hPhi_off (Pi.single i 1) s (by rw [deg_single]; omega)]
         exact base.phi_one i s }, rfl, rfl⟩
  refine ⟨P, ?_, ?_, ?_, ?_, ?_⟩
  · intro a s ha
    rw [hPp]
    exact hPhi_off a s ha
  · intro a s ha
    rw [hPd]
    exact hDPhi_off a s ha
  · intro a
    rw [hPp, hPhi_idx a (t0 : Real), hc0]
  · exact ⟨hbase.Ass, hbase.Bs, hbase.Att,
      hPp ▸ hPhi ▸ C1_insertBlock base.phi r _ _ hblk hbase.phi
        (fun a => (base.dphi.continuous_c a.1).add (hc'cont a)),
      hPd ▸ hDPhi ▸ C1_insertBlock base.dphi r _ _ hdblk hbase.dphi
        (fun a => (hbase.dphi a.1).add (hc''cont a))⟩
  · intro s hs a ha
    have hidx : a ∈ degreeEq d r := mem_degreeEq.2 ha
    refine eikonal_deg_eq_zero_of_paperBlockEquation P base r hr s ⟨a, hidx⟩
      (fun b hb => ?_) (fun b hb => ?_) (fun b hb => ?_) ?_
    · rw [hPp]
      exact hPhi_off b s (by omega)
    · rw [hPd]
      exact hDPhi_off b s (by omega)
    · rw [hPp]
      exact hPhi_off b s (by omega)
    · have hnum : ∀ beta : DegreeIndex d r,
          phaseEikonalMatrix base r s ⟨a, hidx⟩ beta
              * (P.phi.c beta.1 s - base.phi.c beta.1 s)
            = phaseEikonalMatrix base r s ⟨a, hidx⟩ beta * c s beta := by
        intro beta
        rw [hPp, hPhi_idx beta s]
        ring
      rw [Finset.sum_congr rfl fun beta (_ : beta ∈ Finset.univ) => hnum beta,
        hPd, hDPhi_idx ⟨a, hidx⟩ s]
      have := hceq s hs ⟨a, hidx⟩
      linear_combination this

/-! ## Degree two, constructed from the Riccati matrix

Degree two is *not* handled by the linear block equation.  The quadratic phase
`phi_2 = z^T M(s) z` is built from a Riccati matrix through `quadCoeff`, whose
derivative correspondence `hasDerivAt_quadCoeff` supplies exactly the
longitudinal derivative the equation needs, and the cancellation is proved
through `eikonal_deg_two_eq_zero_of_riccatiEquation`, which retains the
quadratic self-interaction `quadraticSelfTerm` that vanishes identically for
every higher degree.
-/

theorem exists_quadratic_phase_update {G : FermiMetricJet d}
    (base : SourcePhaseJet G) (hbase : C1Data G base) {lo hi : Real}
    (M M' M'' : Real -> Fin d -> Fin d -> Complex)
    (hM : ∀ p q s, HasDerivAt (fun t => M t p q) (M' s p q) s)
    (hM' : ∀ p q s, HasDerivAt (fun t => M' t p q) (M'' s p q) s)
    (hM''cont : ∀ p q, Continuous fun s => M'' s p q)
    (hric : ∀ s ∈ Icc lo hi, ∀ a : DegreeIndex d 2,
      2 * quadCoeff (M' s) a.1
          + ∑ beta : DegreeIndex d 2,
              phaseEikonalMatrix base 2 s a beta * quadCoeff (M s) beta.1
          + quadraticSelfTerm G.Att (quadJet M M' hM) a.1 s
        = phaseSource base 2 s a) :
    ∃ P : SourcePhaseJet G,
      (∀ (a : Multiindex d) (s : Real), deg a ≠ 2 ->
        P.phi.c a s = base.phi.c a s) ∧
      (∀ (a : Multiindex d) (s : Real), deg a ≠ 2 ->
        P.dphi.c a s = base.dphi.c a s) ∧
      (∀ (a : Multiindex d) (s : Real), deg a = 2 ->
        P.phi.c a s = base.phi.c a s + quadCoeff (M s) a) ∧
      C1Data G P ∧
      (∀ s ∈ Icc lo hi, ∀ a : Multiindex d, deg a = 2 ->
        jetEikonal G.Ass G.Bs G.Att P.phi P.dphi a s = 0) := by
  have hM'cont : ∀ p q, Continuous fun s => M' s p q := fun p q =>
    continuous_iff_continuousAt.2 fun s => (hM' p q s).continuousAt
  have hblk : ∀ (a : DegreeIndex d 2) (s : Real),
      HasDerivAt (fun t : Real => base.phi.c a.1 t + quadCoeff (M t) a.1)
        (base.dphi.c a.1 s + quadCoeff (M' s) a.1) s :=
    fun a s => (base.dphi_is_deriv a.1 s).add (hasDerivAt_quadCoeff M M' hM a.1 s)
  have hdblk : ∀ (a : DegreeIndex d 2) (s : Real),
      HasDerivAt (fun t : Real => base.dphi.c a.1 t + quadCoeff (M' t) a.1)
        (base.dphi.dc a.1 s + quadCoeff (M'' s) a.1) s :=
    fun a s => (base.dphi.hasDeriv a.1 s).add
      (hasDerivAt_quadCoeff M' M'' hM' a.1 s)
  obtain ⟨Phi, hPhi⟩ : ∃ Phi : LongJet d, Phi = insertBlock base.phi 2
      (fun s a => base.phi.c a.1 s + quadCoeff (M s) a.1)
      (fun s a => base.dphi.c a.1 s + quadCoeff (M' s) a.1) hblk := ⟨_, rfl⟩
  obtain ⟨DPhi, hDPhi⟩ : ∃ DPhi : LongJet d, DPhi = insertBlock base.dphi 2
      (fun s a => base.dphi.c a.1 s + quadCoeff (M' s) a.1)
      (fun s a => base.dphi.dc a.1 s + quadCoeff (M'' s) a.1) hdblk := ⟨_, rfl⟩
  have hPhi_off : ∀ (a : Multiindex d) (s : Real), deg a ≠ 2 ->
      Phi.c a s = base.phi.c a s := by
    intro a s ha
    rw [hPhi, insertBlock_c_of_deg_ne _ _ _ _ _ ha]
  have hDPhi_off : ∀ (a : Multiindex d) (s : Real), deg a ≠ 2 ->
      DPhi.c a s = base.dphi.c a s := by
    intro a s ha
    rw [hDPhi, insertBlock_c_of_deg_ne _ _ _ _ _ ha]
  have hPhidc_off : ∀ (a : Multiindex d) (s : Real), deg a ≠ 2 ->
      Phi.dc a s = base.dphi.c a s := by
    intro a s ha
    rw [hPhi, insertBlock_dc_of_deg_ne _ _ _ _ _ ha]
    exact (base.phi.hasDeriv a s).unique (base.dphi_is_deriv a s)
  have hPhi_idx : ∀ (a : DegreeIndex d 2) (s : Real),
      Phi.c a.1 s = base.phi.c a.1 s + quadCoeff (M s) a.1 := by
    intro a s
    rw [hPhi]
    exact insertBlock_c_index base.phi 2 _ _ hblk a s
  have hDPhi_idx : ∀ (a : DegreeIndex d 2) (s : Real),
      DPhi.c a.1 s = base.dphi.c a.1 s + quadCoeff (M' s) a.1 := by
    intro a s
    rw [hDPhi]
    exact insertBlock_c_index base.dphi 2 _ _ hdblk a s
  have hPhidc_idx : ∀ (a : DegreeIndex d 2) (s : Real),
      Phi.dc a.1 s = base.dphi.c a.1 s + quadCoeff (M' s) a.1 := by
    intro a s
    rw [hPhi]
    exact insertBlock_dc_index base.phi 2 _ _ hblk a s
  have hdc : ∀ (a : Multiindex d) (s : Real), DPhi.c a s = Phi.dc a s := by
    intro a s
    by_cases ha : deg a = 2
    · have hidx : a ∈ degreeEq d 2 := mem_degreeEq.2 ha
      rw [hDPhi_idx ⟨a, hidx⟩ s, hPhidc_idx ⟨a, hidx⟩ s]
    · rw [hDPhi_off a s ha, hPhidc_off a s ha]
  have hdeg0 : deg (0 : Multiindex d) = 0 := by
    show ∑ i, (0 : Multiindex d) i = 0
    simp
  obtain ⟨P, hPp, hPd⟩ : ∃ P : SourcePhaseJet G, P.phi = Phi ∧ P.dphi = DPhi :=
    ⟨{ phi := Phi
       dphi := DPhi
       dphi_is_deriv := fun a s => by
         rw [hdc a s]
         exact Phi.hasDeriv a s
       phi_zero := fun s => by
         rw [hPhi_off 0 s (by rw [hdeg0]; omega)]
         exact base.phi_zero s
       phi_one := fun i s => by
         rw [hPhi_off (Pi.single i 1) s (by rw [deg_single]; omega)]
         exact base.phi_one i s }, rfl, rfl⟩
  refine ⟨P, ?_, ?_, ?_, ?_, ?_⟩
  · intro a s ha
    rw [hPp]
    exact hPhi_off a s ha
  · intro a s ha
    rw [hPd]
    exact hDPhi_off a s ha
  · intro a s ha
    rw [hPp]
    exact hPhi_idx ⟨a, mem_degreeEq.2 ha⟩ s
  · exact ⟨hbase.Ass, hbase.Bs, hbase.Att,
      hPp ▸ hPhi ▸ C1_insertBlock base.phi 2 _ _ hblk hbase.phi
        (fun a => (base.dphi.continuous_c a.1).add
          (continuous_quadCoeff M' hM'cont a.1)),
      hPd ▸ hDPhi ▸ C1_insertBlock base.dphi 2 _ _ hdblk hbase.dphi
        (fun a => (hbase.dphi a.1).add (continuous_quadCoeff M'' hM''cont a.1))⟩
  · intro s hs a ha
    have hidx : a ∈ degreeEq d 2 := mem_degreeEq.2 ha
    have hdelta : ∀ b, (sub P.phi base.phi).c b s = (quadJet M M' hM).c b s := by
      intro b
      show P.phi.c b s - base.phi.c b s
        = if deg b = 2 then quadCoeff (M s) b else 0
      by_cases hb : deg b = 2
      · rw [if_pos hb, hPp, hPhi_idx ⟨b, mem_degreeEq.2 hb⟩ s]
        ring
      · rw [if_neg hb, hPp, hPhi_off b s hb, sub_self]
    refine eikonal_deg_two_eq_zero_of_riccatiEquation P base s ⟨a, hidx⟩
      (fun b hb => ?_) (fun b hb => ?_) (fun b hb => ?_) ?_
    · rw [hPp]
      exact hPhi_off b s (by omega)
    · rw [hPd]
      exact hDPhi_off b s (by omega)
    · rw [hPp]
      exact hPhi_off b s (by omega)
    · have hnum : ∀ beta : DegreeIndex d 2,
          phaseEikonalMatrix base 2 s ⟨a, hidx⟩ beta
              * (P.phi.c beta.1 s - base.phi.c beta.1 s)
            = phaseEikonalMatrix base 2 s ⟨a, hidx⟩ beta
              * quadCoeff (M s) beta.1 := by
        intro beta
        rw [hPp, hPhi_idx beta s]
        ring
      rw [Finset.sum_congr rfl fun beta (_ : beta ∈ Finset.univ) => hnum beta,
        hPd, hDPhi_idx ⟨a, hidx⟩ s,
        quadraticSelfTerm_congr G.Att hdelta a]
      have := hric s hs ⟨a, hidx⟩
      linear_combination this

/-! ## The phase recursion through arbitrary finite order

Degrees zero and one cancel for *every* source phase jet, by the Fermi
normalisations alone.  Degree two is the genuinely nonlinear Riccati step and is
the single remaining input below.  Everything from degree three upwards is the
linear block equation solved by `exists_phase_update`, and the recursion below
runs it to any prescribed finite order.
-/

theorem eq_zero_of_deg_eq_zero {a : Multiindex d} (ha : deg a = 0) :
    a = 0 := by
  funext i
  have hz : ∀ j ∈ (Finset.univ : Finset (Fin d)), a j = 0 :=
    Finset.sum_eq_zero_iff.1 ha
  exact hz i (Finset.mem_univ i)

/-- Degrees zero, one and two together, given the degree-two (Riccati) step. -/
theorem eikonal_zero_of_deg_le_two {G : FermiMetricJet d} (P : SourcePhaseJet G)
    {s : Real}
    (hquad : ∀ a : Multiindex d, deg a = 2 ->
      jetEikonal G.Ass G.Bs G.Att P.phi P.dphi a s = 0)
    (a : Multiindex d) (ha : deg a ≤ 2) :
    jetEikonal G.Ass G.Bs G.Att P.phi P.dphi a s = 0 := by
  rcases Nat.lt_or_ge (deg a) 1 with h0 | h1
  · rw [eq_zero_of_deg_eq_zero (a := a) (by omega)]
    exact P.eikonal_deg_zero s
  · rcases Nat.lt_or_ge (deg a) 2 with h1' | h2
    · obtain ⟨k, hk⟩ := eq_single_of_deg_eq_one (by omega : deg a = 1)
      rw [hk]
      exact P.eikonal_deg_one k s
    · exact hquad a (by omega)

/-- **The phase recursion, run to arbitrary finite order.**  Given a phase whose
degree-two eikonal coefficients already vanish on the paper interval, there is a
phase agreeing with it through degree two whose *actual* `jetEikonal`
coefficients vanish for every multi-index of degree at most `N`. -/
theorem exists_phase_cancelling_upto {G : FermiMetricJet d}
    (base : SourcePhaseJet G) (hbase : C1Data G base) {lo hi : Real}
    (t0 : Icc lo hi)
    (hquad : ∀ s ∈ Icc lo hi, ∀ a : Multiindex d, deg a = 2 ->
      jetEikonal G.Ass G.Bs G.Att base.phi base.dphi a s = 0)
    (N : Nat) :
    ∃ P : SourcePhaseJet G, C1Data G P ∧
      (∀ (a : Multiindex d) (s : Real), deg a ≤ 2 ->
        P.phi.c a s = base.phi.c a s) ∧
      (∀ (a : Multiindex d) (s : Real), deg a ≤ 2 ->
        P.dphi.c a s = base.dphi.c a s) ∧
      (∀ s ∈ Icc lo hi, ∀ a : Multiindex d, deg a ≤ N ->
        jetEikonal G.Ass G.Bs G.Att P.phi P.dphi a s = 0) := by
  induction N with
  | zero =>
    refine ⟨base, hbase, fun a s _ => rfl, fun a s _ => rfl, fun s hs a ha => ?_⟩
    exact eikonal_zero_of_deg_le_two base (fun b hb => hquad s hs b hb) a (by omega)
  | succ N ih =>
    by_cases hN : N + 1 ≤ 2
    · refine ⟨base, hbase, fun a s _ => rfl, fun a s _ => rfl, fun s hs a ha => ?_⟩
      exact eikonal_zero_of_deg_le_two base (fun b hb => hquad s hs b hb) a (by omega)
    · obtain ⟨P, hPC1, hPlow, hPdlow, hPcancel⟩ := ih
      obtain ⟨Q, hQoff, hQdoff, _, hQC1, hQcancel⟩ :=
        exists_phase_update P hPC1 (N + 1) (by omega) t0 (0 : DegreeBlock d (N + 1))
      refine ⟨Q, hQC1, ?_, ?_, ?_⟩
      · intro a s ha
        rw [hQoff a s (by omega), hPlow a s ha]
      · intro a s ha
        rw [hQdoff a s (by omega), hPdlow a s ha]
      · intro s hs a ha
        rcases Nat.lt_or_ge (deg a) (N + 1) with hlt | hge
        · rcases Nat.lt_or_ge (deg a) 1 with h0 | h1
          · rw [eq_zero_of_deg_eq_zero (a := a) (by omega)]
            exact Q.eikonal_deg_zero s
          · rw [eikonal_triangular Q P h1
              (fun b hb => hQoff b s (by omega))
              (fun b hb => hQdoff b s (by omega))]
            exact hPcancel s hs a (by omega)
        · exact hQcancel s hs a (by omega)

/-- **The whole finite-order phase, from the Riccati matrix upwards.**  Degrees
zero and one are free, degree two is built from the Riccati matrix `M` through
`quadCoeff`, and degrees three to `N` are solved by the linear block equation.
The conclusion is about the *actual* `jetEikonal`. -/
theorem exists_phase_cancelling_upto_of_riccati {G : FermiMetricJet d}
    (base : SourcePhaseJet G) (hbase : C1Data G base) {lo hi : Real}
    (t0 : Icc lo hi)
    (M M' M'' : Real -> Fin d -> Fin d -> Complex)
    (hM : ∀ p q s, HasDerivAt (fun t => M t p q) (M' s p q) s)
    (hM' : ∀ p q s, HasDerivAt (fun t => M' t p q) (M'' s p q) s)
    (hM''cont : ∀ p q, Continuous fun s => M'' s p q)
    (hric : ∀ s ∈ Icc lo hi, ∀ a : DegreeIndex d 2,
      2 * quadCoeff (M' s) a.1
          + ∑ beta : DegreeIndex d 2,
              phaseEikonalMatrix base 2 s a beta * quadCoeff (M s) beta.1
          + quadraticSelfTerm G.Att (quadJet M M' hM) a.1 s
        = phaseSource base 2 s a)
    (N : Nat) :
    ∃ P : SourcePhaseJet G, C1Data G P ∧
      (∀ (a : Multiindex d) (s : Real), deg a ≤ 1 ->
        P.phi.c a s = base.phi.c a s) ∧
      (∀ (a : Multiindex d) (s : Real), deg a = 2 ->
        P.phi.c a s = base.phi.c a s + quadCoeff (M s) a) ∧
      (∀ s ∈ Icc lo hi, ∀ a : Multiindex d, deg a ≤ N ->
        jetEikonal G.Ass G.Bs G.Att P.phi P.dphi a s = 0) := by
  obtain ⟨Q, hQoff, hQdoff, hQidx, hQC1, hQquad⟩ :=
    exists_quadratic_phase_update base hbase M M' M'' hM hM' hM''cont hric
  obtain ⟨P, hPC1, hPlow, hPdlow, hPcancel⟩ :=
    exists_phase_cancelling_upto Q hQC1 t0
      (fun s hs a ha => hQquad s hs a ha) N
  refine ⟨P, hPC1, ?_, ?_, hPcancel⟩
  · intro a s ha
    rw [hPlow a s (by omega), hQoff a s (by omega)]
  · intro a s ha
    rw [hPlow a s (by omega), hQidx a s ha]

end LiuWang2025SemilinearWavePhaseUpdate
