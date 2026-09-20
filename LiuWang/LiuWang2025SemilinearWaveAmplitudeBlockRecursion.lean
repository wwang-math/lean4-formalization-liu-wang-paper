import LiuWang.LiuWang2025SemilinearWaveAmplitudeSameDegreeMatrix

/-!
# Liu-Wang semilinear wave: one homogeneous amplitude block, constructed

`LiuWang2025SemilinearWaveAmplitudeSameDegreeMatrix` shows that at transverse
degree `r` the actual transport operator acts on the whole degree-`r` block
through a finite matrix `K_r(s)` plus twice the longitudinal derivative.  This
file solves that block system and inserts the solution back into the amplitude.

The equation solved is exactly the source's, in the form the block identity
produces:

  `2 c_alpha' + sum_beta K_r(s)_{alpha beta} c_beta
     = target_alpha - T_phi(base)_alpha`,

with `target = 0` for the leading amplitude and `target = - i Box_g a_{k-1}` for
the higher ones, so that `- i T_phi a_k + Box_g a_{k-1}` vanishes.  Nothing in
this file assumes any cancellation: the source is *computed* from the actual
`jetTransport` of the already constructed lower data.

**The one analytic input.**  The repository's block ODE produces a twice
differentiable path, which is what `LongJet2` needs, but to do so it requires
the matrix and the source to be `C^1`.  `transportMatrix` and `jetTransport`
read `Box_g phi`, which involves the *second* longitudinal derivative of the
phase; differentiating them once more needs a third, which `SourcePhaseJet` does
not carry.  `AmplitudeBlockRegularity` records exactly those derivative
certificates and nothing else.  It contains no hierarchy equation, no
cancellation field, no amplitude, and no conclusion.
-/

noncomputable section

open scoped BigOperators
open Set

namespace LiuWang2025SemilinearWaveAmplitudeBlockRecursion

open LiuWang2025SemilinearWaveTransverseJet
open LiuWang2025SemilinearWaveLongitudinalJet
open LiuWang2025SemilinearWaveLongitudinalJet.LongJet
open LiuWang2025SemilinearWaveJetOperators
open LiuWang2025SemilinearWaveDegreeBlock
open LiuWang2025SemilinearWaveDegreeBlockODE
open LiuWang2025SemilinearWaveMetricJetPhaseHierarchy
open LiuWang2025SemilinearWaveAmplitudeJetOperators
open LiuWang2025SemilinearWaveAmplitudeJetOperators.WaveJetData
open LiuWang2025SemilinearWaveAmplitudeSameDegreeMatrix

variable {d : Nat}

/-! ## The block source -/

variable (W : WaveJetData d)

/-- The source of the degree-`r` block equation: the prescribed target minus the
actual transport coefficient of the already constructed data.  It is computed,
never assumed. -/
def blockSource (P : SourcePhaseJet W.G) (base : LongJet2 d)
    (target : Multiindex d -> Real -> Complex) (r : Nat) (s : Real)
    (alpha : DegreeIndex d r) : Complex :=
  target alpha.1 s - W.jetTransport P base alpha.1 s

/-- The analytic regularity the block ODE needs, and nothing else: certified
first derivatives, with continuity, of the transport matrix and of the block
source.  No equation, no cancellation, no amplitude. -/
structure AmplitudeBlockRegularity (P : SourcePhaseJet W.G) (base : LongJet2 d)
    (target : Multiindex d -> Real -> Complex) (r : Nat) where
  /-- `P.dphi` is `C1`, which is what makes the matrix and source continuous. -/
  dphiC1 : P.dphi.C1
  /-- The derivative of each matrix entry. -/
  dK : Real -> DegreeIndex d r -> DegreeIndex d r -> Complex
  /-- ... certified. -/
  dK_is_deriv : ∀ a b s,
    HasDerivAt (fun t => transportMatrix W P r t a b) (dK s a b) s
  /-- ... and continuous. -/
  dK_cont : ∀ a b, Continuous fun s => dK s a b
  /-- The derivative of each source entry. -/
  dsrc : Real -> DegreeIndex d r -> Complex
  /-- ... certified. -/
  dsrc_is_deriv : ∀ a s,
    HasDerivAt (fun t => blockSource W P base target r t a) (dsrc s a) s
  /-- ... and continuous. -/
  dsrc_cont : ∀ a, Continuous fun s => dsrc s a

/-! ## One constructed block -/

set_option maxHeartbeats 1000000 in
/-- **One homogeneous amplitude block, constructed.**  The degree-`r` block
equation is solved by the repository's block ODE and inserted into the
amplitude; on the paper interval the *actual* `jetTransport` coefficient at
every multi-index of degree `r` equals the prescribed target.  Nothing about
the outcome is assumed. -/
theorem exists_amplitude_block (P : SourcePhaseJet W.G) (base : LongJet2 d)
    (target : Multiindex d -> Real -> Complex) (r : Nat)
    (hreg : AmplitudeBlockRegularity W P base target r)
    {lo hi : Real} (t0 : Icc lo hi) (x0 : DegreeBlock d r) :
    ∃ u : LongJet2 d,
      (∀ (a : Multiindex d) (s : Real), deg a ≠ r ->
        u.jet.c a s = base.jet.c a s) ∧
      (∀ (a : Multiindex d) (s : Real), deg a ≠ r ->
        u.djet.c a s = base.djet.c a s) ∧
      (∀ a : DegreeIndex d r,
        u.jet.c a.1 (t0 : Real) = base.jet.c a.1 (t0 : Real) + x0 a) ∧
      (∀ s ∈ Icc lo hi, ∀ a : Multiindex d, deg a = r ->
        W.jetTransport P u a s = target a s) := by
  classical
  obtain ⟨B, hBnn, hKb⟩ :=
    exists_transportMatrix_rowSum_bound W P hreg.dphiC1 r lo hi
  obtain ⟨c, c', c'', hc0, hcd, hc'd, _hc2, hceq⟩ :=
    exists_c2_blockSolution (fun s a b => transportMatrix W P r s a b) hreg.dK
      (fun s a => blockSource W P base target r s a) hreg.dsrc
      hreg.dK_is_deriv hreg.dK_cont hreg.dsrc_is_deriv hreg.dsrc_cont hBnn
      hKb t0 x0
  have hblk : ∀ (a : DegreeIndex d r) (s : Real),
      HasDerivAt (fun t : Real => base.jet.c a.1 t + c t a)
        (base.djet.c a.1 s + c' s a) s :=
    fun a s => (base.djet_is_deriv a.1 s).add (hcd a s)
  have hdblk : ∀ (a : DegreeIndex d r) (s : Real),
      HasDerivAt (fun t : Real => base.djet.c a.1 t + c' t a)
        (base.djet.dc a.1 s + c'' s a) s :=
    fun a s => (base.djet.hasDeriv a.1 s).add (hc'd a s)
  obtain ⟨Jet, hJet⟩ : ∃ Jet : LongJet d, Jet = insertBlock base.jet r
      (fun s a => base.jet.c a.1 s + c s a)
      (fun s a => base.djet.c a.1 s + c' s a) hblk := ⟨_, rfl⟩
  obtain ⟨DJet, hDJet⟩ : ∃ DJet : LongJet d, DJet = insertBlock base.djet r
      (fun s a => base.djet.c a.1 s + c' s a)
      (fun s a => base.djet.dc a.1 s + c'' s a) hdblk := ⟨_, rfl⟩
  have hJet_off : ∀ (a : Multiindex d) (s : Real), deg a ≠ r ->
      Jet.c a s = base.jet.c a s := by
    intro a s ha
    rw [hJet, insertBlock_c_of_deg_ne _ _ _ _ _ ha]
  have hDJet_off : ∀ (a : Multiindex d) (s : Real), deg a ≠ r ->
      DJet.c a s = base.djet.c a s := by
    intro a s ha
    rw [hDJet, insertBlock_c_of_deg_ne _ _ _ _ _ ha]
  have hJetdc_off : ∀ (a : Multiindex d) (s : Real), deg a ≠ r ->
      Jet.dc a s = base.djet.c a s := by
    intro a s ha
    rw [hJet, insertBlock_dc_of_deg_ne _ _ _ _ _ ha]
    exact (base.jet.hasDeriv a s).unique (base.djet_is_deriv a s)
  have hJet_idx : ∀ (a : DegreeIndex d r) (s : Real),
      Jet.c a.1 s = base.jet.c a.1 s + c s a := by
    intro a s
    rw [hJet]
    exact insertBlock_c_index base.jet r _ _ hblk a s
  have hDJet_idx : ∀ (a : DegreeIndex d r) (s : Real),
      DJet.c a.1 s = base.djet.c a.1 s + c' s a := by
    intro a s
    rw [hDJet]
    exact insertBlock_c_index base.djet r _ _ hdblk a s
  have hJetdc_idx : ∀ (a : DegreeIndex d r) (s : Real),
      Jet.dc a.1 s = base.djet.c a.1 s + c' s a := by
    intro a s
    rw [hJet]
    exact insertBlock_dc_index base.jet r _ _ hblk a s
  have hdc : ∀ (a : Multiindex d) (s : Real), DJet.c a s = Jet.dc a s := by
    intro a s
    by_cases ha : deg a = r
    · have hidx : a ∈ degreeEq d r := mem_degreeEq.2 ha
      rw [hDJet_idx ⟨a, hidx⟩ s, hJetdc_idx ⟨a, hidx⟩ s]
    · rw [hDJet_off a s ha, hJetdc_off a s ha]
  obtain ⟨u, hu1, hu2⟩ : ∃ u : LongJet2 d, u.jet = Jet ∧ u.djet = DJet :=
    ⟨{ jet := Jet
       djet := DJet
       djet_is_deriv := fun a s => by
         rw [hdc a s]
         exact Jet.hasDeriv a s }, rfl, rfl⟩
  refine ⟨u, ?_, ?_, ?_, ?_⟩
  · intro a s ha
    rw [hu1]
    exact hJet_off a s ha
  · intro a s ha
    rw [hu2]
    exact hDJet_off a s ha
  · intro a
    rw [hu1, hJet_idx a (t0 : Real), hc0]
  · intro s hs a ha
    have hidx : a ∈ degreeEq d r := mem_degreeEq.2 ha
    have hform := jetTransport_block_matrix_form W P u base r s ⟨a, hidx⟩
      (fun b hb => by rw [hu1]; exact hJet_off b s hb)
      (fun b hb => by rw [hu2]; exact hDJet_off b s hb)
    have hd : u.djet.c a s - base.djet.c a s = c' s ⟨a, hidx⟩ := by
      rw [hu2, hDJet_idx ⟨a, hidx⟩ s]
      ring
    have hj : ∀ beta : DegreeIndex d r,
        transportMatrix W P r s ⟨a, hidx⟩ beta
            * (u.jet.c beta.1 s - base.jet.c beta.1 s)
          = transportMatrix W P r s ⟨a, hidx⟩ beta * c s beta := by
      intro beta
      rw [hu1, hJet_idx beta s]
      ring
    rw [hd, Finset.sum_congr rfl fun beta (_ : beta ∈ Finset.univ) => hj beta]
      at hform
    have heq := hceq s hs ⟨a, hidx⟩
    have hsrc : blockSource W P base target r s ⟨a, hidx⟩
        = target a s - W.jetTransport P base a s := rfl
    rw [hsrc] at heq
    linear_combination hform + heq

/-! ## The two cases of the paper's hierarchy -/

/-- **Leading amplitude.**  With target zero the constructed block makes the
actual `T_phi a_0` vanish at every multi-index of degree `r`. -/
theorem exists_amplitude_block_transport_zero (P : SourcePhaseJet W.G)
    (base : LongJet2 d) (r : Nat)
    (hreg : AmplitudeBlockRegularity W P base (fun _ _ => 0) r)
    {lo hi : Real} (t0 : Icc lo hi) (x0 : DegreeBlock d r) :
    ∃ u : LongJet2 d,
      (∀ (a : Multiindex d) (s : Real), deg a ≠ r ->
        u.jet.c a s = base.jet.c a s) ∧
      (∀ (a : Multiindex d) (s : Real), deg a ≠ r ->
        u.djet.c a s = base.djet.c a s) ∧
      (∀ a : DegreeIndex d r,
        u.jet.c a.1 (t0 : Real) = base.jet.c a.1 (t0 : Real) + x0 a) ∧
      (∀ s ∈ Icc lo hi, ∀ a : Multiindex d, deg a = r ->
        W.jetTransport P u a s = 0) :=
  exists_amplitude_block W P base (fun _ _ => 0) r hreg t0 x0

/-- **Higher amplitudes.**  With target `- i Box_g a_{k-1}` the constructed
block makes the actual hierarchy expression `- i T_phi a_k + Box_g a_{k-1}`
vanish at every multi-index of degree `r`.  The sign is the source's. -/
theorem exists_amplitude_block_hierarchy_zero (P : SourcePhaseJet W.G)
    (base ukm : LongJet2 d) (r : Nat)
    (hreg : AmplitudeBlockRegularity W P base
      (fun a s => -Complex.I * W.jetBox ukm a s) r)
    {lo hi : Real} (t0 : Icc lo hi) (x0 : DegreeBlock d r) :
    ∃ u : LongJet2 d,
      (∀ (a : Multiindex d) (s : Real), deg a ≠ r ->
        u.jet.c a s = base.jet.c a s) ∧
      (∀ (a : Multiindex d) (s : Real), deg a ≠ r ->
        u.djet.c a s = base.djet.c a s) ∧
      (∀ a : DegreeIndex d r,
        u.jet.c a.1 (t0 : Real) = base.jet.c a.1 (t0 : Real) + x0 a) ∧
      (∀ s ∈ Icc lo hi, ∀ a : Multiindex d, deg a = r ->
        W.jetHierarchy P u ukm a s = 0) := by
  obtain ⟨u, h1, h2, h3, h4⟩ :=
    exists_amplitude_block W P base (fun a s => -Complex.I * W.jetBox ukm a s) r
      hreg t0 x0
  refine ⟨u, h1, h2, h3, ?_⟩
  intro s hs a ha
  rw [jetHierarchy, h4 s hs a ha]
  have hI : -Complex.I * (-Complex.I * W.jetBox ukm a s) + W.jetBox ukm a s
      = 0 := by
    have hsq : Complex.I * Complex.I = -1 := Complex.I_mul_I
    linear_combination (W.jetBox ukm a s) * hsq
  exact hI

end LiuWang2025SemilinearWaveAmplitudeBlockRecursion
