import LiuWang.LiuWang2025SemilinearWaveAmplitudeBlockRecursion

/-!
# Focused tests for the constructed amplitude block
-/

noncomputable section

open scoped BigOperators
open Set

open LiuWang2025SemilinearWaveTransverseJet
open LiuWang2025SemilinearWaveLongitudinalJet
open LiuWang2025SemilinearWaveLongitudinalJet.LongJet
open LiuWang2025SemilinearWaveJetOperators
open LiuWang2025SemilinearWaveDegreeBlock
open LiuWang2025SemilinearWaveMetricJetPhaseHierarchy
open LiuWang2025SemilinearWaveAmplitudeJetOperators
open LiuWang2025SemilinearWaveAmplitudeJetOperators.WaveJetData
open LiuWang2025SemilinearWaveAmplitudeSameDegreeMatrix
open LiuWang2025SemilinearWaveAmplitudeBlockRecursion

namespace LiuWangAmplitudeBlockRecursionTests

variable {d : Nat}

/-- The block source is computed from the actual transport operator, not
assumed. -/
example (W : WaveJetData d) (P : SourcePhaseJet W.G) (base : LongJet2 d)
    (target : Multiindex d -> Real -> Complex) (r : Nat) (s : Real)
    (alpha : DegreeIndex d r) :
    blockSource W P base target r s alpha
      = target alpha.1 s - W.jetTransport P base alpha.1 s := rfl

/-- **Cancellation of the actual transport coefficient** after solving and
inserting the block, for the leading amplitude. -/
example (W : WaveJetData d) (P : SourcePhaseJet W.G) (base : LongJet2 d)
    (r : Nat) (hreg : AmplitudeBlockRegularity W P base (fun _ _ => 0) r)
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
  exists_amplitude_block_transport_zero W P base r hreg t0 x0

/-- **Cancellation of the actual hierarchy expression** `- i T_phi a_k +
Box_g a_{k-1}` after solving and inserting the block. -/
example (W : WaveJetData d) (P : SourcePhaseJet W.G) (base ukm : LongJet2 d)
    (r : Nat)
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
        W.jetHierarchy P u ukm a s = 0) :=
  exists_amplitude_block_hierarchy_zero W P base ukm r hreg t0 x0

#print axioms LiuWang2025SemilinearWaveAmplitudeBlockRecursion.exists_amplitude_block
#print axioms LiuWang2025SemilinearWaveAmplitudeBlockRecursion.exists_amplitude_block_transport_zero
#print axioms LiuWang2025SemilinearWaveAmplitudeBlockRecursion.exists_amplitude_block_hierarchy_zero

end LiuWangAmplitudeBlockRecursionTests
