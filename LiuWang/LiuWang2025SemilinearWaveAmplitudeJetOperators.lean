import LiuWang.LiuWang2025SemilinearWaveSameDegreeMatrix
import LiuWang.LiuWang2025SemilinearWaveFermiEikonalJet

/-!
# Liu-Wang semilinear wave: jet-level wave and transport operators

The phase recursion is complete through arbitrary finite transverse order.  The
amplitude recursion is not, and this file is the first half of the reason: it
defines the *actual* coordinate operators the amplitude hierarchy needs, in the
same ordinary-monomial transverse jet calculus the phase recursion uses, with no
field asserting that anything vanishes.

In Fermi coordinates the wave operator is

  `Box_g u = A^{ss} d_s^2 u + 2 sum_i A^{si} d_s d_i u + sum_{ij} A^{ij} d_i d_j u
             + beta^s d_s u + sum_i beta^i d_i u`,

so an amplitude must carry two certified longitudinal derivatives, not one.
`LongJet2` is that data.  `jetBox` is the operator above, `jetTransport` is

  `T_phi a = 2 <d phi, d a>_g - (Box_g phi) a`,

and `jetHierarchy` is the source's `- i T_phi a_k + Box_g a_{k-1}`.

**Honest statement of the remaining obstruction.**  For a general quadratic
phase the same-degree part of `T_phi` contains `4 (A M z) . grad_z a_r`, which
mixes distinct degree-`r` monomials exactly as the eikonal's same-degree
operator does.  `LiuWang2025SemilinearWaveJetTowerRecursion.TowerData` carries a
*scalar* coefficient `q_alpha` per multi-index and solves one scalar ODE per
index, so it represents that operator only when `A M` is diagonal.  Nothing in
this file or in `TowerData` proves such a diagonal reduction, and the scalar
tower must therefore not be called paper-complete.  The finite-dimensional block
replacement is the same construction that fixed the phase recursion; it is not
carried out here.
-/

noncomputable section

open scoped BigOperators
open Set

namespace LiuWang2025SemilinearWaveAmplitudeJetOperators

open LiuWang2025SemilinearWaveTransverseJet
open LiuWang2025SemilinearWaveLongitudinalJet
open LiuWang2025SemilinearWaveLongitudinalJet.LongJet
open LiuWang2025SemilinearWaveJetOperators
open LiuWang2025SemilinearWaveDegreeBlock
open LiuWang2025SemilinearWaveMetricJetPhaseHierarchy

variable {d : Nat}

/-! ## Twice longitudinally differentiable jets -/

/-- A transverse jet carrying two certified longitudinal derivatives.  The
second derivative is *not* an assumption about the operator: it is the data the
coordinate wave operator needs to be definable at all. -/
structure LongJet2 (d : Nat) where
  /-- The coefficient family. -/
  jet : LongJet d
  /-- Its longitudinal derivative, itself a jet (so a second derivative is
  certified). -/
  djet : LongJet d
  /-- `djet` really is the longitudinal derivative of `jet`. -/
  djet_is_deriv : ∀ a s, HasDerivAt (jet.c a) (djet.c a s) s

namespace LongJet2

variable (u : LongJet2 d)

/-- The second longitudinal derivative, certified by `djet`'s own jet
structure. -/
def ddc (a : Multiindex d) (s : Real) : Complex := u.djet.dc a s

theorem hasDerivAt_djet (a : Multiindex d) (s : Real) :
    HasDerivAt (u.djet.c a) (u.ddc a s) s := u.djet.hasDeriv a s

end LongJet2

/-- A source phase jet is in particular a twice differentiable jet. -/
def ofSourcePhase {G : FermiMetricJet d} (P : SourcePhaseJet G) : LongJet2 d where
  jet := P.phi
  djet := P.dphi
  djet_is_deriv := P.dphi_is_deriv

/-! ## Convolution against a raw coefficient family -/

/-- Convolution of a jet with an arbitrary coefficient family.  Needed because
the second longitudinal derivative of a `LongJet2` is a family, not a jet. -/
def convRaw (u : LongJet d) (v : Multiindex d -> Real -> Complex)
    (a : Multiindex d) (s : Real) : Complex :=
  ∑ b ∈ below a, u.c b s * v (a - b) s

theorem convRaw_mul (u w : LongJet d) (a : Multiindex d) (s : Real) :
    convRaw u (fun b t => w.c b t) a s = (mul u w).c a s := rfl

theorem convRaw_congr {u : LongJet d} {v v' : Multiindex d -> Real -> Complex}
    {a : Multiindex d} {s : Real}
    (h : ∀ b, deg b ≤ deg a -> v b s = v' b s) :
    convRaw u v a s = convRaw u v' a s := by
  refine Finset.sum_congr rfl fun b hb => ?_
  have hd := deg_add_deg_sub hb
  rw [h (a - b) (by omega)]

theorem convRaw_vanish {u : LongJet d} {v : Multiindex d -> Real -> Complex}
    {a : Multiindex d} {s : Real} {p q : Nat}
    (hu : ∀ b, deg b < p -> u.c b s = 0)
    (hv : ∀ b, deg b < q -> v b s = 0) (ha : deg a < p + q) :
    convRaw u v a s = 0 := by
  refine Finset.sum_eq_zero fun b hb => ?_
  have hd := deg_add_deg_sub hb
  by_cases hbp : deg b < p
  · rw [hu b hbp, zero_mul]
  · rw [hv (a - b) (by omega), mul_zero]

/-! ## The coordinate wave operator -/

/-- The first-order coefficients of `Box_g` in Fermi coordinates, on top of the
metric jet.  Nothing here says that any expression vanishes. -/
structure WaveJetData (d : Nat) where
  /-- The metric jet. -/
  G : FermiMetricJet d
  /-- The coefficient of `d_s u`. -/
  betaS : LongJet d
  /-- The coefficients of `d_i u`. -/
  betaT : Fin d -> LongJet d

namespace WaveJetData

variable (W : WaveJetData d)

/-- **The actual coordinate wave operator, on transverse jets.**  Every term is
a genuine convolution of the metric coefficients against the corresponding
derivative of the amplitude. -/
def jetBox (u : LongJet2 d) (a : Multiindex d) (s : Real) : Complex :=
  convRaw W.G.Ass u.ddc a s
    + 2 * ∑ i, (mul (W.G.Bs i) (transverseDeriv i u.djet)).c a s
    + ∑ i, ∑ j,
        (mul (W.G.Att i j)
          (transverseDeriv i (transverseDeriv j u.jet))).c a s
    + (mul W.betaS u.djet).c a s
    + ∑ i, (mul (W.betaT i) (transverseDeriv i u.jet)).c a s

/-- **The transport operator** `T_phi a = 2 <d phi, d a>_g - (Box_g phi) a`. -/
def jetTransport (P : SourcePhaseJet W.G) (u : LongJet2 d) (a : Multiindex d)
    (s : Real) : Complex :=
  2 * ((mul W.G.Ass (mul P.dphi u.djet)).c a s
      + ∑ i, ((mul (W.G.Bs i) (mul P.dphi (transverseDeriv i u.jet))).c a s
            + (mul (W.G.Bs i) (mul (transverseDeriv i P.phi) u.djet)).c a s)
      + ∑ i, ∑ j,
          (mul (W.G.Att i j)
            (mul (transverseDeriv i P.phi) (transverseDeriv j u.jet))).c a s)
    - convRaw u.jet (fun b t => W.jetBox (ofSourcePhase P) b t) a s

/-- **The source's amplitude hierarchy expression** `- i T_phi a_k + Box_g
a_{k-1}`.  The sign convention is the paper's: the hierarchy asks that this
vanish. -/
def jetHierarchy (P : SourcePhaseJet W.G) (uk ukm : LongJet2 d)
    (a : Multiindex d) (s : Real) : Complex :=
  -Complex.I * W.jetTransport P uk a s + W.jetBox ukm a s

end WaveJetData

/-! ## Locality, regularity, and the value at the centre -/

namespace WaveJetData

variable (W : WaveJetData d)

theorem transverseDeriv_c_zero_eq (u : LongJet d) (i : Fin d) (s : Real) :
    (transverseDeriv i u).c 0 s = u.c (Pi.single i 1) s := by
  show ((((0 : Multiindex d) i) + 1 : Nat) : Complex)
    * u.c ((0 : Multiindex d) + Pi.single i 1) s = _
  rw [show (0 : Multiindex d) + Pi.single i 1 = (Pi.single i 1 : Multiindex d)
      from by
        funext k
        show 0 + _ = _
        omega]
  show ((0 + 1 : Nat) : Complex) * _ = _
  push_cast
  ring

/-- **Locality in transverse degree.**  The degree-`a` coefficient of `jetBox`
reads the amplitude only through degree `deg a + 2`, and its longitudinal
derivatives only through degree `deg a + 1` and `deg a`. -/
theorem jetBox_congr {u v : LongJet2 d} {a : Multiindex d} {s : Real}
    (hjet : ∀ b, deg b ≤ deg a + 2 -> u.jet.c b s = v.jet.c b s)
    (hdjet : ∀ b, deg b ≤ deg a + 1 -> u.djet.c b s = v.djet.c b s)
    (hddc : ∀ b, deg b ≤ deg a -> u.ddc b s = v.ddc b s) :
    W.jetBox u a s = W.jetBox v a s := by
  rw [jetBox, jetBox]
  congr 1
  · congr 1
    · congr 1
      · congr 1
        · exact convRaw_congr hddc
        · congr 1
          refine Finset.sum_congr rfl fun i _ => ?_
          refine mul_c_congr (fun _ _ => rfl) fun b hb => ?_
          exact transverseDeriv_c_congr (hdjet _ (by
            rw [deg_add_single]
            omega))
      · refine Finset.sum_congr rfl fun i _ => ?_
        refine Finset.sum_congr rfl fun j _ => ?_
        refine mul_c_congr (fun _ _ => rfl) fun b hb => ?_
        refine transverseDeriv_c_congr (transverseDeriv_c_congr (hjet _ ?_))
        rw [deg_add_single, deg_add_single]
        omega
    · refine mul_c_congr (fun _ _ => rfl) fun b hb => hdjet b (by omega)
  · refine Finset.sum_congr rfl fun i _ => ?_
    refine mul_c_congr (fun _ _ => rfl) fun b hb => ?_
    exact transverseDeriv_c_congr (hjet _ (by
      rw [deg_add_single]
      omega))

/-- **Continuity of the wave operator's coefficients**, from the certified
derivative data alone.  `C1` of the second longitudinal derivative is the only
extra regularity used. -/
theorem continuous_jetBox (u : LongJet2 d) (hu : u.djet.C1)
    (a : Multiindex d) : Continuous fun s => W.jetBox u a s := by
  refine Continuous.add (Continuous.add (Continuous.add (Continuous.add ?_ ?_) ?_)
    ((mul W.betaS u.djet).continuous_c a)) ?_
  · refine continuous_finset_sum _ fun b _ => ?_
    exact (W.G.Ass.continuous_c b).mul (hu (a - b))
  · exact continuous_const.mul (continuous_finset_sum _ fun i _ =>
      (mul (W.G.Bs i) (transverseDeriv i u.djet)).continuous_c a)
  · exact continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ =>
      (mul (W.G.Att i j)
        (transverseDeriv i (transverseDeriv j u.jet))).continuous_c a
  · exact continuous_finset_sum _ fun i _ =>
      (mul (W.betaT i) (transverseDeriv i u.jet)).continuous_c a

theorem continuous_jetTransport (P : SourcePhaseJet W.G) (u : LongJet2 d)
    (hP : P.dphi.C1) (a : Multiindex d) :
    Continuous fun s => W.jetTransport P u a s := by
  refine Continuous.sub ?_ ?_
  · refine continuous_const.mul (Continuous.add (Continuous.add
      ((mul W.G.Ass (mul P.dphi u.djet)).continuous_c a) ?_) ?_)
    · exact continuous_finset_sum _ fun i _ =>
        ((mul (W.G.Bs i) (mul P.dphi (transverseDeriv i u.jet))).continuous_c a).add
          ((mul (W.G.Bs i)
            (mul (transverseDeriv i P.phi) u.djet)).continuous_c a)
    · exact continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ =>
        (mul (W.G.Att i j)
          (mul (transverseDeriv i P.phi) (transverseDeriv j u.jet))).continuous_c a
  · refine continuous_finset_sum _ fun b _ => ?_
    exact (u.jet.continuous_c b).mul
      (W.continuous_jetBox (ofSourcePhase P) hP (a - b))

/-- **The value of `Box_g phi` at the centre of the beam.**  Everything except
the transverse Hessian pairing and the distinguished first-order coefficient is
killed by the source's low-order phase normalizations. -/
theorem jetBox_phase_deg_zero (P : SourcePhaseJet W.G) (s : Real) :
    W.jetBox (ofSourcePhase P) 0 s
      = (∑ i, ∑ j, (W.G.Att i j).c 0 s
          * (transverseDeriv i (transverseDeriv j P.phi)).c 0 s)
        + (W.betaT W.G.i1).c 0 s := by
  have hdd : (ofSourcePhase P).ddc 0 s = 0 := by
    have hconst : P.dphi.c 0 = fun _ : Real => (0 : Complex) :=
      funext fun t => P.dphi_zero t
    have h1 : HasDerivAt (P.dphi.c 0) (P.dphi.dc 0 s) s := P.dphi.hasDeriv 0 s
    rw [hconst] at h1
    exact h1.unique (hasDerivAt_const s (0 : Complex))
  have hterm1 : convRaw W.G.Ass (ofSourcePhase P).ddc 0 s = 0 := by
    rw [convRaw, below_zero, Finset.sum_singleton,
      show (0 : Multiindex d) - 0 = (0 : Multiindex d) from by
        funext k
        show (0 : Nat) - 0 = 0
        omega, hdd, mul_zero]
  have hterm2 : ∀ i : Fin d,
      (mul (W.G.Bs i) (transverseDeriv i P.dphi)).c 0 s = 0 := by
    intro i
    rw [mul_c_zero, transverseDeriv_c_zero_eq, P.dphi_one i s, mul_zero]
  have hterm4 : (mul W.betaS P.dphi).c 0 s = 0 := by
    rw [mul_c_zero, P.dphi_zero s, mul_zero]
  have hterm5 : ∀ i : Fin d,
      (mul (W.betaT i) (transverseDeriv i P.phi)).c 0 s
        = (W.betaT i).c 0 s * (if i = W.G.i1 then 1 else 0) := by
    intro i
    rw [mul_c_zero, transverseDeriv_c_zero_eq, P.phi_one i s]
  have hbeta : ∑ i, (W.betaT i).c 0 s * (if i = W.G.i1 then 1 else 0)
      = (W.betaT W.G.i1).c 0 s := by
    rw [Finset.sum_eq_single_of_mem W.G.i1 (Finset.mem_univ _)]
    · rw [if_pos rfl, mul_one]
    · intro i _ hi
      rw [if_neg hi, mul_zero]
  have hhess : ∀ i j : Fin d,
      (mul (W.G.Att i j) (transverseDeriv i (transverseDeriv j P.phi))).c 0 s
        = (W.G.Att i j).c 0 s
          * (transverseDeriv i (transverseDeriv j P.phi)).c 0 s :=
    fun i j => mul_c_zero _ _ s
  show convRaw W.G.Ass (ofSourcePhase P).ddc 0 s
      + 2 * ∑ i, (mul (W.G.Bs i) (transverseDeriv i P.dphi)).c 0 s
      + ∑ i, ∑ j,
          (mul (W.G.Att i j)
            (transverseDeriv i (transverseDeriv j P.phi))).c 0 s
      + (mul W.betaS P.dphi).c 0 s
      + ∑ i, (mul (W.betaT i) (transverseDeriv i P.phi)).c 0 s
    = _
  rw [hterm1, Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hterm2 i,
    Finset.sum_const_zero, hterm4,
    Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hterm5 i, hbeta,
    Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) =>
      Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) => hhess i j]
  ring

/-- **The transverse Hessian of a quadratic phase at the centre.**  Both the
diagonal and the off-diagonal case give `2 M_{ij}`, in the same ordinary
monomial normalization the phase recursion uses. -/
theorem hessian_at_center (P : SourcePhaseJet W.G)
    (M : Real -> Fin d -> Fin d -> Complex) {s : Real}
    (hsymm : ∀ p q, M s p q = M s q p)
    (hphi2 : ∀ a : Multiindex d, deg a = 2 -> P.phi.c a s = quadCoeff (M s) a)
    (i j : Fin d) :
    (transverseDeriv i (transverseDeriv j P.phi)).c 0 s = 2 * M s i j := by
  rw [transverseDeriv_c_zero_eq]
  show (((Pi.single i 1 : Multiindex d) j + 1 : Nat) : Complex)
    * P.phi.c ((Pi.single i 1 : Multiindex d) + Pi.single j 1) s = _
  rw [hphi2 _ (by rw [deg_add_single, deg_single])]
  by_cases hij : i = j
  · rw [hij, quadCoeff_diag, Pi.single_eq_same]
    push_cast
    ring
  · rw [quadCoeff_offDiag _ hij, Pi.single_eq_of_ne (Ne.symm hij), hsymm j i]
    push_cast
    ring

/-- **Agreement at the centre with the source's transport coefficient.**  With
`C = 2 A^{transverse}(s,0)`, the value of `Box_g phi` at the centre is
`trace (C M) + beta^{i1}`, which is exactly
`- TransportCenterGeometry.transportCoefficient`. -/
theorem jetBox_phase_deg_zero_trace (P : SourcePhaseJet W.G)
    (M : Real -> Fin d -> Fin d -> Complex) {s : Real}
    (hsymm : ∀ p q, M s p q = M s q p)
    (hphi2 : ∀ a : Multiindex d, deg a = 2 -> P.phi.c a s = quadCoeff (M s) a) :
    W.jetBox (ofSourcePhase P) 0 s
      = (∑ i, ∑ j, (2 * (W.G.Att i j).c 0 s) * M s i j)
        + (W.betaT W.G.i1).c 0 s := by
  rw [W.jetBox_phase_deg_zero P s]
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [W.hessian_at_center P M hsymm hphi2 i j]
  ring

/-- ... and that double sum is the matrix trace `trace (C M)` for symmetric
data. -/
theorem sum_eq_trace (C M : Matrix (Fin d) (Fin d) Complex)
    (hM : ∀ p q, M p q = M q p) :
    (∑ i, ∑ j, C i j * M i j) = Matrix.trace (C * M) := by
  rw [Matrix.trace]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.diag_apply, Matrix.mul_apply]
  exact Finset.sum_congr rfl fun j _ => by rw [hM j i]

end WaveJetData

end LiuWang2025SemilinearWaveAmplitudeJetOperators
