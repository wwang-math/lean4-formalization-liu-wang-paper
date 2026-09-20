import LiuWang.LiuWang2025SemilinearWaveJetOperators

/-!
# Liu-Wang semilinear wave: the Fermi metric jet and the source's phase

Section 3 of the source works in Fermi coordinates along the central null
geodesic and imposes three normalizations on the inverse metric there:

* the row and the column of the transverse block against the null covector
  vanish on the central curve (`nullRow`, `nullCol`);
* the component `A^{i1 i1}` vanishes to second order there (`nullSecondOrder`);
* the longitudinal-transverse pairing against the null covector is normalized
  to one (`longitudinalNormalization`).

`FermiMetricJet` records exactly those, as conditions on the metric jets.  It
records **no** statement about the eikonal, the transport operator or any
cancellation.

`SourcePhaseJet` records the source's prescribed low-order phase, `phi_0 = 0`
and `phi_1 = z^{i1}`, together with the fact that `dphi` really is the
longitudinal derivative of `phi`.  The two facts the recursion needs about
`dphi` at low degree are then *derived* by uniqueness of derivatives, not
assumed.

From this data the degree-zero and degree-one eikonal cancellations of the
source are obtained by computation (`eikonal_deg_zero`, `eikonal_deg_one`), and
the locality of the coefficient calculus is recorded in the form the triangular
recursion needs (`eikonal_local`).

## What is *not* established here

The general-degree decomposition of `jetEikonal` into
`2 lambda d_s c_alpha + q_alpha c_alpha + (lower degrees)` is **not** proved,
and the following obstruction is the reason.  Expanding the transverse block
`sum_{ij} A^{ij} d_i phi d_j phi`, the part linear in the degree-`r`
coefficients comes from pairing `d_i phi` at a degree-`(r-1)` index against
`d_j phi` at a degree-one index.  The convolution constraint then forces the
degree-`r` phase index to be `alpha + e_i - e_k`, where `e_k` is the degree-one
index of the second factor.  For `k = i` this is `alpha`, but for `k /= i` it is
a *different* multi-index of the same total degree.  So the degree-`r` block of
the eikonal system couples distinct multi-indices: the operator is
`4 (A M z) . grad_z`, which is diagonal on monomials only if `A M` is diagonal.

`LiuWang2025SemilinearWaveJetTowerRecursion.TowerData` carries a *scalar*
longitudinal coefficient `q_alpha`, so it cannot represent that block.
Representing it needs a matrix-valued coefficient together with a fundamental
system along the geodesic, or equivalently the flow of `z' = 4 A M z`.

That generalization *is* now carried out, in
`LiuWang2025SemilinearWaveSameDegreeMatrix` and
`LiuWang2025SemilinearWavePhaseUpdate`: the degree-`r` block is a genuine
finite-dimensional linear system whose matrix is built from the metric and the
already constructed lower phase alone (`phaseEikonalMatrix`, shown in
`phaseEikonalMatrix_local` to read the phase only through degree two, which is
the repository's form of `4 (A M z) . grad_z`), whose source is the eikonal of
that lower phase (`phaseSource`), and which is solved constructively by
`LiuWang2025SemilinearWaveDegreeBlockODE.exists_c2_blockSolution`.
`LiuWang2025SemilinearWavePhaseUpdate.exists_phase_update` performs one full
phase step unconditionally, and `exists_phase_cancelling_upto` iterates it to
arbitrary finite order.

Degree two is handled separately, by its own genuinely nonlinear equation:
`LiuWang2025SemilinearWaveSameDegreeMatrix.quadraticSelfTerm` is the Riccati
term, proved to vanish identically above degree two and proved to be a quadratic
form in the block at degree two.  `LiuWang2025SemilinearWaveRiccatiPhaseBridge`
connects it to the repository's generated Hamiltonian Riccati flow: the Fermi
first-order normalization removes the linear block operator, the ordinary
monomial normalizations are proved (`quadCoeff M` is the coefficient family of
`z^T M z`, its gradient has degree-one coefficients `2 M_{ki}`, the source's
`C` is twice the degree-zero transverse block and its `D = (1/4) d_p d_q g^{11}`
is half the degree-two coefficient family of `A^{i1 i1}`), and the generated
flow is extended to a globally twice differentiable path.
`exists_phase_from_riccati` then produces, from metric and Riccati input alone,
a source phase jet whose actual `jetEikonal` coefficients vanish through any
prescribed finite degree.

`eikonalRiccatiAndTransportHierarchy` nevertheless stays open: the amplitude
hierarchy has not yet been made paper-specific.  Nothing here claims that the
amplitude recursion, or the paper's theorem as a whole, has been formalized.
-/

noncomputable section

open scoped BigOperators

namespace LiuWang2025SemilinearWaveMetricJetPhaseHierarchy

open LiuWang2025SemilinearWaveTransverseJet
open LiuWang2025SemilinearWaveLongitudinalJet
open LiuWang2025SemilinearWaveLongitudinalJet.LongJet
open LiuWang2025SemilinearWaveJetOperators

variable {d : Nat}

/-! ## The Fermi normalization of the inverse metric -/

/-- The inverse metric of the source's Fermi chart, presented as longitudinal
jets, together with the normalizations Section 3 imposes along the central null
geodesic.  Only chart normalizations appear; no cancellation is recorded. -/
structure FermiMetricJet (d : Nat) where
  /-- The longitudinal-longitudinal block `A^{ss}`. -/
  Ass : LongJet d
  /-- The longitudinal-transverse block `A^{s i}`. -/
  Bs : Fin d -> LongJet d
  /-- The transverse-transverse block `A^{i j}`. -/
  Att : Fin d -> Fin d -> LongJet d
  /-- The distinguished transverse direction carrying the linear phase. -/
  i1 : Fin d
  /-- The null row: `A^{i1 j}` vanishes on the central curve. -/
  nullRow : ∀ j s, (Att i1 j).c 0 s = 0
  /-- The null column. -/
  nullCol : ∀ i s, (Att i i1).c 0 s = 0
  /-- `A^{i1 i1}` vanishes to second order on the central curve. -/
  nullSecondOrder : ∀ k s, (Att i1 i1).c (Pi.single k 1) s = 0
  /-- The longitudinal pairing against the null covector is normalized. -/
  longitudinalNormalization : ∀ s, (Bs i1).c 0 s = 1

/-! ## The source's prescribed low-order phase -/

/-- The source's phase jet: `phi_0 = 0`, `phi_1 = z^{i1}`, and `dphi` really is
the longitudinal derivative of `phi`. -/
structure SourcePhaseJet (G : FermiMetricJet d) where
  /-- The phase coefficient family. -/
  phi : LongJet d
  /-- Its longitudinal derivative family. -/
  dphi : LongJet d
  /-- `dphi` is certified to be the derivative of `phi`. -/
  dphi_is_deriv : ∀ a s, HasDerivAt (phi.c a) (dphi.c a s) s
  /-- The source's `phi_0 = 0`. -/
  phi_zero : ∀ s, phi.c 0 s = 0
  /-- The source's `phi_1 = z^{i1}`. -/
  phi_one : ∀ i s, phi.c (Pi.single i 1) s = if i = G.i1 then 1 else 0

namespace SourcePhaseJet

variable {G : FermiMetricJet d} (P : SourcePhaseJet G)

/-- **Derived, not assumed.**  The longitudinal derivative vanishes at the
centre because the degree-zero phase coefficient is the zero function. -/
theorem dphi_zero (s : Real) : P.dphi.c 0 s = 0 := by
  have hconst : P.phi.c 0 = fun _ : Real => (0 : Complex) := funext P.phi_zero
  have h1 : HasDerivAt (P.phi.c 0) (P.dphi.c 0 s) s := P.dphi_is_deriv 0 s
  rw [hconst] at h1
  exact h1.unique (hasDerivAt_const s (0 : Complex))

/-- **Derived, not assumed.**  The linear phase is independent of the geodesic
parameter, so its longitudinal derivative vanishes. -/
theorem dphi_one (k : Fin d) (s : Real) : P.dphi.c (Pi.single k 1) s = 0 := by
  have hconst : P.phi.c (Pi.single k 1)
      = fun _ : Real => (if k = G.i1 then (1 : Complex) else 0) :=
    funext (P.phi_one k)
  have h1 : HasDerivAt (P.phi.c (Pi.single k 1)) (P.dphi.c (Pi.single k 1) s) s :=
    P.dphi_is_deriv (Pi.single k 1) s
  rw [hconst] at h1
  exact h1.unique (hasDerivAt_const s _)

/-! ## The low-degree eikonal cancellations, derived -/

/-- **Degree-zero eikonal cancellation.**  The whole degree-zero coefficient
collapses to `A^{i1 i1}` on the central curve, which the null row kills. -/
theorem eikonal_deg_zero (s : Real) :
    jetEikonal G.Ass G.Bs G.Att P.phi P.dphi 0 s = 0 :=
  jetEikonal_coeff_zero_eq_zero G.Ass G.Bs G.Att P.phi P.dphi G.i1 s
    (P.dphi_zero s) (fun i => P.phi_one i s) (G.nullRow G.i1 s)

/-- **Degree-one eikonal cancellation.**  The three surviving terms are killed
by the `s`-independence of the linear phase, by the null row and column, and by
the second-order vanishing of `A^{i1 i1}`. -/
theorem eikonal_deg_one (k : Fin d) (s : Real) :
    jetEikonal G.Ass G.Bs G.Att P.phi P.dphi (Pi.single k 1) s = 0 :=
  jetEikonal_coeff_one_eq_zero G.Ass G.Bs G.Att P.phi P.dphi G.i1 k s
    (P.dphi_zero s) (fun i => P.phi_one i s) (P.dphi_one k s)
    (fun j => G.nullRow j s) (fun i => G.nullCol i s) (G.nullSecondOrder k s)

/-- **Locality of the eikonal coefficient.**  The degree-`alpha` coefficient
reads the phase only up to total degree `deg alpha + 1` and its longitudinal
derivative only up to `deg alpha`.  This is the triangularity input the
recursion needs, in the form in which it is actually true. -/
theorem eikonal_local {P' : SourcePhaseJet G} {a : Multiindex d} {s : Real}
    (hphi : ∀ b, deg b ≤ deg a + 1 -> P.phi.c b s = P'.phi.c b s)
    (hdphi : ∀ b, deg b ≤ deg a -> P.dphi.c b s = P'.dphi.c b s) :
    jetEikonal G.Ass G.Bs G.Att P.phi P.dphi a s
      = jetEikonal G.Ass G.Bs G.Att P'.phi P'.dphi a s :=
  jetEikonal_congr G.Ass G.Bs G.Att hphi hdphi

end SourcePhaseJet

/-! ## Triangularity of the actual variable-metric eikonal system -/

/-- **The variable-metric eikonal system is triangular.**  Through
`transverseDeriv` the degree-`alpha` coefficient can in principle read the phase
at total degree `deg alpha + 1`; those contributions pair a top-degree gradient
against the constant gradient of the linear phase, and the chart's null row and
column annihilate them.  So the degree-`alpha` coefficient depends on the phase
only through degrees at most `deg alpha`.  Nothing to this effect is
assumed. -/
theorem eikonal_triangular {G : FermiMetricJet d} (P P' : SourcePhaseJet G)
    {a : Multiindex d} {s : Real} (ha : 1 ≤ deg a)
    (hphi : ∀ b, deg b ≤ deg a -> P.phi.c b s = P'.phi.c b s)
    (hdphi : ∀ b, deg b ≤ deg a -> P.dphi.c b s = P'.dphi.c b s) :
    jetEikonal G.Ass G.Bs G.Att P.phi P.dphi a s
      = jetEikonal G.Ass G.Bs G.Att P'.phi P'.dphi a s :=
  jetEikonal_congr_of_deg_le G.Ass G.Bs G.Att G.i1 ha hphi hdphi
    (fun i => P.phi_one i s) (P.dphi_zero s) (fun k => P.dphi_one k s)
    (fun j => G.nullRow j s) (fun i => G.nullCol i s)

/-- **The longitudinal derivative enters with the source's `2 lambda`.**
Comparing two phases that agree in all degrees strictly below `deg alpha`, the
longitudinal-longitudinal block cancels, the longitudinal-transverse block
contributes exactly `2 A^{s i1}(0) (d_s c_alpha - d_s c'_alpha)`, and the whole
remaining dependence sits in the transverse-transverse block, displayed
explicitly on the right.  The coefficient `2 A^{s i1}(0)` is computed from the
metric, not posited. -/
theorem eikonal_longitudinal {G : FermiMetricJet d} (P P' : SourcePhaseJet G)
    {a : Multiindex d} {s : Real} (ha : 2 ≤ deg a)
    (hphi : ∀ b, deg b < deg a -> P.phi.c b s = P'.phi.c b s)
    (hdphi : ∀ b, deg b < deg a -> P.dphi.c b s = P'.dphi.c b s) :
    jetEikonal G.Ass G.Bs G.Att P.phi P.dphi a s
        - jetEikonal G.Ass G.Bs G.Att P'.phi P'.dphi a s
      = 2 * ((G.Bs G.i1).c 0 s * (P.dphi.c a s - P'.dphi.c a s))
        + ∑ i, ∑ j, ((mul (G.Att i j)
              (mul (transverseDeriv i P.phi) (transverseDeriv j P.phi))).c a s
            - (mul (G.Att i j)
              (mul (transverseDeriv i P'.phi) (transverseDeriv j P'.phi))).c a s) :=
  jetEikonal_longitudinal_extraction G.Ass G.Bs G.Att G.i1 ha hphi hdphi
    (fun i => P.phi_one i s) (P.dphi_zero s) (fun k => P.dphi_one k s)

/-- With the source's normalization `A^{s i1}(0) = 1`, the longitudinal
derivative enters with coefficient exactly `2`. -/
theorem eikonal_longitudinal_normalized {G : FermiMetricJet d}
    (P P' : SourcePhaseJet G) {a : Multiindex d} {s : Real} (ha : 2 ≤ deg a)
    (hphi : ∀ b, deg b < deg a -> P.phi.c b s = P'.phi.c b s)
    (hdphi : ∀ b, deg b < deg a -> P.dphi.c b s = P'.dphi.c b s) :
    jetEikonal G.Ass G.Bs G.Att P.phi P.dphi a s
        - jetEikonal G.Ass G.Bs G.Att P'.phi P'.dphi a s
      = 2 * (P.dphi.c a s - P'.dphi.c a s)
        + ∑ i, ∑ j, ((mul (G.Att i j)
              (mul (transverseDeriv i P.phi) (transverseDeriv j P.phi))).c a s
            - (mul (G.Att i j)
              (mul (transverseDeriv i P'.phi) (transverseDeriv j P'.phi))).c a s) := by
  rw [eikonal_longitudinal P P' ha hphi hdphi, G.longitudinalNormalization s,
    one_mul]

/-! ## The same-degree operator

Subtracting two phases that agree outside one homogeneous degree, the
longitudinal-longitudinal block cancels and the longitudinal-transverse block
leaves `2 d_s c_r`.  What remains is the transverse-transverse block applied to
the perturbation: the operator below.  It is *derived* from `jetEikonal`, not
posited, and it is proved linear in the perturbation, so it is a genuine linear
operator on the finite dimensional space of homogeneous coefficients of that
degree.
-/

/-- The same-degree operator: the transverse-transverse block of the eikonal,
linearized in the perturbation `delta`.  Its two summands are exactly the two
cross terms of the bilinear expansion of `sum_{ij} A^{ij} d_i phi d_j phi`. -/
def sameDegreeOp (Att : Fin d -> Fin d -> LongJet d)
    (phi phi' delta : LongJet d) (a : Multiindex d) (s : Real) : Complex :=
  ∑ i, ∑ j, ((mul (Att i j)
        (mul (transverseDeriv i delta) (transverseDeriv j phi))).c a s
      + (mul (Att i j)
        (mul (transverseDeriv i phi') (transverseDeriv j delta))).c a s)

/-- **The degree-`alpha` block decomposition of the actual eikonal.**  For two
source phase jets agreeing in all degrees strictly below `deg alpha`, the
difference of their eikonal coefficients is exactly twice the difference of the
longitudinal derivatives plus the same-degree operator applied to the
difference of the phases.  Both pieces are computed from the metric. -/
theorem eikonal_block_decomposition {G : FermiMetricJet d}
    (P P' : SourcePhaseJet G) {a : Multiindex d} {s : Real} (ha : 2 ≤ deg a)
    (hphi : ∀ b, deg b < deg a -> P.phi.c b s = P'.phi.c b s)
    (hdphi : ∀ b, deg b < deg a -> P.dphi.c b s = P'.dphi.c b s) :
    jetEikonal G.Ass G.Bs G.Att P.phi P.dphi a s
        - jetEikonal G.Ass G.Bs G.Att P'.phi P'.dphi a s
      = 2 * (P.dphi.c a s - P'.dphi.c a s)
        + sameDegreeOp G.Att P.phi P'.phi (sub P.phi P'.phi) a s := by
  rw [eikonal_longitudinal_normalized P P' ha hphi hdphi]
  congr 1
  refine Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => ?_
  refine Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) => ?_
  rw [mul_c_sub_right]
  have hinner : ∀ b, deg b ≤ deg a ->
      (sub (mul (transverseDeriv i P.phi) (transverseDeriv j P.phi))
        (mul (transverseDeriv i P'.phi) (transverseDeriv j P'.phi))).c b s
      = (add (mul (transverseDeriv i (sub P.phi P'.phi)) (transverseDeriv j P.phi))
          (mul (transverseDeriv i P'.phi)
            (transverseDeriv j (sub P.phi P'.phi)))).c b s := by
    intro b _
    show (mul (transverseDeriv i P.phi) (transverseDeriv j P.phi)).c b s
        - (mul (transverseDeriv i P'.phi) (transverseDeriv j P'.phi)).c b s
      = (mul (transverseDeriv i (sub P.phi P'.phi)) (transverseDeriv j P.phi)).c b s
        + (mul (transverseDeriv i P'.phi)
            (transverseDeriv j (sub P.phi P'.phi))).c b s
    rw [mul_c_diff]
    congr 1
    · exact mul_c_congr
        (fun e _ => (transverseDeriv_c_sub i P.phi P'.phi e s).symm) (fun _ _ => rfl)
    · exact mul_c_congr (fun _ _ => rfl)
        (fun e _ => (transverseDeriv_c_sub j P.phi P'.phi e s).symm)
  rw [mul_c_congr (fun _ _ => rfl) hinner, mul_c_add_right]

/-- **The same-degree operator is additive.** -/
theorem sameDegreeOp_add (Att : Fin d -> Fin d -> LongJet d)
    (phi phi' delta delta' : LongJet d) (a : Multiindex d) (s : Real) :
    sameDegreeOp Att phi phi' (add delta delta') a s
      = sameDegreeOp Att phi phi' delta a s
        + sameDegreeOp Att phi phi' delta' a s := by
  rw [sameDegreeOp, sameDegreeOp, sameDegreeOp, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) => ?_
  have hL : (mul (Att i j)
        (mul (transverseDeriv i (add delta delta')) (transverseDeriv j phi))).c a s
      = (mul (Att i j)
          (mul (transverseDeriv i delta) (transverseDeriv j phi))).c a s
        + (mul (Att i j)
          (mul (transverseDeriv i delta') (transverseDeriv j phi))).c a s := by
    rw [← mul_c_add_right]
    refine mul_c_congr (fun _ _ => rfl) fun b _ => ?_
    exact mul_c_congr (fun e _ => transverseDeriv_c_add i delta delta' e s)
      (fun _ _ => rfl) |>.trans (mul_c_add_left _ _ _ b s)
  have hR : (mul (Att i j)
        (mul (transverseDeriv i phi') (transverseDeriv j (add delta delta')))).c a s
      = (mul (Att i j)
          (mul (transverseDeriv i phi') (transverseDeriv j delta))).c a s
        + (mul (Att i j)
          (mul (transverseDeriv i phi') (transverseDeriv j delta'))).c a s := by
    rw [← mul_c_add_right]
    refine mul_c_congr (fun _ _ => rfl) fun b _ => ?_
    exact mul_c_congr (fun _ _ => rfl)
      (fun e _ => transverseDeriv_c_add j delta delta' e s)
      |>.trans (mul_c_add_right _ _ _ b s)
  rw [hL, hR]
  ring

/-- **The same-degree operator is homogeneous.**  With additivity this makes it
a genuine complex-linear operator on the homogeneous coefficient block. -/
theorem sameDegreeOp_smul (Att : Fin d -> Fin d -> LongJet d)
    (phi phi' delta : LongJet d) (k : Complex) (a : Multiindex d) (s : Real) :
    sameDegreeOp Att phi phi' (smul k delta) a s
      = k * sameDegreeOp Att phi phi' delta a s := by
  rw [sameDegreeOp, sameDegreeOp, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) => ?_
  have hL : (mul (Att i j)
        (mul (transverseDeriv i (smul k delta)) (transverseDeriv j phi))).c a s
      = k * (mul (Att i j)
          (mul (transverseDeriv i delta) (transverseDeriv j phi))).c a s := by
    rw [← mul_c_smul_right]
    refine mul_c_congr (fun _ _ => rfl) fun b _ => ?_
    exact mul_c_congr (fun e _ => transverseDeriv_c_smul i k delta e s)
      (fun _ _ => rfl) |>.trans (mul_c_smul_left k _ _ b s)
  have hR : (mul (Att i j)
        (mul (transverseDeriv i phi') (transverseDeriv j (smul k delta)))).c a s
      = k * (mul (Att i j)
          (mul (transverseDeriv i phi') (transverseDeriv j delta))).c a s := by
    rw [← mul_c_smul_right]
    refine mul_c_congr (fun _ _ => rfl) fun b _ => ?_
    exact mul_c_congr (fun _ _ => rfl)
      (fun e _ => transverseDeriv_c_smul j k delta e s)
      |>.trans (mul_c_smul_right k _ _ b s)
  rw [hL, hR]
  ring

/-- **The same-degree operator distributes over finite sums of
perturbations.** -/
theorem sameDegreeOp_sum {iota : Type*} [Fintype iota]
    (Att : Fin d -> Fin d -> LongJet d) (phi phi' : LongJet d)
    (f : iota -> LongJet d) (a : Multiindex d) (s : Real) :
    sameDegreeOp Att phi phi' (sumJet f) a s
      = ∑ k, sameDegreeOp Att phi phi' (f k) a s := by
  have hL : ∀ i j : Fin d, (mul (Att i j)
        (mul (transverseDeriv i (sumJet f)) (transverseDeriv j phi))).c a s
      = ∑ k, (mul (Att i j)
          (mul (transverseDeriv i (f k)) (transverseDeriv j phi))).c a s := by
    intro i j
    have h1 : ∀ b, deg b ≤ deg a ->
        (mul (transverseDeriv i (sumJet f)) (transverseDeriv j phi)).c b s
          = (sumJet (fun k => mul (transverseDeriv i (f k))
              (transverseDeriv j phi))).c b s := by
      intro b _
      calc (mul (transverseDeriv i (sumJet f)) (transverseDeriv j phi)).c b s
          = (mul (sumJet (fun k => transverseDeriv i (f k)))
              (transverseDeriv j phi)).c b s :=
            mul_c_congr (fun e _ => transverseDeriv_c_sum i f e s) (fun _ _ => rfl)
        _ = ∑ k, (mul (transverseDeriv i (f k)) (transverseDeriv j phi)).c b s :=
            mul_c_sum_left _ _ b s
        _ = (sumJet (fun k => mul (transverseDeriv i (f k))
              (transverseDeriv j phi))).c b s := rfl
    rw [mul_c_congr (fun _ _ => rfl) h1, mul_c_sum_right]
  have hR : ∀ i j : Fin d, (mul (Att i j)
        (mul (transverseDeriv i phi') (transverseDeriv j (sumJet f)))).c a s
      = ∑ k, (mul (Att i j)
          (mul (transverseDeriv i phi') (transverseDeriv j (f k)))).c a s := by
    intro i j
    have h1 : ∀ b, deg b ≤ deg a ->
        (mul (transverseDeriv i phi') (transverseDeriv j (sumJet f))).c b s
          = (sumJet (fun k => mul (transverseDeriv i phi')
              (transverseDeriv j (f k)))).c b s := by
      intro b _
      calc (mul (transverseDeriv i phi') (transverseDeriv j (sumJet f))).c b s
          = (mul (transverseDeriv i phi')
              (sumJet (fun k => transverseDeriv j (f k)))).c b s :=
            mul_c_congr (fun _ _ => rfl) (fun e _ => transverseDeriv_c_sum j f e s)
        _ = ∑ k, (mul (transverseDeriv i phi') (transverseDeriv j (f k))).c b s :=
            mul_c_sum_right _ _ b s
        _ = (sumJet (fun k => mul (transverseDeriv i phi')
              (transverseDeriv j (f k)))).c b s := rfl
    rw [mul_c_congr (fun _ _ => rfl) h1, mul_c_sum_right]
  have hstep : ∀ i j : Fin d,
      ((mul (Att i j)
          (mul (transverseDeriv i (sumJet f)) (transverseDeriv j phi))).c a s
        + (mul (Att i j)
          (mul (transverseDeriv i phi') (transverseDeriv j (sumJet f)))).c a s)
      = ∑ k, ((mul (Att i j)
            (mul (transverseDeriv i (f k)) (transverseDeriv j phi))).c a s
          + (mul (Att i j)
            (mul (transverseDeriv i phi') (transverseDeriv j (f k)))).c a s) := by
    intro i j
    rw [hL i j, hR i j, ← Finset.sum_add_distrib]
  show (∑ i, ∑ j, _) = _
  rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) =>
    Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) => hstep i j]
  rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) =>
    Finset.sum_comm (s := (Finset.univ : Finset (Fin d)))
      (t := (Finset.univ : Finset iota)), Finset.sum_comm]
  rfl

/-- **The same-degree operator reads the perturbation locally.**  It sees
`delta` only at total degree at most `deg alpha + 1`, so on a perturbation
supported in one homogeneous degree it descends to that degree's block. -/
theorem sameDegreeOp_congr (Att : Fin d -> Fin d -> LongJet d)
    (phi phi' : LongJet d) {delta delta' : LongJet d} {a : Multiindex d}
    {s : Real} (h : ∀ b, deg b ≤ deg a + 1 -> delta.c b s = delta'.c b s) :
    sameDegreeOp Att phi phi' delta a s
      = sameDegreeOp Att phi phi' delta' a s := by
  have hgrad : ∀ (i : Fin d) b, deg b ≤ deg a ->
      (transverseDeriv i delta).c b s = (transverseDeriv i delta').c b s := by
    intro i b hb
    refine transverseDeriv_c_congr ?_
    exact h _ (by
      rw [LiuWang2025SemilinearWaveLongitudinalJet.deg_add_single]
      omega)
  refine Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => ?_
  refine Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) => ?_
  congr 1
  · exact mul_c_congr (fun _ _ => rfl)
      (fun b hb => mul_c_congr (fun e he => hgrad i e (by omega)) (fun _ _ => rfl))
  · exact mul_c_congr (fun _ _ => rfl)
      (fun b hb => mul_c_congr (fun _ _ => rfl) (fun e he => hgrad j e (by omega)))

/-! ## A jet supported at a single multi-index

Used to build genuinely non-constant, off-diagonal metric jets.
-/

/-- The longitudinal jet whose only nonzero coefficient sits at `a0`. -/
def singleJet (a0 : Multiindex d) (f g : Real -> Complex)
    (hf : ∀ s, HasDerivAt f (g s) s) : LongJet d where
  c := fun a s => if a = a0 then f s else 0
  dc := fun a s => if a = a0 then g s else 0
  hasDeriv := by
    intro a s
    by_cases h : a = a0
    · simpa [h] using hf s
    · simpa [h] using hasDerivAt_const s (0 : Complex)

@[simp] theorem singleJet_c_self (a0 : Multiindex d) (f g : Real -> Complex)
    (hf : ∀ s, HasDerivAt f (g s) s) (s : Real) :
    (singleJet a0 f g hf).c a0 s = f s := by
  simp [singleJet]

@[simp] theorem singleJet_c_other {a a0 : Multiindex d} (h : a ≠ a0)
    (f g : Real -> Complex) (hf : ∀ s, HasDerivAt f (g s) s) (s : Real) :
    (singleJet a0 f g hf).c a s = 0 := by
  simp [singleJet, h]

/-- The longitudinal jet whose only nonzero coefficient is a constant one at
`a0`: the standard basis vector of the homogeneous block. -/
def basisJet (a0 : Multiindex d) : LongJet d :=
  singleJet a0 (fun _ => 1) (fun _ => 0) (fun s => hasDerivAt_const s (1 : Complex))

@[simp] theorem basisJet_c (a0 b : Multiindex d) (s : Real) :
    (basisJet a0).c b s = if b = a0 then 1 else 0 := by
  show (if b = a0 then (1 : Complex) else 0) = _
  rfl

/-- The zero longitudinal jet. -/
def zeroJet (d : Nat) : LongJet d where
  c := fun _ _ => 0
  dc := fun _ _ => 0
  hasDeriv := fun _ s => hasDerivAt_const s (0 : Complex)

@[simp] theorem zeroJet_c (a : Multiindex d) (s : Real) :
    (zeroJet d).c a s = 0 := rfl

/-- **The same-degree operator is continuous in the longitudinal parameter**,
automatically. -/
theorem continuous_sameDegreeOp (Att : Fin d -> Fin d -> LongJet d)
    (phi phi' delta : LongJet d) (a : Multiindex d) :
    Continuous fun s => sameDegreeOp Att phi phi' delta a s :=
  continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ =>
    ((mul (Att i j)
        (mul (transverseDeriv i delta) (transverseDeriv j phi))).continuous_c a).add
      ((mul (Att i j)
        (mul (transverseDeriv i phi') (transverseDeriv j delta))).continuous_c a)

/-- The certified longitudinal derivative of the same-degree operator. -/
def sameDegreeOpDeriv (Att : Fin d -> Fin d -> LongJet d)
    (phi phi' delta : LongJet d) (a : Multiindex d) (s : Real) : Complex :=
  ∑ i, ∑ j, ((mul (Att i j)
        (mul (transverseDeriv i delta) (transverseDeriv j phi))).dc a s
      + (mul (Att i j)
        (mul (transverseDeriv i phi') (transverseDeriv j delta))).dc a s)

/-- **The same-degree operator is differentiable in the longitudinal
parameter**, automatically. -/
theorem hasDerivAt_sameDegreeOp (Att : Fin d -> Fin d -> LongJet d)
    (phi phi' delta : LongJet d) (a : Multiindex d) (s : Real) :
    HasDerivAt (fun v => sameDegreeOp Att phi phi' delta a v)
      (sameDegreeOpDeriv Att phi phi' delta a s) s := by
  refine hasDerivAt_finsum _ _ s fun i => ?_
  refine hasDerivAt_finsum _ _ s fun j => ?_
  exact ((mul (Att i j)
      (mul (transverseDeriv i delta) (transverseDeriv j phi))).hasDeriv a s).add
    ((mul (Att i j)
      (mul (transverseDeriv i phi') (transverseDeriv j delta))).hasDeriv a s)

theorem C1_basisJet (a0 : Multiindex d) : (basisJet a0).C1 := by
  intro a
  have hfun : (basisJet a0).dc a = fun _ : Real => (0 : Complex) := by
    funext s
    show (if a = a0 then (0 : Complex) else 0) = 0
    by_cases h : a = a0 <;> simp [h]
  rw [hfun]
  exact continuous_const

theorem C1_zeroJet (d : Nat) : (zeroJet d).C1 := fun _ => continuous_const

/-- **The same-degree operator's derivative is continuous** once the metric and
phase jets are, which is all the paper's smooth data provides anyway. -/
theorem continuous_sameDegreeOpDeriv {Att : Fin d -> Fin d -> LongJet d}
    {phi phi' delta : LongJet d} (hAtt : ∀ i j, (Att i j).C1)
    (hphi : phi.C1) (hphi' : phi'.C1) (hdelta : delta.C1) (a : Multiindex d) :
    Continuous fun s => sameDegreeOpDeriv Att phi phi' delta a s := by
  refine continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_
  exact ((hAtt i j).mul ((hdelta.transverseDeriv i).mul
      (hphi.transverseDeriv j)) a).add
    ((hAtt i j).mul ((hphi'.transverseDeriv i).mul
      (hdelta.transverseDeriv j)) a)

end LiuWang2025SemilinearWaveMetricJetPhaseHierarchy
