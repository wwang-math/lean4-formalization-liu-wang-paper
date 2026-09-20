import LiuWang.LiuWang2025SemilinearWaveDegreeBlockODE
import LiuWang.LiuWang2025SemilinearWaveMetricJetPhaseHierarchy

/-!
# Liu-Wang semilinear wave: the same-degree operator as a matrix

`LiuWang2025SemilinearWaveMetricJetPhaseHierarchy.sameDegreeOp` was derived from
the actual variable-metric eikonal and proved linear in the perturbation.  This
file turns that linear map into the finite matrix the block ODE consumes.

The matrix entries are *computed*: `eikonalMatrix ... alpha beta` is the derived
operator applied to the standard basis jet at `beta`, read off at `alpha`.  The
representation theorem then says the operator is that matrix acting on the
block, which is proved by expanding a degree-`r`-supported perturbation as the
finite sum of its basis components and using the linearity already established.

`eikonal_block_matrix_form` is the payoff.  For two source phase jets differing
only in degree `r`, the difference of their *actual* `jetEikonal` coefficients
over the whole degree-`r` block is

  `2 (d_s c - d_s c') + K(s) (c - c')`,

which is exactly the shape of
`LiuWang2025SemilinearWaveDegreeBlockODE.blockField`.
-/

noncomputable section

open scoped BigOperators

namespace LiuWang2025SemilinearWaveSameDegreeMatrix

open LiuWang2025SemilinearWaveTransverseJet
open LiuWang2025SemilinearWaveLongitudinalJet
open LiuWang2025SemilinearWaveLongitudinalJet.LongJet
open LiuWang2025SemilinearWaveJetOperators
open LiuWang2025SemilinearWaveDegreeBlock
open LiuWang2025SemilinearWaveMetricJetPhaseHierarchy

variable {d : Nat}

/-! ## Expanding a homogeneous perturbation in the standard basis -/

/-- A perturbation supported in one homogeneous degree is the finite sum of the
single-index jets carrying its coefficients. -/
theorem sumSingle_c (delta : LongJet d) (r : Nat) (s : Real)
    (hsupp : ∀ b, deg b ≠ r -> delta.c b s = 0) (b : Multiindex d) :
    (sumJet (fun beta : DegreeIndex d r =>
        singleJet beta.1 (delta.c beta.1) (delta.dc beta.1)
          (delta.hasDeriv beta.1))).c b s = delta.c b s := by
  classical
  rw [sumJet_c]
  by_cases hb : deg b = r
  · have hmem : b ∈ degreeEq d r := mem_degreeEq.2 hb
    rw [Finset.sum_eq_single_of_mem (⟨b, hmem⟩ : DegreeIndex d r)
      (Finset.mem_univ _)]
    · exact singleJet_c_self b (delta.c b) (delta.dc b) (delta.hasDeriv b) s
    · intro beta _ hne
      refine singleJet_c_other ?_ _ _ _ s
      intro hcon
      exact hne (Subtype.ext hcon.symm)
  · refine (Finset.sum_eq_zero fun beta _ => ?_).trans (hsupp b hb).symm
    refine singleJet_c_other ?_ _ _ _ s
    intro hcon
    refine hb ?_
    rw [hcon]
    exact mem_degreeEq.1 beta.2

/-! ## The matrix -/

/-- **The matrix of the same-degree operator**, computed by applying the
derived operator to the standard basis jets. -/
def eikonalMatrix (Att : Fin d -> Fin d -> LongJet d) (phi phi' : LongJet d)
    (r : Nat) (s : Real) (alpha beta : DegreeIndex d r) : Complex :=
  sameDegreeOp Att phi phi' (basisJet beta.1) alpha.1 s

/-- **The same-degree operator is that matrix acting on the block.** -/
theorem sameDegreeOp_matrix (Att : Fin d -> Fin d -> LongJet d)
    (phi phi' delta : LongJet d) (r : Nat) (s : Real)
    (hsupp : ∀ b, deg b ≠ r -> delta.c b s = 0) (alpha : DegreeIndex d r) :
    sameDegreeOp Att phi phi' delta alpha.1 s
      = ∑ beta : DegreeIndex d r,
          eikonalMatrix Att phi phi' r s alpha beta * delta.c beta.1 s := by
  classical
  have hcongr : sameDegreeOp Att phi phi' delta alpha.1 s
      = sameDegreeOp Att phi phi' (sumJet (fun beta : DegreeIndex d r =>
          singleJet beta.1 (delta.c beta.1) (delta.dc beta.1)
            (delta.hasDeriv beta.1))) alpha.1 s :=
    sameDegreeOp_congr Att phi phi'
      (fun b _ => (sumSingle_c delta r s hsupp b).symm)
  rw [hcongr, sameDegreeOp_sum]
  refine Finset.sum_congr rfl fun beta _ => ?_
  have hb : sameDegreeOp Att phi phi'
        (singleJet beta.1 (delta.c beta.1) (delta.dc beta.1)
          (delta.hasDeriv beta.1)) alpha.1 s
      = sameDegreeOp Att phi phi'
        (smul (delta.c beta.1 s) (basisJet beta.1)) alpha.1 s := by
    refine sameDegreeOp_congr Att phi phi' fun b _ => ?_
    show (if b = beta.1 then delta.c beta.1 s else 0)
      = delta.c beta.1 s * (if b = beta.1 then (1 : Complex) else 0)
    by_cases hbb : b = beta.1 <;> simp [hbb]
  rw [hb, sameDegreeOp_smul, eikonalMatrix]
  ring

/-! ## The block form of the actual eikonal difference -/

/-- **The degree-`r` block form of the actual variable-metric eikonal.**  Two
source phase jets that differ only in degree `r` have eikonal coefficients
differing by `2 (d_s c - d_s c') + K(s) (c - c')` over the whole block, with `K`
the computed matrix.  This is exactly the shape of the block ODE's vector
field. -/
theorem eikonal_block_matrix_form {G : FermiMetricJet d}
    (P P' : SourcePhaseJet G) (r : Nat) (hr : 2 ≤ r) (s : Real)
    (alpha : DegreeIndex d r)
    (hphi : ∀ b, deg b < r -> P.phi.c b s = P'.phi.c b s)
    (hdphi : ∀ b, deg b < r -> P.dphi.c b s = P'.dphi.c b s)
    (hoff : ∀ b, r < deg b -> P.phi.c b s = P'.phi.c b s) :
    jetEikonal G.Ass G.Bs G.Att P.phi P.dphi alpha.1 s
        - jetEikonal G.Ass G.Bs G.Att P'.phi P'.dphi alpha.1 s
      = 2 * (P.dphi.c alpha.1 s - P'.dphi.c alpha.1 s)
        + ∑ beta : DegreeIndex d r,
            eikonalMatrix G.Att P.phi P'.phi r s alpha beta
              * (P.phi.c beta.1 s - P'.phi.c beta.1 s) := by
  have hdeg : deg alpha.1 = r := mem_degreeEq.1 alpha.2
  have hsupp : ∀ b, deg b ≠ r -> (sub P.phi P'.phi).c b s = 0 := by
    intro b hb
    show P.phi.c b s - P'.phi.c b s = 0
    rcases Nat.lt_or_ge (deg b) r with h | h
    · rw [hphi b h, sub_self]
    · rw [hoff b (by omega), sub_self]
  have hlow : ∀ b, deg b < deg alpha.1 -> P.phi.c b s = P'.phi.c b s := by
    intro b hb
    exact hphi b (by omega)
  have hlowd : ∀ b, deg b < deg alpha.1 -> P.dphi.c b s = P'.dphi.c b s := by
    intro b hb
    exact hdphi b (by omega)
  rw [eikonal_block_decomposition P P' (by omega) hlow hlowd,
    sameDegreeOp_matrix G.Att P.phi P'.phi (sub P.phi P'.phi) r s hsupp alpha]
  rfl

/-- **The block equation forces cancellation of the actual eikonal.**  If the
degree-`r` coefficients move so as to satisfy

  `2 (d_s c - d_s c') + K(s) (c - c') = - E(P')`,

which is the block ODE with the base phase's own eikonal as source, then every
degree-`r` coefficient of the *actual* `jetEikonal` of the moved phase
vanishes.  This is the recursion step of Section 3, stated against the real
eikonal rather than an abstract residual. -/
theorem eikonal_deg_eq_zero_of_blockEquation {G : FermiMetricJet d}
    (P P' : SourcePhaseJet G) (r : Nat) (hr : 2 ≤ r) (s : Real)
    (hphi : ∀ b, deg b < r -> P.phi.c b s = P'.phi.c b s)
    (hdphi : ∀ b, deg b < r -> P.dphi.c b s = P'.dphi.c b s)
    (hoff : ∀ b, r < deg b -> P.phi.c b s = P'.phi.c b s)
    (alpha : DegreeIndex d r)
    (hblock : 2 * (P.dphi.c alpha.1 s - P'.dphi.c alpha.1 s)
        + ∑ beta : DegreeIndex d r,
            eikonalMatrix G.Att P.phi P'.phi r s alpha beta
              * (P.phi.c beta.1 s - P'.phi.c beta.1 s)
      = - jetEikonal G.Ass G.Bs G.Att P'.phi P'.dphi alpha.1 s) :
    jetEikonal G.Ass G.Bs G.Att P.phi P.dphi alpha.1 s = 0 := by
  have h := eikonal_block_matrix_form P P' r hr s alpha hphi hdphi hoff
  rw [hblock] at h
  linear_combination h

/-! ## Removing the unknown phase from the matrix

For `r >= 3` the quadratic self-interaction of a perturbation supported in
degree `r` lands in transverse degree at least `2r - 2 > r`, so it cannot reach
the degree-`r` coefficient.  Consequently the same-degree operator does not see
the unknown degree-`r` phase at all: it is determined by the already
constructed base phase.  That is proved here, and the fixed matrix
`phaseEikonalMatrix` is built from the base phase alone.
-/

/-- **The quadratic self-interaction misses the degree.**  Two perturbations
supported in degree `r >= 3` interact only from transverse degree `2r - 2`
upwards, which is strictly above `r`. -/
theorem selfInteraction_vanishes (Att : Fin d -> Fin d -> LongJet d)
    {w v : LongJet d} {r : Nat} {s : Real} (hr : 3 ≤ r)
    (hw : ∀ b, deg b ≠ r -> w.c b s = 0)
    (hv : ∀ b, deg b ≠ r -> v.c b s = 0)
    {a : Multiindex d} (ha : deg a = r) (i j : Fin d) :
    (mul (Att i j)
      (mul (transverseDeriv i w) (transverseDeriv j v))).c a s = 0 := by
  obtain ⟨q, hq⟩ : ∃ q, r = q + 1 := ⟨r - 1, by omega⟩
  have hdw : ∀ b, deg b < q -> (transverseDeriv i w).c b s = 0 := by
    intro b hb
    show ((b i + 1 : Nat) : Complex) * w.c (b + Pi.single i 1) s = 0
    rw [hw _ (by
      rw [LiuWang2025SemilinearWaveLongitudinalJet.deg_add_single]
      omega), mul_zero]
  have hdv : ∀ b, deg b < q -> (transverseDeriv j v).c b s = 0 := by
    intro b hb
    show ((b j + 1 : Nat) : Complex) * v.c (b + Pi.single j 1) s = 0
    rw [hv _ (by
      rw [LiuWang2025SemilinearWaveLongitudinalJet.deg_add_single]
      omega), mul_zero]
  refine mul_c_vanish (p := 0) (q := q + q) vanish_below_zero ?_ (by omega)
  intro b hb
  exact mul_c_vanish hdw hdv (by omega)

/-- **The same-degree operator does not see the unknown phase.**  For
`r >= 3`, replacing the first phase argument by the base phase changes nothing,
because the only difference is the cross term between two degree-`r`
perturbations, which misses the degree. -/
theorem sameDegreeOp_base_of_supported (Att : Fin d -> Fin d -> LongJet d)
    {base delta phi w : LongJet d} {r : Nat} {s : Real} (hr : 3 ≤ r)
    (hdelta : ∀ b, deg b ≠ r -> delta.c b s = 0)
    (hw : ∀ b, deg b ≠ r -> w.c b s = 0)
    (hphi : ∀ b, phi.c b s = base.c b s + delta.c b s)
    {a : Multiindex d} (ha : deg a = r) :
    sameDegreeOp Att phi base w a s = sameDegreeOp Att base base w a s := by
  simp only [sameDegreeOp]
  refine Finset.sum_congr rfl fun i (_ : i ∈ (Finset.univ : Finset (Fin d))) => ?_
  refine Finset.sum_congr rfl fun j (_ : j ∈ (Finset.univ : Finset (Fin d))) => ?_
  congr 1
  -- only the first summand differs, and the difference is the cross term
  have hsplit : ∀ b, deg b ≤ deg a ->
      (mul (transverseDeriv i w) (transverseDeriv j phi)).c b s
        = (add (mul (transverseDeriv i w) (transverseDeriv j base))
            (mul (transverseDeriv i w) (transverseDeriv j delta))).c b s := by
    intro b _
    have hgrad : ∀ e, (transverseDeriv j phi).c e s
        = (add (transverseDeriv j base) (transverseDeriv j delta)).c e s := by
      intro e
      show ((e j + 1 : Nat) : Complex) * phi.c (e + Pi.single j 1) s
        = ((e j + 1 : Nat) : Complex) * base.c (e + Pi.single j 1) s
          + ((e j + 1 : Nat) : Complex) * delta.c (e + Pi.single j 1) s
      rw [hphi (e + Pi.single j 1)]
      ring
    calc (mul (transverseDeriv i w) (transverseDeriv j phi)).c b s
        = (mul (transverseDeriv i w)
            (add (transverseDeriv j base) (transverseDeriv j delta))).c b s :=
          mul_c_congr (fun _ _ => rfl) (fun e _ => hgrad e)
      _ = (mul (transverseDeriv i w) (transverseDeriv j base)).c b s
            + (mul (transverseDeriv i w) (transverseDeriv j delta)).c b s :=
          mul_c_add_right _ _ _ b s
      _ = (add (mul (transverseDeriv i w) (transverseDeriv j base))
            (mul (transverseDeriv i w) (transverseDeriv j delta))).c b s := rfl
  rw [mul_c_congr (fun _ _ => rfl) hsplit, mul_c_add_right,
    selfInteraction_vanishes Att hr hw hdelta ha i j, add_zero]

/-- **The fixed matrix of the degree-`r` eikonal system.**  Built from the
metric and the already constructed base phase only; the unknown degree-`r`
coefficients do not appear. -/
def phaseEikonalMatrix {G : FermiMetricJet d} (base : SourcePhaseJet G)
    (r : Nat) (s : Real) (alpha beta : DegreeIndex d r) : Complex :=
  sameDegreeOp G.Att base.phi base.phi (basisJet beta.1) alpha.1 s

/-- The matrix computed from the unknown phase coincides with the fixed one. -/
theorem eikonalMatrix_eq_phaseEikonalMatrix {G : FermiMetricJet d}
    (P base : SourcePhaseJet G) (r : Nat) (hr : 3 ≤ r) (s : Real)
    (hlow : ∀ b, deg b < r -> P.phi.c b s = base.phi.c b s)
    (hoff : ∀ b, r < deg b -> P.phi.c b s = base.phi.c b s)
    (alpha beta : DegreeIndex d r) :
    eikonalMatrix G.Att P.phi base.phi r s alpha beta
      = phaseEikonalMatrix base r s alpha beta := by
  have hdelta : ∀ b, deg b ≠ r -> (sub P.phi base.phi).c b s = 0 := by
    intro b hb
    show P.phi.c b s - base.phi.c b s = 0
    rcases Nat.lt_or_ge (deg b) r with h | h
    · rw [hlow b h, sub_self]
    · rw [hoff b (by omega), sub_self]
  have hw : ∀ b, deg b ≠ r -> (basisJet beta.1).c b s = 0 := by
    intro b hb
    rw [basisJet_c]
    refine if_neg fun hcon => hb ?_
    rw [hcon]
    exact mem_degreeEq.1 beta.2
  exact sameDegreeOp_base_of_supported G.Att hr hdelta hw
    (fun b => by show P.phi.c b s = base.phi.c b s + (P.phi.c b s - base.phi.c b s); ring)
    (mem_degreeEq.1 alpha.2)

/-- **The corrected degree-`r` identity.**  The eikonal of the moved phase is
the eikonal of the base, plus twice the longitudinal derivative of the moved
block, plus the *fixed* matrix acting on the moved block.  No unknown
coefficient hides inside the matrix. -/
theorem eikonal_block_fixed_matrix {G : FermiMetricJet d}
    (P base : SourcePhaseJet G) (r : Nat) (hr : 3 ≤ r) (s : Real)
    (alpha : DegreeIndex d r)
    (hlow : ∀ b, deg b < r -> P.phi.c b s = base.phi.c b s)
    (hdlow : ∀ b, deg b < r -> P.dphi.c b s = base.dphi.c b s)
    (hoff : ∀ b, r < deg b -> P.phi.c b s = base.phi.c b s) :
    jetEikonal G.Ass G.Bs G.Att P.phi P.dphi alpha.1 s
      = jetEikonal G.Ass G.Bs G.Att base.phi base.dphi alpha.1 s
        + 2 * (P.dphi.c alpha.1 s - base.dphi.c alpha.1 s)
        + ∑ beta : DegreeIndex d r, phaseEikonalMatrix base r s alpha beta
            * (P.phi.c beta.1 s - base.phi.c beta.1 s) := by
  have hform := eikonal_block_matrix_form P base r (by omega) s alpha hlow hdlow hoff
  have hmat : ∀ beta : DegreeIndex d r,
      eikonalMatrix G.Att P.phi base.phi r s alpha beta
        = phaseEikonalMatrix base r s alpha beta :=
    fun beta => eikonalMatrix_eq_phaseEikonalMatrix P base r hr s hlow hoff alpha beta
  rw [Finset.sum_congr rfl fun beta (_ : beta ∈ Finset.univ) => by
    rw [hmat beta]] at hform
  linear_combination hform

/-- **The fixed-matrix block equation forces cancellation of the actual
eikonal.** -/
theorem eikonal_deg_eq_zero_of_fixedBlockEquation {G : FermiMetricJet d}
    (P base : SourcePhaseJet G) (r : Nat) (hr : 3 ≤ r) (s : Real)
    (alpha : DegreeIndex d r)
    (hlow : ∀ b, deg b < r -> P.phi.c b s = base.phi.c b s)
    (hdlow : ∀ b, deg b < r -> P.dphi.c b s = base.dphi.c b s)
    (hoff : ∀ b, r < deg b -> P.phi.c b s = base.phi.c b s)
    (hblock : 2 * (P.dphi.c alpha.1 s - base.dphi.c alpha.1 s)
        + ∑ beta : DegreeIndex d r, phaseEikonalMatrix base r s alpha beta
            * (P.phi.c beta.1 s - base.phi.c beta.1 s)
      = - jetEikonal G.Ass G.Bs G.Att base.phi base.dphi alpha.1 s) :
    jetEikonal G.Ass G.Bs G.Att P.phi P.dphi alpha.1 s = 0 := by
  rw [eikonal_block_fixed_matrix P base r hr s alpha hlow hdlow hoff]
  linear_combination hblock

/-! ## Locality of the fixed matrix

The matrix at degree `r >= 3` reads the base phase only through transverse
degrees at most two -- that is, through the quadratic phase.  This is the
repository's form of the source's statement that the same-degree operator is
`4 (A M z) . grad_z`.  In particular later insertions, which only touch degrees
at least `r >= 3`, cannot alter it.
-/

theorem phaseEikonalMatrix_local {G : FermiMetricJet d}
    (base base' : SourcePhaseJet G) (r : Nat) (hr : 3 ≤ r) (s : Real)
    (hagree : ∀ b, deg b ≤ 2 -> base.phi.c b s = base'.phi.c b s)
    (alpha beta : DegreeIndex d r) :
    phaseEikonalMatrix base r s alpha beta
      = phaseEikonalMatrix base' r s alpha beta := by
  obtain ⟨q, hq⟩ : ∃ q, r = q + 1 := ⟨r - 1, by omega⟩
  have hdeg : deg alpha.1 = r := mem_degreeEq.1 alpha.2
  -- the basis jet is supported in degree `r`, so its gradient vanishes below `q`
  have hbj : ∀ (i : Fin d) b, deg b < q ->
      (transverseDeriv i (basisJet beta.1)).c b s = 0 := by
    intro i b hb
    show ((b i + 1 : Nat) : Complex) * (basisJet beta.1).c (b + Pi.single i 1) s = 0
    rw [basisJet_c, if_neg, mul_zero]
    intro hcon
    have : deg (b + (Pi.single i 1 : Multiindex d)) = r := by
      rw [hcon]
      exact mem_degreeEq.1 beta.2
    rw [LiuWang2025SemilinearWaveLongitudinalJet.deg_add_single] at this
    omega
  -- the two base phases have gradients agreeing below degree two
  have hgap : ∀ (j : Fin d) e, deg e < 2 ->
      (sub (transverseDeriv j base.phi) (transverseDeriv j base'.phi)).c e s = 0 := by
    intro j e he
    show ((e j + 1 : Nat) : Complex) * base.phi.c (e + Pi.single j 1) s
        - ((e j + 1 : Nat) : Complex) * base'.phi.c (e + Pi.single j 1) s = 0
    rw [hagree _ (by
      rw [LiuWang2025SemilinearWaveLongitudinalJet.deg_add_single]
      omega)]
    ring
  simp only [phaseEikonalMatrix, sameDegreeOp]
  refine Finset.sum_congr rfl fun i (_ : i ∈ (Finset.univ : Finset (Fin d))) => ?_
  refine Finset.sum_congr rfl fun j (_ : j ∈ (Finset.univ : Finset (Fin d))) => ?_
  congr 1
  · -- first summand: the base phase sits in the right slot
    have hzero : (mul (G.Att i j)
        (sub (mul (transverseDeriv i (basisJet beta.1)) (transverseDeriv j base.phi))
          (mul (transverseDeriv i (basisJet beta.1))
            (transverseDeriv j base'.phi)))).c alpha.1 s = 0 := by
      refine mul_c_vanish (p := 0) (q := q + 2) vanish_below_zero ?_ (by omega)
      intro b hb
      show (mul (transverseDeriv i (basisJet beta.1)) (transverseDeriv j base.phi)).c b s
        - (mul (transverseDeriv i (basisJet beta.1))
            (transverseDeriv j base'.phi)).c b s = 0
      rw [mul_c_sub_right]
      exact mul_c_vanish (hbj i) (hgap j) (by omega)
    have hsub := mul_c_sub_right (G.Att i j)
      (mul (transverseDeriv i (basisJet beta.1)) (transverseDeriv j base.phi))
      (mul (transverseDeriv i (basisJet beta.1)) (transverseDeriv j base'.phi))
      alpha.1 s
    rw [hzero] at hsub
    linear_combination hsub
  · -- second summand: the base phase sits in the left slot
    have hzero : (mul (G.Att i j)
        (sub (mul (transverseDeriv i base.phi) (transverseDeriv j (basisJet beta.1)))
          (mul (transverseDeriv i base'.phi)
            (transverseDeriv j (basisJet beta.1))))).c alpha.1 s = 0 := by
      refine mul_c_vanish (p := 0) (q := 2 + q) vanish_below_zero ?_ (by omega)
      intro b hb
      show (mul (transverseDeriv i base.phi) (transverseDeriv j (basisJet beta.1))).c b s
        - (mul (transverseDeriv i base'.phi)
            (transverseDeriv j (basisJet beta.1))).c b s = 0
      have hL := mul_c_sub_left (transverseDeriv i base.phi)
        (transverseDeriv i base'.phi) (transverseDeriv j (basisJet beta.1)) b s
      rw [hL]
      exact mul_c_vanish (hgap i) (hbj j) (by omega)
    have hsub := mul_c_sub_right (G.Att i j)
      (mul (transverseDeriv i base.phi) (transverseDeriv j (basisJet beta.1)))
      (mul (transverseDeriv i base'.phi) (transverseDeriv j (basisJet beta.1)))
      alpha.1 s
    rw [hzero] at hsub
    linear_combination hsub

/-! ## The source of the degree-`r` block equation -/

/-- The source of the degree-`r` block equation: minus the eikonal of the
already constructed base phase. -/
def phaseSource {G : FermiMetricJet d} (base : SourcePhaseJet G) (r : Nat)
    (s : Real) (alpha : DegreeIndex d r) : Complex :=
  - jetEikonal G.Ass G.Bs G.Att base.phi base.dphi alpha.1 s

/-- **The source depends only on the already constructed lower phase.**  By
triangularity of the variable-metric eikonal, two base phases agreeing through
degree `r` give the same source, so later insertions at higher degree do not
disturb it. -/
theorem phaseSource_stable {G : FermiMetricJet d}
    (base base' : SourcePhaseJet G) (r : Nat) (hr : 1 ≤ r) (s : Real)
    (alpha : DegreeIndex d r)
    (hagree : ∀ b, deg b ≤ r -> base.phi.c b s = base'.phi.c b s)
    (hdagree : ∀ b, deg b ≤ r -> base.dphi.c b s = base'.dphi.c b s) :
    phaseSource base r s alpha = phaseSource base' r s alpha := by
  have hdeg : deg alpha.1 = r := mem_degreeEq.1 alpha.2
  rw [phaseSource, phaseSource,
    eikonal_triangular base base' (by omega)
      (fun b hb => hagree b (by omega)) (fun b hb => hdagree b (by omega))]

/-- **The genuine paper block equation at degree `r >= 3`**, with a matrix and
a source both determined by the base phase.  Satisfying it kills every
degree-`r` coefficient of the actual `jetEikonal`. -/
theorem eikonal_deg_eq_zero_of_paperBlockEquation {G : FermiMetricJet d}
    (P base : SourcePhaseJet G) (r : Nat) (hr : 3 ≤ r) (s : Real)
    (alpha : DegreeIndex d r)
    (hlow : ∀ b, deg b < r -> P.phi.c b s = base.phi.c b s)
    (hdlow : ∀ b, deg b < r -> P.dphi.c b s = base.dphi.c b s)
    (hoff : ∀ b, r < deg b -> P.phi.c b s = base.phi.c b s)
    (hblock : 2 * (P.dphi.c alpha.1 s - base.dphi.c alpha.1 s)
        + ∑ beta : DegreeIndex d r, phaseEikonalMatrix base r s alpha beta
            * (P.phi.c beta.1 s - base.phi.c beta.1 s)
      = phaseSource base r s alpha) :
    jetEikonal G.Ass G.Bs G.Att P.phi P.dphi alpha.1 s = 0 :=
  eikonal_deg_eq_zero_of_fixedBlockEquation P base r hr s alpha hlow hdlow hoff hblock

/-! ## Automatic analytic inputs for the block ODE

Neither continuity nor differentiability of the matrix or of the source is an
assumption anywhere: both are forced by the derivative certificates already
carried by `LongJet`.
-/

/-- The certified longitudinal derivative of the fixed matrix. -/
def phaseEikonalMatrixDeriv {G : FermiMetricJet d} (base : SourcePhaseJet G)
    (r : Nat) (s : Real) (alpha beta : DegreeIndex d r) : Complex :=
  sameDegreeOpDeriv G.Att base.phi base.phi (basisJet beta.1) alpha.1 s

theorem hasDerivAt_phaseEikonalMatrix {G : FermiMetricJet d}
    (base : SourcePhaseJet G) (r : Nat) (alpha beta : DegreeIndex d r)
    (s : Real) :
    HasDerivAt (fun v => phaseEikonalMatrix base r v alpha beta)
      (phaseEikonalMatrixDeriv base r s alpha beta) s :=
  hasDerivAt_sameDegreeOp G.Att base.phi base.phi (basisJet beta.1) alpha.1 s

theorem continuous_phaseEikonalMatrix {G : FermiMetricJet d}
    (base : SourcePhaseJet G) (r : Nat) (alpha beta : DegreeIndex d r) :
    Continuous fun s => phaseEikonalMatrix base r s alpha beta :=
  continuous_sameDegreeOp G.Att base.phi base.phi (basisJet beta.1) alpha.1

theorem continuous_phaseEikonalMatrixDeriv {G : FermiMetricJet d}
    (base : SourcePhaseJet G) (hAtt : ∀ i j, (G.Att i j).C1)
    (hphi : base.phi.C1) (r : Nat) (alpha beta : DegreeIndex d r) :
    Continuous fun s => phaseEikonalMatrixDeriv base r s alpha beta :=
  continuous_sameDegreeOpDeriv hAtt hphi hphi (C1_basisJet beta.1) alpha.1

/-- The certified longitudinal derivative of the source. -/
def phaseSourceDeriv {G : FermiMetricJet d} (base : SourcePhaseJet G) (r : Nat)
    (s : Real) (alpha : DegreeIndex d r) : Complex :=
  - jetEikonalDeriv G.Ass G.Bs G.Att base.phi base.dphi alpha.1 s

theorem hasDerivAt_phaseSource {G : FermiMetricJet d} (base : SourcePhaseJet G)
    (r : Nat) (alpha : DegreeIndex d r) (s : Real) :
    HasDerivAt (fun v => phaseSource base r v alpha)
      (phaseSourceDeriv base r s alpha) s :=
  (hasDerivAt_jetEikonal G.Ass G.Bs G.Att base.phi base.dphi alpha.1 s).neg

theorem continuous_phaseSourceDeriv {G : FermiMetricJet d}
    (base : SourcePhaseJet G) (hAss : G.Ass.C1) (hBs : ∀ i, (G.Bs i).C1)
    (hAtt : ∀ i j, (G.Att i j).C1) (hphi : base.phi.C1) (hdphi : base.dphi.C1)
    (r : Nat) (alpha : DegreeIndex d r) :
    Continuous fun s => phaseSourceDeriv base r s alpha :=
  (continuous_jetEikonalDeriv hAss hBs hAtt hphi hdphi alpha.1).neg

/-! ## Degree two: the genuinely nonlinear Riccati step

For `r >= 3` the quadratic self-interaction of the degree-`r` perturbation
cannot reach degree `r` (`selfInteraction_vanishes`), which is what makes the
block equation linear.  At `r = 2` that same term is exactly the Riccati
quadratic `H C H`, and it is retained here.  Degree two is therefore treated by
its own equation, never by the linear `r >= 3` block equation.
-/

/-- The quadratic self-interaction of a perturbation: the Riccati nonlinearity.
-/
def quadraticSelfTerm (Att : Fin d -> Fin d -> LongJet d) (delta : LongJet d)
    (a : Multiindex d) (s : Real) : Complex :=
  ∑ i, ∑ j, (mul (Att i j)
    (mul (transverseDeriv i delta) (transverseDeriv j delta))).c a s

/-- **The same-degree operator at an arbitrary degree splits into its linear
part, evaluated at the base phase alone, plus the quadratic self-interaction.**
No support hypothesis is needed; for degrees at least three the second summand
then vanishes, and at degree two it is the Riccati term. -/
theorem sameDegreeOp_split (Att : Fin d -> Fin d -> LongJet d)
    {base delta phi : LongJet d} {s : Real}
    (hphi : ∀ b, phi.c b s = base.c b s + delta.c b s) (a : Multiindex d) :
    sameDegreeOp Att phi base delta a s
      = sameDegreeOp Att base base delta a s + quadraticSelfTerm Att delta a s := by
  rw [sameDegreeOp, sameDegreeOp, quadraticSelfTerm, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i (_ : i ∈ (Finset.univ : Finset (Fin d))) => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j (_ : j ∈ (Finset.univ : Finset (Fin d))) => ?_
  have hgrad : ∀ e, (transverseDeriv j phi).c e s
      = (add (transverseDeriv j base) (transverseDeriv j delta)).c e s := by
    intro e
    show ((e j + 1 : Nat) : Complex) * phi.c (e + Pi.single j 1) s
      = ((e j + 1 : Nat) : Complex) * base.c (e + Pi.single j 1) s
        + ((e j + 1 : Nat) : Complex) * delta.c (e + Pi.single j 1) s
    rw [hphi (e + Pi.single j 1)]
    ring
  have hinner : ∀ b, deg b ≤ deg a ->
      (mul (transverseDeriv i delta) (transverseDeriv j phi)).c b s
        = (add (mul (transverseDeriv i delta) (transverseDeriv j base))
            (mul (transverseDeriv i delta) (transverseDeriv j delta))).c b s := by
    intro b _
    calc (mul (transverseDeriv i delta) (transverseDeriv j phi)).c b s
        = (mul (transverseDeriv i delta)
            (add (transverseDeriv j base) (transverseDeriv j delta))).c b s :=
          mul_c_congr (fun _ _ => rfl) (fun e _ => hgrad e)
      _ = (mul (transverseDeriv i delta) (transverseDeriv j base)).c b s
            + (mul (transverseDeriv i delta) (transverseDeriv j delta)).c b s :=
          mul_c_add_right _ _ _ b s
      _ = (add (mul (transverseDeriv i delta) (transverseDeriv j base))
            (mul (transverseDeriv i delta) (transverseDeriv j delta))).c b s := rfl
  have hT1 : (mul (Att i j)
      (mul (transverseDeriv i delta) (transverseDeriv j phi))).c a s
      = (mul (Att i j)
          (mul (transverseDeriv i delta) (transverseDeriv j base))).c a s
        + (mul (Att i j)
          (mul (transverseDeriv i delta) (transverseDeriv j delta))).c a s := by
    rw [mul_c_congr (fun _ _ => rfl) hinner, mul_c_add_right]
  linear_combination hT1

/-- **The degree-two eikonal in Riccati form.**  The degree-two coefficients of
the actual variable-metric eikonal decompose into the base eikonal, twice the
longitudinal derivative of the degree-two block, the *linear* same-degree
operator built from the base phase, and the quadratic Riccati term. -/
theorem eikonal_deg_two_riccati_form {G : FermiMetricJet d}
    (P base : SourcePhaseJet G) (s : Real) (alpha : DegreeIndex d 2)
    (hlow : ∀ b, deg b < 2 -> P.phi.c b s = base.phi.c b s)
    (hdlow : ∀ b, deg b < 2 -> P.dphi.c b s = base.dphi.c b s)
    (hoff : ∀ b, 2 < deg b -> P.phi.c b s = base.phi.c b s) :
    jetEikonal G.Ass G.Bs G.Att P.phi P.dphi alpha.1 s
      = jetEikonal G.Ass G.Bs G.Att base.phi base.dphi alpha.1 s
        + 2 * (P.dphi.c alpha.1 s - base.dphi.c alpha.1 s)
        + ∑ beta : DegreeIndex d 2, phaseEikonalMatrix base 2 s alpha beta
            * (P.phi.c beta.1 s - base.phi.c beta.1 s)
        + quadraticSelfTerm G.Att (sub P.phi base.phi) alpha.1 s := by
  have hdeg : deg alpha.1 = 2 := mem_degreeEq.1 alpha.2
  have hdec := eikonal_block_decomposition P base (a := alpha.1) (s := s)
    (by omega) (fun b hb => hlow b (by omega)) (fun b hb => hdlow b (by omega))
  have hsplit := sameDegreeOp_split G.Att
    (base := base.phi) (delta := sub P.phi base.phi) (phi := P.phi) (s := s)
    (fun b => by
      show P.phi.c b s = base.phi.c b s + (P.phi.c b s - base.phi.c b s)
      ring) alpha.1
  have hsupp : ∀ b, deg b ≠ 2 -> (sub P.phi base.phi).c b s = 0 := by
    intro b hb
    show P.phi.c b s - base.phi.c b s = 0
    rcases Nat.lt_or_ge (deg b) 2 with h | h
    · rw [hlow b h, sub_self]
    · rw [hoff b (by omega), sub_self]
  have hmat := sameDegreeOp_matrix G.Att base.phi base.phi
    (sub P.phi base.phi) 2 s hsupp alpha
  have hentry : ∀ beta : DegreeIndex d 2,
      eikonalMatrix G.Att base.phi base.phi 2 s alpha beta
          * (sub P.phi base.phi).c beta.1 s
        = phaseEikonalMatrix base 2 s alpha beta
          * (P.phi.c beta.1 s - base.phi.c beta.1 s) := fun beta => rfl
  rw [Finset.sum_congr rfl fun beta (_ : beta ∈ Finset.univ) => hentry beta] at hmat
  rw [hmat] at hsplit
  rw [hsplit] at hdec
  linear_combination hdec

/-- **The degree-two Riccati equation forces cancellation of the actual
eikonal.**  This is the degree-two analogue of
`eikonal_deg_eq_zero_of_paperBlockEquation`, with the nonlinear term present. -/
theorem eikonal_deg_two_eq_zero_of_riccatiEquation {G : FermiMetricJet d}
    (P base : SourcePhaseJet G) (s : Real) (alpha : DegreeIndex d 2)
    (hlow : ∀ b, deg b < 2 -> P.phi.c b s = base.phi.c b s)
    (hdlow : ∀ b, deg b < 2 -> P.dphi.c b s = base.dphi.c b s)
    (hoff : ∀ b, 2 < deg b -> P.phi.c b s = base.phi.c b s)
    (hric : 2 * (P.dphi.c alpha.1 s - base.dphi.c alpha.1 s)
        + ∑ beta : DegreeIndex d 2, phaseEikonalMatrix base 2 s alpha beta
            * (P.phi.c beta.1 s - base.phi.c beta.1 s)
        + quadraticSelfTerm G.Att (sub P.phi base.phi) alpha.1 s
      = phaseSource base 2 s alpha) :
    jetEikonal G.Ass G.Bs G.Att P.phi P.dphi alpha.1 s = 0 := by
  rw [eikonal_deg_two_riccati_form P base s alpha hlow hdlow hoff]
  rw [phaseSource] at hric
  linear_combination hric

/-- **For degrees at least three the Riccati term is absent.**  The same split
that produces the nonlinearity at degree two proves it cannot occur higher up,
which is why the two degrees must be treated by different equations. -/
theorem quadraticSelfTerm_eq_zero_of_three_le (Att : Fin d -> Fin d -> LongJet d)
    {delta : LongJet d} {r : Nat} {s : Real} (hr : 3 ≤ r)
    (hdelta : ∀ b, deg b ≠ r -> delta.c b s = 0)
    {a : Multiindex d} (ha : deg a = r) :
    quadraticSelfTerm Att delta a s = 0 := by
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
  exact selfInteraction_vanishes Att hr hdelta hdelta ha i j

/-- The Riccati term depends on the perturbation only through its
coefficients. -/
theorem quadraticSelfTerm_congr (Att : Fin d -> Fin d -> LongJet d)
    {u v : LongJet d} {s : Real} (h : ∀ b, u.c b s = v.c b s)
    (a : Multiindex d) :
    quadraticSelfTerm Att u a s = quadraticSelfTerm Att v a s := by
  refine Finset.sum_congr rfl fun i (_ : i ∈ (Finset.univ : Finset (Fin d))) => ?_
  refine Finset.sum_congr rfl fun j (_ : j ∈ (Finset.univ : Finset (Fin d))) => ?_
  refine mul_c_congr (fun _ _ => rfl) fun b _ => ?_
  exact mul_c_congr (fun e _ => transverseDeriv_c_congr (h (e + Pi.single i 1)))
    (fun e _ => transverseDeriv_c_congr (h (e + Pi.single j 1)))

/-! ## The Riccati term is a genuine quadratic form in the degree-two block

The degree-two equation is therefore a polynomial (Riccati) system whose
quadratic coefficients are built from the metric alone -- the repository's form
of the source's `H C H`.
-/

/-- The bilinear form underlying the Riccati term. -/
def riccatiForm (Att : Fin d -> Fin d -> LongJet d) (u v : LongJet d)
    (a : Multiindex d) (s : Real) : Complex :=
  ∑ i, ∑ j, (mul (Att i j)
    (mul (transverseDeriv i u) (transverseDeriv j v))).c a s

theorem quadraticSelfTerm_eq_riccatiForm (Att : Fin d -> Fin d -> LongJet d)
    (delta : LongJet d) (a : Multiindex d) (s : Real) :
    quadraticSelfTerm Att delta a s = riccatiForm Att delta delta a s := rfl

/-- Reading the bilinear form as the same-degree operator with the *left* slot
carrying the perturbation. -/
theorem riccatiForm_eq_sameDegreeOp_left (Att : Fin d -> Fin d -> LongJet d)
    (u v : LongJet d) (a : Multiindex d) (s : Real) :
    riccatiForm Att u v a s = sameDegreeOp Att v (zeroJet d) u a s := by
  rw [riccatiForm, sameDegreeOp]
  refine Finset.sum_congr rfl fun i (_ : i ∈ (Finset.univ : Finset (Fin d))) => ?_
  refine Finset.sum_congr rfl fun j (_ : j ∈ (Finset.univ : Finset (Fin d))) => ?_
  have hz : ∀ (k : Fin d) e, (transverseDeriv k (zeroJet d)).c e s = 0 := by
    intro k e
    show ((e k + 1 : Nat) : Complex) * (0 : Complex) = 0
    ring
  have hinner : ∀ b,
      (mul (transverseDeriv i (zeroJet d)) (transverseDeriv j u)).c b s = 0 :=
    fun b => mul_c_vanish (p := deg b + 1) (q := 0) (fun e _ => hz i e)
      vanish_below_zero (by omega)
  have houter : (mul (Att i j)
      (mul (transverseDeriv i (zeroJet d)) (transverseDeriv j u))).c a s = 0 :=
    mul_c_vanish (p := 0) (q := deg a + 1) vanish_below_zero
      (fun b _ => hinner b) (by omega)
  rw [houter, add_zero]

/-- ... and with the *right* slot carrying it. -/
theorem riccatiForm_eq_sameDegreeOp_right (Att : Fin d -> Fin d -> LongJet d)
    (u v : LongJet d) (a : Multiindex d) (s : Real) :
    riccatiForm Att u v a s = sameDegreeOp Att (zeroJet d) u v a s := by
  rw [riccatiForm, sameDegreeOp]
  refine Finset.sum_congr rfl fun i (_ : i ∈ (Finset.univ : Finset (Fin d))) => ?_
  refine Finset.sum_congr rfl fun j (_ : j ∈ (Finset.univ : Finset (Fin d))) => ?_
  have hz : ∀ (k : Fin d) e, (transverseDeriv k (zeroJet d)).c e s = 0 := by
    intro k e
    show ((e k + 1 : Nat) : Complex) * (0 : Complex) = 0
    ring
  have hinner : ∀ b,
      (mul (transverseDeriv i v) (transverseDeriv j (zeroJet d))).c b s = 0 :=
    fun b => mul_c_vanish (p := 0) (q := deg b + 1) vanish_below_zero
      (fun e _ => hz j e) (by omega)
  have houter : (mul (Att i j)
      (mul (transverseDeriv i v) (transverseDeriv j (zeroJet d)))).c a s = 0 :=
    mul_c_vanish (p := 0) (q := deg a + 1) vanish_below_zero
      (fun b _ => hinner b) (by omega)
  rw [houter, zero_add]

/-- The quadratic coefficients of the degree-`r` Riccati term, built from the
metric alone by evaluating the bilinear form on pairs of basis jets. -/
def riccatiTensor (Att : Fin d -> Fin d -> LongJet d) (r : Nat)
    (alpha beta gamma : DegreeIndex d r) (s : Real) : Complex :=
  riccatiForm Att (basisJet beta.1) (basisJet gamma.1) alpha.1 s

set_option maxHeartbeats 1000000 in
/-- **The Riccati term is the quadratic form of that tensor on the block.** -/
theorem quadraticSelfTerm_matrix (Att : Fin d -> Fin d -> LongJet d)
    (delta : LongJet d) (r : Nat) (s : Real)
    (hsupp : ∀ b, deg b ≠ r -> delta.c b s = 0) (alpha : DegreeIndex d r) :
    quadraticSelfTerm Att delta alpha.1 s
      = ∑ beta : DegreeIndex d r,
          (∑ gamma : DegreeIndex d r,
            riccatiTensor Att r alpha beta gamma s * delta.c gamma.1 s)
          * delta.c beta.1 s := by
  have hstep : ∀ beta : DegreeIndex d r,
      eikonalMatrix Att delta (zeroJet d) r s alpha beta
        = ∑ gamma : DegreeIndex d r,
            riccatiTensor Att r alpha beta gamma s * delta.c gamma.1 s := by
    intro beta
    have h1 : eikonalMatrix Att delta (zeroJet d) r s alpha beta
        = sameDegreeOp Att (zeroJet d) (basisJet beta.1) delta alpha.1 s :=
      (riccatiForm_eq_sameDegreeOp_left Att (basisJet beta.1) delta
        alpha.1 s).symm.trans
        (riccatiForm_eq_sameDegreeOp_right Att (basisJet beta.1) delta alpha.1 s)
    have h2 : ∀ gamma : DegreeIndex d r,
        eikonalMatrix Att (zeroJet d) (basisJet beta.1) r s alpha gamma
          = riccatiTensor Att r alpha beta gamma s := fun gamma =>
      (riccatiForm_eq_sameDegreeOp_right Att (basisJet beta.1)
        (basisJet gamma.1) alpha.1 s).symm
    rw [h1, sameDegreeOp_matrix Att (zeroJet d) (basisJet beta.1) delta r s
      hsupp alpha]
    exact Finset.sum_congr rfl fun gamma _ => by rw [h2 gamma]
  rw [quadraticSelfTerm_eq_riccatiForm, riccatiForm_eq_sameDegreeOp_left,
    sameDegreeOp_matrix Att delta (zeroJet d) delta r s hsupp alpha]
  exact Finset.sum_congr rfl fun beta _ => by rw [hstep beta]

/-- The quadratic coefficients are continuous in the longitudinal parameter,
automatically. -/
theorem continuous_riccatiTensor (Att : Fin d -> Fin d -> LongJet d) (r : Nat)
    (alpha beta gamma : DegreeIndex d r) :
    Continuous fun s => riccatiTensor Att r alpha beta gamma s := by
  have h : (fun s => riccatiTensor Att r alpha beta gamma s)
      = fun s => sameDegreeOp Att (zeroJet d) (basisJet beta.1)
          (basisJet gamma.1) alpha.1 s :=
    funext fun s => riccatiForm_eq_sameDegreeOp_right Att (basisJet beta.1)
      (basisJet gamma.1) alpha.1 s
  rw [h]
  exact continuous_sameDegreeOp Att (zeroJet d) (basisJet beta.1)
    (basisJet gamma.1) alpha.1

/-- Their certified longitudinal derivative. -/
def riccatiTensorDeriv (Att : Fin d -> Fin d -> LongJet d) (r : Nat)
    (alpha beta gamma : DegreeIndex d r) (s : Real) : Complex :=
  sameDegreeOpDeriv Att (zeroJet d) (basisJet beta.1) (basisJet gamma.1)
    alpha.1 s

theorem hasDerivAt_riccatiTensor (Att : Fin d -> Fin d -> LongJet d) (r : Nat)
    (alpha beta gamma : DegreeIndex d r) (s : Real) :
    HasDerivAt (fun v => riccatiTensor Att r alpha beta gamma v)
      (riccatiTensorDeriv Att r alpha beta gamma s) s := by
  have h : (fun v => riccatiTensor Att r alpha beta gamma v)
      = fun v => sameDegreeOp Att (zeroJet d) (basisJet beta.1)
          (basisJet gamma.1) alpha.1 v :=
    funext fun v => riccatiForm_eq_sameDegreeOp_right Att (basisJet beta.1)
      (basisJet gamma.1) alpha.1 v
  rw [h]
  exact hasDerivAt_sameDegreeOp Att (zeroJet d) (basisJet beta.1)
    (basisJet gamma.1) alpha.1 s

/-- **The degree-two cancellation in block form.**  This is the shape the
Riccati ODE actually produces: matrix, source and quadratic tensor all built
from the metric and the base phase, with the unknown appearing only as the
degree-two block. -/
theorem eikonal_deg_two_eq_zero_of_blockRiccatiEquation {G : FermiMetricJet d}
    (P base : SourcePhaseJet G) (s : Real) (alpha : DegreeIndex d 2)
    (hlow : ∀ b, deg b < 2 -> P.phi.c b s = base.phi.c b s)
    (hdlow : ∀ b, deg b < 2 -> P.dphi.c b s = base.dphi.c b s)
    (hoff : ∀ b, 2 < deg b -> P.phi.c b s = base.phi.c b s)
    (hric : 2 * (P.dphi.c alpha.1 s - base.dphi.c alpha.1 s)
        + ∑ beta : DegreeIndex d 2, phaseEikonalMatrix base 2 s alpha beta
            * (P.phi.c beta.1 s - base.phi.c beta.1 s)
        + ∑ beta : DegreeIndex d 2,
            (∑ gamma : DegreeIndex d 2,
              riccatiTensor G.Att 2 alpha beta gamma s
                * (P.phi.c gamma.1 s - base.phi.c gamma.1 s))
            * (P.phi.c beta.1 s - base.phi.c beta.1 s)
      = phaseSource base 2 s alpha) :
    jetEikonal G.Ass G.Bs G.Att P.phi P.dphi alpha.1 s = 0 := by
  have hsupp : ∀ b, deg b ≠ 2 -> (sub P.phi base.phi).c b s = 0 := by
    intro b hb
    show P.phi.c b s - base.phi.c b s = 0
    rcases Nat.lt_or_ge (deg b) 2 with h | h
    · rw [hlow b h, sub_self]
    · rw [hoff b (by omega), sub_self]
  refine eikonal_deg_two_eq_zero_of_riccatiEquation P base s alpha hlow hdlow
    hoff ?_
  rw [quadraticSelfTerm_matrix G.Att (sub P.phi base.phi) 2 s hsupp alpha]
  exact hric

end LiuWang2025SemilinearWaveSameDegreeMatrix
