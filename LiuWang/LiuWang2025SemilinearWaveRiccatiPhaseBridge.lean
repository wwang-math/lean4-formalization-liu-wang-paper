import LiuWang.LiuWang2025SemilinearWavePhaseUpdate
import LiuWang.LiuWang2025SemilinearWaveRiccatiExistence

/-!
# Liu-Wang semilinear wave: the Riccati / transverse-jet phase bridge

The transverse-jet phase recursion needs, at degree two, a matrix path solving
the source's equation (3.8).  The repository already generates such a path, with
symmetry, positive imaginary part and no caustics, from
`LiuWang2025SemilinearWaveRiccatiExistence.Coefficients`.  This file connects the
two.

The connection is entirely a normalization statement, and the normalizations are
proved rather than stipulated.  `LongJet` uses *ordinary monomial* coefficients,
so for a quadratic phase `z^T M z`:

* `quadCoeff M` is exactly that polynomial's coefficient family
  (`quadCoeff_diag`: `z_p^2` gets `M_{pp}`; `quadCoeff_offDiag`: `z_p z_q` gets
  `M_{pq} + M_{qp}`);
* its transverse gradient has degree-one coefficients `2 M_{ki}`, uniformly in
  the diagonal and off-diagonal cases -- the diagonal picks up a factor two from
  the derivative and one from `quadCoeff`, the off-diagonal one from the
  derivative and two from `quadCoeff` (using symmetry of `M`);
* consequently the quadratic self-interaction is `quadCoeff (4 M C0 M)` with
  `C0` the degree-zero transverse metric block, and the source's `C = 2 C0`;
* and the degree-two coefficient family of `A^{i1 i1}` is `quadCoeff (2 D)`,
  i.e. `D_{pq} = (1/4) d_p d_q g^{11}`, which is the source's `D`.

With those factors the degree-two eikonal equation is *literally* `H' + HCH + D
= 0`.
-/

noncomputable section

open scoped BigOperators
open scoped Matrix.Norms.L2Operator
open Set

namespace LiuWang2025SemilinearWaveRiccatiPhaseBridge

open LiuWang2025SemilinearWaveTransverseJet
open LiuWang2025SemilinearWaveLongitudinalJet
open LiuWang2025SemilinearWaveLongitudinalJet.LongJet
open LiuWang2025SemilinearWaveJetOperators
open LiuWang2025SemilinearWaveDegreeBlock
open LiuWang2025SemilinearWaveMetricJetPhaseHierarchy
open LiuWang2025SemilinearWaveSameDegreeMatrix
open LiuWang2025SemilinearWavePhaseUpdate
open LiuWang2025SemilinearWaveDegreeBlockODE
open LiuWang2025SemilinearWaveRiccatiExistence
open LiuWang2025SemilinearWaveRiccatiPhase
open LiuWang2025SemilinearWaveRiccatiFlow
open Matrix

variable {d : Nat}

/-! ## Convolution of basis jets -/

theorem single_inj {k l : Fin d}
    (h : (Pi.single k 1 : Multiindex d) = Pi.single l 1) : k = l := by
  by_contra hne
  have h1 := congrFun h k
  rw [Pi.single_eq_same, Pi.single_eq_of_ne hne] at h1
  exact one_ne_zero h1

theorem mul_basisJet_basisJet (u v a : Multiindex d) (s : Real) :
    (mul (basisJet u) (basisJet v)).c a s = if a = u + v then 1 else 0 := by
  classical
  by_cases h : a = u + v
  · subst h
    rw [if_pos rfl, mul_c,
      Finset.sum_eq_single_of_mem u (mem_below.2 fun i => by
        show u i ≤ u i + v i
        omega)]
    · rw [basisJet_c, if_pos rfl, basisJet_c, if_pos, one_mul]
      funext i
      show u i + v i - u i = v i
      omega
    · intro b _ hb
      rw [basisJet_c, if_neg hb, zero_mul]
  · rw [if_neg h, mul_c]
    refine Finset.sum_eq_zero fun b hb => ?_
    by_cases hbu : b = u
    · subst hbu
      rw [basisJet_c, if_pos rfl, one_mul, basisJet_c, if_neg]
      intro hcon
      refine h (funext fun i => ?_)
      have h1 := mem_below.1 hb i
      have h2 : a i - b i = v i := congrFun hcon i
      show a i = b i + v i
      omega
    · rw [basisJet_c, if_neg hbu, zero_mul]

/-! ## Degree-one jets -/

/-- The jet of a linear form `sum_k A_k z_k`. -/
def linJet (A : Fin d -> Complex) : LongJet d :=
  sumJet fun k => smul (A k) (basisJet (Pi.single k 1))

@[simp] theorem linJet_c (A : Fin d -> Complex) (b : Multiindex d) (s : Real) :
    (linJet A).c b s
      = ∑ k, A k * (if b = (Pi.single k 1 : Multiindex d) then 1 else 0) := rfl

theorem linJet_c_single (A : Fin d -> Complex) (k : Fin d) (s : Real) :
    (linJet A).c (Pi.single k 1) s = A k := by
  classical
  rw [linJet_c, Finset.sum_eq_single_of_mem k (Finset.mem_univ k)]
  · rw [if_pos rfl, mul_one]
  · intro l _ hl
    rw [if_neg (fun hcon => hl (single_inj hcon).symm), mul_zero]

theorem linJet_c_of_deg_ne_one (A : Fin d -> Complex) {b : Multiindex d}
    (hb : deg b ≠ 1) (s : Real) : (linJet A).c b s = 0 := by
  rw [linJet_c]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [if_neg (fun hcon => hb (by rw [hcon, deg_single])), mul_zero]

/-- Convolution of two linear-form jets, in closed form. -/
theorem mul_linJet_c (A B : Fin d -> Complex) (a : Multiindex d) (s : Real) :
    (mul (linJet A) (linJet B)).c a s
      = ∑ k, ∑ l, A k * B l
          * (if a = (Pi.single k 1 : Multiindex d) + Pi.single l 1 then 1 else 0) := by
  rw [linJet, linJet, mul_c_sum_left]
  refine Finset.sum_congr rfl fun k (_ : k ∈ Finset.univ) => ?_
  rw [mul_c_smul_left, mul_c_sum_right, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l (_ : l ∈ Finset.univ) => ?_
  rw [mul_c_smul_right, mul_basisJet_basisJet]
  ring

theorem linJet_vanish_below_one (A : Fin d -> Complex) (s : Real) :
    ∀ b, deg b < 1 -> (linJet A).c b s = 0 :=
  fun b hb => linJet_c_of_deg_ne_one A (by omega) s

theorem mul_linJet_vanish_below_two (A B : Fin d -> Complex) (s : Real) :
    ∀ b, deg b < 2 -> (mul (linJet A) (linJet B)).c b s = 0 :=
  fun b hb => mul_c_vanish (linJet_vanish_below_one A s)
    (linJet_vanish_below_one B s) (by omega)

/-! ## The exact normalization of the quadratic phase -/

/-- **The degree-one normalization of the transverse gradient of `z^T M z`.**
Both the diagonal and the off-diagonal case give `2 M_{k i}`: on the diagonal
the derivative contributes a factor two and `quadCoeff` a factor one, off the
diagonal the derivative contributes one and `quadCoeff` two.  Nothing is hidden
in a definition. -/
theorem transverseDeriv_quadJet_single
    (M M' : Real -> Fin d -> Fin d -> Complex)
    (hM : ∀ p q s, HasDerivAt (fun t => M t p q) (M' s p q) s)
    {s : Real} (hsymm : ∀ p q, M s p q = M s q p) (i k : Fin d) :
    (transverseDeriv i (quadJet M M' hM)).c (Pi.single k 1) s = 2 * M s k i := by
  show (((Pi.single k 1 : Multiindex d) i + 1 : Nat) : Complex)
      * (quadJet M M' hM).c ((Pi.single k 1 : Multiindex d) + Pi.single i 1) s
    = 2 * M s k i
  rw [quadJet_c, if_pos (by rw [deg_add_single, deg_single])]
  by_cases hki : k = i
  · subst hki
    rw [quadCoeff_diag, Pi.single_eq_same]
    norm_num
  · rw [quadCoeff_offDiag _ hki, Pi.single_eq_of_ne (Ne.symm hki), hsymm i k]
    push_cast
    ring

/-- The transverse gradient of the quadratic phase is the jet of a linear form.
-/
theorem transverseDeriv_quadJet_c
    (M M' : Real -> Fin d -> Fin d -> Complex)
    (hM : ∀ p q s, HasDerivAt (fun t => M t p q) (M' s p q) s)
    {s : Real} (hsymm : ∀ p q, M s p q = M s q p) (i : Fin d)
    (b : Multiindex d) :
    (transverseDeriv i (quadJet M M' hM)).c b s
      = (linJet (fun k => 2 * M s k i)).c b s := by
  by_cases hb : deg b = 1
  · obtain ⟨k, hk⟩ := eq_single_of_deg_eq_one hb
    rw [hk, transverseDeriv_quadJet_single M M' hM hsymm i k, linJet_c_single]
  · rw [linJet_c_of_deg_ne_one _ hb]
    show (((b i + 1 : Nat)) : Complex)
      * (quadJet M M' hM).c (b + Pi.single i 1) s = 0
    rw [quadJet_c, if_neg (by rw [deg_add_single]; omega), mul_zero]

theorem sum_comm_four (F : Fin d -> Fin d -> Fin d -> Fin d -> Complex) :
    ∑ i, ∑ j, ∑ k, ∑ l, F i j k l = ∑ k, ∑ l, ∑ i, ∑ j, F i j k l := by
  calc ∑ i, ∑ j, ∑ k, ∑ l, F i j k l
      = ∑ i, ∑ k, ∑ j, ∑ l, F i j k l :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ k, ∑ i, ∑ j, ∑ l, F i j k l := Finset.sum_comm
    _ = ∑ k, ∑ i, ∑ l, ∑ j, F i j k l :=
        Finset.sum_congr rfl fun k _ =>
          Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ k, ∑ l, ∑ i, ∑ j, F i j k l :=
        Finset.sum_congr rfl fun k _ => Finset.sum_comm

/-- **The Riccati quadratic term, in closed matrix form.**  With `C0` the
degree-zero transverse metric block, the quadratic self-interaction of
`z^T M z` is the quadratic phase of `4 M C0 M^T`. -/
theorem quadraticSelfTerm_quadJet (G : FermiMetricJet d)
    (M M' : Real -> Fin d -> Fin d -> Complex)
    (hM : ∀ p q s, HasDerivAt (fun t => M t p q) (M' s p q) s)
    {s : Real} (hsymm : ∀ p q, M s p q = M s q p)
    {a : Multiindex d} (ha : deg a = 2) :
    quadraticSelfTerm G.Att (quadJet M M' hM) a s
      = quadCoeff
          (fun k l => 4 * ∑ i, ∑ j, M s k i * (G.Att i j).c 0 s * M s l j) a := by
  classical
  have hgrad : ∀ (i : Fin d) b,
      (transverseDeriv i (quadJet M M' hM)).c b s
        = (linJet (fun k => 2 * M s k i)).c b s :=
    fun i b => transverseDeriv_quadJet_c M M' hM hsymm i b
  have hterm : ∀ i j : Fin d,
      (mul (G.Att i j)
        (mul (transverseDeriv i (quadJet M M' hM))
          (transverseDeriv j (quadJet M M' hM)))).c a s
      = ∑ k, ∑ l, ((G.Att i j).c 0 s * (4 * (M s k i * M s l j)))
          * (if a = (Pi.single k 1 : Multiindex d) + Pi.single l 1 then 1 else 0) := by
    intro i j
    have hinner : ∀ b, deg b ≤ deg a ->
        (mul (transverseDeriv i (quadJet M M' hM))
          (transverseDeriv j (quadJet M M' hM))).c b s
        = (mul (linJet (fun k => 2 * M s k i))
            (linJet (fun l => 2 * M s l j))).c b s :=
      fun b _ => mul_c_congr (fun e _ => hgrad i e) (fun e _ => hgrad j e)
    rw [mul_c_congr (fun _ _ => rfl) hinner,
      mul_c_bot (by
        intro b hb
        exact mul_linJet_vanish_below_two _ _ s b (by omega)),
      mul_linJet_c, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k (_ : k ∈ Finset.univ) => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l (_ : l ∈ Finset.univ) => ?_
    ring
  rw [quadraticSelfTerm]
  rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) =>
    Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) => hterm i j]
  refine (sum_comm_four (fun i j k l =>
    ((G.Att i j).c 0 s * (4 * (M s k i * M s l j)))
      * (if a = (Pi.single k 1 : Multiindex d) + Pi.single l 1 then 1 else 0))).trans ?_
  rw [quadCoeff]
  refine Finset.sum_congr rfl fun k (_ : k ∈ Finset.univ) => ?_
  refine Finset.sum_congr rfl fun l (_ : l ∈ Finset.univ) => ?_
  by_cases hkl : (Pi.single k 1 + Pi.single l 1 : Multiindex d) = a
  · rw [if_pos hkl]
    have hrev : a = (Pi.single k 1 : Multiindex d) + Pi.single l 1 := hkl.symm
    rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) =>
      Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) => by
        rw [if_pos hrev]]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  · rw [if_neg hkl]
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
    rw [if_neg (fun hcon => hkl hcon.symm), mul_zero]

/-! ## Linearity of the quadratic coefficient family -/

theorem quadCoeff_sum_eq_zero (A B E : Fin d -> Fin d -> Complex)
    (h : ∀ p q, A p q + B p q + E p q = 0) (a : Multiindex d) :
    quadCoeff A a + quadCoeff B a + quadCoeff E a = 0 := by
  classical
  rw [quadCoeff, quadCoeff, quadCoeff, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun p _ => ?_
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun q _ => ?_
  by_cases hpq : (Pi.single p 1 + Pi.single q 1 : Multiindex d) = a
  · rw [if_pos hpq, if_pos hpq, if_pos hpq]
    exact h p q
  · rw [if_neg hpq, if_neg hpq, if_neg hpq]
    ring

/-! ## Paper-specific compatibility data

This records coordinate normalizations of the metric jet and the identification
of the source's matrices `C` and `D` with metric coefficients.  It contains no
Riccati equation, no degree-two cancellation, and no statement about
`jetEikonal`.
-/

/-- Compatibility of a Fermi metric jet with the coefficient matrices of the
source's equation (3.8). -/
structure FermiCompat (G : FermiMetricJet d)
    (C D : Real -> Fin d -> Fin d -> Complex) : Prop where
  /-- In Fermi coordinates the first transverse derivatives of the metric vanish
  on the central curve. -/
  firstOrderVanishing : ∀ (i j k : Fin d) (s : Real),
    (G.Att i j).c (Pi.single k 1) s = 0
  /-- `C = 2 g^{transverse}(s, 0)`. -/
  matchC : ∀ (p q : Fin d) (s : Real), C s p q = 2 * (G.Att p q).c 0 s
  /-- `2 D` is the degree-two coefficient family of `A^{i1 i1}`; equivalently
  `D_{pq} = (1/4) d_p d_q g^{11}`, the source's `D`. -/
  matchD : ∀ (a : Multiindex d) (s : Real), deg a = 2 ->
    (G.Att G.i1 G.i1).c a s = 2 * quadCoeff (D s) a

theorem FermiCompat.att_deg_one {G : FermiMetricJet d}
    {C D : Real -> Fin d -> Fin d -> Complex} (h : FermiCompat G C D)
    (i j : Fin d) {b : Multiindex d} (hb : deg b = 1) (s : Real) :
    (G.Att i j).c b s = 0 := by
  obtain ⟨k, hk⟩ := eq_single_of_deg_eq_one hb
  rw [hk]
  exact h.firstOrderVanishing i j k s

/-- The base phase carries only the source's prescribed degrees zero and one:
its degree-two block is the unknown to be constructed. -/
def QuadFree {G : FermiMetricJet d} (base : SourcePhaseJet G) : Prop :=
  ∀ (b : Multiindex d) (s : Real), deg b = 2 -> base.phi.c b s = 0

theorem QuadFree.dphi {G : FermiMetricJet d} {base : SourcePhaseJet G}
    (h : QuadFree base) (b : Multiindex d) (hb : deg b = 2) (s : Real) :
    base.dphi.c b s = 0 := by
  have hconst : base.phi.c b = fun _ : Real => (0 : Complex) :=
    funext fun t => h b t hb
  have h1 : HasDerivAt (base.phi.c b) (base.dphi.c b s) s := base.dphi_is_deriv b s
  rw [hconst] at h1
  exact h1.unique (hasDerivAt_const s (0 : Complex))

/-! ## Vanishing of the degree-two linear operator -/

theorem deg_zero_index : deg (0 : Multiindex d) = 0 := by
  show ∑ i, (0 : Multiindex d) i = 0
  simp

theorem deriv_basisJet_vanish {beta : Multiindex d} (hbeta : deg beta = 2)
    (i : Fin d) {e : Multiindex d} (he : deg e ≠ 1) (s : Real) :
    (transverseDeriv i (basisJet beta)).c e s = 0 := by
  show ((e i + 1 : Nat) : Complex)
    * (basisJet beta).c (e + Pi.single i 1) s = 0
  rw [basisJet_c, if_neg, mul_zero]
  intro hcon
  refine he ?_
  have hd : deg (e + (Pi.single i 1 : Multiindex d)) = 2 := by
    rw [hcon]; exact hbeta
  rw [deg_add_single] at hd
  omega

theorem deriv_base_deg_one_vanish {G : FermiMetricJet d}
    {base : SourcePhaseJet G} (hq : QuadFree base) (j : Fin d)
    {e : Multiindex d} (he : deg e = 1) (s : Real) :
    (transverseDeriv j base.phi).c e s = 0 := by
  show ((e j + 1 : Nat) : Complex)
    * base.phi.c (e + Pi.single j 1) s = 0
  rw [hq _ s (by rw [deg_add_single, he]), mul_zero]

theorem mul_c_eq_zero_deg_two {u v : LongJet d} {a : Multiindex d} {s : Real}
    (ha : deg a = 2) (h0 : v.c a s = 0) (h1 : ∀ b, deg b = 1 -> u.c b s = 0)
    (h2 : v.c 0 s = 0) : (mul u v).c a s = 0 := by
  rw [mul_c]
  refine Finset.sum_eq_zero fun b hb => ?_
  have hd := deg_add_deg_sub hb
  rcases Nat.lt_or_ge (deg b) 1 with hlt | hge
  · have hb0 : b = 0 := eq_zero_of_deg_eq_zero (by omega)
    rw [hb0, show a - (0 : Multiindex d) = a from by
      funext i
      show a i - 0 = a i
      omega, h0, mul_zero]
  · rcases Nat.lt_or_ge (deg b) 2 with hlt2 | hge2
    · rw [h1 b (by omega), zero_mul]
    · rw [eq_zero_of_deg_eq_zero (a := a - b) (by omega), h2, mul_zero]

/-- **The degree-two linear operator vanishes in Fermi coordinates.**  Its
entries pair a degree-one metric coefficient against a degree-one gradient, and
the Fermi normalization kills the former.  This is why degree two is a pure
Riccati equation with no linear term, exactly as in the source. -/
theorem phaseEikonalMatrix_base_eq_zero {G : FermiMetricJet d}
    {C D : Real -> Fin d -> Fin d -> Complex} (hcompat : FermiCompat G C D)
    {base : SourcePhaseJet G} (hq : QuadFree base) (s : Real)
    (alpha beta : DegreeIndex d 2) :
    phaseEikonalMatrix base 2 s alpha beta = 0 := by
  have hdegA : deg alpha.1 = 2 := mem_degreeEq.1 alpha.2
  have hdegB : deg beta.1 = 2 := mem_degreeEq.1 beta.2
  refine Finset.sum_eq_zero fun i (_ : i ∈ (Finset.univ : Finset (Fin d))) => ?_
  refine Finset.sum_eq_zero fun j (_ : j ∈ (Finset.univ : Finset (Fin d))) => ?_
  have hL : (mul (G.Att i j) (mul (transverseDeriv i (basisJet beta.1))
      (transverseDeriv j base.phi))).c alpha.1 s = 0 := by
    refine mul_c_eq_zero_deg_two hdegA ?_
      (fun b hb => hcompat.att_deg_one i j hb s) ?_
    · rw [mul_c]
      refine Finset.sum_eq_zero fun e he => ?_
      have hd := deg_add_deg_sub he
      by_cases h1e : deg e = 1
      · rw [deriv_base_deg_one_vanish hq j (by omega) s, mul_zero]
      · rw [deriv_basisJet_vanish hdegB i h1e s, zero_mul]
    · rw [mul_c]
      refine Finset.sum_eq_zero fun e he => ?_
      have hd := deg_add_deg_sub he
      rw [deriv_basisJet_vanish hdegB i (by rw [deg_zero_index] at hd; omega) s,
        zero_mul]
  have hR : (mul (G.Att i j) (mul (transverseDeriv i base.phi)
      (transverseDeriv j (basisJet beta.1)))).c alpha.1 s = 0 := by
    refine mul_c_eq_zero_deg_two hdegA ?_
      (fun b hb => hcompat.att_deg_one i j hb s) ?_
    · rw [mul_c]
      refine Finset.sum_eq_zero fun e he => ?_
      have hd := deg_add_deg_sub he
      by_cases h1e : deg (alpha.1 - e) = 1
      · rw [deriv_base_deg_one_vanish hq i (by omega) s, zero_mul]
      · rw [deriv_basisJet_vanish hdegB j h1e s, mul_zero]
    · rw [mul_c]
      refine Finset.sum_eq_zero fun e he => ?_
      have hd := deg_add_deg_sub he
      rw [deriv_basisJet_vanish hdegB j
        (by rw [deg_zero_index] at hd; omega) s, mul_zero]
  rw [hL, hR, add_zero]

/-! ## The degree-two eikonal of the base phase -/

theorem mul_c_deg_two_split {u v : LongJet d} {a : Multiindex d} {s : Real}
    (ha : deg a = 2) (h1 : ∀ b, deg b = 1 -> u.c b s = 0) :
    (mul u v).c a s = u.c 0 s * v.c a s + u.c a s * v.c 0 s := by
  classical
  have hane : (0 : Multiindex d) ≠ a := by
    intro h
    rw [← h, deg_zero_index] at ha
    omega
  have hsub0 : a - (0 : Multiindex d) = a := by
    funext i
    show a i - 0 = a i
    omega
  have hsuba : a - a = (0 : Multiindex d) := by
    funext i
    show a i - a i = 0
    omega
  rw [mul_c, Finset.sum_eq_add_of_mem (0 : Multiindex d) a
    (mem_below.2 fun _ => Nat.zero_le _) (self_mem_below a) hane ?_]
  · rw [hsub0, hsuba]
  · intro b hb hne
    have hd := deg_add_deg_sub hb
    rcases Nat.lt_or_ge (deg b) 1 with hlt | hge
    · exact absurd (eq_zero_of_deg_eq_zero (a := b) (by omega)) hne.1
    · rcases Nat.lt_or_ge (deg b) 2 with hlt2 | hge2
      · rw [h1 b (by omega), zero_mul]
      · have hz : a - b = 0 := eq_zero_of_deg_eq_zero (by omega)
        have hba : b = a := by
          funext i
          have h1i := mem_below.1 hb i
          have h2i : a i - b i = 0 := congrFun hz i
          omega
        exact absurd hba hne.2

/-- **The degree-two eikonal of the base phase is the source's `D` term.**  Every
other contribution is killed: the longitudinal derivative vanishes through
degree two, the Fermi first-order normalization kills the mixed terms, and the
null row and column kill the remaining degree-zero pairings. -/
theorem jetEikonal_base_deg_two {G : FermiMetricJet d}
    {C D : Real -> Fin d -> Fin d -> Complex} (hcompat : FermiCompat G C D)
    {base : SourcePhaseJet G} (hq : QuadFree base) (s : Real)
    {a : Multiindex d} (ha : deg a = 2) :
    jetEikonal G.Ass G.Bs G.Att base.phi base.dphi a s
      = (G.Att G.i1 G.i1).c a s := by
  classical
  have hdphi : ∀ b, deg b < 3 -> base.dphi.c b s = 0 := by
    intro b hb
    rcases Nat.lt_or_ge (deg b) 1 with h0 | h1
    · rw [eq_zero_of_deg_eq_zero (a := b) (by omega)]
      exact base.dphi_zero s
    · rcases Nat.lt_or_ge (deg b) 2 with h1' | h2
      · obtain ⟨k, hk⟩ := eq_single_of_deg_eq_one (by omega : deg b = 1)
        rw [hk]
        exact base.dphi_one k s
      · exact hq.dphi b (by omega) s
  have hgradVanish : ∀ (i : Fin d) b, deg b = 1 ->
      (transverseDeriv i base.phi).c b s = 0 :=
    fun i b hb => deriv_base_deg_one_vanish hq i hb s
  have hgrad0 : ∀ i : Fin d, (transverseDeriv i base.phi).c 0 s
      = if i = G.i1 then 1 else 0 := by
    intro i
    show ((((0 : Multiindex d) i) + 1 : Nat) : Complex)
      * base.phi.c ((0 : Multiindex d) + Pi.single i 1) s = _
    rw [show (0 : Multiindex d) + Pi.single i 1 = (Pi.single i 1 : Multiindex d) from
      by funext k; show 0 + _ = _; omega, base.phi_one i s]
    show ((0 + 1 : Nat) : Complex) * _ = _
    push_cast
    ring
  -- the first two blocks vanish outright
  have hT1 : (mul G.Ass (mul base.dphi base.dphi)).c a s = 0 :=
    mul_c_vanish (p := 0) (q := 6) vanish_below_zero
      (fun b hb => mul_c_vanish (p := 3) (q := 3) hdphi hdphi (by omega))
      (by omega)
  have hT2 : ∀ i : Fin d,
      (mul (G.Bs i) (mul base.dphi (transverseDeriv i base.phi))).c a s = 0 :=
    fun i => mul_c_vanish (p := 0) (q := 3) vanish_below_zero
      (fun b hb => mul_c_vanish (p := 3) (q := 0) hdphi vanish_below_zero
        (by omega)) (by omega)
  -- the transverse block
  have hinner : ∀ i j : Fin d,
      (mul (transverseDeriv i base.phi) (transverseDeriv j base.phi)).c a s
        = (if i = G.i1 then 1 else 0) * (transverseDeriv j base.phi).c a s
          + (transverseDeriv i base.phi).c a s * (if j = G.i1 then 1 else 0) := by
    intro i j
    rw [mul_c_deg_two_split ha (hgradVanish i), hgrad0 i, hgrad0 j]
  have hterm : ∀ i j : Fin d,
      (mul (G.Att i j) (mul (transverseDeriv i base.phi)
        (transverseDeriv j base.phi))).c a s
      = (G.Att i j).c 0 s * ((if i = G.i1 then 1 else 0)
            * (transverseDeriv j base.phi).c a s
          + (transverseDeriv i base.phi).c a s * (if j = G.i1 then 1 else 0))
        + (G.Att i j).c a s * ((if i = G.i1 then 1 else 0)
            * (if j = G.i1 then 1 else 0)) := by
    intro i j
    rw [mul_c_deg_two_split ha (fun b hb => hcompat.att_deg_one i j hb s),
      hinner i j, mul_c_zero, hgrad0 i, hgrad0 j]
  have hT3 : ∑ i, ∑ j, (mul (G.Att i j) (mul (transverseDeriv i base.phi)
      (transverseDeriv j base.phi))).c a s = (G.Att G.i1 G.i1).c a s := by
    rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) =>
      Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) => hterm i j]
    rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) =>
      Finset.sum_add_distrib]
    rw [Finset.sum_add_distrib]
    have hA : ∑ i, ∑ j, (G.Att i j).c 0 s * ((if i = G.i1 then 1 else 0)
        * (transverseDeriv j base.phi).c a s
      + (transverseDeriv i base.phi).c a s * (if j = G.i1 then 1 else 0)) = 0 := by
      refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
      by_cases hi : i = G.i1
      · rw [hi, G.nullRow j s]
        ring
      · by_cases hj : j = G.i1
        · rw [hj, G.nullCol i s]
          ring
        · rw [if_neg hi, if_neg hj]
          ring
    have hB : ∑ i, ∑ j, (G.Att i j).c a s * ((if i = G.i1 then 1 else 0)
        * (if j = G.i1 then 1 else 0)) = (G.Att G.i1 G.i1).c a s := by
      rw [Finset.sum_eq_single_of_mem G.i1 (Finset.mem_univ _)]
      · rw [Finset.sum_eq_single_of_mem G.i1 (Finset.mem_univ _)]
        · rw [if_pos rfl]
          ring
        · intro j _ hj
          rw [if_neg hj]
          ring
      · intro i _ hi
        refine Finset.sum_eq_zero fun j _ => ?_
        rw [if_neg hi]
        ring
    rw [hA, hB, zero_add]
  rw [jetEikonal, hT1, Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hT2 i,
    Finset.sum_const_zero, hT3]
  ring

theorem quadCoeff_smul (k : Complex) (N : Fin d -> Fin d -> Complex)
    (a : Multiindex d) :
    quadCoeff (fun p q => k * N p q) a = k * quadCoeff N a := by
  classical
  rw [quadCoeff, quadCoeff, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  by_cases h : (Pi.single p 1 + Pi.single q 1 : Multiindex d) = a
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h, mul_zero]

/-! ## The degree-two bridge -/

/-- **The exact degree-two identity consumed by the phase recursion, derived.**
Its three ingredients are: the Fermi normalization (which removes the linear
block operator), the closed matrix form of the quadratic self-interaction, and
the source's matrix Riccati equation.  Nothing here is taken as input. -/
theorem hric_of_riccati {G : FermiMetricJet d}
    {C D : Real -> Fin d -> Fin d -> Complex} (hcompat : FermiCompat G C D)
    {base : SourcePhaseJet G} (hq : QuadFree base)
    (M M' : Real -> Fin d -> Fin d -> Complex)
    (hM : ∀ p q s, HasDerivAt (fun t => M t p q) (M' s p q) s)
    {s : Real} (hsymm : ∀ p q, M s p q = M s q p)
    (heq : ∀ p q, M' s p q
        + (∑ i, ∑ j, M s p i * C s i j * M s j q) + D s p q = 0)
    (alpha : DegreeIndex d 2) :
    2 * quadCoeff (M' s) alpha.1
        + ∑ beta : DegreeIndex d 2,
            phaseEikonalMatrix base 2 s alpha beta * quadCoeff (M s) beta.1
        + quadraticSelfTerm G.Att (quadJet M M' hM) alpha.1 s
      = phaseSource base 2 s alpha := by
  classical
  have hdeg : deg alpha.1 = 2 := mem_degreeEq.1 alpha.2
  have hmat : ∀ beta : DegreeIndex d 2,
      phaseEikonalMatrix base 2 s alpha beta * quadCoeff (M s) beta.1 = 0 := by
    intro beta
    rw [phaseEikonalMatrix_base_eq_zero hcompat hq s alpha beta, zero_mul]
  -- the quadratic coefficients of the self-interaction are twice `M C M`
  have hR : ∀ k l : Fin d,
      4 * ∑ i, ∑ j, M s k i * (G.Att i j).c 0 s * M s l j
        = 2 * ∑ i, ∑ j, M s k i * C s i j * M s j l := by
    intro k l
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hcompat.matchC i j s, hsymm j l]
    ring
  -- the three quadratic families sum to zero
  have hzero : quadCoeff (fun p q => 2 * M' s p q) alpha.1
      + quadCoeff (fun p q => 2 * ∑ i, ∑ j, M s p i * C s i j * M s j q) alpha.1
      + quadCoeff (fun p q => 2 * D s p q) alpha.1 = 0 := by
    refine quadCoeff_sum_eq_zero _ _ _ (fun p q => ?_) alpha.1
    have h := heq p q
    linear_combination 2 * h
  rw [Finset.sum_congr rfl fun beta (_ : beta ∈ Finset.univ) => hmat beta,
    Finset.sum_const_zero, add_zero,
    quadraticSelfTerm_quadJet G M M' hM hsymm hdeg]
  rw [show (fun k l => 4 * ∑ i, ∑ j, M s k i * (G.Att i j).c 0 s * M s l j)
      = (fun k l => 2 * ∑ i, ∑ j, M s k i * C s i j * M s j l) from
    funext fun k => funext fun l => hR k l]
  rw [quadCoeff_smul]
  rw [phaseSource, jetEikonal_base_deg_two hcompat hq s hdeg,
    hcompat.matchD alpha.1 s hdeg]
  rw [quadCoeff_smul, quadCoeff_smul, quadCoeff_smul] at hzero
  linear_combination hzero

/-! ## Global `C^2` extension of an interval-certified path

The generated Riccati flow is certified on the paper interval, while `LongJet`
demands derivative certificates at every real parameter.  The mismatch is closed
by the same construction that promotes the higher-degree block solutions: the
second derivative is frozen outside the interval, and the path and its first
derivative are its iterated primitives.  The mean value inequality identifies
the extension with the original on the interval.
-/

theorem exists_c2_extension {lo hi : Real} {t0 : Real} (ht0 : t0 ∈ Icc lo hi)
    (f f' f'' : Real -> Complex)
    (hf : ∀ t ∈ Icc lo hi, HasDerivWithinAt f (f' t) (Icc lo hi) t)
    (hf' : ∀ t ∈ Icc lo hi, HasDerivWithinAt f' (f'' t) (Icc lo hi) t)
    (hcont : ContinuousOn f'' (Icc lo hi)) :
    ∃ g g' g'' : Real -> Complex,
      (∀ t, HasDerivAt g (g' t) t) ∧ (∀ t, HasDerivAt g' (g'' t) t) ∧
      Continuous g'' ∧
      (∀ t ∈ Icc lo hi, g t = f t) ∧ (∀ t ∈ Icc lo hi, g' t = f' t) := by
  have hlohi : lo ≤ hi := le_trans ht0.1 ht0.2
  obtain ⟨G2, hG2def⟩ : ∃ G2 : Real -> Complex,
      G2 = fun t => f'' (clamp lo hi t) := ⟨_, rfl⟩
  have hG2cont : Continuous G2 := by
    rw [hG2def]
    exact hcont.comp_continuous (continuous_clamp lo hi) (clamp_mem hlohi)
  obtain ⟨V, hVdef⟩ : ∃ V : Real -> Complex,
      V = fun t => f' t0 + ∫ v in t0..t, G2 v := ⟨_, rfl⟩
  have hVderiv : ∀ t : Real, HasDerivAt V (G2 t) t := by
    intro t
    rw [hVdef]
    exact (intervalIntegral.integral_hasDerivAt_right
      (hG2cont.intervalIntegrable _ _)
      hG2cont.stronglyMeasurable.stronglyMeasurableAtFilter
      hG2cont.continuousAt).const_add _
  have hVcont : Continuous V :=
    continuous_iff_continuousAt.2 fun t => (hVderiv t).continuousAt
  obtain ⟨U, hUdef⟩ : ∃ U : Real -> Complex,
      U = fun t => f t0 + ∫ v in t0..t, V v := ⟨_, rfl⟩
  have hUderiv : ∀ t : Real, HasDerivAt U (V t) t := by
    intro t
    rw [hUdef]
    exact (intervalIntegral.integral_hasDerivAt_right
      (hVcont.intervalIntegrable _ _)
      hVcont.stronglyMeasurable.stronglyMeasurableAtFilter
      hVcont.continuousAt).const_add _
  have hG2eq : ∀ t ∈ Icc lo hi, G2 t = f'' t := by
    intro t ht
    rw [hG2def]
    simp only []
    rw [clamp_eq_self ht]
  have hVeq : ∀ t ∈ Icc lo hi, V t = f' t := by
    refine eq_of_hasDerivWithinAt_eq (F := G2) ht0 ?_
      (fun t ht => (hVderiv t).hasDerivWithinAt) (fun t ht => ?_)
    · rw [hVdef]
      simp only []
      rw [intervalIntegral.integral_same, add_zero]
    · rw [hG2eq t ht]
      exact hf' t ht
  have hUeq : ∀ t ∈ Icc lo hi, U t = f t := by
    refine eq_of_hasDerivWithinAt_eq (F := f') ht0 ?_ (fun t ht => ?_)
      (fun t ht => hf t ht)
    · rw [hUdef]
      simp only []
      rw [intervalIntegral.integral_same, add_zero]
    · rw [← hVeq t ht]
      exact (hUderiv t).hasDerivWithinAt
  exact ⟨U, V, G2, hUderiv, hVderiv, hG2cont, hUeq, hVeq⟩

/-! ## The coefficient matrices of equation (3.8), read off the metric jet -/

theorem exists_pair_of_deg_eq_two {a : Multiindex d} (ha : deg a = 2) :
    ∃ p q : Fin d, a = (Pi.single p 1 : Multiindex d) + Pi.single q 1 := by
  have hne : ∃ p, a p ≠ 0 := by
    by_contra hc
    have hc' : ∀ p, a p = 0 := fun p => not_not.1 (not_exists.1 hc p)
    have hz : deg a = 0 := by
      show ∑ i, a i = 0
      exact Finset.sum_eq_zero fun i _ => hc' i
    omega
  obtain ⟨p, hp⟩ := hne
  have hp1 : 1 ≤ a p := Nat.one_le_iff_ne_zero.2 hp
  have hsub : deg (a - (Pi.single p 1 : Multiindex d)) = 1 := by
    have := deg_sub_single (a := a) (i := p) hp1
    omega
  obtain ⟨q, hq⟩ := eq_single_of_deg_eq_one hsub
  refine ⟨p, q, funext fun i => ?_⟩
  have h1 : a i - (Pi.single p 1 : Multiindex d) i
      = (Pi.single q 1 : Multiindex d) i := congrFun hq i
  show a i = (Pi.single p 1 : Multiindex d) i + (Pi.single q 1 : Multiindex d) i
  by_cases hip : i = p
  · rw [hip] at h1 ⊢
    rw [Pi.single_eq_same] at h1 ⊢
    omega
  · rw [Pi.single_eq_of_ne hip] at h1 ⊢
    omega

/-- The source's `C`: twice the degree-zero transverse metric block. -/
def metricC (G : FermiMetricJet d) (s : Real) (p q : Fin d) : Complex :=
  2 * (G.Att p q).c 0 s

/-- The source's `D = (1/4) d_p d_q g^{11}`, in ordinary monomial coefficients.
The diagonal picks up `1/2` and the off-diagonal `1/4`, which is exactly what
makes `2 D` the degree-two coefficient family of `A^{i1 i1}`. -/
def metricD (G : FermiMetricJet d) (s : Real) (p q : Fin d) : Complex :=
  if p = q then
    (2 : Complex)⁻¹ * (G.Att G.i1 G.i1).c
      ((Pi.single p 1 : Multiindex d) + Pi.single p 1) s
  else
    (4 : Complex)⁻¹ * (G.Att G.i1 G.i1).c
      ((Pi.single p 1 : Multiindex d) + Pi.single q 1) s

/-- **The `D` normalization, proved.** -/
theorem metricD_spec (G : FermiMetricJet d) {a : Multiindex d} (ha : deg a = 2)
    (s : Real) :
    (G.Att G.i1 G.i1).c a s = 2 * quadCoeff (metricD G s) a := by
  obtain ⟨p, q, hpq⟩ := exists_pair_of_deg_eq_two ha
  subst hpq
  by_cases hpq' : p = q
  · rw [hpq', quadCoeff_diag]
    show _ = 2 * (if q = q then (2 : Complex)⁻¹ * _ else _)
    rw [if_pos rfl]
    ring
  · rw [quadCoeff_offDiag _ hpq']
    show _ = 2 * ((if p = q then (2 : Complex)⁻¹ * _
        else (4 : Complex)⁻¹ * (G.Att G.i1 G.i1).c
          ((Pi.single p 1 : Multiindex d) + Pi.single q 1) s)
      + (if q = p then (2 : Complex)⁻¹ * _
        else (4 : Complex)⁻¹ * (G.Att G.i1 G.i1).c
          ((Pi.single q 1 : Multiindex d) + Pi.single p 1) s))
    rw [if_neg hpq', if_neg (Ne.symm hpq'),
      show ((Pi.single q 1 : Multiindex d) + Pi.single p 1)
        = (Pi.single p 1 : Multiindex d) + Pi.single q 1 from add_comm _ _]
    ring

theorem metricC_spec (G : FermiMetricJet d) (p q : Fin d) (s : Real) :
    metricC G s p q = 2 * (G.Att p q).c 0 s := rfl

/-- The metric data the bridge consumes.  Fermi first-order normalization,
symmetry and reality of the transverse block, and `C1` regularity.  There is no
Riccati equation, no degree-two cancellation and no phase here. -/
structure FermiQuadraticData (G : FermiMetricJet d) : Prop where
  firstOrderVanishing : ∀ (i j k : Fin d) (s : Real),
    (G.Att i j).c (Pi.single k 1) s = 0
  attSymm : ∀ (i j : Fin d) (b : Multiindex d) (s : Real),
    (G.Att i j).c b s = (G.Att j i).c b s
  attReal : ∀ (i j : Fin d) (b : Multiindex d) (s : Real),
    (starRingEnd Complex) ((G.Att i j).c b s) = (G.Att i j).c b s
  attC1 : ∀ i j, (G.Att i j).C1

theorem FermiQuadraticData.toFermiCompat {G : FermiMetricJet d}
    (h : FermiQuadraticData G) : FermiCompat G (metricC G) (metricD G) where
  firstOrderVanishing := h.firstOrderVanishing
  matchC := fun _ _ _ => rfl
  matchD := fun _ s ha => metricD_spec G ha s

/-! ## Entrywise derivatives of matrix paths -/

/-- Evaluation of a matrix entry is a real-linear continuous map, because the
space is finite dimensional.  This is what lets an entrywise derivative be read
off a matrix-valued one. -/
def entryCLM (p q : Fin d) :
    Matrix (Fin d) (Fin d) Complex →L[Real] Complex :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A => A p q
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

theorem hasDerivAt_entry {f : Real -> Matrix (Fin d) (Fin d) Complex}
    {f' : Matrix (Fin d) (Fin d) Complex} {t : Real} (h : HasDerivAt f f' t)
    (p q : Fin d) : HasDerivAt (fun s => f s p q) (f' p q) t :=
  (entryCLM p q).hasFDerivAt.comp_hasDerivAt t h

/-! ## Metric-derived coefficient data -/

def metricC' (G : FermiMetricJet d) (s : Real) (p q : Fin d) : Complex :=
  2 * (G.Att p q).dc 0 s

def metricD' (G : FermiMetricJet d) (s : Real) (p q : Fin d) : Complex :=
  if p = q then
    (2 : Complex)⁻¹ * (G.Att G.i1 G.i1).dc
      ((Pi.single p 1 : Multiindex d) + Pi.single p 1) s
  else
    (4 : Complex)⁻¹ * (G.Att G.i1 G.i1).dc
      ((Pi.single p 1 : Multiindex d) + Pi.single q 1) s

theorem hasDerivAt_metricC (G : FermiMetricJet d) (p q : Fin d) (s : Real) :
    HasDerivAt (fun t => metricC G t p q) (metricC' G s p q) s :=
  ((G.Att p q).hasDeriv 0 s).const_mul 2

theorem hasDerivAt_metricD (G : FermiMetricJet d) (p q : Fin d) (s : Real) :
    HasDerivAt (fun t => metricD G t p q) (metricD' G s p q) s := by
  by_cases h : p = q
  · simpa [metricD, metricD', h] using
      ((G.Att G.i1 G.i1).hasDeriv
        ((Pi.single q 1 : Multiindex d) + Pi.single q 1) s).const_mul (2 : Complex)⁻¹
  · simpa [metricD, metricD', h] using
      ((G.Att G.i1 G.i1).hasDeriv
        ((Pi.single p 1 : Multiindex d) + Pi.single q 1) s).const_mul (4 : Complex)⁻¹

theorem continuous_metricC (G : FermiMetricJet d) (p q : Fin d) :
    Continuous fun s => metricC G s p q :=
  continuous_const.mul ((G.Att p q).continuous_c 0)

theorem continuous_metricD (G : FermiMetricJet d) (p q : Fin d) :
    Continuous fun s => metricD G s p q := by
  by_cases h : p = q
  · simpa [metricD, h] using
      (continuous_const.mul ((G.Att G.i1 G.i1).continuous_c
        ((Pi.single q 1 : Multiindex d) + Pi.single q 1)))
  · simpa [metricD, h] using
      (continuous_const.mul ((G.Att G.i1 G.i1).continuous_c
        ((Pi.single p 1 : Multiindex d) + Pi.single q 1)))

theorem continuous_metricC' {G : FermiMetricJet d}
    (hG : FermiQuadraticData G) (p q : Fin d) :
    Continuous fun s => metricC' G s p q :=
  continuous_const.mul (hG.attC1 p q 0)

theorem continuous_metricD' {G : FermiMetricJet d}
    (hG : FermiQuadraticData G) (p q : Fin d) :
    Continuous fun s => metricD' G s p q := by
  by_cases h : p = q
  · simpa [metricD', h] using
      (continuous_const.mul (hG.attC1 G.i1 G.i1
        ((Pi.single q 1 : Multiindex d) + Pi.single q 1)))
  · simpa [metricD', h] using
      (continuous_const.mul (hG.attC1 G.i1 G.i1
        ((Pi.single p 1 : Multiindex d) + Pi.single q 1)))

/-- **The source's equation-(3.8) coefficient data, read off the metric jet.**
Only interval geometry and the admissible initial Hessian are extra inputs. -/
def toCoefficients (G : FermiMetricJet d) (hG : FermiQuadraticData G)
    (lower upper startTime endTime : Real)
    (hstart : startTime ∈ Ioo lower upper) (hend : endTime ∈ Ioo lower upper)
    (H0 : Matrix (Fin d) (Fin d) Complex) (hH0symm : H0.IsSymm)
    (hH0pos : ComplexPosDef (hermitianImaginaryPart H0)) :
    Coefficients (Fin d) where
  lower := lower
  upper := upper
  startTime := startTime
  endTime := endTime
  start_mem := hstart
  end_mem := hend
  C := metricC G
  D := metricD G
  C_continuous :=
    (continuous_pi fun p => continuous_pi fun q => continuous_metricC G p q).continuousOn
  D_continuous :=
    (continuous_pi fun p => continuous_pi fun q => continuous_metricD G p q).continuousOn
  C_symmetric := by
    intro t _
    ext p q
    show metricC G t q p = metricC G t p q
    rw [metricC, metricC, hG.attSymm q p 0 t]
  D_symmetric := by
    intro t _
    ext p q
    show metricD G t q p = metricD G t p q
    by_cases h : p = q
    · rw [h]
    · rw [metricD, metricD, if_neg (Ne.symm h), if_neg h,
        show ((Pi.single q 1 : Multiindex d) + Pi.single p 1)
          = (Pi.single p 1 : Multiindex d) + Pi.single q 1 from add_comm _ _]
  C_hermitian := by
    intro t _
    ext p q
    show (starRingEnd Complex) (metricC G t q p) = metricC G t p q
    rw [metricC, metricC, map_mul, hG.attReal q p 0 t, hG.attSymm q p 0 t]
    congr 1
    exact map_ofNat _ _
  D_hermitian := by
    intro t _
    ext p q
    show (starRingEnd Complex) (metricD G t q p) = metricD G t p q
    by_cases h : p = q
    · rw [h, metricD, if_pos rfl, map_mul, hG.attReal G.i1 G.i1 _ t, map_inv₀,
        map_ofNat]
    · rw [metricD, metricD, if_neg (Ne.symm h), if_neg h, map_mul,
        hG.attReal G.i1 G.i1 _ t, map_inv₀, map_ofNat,
        show ((Pi.single q 1 : Multiindex d) + Pi.single p 1)
          = (Pi.single p 1 : Multiindex d) + Pi.single q 1 from add_comm _ _]
  H0 := H0
  H0_symmetric := hH0symm
  H0_imaginaryPositive := hH0pos

/-! ## The generated Riccati matrix as a global `C^2` path -/

set_option maxHeartbeats 1000000 in
/-- **The generated Riccati flow, extended to a globally twice differentiable
matrix path.**  On the paper interval it *is* the generated flow, and it
satisfies the entrywise form of equation (3.8) there.  No path, derivative
certificate or invertibility statement is an input. -/
theorem exists_global_riccati (G : FermiMetricJet d) (hG : FermiQuadraticData G)
    (dat : Coefficients (Fin d)) (hC : dat.C = metricC G)
    (hD : dat.D = metricD G) :
    ∃ M M' M'' : Real -> Fin d -> Fin d -> Complex,
      (∀ p q s, HasDerivAt (fun t => M t p q) (M' s p q) s) ∧
      (∀ p q s, HasDerivAt (fun t => M' t p q) (M'' s p q) s) ∧
      (∀ p q, Continuous fun s => M'' s p q) ∧
      (∀ s ∈ uIcc dat.startTime dat.endTime, ∀ p q,
        M s p q = dat.toRiccatiFlow.H s p q) ∧
      (∀ s ∈ uIcc dat.startTime dat.endTime, ∀ p q,
        M' s p q + (∑ i, ∑ j, M s p i * metricC G s i j * M s j q)
          + metricD G s p q = 0) := by
  classical
  obtain ⟨Hf, hHf⟩ : ∃ Hf, Hf = dat.toRiccatiFlow.H := ⟨_, rfl⟩
  obtain ⟨lo, hlo⟩ : ∃ lo, lo = min dat.startTime dat.endTime := ⟨_, rfl⟩
  obtain ⟨hi, hhi⟩ : ∃ hi, hi = max dat.startTime dat.endTime := ⟨_, rfl⟩
  have hJ : uIcc dat.startTime dat.endTime = Icc lo hi := by rw [hlo, hhi]; rfl
  have ht0 : dat.startTime ∈ Icc lo hi := by
    rw [← hJ]
    exact left_mem_uIcc
  have hmat : ∀ t ∈ Icc lo hi,
      HasDerivAt Hf (-(Hf t * dat.C t * Hf t) - dat.D t) t := by
    intro t ht
    rw [hHf]
    exact dat.generated_H_hasDerivAt (by rw [hJ]; exact ht)
  obtain ⟨f, hf⟩ : ∃ f : Fin d -> Fin d -> Real -> Complex,
      f = fun p q t => Hf t p q := ⟨_, rfl⟩
  obtain ⟨g, hg⟩ : ∃ g : Fin d -> Fin d -> Real -> Complex,
      g = fun p q t =>
        -(∑ j, (∑ i, Hf t p i * metricC G t i j) * Hf t j q)
          - metricD G t p q := ⟨_, rfl⟩
  have hfd : ∀ (p q : Fin d), ∀ t ∈ Icc lo hi, HasDerivAt (f p q) (g p q t) t := by
    intro p q t ht
    have h := hasDerivAt_entry (hmat t ht) p q
    have heq : (-(Hf t * dat.C t * Hf t) - dat.D t) p q = g p q t := by
      show -((Hf t * dat.C t * Hf t) p q) - dat.D t p q = _
      rw [hg, hC, hD]
      simp only [Matrix.mul_apply]
    rw [heq] at h
    simpa [hf] using h
  have hfe : ∀ (a b : Fin d), (f a b) = fun u => Hf u a b := by
    intro a b
    rw [hf]
  have hHd : ∀ (p q : Fin d), ∀ t ∈ Icc lo hi,
      HasDerivAt (fun u => Hf u p q) (g p q t) t := by
    intro p q t ht
    have := hfd p q t ht
    rw [hfe p q] at this
    exact this
  obtain ⟨g', hg'⟩ : ∃ g' : Fin d -> Fin d -> Real -> Complex,
      g' = fun p q t =>
        -(∑ j, ((∑ i, (g p i t * metricC G t i j + Hf t p i * metricC' G t i j))
            * Hf t j q
          + (∑ i, Hf t p i * metricC G t i j) * g j q t))
        - metricD' G t p q := ⟨_, rfl⟩
  have hgd : ∀ (p q : Fin d), ∀ t ∈ Icc lo hi,
      HasDerivAt (g p q) (g' p q t) t := by
    intro p q t ht
    have hP : HasDerivAt
        (fun u => ∑ j, (∑ i, Hf u p i * metricC G u i j) * Hf u j q)
        (∑ j, ((∑ i, (g p i t * metricC G t i j + Hf t p i * metricC' G t i j))
            * Hf t j q
          + (∑ i, Hf t p i * metricC G t i j) * g j q t)) t := by
      refine hasDerivAt_finsum _ _ t fun j => ?_
      have h1 : HasDerivAt (fun u => ∑ i, Hf u p i * metricC G u i j)
          (∑ i, (g p i t * metricC G t i j + Hf t p i * metricC' G t i j)) t :=
        hasDerivAt_finsum _ _ t fun i =>
          HasDerivAt.fun_mul (hHd p i t ht) (hasDerivAt_metricC G i j t)
      exact HasDerivAt.fun_mul h1 (hHd j q t ht)
    have hres := HasDerivAt.fun_sub (HasDerivAt.fun_neg hP)
      (hasDerivAt_metricD G p q t)
    have hfun : (g p q) = (fun u : Real =>
        -(∑ j, (∑ i, Hf u p i * metricC G u i j) * Hf u j q)
          - metricD G u p q) := by rw [hg]
    rw [hg']
    simp only []
    rw [hfun]
    exact hres
  have hfcont : ∀ (p q : Fin d), ContinuousOn (f p q) (Icc lo hi) :=
    fun p q t ht => ((hfd p q t ht).continuousAt).continuousWithinAt
  have hgcont : ∀ (p q : Fin d), ContinuousOn (g p q) (Icc lo hi) :=
    fun p q t ht => ((hgd p q t ht).continuousAt).continuousWithinAt
  have hHcont : ∀ (p q : Fin d), ContinuousOn (fun t => Hf t p q) (Icc lo hi) := by
    intro p q
    have := hfcont p q
    rw [hfe p q] at this
    exact this
  have hg'cont : ∀ (p q : Fin d), ContinuousOn (g' p q) (Icc lo hi) := by
    intro p q
    rw [hg']
    refine ContinuousOn.sub (ContinuousOn.neg ?_)
      (continuous_metricD' hG p q).continuousOn
    refine continuousOn_finset_sum _ fun j _ => ?_
    refine ContinuousOn.add (ContinuousOn.mul ?_ (hHcont j q)) ?_
    · refine continuousOn_finset_sum _ fun i _ => ?_
      exact ((hgcont p i).mul (continuous_metricC G i j).continuousOn).add
        ((hHcont p i).mul (continuous_metricC' hG i j).continuousOn)
    · exact (continuousOn_finset_sum _ fun i _ =>
        (hHcont p i).mul (continuous_metricC G i j).continuousOn).mul (hgcont j q)
  choose E E' E'' hE hE' hE''cont hEeq hE'eq using fun pq : Fin d × Fin d =>
    exists_c2_extension (t0 := dat.startTime) ht0 (f pq.1 pq.2) (g pq.1 pq.2)
      (g' pq.1 pq.2) (fun t ht => (hfd pq.1 pq.2 t ht).hasDerivWithinAt)
      (fun t ht => (hgd pq.1 pq.2 t ht).hasDerivWithinAt) (hg'cont pq.1 pq.2)
  refine ⟨fun t p q => E (p, q) t, fun t p q => E' (p, q) t,
    fun t p q => E'' (p, q) t, fun p q s => hE (p, q) s,
    fun p q s => hE' (p, q) s, fun p q => hE''cont (p, q), ?_, ?_⟩
  · intro s hs p q
    rw [hJ] at hs
    have := hEeq (p, q) s hs
    rw [hfe p q] at this
    simp only [] at this ⊢
    rw [this, hHf]
  · intro s hs p q
    rw [hJ] at hs
    simp only []
    rw [hE'eq (p, q) s hs]
    have hsum : ∀ i j : Fin d, E (p, i) s * metricC G s i j * E (j, q) s
        = Hf s p i * metricC G s i j * Hf s j q := by
      intro i j
      have h1 := hEeq (p, i) s hs
      have h2 := hEeq (j, q) s hs
      rw [hfe p i] at h1
      rw [hfe j q] at h2
      simp only [] at h1 h2
      rw [h1, h2]
    rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) =>
      Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) => hsum i j, hg]
    simp only []
    rw [Finset.sum_comm]
    have hdist : ∀ x : Fin d, (∑ x1, Hf s p x1 * metricC G s x1 x) * Hf s x q
        = ∑ x1, Hf s p x1 * metricC G s x1 x * Hf s x q :=
      fun x => Finset.sum_mul _ _ _
    rw [Finset.sum_congr rfl fun x (_ : x ∈ Finset.univ) => hdist x]
    ring

/-! ## The main endpoint -/

set_option maxHeartbeats 1000000 in
/-- **The finite-order phase, generated from metric and Riccati input alone.**
The inputs are the metric jet with its Fermi normalization, a base phase
carrying only the source's degrees zero and one, interval geometry and an
admissible initial Hessian.  No matrix path, no degree-two identity, no
cancellation statement and no invertibility claim is assumed: the Riccati flow
is generated, extended, shown to satisfy the exact degree-two identity, and fed
into the transverse-jet recursion.  The conclusion is about the *actual*
`jetEikonal`. -/
theorem exists_phase_from_riccati (G : FermiMetricJet d)
    (hG : FermiQuadraticData G) (base : SourcePhaseJet G) (hbase : C1Data G base)
    (hq : QuadFree base) {lower upper startTime endTime : Real}
    (hstart : startTime ∈ Ioo lower upper) (hend : endTime ∈ Ioo lower upper)
    (H0 : Matrix (Fin d) (Fin d) Complex) (hH0symm : H0.IsSymm)
    (hH0pos : ComplexPosDef (hermitianImaginaryPart H0))
    (t0 : Icc (min startTime endTime) (max startTime endTime)) (N : Nat) :
    ∃ (M : Real -> Fin d -> Fin d -> Complex) (P : SourcePhaseJet G),
      (∀ s ∈ uIcc startTime endTime, M s
        = (toCoefficients G hG lower upper startTime endTime hstart hend H0
            hH0symm hH0pos).toRiccatiFlow.H s) ∧
      (∀ s ∈ uIcc startTime endTime, Matrix.IsSymm (M s)) ∧
      C1Data G P ∧
      (∀ (a : Multiindex d) (s : Real), deg a ≤ 1 ->
        P.phi.c a s = base.phi.c a s) ∧
      (∀ (a : Multiindex d) (s : Real), deg a = 2 ->
        P.phi.c a s = base.phi.c a s + quadCoeff (M s) a) ∧
      (∀ s ∈ uIcc startTime endTime, ∀ a : Multiindex d, deg a ≤ N ->
        jetEikonal G.Ass G.Bs G.Att P.phi P.dphi a s = 0) := by
  classical
  obtain ⟨M, M', M'', hM, hM', hM''cont, hMeq, hMric⟩ :=
    exists_global_riccati G hG
      (toCoefficients G hG lower upper startTime endTime hstart hend H0
        hH0symm hH0pos) rfl rfl
  have hJ : uIcc startTime endTime
      = Icc (min startTime endTime) (max startTime endTime) := rfl
  have hMmat : ∀ s ∈ uIcc startTime endTime, M s
      = (toCoefficients G hG lower upper startTime endTime hstart hend H0
          hH0symm hH0pos).toRiccatiFlow.H s := by
    intro s hs
    exact funext fun p => funext fun q => hMeq s hs p q
  have hsymm : ∀ s ∈ uIcc startTime endTime, ∀ p q : Fin d,
      M s p q = M s q p := by
    intro s hs p q
    have hflow := ((toCoefficients G hG lower upper startTime endTime hstart hend
      H0 hH0symm hH0pos).toRiccatiFlow.phase_certificate
      (t := s) hs).phaseHessianSymmetric
    have h1 : ((toCoefficients G hG lower upper startTime endTime hstart hend H0
        hH0symm hH0pos).toRiccatiFlow.H s) q p
      = ((toCoefficients G hG lower upper startTime endTime hstart hend H0
        hH0symm hH0pos).toRiccatiFlow.H s) p q := congrFun (congrFun hflow p) q
    rw [hMeq s hs p q, hMeq s hs q p, h1]
  have hric : ∀ s ∈ Icc (min startTime endTime) (max startTime endTime),
      ∀ a : DegreeIndex d 2,
        2 * quadCoeff (M' s) a.1
            + ∑ beta : DegreeIndex d 2,
                phaseEikonalMatrix base 2 s a beta * quadCoeff (M s) beta.1
            + quadraticSelfTerm G.Att (quadJet M M' hM) a.1 s
          = phaseSource base 2 s a := by
    intro s hs a
    rw [← hJ] at hs
    exact hric_of_riccati hG.toFermiCompat hq M M' hM (hsymm s hs)
      (fun p q => hMric s hs p q) a
  obtain ⟨P, hPC1, hPlow, hPquad, hPcancel⟩ :=
    exists_phase_cancelling_upto_of_riccati base hbase t0 M M' M'' hM hM'
      hM''cont hric N
  refine ⟨M, P, hMmat, ?_, hPC1, hPlow, hPquad, ?_⟩
  · intro s hs
    ext p q
    exact hsymm s hs q p
  · intro s hs a ha
    rw [hJ] at hs
    exact hPcancel s hs a ha

/-- **The generated degree-two phase is uniformly coercive.**  Any quantitative
lower bound on the initial phase transports to the whole interval through the
existing Riccati machinery, and the constructed phase carries that matrix. -/
theorem generated_quadratic_coercivity (G : FermiMetricJet d)
    (hG : FermiQuadraticData G) {lower upper startTime endTime : Real}
    (hstart : startTime ∈ Ioo lower upper) (hend : endTime ∈ Ioo lower upper)
    (H0 : Matrix (Fin d) (Fin d) Complex) (hH0symm : H0.IsSymm)
    (hH0pos : ComplexPosDef (hermitianImaginaryPart H0))
    {M : Real -> Fin d -> Fin d -> Complex}
    (hMmat : ∀ s ∈ uIcc startTime endTime, M s
      = (toCoefficients G hG lower upper startTime endTime hstart hend H0
          hH0symm hH0pos).toRiccatiFlow.H s)
    (c0 : Real) (hc0 : 0 < c0)
    (hcoercive : RealCoercive (hermitianImaginaryPart H0) c0)
    {s : Real} (hs : s ∈ uIcc startTime endTime) (x : Fin d -> Complex) :
    (c0 / (toCoefficients G hG lower upper startTime endTime hstart hend H0
        hH0symm hH0pos).actionBound ^ 2) * ‖x‖ ^ 2
      ≤ (complexQuadratic (M s) x).im := by
  rw [hMmat s hs]
  exact (toCoefficients G hG lower upper startTime endTime hstart hend H0
    hH0symm hH0pos).generated_uniform_coercivity c0 hc0 hcoercive hs x

end LiuWang2025SemilinearWaveRiccatiPhaseBridge
