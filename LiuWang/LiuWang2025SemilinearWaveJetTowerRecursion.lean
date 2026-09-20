import LiuWang.LiuWang2025SemilinearWaveLongitudinalJet
import LiuWang.LiuWang2025SemilinearWaveTransportHierarchy

/-!
# Liu-Wang semilinear wave: the triangular longitudinal recursion

Both of Section 3's coefficient hierarchies have the same shape.  Writing the
transverse jet of the eikonal, respectively of the transport expression, in
multi-index coordinates, the coefficient at a multi-index `alpha` is

  `2 d_s c_alpha(s) + q_alpha(s) c_alpha(s) - (source built from strictly
   lower total degree)`,

the `q_alpha` coming from the diagonal action of the paper's `4 (M z) . grad_z`
on `z^alpha`, and the source from the already-known coefficients.  That is a
*triangular* system: degree by degree it is a scalar inhomogeneous linear ODE
along the geodesic.

`TowerData` records the two coefficient families of that system -- the
longitudinal coefficient `q` and the source functional `src`, with an explicit
locality axiom saying that `src` at total degree `r` reads only coefficients of
degree strictly below `r`.  It records *no* cancellation.

`tower` then solves the system degree by degree using the repository's existing
integrating-factor solution `hierarchyAmplitude`, which is itself a construction
by quadrature, not an assumption.  The theorems below establish, for the
constructed family:

* `tower_of_deg_le_base` / `tower_of_deg_gt` : the prescribed low degrees are
  kept and the unreached degrees are zero;
* `tower_stable` : raising the truncation order never disturbs a degree that
  has already been solved, so the recursion has a well-defined limit;
* `tower_hasDerivAt` and `tower_solves` : every constructed coefficient of
  degree `baseDeg + r + 1` satisfies its own ODE;
* `tower_src_stable` and `towerCoefficient_eq_zero` : the source may equally be
  read off the final family, so the cancellation holds *simultaneously* for all
  constructed degrees.

The degrees at or below `baseDeg` are the source's prescribed `phi_0 = 0` and
`phi_1 = z^1`; their cancellation is the Fermi normalization of the chart and is
imposed as `FermiNormalizedBase`, a statement about the geometry and the
prescribed low-order phase only.  It is proved for the Fermi chart, from actual
derivatives of the metric components, in
`LiuWang2025SemilinearWaveFermiEikonalJet`.
-/

noncomputable section

open scoped BigOperators

namespace LiuWang2025SemilinearWaveJetTowerRecursion

open LiuWang2025SemilinearWaveTransverseJet
open LiuWang2025SemilinearWaveTransportHierarchy

variable {d : Nat}

/-- The data of one triangular longitudinal system: the diagonal longitudinal
coefficient and the source functional, the latter reading only strictly lower
total degrees.  No cancellation is recorded here. -/
structure TowerData (d : Nat) where
  /-- The longitudinal coefficient at each multi-index. -/
  q : Multiindex d -> Real -> Complex
  /-- Continuity of the longitudinal coefficient. -/
  hq : ∀ a, Continuous (q a)
  /-- The source at total degree `r`, as a functional of the coefficient
  family. -/
  src : Nat -> (Multiindex d -> Real -> Complex) -> Multiindex d -> Real -> Complex
  /-- The source of a continuous family is continuous. -/
  hsrc : ∀ (r : Nat) (fam : Multiindex d -> Real -> Complex) (a : Multiindex d),
    (∀ b, Continuous (fam b)) -> Continuous (src r fam a)
  /-- **Triangularity.**  The source at degree `r` reads only coefficients of
  total degree strictly below `r`. -/
  src_lower : ∀ (r : Nat) (fam fam' : Multiindex d -> Real -> Complex)
    (a : Multiindex d),
    (∀ b, deg b < r -> fam b = fam' b) -> src r fam a = src r fam' a

namespace TowerData

variable (T : TowerData d) (s0 : Real) (init : Multiindex d -> Complex)
  (base : Multiindex d -> Real -> Complex) (baseDeg : Nat)

/-- **The triangular recursion.**  Degrees at or below `baseDeg` are the
prescribed ones; each higher degree is obtained from the integrating-factor
solution of its own scalar ODE, whose source is the already-constructed family
of strictly lower degree. -/
def tower : Nat -> Multiindex d -> Real -> Complex
  | 0 => fun a => if deg a ≤ baseDeg then base a else 0
  | r + 1 => fun a =>
      if deg a = baseDeg + r + 1 then
        hierarchyAmplitude (T.q a)
          (T.src (baseDeg + r + 1) (tower r) a) s0 (init a)
      else tower r a

theorem tower_zero (a : Multiindex d) :
    tower T s0 init base baseDeg 0 a = if deg a ≤ baseDeg then base a else 0 := rfl

theorem tower_succ (r : Nat) (a : Multiindex d) :
    tower T s0 init base baseDeg (r + 1) a
      = if deg a = baseDeg + r + 1 then
          hierarchyAmplitude (T.q a)
            (T.src (baseDeg + r + 1) (tower T s0 init base baseDeg r) a) s0 (init a)
        else tower T s0 init base baseDeg r a := rfl

/-- The prescribed low degrees are preserved by the whole recursion. -/
theorem tower_of_deg_le_base (r : Nat) {a : Multiindex d} (ha : deg a ≤ baseDeg) :
    tower T s0 init base baseDeg r a = base a := by
  induction r with
  | zero => rw [tower_zero, if_pos ha]
  | succ r ih => rw [tower_succ, if_neg (by omega), ih]

/-- Degrees the recursion has not yet reached are zero. -/
theorem tower_of_deg_gt (r : Nat) {a : Multiindex d} (ha : baseDeg + r < deg a) :
    tower T s0 init base baseDeg r a = 0 := by
  induction r with
  | zero => rw [tower_zero, if_neg (by omega)]
  | succ r ih => rw [tower_succ, if_neg (by omega), ih (by omega)]

/-- **Stability of the recursion.**  A degree already solved is never revised,
so the truncations have a common limit on every fixed degree. -/
theorem tower_stable {a : Multiindex d} {r r' : Nat} (hle : r ≤ r')
    (hdeg : deg a ≤ baseDeg + r) :
    tower T s0 init base baseDeg r' a = tower T s0 init base baseDeg r a := by
  induction r' with
  | zero =>
    obtain rfl : r = 0 := Nat.le_zero.1 hle
    rfl
  | succ r' ih =>
    rcases Nat.lt_or_ge r (r' + 1) with h | h
    · have hr : r ≤ r' := Nat.lt_succ_iff.1 h
      rw [tower_succ, if_neg (by omega), ih hr]
    · obtain rfl : r = r' + 1 := le_antisymm hle h
      rfl

/-- Every constructed coefficient is continuous. -/
theorem tower_continuous (hbase : ∀ a, Continuous (base a)) (r : Nat) :
    ∀ a, Continuous (tower T s0 init base baseDeg r a) := by
  induction r with
  | zero =>
    intro a
    by_cases h : deg a ≤ baseDeg
    · have heq : tower T s0 init base baseDeg 0 a = base a := by
        rw [tower_zero, if_pos h]
      rw [heq]
      exact hbase a
    · have heq : tower T s0 init base baseDeg 0 a = 0 := by
        rw [tower_zero, if_neg h]
      rw [heq]
      exact continuous_const
  | succ r ih =>
    intro a
    by_cases h : deg a = baseDeg + r + 1
    · have heq : tower T s0 init base baseDeg (r + 1) a
          = hierarchyAmplitude (T.q a)
              (T.src (baseDeg + r + 1) (tower T s0 init base baseDeg r) a) s0
              (init a) := by
        rw [tower_succ, if_pos h]
      rw [heq]
      exact continuous_hierarchyAmplitude (T.hq a) (T.hsrc _ _ a ih) s0 (init a)
    · have heq : tower T s0 init base baseDeg (r + 1) a
          = tower T s0 init base baseDeg r a := by
        rw [tower_succ, if_neg h]
      rw [heq]
      exact ih a

/-- **Each constructed coefficient really solves its own ODE**, with the
derivative certified. -/
theorem tower_hasDerivAt (hbase : ∀ a, Continuous (base a)) (r : Nat)
    {a : Multiindex d} (ha : deg a = baseDeg + r + 1) (s : Real) :
    HasDerivAt (tower T s0 init base baseDeg (r + 1) a)
      (-((2 : Complex))⁻¹ * T.q a s * tower T s0 init base baseDeg (r + 1) a s
        + ((2 : Complex))⁻¹
            * T.src (baseDeg + r + 1) (tower T s0 init base baseDeg r) a s) s := by
  have hfun : tower T s0 init base baseDeg (r + 1) a
      = hierarchyAmplitude (T.q a)
          (T.src (baseDeg + r + 1) (tower T s0 init base baseDeg r) a) s0
          (init a) := by
    rw [tower_succ, if_pos ha]
  rw [hfun]
  exact hierarchyAmplitude_hasDerivAt (T.hq a)
    (T.hsrc _ _ a (tower_continuous T s0 init base baseDeg hbase r)) s0 (init a) s

/-- The ODE itself, in the source's form `2 c' + q c = source`. -/
theorem tower_solves (r : Nat) {a : Multiindex d} (s : Real) :
    2 * (-((2 : Complex))⁻¹ * T.q a s * tower T s0 init base baseDeg (r + 1) a s
          + ((2 : Complex))⁻¹
              * T.src (baseDeg + r + 1) (tower T s0 init base baseDeg r) a s)
        + T.q a s * tower T s0 init base baseDeg (r + 1) a s
      = T.src (baseDeg + r + 1) (tower T s0 init base baseDeg r) a s := by
  ring

/-- **The source may be read off the final family.**  Triangularity plus
stability means the degree-`baseDeg + r + 1` source is unchanged if computed
from any later truncation. -/
theorem tower_src_stable {r r' : Nat} (hle : r ≤ r') (a : Multiindex d) :
    T.src (baseDeg + r + 1) (tower T s0 init base baseDeg r) a
      = T.src (baseDeg + r + 1) (tower T s0 init base baseDeg r') a := by
  refine T.src_lower _ _ _ a fun b hb => ?_
  exact (tower_stable T s0 init base baseDeg hle (by omega)).symm

/-! ### The constructed longitudinal derivative of the whole family -/

/-- The longitudinal derivative of the constructed family, itself constructed:
the prescribed derivative in the low degrees, the ODE right-hand side in the
solved degrees, zero beyond. -/
def towerDeriv (dbase : Multiindex d -> Real -> Complex) (R : Nat)
    (b : Multiindex d) (u : Real) : Complex :=
  if deg b ≤ baseDeg then dbase b u
  else if deg b ≤ baseDeg + R then
    -((2 : Complex))⁻¹ * T.q b u * tower T s0 init base baseDeg R b u
      + ((2 : Complex))⁻¹ * T.src (deg b) (tower T s0 init base baseDeg R) b u
  else 0

/-- **The constructed derivative really is the derivative.** -/
theorem towerDeriv_hasDerivAt (hbase : ∀ a, Continuous (base a))
    (dbase : Multiindex d -> Real -> Complex)
    (hdbase : ∀ b u, HasDerivAt (base b) (dbase b u) u) (R : Nat)
    (b : Multiindex d) (u : Real) :
    HasDerivAt (tower T s0 init base baseDeg R b)
      (towerDeriv T s0 init base baseDeg dbase R b u) u := by
  by_cases hlow : deg b ≤ baseDeg
  · have heq : tower T s0 init base baseDeg R b = base b :=
      tower_of_deg_le_base T s0 init base baseDeg R hlow
    rw [heq, towerDeriv, if_pos hlow]
    exact hdbase b u
  · by_cases hhigh : deg b ≤ baseDeg + R
    · obtain ⟨r, hr⟩ : ∃ r, deg b = baseDeg + r + 1 := ⟨deg b - baseDeg - 1, by omega⟩
      have hrR : r + 1 ≤ R := by omega
      have hstab : tower T s0 init base baseDeg R b
          = tower T s0 init base baseDeg (r + 1) b :=
        tower_stable T s0 init base baseDeg hrR (by omega)
      have hsrc : T.src (baseDeg + r + 1) (tower T s0 init base baseDeg r) b u
          = T.src (deg b) (tower T s0 init base baseDeg R) b u := by
        rw [hr]
        exact congrFun (tower_src_stable T s0 init base baseDeg
          (Nat.le_of_succ_le hrR) b) u
      rw [towerDeriv, if_neg hlow, if_pos hhigh, hstab]
      have h := tower_hasDerivAt T s0 init base baseDeg hbase r hr u
      rw [← hstab, hsrc] at h
      rw [hstab] at h
      exact h
    · have heq : tower T s0 init base baseDeg R b = 0 :=
        tower_of_deg_gt T s0 init base baseDeg R (by omega)
      rw [heq, towerDeriv, if_neg hlow, if_neg hhigh]
      exact hasDerivAt_const u 0

end TowerData

/-! ## The jet-level cancellation -/

open TowerData

/-- The coefficient of `z^alpha` in the jet-level eikonal, respectively
transport, expression: the left-hand side of the source's ODE minus its
source term. -/
def towerCoefficient (T : TowerData d)
    (fam dfam : Multiindex d -> Real -> Complex) (a : Multiindex d) (s : Real) :
    Complex :=
  2 * dfam a s + T.q a s * fam a s - T.src (deg a) fam a s

/-- **Every constructed degree cancels.**  The derivative appearing here is the
constructed one, certified by `towerDeriv_hasDerivAt`; the source is read off
the final family.  Nothing about the cancellation is assumed. -/
theorem towerCoefficient_eq_zero (T : TowerData d) (s0 : Real)
    (init : Multiindex d -> Complex) (base dbase : Multiindex d -> Real -> Complex)
    (baseDeg R : Nat) {a : Multiindex d}
    (hlow : ¬ deg a ≤ baseDeg) (hhigh : deg a ≤ baseDeg + R) (s : Real) :
    towerCoefficient T (tower T s0 init base baseDeg R)
      (towerDeriv T s0 init base baseDeg dbase R) a s = 0 := by
  rw [towerCoefficient, towerDeriv, if_neg hlow, if_pos hhigh]
  ring

/-- **The Fermi normalization of the prescribed low-order phase.**  The
source's `phi_0 = 0` and `phi_1 = z^1` make the jet-level expression vanish in
total degrees at most `baseDeg`.  This is a statement about the chart and the
prescribed low-order phase only, and for the Fermi chart it is proved from
actual derivatives of the metric components in
`LiuWang2025SemilinearWaveFermiEikonalJet` (`eikonal_center_eq_zero` and
`eikonal_firstJet_eq_zero`). -/
def FermiNormalizedBase (T : TowerData d)
    (base dbase : Multiindex d -> Real -> Complex) (baseDeg : Nat) : Prop :=
  ∀ (a : Multiindex d), deg a ≤ baseDeg -> ∀ s : Real,
    2 * dbase a s + T.q a s * base a s = T.src (deg a) base a s

/-- **The prescribed degrees cancel too**, given the Fermi normalization of the
chart.  Triangularity is what lets the source be recomputed from the
constructed family. -/
theorem towerCoefficient_eq_zero_of_le_base (T : TowerData d) (s0 : Real)
    (init : Multiindex d -> Complex) (base dbase : Multiindex d -> Real -> Complex)
    (baseDeg R : Nat) (hnorm : FermiNormalizedBase T base dbase baseDeg)
    {a : Multiindex d} (ha : deg a ≤ baseDeg) (s : Real) :
    towerCoefficient T (tower T s0 init base baseDeg R)
      (towerDeriv T s0 init base baseDeg dbase R) a s = 0 := by
  have hfam : tower T s0 init base baseDeg R a = base a :=
    tower_of_deg_le_base T s0 init base baseDeg R ha
  have hsrc : T.src (deg a) (tower T s0 init base baseDeg R) a
      = T.src (deg a) base a := by
    refine T.src_lower _ _ _ a fun b hb => ?_
    exact tower_of_deg_le_base T s0 init base baseDeg R (by omega)
  rw [towerCoefficient, towerDeriv, if_pos ha, hfam, hsrc]
  linear_combination hnorm a ha s

/-- **All degrees through the constructed order cancel.** -/
theorem towerCoefficient_eq_zero_of_le (T : TowerData d) (s0 : Real)
    (init : Multiindex d -> Complex) (base dbase : Multiindex d -> Real -> Complex)
    (baseDeg R : Nat) (hnorm : FermiNormalizedBase T base dbase baseDeg)
    {a : Multiindex d} (ha : deg a ≤ baseDeg + R) (s : Real) :
    towerCoefficient T (tower T s0 init base baseDeg R)
      (towerDeriv T s0 init base baseDeg dbase R) a s = 0 := by
  by_cases hlow : deg a ≤ baseDeg
  · exact towerCoefficient_eq_zero_of_le_base T s0 init base dbase baseDeg R hnorm
      hlow s
  · exact towerCoefficient_eq_zero T s0 init base dbase baseDeg R hlow ha s

end LiuWang2025SemilinearWaveJetTowerRecursion
