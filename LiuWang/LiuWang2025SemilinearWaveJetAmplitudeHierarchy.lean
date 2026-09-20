import LiuWang.LiuWang2025SemilinearWaveJetTowerRecursion

/-!
# Liu-Wang semilinear wave: the amplitude jets

The source's amplitude hierarchy is a *double* recursion: over the frequency
order `k` of `a_rho = chi sum_k rho^{-k} b_k`, and, inside each order, over the
transverse total degree.  For each `k` the transverse system has exactly the
shape solved by `LiuWang2025SemilinearWaveJetTowerRecursion`, with a source that
reads

* strictly lower transverse degrees of `b_k` itself, and
* the whole of `b_{k-1}`, through `Box_g`.

`HierarchyData` records those two dependencies, with the triangularity axiom on
the first.  `amplitude` then runs the inner tower once per frequency order,
carrying the continuity of each constructed family forward so that the next
order's integrating factor is legitimate.  Nothing in `HierarchyData` is a
cancellation statement.

`amplitude_coefficient_eq_zero` is the conclusion: at every frequency order and
every transverse degree through `baseDeg + R`, the constructed family satisfies
the source's transport equation, with the derivative certified by
`amplitude_hasDerivAt`.
-/

noncomputable section

open scoped BigOperators

namespace LiuWang2025SemilinearWaveJetAmplitudeHierarchy

open LiuWang2025SemilinearWaveTransverseJet
open LiuWang2025SemilinearWaveJetTowerRecursion
open LiuWang2025SemilinearWaveJetTowerRecursion.TowerData

variable {d : Nat}

/-- The data of the source's amplitude hierarchy: one longitudinal coefficient
and one source functional, the latter reading the previous frequency order in
full and the current order only below the current transverse degree. -/
structure HierarchyData (d : Nat) where
  /-- The longitudinal transport coefficient. -/
  q : Multiindex d -> Real -> Complex
  /-- Continuity of the transport coefficient. -/
  hq : ∀ a, Continuous (q a)
  /-- The source at transverse degree `r`, reading the previous frequency order
  `prev` and the current order's lower degrees `fam`. -/
  src : Nat -> (Multiindex d -> Real -> Complex) ->
    (Multiindex d -> Real -> Complex) -> Multiindex d -> Real -> Complex
  /-- Continuity of the source. -/
  hsrc : ∀ (r : Nat) (prev fam : Multiindex d -> Real -> Complex) (a : Multiindex d),
    (∀ b, Continuous (prev b)) -> (∀ b, Continuous (fam b)) ->
      Continuous (src r prev fam a)
  /-- **Triangularity in the current order.** -/
  src_lower : ∀ (r : Nat) (prev fam fam' : Multiindex d -> Real -> Complex)
    (a : Multiindex d),
    (∀ b, deg b < r -> fam b = fam' b) -> src r prev fam a = src r prev fam' a

namespace HierarchyData

variable (H : HierarchyData d)

/-- One frequency order of the hierarchy, as a triangular longitudinal
system. -/
def toTower (prev : Multiindex d -> Real -> Complex)
    (hprev : ∀ b, Continuous (prev b)) : TowerData d where
  q := H.q
  hq := H.hq
  src := fun r fam => H.src r prev fam
  hsrc := fun r fam a hfam => H.hsrc r prev fam a hprev hfam
  src_lower := fun r fam fam' a h => H.src_lower r prev fam fam' a h

@[simp] theorem toTower_q (prev : Multiindex d -> Real -> Complex)
    (hprev : ∀ b, Continuous (prev b)) : (H.toTower prev hprev).q = H.q := rfl

/-- **The constructed amplitude family**, carrying its own continuity so that
the next frequency order's integrating factor is legitimate. -/
def amplitudeWithCont (s0 : Real) (init : Nat -> Multiindex d -> Complex)
    (base : Nat -> Multiindex d -> Real -> Complex)
    (hbase : ∀ k a, Continuous (base k a)) (baseDeg R : Nat) :
    Nat -> { f : Multiindex d -> Real -> Complex // ∀ a, Continuous (f a) }
  | 0 =>
      ⟨tower (H.toTower (fun _ _ => 0) (fun _ => continuous_const)) s0 (init 0)
          (base 0) baseDeg R,
        tower_continuous _ s0 (init 0) (base 0) baseDeg (hbase 0) R⟩
  | k + 1 =>
      ⟨tower (H.toTower (amplitudeWithCont s0 init base hbase baseDeg R k).1
            (amplitudeWithCont s0 init base hbase baseDeg R k).2)
          s0 (init (k + 1)) (base (k + 1)) baseDeg R,
        tower_continuous _ s0 (init (k + 1)) (base (k + 1)) baseDeg
          (hbase (k + 1)) R⟩

/-- The coefficient family at frequency order `k`. -/
def amplitude (s0 : Real) (init : Nat -> Multiindex d -> Complex)
    (base : Nat -> Multiindex d -> Real -> Complex)
    (hbase : ∀ k a, Continuous (base k a)) (baseDeg R k : Nat) :
    Multiindex d -> Real -> Complex :=
  (H.amplitudeWithCont s0 init base hbase baseDeg R k).1

theorem amplitude_continuous (s0 : Real) (init : Nat -> Multiindex d -> Complex)
    (base : Nat -> Multiindex d -> Real -> Complex)
    (hbase : ∀ k a, Continuous (base k a)) (baseDeg R k : Nat) :
    ∀ a, Continuous (H.amplitude s0 init base hbase baseDeg R k a) :=
  (H.amplitudeWithCont s0 init base hbase baseDeg R k).2

/-- The previous frequency order seen by order `k`. -/
def previous (s0 : Real) (init : Nat -> Multiindex d -> Complex)
    (base : Nat -> Multiindex d -> Real -> Complex)
    (hbase : ∀ k a, Continuous (base k a)) (baseDeg R : Nat) :
    Nat -> Multiindex d -> Real -> Complex
  | 0 => fun _ _ => 0
  | k + 1 => H.amplitude s0 init base hbase baseDeg R k

theorem previous_continuous (s0 : Real) (init : Nat -> Multiindex d -> Complex)
    (base : Nat -> Multiindex d -> Real -> Complex)
    (hbase : ∀ k a, Continuous (base k a)) (baseDeg R : Nat) :
    ∀ k b, Continuous (H.previous s0 init base hbase baseDeg R k b) := by
  intro k
  cases k with
  | zero => intro b; exact continuous_const
  | succ k => exact H.amplitude_continuous s0 init base hbase baseDeg R k

/-- Order `k` really is the tower built over order `k - 1`. -/
theorem amplitude_eq_tower (s0 : Real) (init : Nat -> Multiindex d -> Complex)
    (base : Nat -> Multiindex d -> Real -> Complex)
    (hbase : ∀ k a, Continuous (base k a)) (baseDeg R k : Nat) :
    H.amplitude s0 init base hbase baseDeg R k
      = tower (H.toTower (H.previous s0 init base hbase baseDeg R k)
            (H.previous_continuous s0 init base hbase baseDeg R k))
          s0 (init k) (base k) baseDeg R := by
  cases k with
  | zero => rfl
  | succ k => rfl

/-- The longitudinal derivative of the constructed amplitude family, itself
constructed. -/
def amplitudeDeriv (s0 : Real) (init : Nat -> Multiindex d -> Complex)
    (base : Nat -> Multiindex d -> Real -> Complex)
    (hbase : ∀ k a, Continuous (base k a))
    (dbase : Nat -> Multiindex d -> Real -> Complex) (baseDeg R k : Nat) :
    Multiindex d -> Real -> Complex :=
  towerDeriv (H.toTower (H.previous s0 init base hbase baseDeg R k)
      (H.previous_continuous s0 init base hbase baseDeg R k))
    s0 (init k) (base k) baseDeg (dbase k) R

/-- **The constructed derivative really is the derivative**, at every frequency
order and every transverse multi-index. -/
theorem amplitude_hasDerivAt (s0 : Real) (init : Nat -> Multiindex d -> Complex)
    (base : Nat -> Multiindex d -> Real -> Complex)
    (hbase : ∀ k a, Continuous (base k a))
    (dbase : Nat -> Multiindex d -> Real -> Complex)
    (hdbase : ∀ k b u, HasDerivAt (base k b) (dbase k b u) u)
    (baseDeg R k : Nat) (b : Multiindex d) (u : Real) :
    HasDerivAt (H.amplitude s0 init base hbase baseDeg R k b)
      (H.amplitudeDeriv s0 init base hbase dbase baseDeg R k b u) u := by
  rw [amplitude_eq_tower, amplitudeDeriv]
  exact towerDeriv_hasDerivAt _ s0 (init k) (base k) baseDeg (hbase k) (dbase k)
    (hdbase k) R b u

/-- **Every constructed amplitude coefficient satisfies the source's transport
equation.**  At frequency order `k` and transverse degree at most
`baseDeg + R`, the jet-level transport expression vanishes: the prescribed
degrees by the Fermi normalization of the chart, the constructed degrees by the
recursion. -/
theorem amplitude_coefficient_eq_zero (s0 : Real)
    (init : Nat -> Multiindex d -> Complex)
    (base : Nat -> Multiindex d -> Real -> Complex)
    (hbase : ∀ k a, Continuous (base k a))
    (dbase : Nat -> Multiindex d -> Real -> Complex)
    (baseDeg R k : Nat)
    (hnorm : FermiNormalizedBase
      (H.toTower (H.previous s0 init base hbase baseDeg R k)
        (H.previous_continuous s0 init base hbase baseDeg R k))
      (base k) (dbase k) baseDeg)
    {a : Multiindex d} (ha : deg a ≤ baseDeg + R) (s : Real) :
    towerCoefficient
        (H.toTower (H.previous s0 init base hbase baseDeg R k)
          (H.previous_continuous s0 init base hbase baseDeg R k))
        (H.amplitude s0 init base hbase baseDeg R k)
        (H.amplitudeDeriv s0 init base hbase dbase baseDeg R k) a s = 0 := by
  rw [amplitude_eq_tower, amplitudeDeriv]
  exact towerCoefficient_eq_zero_of_le _ s0 (init k) (base k) (dbase k) baseDeg R
    hnorm ha s

end HierarchyData

end LiuWang2025SemilinearWaveJetAmplitudeHierarchy
