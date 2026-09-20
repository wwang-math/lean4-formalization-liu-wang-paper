import LiuWang.LiuWang2025SemilinearWaveJetOperators

/-!
# Liu-Wang semilinear wave: homogeneous degree blocks

At a fixed transverse degree `r` the source's eikonal equation is *not* a family
of independent scalar ODEs: the operator `4 (A M z) . grad_z` moves the
multi-index `alpha` to `alpha + e_i - e_k`, so the whole space of homogeneous
polynomials of degree `r` moves together.  That space is finite dimensional, and
this file gives it a type.

* `degreeEq d r` is the finite set of multi-indices of total degree exactly `r`;
* `DegreeIndex d r` is its coercion to a type, a `Fintype`;
* `DegreeBlock d r` is the space of complex coefficient vectors on it, a finite
  dimensional complex normed space.

`insertBlock` writes a block into a `LongJet` at degree `r`, leaving every other
degree untouched, and `restrictBlock` reads one off.  The ordinary monomial
normalization fixed in `LiuWang2025SemilinearWaveLongitudinalJet` is used
throughout; nothing is divided by `alpha!`.

The last section translates the Riccati matrix `M(s)` into ordinary monomial
coefficients of the source's `phi_2 = z^T M z`.  Off-diagonal monomials collect
*both* `M_{pq}` and `M_{qp}`, and that is proved rather than stipulated.
-/

noncomputable section

open scoped BigOperators

namespace LiuWang2025SemilinearWaveDegreeBlock

open LiuWang2025SemilinearWaveTransverseJet
open LiuWang2025SemilinearWaveLongitudinalJet
open LiuWang2025SemilinearWaveLongitudinalJet.LongJet
open LiuWang2025SemilinearWaveJetOperators

variable {d : Nat}

/-! ## The finite index set of a homogeneous degree -/

/-- The multi-indices of total degree exactly `r`. -/
def degreeEq (d r : Nat) : Finset (Multiindex d) :=
  (degreeLE d r).filter (fun a => deg a = r)

@[simp] theorem mem_degreeEq {r : Nat} {a : Multiindex d} :
    a ∈ degreeEq d r ↔ deg a = r := by
  rw [degreeEq, Finset.mem_filter, mem_degreeLE]
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨by omega, h⟩

/-- The index type of a homogeneous degree. -/
abbrev DegreeIndex (d r : Nat) := {a : Multiindex d // a ∈ degreeEq d r}

/-- The coefficient space of a homogeneous degree: finite dimensional over the
complex numbers. -/
abbrev DegreeBlock (d r : Nat) := DegreeIndex d r -> Complex

@[simp] theorem degreeIndex_deg {r : Nat} (a : DegreeIndex d r) : deg a.1 = r :=
  mem_degreeEq.1 a.2

/-- Blocks are determined by their coordinates. -/
theorem block_ext {r : Nat} {x y : DegreeBlock d r}
    (h : ∀ a : DegreeIndex d r, x a = y a) : x = y := funext h

/-! ## Passing between blocks and coefficient families -/

/-- Read a homogeneous block off a coefficient family. -/
def restrictBlock (f : Multiindex d -> Complex) (r : Nat) : DegreeBlock d r :=
  fun a => f a.1

/-- Spread a homogeneous block into a coefficient family, zero elsewhere. -/
def ofBlock {r : Nat} (x : DegreeBlock d r) : Multiindex d -> Complex :=
  fun a => if h : a ∈ degreeEq d r then x ⟨a, h⟩ else 0

@[simp] theorem ofBlock_apply {r : Nat} (x : DegreeBlock d r)
    (a : DegreeIndex d r) : ofBlock x a.1 = x a := by
  rw [ofBlock, dif_pos a.2]

@[simp] theorem ofBlock_of_deg_ne {r : Nat} (x : DegreeBlock d r)
    {a : Multiindex d} (h : deg a ≠ r) : ofBlock x a = 0 := by
  rw [ofBlock, dif_neg]
  simpa using h

@[simp] theorem restrictBlock_ofBlock {r : Nat} (x : DegreeBlock d r) :
    restrictBlock (ofBlock x) r = x := by
  funext a
  exact ofBlock_apply x a

/-! ## Writing a block into a longitudinal jet -/

/-- Replace the degree-`r` coefficients of a jet by a prescribed block, keeping
its longitudinal derivative data consistent. -/
def insertBlock (u : LongJet d) (r : Nat) (blk dblk : Real -> DegreeBlock d r)
    (h : ∀ (a : DegreeIndex d r) (s : Real),
      HasDerivAt (fun t : Real => blk t a) (dblk s a) s) : LongJet d where
  c := fun a s => if ha : a ∈ degreeEq d r then blk s ⟨a, ha⟩ else u.c a s
  dc := fun a s => if ha : a ∈ degreeEq d r then dblk s ⟨a, ha⟩ else u.dc a s
  hasDeriv := by
    intro a s
    by_cases ha : a ∈ degreeEq d r
    · simpa [ha] using h ⟨a, ha⟩ s
    · simpa [ha] using u.hasDeriv a s

/-- **Insertion touches only the chosen degree.** -/
@[simp] theorem insertBlock_c_of_deg_ne (u : LongJet d) (r : Nat)
    (blk dblk : Real -> DegreeBlock d r) (h) {a : Multiindex d} (ha : deg a ≠ r)
    (s : Real) : (insertBlock u r blk dblk h).c a s = u.c a s := by
  show (if ha' : a ∈ degreeEq d r then blk s ⟨a, ha'⟩ else u.c a s) = _
  rw [dif_neg (by simpa using ha)]

@[simp] theorem insertBlock_dc_of_deg_ne (u : LongJet d) (r : Nat)
    (blk dblk : Real -> DegreeBlock d r) (h) {a : Multiindex d} (ha : deg a ≠ r)
    (s : Real) : (insertBlock u r blk dblk h).dc a s = u.dc a s := by
  show (if ha' : a ∈ degreeEq d r then dblk s ⟨a, ha'⟩ else u.dc a s) = _
  rw [dif_neg (by simpa using ha)]

/-- ... and writes exactly the block there. -/
@[simp] theorem insertBlock_c_index (u : LongJet d) (r : Nat)
    (blk dblk : Real -> DegreeBlock d r) (h) (a : DegreeIndex d r) (s : Real) :
    (insertBlock u r blk dblk h).c a.1 s = blk s a := by
  show (if ha' : a.1 ∈ degreeEq d r then blk s ⟨a.1, ha'⟩ else u.c a.1 s) = _
  rw [dif_pos a.2]

@[simp] theorem insertBlock_dc_index (u : LongJet d) (r : Nat)
    (blk dblk : Real -> DegreeBlock d r) (h) (a : DegreeIndex d r) (s : Real) :
    (insertBlock u r blk dblk h).dc a.1 s = dblk s a := by
  show (if ha' : a.1 ∈ degreeEq d r then dblk s ⟨a.1, ha'⟩ else u.dc a.1 s) = _
  rw [dif_pos a.2]

/-- Two jets built by insertion over the same base agree away from degree `r`. -/
theorem insertBlock_agree_off (u : LongJet d) (r : Nat)
    (blk dblk blk' dblk' : Real -> DegreeBlock d r) (h h')
    {a : Multiindex d} (ha : deg a ≠ r) (s : Real) :
    (insertBlock u r blk dblk h).c a s = (insertBlock u r blk' dblk' h').c a s := by
  rw [insertBlock_c_of_deg_ne u r blk dblk h ha s,
    insertBlock_c_of_deg_ne u r blk' dblk' h' ha s]

/-! ## The Riccati matrix as ordinary monomial coefficients

The source's `phi_2 = z^T M(s) z = sum_{p,q} M_{pq} z_p z_q`.  In ordinary
monomial coordinates the multi-index `e_p + e_q` collects every pair whose
coordinate sum is that index, so an off-diagonal monomial receives `M_{pq}` and
`M_{qp}` both, while `z_p^2` receives only `M_{pp}`.
-/

/-- The degree-two monomial coefficients generated by a matrix. -/
def quadCoeff (M : Fin d -> Fin d -> Complex) (a : Multiindex d) : Complex :=
  ∑ p, ∑ q, if (Pi.single p 1 + Pi.single q 1 : Multiindex d) = a then M p q else 0

/-- **Diagonal normalization.**  `z_p^2` receives exactly `M_{pp}`. -/
theorem quadCoeff_diag (M : Fin d -> Fin d -> Complex) (p : Fin d) :
    quadCoeff M ((Pi.single p 1 : Multiindex d) + Pi.single p 1) = M p p := by
  classical
  rw [quadCoeff, Finset.sum_eq_single_of_mem p (Finset.mem_univ p)]
  · rw [Finset.sum_eq_single_of_mem p (Finset.mem_univ p)]
    · rw [if_pos rfl]
    · intro q _ hq
      refine if_neg fun hcon => hq ?_
      have hval := congrFun hcon q
      by_cases hqp : q = p
      · exact hqp
      · exfalso
        simp [hqp] at hval
  · intro u _ hu
    refine Finset.sum_eq_zero fun q _ => if_neg fun hcon => hu ?_
    have hval := congrFun hcon u
    by_cases hup : u = p
    · exact hup
    · exfalso
      simp [hup] at hval

/-- **Off-diagonal normalization.**  `z_p z_q` with `p /= q` receives both
`M_{pq}` and `M_{qp}`. -/
theorem quadCoeff_offDiag (M : Fin d -> Fin d -> Complex) {p q : Fin d}
    (hpq : p ≠ q) :
    quadCoeff M ((Pi.single p 1 : Multiindex d) + Pi.single q 1)
      = M p q + M q p := by
  classical
  have hkey : ∀ u v : Fin d,
      ((Pi.single u 1 : Multiindex d) + Pi.single v 1
        = (Pi.single p 1 : Multiindex d) + Pi.single q 1)
      ↔ ((u = p ∧ v = q) ∨ (u = q ∧ v = p)) := by
    intro u v
    constructor
    · intro hcon
      have hu := congrFun hcon u
      have hv := congrFun hcon v
      have hp := congrFun hcon p
      have hq := congrFun hcon q
      by_cases hup : u = p
      · left
        refine ⟨hup, ?_⟩
        subst hup
        by_contra hvq
        simp [Ne.symm hpq, Ne.symm hvq] at hq
      · right
        have huq : u = q := by
          by_contra huq
          simp [hup, huq] at hu
        refine ⟨huq, ?_⟩
        subst huq
        by_contra hvp
        simp [hpq, Ne.symm hvp] at hp
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · rfl
      · exact add_comm _ _
  rw [quadCoeff]
  rw [Finset.sum_eq_add_of_mem p q (Finset.mem_univ p) (Finset.mem_univ q) hpq ?_]
  · rw [Finset.sum_eq_single_of_mem q (Finset.mem_univ q),
      Finset.sum_eq_single_of_mem p (Finset.mem_univ p)]
    · rw [if_pos ((hkey q p).2 (Or.inr ⟨rfl, rfl⟩)), if_pos rfl]
    · intro v _ hv
      refine if_neg fun hcon => hv ?_
      rcases (hkey q v).1 hcon with ⟨h1, _⟩ | ⟨_, h2⟩
      · exact absurd h1.symm hpq
      · exact h2
    · intro v _ hv
      refine if_neg fun hcon => hv ?_
      rcases (hkey p v).1 hcon with ⟨_, h2⟩ | ⟨h1, _⟩
      · exact h2
      · exact absurd h1 hpq
  · intro u _ hu
    refine Finset.sum_eq_zero fun v _ => if_neg fun hcon => ?_
    rcases (hkey u v).1 hcon with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact hu.1 h1
    · exact hu.2 h1

/-- Insertion preserves continuity of the derivative family. -/
theorem C1_insertBlock (u : LongJet d) (r : Nat)
    (blk dblk : Real -> DegreeBlock d r)
    (h : ∀ (a : DegreeIndex d r) (s : Real),
      HasDerivAt (fun t : Real => blk t a) (dblk s a) s)
    (hu : u.C1) (hd : ∀ a : DegreeIndex d r, Continuous fun s => dblk s a) :
    (insertBlock u r blk dblk h).C1 := by
  intro a
  by_cases ha : a ∈ degreeEq d r
  · have heq : (insertBlock u r blk dblk h).dc a = fun s => dblk s ⟨a, ha⟩ := by
      funext s
      show (if ha' : a ∈ degreeEq d r then dblk s ⟨a, ha'⟩ else u.dc a s) = _
      rw [dif_pos ha]
    rw [heq]
    exact hd ⟨a, ha⟩
  · have heq : (insertBlock u r blk dblk h).dc a = u.dc a := by
      funext s
      show (if ha' : a ∈ degreeEq d r then dblk s ⟨a, ha'⟩ else u.dc a s) = _
      rw [dif_neg ha]
    rw [heq]
    exact hu a

/-- **The Riccati-derivative / `quadCoeff`-derivative correspondence.**  The
longitudinal derivative of the quadratic phase coefficients is the `quadCoeff`
of the derivative of the Riccati matrix -- so a solution of the matrix Riccati
equation really does give a differentiable degree-two phase block, with the
derivative the block equation expects. -/
theorem hasDerivAt_quadCoeff {d : Nat}
    (M M' : Real -> Fin d -> Fin d -> Complex)
    (hM : ∀ p q s, HasDerivAt (fun t => M t p q) (M' s p q) s)
    (a : Multiindex d) (s : Real) :
    HasDerivAt (fun t => quadCoeff (M t) a) (quadCoeff (M' s) a) s := by
  refine hasDerivAt_finsum _ _ s fun p => ?_
  refine hasDerivAt_finsum _ _ s fun q => ?_
  by_cases h : (Pi.single p 1 + Pi.single q 1 : Multiindex d) = a
  · simpa [h] using hM p q s
  · simpa [h] using hasDerivAt_const s (0 : Complex)

/-- **The degree-two phase built from a Riccati matrix**: `phi_2 = z^T M(s) z`
in ordinary monomial coordinates, with its certified longitudinal derivative. -/
def quadJet {d : Nat} (M M' : Real -> Fin d -> Fin d -> Complex)
    (hM : ∀ p q s, HasDerivAt (fun t => M t p q) (M' s p q) s) : LongJet d where
  c := fun a s => if deg a = 2 then quadCoeff (M s) a else 0
  dc := fun a s => if deg a = 2 then quadCoeff (M' s) a else 0
  hasDeriv := by
    intro a s
    by_cases h : deg a = 2
    · simpa [h] using hasDerivAt_quadCoeff M M' hM a s
    · simpa [h] using hasDerivAt_const s (0 : Complex)

@[simp] theorem quadJet_c {d : Nat} (M M' : Real -> Fin d -> Fin d -> Complex)
    (hM : ∀ p q s, HasDerivAt (fun t => M t p q) (M' s p q) s)
    (a : Multiindex d) (s : Real) :
    (quadJet M M' hM).c a s = if deg a = 2 then quadCoeff (M s) a else 0 := rfl

theorem continuous_quadCoeff {d : Nat} (M : Real -> Fin d -> Fin d -> Complex)
    (hM : ∀ p q, Continuous fun s => M s p q) (a : Multiindex d) :
    Continuous fun s => quadCoeff (M s) a := by
  refine continuous_finset_sum _ fun p _ => continuous_finset_sum _ fun q _ => ?_
  by_cases h : (Pi.single p 1 + Pi.single q 1 : Multiindex d) = a
  · simpa [h] using hM p q
  · simpa [h] using (continuous_const : Continuous fun _ : Real => (0 : Complex))

end LiuWang2025SemilinearWaveDegreeBlock
