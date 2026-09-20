import LiuWang.LiuWang2025SemilinearWaveFermiEikonalJet

/-!
# Liu--Wang 2025: a non-vacuous Fermi metric jet with prescribed `C` and `D`

Source: Boya Liu and Weinan Wang, *On a partial data inverse problem for the
semi-linear wave equation*, arXiv:2511.08794v1, Section 3.

`LiuWang2025SemilinearWaveFermiEikonalJet` derives the paper's Riccati
equation (3.8) from the Fermi normalization of an arbitrary `C^2` inverse
metric along a transverse line.  A reviewer is entitled to ask whether that
normalization is satisfiable at all, and with a *curved* metric -- that is,
with a nonzero `D = (1/4) d^2 g^{11}`.

This module answers that.  For any prescribed coefficient matrices `C` and `D`
satisfying only the paper's own structural conditions

* `C` symmetric with `C_{1j} = C_{j1} = 0` (the paper's `C_{11} = 0` and
  `C_{ij} = 0` for `i != j`, in particular for the distinguished index), and
* `D` symmetric,

Lean constructs a `C^2` metric line jet, verifies the whole Fermi
normalization for it, and assembles the corresponding `FermiEikonalFamily`.
Consequently the equivalence

`eikonal second jet vanishes in every direction  <->  M' + M C M + D = 0`

has content for every prescribed `C` and `D`, and in particular for `D != 0`,
where the geodesic is genuinely surrounded by curvature.
-/

noncomputable section

open scoped BigOperators
open Matrix

namespace LiuWang2025SemilinearWaveFermiEikonalModel

open LiuWang2025SemilinearWaveFermiEikonalJet

variable {iota : Type*} [DecidableEq iota]

/-- The `(z^1, z^1)` slot of the transverse block, the only one that carries
second-order `z`-dependence in the model. -/
def isTop (i1 : iota) (a b : Option iota) : Bool :=
  a.elim false fun i => b.elim false fun j => decide (i = i1 ∧ j = i1)

theorem isTop_symm (i1 : iota) (a b : Option iota) :
    isTop i1 a b = isTop i1 b a := by
  cases a with
  | none => cases b <;> simp [isTop]
  | some i =>
      cases b with
      | none => simp [isTop]
      | some j =>
          by_cases hi : i = i1 <;> by_cases hj : j = i1 <;>
            simp [isTop, hi, hj]

/-- The constant part of the model inverse metric on the geodesic. -/
def baseG (i1 : iota) (C : Matrix iota iota Complex) :
    Option iota -> Option iota -> Complex := fun a b =>
  a.elim (b.elim 0 fun j => if j = i1 then 1 else 0)
    fun i => b.elim (if i = i1 then 1 else 0) fun j => C i j / 2

theorem baseG_symm (i1 : iota) {C : Matrix iota iota Complex}
    (hC : ∀ i j, C i j = C j i) (a b : Option iota) :
    baseG i1 C a b = baseG i1 C b a := by
  cases a with
  | none => cases b <;> simp [baseG]
  | some i =>
      cases b with
      | none => simp [baseG]
      | some j => simp [baseG, hC i j]

/-- The model inverse metric restricted to the transverse line `z = t w`. -/
def modelG (i1 : iota) (C : Matrix iota iota Complex) (hess : Complex)
    (t : Real) : Option iota -> Option iota -> Complex := fun a b =>
  if isTop i1 a b then 2 * hess * (t : Complex) ^ 2 else baseG i1 C a b

/-- Its first derivative. -/
def modelG₁ (i1 : iota) (hess : Complex) (t : Real) :
    Option iota -> Option iota -> Complex := fun a b =>
  if isTop i1 a b then 4 * hess * (t : Complex) else 0

/-- Its second derivative. -/
def modelG₂ (i1 : iota) (hess : Complex) (_t : Real) :
    Option iota -> Option iota -> Complex := fun a b =>
  if isTop i1 a b then 4 * hess else 0

/-- The model is a genuine `C^2` metric line jet. -/
def modelLineJet (i1 : iota) {C : Matrix iota iota Complex}
    (hC : ∀ i j, C i j = C j i) (hess : Complex) : MetricLineJet iota where
  G := modelG i1 C hess
  G₁ := modelG₁ i1 hess
  G₂ := modelG₂ i1 hess
  symm := by
    intro t a b
    simp only [modelG, isTop_symm i1 a b, baseG_symm i1 hC a b]
  hasDerivG := by
    intro t a b
    have hid : HasDerivAt (fun y : Real => (y : Complex)) 1 t := by
      simpa using (hasDerivAt_id t).ofReal_comp
    by_cases h : isTop i1 a b = true
    · show HasDerivAt (fun s : Real =>
        if isTop i1 a b then 2 * hess * (s : Complex) ^ 2 else baseG i1 C a b)
        (modelG₁ i1 hess t a b) t
      simp only [h, if_true, modelG₁]
      have hpow := (hid.pow 2).const_mul (2 * hess)
      convert hpow using 1
      push_cast
      ring
    · show HasDerivAt (fun s : Real =>
        if isTop i1 a b then 2 * hess * (s : Complex) ^ 2 else baseG i1 C a b)
        (modelG₁ i1 hess t a b) t
      simp only [h, if_false, modelG₁, Bool.false_eq_true]
      exact hasDerivAt_const t _
  hasDerivG₁ := by
    intro t a b
    have hid : HasDerivAt (fun y : Real => (y : Complex)) 1 t := by
      simpa using (hasDerivAt_id t).ofReal_comp
    by_cases h : isTop i1 a b = true
    · show HasDerivAt (fun s : Real =>
        if isTop i1 a b then 4 * hess * (s : Complex) else 0)
        (modelG₂ i1 hess t a b) t
      simp only [h, if_true, modelG₂]
      have hlin := hid.const_mul (4 * hess)
      convert hlin using 1
      ring
    · show HasDerivAt (fun s : Real =>
        if isTop i1 a b then 4 * hess * (s : Complex) else 0)
        (modelG₂ i1 hess t a b) t
      simp only [h, if_false, modelG₂, Bool.false_eq_true]
      exact hasDerivAt_const t _

/-! ### Evaluation lemmas for the model -/

theorem modelG_top (i1 : iota) (C : Matrix iota iota Complex) (hess : Complex)
    (t : Real) :
    modelG i1 C hess t (some i1) (some i1) = 2 * hess * (t : Complex) ^ 2 := by
  simp [modelG, isTop]

theorem modelG_transverse_of_ne (i1 : iota) (C : Matrix iota iota Complex)
    (hess : Complex) (t : Real) {i j : iota} (h : ¬(i = i1 ∧ j = i1)) :
    modelG i1 C hess t (some i) (some j) = C i j / 2 := by
  simp [modelG, isTop, baseG, h]

theorem modelG_pairing (i1 : iota) (C : Matrix iota iota Complex)
    (hess : Complex) (t : Real) :
    modelG i1 C hess t none (some i1) = 1 := by
  simp [modelG, isTop, baseG]

theorem modelG₁_top (i1 : iota) (hess : Complex) (t : Real) :
    modelG₁ i1 hess t (some i1) (some i1) = 4 * hess * (t : Complex) := by
  simp [modelG₁, isTop]

theorem modelG₁_of_ne (i1 : iota) (hess : Complex) (t : Real)
    {i j : iota} (h : ¬(i = i1 ∧ j = i1)) :
    modelG₁ i1 hess t (some i) (some j) = 0 := by
  simp [modelG₁, isTop, h]

theorem modelG₂_top (i1 : iota) (hess : Complex) (t : Real) :
    modelG₂ i1 hess t (some i1) (some i1) = 4 * hess := by
  simp [modelG₂, isTop]

section FermiNormalizationSection

variable [Fintype iota]

/-- The model satisfies the whole Fermi normalization with the prescribed
`C` and `D`. -/
theorem modelFermiNormalization (i1 : iota)
    {C D : Matrix iota iota Complex}
    (hC : ∀ i j, C i j = C j i) (hCtop : ∀ j, C i1 j = 0)
    (M dM : Matrix iota iota Complex) (hM : Mᵀ = M) (w : iota -> Real) :
    FermiNormalization (modelLineJet i1 hC
        (quadForm D (FermiPhaseLine.dir ⟨i1, M, dM, w⟩)))
      ⟨i1, M, dM, w⟩ C D where
  pairingNormalized := by
    simp [modelLineJet, modelG, isTop, baseG]
  nullRow := by
    intro i
    by_cases hi : i = i1
    · rw [hi]
      show modelG i1 C _ 0 (some i1) (some i1) = 0
      rw [modelG_top]
      simp
    · show modelG i1 C _ 0 (some i1) (some i) = 0
      rw [modelG_transverse_of_ne i1 C _ 0 (fun h => hi h.2), hCtop i]
      simp
  nullRowDeriv := by
    intro i
    by_cases hi : i = i1
    · rw [hi]
      show modelG₁ i1 _ 0 (some i1) (some i1) = 0
      rw [modelG₁_top]
      simp
    · show modelG₁ i1 _ 0 (some i1) (some i) = 0
      exact modelG₁_of_ne i1 _ 0 (fun h => hi h.2)
  transverseMetric := by
    intro i j
    by_cases hij : i = i1 ∧ j = i1
    · rw [hij.1, hij.2]
      show modelG i1 C _ 0 (some i1) (some i1) = C i1 i1 / 2
      rw [modelG_top, hCtop i1]
      simp
    · show modelG i1 C _ 0 (some i) (some j) = C i j / 2
      exact modelG_transverse_of_ne i1 C _ 0 hij
  hessianOfG11 := by
    show modelG₂ i1 _ 0 (some i1) (some i1) = _
    rw [modelG₂_top]
  phaseSymmetric := hM

/-- The model family over all real transverse directions. -/
def modelFamily (i1 : iota) {C D M dM : Matrix iota iota Complex}
    (hC : ∀ i j, C i j = C j i) (hCtop : ∀ j, C i1 j = 0)
    (hMsymm : Mᵀ = M) (hdMsymm : dMᵀ = dM) (hCsymm : Cᵀ = C) (hDsymm : Dᵀ = D) :
    FermiEikonalFamily iota where
  i1 := i1
  M := M
  dM := dM
  C := C
  D := D
  line := fun w =>
    modelLineJet i1 hC (quadForm D (FermiPhaseLine.dir ⟨i1, M, dM, w⟩))
  Msymm := hMsymm
  dMsymm := hdMsymm
  Csymm := hCsymm
  Dsymm := hDsymm
  normalized := fun w => modelFermiNormalization i1 hC hCtop M dM hMsymm w

/-- **Non-vacuity of the eikonal/Riccati equivalence.**  For the model family
the transverse second jet of the eikonal symbol is exactly the paper's Riccati
expression contracted with the direction, for every prescribed `C` and `D`. -/
theorem modelFamily_secondJet (i1 : iota)
    {C D M dM : Matrix iota iota Complex}
    (hC : ∀ i j, C i j = C j i) (hCtop : ∀ j, C i1 j = 0)
    (hMsymm : Mᵀ = M) (hdMsymm : dMᵀ = dM) (hCsymm : Cᵀ = C) (hDsymm : Dᵀ = D)
    (w : iota -> Real) :
    eikonalDeriv₂
        ((modelFamily i1 hC hCtop hMsymm hdMsymm hCsymm hDsymm).line w)
        ((modelFamily i1 hC hCtop hMsymm hdMsymm hCsymm hDsymm).phaseLine w).gradJet 0
      = 4 * quadForm (dM + M * C * M + D)
          (FermiPhaseLine.dir ⟨i1, M, dM, w⟩) :=
  eikonal_secondJet_eq
    ((modelFamily i1 hC hCtop hMsymm hdMsymm hCsymm hDsymm).normalized w)

end FermiNormalizationSection

end LiuWang2025SemilinearWaveFermiEikonalModel
