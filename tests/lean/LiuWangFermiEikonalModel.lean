import LiuWang.LiuWang2025SemilinearWaveFermiEikonalModel

open Matrix
open LiuWang2025SemilinearWaveFermiEikonalJet
open LiuWang2025SemilinearWaveFermiEikonalModel

#check @modelLineJet
#check @modelFermiNormalization
#check @modelFamily
#check @modelFamily_secondJet

/-- The Fermi normalization is satisfiable for every prescribed `C` (with the
paper's structural zeros) and every `D`, including `D ≠ 0`. -/
example {iota : Type} [Fintype iota] [DecidableEq iota] (i1 : iota)
    {C D M dM : Matrix iota iota ℂ}
    (hC : ∀ i j, C i j = C j i) (hCtop : ∀ j, C i1 j = 0)
    (hM : Mᵀ = M) (w : iota → ℝ) :
    FermiNormalization
      (modelLineJet i1 hC (quadForm D (FermiPhaseLine.dir ⟨i1, M, dM, w⟩)))
      ⟨i1, M, dM, w⟩ C D :=
  modelFermiNormalization i1 hC hCtop M dM hM w

#print axioms modelLineJet
#print axioms modelFermiNormalization
#print axioms modelFamily
#print axioms modelFamily_secondJet
