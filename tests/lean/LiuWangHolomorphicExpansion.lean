import LiuWang.LiuWang2025SemilinearWaveHolomorphicExpansion

open LiuWang2025SemilinearWaveHolomorphicExpansion

#check @SourceNonlinearity.coeff_zero
#check @SourceNonlinearity.coeff_one
#check @SourceNonlinearity.hasSum_taylor
#check @SourceNonlinearity.hasSum_tail
#check @SourceNonlinearity.hasSum_eval
#check @SourceNonlinearity.toPointwiseExpansion
#check @certificate

/-- Conditions (i) and (ii) give the paper's displayed expansion. -/
example {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (S : SourceNonlinearity E) (z : ℂ) :
    S.coeff 0 = 0 ∧ S.coeff 1 = 0 ∧
      HasSum
        (fun k : ℕ =>
          ((Nat.factorial (k + 2) : ℂ))⁻¹ • (z ^ (k + 2) • S.coeff (k + 2)))
        (S.V z) :=
  ⟨S.coeff_zero, S.coeff_one, S.hasSum_tail z⟩

/-- Evaluation at a point of the closure of `Omega` gives the scalar
display `V(x,z) = sum_k V_k(x) z^k / k!`. -/
example {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (S : SourceNonlinearity E) (L : E →L[ℂ] ℂ) (z : ℂ) :
    HasSum (fun k : ℕ => L (S.coeff k) * z ^ k / (Nat.factorial k : ℂ))
      (L (S.V z)) :=
  S.hasSum_eval L z

/-- The recovery module's expansion packet is now constructed. -/
noncomputable example (S : SourceNonlinearity ℂ) :
    LiuWang2025SemilinearWaveHolomorphicRecovery.PointwiseExpansion :=
  S.toPointwiseExpansion

#print axioms SourceNonlinearity.hasSum_taylor
#print axioms SourceNonlinearity.hasSum_tail
#print axioms SourceNonlinearity.hasSum_eval
#print axioms SourceNonlinearity.toPointwiseExpansion
#print axioms certificate

/-! Source Subsections 4.2--4.3: the induction on the order and its closure. -/

#check @LiuWang2025SemilinearWaveHolomorphicExpansion.SourceNonlinearity.eq_of_coeff_eq_from_three
#check @LiuWang2025SemilinearWaveHolomorphicExpansion.forall_eq_of_inductive_step
#check @LiuWang2025SemilinearWaveHolomorphicExpansion.eq_of_cubic_and_inductive_step

#print axioms LiuWang2025SemilinearWaveHolomorphicExpansion.forall_eq_of_inductive_step
#print axioms LiuWang2025SemilinearWaveHolomorphicExpansion.eq_of_cubic_and_inductive_step
