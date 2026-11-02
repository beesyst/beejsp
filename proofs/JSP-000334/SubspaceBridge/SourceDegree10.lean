import SubspaceBridge.SourceBalancedAuxiliary10
open scoped BigOperators Classical
noncomputable section
namespace CompoundFeasibility.Auxiliary10.SourceBalance10
open SourceMultiblock10 SourceNormalHighIndex10 SchmidtPolynomial10

theorem source_polynomial_degrees10 {m : ℕ} (r : Fin m → ℕ)
    (P : MvPolynomial (Vars10 m) ℤ) (hhom : homogeneous10 r P) (hn : P ≠ 0) :
    (∀ h, blockDegree10 P h = r h) ∧ (∀ u, P.degreeOf u ≤ r u.1) := by
  constructor
  · exact homogeneous10_blockDegree r P hhom hn
  · intro u
    apply MvPolynomial.degreeOf_le_iff.mpr
    intro b hb
    have hs := hhom b hb u.1
    have ht := Finset.single_le_sum (f := fun j : Fin 10 => b (u.1,j))
      (fun j _ => Nat.zero_le _) (Finset.mem_univ u.2)
    simpa only [hs] using ht

end CompoundFeasibility.Auxiliary10.SourceBalance10
