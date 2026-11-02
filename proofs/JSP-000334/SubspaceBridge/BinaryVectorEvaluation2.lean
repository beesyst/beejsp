import SubspaceBridge.BinaryIntegerNonvanishing2
import SubspaceBridge.BinaryAnalyticBudget2
open scoped BigOperators Classical
namespace JSP000334

noncomputable def binaryLocalVectorValue (L : Matrix (Fin 2) (Fin 2) ℤ)
    (w : Fin 2 → ℤ) (i : Fin 2) : ℚ := ∑ j : Fin 2,(L i j : ℚ)*(w j : ℚ)

theorem binary_vector_local_evaluation {m : ℕ} (L : Matrix (Fin 2) (Fin 2) ℤ)
    (hL : (binaryLocalRationalMatrix L).det ≠ 0) (w : Fin m → Fin 2 → ℤ)
    (J : RothBlockVars2 m →₀ ℕ) (P : MvPolynomial (RothBlockVars2 m) ℤ) :
    ((MvPolynomial.eval (fun u => w u.1 u.2) (binaryDividedDerivative J P) : ℤ) : ℚ) =
      MvPolynomial.eval₂ (RingHom.id ℚ) (fun u => binaryLocalVectorValue L (w u.1) u.2)
        (binaryLocalExpansion L J P) := by
  have he : (MvPolynomial.eval₂Hom (RingHom.id ℚ) (fun u : RothBlockVars2 m => (w u.1 u.2 : ℚ))).comp
      (binaryLocalSubstitution (binaryLocalRationalMatrix L)) =
      MvPolynomial.eval₂Hom (RingHom.id ℚ) (fun u => binaryLocalVectorValue L (w u.1) u.2) := by
    apply MvPolynomial.ringHom_ext
    · intro q
      simp [binaryLocalSubstitution]
    · intro u
      simp [binaryLocalSubstitution,binaryLocalLinearChart,binaryLocalVectorValue,binaryLocalRationalMatrix]
  rw [binary_integer_eval_cast]
  have hh := congrArg (MvPolynomial.eval₂Hom (RingHom.id ℚ) (fun u : RothBlockVars2 m => (w u.1 u.2 : ℚ)))
    (binaryLocal_expansion_reconstruct L hL J P)
  rw [← RingHom.comp_apply,he] at hh
  simpa using hh.symm

theorem binary_expansion_support_card {m : ℕ} (r : Fin m → ℕ)
    (P : MvPolynomial (RothBlockVars2 m) ℤ) (hP : binaryBlockHomogeneous r P)
    (L : Matrix (Fin 2) (Fin 2) ℤ) (J : RothBlockVars2 m →₀ ℕ) :
    (binaryLocalExpansion L J P).support.card ≤ 2^(∑ h,r h) := by
  classical
  let d : Fin m → ℕ := fun h => r h-∑ i : Fin 2,J (h,i)
  let S := (binaryLocalExpansion L J P).support
  have hd (b : RothBlockVars2 m →₀ ℕ) (hb : b ∈ S) (h : Fin m) :
      b (h,0)+b (h,1)=d h := by
    simpa only [Fin.sum_univ_two] using binaryLocal_expansion_block_degree r L J P hP b
      (MvPolynomial.mem_support_iff.mp hb) h
  let f : {b // b ∈ S} → BinaryAuxCoefficients d := fun b h =>
    ⟨b.val (h,0),by have hh := hd b.val b.property h; omega⟩
  have hf : Function.Injective f := by
    intro b c he
    apply Subtype.ext
    ext ⟨h,i⟩
    have hp : b.val (h,0)=c.val (h,0) := congrArg (fun a : BinaryAuxCoefficients d => (a h).val) he
    have hb := hd b.val b.property h
    have hc := hd c.val c.property h
    have hi : i=0 ∨ i=1 := by omega
    rcases hi with rfl | rfl <;> omega
  have hcard := Fintype.card_le_of_injective f hf
  have hh : S.card ≤ 2^(∑ h,d h) := by
    simpa only [Fintype.card_coe] using hcard.trans (binary_dimension_pow_bound d)
  exact hh.trans (Nat.pow_le_pow_right (by omega) (Finset.sum_le_sum (fun h _ => Nat.sub_le _ _)))

end JSP000334
