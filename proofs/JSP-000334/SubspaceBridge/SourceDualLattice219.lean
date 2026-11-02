import SubspaceBridge.SourceSatz51Entry218
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceDualGeometry219

def pairing219 (z : Fin 10 → ℚ) (x : Fin 10 → ℤ) : ℚ := ∑ i, (x i : ℚ)*z i

def integralDual219 (G : AddSubgroup (Fin 10 → ℤ)) : Set (Fin 10 → ℚ) :=
  {z | ∀ x : G, ∃ a : ℤ, pairing219 z x = (a : ℚ)}

def scaledDual219 (G : AddSubgroup (Fin 10 → ℤ)) : Set (Fin 10 → ℚ) :=
  (fun z : Fin 10 → ℚ => (G.index : ℚ) • z) '' integralDual219 G

theorem pairing_smul219 (a : ℚ) (z : Fin 10 → ℚ) (x : Fin 10 → ℤ) :
    pairing219 (a • z) x = a*pairing219 z x := by
  simp only [pairing219,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem scaledDual_pairing219 (G : AddSubgroup (Fin 10 → ℤ)) (hD : G.index ≠ 0)
    (z : Fin 10 → ℚ) : z ∈ scaledDual219 G ↔
      ∀ x : G, ∃ a : ℤ, pairing219 z x = (G.index : ℚ)*(a : ℚ) := by
  constructor
  · rintro ⟨v,hv,rfl⟩ x
    obtain ⟨a,ha⟩ := hv x
    refine ⟨a,?_⟩
    rw [pairing_smul219,ha]
  · intro hz
    refine ⟨(G.index : ℚ)⁻¹ • z,?_,?_⟩
    · intro x
      obtain ⟨a,ha⟩ := hz x
      refine ⟨a,?_⟩
      rw [pairing_smul219]
      rw [ha,← mul_assoc,inv_mul_cancel₀ (by exact_mod_cast hD),one_mul]
    · ext i
      simp only [Pi.smul_apply,smul_eq_mul,← mul_assoc,mul_inv_cancel₀ (show (G.index : ℚ) ≠ 0 by exact_mod_cast hD),one_mul]


def dualVector219 (W : Matrix (Fin 10) (Fin 10) ℚ) (j i : Fin 10) : ℚ := W⁻¹ i j

theorem dualVector_pairing219 (W : Matrix (Fin 10) (Fin 10) ℚ) (hW : IsUnit W)
    (i j : Fin 10) : (∑ k, W i k*dualVector219 W j k) = if i=j then 1 else 0 := by
  have h := congrArg (fun M : Matrix (Fin 10) (Fin 10) ℚ => M i j)
    (Matrix.mul_nonsing_inv W ((Matrix.isUnit_iff_isUnit_det W).mp hW))
  simpa only [Matrix.mul_apply,Matrix.one_apply,dualVector219] using h

def basisDualSpan219 (G : AddSubgroup (Fin 10 → ℤ)) (c : Basis (Fin 10) ℤ G) :
    Submodule ℤ (Fin 10 → ℚ) :=
  Submodule.span ℤ (Set.range (fun j => (G.index : ℚ) •
    dualVector219 (fun j i => ((c j : Fin 10 → ℤ) i : ℚ)) j))

theorem scaledDual_integral219 (G : AddSubgroup (Fin 10 → ℤ))
    (z : Fin 10 → ℚ) (hz : z ∈ scaledDual219 G) :
    ∃ a : Fin 10 → ℤ, ∀ i, z i = (a i : ℚ) := by
  obtain ⟨v,hv,rfl⟩ := hz
  have hh (i : Fin 10) : ∃ a : ℤ, (G.index : ℚ)*v i = (a : ℚ) := by
    let x : G := ⟨G.index • Pi.single i 1,G.nsmul_index_mem _⟩
    obtain ⟨a,ha⟩ := hv x
    refine ⟨a,?_⟩
    simpa [pairing219,x,Pi.single_apply,Finset.sum_ite_eq',mul_ite,nsmul_eq_mul] using ha
  choose a ha using hh
  exact ⟨a,ha⟩

end CompoundFeasibility.SourceDualGeometry219
