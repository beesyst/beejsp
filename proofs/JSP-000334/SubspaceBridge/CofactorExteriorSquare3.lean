import SubspaceBridge.CofactorSourceVanishing3
import SubspaceBridge.OriginalPlaneTransport3
import Mathlib.LinearAlgebra.CrossProduct
open scoped BigOperators Matrix
namespace JSP000334
noncomputable section

theorem cofactor_compound_reverse_product3 (p mu : Fin 3 → ℝ)
    (hp : ∀ i, 0 < p i) (hm : ∀ i, 0 < mu i)
    (hpp : ∏ i, p i ≤ (216 : ℝ)^2)
    (hmp : (1 : ℝ)/6 ≤ ∏ i, mu i)
    (hf : ∀ i, mu i ≤ 2*p i) :
    ∀ i, p i / 1119744 ≤ mu i := by
  classical
  let a : Fin 3 → ℝ := fun i => mu i / p i
  have ha : ∀ i, 0 < a i := fun i => div_pos (hm i) (hp i)
  have hu (i : Fin 3) : a i ≤ 2 := (div_le_iff₀ (hp i)).mpr (by simpa [mul_comm] using hf i)
  have hP : 0 < ∏ i, p i := Finset.prod_pos (fun i _ => hp i)
  have hprod : (1 : ℝ)/279936 ≤ ∏ i, a i := by
    simp only [a,Finset.prod_div_distrib]
    apply (le_div_iff₀ hP).mpr
    nlinarith
  intro k
  have hc : (Finset.univ.erase k : Finset (Fin 3)).card = 2 := by simp
  have hother : (∏ i ∈ Finset.univ.erase k, a i) ≤ 4 := by
    calc
      _ ≤ ∏ _i ∈ Finset.univ.erase k, (2 : ℝ) :=
        Finset.prod_le_prod (fun i _ => (ha i).le) (fun i _ => hu i)
      _ = 4 := by norm_num [Finset.prod_const,hc]
  have hmul := mul_le_mul_of_nonneg_left hother (ha k).le
  rw [Finset.mul_prod_erase Finset.univ a (Finset.mem_univ k)] at hmul
  have hh : (1 : ℝ)/1119744 ≤ a k := by linarith
  have hh' := (le_div_iff₀ (hp k)).mp hh
  nlinarith

def hodgeWedge3 {R : Type*} [CommRing R] (x y : Fin 3 → R) : Fin 3 → R :=
  ![x 1*y 2-x 2*y 1,x 2*y 0-x 0*y 2,x 0*y 1-x 1*y 0]

theorem hodgeWedge3_matrix {R : Type*} [CommRing R]
    (A : Matrix (Fin 3) (Fin 3) R) (x y : Fin 3 → R) :
    hodgeWedge3 (A *ᵥ x) (A *ᵥ y) = A.adjugate.transpose *ᵥ hodgeWedge3 x y := by
  ext i
  fin_cases i <;>
    simp [hodgeWedge3,Matrix.mulVec,dotProduct,Fin.sum_univ_three,
      Matrix.adjugate_fin_three,Matrix.transpose_apply,
      Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] <;> ring

def hodgeFrame3 {R : Type*} [CommRing R] (u : Fin 3 → Fin 3 → R) : Fin 3 → Fin 3 → R :=
  ![hodgeWedge3 (u 0) (u 1),hodgeWedge3 (u 0) (u 2),hodgeWedge3 (u 1) (u 2)]

theorem hodgeFrame3_det {R : Type*} [CommRing R] (u : Matrix (Fin 3) (Fin 3) R) :
    Matrix.det (hodgeFrame3 u) = u.det^2 := by
  simp [hodgeFrame3,hodgeWedge3,Matrix.det_fin_three,
    Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]
  ring

theorem hodgeFrame3_independent {K : Type*} [Field K] (u : Fin 3 → Fin 3 → K)
    (hu : LinearIndependent K u) : LinearIndependent K (hodgeFrame3 u) := by
  apply Matrix.linearIndependent_rows_iff_isUnit.mpr
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  change IsUnit (Matrix.det (hodgeFrame3 u))
  rw [hodgeFrame3_det (u : Matrix (Fin 3) (Fin 3) K)]
  exact isUnit_iff_ne_zero.mpr (pow_ne_zero _
    (isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp
      (Matrix.linearIndependent_rows_iff_isUnit.mp hu))))

theorem hodgeWedge3_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (x y : Fin 3 → R) :
    (fun i => f (hodgeWedge3 x y i)) = hodgeWedge3 (fun i => f (x i)) (fun i => f (y i)) := by
  ext i
  fin_cases i <;> simp [hodgeWedge3,Matrix.cons_val_one,Matrix.cons_val_two]

theorem hodgeFrame3_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (u : Fin 3 → Fin 3 → R) :
    (fun j i => f (hodgeFrame3 u j i)) = hodgeFrame3 (fun j i => f (u j i)) := by
  ext j i
  fin_cases j <;> fin_cases i <;> simp [hodgeFrame3,hodgeWedge3,Matrix.cons_val_one,Matrix.cons_val_two]

def pairWeights3 (c : Fin 3 → ℝ) (i : Fin 3) : ℝ :=
  (c (i.succAbove 0)+c (i.succAbove 1))/2

theorem pairWeights3_bounds (c0 c2 c3 : Fin 3 → ℝ)
    (h0 : ∀ i, -1 ≤ c0 i ∧ c0 i ≤ 1)
    (h2 : ∀ i, -1 ≤ c2 i ∧ c2 i ≤ 0)
    (h3 : ∀ i, -1 ≤ c3 i ∧ c3 i ≤ 0)
    (hb : ∑ i, (c0 i+c2 i+c3 i) = 0) :
    (∀ i, -1 ≤ pairWeights3 c0 i ∧ pairWeights3 c0 i ≤ 1) ∧
    (∀ i, -1 ≤ pairWeights3 c2 i ∧ pairWeights3 c2 i ≤ 0) ∧
    (∀ i, -1 ≤ pairWeights3 c3 i ∧ pairWeights3 c3 i ≤ 0) ∧
    (∑ i, (pairWeights3 c0 i+pairWeights3 c2 i+pairWeights3 c3 i)) = 0 := by
  refine ⟨fun i => ?_,fun i => ?_,fun i => ?_,?_⟩
  · dsimp [pairWeights3]; constructor <;> linarith [(h0 (i.succAbove 0)).1,(h0 (i.succAbove 1)).1,(h0 (i.succAbove 0)).2,(h0 (i.succAbove 1)).2]
  · dsimp [pairWeights3]; constructor <;> linarith [(h2 (i.succAbove 0)).1,(h2 (i.succAbove 1)).1,(h2 (i.succAbove 0)).2,(h2 (i.succAbove 1)).2]
  · dsimp [pairWeights3]; constructor <;> linarith [(h3 (i.succAbove 0)).1,(h3 (i.succAbove 1)).1,(h3 (i.succAbove 0)).2,(h3 (i.succAbove 1)).2]
  · simp [pairWeights3,Fin.sum_univ_three,Fin.succAbove] at hb ⊢
    linarith

theorem pairWeights3_power (Q : ℝ) (hQ : 0 < Q) (c : Fin 3 → ℝ) (i : Fin 3) :
    (Q^2) ^ pairWeights3 c i = Q ^ (c (i.succAbove 0)+c (i.succAbove 1)) := by
  rw [← Real.rpow_natCast,← Real.rpow_mul hQ.le]
  congr 1
  dsimp [pairWeights3]
  ring

theorem hodgeWedge3_padic_bound (p : ℕ) [Fact p.Prime]
    (x y : Fin 3 → ℚ) (t : Fin 3 → ℝ) (ht : ∀ i, 0 ≤ t i)
    (hx : ∀ i, (padicNorm p (x i) : ℝ) ≤ t i)
    (hy : ∀ i, (padicNorm p (y i) : ℝ) ≤ t i) (i : Fin 3) :
    (padicNorm p (hodgeWedge3 x y i) : ℝ) ≤ t (i.succAbove 0)*t (i.succAbove 1) := by
  fin_cases i
  · simpa [hodgeWedge3,Fin.succAbove,mul_comm] using
      conditional_padic_minor_bound3 p (x 1) (y 2) (y 1) (x 2) (t 1) (t 2)
        (ht 1) (hx 1) (hy 2) (hy 1) (hx 2)
  · have h := conditional_padic_minor_bound3 p (x 0) (y 2) (y 0) (x 2) (t 0) (t 2)
        (ht 0) (hx 0) (hy 2) (hy 0) (hx 2)
    have he : hodgeWedge3 x y 1 = -(x 0*y 2-y 0*x 2) := by
      simp [hodgeWedge3]; ring
    change (padicNorm p (hodgeWedge3 x y 1) : ℝ) ≤ t 0*t 2
    rw [he,padicNorm.neg]
    simpa [Fin.succAbove] using h
  · simpa [hodgeWedge3,Fin.succAbove,mul_comm] using
      conditional_padic_minor_bound3 p (x 0) (y 1) (y 0) (x 1) (t 0) (t 1)
        (ht 0) (hx 0) (hy 1) (hy 0) (hx 1)

theorem pairWeights3_Q_squared (Q : ℝ) (hQ : 1 < Q) : 1 < Q^2 := by
  nlinarith

theorem hodgeWedge3_source_mem (k2 k3 : Fin 3) (Q : ℝ) (hQ : 1 < Q)
    (c2 c3 : Fin 3 → ℝ) (hc2 : ∀ i, c2 i ≤ 0) (hc3 : ∀ i, c3 i ≤ 0)
    (x y : qSourceLattice3 k2 k3 Q c2 c3) :
    hodgeWedge3 (x : IntegerTriple) (y : IntegerTriple) ∈
      cofactorSourceLattice3 k2 k3 (Q^2) (pairWeights3 c2) (pairWeights3 c3) := by
  have hp : 0 < Q := lt_trans zero_lt_one hQ
  have hpc (c : Fin 3 → ℝ) (hc : ∀ i, c i ≤ 0) (i : Fin 3) : pairWeights3 c i ≤ 0 := by
    dsimp [pairWeights3]; linarith [hc (i.succAbove 0),hc (i.succAbove 1)]
  apply ((cofactorSourceLattice3_spec k2 k3 (Q^2) (pairWeights3 c2) (pairWeights3 c3)
    (pairWeights3_Q_squared Q hQ) (hpc c2 hc2) (hpc c3 hc3)).1 _).mpr
  have hx := ((qSourceLattice3_spec k2 k3 Q c2 c3 hQ hc2 hc3).1 _).mp x.property
  have hy := ((qSourceLattice3_spec k2 k3 Q c2 c3 hQ hc2 hc3).1 _).mp y.property
  have hid (k : Fin 3) (i : Fin 3) :
      cofactorForms3 k i (fun j => ((hodgeWedge3 (x : IntegerTriple) (y : IntegerTriple) j : ℤ) : ℚ)) =
      hodgeWedge3 (fun j => threeCoordinateSumForms k j (fun l => ((x : IntegerTriple) l : ℚ)))
        (fun j => threeCoordinateSumForms k j (fun l => ((y : IntegerTriple) l : ℚ))) i := by
    have h := congrFun (hodgeWedge3_matrix (retainedIntegerMatrix3 k) (x : IntegerTriple) (y : IntegerTriple)) i
    have hQcast := congrArg (fun z : ℤ => (z : ℚ)) h
    change ((hodgeWedge3 (retainedIntegerMatrix3 k *ᵥ (x : IntegerTriple))
      (retainedIntegerMatrix3 k *ᵥ (y : IntegerTriple)) i : ℤ) : ℚ) =
      (((cofactorIntegerMatrix3 k *ᵥ hodgeWedge3 (x : IntegerTriple) (y : IntegerTriple)) i : ℤ) : ℚ) at hQcast
    rw [cofactorIntegerMatrix3_apply] at hQcast
    have hm := congrFun (hodgeWedge3_map (Int.castRingHom ℚ)
      (retainedIntegerMatrix3 k *ᵥ (x : IntegerTriple)) (retainedIntegerMatrix3 k *ᵥ (y : IntegerTriple))) i
    change ((hodgeWedge3 (retainedIntegerMatrix3 k *ᵥ (x : IntegerTriple))
      (retainedIntegerMatrix3 k *ᵥ (y : IntegerTriple)) i : ℤ) : ℚ) =
      hodgeWedge3 (fun j => ((retainedIntegerMatrix3 k *ᵥ (x : IntegerTriple)) j : ℚ))
        (fun j => ((retainedIntegerMatrix3 k *ᵥ (y : IntegerTriple)) j : ℚ)) i at hm
    simp only [retainedIntegerMatrix3_apply] at hm
    exact hQcast.symm.trans hm
  constructor
  · intro i
    rw [hid,pairWeights3_power Q hp,Real.rpow_add hp]
    exact hodgeWedge3_padic_bound 2 _ _ (fun i => Q^c2 i)
      (fun i => (Real.rpow_pos_of_pos hp _).le) hx.1 hy.1 i
  · intro i
    rw [hid,pairWeights3_power Q hp,Real.rpow_add hp]
    exact hodgeWedge3_padic_bound 3 _ _ (fun i => Q^c3 i)
      (fun i => (Real.rpow_pos_of_pos hp _).le) hx.2 hy.2 i

end
end JSP000334
