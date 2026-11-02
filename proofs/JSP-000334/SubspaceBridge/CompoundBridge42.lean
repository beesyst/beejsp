import SubspaceBridge.OriginalPlaneTransport3
import Mathlib.LinearAlgebra.ExteriorPower.Pairing
import Mathlib.NumberTheory.Padics.PadicNorm
open scoped BigOperators Matrix
namespace CompoundFeasibility

def lo : Fin 6 → Fin 4 := ![0,0,0,1,1,2]
def hi : Fin 6 → Fin 4 := ![1,2,3,2,3,3]
def wedge {R : Type*} [CommRing R] (x y : Fin 4 → R) : Fin 6 → R :=
  fun s => x (lo s) * y (hi s) - x (hi s) * y (lo s)
def compound {R : Type*} [CommRing R] (A : Matrix (Fin 4) (Fin 4) R) : Matrix (Fin 6) (Fin 6) R :=
  fun s t => A (lo s) (lo t) * A (hi s) (hi t) - A (lo s) (hi t) * A (hi s) (lo t)

theorem wedge_transform {R : Type*} [CommRing R] (A : Matrix (Fin 4) (Fin 4) R)
    (x y : Fin 4 → R) : compound A *ᵥ wedge x y = wedge (A *ᵥ x) (A *ᵥ y) := by
  ext s
  fin_cases s <;> simp [compound,wedge,lo,hi,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> ring

theorem compound_mul {R : Type*} [CommRing R] (A B : Matrix (Fin 4) (Fin 4) R) :
    compound (A * B) = compound A * compound B := by
  ext s t
  fin_cases s <;> fin_cases t <;>
    simp [compound,lo,hi,Matrix.mul_apply,Fin.sum_univ_succ] <;> ring

theorem wedge_integer_cast (x y : Fin 4 → ℤ) :
    (fun s => (wedge (R := ℤ) x y s : ℚ)) = wedge (fun i => (x i : ℚ)) (fun i => (y i : ℚ)) := by
  ext s
  simp [wedge]

theorem compound_dimension : Module.finrank ℚ (Fin 6 → ℚ) = Nat.choose 4 2 := by norm_num [Nat.choose]


theorem compound_one {R : Type*} [CommRing R] :
    compound (1 : Matrix (Fin 4) (Fin 4) R) = (1 : Matrix (Fin 6) (Fin 6) R) := by
  have entry {n : ℕ} (i j : Fin n) :
      (1 : Matrix (Fin n) (Fin n) R) i j = if i.val = j.val then 1 else 0 := by
    simp only [Matrix.one_apply,Fin.ext_iff]
  ext s t
  simp only [compound,entry]
  fin_cases s <;> fin_cases t
  · change ((if (0 : ℕ) = 0 then (1 : R) else 0) * (if (1 : ℕ) = 1 then 1 else 0) -
      (if (0 : ℕ) = 1 then 1 else 0) * (if (1 : ℕ) = 0 then 1 else 0)) =
      (if (0 : ℕ) = 0 then 1 else 0)
    norm_num
  · change ((if (0 : ℕ) = 0 then (1 : R) else 0) * (if (1 : ℕ) = 2 then 1 else 0) -
      (if (0 : ℕ) = 2 then 1 else 0) * (if (1 : ℕ) = 0 then 1 else 0)) =
      (if (0 : ℕ) = 1 then 1 else 0)
    norm_num
  · change ((if (0 : ℕ) = 0 then (1 : R) else 0) * (if (1 : ℕ) = 3 then 1 else 0) -
      (if (0 : ℕ) = 3 then 1 else 0) * (if (1 : ℕ) = 0 then 1 else 0)) =
      (if (0 : ℕ) = 2 then 1 else 0)
    norm_num
  · change ((if (0 : ℕ) = 1 then (1 : R) else 0) * (if (1 : ℕ) = 2 then 1 else 0) -
      (if (0 : ℕ) = 2 then 1 else 0) * (if (1 : ℕ) = 1 then 1 else 0)) =
      (if (0 : ℕ) = 3 then 1 else 0)
    norm_num
  · change ((if (0 : ℕ) = 1 then (1 : R) else 0) * (if (1 : ℕ) = 3 then 1 else 0) -
      (if (0 : ℕ) = 3 then 1 else 0) * (if (1 : ℕ) = 1 then 1 else 0)) =
      (if (0 : ℕ) = 4 then 1 else 0)
    norm_num
  · change ((if (0 : ℕ) = 2 then (1 : R) else 0) * (if (1 : ℕ) = 3 then 1 else 0) -
      (if (0 : ℕ) = 3 then 1 else 0) * (if (1 : ℕ) = 2 then 1 else 0)) =
      (if (0 : ℕ) = 5 then 1 else 0)
    norm_num
  · change ((if (0 : ℕ) = 0 then (1 : R) else 0) * (if (2 : ℕ) = 1 then 1 else 0) -
      (if (0 : ℕ) = 1 then 1 else 0) * (if (2 : ℕ) = 0 then 1 else 0)) =
      (if (1 : ℕ) = 0 then 1 else 0)
    norm_num
  · change ((if (0 : ℕ) = 0 then (1 : R) else 0) * (if (2 : ℕ) = 2 then 1 else 0) -
      (if (0 : ℕ) = 2 then 1 else 0) * (if (2 : ℕ) = 0 then 1 else 0)) =
      (if (1 : ℕ) = 1 then 1 else 0)
    norm_num
  · change ((if (0 : ℕ) = 0 then (1 : R) else 0) * (if (2 : ℕ) = 3 then 1 else 0) -
      (if (0 : ℕ) = 3 then 1 else 0) * (if (2 : ℕ) = 0 then 1 else 0)) =
      (if (1 : ℕ) = 2 then 1 else 0)
    norm_num
  · change ((if (0 : ℕ) = 1 then (1 : R) else 0) * (if (2 : ℕ) = 2 then 1 else 0) -
      (if (0 : ℕ) = 2 then 1 else 0) * (if (2 : ℕ) = 1 then 1 else 0)) =
      (if (1 : ℕ) = 3 then 1 else 0)
    norm_num
  · change ((if (0 : ℕ) = 1 then (1 : R) else 0) * (if (2 : ℕ) = 3 then 1 else 0) -
      (if (0 : ℕ) = 3 then 1 else 0) * (if (2 : ℕ) = 1 then 1 else 0)) =
      (if (1 : ℕ) = 4 then 1 else 0)
    norm_num
  · change ((if (0 : ℕ) = 2 then (1 : R) else 0) * (if (2 : ℕ) = 3 then 1 else 0) -
      (if (0 : ℕ) = 3 then 1 else 0) * (if (2 : ℕ) = 2 then 1 else 0)) =
      (if (1 : ℕ) = 5 then 1 else 0)
    norm_num
  · change ((if (0 : ℕ) = 0 then (1 : R) else 0) * (if (3 : ℕ) = 1 then 1 else 0) -
      (if (0 : ℕ) = 1 then 1 else 0) * (if (3 : ℕ) = 0 then 1 else 0)) =
      (if (2 : ℕ) = 0 then 1 else 0)
    norm_num
  · change ((if (0 : ℕ) = 0 then (1 : R) else 0) * (if (3 : ℕ) = 2 then 1 else 0) -
      (if (0 : ℕ) = 2 then 1 else 0) * (if (3 : ℕ) = 0 then 1 else 0)) =
      (if (2 : ℕ) = 1 then 1 else 0)
    norm_num
  · change ((if (0 : ℕ) = 0 then (1 : R) else 0) * (if (3 : ℕ) = 3 then 1 else 0) -
      (if (0 : ℕ) = 3 then 1 else 0) * (if (3 : ℕ) = 0 then 1 else 0)) =
      (if (2 : ℕ) = 2 then 1 else 0)
    norm_num
  · change ((if (0 : ℕ) = 1 then (1 : R) else 0) * (if (3 : ℕ) = 2 then 1 else 0) -
      (if (0 : ℕ) = 2 then 1 else 0) * (if (3 : ℕ) = 1 then 1 else 0)) =
      (if (2 : ℕ) = 3 then 1 else 0)
    norm_num
  · change ((if (0 : ℕ) = 1 then (1 : R) else 0) * (if (3 : ℕ) = 3 then 1 else 0) -
      (if (0 : ℕ) = 3 then 1 else 0) * (if (3 : ℕ) = 1 then 1 else 0)) =
      (if (2 : ℕ) = 4 then 1 else 0)
    norm_num
  · change ((if (0 : ℕ) = 2 then (1 : R) else 0) * (if (3 : ℕ) = 3 then 1 else 0) -
      (if (0 : ℕ) = 3 then 1 else 0) * (if (3 : ℕ) = 2 then 1 else 0)) =
      (if (2 : ℕ) = 5 then 1 else 0)
    norm_num
  · change ((if (1 : ℕ) = 0 then (1 : R) else 0) * (if (2 : ℕ) = 1 then 1 else 0) -
      (if (1 : ℕ) = 1 then 1 else 0) * (if (2 : ℕ) = 0 then 1 else 0)) =
      (if (3 : ℕ) = 0 then 1 else 0)
    norm_num
  · change ((if (1 : ℕ) = 0 then (1 : R) else 0) * (if (2 : ℕ) = 2 then 1 else 0) -
      (if (1 : ℕ) = 2 then 1 else 0) * (if (2 : ℕ) = 0 then 1 else 0)) =
      (if (3 : ℕ) = 1 then 1 else 0)
    norm_num
  · change ((if (1 : ℕ) = 0 then (1 : R) else 0) * (if (2 : ℕ) = 3 then 1 else 0) -
      (if (1 : ℕ) = 3 then 1 else 0) * (if (2 : ℕ) = 0 then 1 else 0)) =
      (if (3 : ℕ) = 2 then 1 else 0)
    norm_num
  · change ((if (1 : ℕ) = 1 then (1 : R) else 0) * (if (2 : ℕ) = 2 then 1 else 0) -
      (if (1 : ℕ) = 2 then 1 else 0) * (if (2 : ℕ) = 1 then 1 else 0)) =
      (if (3 : ℕ) = 3 then 1 else 0)
    norm_num
  · change ((if (1 : ℕ) = 1 then (1 : R) else 0) * (if (2 : ℕ) = 3 then 1 else 0) -
      (if (1 : ℕ) = 3 then 1 else 0) * (if (2 : ℕ) = 1 then 1 else 0)) =
      (if (3 : ℕ) = 4 then 1 else 0)
    norm_num
  · change ((if (1 : ℕ) = 2 then (1 : R) else 0) * (if (2 : ℕ) = 3 then 1 else 0) -
      (if (1 : ℕ) = 3 then 1 else 0) * (if (2 : ℕ) = 2 then 1 else 0)) =
      (if (3 : ℕ) = 5 then 1 else 0)
    norm_num
  · change ((if (1 : ℕ) = 0 then (1 : R) else 0) * (if (3 : ℕ) = 1 then 1 else 0) -
      (if (1 : ℕ) = 1 then 1 else 0) * (if (3 : ℕ) = 0 then 1 else 0)) =
      (if (4 : ℕ) = 0 then 1 else 0)
    norm_num
  · change ((if (1 : ℕ) = 0 then (1 : R) else 0) * (if (3 : ℕ) = 2 then 1 else 0) -
      (if (1 : ℕ) = 2 then 1 else 0) * (if (3 : ℕ) = 0 then 1 else 0)) =
      (if (4 : ℕ) = 1 then 1 else 0)
    norm_num
  · change ((if (1 : ℕ) = 0 then (1 : R) else 0) * (if (3 : ℕ) = 3 then 1 else 0) -
      (if (1 : ℕ) = 3 then 1 else 0) * (if (3 : ℕ) = 0 then 1 else 0)) =
      (if (4 : ℕ) = 2 then 1 else 0)
    norm_num
  · change ((if (1 : ℕ) = 1 then (1 : R) else 0) * (if (3 : ℕ) = 2 then 1 else 0) -
      (if (1 : ℕ) = 2 then 1 else 0) * (if (3 : ℕ) = 1 then 1 else 0)) =
      (if (4 : ℕ) = 3 then 1 else 0)
    norm_num
  · change ((if (1 : ℕ) = 1 then (1 : R) else 0) * (if (3 : ℕ) = 3 then 1 else 0) -
      (if (1 : ℕ) = 3 then 1 else 0) * (if (3 : ℕ) = 1 then 1 else 0)) =
      (if (4 : ℕ) = 4 then 1 else 0)
    norm_num
  · change ((if (1 : ℕ) = 2 then (1 : R) else 0) * (if (3 : ℕ) = 3 then 1 else 0) -
      (if (1 : ℕ) = 3 then 1 else 0) * (if (3 : ℕ) = 2 then 1 else 0)) =
      (if (4 : ℕ) = 5 then 1 else 0)
    norm_num
  · change ((if (2 : ℕ) = 0 then (1 : R) else 0) * (if (3 : ℕ) = 1 then 1 else 0) -
      (if (2 : ℕ) = 1 then 1 else 0) * (if (3 : ℕ) = 0 then 1 else 0)) =
      (if (5 : ℕ) = 0 then 1 else 0)
    norm_num
  · change ((if (2 : ℕ) = 0 then (1 : R) else 0) * (if (3 : ℕ) = 2 then 1 else 0) -
      (if (2 : ℕ) = 2 then 1 else 0) * (if (3 : ℕ) = 0 then 1 else 0)) =
      (if (5 : ℕ) = 1 then 1 else 0)
    norm_num
  · change ((if (2 : ℕ) = 0 then (1 : R) else 0) * (if (3 : ℕ) = 3 then 1 else 0) -
      (if (2 : ℕ) = 3 then 1 else 0) * (if (3 : ℕ) = 0 then 1 else 0)) =
      (if (5 : ℕ) = 2 then 1 else 0)
    norm_num
  · change ((if (2 : ℕ) = 1 then (1 : R) else 0) * (if (3 : ℕ) = 2 then 1 else 0) -
      (if (2 : ℕ) = 2 then 1 else 0) * (if (3 : ℕ) = 1 then 1 else 0)) =
      (if (5 : ℕ) = 3 then 1 else 0)
    norm_num
  · change ((if (2 : ℕ) = 1 then (1 : R) else 0) * (if (3 : ℕ) = 3 then 1 else 0) -
      (if (2 : ℕ) = 3 then 1 else 0) * (if (3 : ℕ) = 1 then 1 else 0)) =
      (if (5 : ℕ) = 4 then 1 else 0)
    norm_num
  · change ((if (2 : ℕ) = 2 then (1 : R) else 0) * (if (3 : ℕ) = 3 then 1 else 0) -
      (if (2 : ℕ) = 3 then 1 else 0) * (if (3 : ℕ) = 2 then 1 else 0)) =
      (if (5 : ℕ) = 5 then 1 else 0)
    norm_num

theorem compound_unit {K : Type*} [Field K] (A : Matrix (Fin 4) (Fin 4) K)
    (hA : IsUnit A) : IsUnit (compound A) := by
  obtain ⟨u,rfl⟩ := hA
  apply isUnit_iff_exists.mpr
  refine ⟨compound (↑u⁻¹),?_,?_⟩
  · rw [← compound_mul,Units.mul_inv,compound_one]
  · rw [← compound_mul,Units.inv_mul,compound_one]

theorem compound_rows_independent {K : Type*} [Field K] (A : Matrix (Fin 4) (Fin 4) K)
    (hA : IsUnit A) : LinearIndependent K (compound A).row :=
  Matrix.linearIndependent_rows_iff_isUnit.mpr (compound_unit A hA)

theorem compound_columns_independent {K : Type*} [Field K] (A : Matrix (Fin 4) (Fin 4) K)
    (hA : IsUnit A) : LinearIndependent K (compound A).col :=
  Matrix.linearIndependent_cols_iff_isUnit.mpr (compound_unit A hA)

noncomputable def normBall (p e : ℕ) [Fact p.Prime] : AddSubgroup ℚ where
  carrier := {q | padicNorm p q ≤ ((p : ℚ) ^ e)⁻¹}
  zero_mem' := by
    change padicNorm p 0 ≤ _
    rw [padicNorm.zero]
    positivity
  add_mem' hx hy := padicNorm.nonarchimedean.trans (max_le hx hy)
  neg_mem' hx := by simpa only [Set.mem_setOf_eq,padicNorm.neg] using hx

def row4 (A : Matrix (Fin 4) (Fin 4) ℚ) (i : Fin 4) : (Fin 4 → ℤ) →+ ℚ where
  toFun x := (A *ᵥ (fun j => (x j : ℚ))) i
  map_zero' := by simp [Matrix.mulVec,dotProduct]
  map_add' x y := by simp [Matrix.mulVec,dotProduct,mul_add,Finset.sum_add_distrib]

def row6 (A : Matrix (Fin 6) (Fin 6) ℚ) (i : Fin 6) : (Fin 6 → ℤ) →+ ℚ where
  toFun x := (A *ᵥ (fun j => (x j : ℚ))) i
  map_zero' := by simp [Matrix.mulVec,dotProduct]
  map_add' x y := by simp [Matrix.mulVec,dotProduct,mul_add,Finset.sum_add_distrib]

noncomputable def lattice4 (p : ℕ) [Fact p.Prime] (A : Matrix (Fin 4) (Fin 4) ℚ)
    (e : Fin 4 → ℕ) : AddSubgroup (Fin 4 → ℤ) :=
  ⨅ i, (normBall p (e i)).comap (row4 A i)

noncomputable def lattice6 (p : ℕ) [Fact p.Prime] (A : Matrix (Fin 4) (Fin 4) ℚ)
    (e : Fin 4 → ℕ) : AddSubgroup (Fin 6 → ℤ) :=
  ⨅ s, (normBall p (e (lo s) + e (hi s))).comap (row6 (compound A) s)

theorem wedge_lattice (p : ℕ) [Fact p.Prime] (A : Matrix (Fin 4) (Fin 4) ℚ)
    (e : Fin 4 → ℕ) (x y : Fin 4 → ℤ) (hx : x ∈ lattice4 p A e) (hy : y ∈ lattice4 p A e) :
    wedge x y ∈ lattice6 p A e := by
  simp only [lattice4,AddSubgroup.mem_iInf,AddSubgroup.mem_comap] at hx hy
  simp only [lattice6,AddSubgroup.mem_iInf,AddSubgroup.mem_comap]
  change ∀ i, padicNorm p ((A *ᵥ (fun j => (x j : ℚ))) i) ≤ ((p : ℚ) ^ e i)⁻¹ at hx
  change ∀ i, padicNorm p ((A *ᵥ (fun j => (y j : ℚ))) i) ≤ ((p : ℚ) ^ e i)⁻¹ at hy
  change ∀ s, padicNorm p ((compound A *ᵥ (fun j => (wedge (R := ℤ) x y j : ℚ))) s) ≤
    ((p : ℚ) ^ (e (lo s) + e (hi s)))⁻¹
  rw [wedge_integer_cast,wedge_transform]
  intro s
  have hpos (i : Fin 4) : 0 ≤ ((p : ℚ) ^ e i)⁻¹ := inv_nonneg.mpr (pow_nonneg (Nat.cast_nonneg p) _)
  have h₁ := mul_le_mul (hx (lo s)) (hy (hi s)) (padicNorm.nonneg _) (hpos _)
  have h₂ := mul_le_mul (hx (hi s)) (hy (lo s)) (padicNorm.nonneg _) (hpos _)
  change padicNorm p (_ - _) ≤ _
  apply padicNorm.sub.trans
  rw [padicNorm.mul,padicNorm.mul]
  apply max_le
  · simpa only [pow_add,mul_inv] using h₁
  · simpa only [pow_add,mul_inv,mul_comm] using h₂

noncomputable def sourceLattice4 (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (e₂ e₃ : Fin 4 → ℕ) : AddSubgroup (Fin 4 → ℤ) := lattice4 2 A₂ e₂ ⊓ lattice4 3 A₃ e₃

noncomputable def sourceLattice6 (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (e₂ e₃ : Fin 4 → ℕ) : AddSubgroup (Fin 6 → ℤ) := lattice6 2 A₂ e₂ ⊓ lattice6 3 A₃ e₃

theorem source_wedge_mem (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) (e₂ e₃ : Fin 4 → ℕ)
    (x y : sourceLattice4 A₂ A₃ e₂ e₃) :
    wedge (x : Fin 4 → ℤ) (y : Fin 4 → ℤ) ∈ sourceLattice6 A₂ A₃ e₂ e₃ :=
  ⟨wedge_lattice 2 A₂ e₂ x y x.property.1 y.property.1,
    wedge_lattice 3 A₃ e₃ x y x.property.2 y.property.2⟩
def compoundFrame (u : Fin 4 → Fin 4 → ℤ) : Fin 6 → Fin 6 → ℤ :=
  fun s => wedge (u (lo s)) (u (hi s))

theorem compoundFrame_cast {R : Type*} [CommRing R] (u : Fin 4 → Fin 4 → ℤ) :
    (fun s t => (compoundFrame u s t : R)) =
      compound (Matrix.map (u : Matrix (Fin 4) (Fin 4) ℤ) (Int.castRingHom R)) := by
  ext s t
  simp [compoundFrame,wedge,compound]

theorem integral_frame_rational_independent (u : Fin 4 → Fin 4 → ℤ)
    (hu : LinearIndependent ℝ (fun j => fun i => (u j i : ℝ))) :
    LinearIndependent ℚ (fun j => fun i => (u j i : ℚ)) := by
  let U : Matrix (Fin 4) (Fin 4) ℤ := u
  let M := U.map (Int.castRingHom ℝ)
  have hM : M.det ≠ 0 := isUnit_iff_ne_zero.mp
    ((Matrix.isUnit_iff_isUnit_det M).mp (Matrix.linearIndependent_rows_iff_isUnit.mp hu))
  have hdZ : U.det ≠ 0 := by
    intro he
    apply hM
    rw [show M.det = (U.det : ℝ) from ((Int.castRingHom ℝ).map_det _).symm,he,Int.cast_zero]
  have hdQ : (U.map (Int.castRingHom ℚ)).det ≠ 0 := by
    rw [show (U.map (Int.castRingHom ℚ)).det = (U.det : ℚ) from ((Int.castRingHom ℚ).map_det _).symm]
    exact_mod_cast hdZ
  exact Matrix.linearIndependent_rows_of_det_ne_zero hdQ

theorem compoundFrame_independent (u : Fin 4 → Fin 4 → ℤ)
    (hu : LinearIndependent ℝ (fun j => fun i => (u j i : ℝ))) :
    LinearIndependent ℚ (fun s => fun t => (compoundFrame u s t : ℚ)) ∧
    LinearIndependent ℝ (fun s => fun t => (compoundFrame u s t : ℝ)) := by
  constructor
  · rw [compoundFrame_cast]
    exact compound_rows_independent _ (Matrix.linearIndependent_rows_iff_isUnit.mp
      (integral_frame_rational_independent u hu))
  · rw [compoundFrame_cast]
    exact compound_rows_independent _ (Matrix.linearIndependent_rows_iff_isUnit.mp hu)

theorem arch_minor_bound (L : Matrix (Fin 4) (Fin 4) ℝ) (A : Fin 4 → ℝ)
    (hA : ∀ i, 0 < A i) (rₓ rᵧ : ℝ) (hrₓ : 0 ≤ rₓ) (hrᵧ : 0 ≤ rᵧ)
    (x y : Fin 4 → ℝ) (hx : ∀ i, |(L *ᵥ x) i| ≤ rₓ * A i)
    (hy : ∀ i, |(L *ᵥ y) i| ≤ rᵧ * A i) (s : Fin 6) :
    |(compound L *ᵥ wedge x y) s| ≤ 2 * rₓ * rᵧ * A (lo s) * A (hi s) := by
  rw [wedge_transform]
  change |_ * _ - _ * _| ≤ _
  calc
    _ ≤ |(L *ᵥ x) (lo s) * (L *ᵥ y) (hi s)| + |(L *ᵥ x) (hi s) * (L *ᵥ y) (lo s)| := abs_sub _ _
    _ = |(L *ᵥ x) (lo s)| * |(L *ᵥ y) (hi s)| + |(L *ᵥ x) (hi s)| * |(L *ᵥ y) (lo s)| := by rw [abs_mul,abs_mul]
    _ ≤ (rₓ * A (lo s)) * (rᵧ * A (hi s)) + (rₓ * A (hi s)) * (rᵧ * A (lo s)) :=
      add_le_add (mul_le_mul (hx _) (hy _) (abs_nonneg _) (mul_nonneg hrₓ (hA _).le))
        (mul_le_mul (hx _) (hy _) (abs_nonneg _) (mul_nonneg hrₓ (hA _).le))
    _ = _ := by ring

theorem ceil_pair_bounds (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Nat.ceil (a + b) ≤ Nat.ceil a + Nat.ceil b ∧
    Nat.ceil a + Nat.ceil b ≤ Nat.ceil (a + b) + 1 := by
  refine ⟨Nat.ceil_add_le a b,?_⟩
  have h₁ := Nat.ceil_lt_add_one ha
  have h₂ := Nat.ceil_lt_add_one hb
  have h₃ : a + b ≤ (Nat.ceil (a + b) : ℝ) := Nat.le_ceil _
  have hh : (Nat.ceil a : ℝ) + (Nat.ceil b : ℝ) < (Nat.ceil (a + b) : ℝ) + 2 := by linarith
  have hn : Nat.ceil a + Nat.ceil b < Nat.ceil (a + b) + 2 := by exact_mod_cast hh
  omega

theorem ceil_pair_prime_powers (p : ℕ) (hp : 1 ≤ p) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    p ^ Nat.ceil (a + b) ≤ p ^ (Nat.ceil a + Nat.ceil b) ∧
    p ^ (Nat.ceil a + Nat.ceil b) ≤ p * p ^ Nat.ceil (a + b) := by
  obtain ⟨hl,hu⟩ := ceil_pair_bounds a b ha hb
  constructor
  · exact Nat.pow_le_pow_right hp hl
  · have hh := Nat.pow_le_pow_right hp hu
    simpa only [pow_succ,mul_comm] using hh
theorem lattice4_spec (p : ℕ) [Fact p.Prime] (A : Matrix (Fin 4) (Fin 4) ℚ)
    (e : Fin 4 → ℕ) (x : Fin 4 → ℤ) : x ∈ lattice4 p A e ↔
    ∀ i, padicNorm p ((A *ᵥ (fun j => (x j : ℚ))) i) ≤ (p : ℚ) ^ (-(e i : ℤ)) := by
  simp only [lattice4,AddSubgroup.mem_iInf,AddSubgroup.mem_comap]
  change (∀ i, padicNorm p ((A *ᵥ (fun j => (x j : ℚ))) i) ≤ ((p : ℚ) ^ e i)⁻¹) ↔ _
  simp only [zpow_neg,zpow_natCast]

theorem lattice6_spec (p : ℕ) [Fact p.Prime] (A : Matrix (Fin 4) (Fin 4) ℚ)
    (e : Fin 4 → ℕ) (z : Fin 6 → ℤ) : z ∈ lattice6 p A e ↔
    ∀ s, padicNorm p ((compound A *ᵥ (fun t => (z t : ℚ))) s) ≤
      (p : ℚ) ^ (-((e (lo s) + e (hi s) : ℕ) : ℤ)) := by
  simp only [lattice6,AddSubgroup.mem_iInf,AddSubgroup.mem_comap]
  change (∀ s, padicNorm p ((compound A *ᵥ (fun t => (z t : ℚ))) s) ≤
    ((p : ℚ) ^ (e (lo s) + e (hi s)))⁻¹) ↔ _
  simp only [zpow_neg,zpow_natCast]

theorem compound_width_positive (A : Fin 4 → ℝ) (hA : ∀ i, 0 < A i) :
    ∀ s : Fin 6, 0 < A (lo s) * A (hi s) := fun s => mul_pos (hA _) (hA _)

theorem compound_width_product (A : Fin 4 → ℝ) :
    (∏ s : Fin 6, A (lo s) * A (hi s)) = (∏ i : Fin 4, A i) ^ (3 : ℕ) := by
  simp [Fin.prod_univ_succ,lo,hi]
  <;> ring

theorem compound_exponent_sum (e : Fin 4 → ℕ) :
    (∑ s : Fin 6, (e (lo s) + e (hi s))) = 3 * ∑ i : Fin 4, e i := by
  simp [Fin.sum_univ_succ,lo,hi]
  <;> ring

theorem source_compound_bridge42 (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) (e₂ e₃ : Fin 4 → ℕ)
    (u : Fin 4 → Fin 4 → ℤ) (hum : ∀ j, u j ∈ sourceLattice4 A₂ A₃ e₂ e₃)
    (hu : LinearIndependent ℝ (fun j => fun i => (u j i : ℝ)))
    (L : Matrix (Fin 4) (Fin 4) ℝ) (A r : Fin 4 → ℝ) (hA : ∀ i, 0 < A i)
    (hr : ∀ j, 0 ≤ r j)
    (harch : ∀ j i, |(L *ᵥ (fun k => (u j k : ℝ))) i| ≤ r j * A i) :
    (∀ s, compoundFrame u s ∈ sourceLattice6 A₂ A₃ e₂ e₃) ∧
    LinearIndependent ℚ (fun s => fun t => (compoundFrame u s t : ℚ)) ∧
    LinearIndependent ℝ (fun s => fun t => (compoundFrame u s t : ℝ)) ∧
    (fun s t => (compoundFrame u s t : ℚ)) = compound (Matrix.map (u : Matrix (Fin 4) (Fin 4) ℤ) (Int.castRingHom ℚ)) ∧
    (fun s t => (compoundFrame u s t : ℝ)) = compound (Matrix.map (u : Matrix (Fin 4) (Fin 4) ℤ) (Int.castRingHom ℝ)) ∧
    ∀ s t, |(compound L *ᵥ (fun q => (compoundFrame u s q : ℝ))) t| ≤
      2 * r (lo s) * r (hi s) * A (lo t) * A (hi t) := by
  obtain ⟨hq,hR⟩ := compoundFrame_independent u hu
  refine ⟨?_,hq,hR,compoundFrame_cast u,compoundFrame_cast u,?_⟩
  · intro s
    exact source_wedge_mem A₂ A₃ e₂ e₃ ⟨u (lo s),hum _⟩ ⟨u (hi s),hum _⟩
  · intro s t
    have hc : (fun q => (compoundFrame u s q : ℝ)) =
        wedge (fun i => (u (lo s) i : ℝ)) (fun i => (u (hi s) i : ℝ)) := by
      ext q
      simp [compoundFrame,wedge]
    rw [hc]
    exact arch_minor_bound L A hA (r (lo s)) (r (hi s)) (hr _) (hr _) _ _ (harch _) (harch _) t

end CompoundFeasibility
