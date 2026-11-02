import SubspaceBridge.CompoundBridge42
open scoped BigOperators Matrix
namespace CompoundFeasibility.Exterior3

def tripleIndex4 : Fin 4 → Fin 3 → Fin 4 := ![![0,1,2], ![0,1,3], ![0,2,3], ![1,2,3]]

def tripleWedge4 {R : Type*} [CommRing R] (x y z : Fin 4 → R) : Fin 4 → R :=
  fun s => Matrix.det (fun i j : Fin 3 => (![x,y,z] j) (tripleIndex4 s i))

def compound3Matrix4 {R : Type*} [CommRing R] (A : Matrix (Fin 4) (Fin 4) R) :
    Matrix (Fin 4) (Fin 4) R := fun s t =>
  Matrix.det (A.submatrix (tripleIndex4 s) (tripleIndex4 t))

theorem tripleWedge4_expansion {R : Type*} [CommRing R] (x y z : Fin 4 → R) (s : Fin 4) :
    tripleWedge4 x y z s =
      x (tripleIndex4 s 0) * y (tripleIndex4 s 1) * z (tripleIndex4 s 2) +
      x (tripleIndex4 s 1) * y (tripleIndex4 s 2) * z (tripleIndex4 s 0) +
      x (tripleIndex4 s 2) * y (tripleIndex4 s 0) * z (tripleIndex4 s 1) -
      x (tripleIndex4 s 2) * y (tripleIndex4 s 1) * z (tripleIndex4 s 0) -
      x (tripleIndex4 s 1) * y (tripleIndex4 s 0) * z (tripleIndex4 s 2) -
      x (tripleIndex4 s 0) * y (tripleIndex4 s 2) * z (tripleIndex4 s 1) := by
  simp [tripleWedge4,Matrix.det_fin_three]
  ring

theorem tripleWedge4_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (x y z : Fin 4 → R) :
    tripleWedge4 (fun i => f (x i)) (fun i => f (y i)) (fun i => f (z i)) =
      fun s => f (tripleWedge4 x y z s) := by
  ext s
  simp [tripleWedge4_expansion]

theorem tripleWedge4_transform {R : Type*} [CommRing R] (A : Matrix (Fin 4) (Fin 4) R)
    (x y z : Fin 4 → R) :
    compound3Matrix4 A *ᵥ tripleWedge4 x y z = tripleWedge4 (A *ᵥ x) (A *ᵥ y) (A *ᵥ z) := by
  ext s
  fin_cases s <;>
    simp [compound3Matrix4,tripleWedge4_expansion,Matrix.det_fin_three,
      tripleIndex4,Matrix.submatrix,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> ring

noncomputable def tripleLattice4 (p : ℕ) [Fact p.Prime]
    (A : Matrix (Fin 4) (Fin 4) ℚ) (e : Fin 4 → ℕ) : AddSubgroup (Fin 4 → ℤ) :=
  ⨅ s, (normBall p (e (tripleIndex4 s 0) + e (tripleIndex4 s 1) + e (tripleIndex4 s 2))).comap
    (row4 (compound3Matrix4 A) s)

theorem padic_tripleWedge4_bound (p : ℕ) [Fact p.Prime] (x y z : Fin 4 → ℚ)
    (b : Fin 4 → ℚ) (hb : ∀ i, 0 ≤ b i)
    (hx : ∀ i, padicNorm p (x i) ≤ b i) (hy : ∀ i, padicNorm p (y i) ≤ b i)
    (hz : ∀ i, padicNorm p (z i) ≤ b i) (s : Fin 4) :
    padicNorm p (tripleWedge4 x y z s) ≤
      b (tripleIndex4 s 0) * b (tripleIndex4 s 1) * b (tripleIndex4 s 2) := by
  have term (i j k : Fin 4) : padicNorm p (x i * y j * z k) ≤ b i * b j * b k := by
    rw [padicNorm.mul,padicNorm.mul]
    exact mul_le_mul (mul_le_mul (hx i) (hy j) (padicNorm.nonneg _) (hb _)) (hz k)
      (padicNorm.nonneg _) (mul_nonneg (hb _) (hb _))
  rw [tripleWedge4_expansion]
  apply padicNorm.sub.trans
  apply max_le
  · apply padicNorm.sub.trans
    apply max_le
    · apply padicNorm.sub.trans
      apply max_le
      · apply padicNorm.nonarchimedean.trans
        apply max_le
        · apply padicNorm.nonarchimedean.trans
          exact max_le (term _ _ _) (by simpa only [mul_comm,mul_left_comm,mul_assoc] using term (tripleIndex4 s 1) (tripleIndex4 s 2) (tripleIndex4 s 0))
        · simpa only [mul_comm,mul_left_comm,mul_assoc] using term (tripleIndex4 s 2) (tripleIndex4 s 0) (tripleIndex4 s 1)
      · simpa only [mul_comm,mul_left_comm,mul_assoc] using term (tripleIndex4 s 2) (tripleIndex4 s 1) (tripleIndex4 s 0)
    · simpa only [mul_comm,mul_left_comm,mul_assoc] using term (tripleIndex4 s 1) (tripleIndex4 s 0) (tripleIndex4 s 2)
  · simpa only [mul_comm,mul_left_comm,mul_assoc] using term (tripleIndex4 s 0) (tripleIndex4 s 2) (tripleIndex4 s 1)

theorem tripleWedge4_lattice (p : ℕ) [Fact p.Prime] (A : Matrix (Fin 4) (Fin 4) ℚ)
    (e : Fin 4 → ℕ) (x y z : Fin 4 → ℤ)
    (hx : x ∈ lattice4 p A e) (hy : y ∈ lattice4 p A e) (hz : z ∈ lattice4 p A e) :
    tripleWedge4 x y z ∈ tripleLattice4 p A e := by
  simp only [lattice4,AddSubgroup.mem_iInf,AddSubgroup.mem_comap] at hx hy hz
  change (∀ i, padicNorm p ((A *ᵥ (fun j => (x j : ℚ))) i) ≤ ((p : ℚ) ^ e i)⁻¹) at hx
  change (∀ i, padicNorm p ((A *ᵥ (fun j => (y j : ℚ))) i) ≤ ((p : ℚ) ^ e i)⁻¹) at hy
  change (∀ i, padicNorm p ((A *ᵥ (fun j => (z j : ℚ))) i) ≤ ((p : ℚ) ^ e i)⁻¹) at hz
  simp only [tripleLattice4,AddSubgroup.mem_iInf,AddSubgroup.mem_comap]
  change ∀ s, padicNorm p ((compound3Matrix4 A *ᵥ
    (fun j => (tripleWedge4 (R := ℤ) x y z j : ℚ))) s) ≤
      ((p : ℚ) ^ (e (tripleIndex4 s 0) + e (tripleIndex4 s 1) + e (tripleIndex4 s 2)))⁻¹
  have hc : (fun j => (tripleWedge4 (R := ℤ) x y z j : ℚ)) =
      tripleWedge4 (fun j => (x j : ℚ)) (fun j => (y j : ℚ)) (fun j => (z j : ℚ)) := by
    ext s
    simp [tripleWedge4_expansion]
  rw [hc,tripleWedge4_transform]
  intro s
  simpa only [pow_add,mul_inv] using padic_tripleWedge4_bound p _ _ _ _
    (fun i => inv_nonneg.mpr (pow_nonneg (Nat.cast_nonneg p) _)) hx hy hz s
end CompoundFeasibility.Exterior3
