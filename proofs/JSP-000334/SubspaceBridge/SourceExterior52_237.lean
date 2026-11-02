import SubspaceBridge.CompoundSourceFamily42
import SubspaceBridge.OriginalVariableGap5
import SubspaceBridge.SourceRatioLine236
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.Exterior52_237

def lo237 : Fin 10 → Fin 5 := ![0,0,0,0,1,1,1,2,2,3]
def hi237 : Fin 10 → Fin 5 := ![1,2,3,4,2,3,4,3,4,4]

theorem pair_lt237 : ∀ s, lo237 s < hi237 s := by decide

theorem pair_unique237 : ∀ s t, lo237 s = lo237 t → hi237 s = hi237 t → s = t := by decide

theorem pair_exists237 : ∀ a b : Fin 5, a < b → ∃ s, lo237 s = a ∧ hi237 s = b := by decide

def pair237 (s : Fin 10) : {a : Finset (Fin 5) // a.card = 2} :=
  ⟨{lo237 s,hi237 s},Finset.card_pair (ne_of_lt (pair_lt237 s))⟩

def wedge237 {R : Type*} [CommRing R] (x y : Fin 5 → R) : Fin 10 → R :=
  fun s => x (lo237 s)*y (hi237 s)-x (hi237 s)*y (lo237 s)

def compound237 {R : Type*} [CommRing R] (A : Matrix (Fin 5) (Fin 5) R) :
    Matrix (Fin 10) (Fin 10) R :=
  fun s t => A (lo237 s) (lo237 t)*A (hi237 s) (hi237 t)-
    A (lo237 s) (hi237 t)*A (hi237 s) (lo237 t)

theorem wedge_add_left237 {R : Type*} [CommRing R] (x y z : Fin 5 → R) :
    wedge237 (x+y) z = wedge237 x z+wedge237 y z := by
  ext s
  simp only [wedge237,Pi.add_apply]
  ring

theorem wedge_add_right237 {R : Type*} [CommRing R] (x y z : Fin 5 → R) :
    wedge237 x (y+z) = wedge237 x y+wedge237 x z := by
  ext s
  simp only [wedge237,Pi.add_apply]
  ring

theorem wedge_smul_left237 {R : Type*} [CommRing R] (a : R) (x y : Fin 5 → R) :
    wedge237 (a • x) y = a • wedge237 x y := by
  ext s
  simp only [wedge237,Pi.smul_apply,smul_eq_mul]
  ring

theorem wedge_smul_right237 {R : Type*} [CommRing R] (a : R) (x y : Fin 5 → R) :
    wedge237 x (a • y) = a • wedge237 x y := by
  ext s
  simp only [wedge237,Pi.smul_apply,smul_eq_mul]
  ring

theorem wedge_transform237 {R : Type*} [CommRing R] (A : Matrix (Fin 5) (Fin 5) R)
    (x y : Fin 5 → R) : compound237 A *ᵥ wedge237 x y = wedge237 (A *ᵥ x) (A *ᵥ y) := by
  ext s
  simp [compound237,wedge237,lo237,hi237,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
  ring

theorem compound_mul237 {R : Type*} [CommRing R] (A B : Matrix (Fin 5) (Fin 5) R) :
    compound237 (A*B) = compound237 A*compound237 B := by
  ext s t
  simp [compound237,lo237,hi237,Matrix.mul_apply,Fin.sum_univ_succ]
  ring

theorem wedge_cast237 {R : Type*} [CommRing R] (x y : Fin 5 → ℤ) :
    (fun s => (wedge237 (R := ℤ) x y s : R)) = wedge237 (fun i => (x i : R)) (fun i => (y i : R)) := by
  ext s
  simp only [wedge237,Int.cast_sub,Int.cast_mul]

theorem compound_map237 {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (A : Matrix (Fin 5) (Fin 5) R) :
    compound237 (A.map f) = (compound237 A).map f := by
  ext s t
  simp only [compound237,Matrix.map_apply,map_sub,map_mul]

theorem compound_one237 {R : Type*} [CommRing R] :
    compound237 (1 : Matrix (Fin 5) (Fin 5) R) = 1 := by
  have entry {n : ℕ} (i j : Fin n) :
      (1 : Matrix (Fin n) (Fin n) R) i j = if i.val = j.val then 1 else 0 := by
    simp only [Matrix.one_apply,Fin.ext_iff]
  ext s t
  simp only [compound237,entry]
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
  · change ((if (0 : ℕ) = 0 then (1 : R) else 0) * (if (1 : ℕ) = 4 then 1 else 0) -
      (if (0 : ℕ) = 4 then 1 else 0) * (if (1 : ℕ) = 0 then 1 else 0)) =
      (if (0 : ℕ) = 3 then 1 else 0)
    norm_num
  · change ((if (0 : ℕ) = 1 then (1 : R) else 0) * (if (1 : ℕ) = 2 then 1 else 0) -
      (if (0 : ℕ) = 2 then 1 else 0) * (if (1 : ℕ) = 1 then 1 else 0)) =
      (if (0 : ℕ) = 4 then 1 else 0)
    norm_num
  · change ((if (0 : ℕ) = 1 then (1 : R) else 0) * (if (1 : ℕ) = 3 then 1 else 0) -
      (if (0 : ℕ) = 3 then 1 else 0) * (if (1 : ℕ) = 1 then 1 else 0)) =
      (if (0 : ℕ) = 5 then 1 else 0)
    norm_num
  · change ((if (0 : ℕ) = 1 then (1 : R) else 0) * (if (1 : ℕ) = 4 then 1 else 0) -
      (if (0 : ℕ) = 4 then 1 else 0) * (if (1 : ℕ) = 1 then 1 else 0)) =
      (if (0 : ℕ) = 6 then 1 else 0)
    norm_num
  · change ((if (0 : ℕ) = 2 then (1 : R) else 0) * (if (1 : ℕ) = 3 then 1 else 0) -
      (if (0 : ℕ) = 3 then 1 else 0) * (if (1 : ℕ) = 2 then 1 else 0)) =
      (if (0 : ℕ) = 7 then 1 else 0)
    norm_num
  · change ((if (0 : ℕ) = 2 then (1 : R) else 0) * (if (1 : ℕ) = 4 then 1 else 0) -
      (if (0 : ℕ) = 4 then 1 else 0) * (if (1 : ℕ) = 2 then 1 else 0)) =
      (if (0 : ℕ) = 8 then 1 else 0)
    norm_num
  · change ((if (0 : ℕ) = 3 then (1 : R) else 0) * (if (1 : ℕ) = 4 then 1 else 0) -
      (if (0 : ℕ) = 4 then 1 else 0) * (if (1 : ℕ) = 3 then 1 else 0)) =
      (if (0 : ℕ) = 9 then 1 else 0)
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
  · change ((if (0 : ℕ) = 0 then (1 : R) else 0) * (if (2 : ℕ) = 4 then 1 else 0) -
      (if (0 : ℕ) = 4 then 1 else 0) * (if (2 : ℕ) = 0 then 1 else 0)) =
      (if (1 : ℕ) = 3 then 1 else 0)
    norm_num
  · change ((if (0 : ℕ) = 1 then (1 : R) else 0) * (if (2 : ℕ) = 2 then 1 else 0) -
      (if (0 : ℕ) = 2 then 1 else 0) * (if (2 : ℕ) = 1 then 1 else 0)) =
      (if (1 : ℕ) = 4 then 1 else 0)
    norm_num
  · change ((if (0 : ℕ) = 1 then (1 : R) else 0) * (if (2 : ℕ) = 3 then 1 else 0) -
      (if (0 : ℕ) = 3 then 1 else 0) * (if (2 : ℕ) = 1 then 1 else 0)) =
      (if (1 : ℕ) = 5 then 1 else 0)
    norm_num
  · change ((if (0 : ℕ) = 1 then (1 : R) else 0) * (if (2 : ℕ) = 4 then 1 else 0) -
      (if (0 : ℕ) = 4 then 1 else 0) * (if (2 : ℕ) = 1 then 1 else 0)) =
      (if (1 : ℕ) = 6 then 1 else 0)
    norm_num
  · change ((if (0 : ℕ) = 2 then (1 : R) else 0) * (if (2 : ℕ) = 3 then 1 else 0) -
      (if (0 : ℕ) = 3 then 1 else 0) * (if (2 : ℕ) = 2 then 1 else 0)) =
      (if (1 : ℕ) = 7 then 1 else 0)
    norm_num
  · change ((if (0 : ℕ) = 2 then (1 : R) else 0) * (if (2 : ℕ) = 4 then 1 else 0) -
      (if (0 : ℕ) = 4 then 1 else 0) * (if (2 : ℕ) = 2 then 1 else 0)) =
      (if (1 : ℕ) = 8 then 1 else 0)
    norm_num
  · change ((if (0 : ℕ) = 3 then (1 : R) else 0) * (if (2 : ℕ) = 4 then 1 else 0) -
      (if (0 : ℕ) = 4 then 1 else 0) * (if (2 : ℕ) = 3 then 1 else 0)) =
      (if (1 : ℕ) = 9 then 1 else 0)
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
  · change ((if (0 : ℕ) = 0 then (1 : R) else 0) * (if (3 : ℕ) = 4 then 1 else 0) -
      (if (0 : ℕ) = 4 then 1 else 0) * (if (3 : ℕ) = 0 then 1 else 0)) =
      (if (2 : ℕ) = 3 then 1 else 0)
    norm_num
  · change ((if (0 : ℕ) = 1 then (1 : R) else 0) * (if (3 : ℕ) = 2 then 1 else 0) -
      (if (0 : ℕ) = 2 then 1 else 0) * (if (3 : ℕ) = 1 then 1 else 0)) =
      (if (2 : ℕ) = 4 then 1 else 0)
    norm_num
  · change ((if (0 : ℕ) = 1 then (1 : R) else 0) * (if (3 : ℕ) = 3 then 1 else 0) -
      (if (0 : ℕ) = 3 then 1 else 0) * (if (3 : ℕ) = 1 then 1 else 0)) =
      (if (2 : ℕ) = 5 then 1 else 0)
    norm_num
  · change ((if (0 : ℕ) = 1 then (1 : R) else 0) * (if (3 : ℕ) = 4 then 1 else 0) -
      (if (0 : ℕ) = 4 then 1 else 0) * (if (3 : ℕ) = 1 then 1 else 0)) =
      (if (2 : ℕ) = 6 then 1 else 0)
    norm_num
  · change ((if (0 : ℕ) = 2 then (1 : R) else 0) * (if (3 : ℕ) = 3 then 1 else 0) -
      (if (0 : ℕ) = 3 then 1 else 0) * (if (3 : ℕ) = 2 then 1 else 0)) =
      (if (2 : ℕ) = 7 then 1 else 0)
    norm_num
  · change ((if (0 : ℕ) = 2 then (1 : R) else 0) * (if (3 : ℕ) = 4 then 1 else 0) -
      (if (0 : ℕ) = 4 then 1 else 0) * (if (3 : ℕ) = 2 then 1 else 0)) =
      (if (2 : ℕ) = 8 then 1 else 0)
    norm_num
  · change ((if (0 : ℕ) = 3 then (1 : R) else 0) * (if (3 : ℕ) = 4 then 1 else 0) -
      (if (0 : ℕ) = 4 then 1 else 0) * (if (3 : ℕ) = 3 then 1 else 0)) =
      (if (2 : ℕ) = 9 then 1 else 0)
    norm_num
  · change ((if (0 : ℕ) = 0 then (1 : R) else 0) * (if (4 : ℕ) = 1 then 1 else 0) -
      (if (0 : ℕ) = 1 then 1 else 0) * (if (4 : ℕ) = 0 then 1 else 0)) =
      (if (3 : ℕ) = 0 then 1 else 0)
    norm_num
  · change ((if (0 : ℕ) = 0 then (1 : R) else 0) * (if (4 : ℕ) = 2 then 1 else 0) -
      (if (0 : ℕ) = 2 then 1 else 0) * (if (4 : ℕ) = 0 then 1 else 0)) =
      (if (3 : ℕ) = 1 then 1 else 0)
    norm_num
  · change ((if (0 : ℕ) = 0 then (1 : R) else 0) * (if (4 : ℕ) = 3 then 1 else 0) -
      (if (0 : ℕ) = 3 then 1 else 0) * (if (4 : ℕ) = 0 then 1 else 0)) =
      (if (3 : ℕ) = 2 then 1 else 0)
    norm_num
  · change ((if (0 : ℕ) = 0 then (1 : R) else 0) * (if (4 : ℕ) = 4 then 1 else 0) -
      (if (0 : ℕ) = 4 then 1 else 0) * (if (4 : ℕ) = 0 then 1 else 0)) =
      (if (3 : ℕ) = 3 then 1 else 0)
    norm_num
  · change ((if (0 : ℕ) = 1 then (1 : R) else 0) * (if (4 : ℕ) = 2 then 1 else 0) -
      (if (0 : ℕ) = 2 then 1 else 0) * (if (4 : ℕ) = 1 then 1 else 0)) =
      (if (3 : ℕ) = 4 then 1 else 0)
    norm_num
  · change ((if (0 : ℕ) = 1 then (1 : R) else 0) * (if (4 : ℕ) = 3 then 1 else 0) -
      (if (0 : ℕ) = 3 then 1 else 0) * (if (4 : ℕ) = 1 then 1 else 0)) =
      (if (3 : ℕ) = 5 then 1 else 0)
    norm_num
  · change ((if (0 : ℕ) = 1 then (1 : R) else 0) * (if (4 : ℕ) = 4 then 1 else 0) -
      (if (0 : ℕ) = 4 then 1 else 0) * (if (4 : ℕ) = 1 then 1 else 0)) =
      (if (3 : ℕ) = 6 then 1 else 0)
    norm_num
  · change ((if (0 : ℕ) = 2 then (1 : R) else 0) * (if (4 : ℕ) = 3 then 1 else 0) -
      (if (0 : ℕ) = 3 then 1 else 0) * (if (4 : ℕ) = 2 then 1 else 0)) =
      (if (3 : ℕ) = 7 then 1 else 0)
    norm_num
  · change ((if (0 : ℕ) = 2 then (1 : R) else 0) * (if (4 : ℕ) = 4 then 1 else 0) -
      (if (0 : ℕ) = 4 then 1 else 0) * (if (4 : ℕ) = 2 then 1 else 0)) =
      (if (3 : ℕ) = 8 then 1 else 0)
    norm_num
  · change ((if (0 : ℕ) = 3 then (1 : R) else 0) * (if (4 : ℕ) = 4 then 1 else 0) -
      (if (0 : ℕ) = 4 then 1 else 0) * (if (4 : ℕ) = 3 then 1 else 0)) =
      (if (3 : ℕ) = 9 then 1 else 0)
    norm_num
  · change ((if (1 : ℕ) = 0 then (1 : R) else 0) * (if (2 : ℕ) = 1 then 1 else 0) -
      (if (1 : ℕ) = 1 then 1 else 0) * (if (2 : ℕ) = 0 then 1 else 0)) =
      (if (4 : ℕ) = 0 then 1 else 0)
    norm_num
  · change ((if (1 : ℕ) = 0 then (1 : R) else 0) * (if (2 : ℕ) = 2 then 1 else 0) -
      (if (1 : ℕ) = 2 then 1 else 0) * (if (2 : ℕ) = 0 then 1 else 0)) =
      (if (4 : ℕ) = 1 then 1 else 0)
    norm_num
  · change ((if (1 : ℕ) = 0 then (1 : R) else 0) * (if (2 : ℕ) = 3 then 1 else 0) -
      (if (1 : ℕ) = 3 then 1 else 0) * (if (2 : ℕ) = 0 then 1 else 0)) =
      (if (4 : ℕ) = 2 then 1 else 0)
    norm_num
  · change ((if (1 : ℕ) = 0 then (1 : R) else 0) * (if (2 : ℕ) = 4 then 1 else 0) -
      (if (1 : ℕ) = 4 then 1 else 0) * (if (2 : ℕ) = 0 then 1 else 0)) =
      (if (4 : ℕ) = 3 then 1 else 0)
    norm_num
  · change ((if (1 : ℕ) = 1 then (1 : R) else 0) * (if (2 : ℕ) = 2 then 1 else 0) -
      (if (1 : ℕ) = 2 then 1 else 0) * (if (2 : ℕ) = 1 then 1 else 0)) =
      (if (4 : ℕ) = 4 then 1 else 0)
    norm_num
  · change ((if (1 : ℕ) = 1 then (1 : R) else 0) * (if (2 : ℕ) = 3 then 1 else 0) -
      (if (1 : ℕ) = 3 then 1 else 0) * (if (2 : ℕ) = 1 then 1 else 0)) =
      (if (4 : ℕ) = 5 then 1 else 0)
    norm_num
  · change ((if (1 : ℕ) = 1 then (1 : R) else 0) * (if (2 : ℕ) = 4 then 1 else 0) -
      (if (1 : ℕ) = 4 then 1 else 0) * (if (2 : ℕ) = 1 then 1 else 0)) =
      (if (4 : ℕ) = 6 then 1 else 0)
    norm_num
  · change ((if (1 : ℕ) = 2 then (1 : R) else 0) * (if (2 : ℕ) = 3 then 1 else 0) -
      (if (1 : ℕ) = 3 then 1 else 0) * (if (2 : ℕ) = 2 then 1 else 0)) =
      (if (4 : ℕ) = 7 then 1 else 0)
    norm_num
  · change ((if (1 : ℕ) = 2 then (1 : R) else 0) * (if (2 : ℕ) = 4 then 1 else 0) -
      (if (1 : ℕ) = 4 then 1 else 0) * (if (2 : ℕ) = 2 then 1 else 0)) =
      (if (4 : ℕ) = 8 then 1 else 0)
    norm_num
  · change ((if (1 : ℕ) = 3 then (1 : R) else 0) * (if (2 : ℕ) = 4 then 1 else 0) -
      (if (1 : ℕ) = 4 then 1 else 0) * (if (2 : ℕ) = 3 then 1 else 0)) =
      (if (4 : ℕ) = 9 then 1 else 0)
    norm_num
  · change ((if (1 : ℕ) = 0 then (1 : R) else 0) * (if (3 : ℕ) = 1 then 1 else 0) -
      (if (1 : ℕ) = 1 then 1 else 0) * (if (3 : ℕ) = 0 then 1 else 0)) =
      (if (5 : ℕ) = 0 then 1 else 0)
    norm_num
  · change ((if (1 : ℕ) = 0 then (1 : R) else 0) * (if (3 : ℕ) = 2 then 1 else 0) -
      (if (1 : ℕ) = 2 then 1 else 0) * (if (3 : ℕ) = 0 then 1 else 0)) =
      (if (5 : ℕ) = 1 then 1 else 0)
    norm_num
  · change ((if (1 : ℕ) = 0 then (1 : R) else 0) * (if (3 : ℕ) = 3 then 1 else 0) -
      (if (1 : ℕ) = 3 then 1 else 0) * (if (3 : ℕ) = 0 then 1 else 0)) =
      (if (5 : ℕ) = 2 then 1 else 0)
    norm_num
  · change ((if (1 : ℕ) = 0 then (1 : R) else 0) * (if (3 : ℕ) = 4 then 1 else 0) -
      (if (1 : ℕ) = 4 then 1 else 0) * (if (3 : ℕ) = 0 then 1 else 0)) =
      (if (5 : ℕ) = 3 then 1 else 0)
    norm_num
  · change ((if (1 : ℕ) = 1 then (1 : R) else 0) * (if (3 : ℕ) = 2 then 1 else 0) -
      (if (1 : ℕ) = 2 then 1 else 0) * (if (3 : ℕ) = 1 then 1 else 0)) =
      (if (5 : ℕ) = 4 then 1 else 0)
    norm_num
  · change ((if (1 : ℕ) = 1 then (1 : R) else 0) * (if (3 : ℕ) = 3 then 1 else 0) -
      (if (1 : ℕ) = 3 then 1 else 0) * (if (3 : ℕ) = 1 then 1 else 0)) =
      (if (5 : ℕ) = 5 then 1 else 0)
    norm_num
  · change ((if (1 : ℕ) = 1 then (1 : R) else 0) * (if (3 : ℕ) = 4 then 1 else 0) -
      (if (1 : ℕ) = 4 then 1 else 0) * (if (3 : ℕ) = 1 then 1 else 0)) =
      (if (5 : ℕ) = 6 then 1 else 0)
    norm_num
  · change ((if (1 : ℕ) = 2 then (1 : R) else 0) * (if (3 : ℕ) = 3 then 1 else 0) -
      (if (1 : ℕ) = 3 then 1 else 0) * (if (3 : ℕ) = 2 then 1 else 0)) =
      (if (5 : ℕ) = 7 then 1 else 0)
    norm_num
  · change ((if (1 : ℕ) = 2 then (1 : R) else 0) * (if (3 : ℕ) = 4 then 1 else 0) -
      (if (1 : ℕ) = 4 then 1 else 0) * (if (3 : ℕ) = 2 then 1 else 0)) =
      (if (5 : ℕ) = 8 then 1 else 0)
    norm_num
  · change ((if (1 : ℕ) = 3 then (1 : R) else 0) * (if (3 : ℕ) = 4 then 1 else 0) -
      (if (1 : ℕ) = 4 then 1 else 0) * (if (3 : ℕ) = 3 then 1 else 0)) =
      (if (5 : ℕ) = 9 then 1 else 0)
    norm_num
  · change ((if (1 : ℕ) = 0 then (1 : R) else 0) * (if (4 : ℕ) = 1 then 1 else 0) -
      (if (1 : ℕ) = 1 then 1 else 0) * (if (4 : ℕ) = 0 then 1 else 0)) =
      (if (6 : ℕ) = 0 then 1 else 0)
    norm_num
  · change ((if (1 : ℕ) = 0 then (1 : R) else 0) * (if (4 : ℕ) = 2 then 1 else 0) -
      (if (1 : ℕ) = 2 then 1 else 0) * (if (4 : ℕ) = 0 then 1 else 0)) =
      (if (6 : ℕ) = 1 then 1 else 0)
    norm_num
  · change ((if (1 : ℕ) = 0 then (1 : R) else 0) * (if (4 : ℕ) = 3 then 1 else 0) -
      (if (1 : ℕ) = 3 then 1 else 0) * (if (4 : ℕ) = 0 then 1 else 0)) =
      (if (6 : ℕ) = 2 then 1 else 0)
    norm_num
  · change ((if (1 : ℕ) = 0 then (1 : R) else 0) * (if (4 : ℕ) = 4 then 1 else 0) -
      (if (1 : ℕ) = 4 then 1 else 0) * (if (4 : ℕ) = 0 then 1 else 0)) =
      (if (6 : ℕ) = 3 then 1 else 0)
    norm_num
  · change ((if (1 : ℕ) = 1 then (1 : R) else 0) * (if (4 : ℕ) = 2 then 1 else 0) -
      (if (1 : ℕ) = 2 then 1 else 0) * (if (4 : ℕ) = 1 then 1 else 0)) =
      (if (6 : ℕ) = 4 then 1 else 0)
    norm_num
  · change ((if (1 : ℕ) = 1 then (1 : R) else 0) * (if (4 : ℕ) = 3 then 1 else 0) -
      (if (1 : ℕ) = 3 then 1 else 0) * (if (4 : ℕ) = 1 then 1 else 0)) =
      (if (6 : ℕ) = 5 then 1 else 0)
    norm_num
  · change ((if (1 : ℕ) = 1 then (1 : R) else 0) * (if (4 : ℕ) = 4 then 1 else 0) -
      (if (1 : ℕ) = 4 then 1 else 0) * (if (4 : ℕ) = 1 then 1 else 0)) =
      (if (6 : ℕ) = 6 then 1 else 0)
    norm_num
  · change ((if (1 : ℕ) = 2 then (1 : R) else 0) * (if (4 : ℕ) = 3 then 1 else 0) -
      (if (1 : ℕ) = 3 then 1 else 0) * (if (4 : ℕ) = 2 then 1 else 0)) =
      (if (6 : ℕ) = 7 then 1 else 0)
    norm_num
  · change ((if (1 : ℕ) = 2 then (1 : R) else 0) * (if (4 : ℕ) = 4 then 1 else 0) -
      (if (1 : ℕ) = 4 then 1 else 0) * (if (4 : ℕ) = 2 then 1 else 0)) =
      (if (6 : ℕ) = 8 then 1 else 0)
    norm_num
  · change ((if (1 : ℕ) = 3 then (1 : R) else 0) * (if (4 : ℕ) = 4 then 1 else 0) -
      (if (1 : ℕ) = 4 then 1 else 0) * (if (4 : ℕ) = 3 then 1 else 0)) =
      (if (6 : ℕ) = 9 then 1 else 0)
    norm_num
  · change ((if (2 : ℕ) = 0 then (1 : R) else 0) * (if (3 : ℕ) = 1 then 1 else 0) -
      (if (2 : ℕ) = 1 then 1 else 0) * (if (3 : ℕ) = 0 then 1 else 0)) =
      (if (7 : ℕ) = 0 then 1 else 0)
    norm_num
  · change ((if (2 : ℕ) = 0 then (1 : R) else 0) * (if (3 : ℕ) = 2 then 1 else 0) -
      (if (2 : ℕ) = 2 then 1 else 0) * (if (3 : ℕ) = 0 then 1 else 0)) =
      (if (7 : ℕ) = 1 then 1 else 0)
    norm_num
  · change ((if (2 : ℕ) = 0 then (1 : R) else 0) * (if (3 : ℕ) = 3 then 1 else 0) -
      (if (2 : ℕ) = 3 then 1 else 0) * (if (3 : ℕ) = 0 then 1 else 0)) =
      (if (7 : ℕ) = 2 then 1 else 0)
    norm_num
  · change ((if (2 : ℕ) = 0 then (1 : R) else 0) * (if (3 : ℕ) = 4 then 1 else 0) -
      (if (2 : ℕ) = 4 then 1 else 0) * (if (3 : ℕ) = 0 then 1 else 0)) =
      (if (7 : ℕ) = 3 then 1 else 0)
    norm_num
  · change ((if (2 : ℕ) = 1 then (1 : R) else 0) * (if (3 : ℕ) = 2 then 1 else 0) -
      (if (2 : ℕ) = 2 then 1 else 0) * (if (3 : ℕ) = 1 then 1 else 0)) =
      (if (7 : ℕ) = 4 then 1 else 0)
    norm_num
  · change ((if (2 : ℕ) = 1 then (1 : R) else 0) * (if (3 : ℕ) = 3 then 1 else 0) -
      (if (2 : ℕ) = 3 then 1 else 0) * (if (3 : ℕ) = 1 then 1 else 0)) =
      (if (7 : ℕ) = 5 then 1 else 0)
    norm_num
  · change ((if (2 : ℕ) = 1 then (1 : R) else 0) * (if (3 : ℕ) = 4 then 1 else 0) -
      (if (2 : ℕ) = 4 then 1 else 0) * (if (3 : ℕ) = 1 then 1 else 0)) =
      (if (7 : ℕ) = 6 then 1 else 0)
    norm_num
  · change ((if (2 : ℕ) = 2 then (1 : R) else 0) * (if (3 : ℕ) = 3 then 1 else 0) -
      (if (2 : ℕ) = 3 then 1 else 0) * (if (3 : ℕ) = 2 then 1 else 0)) =
      (if (7 : ℕ) = 7 then 1 else 0)
    norm_num
  · change ((if (2 : ℕ) = 2 then (1 : R) else 0) * (if (3 : ℕ) = 4 then 1 else 0) -
      (if (2 : ℕ) = 4 then 1 else 0) * (if (3 : ℕ) = 2 then 1 else 0)) =
      (if (7 : ℕ) = 8 then 1 else 0)
    norm_num
  · change ((if (2 : ℕ) = 3 then (1 : R) else 0) * (if (3 : ℕ) = 4 then 1 else 0) -
      (if (2 : ℕ) = 4 then 1 else 0) * (if (3 : ℕ) = 3 then 1 else 0)) =
      (if (7 : ℕ) = 9 then 1 else 0)
    norm_num
  · change ((if (2 : ℕ) = 0 then (1 : R) else 0) * (if (4 : ℕ) = 1 then 1 else 0) -
      (if (2 : ℕ) = 1 then 1 else 0) * (if (4 : ℕ) = 0 then 1 else 0)) =
      (if (8 : ℕ) = 0 then 1 else 0)
    norm_num
  · change ((if (2 : ℕ) = 0 then (1 : R) else 0) * (if (4 : ℕ) = 2 then 1 else 0) -
      (if (2 : ℕ) = 2 then 1 else 0) * (if (4 : ℕ) = 0 then 1 else 0)) =
      (if (8 : ℕ) = 1 then 1 else 0)
    norm_num
  · change ((if (2 : ℕ) = 0 then (1 : R) else 0) * (if (4 : ℕ) = 3 then 1 else 0) -
      (if (2 : ℕ) = 3 then 1 else 0) * (if (4 : ℕ) = 0 then 1 else 0)) =
      (if (8 : ℕ) = 2 then 1 else 0)
    norm_num
  · change ((if (2 : ℕ) = 0 then (1 : R) else 0) * (if (4 : ℕ) = 4 then 1 else 0) -
      (if (2 : ℕ) = 4 then 1 else 0) * (if (4 : ℕ) = 0 then 1 else 0)) =
      (if (8 : ℕ) = 3 then 1 else 0)
    norm_num
  · change ((if (2 : ℕ) = 1 then (1 : R) else 0) * (if (4 : ℕ) = 2 then 1 else 0) -
      (if (2 : ℕ) = 2 then 1 else 0) * (if (4 : ℕ) = 1 then 1 else 0)) =
      (if (8 : ℕ) = 4 then 1 else 0)
    norm_num
  · change ((if (2 : ℕ) = 1 then (1 : R) else 0) * (if (4 : ℕ) = 3 then 1 else 0) -
      (if (2 : ℕ) = 3 then 1 else 0) * (if (4 : ℕ) = 1 then 1 else 0)) =
      (if (8 : ℕ) = 5 then 1 else 0)
    norm_num
  · change ((if (2 : ℕ) = 1 then (1 : R) else 0) * (if (4 : ℕ) = 4 then 1 else 0) -
      (if (2 : ℕ) = 4 then 1 else 0) * (if (4 : ℕ) = 1 then 1 else 0)) =
      (if (8 : ℕ) = 6 then 1 else 0)
    norm_num
  · change ((if (2 : ℕ) = 2 then (1 : R) else 0) * (if (4 : ℕ) = 3 then 1 else 0) -
      (if (2 : ℕ) = 3 then 1 else 0) * (if (4 : ℕ) = 2 then 1 else 0)) =
      (if (8 : ℕ) = 7 then 1 else 0)
    norm_num
  · change ((if (2 : ℕ) = 2 then (1 : R) else 0) * (if (4 : ℕ) = 4 then 1 else 0) -
      (if (2 : ℕ) = 4 then 1 else 0) * (if (4 : ℕ) = 2 then 1 else 0)) =
      (if (8 : ℕ) = 8 then 1 else 0)
    norm_num
  · change ((if (2 : ℕ) = 3 then (1 : R) else 0) * (if (4 : ℕ) = 4 then 1 else 0) -
      (if (2 : ℕ) = 4 then 1 else 0) * (if (4 : ℕ) = 3 then 1 else 0)) =
      (if (8 : ℕ) = 9 then 1 else 0)
    norm_num
  · change ((if (3 : ℕ) = 0 then (1 : R) else 0) * (if (4 : ℕ) = 1 then 1 else 0) -
      (if (3 : ℕ) = 1 then 1 else 0) * (if (4 : ℕ) = 0 then 1 else 0)) =
      (if (9 : ℕ) = 0 then 1 else 0)
    norm_num
  · change ((if (3 : ℕ) = 0 then (1 : R) else 0) * (if (4 : ℕ) = 2 then 1 else 0) -
      (if (3 : ℕ) = 2 then 1 else 0) * (if (4 : ℕ) = 0 then 1 else 0)) =
      (if (9 : ℕ) = 1 then 1 else 0)
    norm_num
  · change ((if (3 : ℕ) = 0 then (1 : R) else 0) * (if (4 : ℕ) = 3 then 1 else 0) -
      (if (3 : ℕ) = 3 then 1 else 0) * (if (4 : ℕ) = 0 then 1 else 0)) =
      (if (9 : ℕ) = 2 then 1 else 0)
    norm_num
  · change ((if (3 : ℕ) = 0 then (1 : R) else 0) * (if (4 : ℕ) = 4 then 1 else 0) -
      (if (3 : ℕ) = 4 then 1 else 0) * (if (4 : ℕ) = 0 then 1 else 0)) =
      (if (9 : ℕ) = 3 then 1 else 0)
    norm_num
  · change ((if (3 : ℕ) = 1 then (1 : R) else 0) * (if (4 : ℕ) = 2 then 1 else 0) -
      (if (3 : ℕ) = 2 then 1 else 0) * (if (4 : ℕ) = 1 then 1 else 0)) =
      (if (9 : ℕ) = 4 then 1 else 0)
    norm_num
  · change ((if (3 : ℕ) = 1 then (1 : R) else 0) * (if (4 : ℕ) = 3 then 1 else 0) -
      (if (3 : ℕ) = 3 then 1 else 0) * (if (4 : ℕ) = 1 then 1 else 0)) =
      (if (9 : ℕ) = 5 then 1 else 0)
    norm_num
  · change ((if (3 : ℕ) = 1 then (1 : R) else 0) * (if (4 : ℕ) = 4 then 1 else 0) -
      (if (3 : ℕ) = 4 then 1 else 0) * (if (4 : ℕ) = 1 then 1 else 0)) =
      (if (9 : ℕ) = 6 then 1 else 0)
    norm_num
  · change ((if (3 : ℕ) = 2 then (1 : R) else 0) * (if (4 : ℕ) = 3 then 1 else 0) -
      (if (3 : ℕ) = 3 then 1 else 0) * (if (4 : ℕ) = 2 then 1 else 0)) =
      (if (9 : ℕ) = 7 then 1 else 0)
    norm_num
  · change ((if (3 : ℕ) = 2 then (1 : R) else 0) * (if (4 : ℕ) = 4 then 1 else 0) -
      (if (3 : ℕ) = 4 then 1 else 0) * (if (4 : ℕ) = 2 then 1 else 0)) =
      (if (9 : ℕ) = 8 then 1 else 0)
    norm_num
  · change ((if (3 : ℕ) = 3 then (1 : R) else 0) * (if (4 : ℕ) = 4 then 1 else 0) -
      (if (3 : ℕ) = 4 then 1 else 0) * (if (4 : ℕ) = 3 then 1 else 0)) =
      (if (9 : ℕ) = 9 then 1 else 0)
    norm_num

end CompoundFeasibility.Exterior52_237
