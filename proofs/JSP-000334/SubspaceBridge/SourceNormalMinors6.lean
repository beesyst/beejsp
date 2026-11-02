import SubspaceBridge.SourceMixedSelection6
import Mathlib.LinearAlgebra.Matrix.AbsoluteValue
import Mathlib.Algebra.GCDMonoid.Finset
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceHeightBounds6
open SourceNormalIndex SourceNormalHeight SourceProper6 SourceMixed6

def rawNormal6 (v : Matrix (Fin 6) (Fin 6) ℤ) (i : Fin 6) : ℤ := v.adjugate i 5

theorem rawNormal6_signed_minor (v : Matrix (Fin 6) (Fin 6) ℤ) (i : Fin 6) :
    rawNormal6 v i = (-1)^(5+i.val) *
      (v.submatrix Fin.castSucc i.succAbove).det := by
  unfold rawNormal6
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
  have he : (5 : Fin 6).succAbove = Fin.castSucc := Fin.succAbove_last
  rw [he]
  congr 1 <;> norm_num

theorem rawNormal6_pairing (v : Matrix (Fin 6) (Fin 6) ℤ) (j : Fin 6) :
    (∑ i, rawNormal6 v i*v j i) = if j=5 then v.det else 0 := by
  have h := congrArg (fun B : Matrix (Fin 6) (Fin 6) ℤ => B j 5) (Matrix.mul_adjugate v)
  simpa [rawNormal6,Matrix.mul_apply,Matrix.smul_apply,Matrix.one_apply,mul_comm,mul_ite] using h

theorem rawNormal6_annihilates (v : Matrix (Fin 6) (Fin 6) ℤ) (j : Fin 5) :
    (∑ i, rawNormal6 v i*v j.castSucc i) = 0 := by
  rw [rawNormal6_pairing,if_neg]
  intro h
  have he := congrArg Fin.val h
  change j.val=5 at he
  omega

theorem rawNormal6_nonzero (v : Matrix (Fin 6) (Fin 6) ℤ)
    (hv : LinearIndependent ℚ (fun j i => (v j i : ℚ))) : rawNormal6 v ≠ 0 := by
  let u : Matrix (Fin 6) (Fin 6) ℚ := (Int.castRingHom ℚ).mapMatrix v
  have hu : u = v.map (Int.castRingHom ℚ) := by
    ext i j
    rfl
  have hli : LinearIndependent ℚ (fun j => u j) := hv
  have hd : u.det ≠ 0 := isUnit_iff_ne_zero.mp
    ((Matrix.isUnit_iff_isUnit_det _).mp (Matrix.linearIndependent_rows_iff_isUnit.mp hli))
  intro hz
  have hAdj : (Int.castRingHom ℚ).mapMatrix v.adjugate = u.adjugate :=
    (Int.castRingHom ℚ).map_adjugate v
  have hzcol (k : Fin 6) : u.adjugate k 5 = 0 := by
    have he := congrArg (fun B : Matrix (Fin 6) (Fin 6) ℚ => B k 5) hAdj
    change (v.adjugate k 5 : ℚ) = u.adjugate k 5 at he
    have hw : v.adjugate k 5 = 0 := congrFun hz k
    calc
      u.adjugate k 5 = (v.adjugate k 5 : ℚ) := he.symm
      _ = 0 := by rw [hw,Int.cast_zero]
  have hleft : (u*u.adjugate) 5 5 = 0 := by
    simp only [Matrix.mul_apply,hzcol,mul_zero,Finset.sum_const_zero]
  have hright : (u.det • (1 : Matrix (Fin 6) (Fin 6) ℚ)) 5 5 = u.det := by
    simp [Matrix.smul_apply,Matrix.one_apply]
  have hmul : u*u.adjugate = u.det • (1 : Matrix (Fin 6) (Fin 6) ℚ) :=
    Matrix.mul_adjugate u
  have he : (u*u.adjugate) 5 5 = (u.det • (1 : Matrix (Fin 6) (Fin 6) ℚ)) 5 5 :=
    congrArg (fun B : Matrix (Fin 6) (Fin 6) ℚ => B 5 5) hmul
  exact hd (hright.symm.trans (he.symm.trans hleft))


theorem primitive_minor_factor6 (v : Matrix (Fin 6) (Fin 6) ℤ)
    (hv : LinearIndependent ℚ (fun j i => (v j i : ℚ))) (M a : Fin 6 → ℤ)
    (hM : M ≠ 0) (ha : (∑ i, a i*M i)=1)
    (hann : ∀ j : Fin 5, (∑ i, M i*v j.castSucc i)=0) :
    let g : ℤ := ∑ i, a i*rawNormal6 v i
    g ≠ 0 ∧ (∀ i, rawNormal6 v i=g*M i) ∧
      ∀ d : ℤ, (∀ i, d ∣ rawNormal6 v i) ↔ d ∣ g := by
  obtain ⟨q,hq,hW⟩ := actual_normal_last_dual6 v hv (rawNormal6 v)
    (rawNormal6_nonzero v hv) (rawNormal6_annihilates v)
  obtain ⟨r,hr,hN⟩ := actual_normal_last_dual6 v hv M hM hann
  have hforms : normalForm6 (rawNormal6 v) = (q/r) • normalForm6 M := by
    rw [hN,smul_smul,div_mul_cancel₀ q hr]
    exact hW
  have hi (i : Fin 6) : (rawNormal6 v i : ℚ) = (q/r)*(M i : ℚ) := by
    have h := congrArg (fun f : Module.Dual ℚ (Fin 6 → ℚ) => f (Pi.single i 1)) hforms
    simpa [normalForm6,Pi.single_apply] using h
  let g : ℤ := ∑ i, a i*rawNormal6 v i
  have hgQ : (g : ℚ) = q/r := by
    have haQ : (∑ i, (a i : ℚ)*(M i : ℚ))=1 := by exact_mod_cast ha
    calc
      (g : ℚ) = ∑ i, (a i : ℚ)*(rawNormal6 v i : ℚ) := by simp [g]
      _ = (q/r)*(∑ i, (a i : ℚ)*(M i : ℚ)) := by
        simp only [hi,Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = q/r := by rw [haQ,mul_one]
  have hg : g ≠ 0 := by
    intro hz
    rw [hz,Int.cast_zero] at hgQ
    exact (div_ne_zero hq hr) hgQ.symm
  have hscale (i : Fin 6) : rawNormal6 v i=g*M i := by
    have h : (rawNormal6 v i : ℚ) = (g : ℚ)*(M i : ℚ) := by rw [hgQ];exact hi i
    exact_mod_cast h
  refine ⟨hg,hscale,?_⟩
  intro d
  constructor
  · intro hd
    exact Finset.dvd_sum (fun i _ => dvd_mul_of_dvd_right (hd i) (a i))
  · intro hd i
    rw [hscale]
    exact dvd_mul_of_dvd_left hd (M i)



theorem primitive_minor_gcd6 (v : Matrix (Fin 6) (Fin 6) ℤ)
    (hv : LinearIndependent ℚ (fun j i => (v j i : ℚ))) (M a : Fin 6 → ℤ)
    (hM : M ≠ 0) (ha : (∑ i, a i*M i)=1)
    (hann : ∀ j : Fin 5, (∑ i, M i*v j.castSucc i)=0) :
    Finset.univ.gcd (fun i => (rawNormal6 v i).natAbs) =
      (∑ i, a i*rawNormal6 v i).natAbs := by
  have h := primitive_minor_factor6 v hv M a hM ha hann
  apply Nat.dvd_antisymm
  · apply Int.natCast_dvd.mp
    apply (h.2.2 _).mp
    intro i
    exact Int.natCast_dvd.mpr (Finset.gcd_dvd (Finset.mem_univ i))
  · apply Finset.dvd_gcd
    intro i _
    exact Int.natAbs_dvd_natAbs.mpr ((h.2.2 _).mpr dvd_rfl i)

theorem primitive_minor_normalization6 (v : Matrix (Fin 6) (Fin 6) ℤ)
    (hv : LinearIndependent ℚ (fun j i => (v j i : ℚ))) (M a : Fin 6 → ℤ)
    (hM : M ≠ 0) (ha : (∑ i, a i*M i)=1)
    (hann : ∀ j : Fin 5, (∑ i, M i*v j.castSucc i)=0) :
    let d := Finset.univ.gcd (fun i => (rawNormal6 v i).natAbs)
    (fun i => rawNormal6 v i/(d : ℤ)) = M ∨
      (fun i => rawNormal6 v i/(d : ℤ)) = -M := by
  have h := primitive_minor_factor6 v hv M a hM ha hann
  let g : ℤ := ∑ i, a i*rawNormal6 v i
  have hg : g ≠ 0 := h.1
  have hgpos : 0 < g.natAbs := Int.natAbs_pos.mpr hg
  have hgn : (g.natAbs : ℤ) ≠ 0 := by
    have hp : (0 : ℤ) < g.natAbs := by exact_mod_cast hgpos
    exact hp.ne'
  dsimp only
  rw [primitive_minor_gcd6 v hv M a hM ha hann]
  change (fun i => rawNormal6 v i/(g.natAbs : ℤ)) = M ∨
    (fun i => rawNormal6 v i/(g.natAbs : ℤ)) = -M
  rcases Int.natAbs_eq g with he | he
  · left
    funext i
    rw [h.2.1 i]
    change g*M i/(g.natAbs : ℤ) = M i
    nth_rw 1 [he]
    rw [Int.mul_ediv_cancel_left _ hgn]
  · right
    funext i
    change rawNormal6 v i/(g.natAbs : ℤ) = -M i
    rw [h.2.1 i]
    change g*M i/(g.natAbs : ℤ) = -M i
    nth_rw 1 [he]
    rw [show -(g.natAbs : ℤ)*M i = (g.natAbs : ℤ)*(-M i) by ring,
      Int.mul_ediv_cancel_left _ hgn]


def transformedFrame6 {F : Type*} [CommRing F]
    (B : Matrix (Fin 6) (Fin 6) F) (v : Matrix (Fin 6) (Fin 6) ℤ) :
    Matrix (Fin 6) (Fin 6) F := (v.map (Int.castRingHom F))*B.transpose

theorem transformedFrame6_apply {F : Type*} [CommRing F]
    (B : Matrix (Fin 6) (Fin 6) F) (v : Matrix (Fin 6) (Fin 6) ℤ) (j i : Fin 6) :
    transformedFrame6 B v j i = (B *ᵥ (fun k => (v j k : F))) i := by
  simp [transformedFrame6,Matrix.mul_apply,Matrix.mulVec,dotProduct,mul_comm]

theorem transformed_adjugate_cofactor6 {F : Type*} [CommRing F]
    (B : Matrix (Fin 6) (Fin 6) F) (v : Matrix (Fin 6) (Fin 6) ℤ)
    (M : Fin 6 → ℤ) (g : ℤ) (hscale : ∀ k, rawNormal6 v k = g*M k) (i : Fin 6) :
    (transformedFrame6 B v).adjugate i 5 = (g : F)*cofactorValue6 B M i := by
  have hmap := (Int.castRingHom F).map_adjugate v
  change v.adjugate.map (Int.castRingHom F) = (v.map (Int.castRingHom F)).adjugate at hmap
  rw [transformedFrame6,Matrix.adjugate_mul_distrib,← Matrix.adjugate_transpose,← hmap]
  change (∑ k, cofactor6 B i k*(rawNormal6 v k : F)) = (g : F)*cofactorValue6 B M i
  simp only [hscale,Int.cast_mul,cofactorValue6,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem transformed_minor_cofactor6 {F : Type*} [CommRing F]
    (B : Matrix (Fin 6) (Fin 6) F) (v : Matrix (Fin 6) (Fin 6) ℤ)
    (M : Fin 6 → ℤ) (g : ℤ) (hscale : ∀ k, rawNormal6 v k = g*M k) (i : Fin 6) :
    (-1 : F)^(5+i.val) *
      ((transformedFrame6 B v).submatrix Fin.castSucc i.succAbove).det =
      (g : F)*cofactorValue6 B M i := by
  have hminor : (transformedFrame6 B v).adjugate i 5 = (-1 : F)^(5+i.val) *
      ((transformedFrame6 B v).submatrix Fin.castSucc i.succAbove).det := by
    rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
    have hlast : (5 : Fin 6).succAbove = Fin.castSucc := Fin.succAbove_last
    rw [hlast]
    congr 1
  exact hminor.symm.trans (transformed_adjugate_cofactor6 B v M g hscale i)

theorem primitive_transformed_minor6 {F : Type*} [CommRing F]
    (B : Matrix (Fin 6) (Fin 6) F) (v : Matrix (Fin 6) (Fin 6) ℤ)
    (hv : LinearIndependent ℚ (fun j i => (v j i : ℚ))) (M a : Fin 6 → ℤ)
    (hM : M ≠ 0) (ha : (∑ i, a i*M i)=1)
    (hann : ∀ j : Fin 5, (∑ i, M i*v j.castSucc i)=0) (i : Fin 6) :
    (-1 : F)^(5+i.val) *
      ((transformedFrame6 B v).submatrix Fin.castSucc i.succAbove).det =
      ((∑ k, a k*rawNormal6 v k : ℤ) : F)*cofactorValue6 B M i :=
  transformed_minor_cofactor6 B v M _ (primitive_minor_factor6 v hv M a hM ha hann).2.1 i


def minorNormalization6 (v : Matrix (Fin 6) (Fin 6) ℤ) (M a : Fin 6 → ℤ) : Prop :=
  let g : ℤ := ∑ i, a i*rawNormal6 v i
  let d := Finset.univ.gcd (fun i => (rawNormal6 v i).natAbs)
  rawNormal6 v ≠ 0 ∧ g ≠ 0 ∧ (∀ i, rawNormal6 v i = g*M i) ∧
    (∀ b : ℤ, (∀ i, b ∣ rawNormal6 v i) ↔ b ∣ g) ∧ d = g.natAbs ∧
    ((fun i => rawNormal6 v i/(d : ℤ)) = M ∨ (fun i => rawNormal6 v i/(d : ℤ)) = -M)

theorem primitive_minor_data6 (v : Matrix (Fin 6) (Fin 6) ℤ)
    (hv : LinearIndependent ℚ (fun j i => (v j i : ℚ))) (M a : Fin 6 → ℤ)
    (hM : M ≠ 0) (ha : (∑ i, a i*M i)=1)
    (hann : ∀ j : Fin 5, (∑ i, M i*v j.castSucc i)=0) : minorNormalization6 v M a := by
  have h := primitive_minor_factor6 v hv M a hM ha hann
  exact ⟨rawNormal6_nonzero v hv,h.1,h.2.1,h.2.2,primitive_minor_gcd6 v hv M a hM ha hann,
    primitive_minor_normalization6 v hv M a hM ha hann⟩

theorem transformed_minor_map6 {F G : Type*} [CommRing F] [CommRing G]
    (f : F →+* G) (B : Matrix (Fin 6) (Fin 6) F) (v : Matrix (Fin 6) (Fin 6) ℤ)
    (M : Fin 6 → ℤ) (g : ℤ) (hscale : ∀ k, rawNormal6 v k = g*M k) (i : Fin 6) :
    (-1 : G)^(5+i.val) *
      ((transformedFrame6 (B.map f) v).submatrix Fin.castSucc i.succAbove).det =
      f ((-1 : F)^(5+i.val) *
        ((transformedFrame6 B v).submatrix Fin.castSucc i.succAbove).det) := by
  rw [transformed_minor_cofactor6 (B.map f) v M g hscale i,
    transformed_minor_cofactor6 B v M g hscale i,cofactorValue6_map]
  simp only [map_mul,map_intCast]

theorem finite_transformed_minor6 (p : ℕ) [Fact p.Prime]
    (A : Matrix (Fin 4) (Fin 4) ℚ) (v : Matrix (Fin 6) (Fin 6) ℤ)
    (M : Fin 6 → ℤ) (g : ℤ) (hscale : ∀ k, rawNormal6 v k = g*M k) (i : Fin 6) :
    (-1 : ℚ_[p])^(5+i.val) *
      ((transformedFrame6 (Auxiliary6.SourceExpansion.finiteMatrix p A) v).submatrix
        Fin.castSucc i.succAbove).det =
      (g : ℚ_[p])*(∑ k, (M k : ℚ_[p])*
        algebraMap ℚ ℚ_[p] (cofactor6 (compound A) i k)) := by
  rw [transformed_minor_cofactor6 _ v M g hscale i]
  simp only [cofactorValue6,finite_cofactor6_rational]

def actualTransformedCofactors6 (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (v : Matrix (Fin 6) (Fin 6) ℤ)
    (M a : Fin 6 → ℤ) : Prop :=
  let g : ℤ := ∑ k, a k*rawNormal6 v k
  ∀ i : Fin 6,
    (-1 : ℝ)^(5+i.val) *
      ((transformedFrame6 (compound L) v).submatrix Fin.castSucc i.succAbove).det =
      (g : ℝ)*cofactorValue6 (compound L) M i ∧
    (-1 : ℚ_[2])^(5+i.val) *
      ((transformedFrame6 (Auxiliary6.SourceExpansion.finiteMatrix 2 A2) v).submatrix
        Fin.castSucc i.succAbove).det =
      (g : ℚ_[2])*cofactorValue6 (Auxiliary6.SourceExpansion.finiteMatrix 2 A2) M i ∧
    (-1 : ℚ_[3])^(5+i.val) *
      ((transformedFrame6 (Auxiliary6.SourceExpansion.finiteMatrix 3 A3) v).submatrix
        Fin.castSucc i.succAbove).det =
      (g : ℚ_[3])*cofactorValue6 (Auxiliary6.SourceExpansion.finiteMatrix 3 A3) M i

theorem actual_primitive_transformed6 (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (v : Matrix (Fin 6) (Fin 6) ℤ)
    (hv : LinearIndependent ℚ (fun j i => (v j i : ℚ))) (M a : Fin 6 → ℤ)
    (hM : M ≠ 0) (ha : (∑ i, a i*M i)=1)
    (hann : ∀ j : Fin 5, (∑ i, M i*v j.castSucc i)=0) :
    actualTransformedCofactors6 A2 A3 L v M a := by
  intro i
  exact ⟨primitive_transformed_minor6 _ v hv M a hM ha hann i,
    primitive_transformed_minor6 _ v hv M a hM ha hann i,
    primitive_transformed_minor6 _ v hv M a hM ha hann i⟩

def actualTransformedNonzero6 (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (v : Matrix (Fin 6) (Fin 6) ℤ) (s : MixedIndex6) : Prop :=
  (transformedFrame6 (compound L) v).adjugate (s 0) 5 ≠ 0 ∧
    (transformedFrame6 (Auxiliary6.SourceExpansion.finiteMatrix 2 A2) v).adjugate (s 1) 5 ≠ 0 ∧
    (transformedFrame6 (Auxiliary6.SourceExpansion.finiteMatrix 3 A3) v).adjugate (s 2) 5 ≠ 0

theorem actual_transformed_nonzero6 (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (v : Matrix (Fin 6) (Fin 6) ℤ)
    (M : Fin 6 → ℤ) (g : ℤ) (hg : g ≠ 0)
    (hscale : ∀ k, rawNormal6 v k = g*M k) (s : MixedIndex6)
    (hs : actualNonzero6 A2 A3 L M s) : actualTransformedNonzero6 A2 A3 L v s := by
  dsimp only [actualTransformedNonzero6]
  rw [transformed_adjugate_cofactor6 _ v M g hscale,
    transformed_adjugate_cofactor6 _ v M g hscale,
    transformed_adjugate_cofactor6 _ v M g hscale]
  exact ⟨mul_ne_zero (by exact_mod_cast hg) hs.1,
    mul_ne_zero (by exact_mod_cast hg) hs.2.1,
    mul_ne_zero (by exact_mod_cast hg) hs.2.2⟩

end CompoundFeasibility.SourceHeightBounds6
