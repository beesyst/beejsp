import SubspaceBridge.OriginalExterior3_4
import SubspaceBridge.OriginalMinima4
import SubspaceBridge.CompoundSourceFamily42
import Mathlib.RingTheory.Algebraic.Integral
open scoped BigOperators Matrix
namespace CompoundFeasibility.Exterior3
def missing4 : Fin 4 → Fin 4 := ![3,2,1,0]
def sign4 {R : Type*} [CommRing R] : Fin 4 → R := ![-1,1,-1,1]
def complementMatrix4 {R : Type*} [CommRing R] : Matrix (Fin 4) (Fin 4) R :=
  fun s t => if t = missing4 s then sign4 s else 0

def signedAdjugate4 {R : Type*} [CommRing R] (A : Matrix (Fin 4) (Fin 4) R) :
    Matrix (Fin 4) (Fin 4) R :=
  (complementMatrix4 (R := R)) * A.adjugate.transpose * (complementMatrix4 (R := R)).transpose

theorem compound3_adjugate_row0 {R : Type*} [CommRing R] (A : Matrix (Fin 4) (Fin 4) R) (t : Fin 4) :
    compound3Matrix4 A 0 t = signedAdjugate4 A 0 t := by
  have h3 : ((3 : Fin 4) : ℕ) = 3 := rfl
  fin_cases t <;>
    simp [h3,signedAdjugate4,compound3Matrix4,complementMatrix4,missing4,sign4,tripleIndex4,Matrix.mul_apply,
      Fin.sum_univ_succ,Matrix.transpose_apply,Matrix.adjugate_fin_succ_eq_det_submatrix,
      Matrix.det_fin_three,Matrix.submatrix,Fin.succAbove] <;> ring

theorem compound3_adjugate_row1 {R : Type*} [CommRing R] (A : Matrix (Fin 4) (Fin 4) R) (t : Fin 4) :
    compound3Matrix4 A 1 t = signedAdjugate4 A 1 t := by
  have h3 : ((3 : Fin 4) : ℕ) = 3 := rfl
  fin_cases t <;>
    simp [h3,signedAdjugate4,compound3Matrix4,complementMatrix4,missing4,sign4,tripleIndex4,Matrix.mul_apply,
      Fin.sum_univ_succ,Matrix.transpose_apply,Matrix.adjugate_fin_succ_eq_det_submatrix,
      Matrix.det_fin_three,Matrix.submatrix,Fin.succAbove] <;> ring

theorem compound3_adjugate_row2 {R : Type*} [CommRing R] (A : Matrix (Fin 4) (Fin 4) R) (t : Fin 4) :
    compound3Matrix4 A 2 t = signedAdjugate4 A 2 t := by
  have h3 : ((3 : Fin 4) : ℕ) = 3 := rfl
  fin_cases t <;>
    simp [h3,signedAdjugate4,compound3Matrix4,complementMatrix4,missing4,sign4,tripleIndex4,Matrix.mul_apply,
      Fin.sum_univ_succ,Matrix.transpose_apply,Matrix.adjugate_fin_succ_eq_det_submatrix,
      Matrix.det_fin_three,Matrix.submatrix,Fin.succAbove] <;> ring

theorem compound3_adjugate_row3 {R : Type*} [CommRing R] (A : Matrix (Fin 4) (Fin 4) R) (t : Fin 4) :
    compound3Matrix4 A 3 t = signedAdjugate4 A 3 t := by
  have h3 : ((3 : Fin 4) : ℕ) = 3 := rfl
  fin_cases t <;>
    simp [h3,signedAdjugate4,compound3Matrix4,complementMatrix4,missing4,sign4,tripleIndex4,Matrix.mul_apply,
      Fin.sum_univ_succ,Matrix.transpose_apply,Matrix.adjugate_fin_succ_eq_det_submatrix,
      Matrix.det_fin_three,Matrix.submatrix,Fin.succAbove] <;> ring

theorem compound3_adjugate {R : Type*} [CommRing R] (A : Matrix (Fin 4) (Fin 4) R) :
    compound3Matrix4 A = complementMatrix4 * A.adjugate.transpose * complementMatrix4.transpose := by
  ext s t
  fin_cases s
  · exact compound3_adjugate_row0 A t
  · exact compound3_adjugate_row1 A t
  · exact compound3_adjugate_row2 A t
  · exact compound3_adjugate_row3 A t

theorem complementMatrix4_orthogonal {R : Type*} [CommRing R] :
    (complementMatrix4 : Matrix (Fin 4) (Fin 4) R).transpose * complementMatrix4 = 1 ∧
    (complementMatrix4 : Matrix (Fin 4) (Fin 4) R) * complementMatrix4.transpose = 1 := by
  constructor <;> ext s t <;> fin_cases s <;> fin_cases t <;>
    simp [complementMatrix4,missing4,sign4,Matrix.mul_apply,Fin.sum_univ_succ,
      Matrix.transpose_apply,Matrix.one_apply]

theorem compound3_det {R : Type*} [CommRing R] (A : Matrix (Fin 4) (Fin 4) R) :
    (compound3Matrix4 A).det = A.det ^ 3 := by
  have h := congrArg Matrix.det (complementMatrix4_orthogonal (R := R)).1
  rw [Matrix.det_mul,Matrix.det_transpose,Matrix.det_one] at h
  rw [compound3_adjugate,Matrix.det_mul,Matrix.det_mul,Matrix.det_transpose,
    Matrix.det_transpose,Matrix.det_adjugate]
  simpa only [Fintype.card_fin] using show
    (complementMatrix4 : Matrix (Fin 4) (Fin 4) R).det * A.det ^ (4-1) * complementMatrix4.det = A.det^3 by
    calc
      _ = A.det^3 * (complementMatrix4.det * complementMatrix4.det) := by ring
      _ = _ := by rw [h,mul_one]

theorem compound3_one {R : Type*} [CommRing R] :
    compound3Matrix4 (1 : Matrix (Fin 4) (Fin 4) R) = 1 := by
  rw [compound3_adjugate,Matrix.adjugate_one,Matrix.transpose_one,Matrix.mul_one]
  exact (complementMatrix4_orthogonal (R := R)).2

theorem compound3_mul {R : Type*} [CommRing R] (A B : Matrix (Fin 4) (Fin 4) R) :
    compound3Matrix4 (A * B) = compound3Matrix4 A * compound3Matrix4 B := by
  rw [compound3_adjugate (A*B),Matrix.adjugate_mul_distrib,Matrix.transpose_mul,
    compound3_adjugate A,compound3_adjugate B]
  let H : Matrix (Fin 4) (Fin 4) R := complementMatrix4
  have hH : H.transpose * H = 1 := (complementMatrix4_orthogonal (R := R)).1
  change H * (A.adjugate.transpose * B.adjugate.transpose) * H.transpose =
    (H * A.adjugate.transpose * H.transpose) * (H * B.adjugate.transpose * H.transpose)
  calc
    _ = H * A.adjugate.transpose * (H.transpose * H) * B.adjugate.transpose * H.transpose := by
      rw [hH,Matrix.mul_one]
      simp only [Matrix.mul_assoc]
    _ = _ := by simp only [Matrix.mul_assoc]

theorem compound3_transpose {R : Type*} [CommRing R] (A : Matrix (Fin 4) (Fin 4) R) :
    compound3Matrix4 A.transpose = (compound3Matrix4 A).transpose := by
  ext s t
  change (A.submatrix (tripleIndex4 t) (tripleIndex4 s)).transpose.det = _
  exact Matrix.det_transpose _

theorem compound3_unit {R : Type*} [CommRing R] (A : Matrix (Fin 4) (Fin 4) R)
    (hA : IsUnit A) : IsUnit (compound3Matrix4 A) := by
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  rw [compound3_det]
  exact ((Matrix.isUnit_iff_isUnit_det _).mp hA).pow 3

theorem compound3_inverse {K : Type*} [Field K] (A : Matrix (Fin 4) (Fin 4) K)
    (hA : IsUnit A) : compound3Matrix4 A⁻¹ = (compound3Matrix4 A)⁻¹ := by
  apply Eq.symm
  apply Matrix.inv_eq_right_inv
  rw [← compound3_mul,Matrix.mul_nonsing_inv A ((Matrix.isUnit_iff_isUnit_det _).mp hA),compound3_one]

theorem compound3_dual_pairing {K : Type*} [Field K] (A : Matrix (Fin 4) (Fin 4) K)
    (hA : IsUnit A) (s t : Fin 4) :
    ∑ j, compound3Matrix4 A s j * compound3Matrix4 (A⁻¹).transpose t j =
      if s = t then 1 else 0 := by
  have h : compound3Matrix4 A * (compound3Matrix4 (A⁻¹).transpose).transpose = 1 := by
    rw [compound3_transpose,Matrix.transpose_transpose,← compound3_mul,
      Matrix.mul_nonsing_inv A ((Matrix.isUnit_iff_isUnit_det _).mp hA),compound3_one]
  simpa only [Matrix.mul_apply,Matrix.transpose_apply,Matrix.one_apply] using congrFun (congrFun h s) t

theorem compound3_algebraic (L : Matrix (Fin 4) (Fin 4) ℝ)
    (hL : ∀ i j, IsAlgebraic ℚ (L i j)) :
    ∀ s t, IsAlgebraic ℚ (compound3Matrix4 L s t) := by
  intro s t
  simp only [compound3Matrix4,Matrix.det_fin_three,Matrix.submatrix_apply]
  apply IsAlgebraic.sub
  · apply IsAlgebraic.add
    · apply IsAlgebraic.add
      · apply IsAlgebraic.sub
        · exact (((hL _ _).mul (hL _ _)).mul (hL _ _)).sub (((hL _ _).mul (hL _ _)).mul (hL _ _))
        · exact ((hL _ _).mul (hL _ _)).mul (hL _ _)
      · exact ((hL _ _).mul (hL _ _)).mul (hL _ _)
    · exact ((hL _ _).mul (hL _ _)).mul (hL _ _)
  · exact ((hL _ _).mul (hL _ _)).mul (hL _ _)

def tripleWeights4 (c : Fin 4 → ℝ) : Fin 4 → ℝ :=
  fun s => c (tripleIndex4 s 0) + c (tripleIndex4 s 1) + c (tripleIndex4 s 2)

theorem tripleWeights4_sum (c : Fin 4 → ℝ) :
    ∑ s, tripleWeights4 c s = 3 * ∑ i, c i := by
  simp [tripleWeights4,tripleIndex4,Fin.sum_univ_succ]
  ring

theorem tripleWeights4_balance (c₀ c₂ c₃ : Fin 4 → ℝ)
    (hb : ∑ i, (c₀ i + c₂ i + c₃ i) = 0) :
    ∑ s, (tripleWeights4 c₀ s + tripleWeights4 c₂ s + tripleWeights4 c₃ s) = 0 := by
  calc
    _ = ∑ s, tripleWeights4 (fun i => c₀ i + c₂ i + c₃ i) s := by
      apply Finset.sum_congr rfl
      intro s _
      dsimp [tripleWeights4]
      ring
    _ = 3 * ∑ i, (c₀ i + c₂ i + c₃ i) := tripleWeights4_sum _
    _ = 0 := by rw [hb,mul_zero]

theorem tripleWeights4_bounds (c₀ c₂ c₃ : Fin 4 → ℝ)
    (h₀ : ∀ i, |c₀ i| ≤ 1) (h₂ : ∀ i, -1 ≤ c₂ i ∧ c₂ i ≤ 0)
    (h₃ : ∀ i, -1 ≤ c₃ i ∧ c₃ i ≤ 0) :
    (∀ s, |tripleWeights4 c₀ s| ≤ 3) ∧
    (∀ s, -3 ≤ tripleWeights4 c₂ s ∧ tripleWeights4 c₂ s ≤ 0) ∧
    (∀ s, -3 ≤ tripleWeights4 c₃ s ∧ tripleWeights4 c₃ s ≤ 0) := by
  refine ⟨?_,?_,?_⟩
  · intro s
    dsimp [tripleWeights4]
    exact ((abs_add _ _).trans (add_le_add_right (abs_add _ _) _)).trans (by linarith [h₀ (tripleIndex4 s 0),h₀ (tripleIndex4 s 1),h₀ (tripleIndex4 s 2)])
  · intro s
    dsimp [tripleWeights4]
    constructor <;> linarith [(h₂ (tripleIndex4 s 0)).1,(h₂ (tripleIndex4 s 1)).1,
      (h₂ (tripleIndex4 s 2)).1,(h₂ (tripleIndex4 s 0)).2,
      (h₂ (tripleIndex4 s 1)).2,(h₂ (tripleIndex4 s 2)).2]
  · intro s
    dsimp [tripleWeights4]
    constructor <;> linarith [(h₃ (tripleIndex4 s 0)).1,(h₃ (tripleIndex4 s 1)).1,
      (h₃ (tripleIndex4 s 2)).1,(h₃ (tripleIndex4 s 0)).2,
      (h₃ (tripleIndex4 s 1)).2,(h₃ (tripleIndex4 s 2)).2]

theorem ceil_triple_bounds (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    Nat.ceil (a+b+c) ≤ Nat.ceil a + Nat.ceil b + Nat.ceil c ∧
    Nat.ceil a + Nat.ceil b + Nat.ceil c ≤ Nat.ceil (a+b+c) + 2 := by
  obtain ⟨h₁,h₂⟩ := ceil_pair_bounds a b ha hb
  obtain ⟨h₃,h₄⟩ := ceil_pair_bounds (a+b) c (add_nonneg ha hb) hc
  omega

theorem arch_tripleWedge4_bound (x y z : Fin 4 → ℝ) (A : Fin 4 → ℝ)
    (hA : ∀ i, 0 < A i) (rₓ rᵧ r_z : ℝ) (hrₓ : 0 ≤ rₓ) (hrᵧ : 0 ≤ rᵧ) (hr_z : 0 ≤ r_z)
    (hx : ∀ i, |x i| ≤ rₓ * A i) (hy : ∀ i, |y i| ≤ rᵧ * A i)
    (hz : ∀ i, |z i| ≤ r_z * A i) (s : Fin 4) :
    |tripleWedge4 x y z s| ≤
      6 * rₓ * rᵧ * r_z * A (tripleIndex4 s 0) * A (tripleIndex4 s 1) * A (tripleIndex4 s 2) := by
  have term (i j k : Fin 4) : |x i * y j * z k| ≤ (rₓ*A i)*(rᵧ*A j)*(r_z*A k) := by
    rw [abs_mul,abs_mul]
    exact mul_le_mul (mul_le_mul (hx i) (hy j) (abs_nonneg _) (mul_nonneg hrₓ (hA _).le))
      (hz k) (abs_nonneg _) (mul_nonneg (mul_nonneg hrₓ (hA _).le) (mul_nonneg hrᵧ (hA _).le))
  let a := tripleIndex4 s 0
  let b := tripleIndex4 s 1
  let c := tripleIndex4 s 2
  have t₁ := term a b c
  have t₂ := term b c a
  have t₃ := term c a b
  have t₄ := term c b a
  have t₅ := term b a c
  have t₆ := term a c b
  have h₁ := abs_add (x a*y b*z c) (x b*y c*z a)
  have h₂ := abs_add (x a*y b*z c+x b*y c*z a) (x c*y a*z b)
  have h₃ := abs_sub (x a*y b*z c+x b*y c*z a+x c*y a*z b) (x c*y b*z a)
  have h₄ := abs_sub (x a*y b*z c+x b*y c*z a+x c*y a*z b-x c*y b*z a) (x b*y a*z c)
  have h₅ := abs_sub (x a*y b*z c+x b*y c*z a+x c*y a*z b-x c*y b*z a-x b*y a*z c) (x a*y c*z b)
  rw [tripleWedge4_expansion]
  change |x a*y b*z c+x b*y c*z a+x c*y a*z b-x c*y b*z a-x b*y a*z c-x a*y c*z b| ≤ _
  calc
    _ ≤ (rₓ*A a)*(rᵧ*A b)*(r_z*A c)+(rₓ*A b)*(rᵧ*A c)*(r_z*A a)+
      (rₓ*A c)*(rᵧ*A a)*(r_z*A b)+(rₓ*A c)*(rᵧ*A b)*(r_z*A a)+
      (rₓ*A b)*(rᵧ*A a)*(r_z*A c)+(rₓ*A a)*(rᵧ*A c)*(r_z*A b) := by linarith
    _ = _ := by dsimp [a,b,c]; ring

theorem arch_compound3_bound (L : Matrix (Fin 4) (Fin 4) ℝ) (A : Fin 4 → ℝ)
    (hA : ∀ i, 0 < A i) (rₓ rᵧ r_z : ℝ) (hrₓ : 0 ≤ rₓ) (hrᵧ : 0 ≤ rᵧ) (hr_z : 0 ≤ r_z)
    (x y z : Fin 4 → ℝ) (hx : ∀ i, |(L *ᵥ x) i| ≤ rₓ * A i)
    (hy : ∀ i, |(L *ᵥ y) i| ≤ rᵧ * A i) (hz : ∀ i, |(L *ᵥ z) i| ≤ r_z * A i) (s : Fin 4) :
    |(compound3Matrix4 L *ᵥ tripleWedge4 x y z) s| ≤
      6 * rₓ * rᵧ * r_z * A (tripleIndex4 s 0) * A (tripleIndex4 s 1) * A (tripleIndex4 s 2) := by
  rw [tripleWedge4_transform]
  exact arch_tripleWedge4_bound _ _ _ A hA rₓ rᵧ r_z hrₓ hrᵧ hr_z hx hy hz s


noncomputable def originalExponents3_4 (p : ℕ) (Q : ℝ) (c : Fin 4 → ℝ) : Fin 4 → ℕ :=
  fun i => Nat.ceil (JSP000334.qThreshold p Q (c i))

noncomputable def summedExponents3_4 (p : ℕ) (Q : ℝ) (c : Fin 4 → ℝ) : Fin 4 → ℕ :=
  fun s => originalExponents3_4 p Q c (tripleIndex4 s 0) +
    originalExponents3_4 p Q c (tripleIndex4 s 1) + originalExponents3_4 p Q c (tripleIndex4 s 2)

noncomputable def originalCompoundGroup3_4 (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (Q : ℝ) (c₂ c₃ : Fin 4 → ℝ) : AddSubgroup (Fin 4 → ℤ) :=
  tripleLattice4 2 A₂ (originalExponents3_4 2 Q c₂) ⊓ tripleLattice4 3 A₃ (originalExponents3_4 3 Q c₃)

theorem original_triple_mem4 (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (Q : ℝ) (c₂ c₃ : Fin 4 → ℝ) (x y z : originalSourceGroup4 A₂ A₃ Q c₂ c₃) :
    tripleWedge4 (x : Fin 4 → ℤ) (y : Fin 4 → ℤ) (z : Fin 4 → ℤ) ∈
      originalCompoundGroup3_4 A₂ A₃ Q c₂ c₃ :=
  ⟨tripleWedge4_lattice 2 A₂ _ x y z x.property.1 y.property.1 z.property.1,
    tripleWedge4_lattice 3 A₃ _ x y z x.property.2 y.property.2 z.property.2⟩

theorem summedExponents3_4_sum (p : ℕ) (Q : ℝ) (c : Fin 4 → ℝ) :
    ∑ s, summedExponents3_4 p Q c s = 3 * ∑ i, originalExponents3_4 p Q c i := by
  simp [summedExponents3_4,tripleIndex4,Fin.sum_univ_succ]
  ring

theorem source_triple_rounding4 (p : ℕ) (hp : 1 < p) (Q : ℝ) (hQ : 1 < Q)
    (c : Fin 4 → ℝ) (hc : ∀ i, c i ≤ 0) (s : Fin 4) :
    Nat.ceil (JSP000334.qThreshold p Q (tripleWeights4 c s)) ≤ summedExponents3_4 p Q c s ∧
    summedExponents3_4 p Q c s ≤ Nat.ceil (JSP000334.qThreshold p Q (tripleWeights4 c s)) + 2 := by
  have ht : JSP000334.qThreshold p Q (tripleWeights4 c s) =
      JSP000334.qThreshold p Q (c (tripleIndex4 s 0)) +
      JSP000334.qThreshold p Q (c (tripleIndex4 s 1)) + JSP000334.qThreshold p Q (c (tripleIndex4 s 2)) := by
    unfold JSP000334.qThreshold tripleWeights4
    ring
  rw [ht]
  exact ceil_triple_bounds _ _ _
    (JSP000334.qThreshold_nonneg p hp Q _ hQ (hc _))
    (JSP000334.qThreshold_nonneg p hp Q _ hQ (hc _))
    (JSP000334.qThreshold_nonneg p hp Q _ hQ (hc _))

theorem triple_widths_rpow4 (Q : ℝ) (hQ : 0 < Q) (c : Fin 4 → ℝ) (s : Fin 4) :
    Q ^ tripleWeights4 c s = Q ^ c (tripleIndex4 s 0) * Q ^ c (tripleIndex4 s 1) * Q ^ c (tripleIndex4 s 2) := by
  simp only [tripleWeights4,Real.rpow_add hQ]

theorem source_triple_gauge4 (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c : Fin 4 → ℝ) (rₓ rᵧ r_z : ℝ)
    (hrₓ : 0 ≤ rₓ) (hrᵧ : 0 ≤ rᵧ) (hr_z : 0 ≤ r_z) (x y z : Fin 4 → ℝ)
    (hx : ∀ i, |(L *ᵥ x) i| ≤ rₓ * Q ^ c i)
    (hy : ∀ i, |(L *ᵥ y) i| ≤ rᵧ * Q ^ c i)
    (hz : ∀ i, |(L *ᵥ z) i| ≤ r_z * Q ^ c i) :
    coordinateGauge4 (originalCoordinates4 (compound3Matrix4 L) (compound3_unit L hL)
      Q hQ (tripleWeights4 c)) (tripleWedge4 x y z) ≤ 6*rₓ*rᵧ*r_z := by
  apply (originalCoordinates4_bounds (compound3Matrix4 L) (compound3_unit L hL)
    Q hQ (tripleWeights4 c) _ _).mpr
  intro s
  rw [triple_widths_rpow4 Q (lt_trans zero_lt_one hQ)]
  have hh := arch_compound3_bound L (fun i => Q ^ c i)
    (fun i => Real.rpow_pos_of_pos (lt_trans zero_lt_one hQ) _) rₓ rᵧ r_z hrₓ hrᵧ hr_z x y z hx hy hz s
  convert hh using 1 <;> ring

def tripleFrame4 (u : Fin 4 → Fin 4 → ℤ) : Fin 4 → Fin 4 → ℤ :=
  fun s => tripleWedge4 (u (tripleIndex4 s 0)) (u (tripleIndex4 s 1)) (u (tripleIndex4 s 2))

theorem tripleFrame4_cast {R : Type*} [CommRing R] (u : Fin 4 → Fin 4 → ℤ) :
    (fun s t => (tripleFrame4 u s t : R)) =
      compound3Matrix4 (Matrix.map (u : Matrix (Fin 4) (Fin 4) ℤ) (Int.castRingHom R)) := by
  ext s t
  simp [tripleFrame4,tripleWedge4_expansion,compound3Matrix4,Matrix.det_fin_three]
  ring

theorem tripleFrame4_independent (u : Fin 4 → Fin 4 → ℤ)
    (hu : LinearIndependent ℝ (fun j => fun i => (u j i : ℝ))) :
    LinearIndependent ℚ (fun s => fun t => (tripleFrame4 u s t : ℚ)) ∧
    LinearIndependent ℝ (fun s => fun t => (tripleFrame4 u s t : ℝ)) := by
  constructor
  · rw [tripleFrame4_cast]
    exact Matrix.linearIndependent_rows_iff_isUnit.mpr
      (compound3_unit _ (Matrix.linearIndependent_rows_iff_isUnit.mp
        (integral_frame_rational_independent u hu)))
  · rw [tripleFrame4_cast]
    exact Matrix.linearIndependent_rows_iff_isUnit.mpr
      (compound3_unit _ (Matrix.linearIndependent_rows_iff_isUnit.mp hu))

theorem tripleFrame4_cofactor {R : Type*} [CommRing R] (u : Fin 4 → Fin 4 → ℤ) :
    (fun s t => (tripleFrame4 u s t : R)) =
      complementMatrix4 * (Matrix.map (u : Matrix (Fin 4) (Fin 4) ℤ) (Int.castRingHom R)).adjugate.transpose *
        complementMatrix4.transpose := by
  rw [tripleFrame4_cast,compound3_adjugate]

theorem tripleFrame4_pairing (u : Fin 4 → Fin 4 → ℤ)
    (hu : LinearIndependent ℝ (fun j => fun i => (u j i : ℝ))) (s t : Fin 4) :
    ∑ j, (tripleFrame4 u s j : ℚ) *
      compound3Matrix4 ((Matrix.map (u : Matrix (Fin 4) (Fin 4) ℤ) (Int.castRingHom ℚ))⁻¹).transpose t j =
        if s = t then 1 else 0 := by
  have hU := Matrix.linearIndependent_rows_iff_isUnit.mp (integral_frame_rational_independent u hu)
  have h := compound3_dual_pairing (Matrix.map (u : Matrix (Fin 4) (Fin 4) ℤ) (Int.castRingHom ℚ)) hU s t
  simpa only [← tripleFrame4_cast] using h

theorem tripleFrame4_real_cast (u : Fin 4 → Fin 4 → ℤ) (s : Fin 4) :
    integerReal (tripleFrame4 u s) =
      tripleWedge4 (integerReal (u (tripleIndex4 s 0))) (integerReal (u (tripleIndex4 s 1)))
        (integerReal (u (tripleIndex4 s 2))) := by
  exact (tripleWedge4_map (Int.castRingHom ℝ) _ _ _).symm

theorem source_tripleFrame4_gauge (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c : Fin 4 → ℝ) (u : Fin 4 → Fin 4 → ℤ) (r : Fin 4 → ℝ)
    (hr : ∀ i, 0 ≤ r i) (hu : ∀ j i, |(L *ᵥ integerReal (u j)) i| ≤ r j * Q ^ c i) :
    ∀ s, coordinateGauge4 (originalCoordinates4 (compound3Matrix4 L) (compound3_unit L hL)
      Q hQ (tripleWeights4 c)) (integerReal (tripleFrame4 u s)) ≤
        6*r (tripleIndex4 s 0)*r (tripleIndex4 s 1)*r (tripleIndex4 s 2) := by
  intro s
  rw [tripleFrame4_real_cast]
  exact source_triple_gauge4 L hL Q hQ c _ _ _ (hr _) (hr _) (hr _) _ _ _ (hu _) (hu _) (hu _)

theorem source_original_exterior3_bridge4 (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (h₂ : A₂.det = 1) (h₃ : A₃.det = 1)
    (hL : L.det = 1) (hAlg : ∀ i j, IsAlgebraic ℚ (L i j))
    (Q : ℝ) (hQ : 1 < Q) (c₀ c₂ c₃ : Fin 4 → ℝ)
    (hc₀ : ∀ i, |c₀ i| ≤ 1) (hc₂ : ∀ i, -1 ≤ c₂ i ∧ c₂ i ≤ 0)
    (hc₃ : ∀ i, -1 ≤ c₃ i ∧ c₃ i ≤ 0) (hb : ∑ i, (c₀ i+c₂ i+c₃ i) = 0) :
    let hLu := sourceUnit42 L hL
    let lam := sourceMinima4 A₂ A₃ L hLu Q hQ c₀ c₂ c₃
    (compound3Matrix4 A₂).det = 1 ∧ (compound3Matrix4 A₃).det = 1 ∧ (compound3Matrix4 L).det = 1 ∧
    IsUnit (compound3Matrix4 A₂) ∧ IsUnit (compound3Matrix4 A₃) ∧ IsUnit (compound3Matrix4 L) ∧
    (∀ s t, IsAlgebraic ℚ (compound3Matrix4 L s t)) ∧
    (∀ s, |tripleWeights4 c₀ s| ≤ 3) ∧
    (∀ s, -3 ≤ tripleWeights4 c₂ s ∧ tripleWeights4 c₂ s ≤ 0) ∧
    (∀ s, -3 ≤ tripleWeights4 c₃ s ∧ tripleWeights4 c₃ s ≤ 0) ∧
    (∑ s, (tripleWeights4 c₀ s+tripleWeights4 c₂ s+tripleWeights4 c₃ s) = 0) ∧
    (∀ s, Nat.ceil (JSP000334.qThreshold 2 Q (tripleWeights4 c₂ s)) ≤ summedExponents3_4 2 Q c₂ s ∧
      summedExponents3_4 2 Q c₂ s ≤ Nat.ceil (JSP000334.qThreshold 2 Q (tripleWeights4 c₂ s)) + 2) ∧
    (∀ s, Nat.ceil (JSP000334.qThreshold 3 Q (tripleWeights4 c₃ s)) ≤ summedExponents3_4 3 Q c₃ s ∧
      summedExponents3_4 3 Q c₃ s ≤ Nat.ceil (JSP000334.qThreshold 3 Q (tripleWeights4 c₃ s)) + 2) ∧
    (∑ s, summedExponents3_4 2 Q c₂ s) = 3 * ∑ i, originalExponents3_4 2 Q c₂ i ∧
    (∑ s, summedExponents3_4 3 Q c₃ s) = 3 * ∑ i, originalExponents3_4 3 Q c₃ i ∧
    (∀ s, 0 < Q ^ c₀ (tripleIndex4 s 0) * Q ^ c₀ (tripleIndex4 s 1) * Q ^ c₀ (tripleIndex4 s 2)) ∧
    ∃ u : Fin 4 → originalSourceGroup4 A₂ A₃ Q c₂ c₃,
      let uZ : Fin 4 → Fin 4 → ℤ := fun j => (u j : Fin 4 → ℤ)
      LinearIndependent ℝ (fun j => integerReal (uZ j)) ∧
      LinearIndependent ℚ (fun j => fun i => (uZ j i : ℚ)) ∧
      (∀ j, 0 < lam j) ∧ Monotone lam ∧
      (∀ j, coordinateGauge4 (originalCoordinates4 L hLu Q hQ c₀) (integerReal (uZ j)) = lam j) ∧
      (∀ s, tripleFrame4 uZ s ∈ originalCompoundGroup3_4 A₂ A₃ Q c₂ c₃) ∧
      LinearIndependent ℚ (fun s => fun t => (tripleFrame4 uZ s t : ℚ)) ∧
      LinearIndependent ℝ (fun s => fun t => (tripleFrame4 uZ s t : ℝ)) ∧
      (∀ s, coordinateGauge4 (originalCoordinates4 (compound3Matrix4 L) (compound3_unit L hLu)
        Q hQ (tripleWeights4 c₀)) (integerReal (tripleFrame4 uZ s)) ≤
          6*lam (tripleIndex4 s 0)*lam (tripleIndex4 s 1)*lam (tripleIndex4 s 2)) ∧
      (∀ s t, |(compound3Matrix4 L *ᵥ integerReal (tripleFrame4 uZ s)) t| ≤
        (6*lam (tripleIndex4 s 0)*lam (tripleIndex4 s 1)*lam (tripleIndex4 s 2))*Q ^ tripleWeights4 c₀ t) ∧
      (fun s t => (tripleFrame4 uZ s t : ℚ)) = complementMatrix4 *
        (Matrix.map (uZ : Matrix (Fin 4) (Fin 4) ℤ) (Int.castRingHom ℚ)).adjugate.transpose *
          complementMatrix4.transpose ∧
      ∀ s t, ∑ j, (tripleFrame4 uZ s j : ℚ) * compound3Matrix4
        ((Matrix.map (uZ : Matrix (Fin 4) (Fin 4) ℤ) (Int.castRingHom ℚ))⁻¹).transpose t j =
          if s = t then 1 else 0 := by
  dsimp only
  let hLu : IsUnit L := sourceUnit42 L hL
  let lam := sourceMinima4 A₂ A₃ L hLu Q hQ c₀ c₂ c₃
  obtain ⟨hw₀,hw₂,hw₃⟩ := tripleWeights4_bounds c₀ c₂ c₃ hc₀ hc₂ hc₃
  obtain ⟨u,hu,hpos,hmono,hatt,hreal⟩ := exists_sourceMinima4_attaining A₂ A₃ L hLu Q hQ c₀ c₂ c₃
  let uZ : Fin 4 → Fin 4 → ℤ := fun j => (u j : Fin 4 → ℤ)
  have hur : LinearIndependent ℝ (fun j => fun i => (uZ j i : ℝ)) := hu
  obtain ⟨hfrQ,hfrR⟩ := tripleFrame4_independent uZ hur
  have hg := source_tripleFrame4_gauge L hLu Q hQ c₀ uZ lam (fun j => (hpos j).le) hreal
  refine ⟨?_,?_,?_,compound3_unit A₂ (sourceUnit42 A₂ h₂),compound3_unit A₃ (sourceUnit42 A₃ h₃),
    compound3_unit L hLu,compound3_algebraic L hAlg,hw₀,hw₂,hw₃,
    tripleWeights4_balance c₀ c₂ c₃ hb,
    source_triple_rounding4 2 (by decide) Q hQ c₂ (fun i => (hc₂ i).2),
    source_triple_rounding4 3 (by decide) Q hQ c₃ (fun i => (hc₃ i).2),
    summedExponents3_4_sum 2 Q c₂,summedExponents3_4_sum 3 Q c₃,?_,u,
    hu,integral_frame_rational_independent uZ hur,hpos,hmono,hatt,?_,hfrQ,hfrR,hg,?_,
    tripleFrame4_cofactor uZ,tripleFrame4_pairing uZ hur⟩
  · rw [compound3_det,h₂,one_pow]
  · rw [compound3_det,h₃,one_pow]
  · rw [compound3_det,hL,one_pow]
  · intro s
    exact mul_pos (mul_pos (Real.rpow_pos_of_pos (lt_trans zero_lt_one hQ) _)
      (Real.rpow_pos_of_pos (lt_trans zero_lt_one hQ) _))
      (Real.rpow_pos_of_pos (lt_trans zero_lt_one hQ) _)
  · intro s
    exact original_triple_mem4 A₂ A₃ Q c₂ c₃ (u (tripleIndex4 s 0)) (u (tripleIndex4 s 1)) (u (tripleIndex4 s 2))
  · intro s
    exact (originalCoordinates4_bounds (compound3Matrix4 L) (compound3_unit L hLu)
      Q hQ (tripleWeights4 c₀) _ _).mp (hg s)

end CompoundFeasibility.Exterior3
