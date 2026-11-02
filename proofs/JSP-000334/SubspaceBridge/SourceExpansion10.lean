import SubspaceBridge.SourceAuxiliary10
open scoped BigOperators Matrix Classical
noncomputable section
namespace CompoundFeasibility.Auxiliary10.SourceExpansion10
open SourceMultiblock10 SourceNormalHighIndex10 SchmidtPolynomial10 Aux6Mass

def linearChart {K : Type*} [CommRing K] {m : ℕ}
    (B : Matrix (Fin 10) (Fin 10) K) (u : Vars10 m) : MvPolynomial (Vars10 m) K :=
  ∑ j : Fin 10, MvPolynomial.C (B u.2 j) * MvPolynomial.X (u.1,j)

def substitution {K : Type*} [CommRing K] {m : ℕ}
    (B : Matrix (Fin 10) (Fin 10) K) :
    MvPolynomial (Vars10 m) K →+* MvPolynomial (Vars10 m) K :=
  MvPolynomial.eval₂Hom MvPolynomial.C (linearChart B)

def expansion {K : Type*} [Field K] {m : ℕ}
    (A : Matrix (Fin 10) (Fin 10) K) (J : Vars10 m →₀ ℕ)
    (P : MvPolynomial (Vars10 m) ℤ) : MvPolynomial (Vars10 m) K :=
  substitution A⁻¹ (derivative10 J (P.map (Int.castRingHom K)))

theorem chart_one {K : Type*} [CommRing K] {m : ℕ} (u : Vars10 m) :
    linearChart (1 : Matrix (Fin 10) (Fin 10) K) u = MvPolynomial.X u := by
  simp [linearChart, Matrix.one_apply, mul_ite, Finset.sum_ite_eq, Finset.sum_ite_eq']

theorem chart_comp {K : Type*} [CommRing K] {m : ℕ}
    (A B : Matrix (Fin 10) (Fin 10) K) (u : Vars10 m) :
    substitution A (linearChart B u) = linearChart (B * A) u := by
  simp only [linearChart, substitution, map_sum, map_mul,
    MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X']
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Matrix.mul_apply]
  rw [map_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_mul]
  ring

theorem substitution_comp {K : Type*} [CommRing K] {m : ℕ}
    (A B : Matrix (Fin 10) (Fin 10) K) (P : MvPolynomial (Vars10 m) K) :
    substitution A (substitution B P) = substitution (B * A) P := by
  have he : (substitution (m := m) A).comp (substitution B) = substitution (B * A) := by
    apply MvPolynomial.ringHom_ext
    · intro c; simp [substitution]
    · intro u
      simp only [RingHom.comp_apply, substitution, MvPolynomial.eval₂Hom_X']
      exact chart_comp A B u
  exact congrArg (fun f => f P) he

theorem substitution_one {K : Type*} [CommRing K] {m : ℕ}
    (P : MvPolynomial (Vars10 m) K) : substitution 1 P = P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [substitution]
  | add P Q hP hQ => simp [hP, hQ]
  | mul_X P u hP =>
    rw [map_mul, hP]
    simp [substitution, chart_one]

theorem reconstruct {K : Type*} [Field K] {m : ℕ}
    (A : Matrix (Fin 10) (Fin 10) K) (hA : A.det ≠ 0)
    (J : Vars10 m →₀ ℕ) (P : MvPolynomial (Vars10 m) ℤ) :
    substitution A (expansion A J P) = derivative10 J (P.map (Int.castRingHom K)) := by
  rw [expansion, substitution_comp, Matrix.nonsing_inv_mul A (isUnit_iff_ne_zero.mpr hA),
    substitution_one]

theorem unique {K : Type*} [Field K] {m : ℕ}
    (A : Matrix (Fin 10) (Fin 10) K) (hA : A.det ≠ 0)
    (J : Vars10 m →₀ ℕ) (P : MvPolynomial (Vars10 m) ℤ)
    (Q : MvPolynomial (Vars10 m) K)
    (hQ : substitution A Q = derivative10 J (P.map (Int.castRingHom K))) :
    Q = expansion A J P := by
  have he := congrArg (substitution A⁻¹) hQ
  rw [substitution_comp, Matrix.mul_nonsing_inv A (isUnit_iff_ne_zero.mpr hA),
    substitution_one] at he
  exact he

theorem chart_mass {K : Type*} [NormedField K] {m : ℕ}
    (B : Matrix (Fin 10) (Fin 10) K) (G : ℝ)
    (hB : ∀ i j, ‖B i j‖ ≤ G) (u : Vars10 m) : mass (linearChart B u) ≤ 10 * G := by
  calc
    _ ≤ ∑ j : Fin 10, mass (MvPolynomial.C (B u.2 j) * MvPolynomial.X (u.1,j)) := mass_sum _ _
    _ ≤ ∑ _j : Fin 10, G := by
      apply Finset.sum_le_sum
      intro j _
      rw [mass_C_mul_X]
      exact hB _ _
    _ = _ := by simp

theorem monomial_mass {K : Type*} [NormedField K] {m : ℕ} {r : Fin m → ℕ}
    (A : Matrix (Fin 10) (Fin 10) K) (G : ℝ) (hG : 1 ≤ G)
    (hentry : ∀ i j, ‖A⁻¹ i j‖ ≤ G)
    (b : RothAuxCoefficients r) (J : Vars10 m →₀ ℕ) (c : ℤ) :
    mass (expansion A J (MvPolynomial.monomial (exponent10 b) c)) ≤
      (c.natAbs : ℝ) * (20 * G) ^ (∑ h, r h) := by
  let R := ∑ h, r h
  have hbase : 1 ≤ 10 * G := by linarith
  have hsum : (∑ u : Vars10 m, (exponent10 b - J) u) ≤ R := by
    change (∑ u : Vars10 m, (exponent10 b - J) u) ≤ ∑ h, r h
    rw [← exponent10_sum b]
    exact Finset.sum_le_sum (fun u _ => Nat.sub_le _ _)
  have hprod : mass (∏ u : Vars10 m, linearChart A⁻¹ u ^ (exponent10 b - J) u) ≤ (10 * G) ^ R := by
    calc
      _ ≤ ∏ u : Vars10 m, mass (linearChart A⁻¹ u ^ (exponent10 b - J) u) := mass_prod _ _
      _ ≤ ∏ u : Vars10 m, (10 * G) ^ (exponent10 b - J) u := by
        apply Finset.prod_le_prod
        · intro u _; exact mass_nonneg _
        · intro u _
          exact (mass_pow _ _).trans
            (pow_le_pow_left₀ (mass_nonneg _) (chart_mass A⁻¹ G hentry u) _)
      _ = (10 * G) ^ (∑ u : Vars10 m, (exponent10 b - J) u) := Finset.prod_pow_eq_pow_sum _ _ _
      _ ≤ _ := pow_le_pow_right₀ hbase hsum
  have hc : ‖(c : K)‖ ≤ (c.natAbs : ℝ) := by
    simpa only [zsmul_eq_mul, mul_one, norm_one, Int.norm_eq_abs, Int.cast_abs, Int.cast_natAbs] using (norm_zsmul_le (n := c) (a := (1 : K)))
  have he : expansion A J (MvPolynomial.monomial (exponent10 b) c) =
      MvPolynomial.C ((c : K) * ∏ u : Vars10 m, (Nat.choose (exponent10 b u) (J u) : K)) *
        ∏ u : Vars10 m, linearChart A⁻¹ u ^ (exponent10 b - J) u := by
    rw [expansion, MvPolynomial.map_monomial, derivative10_monomial, substitution,
      MvPolynomial.eval₂Hom_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
    rfl
  rw [he]
  calc
    _ ≤ mass (MvPolynomial.C ((c : K) * ∏ u : Vars10 m,
        (Nat.choose (exponent10 b u) (J u) : K))) *
        mass (∏ u : Vars10 m, linearChart A⁻¹ u ^ (exponent10 b - J) u) := mass_mul _ _
    _ ≤ ((c.natAbs : ℝ) * (2 : ℝ)^R) * (10 * G)^R := by
      apply mul_le_mul
      · rw [MvPolynomial.C_apply, mass_monomial]
        exact (norm_mul_le _ _).trans
          (mul_le_mul hc (Aux10Height.binomial_norm10 b J) (norm_nonneg _) (Nat.cast_nonneg _))
      · exact hprod
      · exact mass_nonneg _
      · positivity
    _ = _ := by rw [mul_assoc, ← mul_pow]; congr 2; ring



theorem support_index {m : ℕ} (r : Fin m → ℕ)
    (P : MvPolynomial (Vars10 m) ℤ) (hP : homogeneous10 r P)
    (d : Vars10 m →₀ ℕ) (hd : d ∈ P.support) :
    ∃ b : RothAuxCoefficients r, exponent10 b = d := by
  have hle (h : Fin m) (i : Fin 10) : d (h,i) ≤ r h := by
    rw [← hP d hd h]
    exact Finset.single_le_sum (f := fun j : Fin 10 => d (h,j)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  refine ⟨fun h => ⟨fun i => ⟨d (h,i), by have hh := hle h i; omega⟩, hP d hd h⟩, ?_⟩
  ext u
  rfl

theorem support_card {m : ℕ} (r : Fin m → ℕ) (hr : ∀ h, 0 < r h)
    (P : MvPolynomial (Vars10 m) ℤ) (hP : homogeneous10 r P) :
    P.support.card ≤ 1024 ^ (∑ h, r h) := by
  have hs : P.support ⊆ Finset.univ.image (@exponent10 m r) := by
    intro d hd
    obtain ⟨b,hb⟩ := support_index r P hP d hd
    exact Finset.mem_image.mpr ⟨b,Finset.mem_univ _,hb⟩
  calc
    _ ≤ (Finset.univ.image (@exponent10 m r)).card := Finset.card_le_card hs
    _ ≤ Fintype.card (RothAuxCoefficients r) := Finset.card_image_le
    _ ≤ _ := dimension10_le_pow r hr

theorem expansion_sum {K : Type*} [Field K] {m : ℕ}
    (A : Matrix (Fin 10) (Fin 10) K) (J : Vars10 m →₀ ℕ)
    (P : MvPolynomial (Vars10 m) ℤ) :
    expansion A J P = ∑ d ∈ P.support, expansion A J (MvPolynomial.monomial d (P.coeff d)) := by
  unfold expansion
  rw [← derivative10_map, derivative10, MvPolynomial.sum_def, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro d hd
  simp only [MvPolynomial.map_monomial, derivative10_monomial, map_mul, map_prod, map_natCast]

theorem coefficient_bound {K : Type*} [NormedField K] {m : ℕ}
    (r : Fin m → ℕ) (hr : ∀ h, 0 < r h)
    (P : MvPolynomial (Vars10 m) ℤ) (hP : homogeneous10 r P)
    (D : ℝ) (hD : 1 ≤ D) (hheight : (height10 P : ℝ) ≤ D ^ (∑ h, r h))
    (A : Matrix (Fin 10) (Fin 10) K) (G : ℝ) (hG : 1 ≤ G)
    (hentry : ∀ i j, ‖A⁻¹ i j‖ ≤ G) (J b : Vars10 m →₀ ℕ) :
    ‖(expansion A J P).coeff b‖ ≤ (20480 * D * G) ^ (∑ h, r h) := by
  have hDpos : 0 ≤ D := by linarith
  have hGpos : 0 ≤ G := by linarith
  apply (coeff_le_mass _ _).trans
  rw [expansion_sum]
  calc
    _ ≤ ∑ d ∈ P.support, mass (expansion A J (MvPolynomial.monomial d (P.coeff d))) := mass_sum _ _
    _ ≤ ∑ _d ∈ P.support, D^(∑ h, r h) * (20 * G)^(∑ h, r h) := by
      apply Finset.sum_le_sum
      intro d hd
      obtain ⟨a,ha⟩ := support_index r P hP d hd
      have hc : ((P.coeff d).natAbs : ℝ) ≤ D^(∑ h, r h) := by
        have hh : (P.coeff d).natAbs ≤ height10 P := Finset.le_sup (f := fun e => (P.coeff e).natAbs) hd
        exact (by exact_mod_cast hh : ((P.coeff d).natAbs : ℝ) ≤ (height10 P : ℝ)).trans hheight
      have hm := monomial_mass A G hG hentry a J (P.coeff d)
      rw [ha] at hm
      exact hm.trans (mul_le_mul_of_nonneg_right hc (by positivity))
    _ = (P.support.card : ℝ) * (D^(∑ h, r h) * (20 * G)^(∑ h, r h)) := by simp
    _ ≤ (1024 : ℝ)^(∑ h, r h) * (D^(∑ h, r h) * (20 * G)^(∑ h, r h)) := by
      have hc : (P.support.card : ℝ) ≤ (1024 : ℝ)^(∑ h, r h) := by exact_mod_cast support_card r hr P hP
      exact mul_le_mul_of_nonneg_right hc (by positivity)
    _ = _ := by rw [← mul_pow, ← mul_pow]; congr 1; ring



def inverseBudget {K : Type*} [NormedField K] (A : Matrix (Fin 10) (Fin 10) K) : ℝ :=
  1 + ∑ i : Fin 10, ∑ j : Fin 10, ‖A⁻¹ i j‖

theorem inverseBudget_one {K : Type*} [NormedField K]
    (A : Matrix (Fin 10) (Fin 10) K) : 1 ≤ inverseBudget A := by
  unfold inverseBudget
  exact le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => norm_nonneg _)))

theorem inverseBudget_entry {K : Type*} [NormedField K]
    (A : Matrix (Fin 10) (Fin 10) K) (i j : Fin 10) : ‖A⁻¹ i j‖ ≤ inverseBudget A := by
  have hrow : ‖A⁻¹ i j‖ ≤ ∑ k : Fin 10, ‖A⁻¹ i k‖ :=
    Finset.single_le_sum (fun _ _ => norm_nonneg _) (Finset.mem_univ j)
  have hall : (∑ k : Fin 10, ‖A⁻¹ i k‖) ≤ ∑ h : Fin 10, ∑ k : Fin 10, ‖A⁻¹ h k‖ :=
    Finset.single_le_sum (fun _ _ => Finset.sum_nonneg (fun _ _ => norm_nonneg _)) (Finset.mem_univ i)
  unfold inverseBudget
  linarith

theorem source_coefficient_bounds (A2 A3 : Matrix (Fin 10) (Fin 10) ℚ)
    (L : Matrix (Fin 10) (Fin 10) ℝ) (D : ℝ) (hD : 1 ≤ D) :
    ∃ E : ℝ, 1 ≤ E ∧ ∀ (m : ℕ) (r : Fin m → ℕ), (∀ h, 0 < r h) →
      ∀ P : MvPolynomial (Vars10 m) ℤ, homogeneous10 r P →
      (height10 P : ℝ) ≤ D^(∑ h, r h) → ∀ J b : Vars10 m →₀ ℕ,
      ‖(expansion L J P).coeff b‖ ≤ E^(∑ h, r h) ∧
      ‖(expansion (SourceForms10.finiteMatrix10 2 A2) J P).coeff b‖ ≤ E^(∑ h, r h) ∧
      ‖(expansion (SourceForms10.finiteMatrix10 3 A3) J P).coeff b‖ ≤ E^(∑ h, r h) := by
  let G := max (inverseBudget L)
    (max (inverseBudget (SourceForms10.finiteMatrix10 2 A2)) (inverseBudget (SourceForms10.finiteMatrix10 3 A3)))
  have h0 : inverseBudget L ≤ G := le_max_left _ _
  have h2 : inverseBudget (SourceForms10.finiteMatrix10 2 A2) ≤ G := (le_max_left _ _).trans (le_max_right _ _)
  have h3 : inverseBudget (SourceForms10.finiteMatrix10 3 A3) ≤ G := (le_max_right _ _).trans (le_max_right _ _)
  have hG : 1 ≤ G := (inverseBudget_one _).trans h0
  refine ⟨20480 * D * G, by nlinarith, ?_⟩
  intro m r hr P hP hheight J b
  exact ⟨coefficient_bound r hr P hP D hD hheight _ G hG
      (fun i j => (inverseBudget_entry _ i j).trans h0) J b,
    coefficient_bound r hr P hP D hD hheight _ G hG
      (fun i j => (inverseBudget_entry _ i j).trans h2) J b,
    coefficient_bound r hr P hP D hD hheight _ G hG
      (fun i j => (inverseBudget_entry _ i j).trans h3) J b⟩


end CompoundFeasibility.Auxiliary10.SourceExpansion10
