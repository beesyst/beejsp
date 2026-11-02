import SubspaceBridge.AuxiliaryFeasibility6
import Mathlib.NumberTheory.Padics.PadicNumbers

open scoped BigOperators Matrix Classical
noncomputable section
namespace CompoundFeasibility.Auxiliary6.SourceExpansion
open Aux6Mass

def linearChart {K : Type*} [CommRing K] {m : ℕ}
    (B : Matrix (Fin 6) (Fin 6) K) (u : Vars6 m) : MvPolynomial (Vars6 m) K :=
  ∑ j : Fin 6, MvPolynomial.C (B u.2 j) * MvPolynomial.X (u.1,j)

def substitution {K : Type*} [CommRing K] {m : ℕ}
    (B : Matrix (Fin 6) (Fin 6) K) :
    MvPolynomial (Vars6 m) K →+* MvPolynomial (Vars6 m) K :=
  MvPolynomial.eval₂Hom MvPolynomial.C (linearChart B)

def expansion {K : Type*} [Field K] {m : ℕ}
    (A : Matrix (Fin 6) (Fin 6) K) (J : Vars6 m →₀ ℕ)
    (P : MvPolynomial (Vars6 m) ℤ) : MvPolynomial (Vars6 m) K :=
  substitution A⁻¹ (derivative6 J (P.map (Int.castRingHom K)))

theorem chart_one {K : Type*} [CommRing K] {m : ℕ} (u : Vars6 m) :
    linearChart (1 : Matrix (Fin 6) (Fin 6) K) u = MvPolynomial.X u := by
  simp [linearChart, Matrix.one_apply, mul_ite, Finset.sum_ite_eq, Finset.sum_ite_eq']

theorem chart_comp {K : Type*} [CommRing K] {m : ℕ}
    (A B : Matrix (Fin 6) (Fin 6) K) (u : Vars6 m) :
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
    (A B : Matrix (Fin 6) (Fin 6) K) (P : MvPolynomial (Vars6 m) K) :
    substitution A (substitution B P) = substitution (B * A) P := by
  have he : (substitution (m := m) A).comp (substitution B) = substitution (B * A) := by
    apply MvPolynomial.ringHom_ext
    · intro c; simp [substitution]
    · intro u
      simp only [RingHom.comp_apply, substitution, MvPolynomial.eval₂Hom_X']
      exact chart_comp A B u
  exact congrArg (fun f => f P) he

theorem substitution_one {K : Type*} [CommRing K] {m : ℕ}
    (P : MvPolynomial (Vars6 m) K) : substitution 1 P = P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [substitution]
  | add P Q hP hQ => simp [hP, hQ]
  | mul_X P u hP =>
    rw [map_mul, hP]
    simp [substitution, chart_one]

theorem reconstruct {K : Type*} [Field K] {m : ℕ}
    (A : Matrix (Fin 6) (Fin 6) K) (hA : A.det ≠ 0)
    (J : Vars6 m →₀ ℕ) (P : MvPolynomial (Vars6 m) ℤ) :
    substitution A (expansion A J P) = derivative6 J (P.map (Int.castRingHom K)) := by
  rw [expansion, substitution_comp, Matrix.nonsing_inv_mul A (isUnit_iff_ne_zero.mpr hA),
    substitution_one]

theorem unique {K : Type*} [Field K] {m : ℕ}
    (A : Matrix (Fin 6) (Fin 6) K) (hA : A.det ≠ 0)
    (J : Vars6 m →₀ ℕ) (P : MvPolynomial (Vars6 m) ℤ)
    (Q : MvPolynomial (Vars6 m) K)
    (hQ : substitution A Q = derivative6 J (P.map (Int.castRingHom K))) :
    Q = expansion A J P := by
  have he := congrArg (substitution A⁻¹) hQ
  rw [substitution_comp, Matrix.mul_nonsing_inv A (isUnit_iff_ne_zero.mpr hA),
    substitution_one] at he
  exact he

theorem chart_mass {K : Type*} [NormedField K] {m : ℕ}
    (B : Matrix (Fin 6) (Fin 6) K) (G : ℝ)
    (hB : ∀ i j, ‖B i j‖ ≤ G) (u : Vars6 m) : mass (linearChart B u) ≤ 6 * G := by
  calc
    _ ≤ ∑ j : Fin 6, mass (MvPolynomial.C (B u.2 j) * MvPolynomial.X (u.1,j)) := mass_sum _ _
    _ ≤ ∑ _j : Fin 6, G := by
      apply Finset.sum_le_sum
      intro j _
      rw [mass_C_mul_X]
      exact hB _ _
    _ = _ := by simp

theorem monomial_mass {K : Type*} [NormedField K] {m : ℕ} {r : Fin m → ℕ}
    (A : Matrix (Fin 6) (Fin 6) K) (G : ℝ) (hG : 1 ≤ G)
    (hentry : ∀ i j, ‖A⁻¹ i j‖ ≤ G)
    (b : RothAuxCoefficients r) (J : Vars6 m →₀ ℕ) (c : ℤ) :
    mass (expansion A J (MvPolynomial.monomial (exponent6 b) c)) ≤
      (c.natAbs : ℝ) * (12 * G) ^ (∑ h, r h) := by
  let R := ∑ h, r h
  have hbase : 1 ≤ 6 * G := by linarith
  have hsum : (∑ u : Vars6 m, (exponent6 b - J) u) ≤ R := by
    change (∑ u : Vars6 m, (exponent6 b - J) u) ≤ ∑ h, r h
    rw [← exponent6_sum b]
    exact Finset.sum_le_sum (fun u _ => Nat.sub_le _ _)
  have hprod : mass (∏ u : Vars6 m, linearChart A⁻¹ u ^ (exponent6 b - J) u) ≤ (6 * G) ^ R := by
    calc
      _ ≤ ∏ u : Vars6 m, mass (linearChart A⁻¹ u ^ (exponent6 b - J) u) := mass_prod _ _
      _ ≤ ∏ u : Vars6 m, (6 * G) ^ (exponent6 b - J) u := by
        apply Finset.prod_le_prod
        · intro u _; exact mass_nonneg _
        · intro u _
          exact (mass_pow _ _).trans
            (pow_le_pow_left₀ (mass_nonneg _) (chart_mass A⁻¹ G hentry u) _)
      _ = (6 * G) ^ (∑ u : Vars6 m, (exponent6 b - J) u) := Finset.prod_pow_eq_pow_sum _ _ _
      _ ≤ _ := pow_le_pow_right₀ hbase hsum
  have hc : ‖(c : K)‖ ≤ (c.natAbs : ℝ) := by
    simpa only [zsmul_eq_mul, mul_one, norm_one, Int.norm_eq_abs, Int.cast_abs, Int.cast_natAbs] using (norm_zsmul_le (n := c) (a := (1 : K)))
  have he : expansion A J (MvPolynomial.monomial (exponent6 b) c) =
      MvPolynomial.C ((c : K) * ∏ u : Vars6 m, (Nat.choose (exponent6 b u) (J u) : K)) *
        ∏ u : Vars6 m, linearChart A⁻¹ u ^ (exponent6 b - J) u := by
    rw [expansion, MvPolynomial.map_monomial, derivative6_monomial, substitution,
      MvPolynomial.eval₂Hom_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
    rfl
  rw [he]
  calc
    _ ≤ mass (MvPolynomial.C ((c : K) * ∏ u : Vars6 m,
        (Nat.choose (exponent6 b u) (J u) : K))) *
        mass (∏ u : Vars6 m, linearChart A⁻¹ u ^ (exponent6 b - J) u) := mass_mul _ _
    _ ≤ ((c.natAbs : ℝ) * (2 : ℝ)^R) * (6 * G)^R := by
      apply mul_le_mul
      · rw [MvPolynomial.C_apply, mass_monomial]
        exact (norm_mul_le _ _).trans
          (mul_le_mul hc (Aux6Height.binomial_norm6 b J) (norm_nonneg _) (Nat.cast_nonneg _))
      · exact hprod
      · exact mass_nonneg _
      · positivity
    _ = _ := by rw [mul_assoc, ← mul_pow]; congr 2; ring



theorem support_index {m : ℕ} (r : Fin m → ℕ)
    (P : MvPolynomial (Vars6 m) ℤ) (hP : homogeneous6 r P)
    (d : Vars6 m →₀ ℕ) (hd : d ∈ P.support) :
    ∃ b : RothAuxCoefficients r, exponent6 b = d := by
  have hle (h : Fin m) (i : Fin 6) : d (h,i) ≤ r h := by
    rw [← hP d hd h]
    exact Finset.single_le_sum (f := fun j : Fin 6 => d (h,j)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  refine ⟨fun h => ⟨fun i => ⟨d (h,i), by have hh := hle h i; omega⟩, hP d hd h⟩, ?_⟩
  ext u
  rfl

theorem support_card {m : ℕ} (r : Fin m → ℕ) (hr : ∀ h, 0 < r h)
    (P : MvPolynomial (Vars6 m) ℤ) (hP : homogeneous6 r P) :
    P.support.card ≤ 64 ^ (∑ h, r h) := by
  have hs : P.support ⊆ Finset.univ.image (@exponent6 m r) := by
    intro d hd
    obtain ⟨b,hb⟩ := support_index r P hP d hd
    exact Finset.mem_image.mpr ⟨b,Finset.mem_univ _,hb⟩
  calc
    _ ≤ (Finset.univ.image (@exponent6 m r)).card := Finset.card_le_card hs
    _ ≤ Fintype.card (RothAuxCoefficients r) := Finset.card_image_le
    _ ≤ _ := dimension6_le_pow r hr

theorem expansion_sum {K : Type*} [Field K] {m : ℕ}
    (A : Matrix (Fin 6) (Fin 6) K) (J : Vars6 m →₀ ℕ)
    (P : MvPolynomial (Vars6 m) ℤ) :
    expansion A J P = ∑ d ∈ P.support, expansion A J (MvPolynomial.monomial d (P.coeff d)) := by
  unfold expansion
  rw [← derivative6_map, derivative6, MvPolynomial.sum_def, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro d hd
  simp only [MvPolynomial.map_monomial, derivative6_monomial, map_mul, map_prod, map_natCast]

theorem coefficient_bound {K : Type*} [NormedField K] {m : ℕ}
    (r : Fin m → ℕ) (hr : ∀ h, 0 < r h)
    (P : MvPolynomial (Vars6 m) ℤ) (hP : homogeneous6 r P)
    (D : ℝ) (hD : 1 ≤ D) (hheight : (height6 P : ℝ) ≤ D ^ (∑ h, r h))
    (A : Matrix (Fin 6) (Fin 6) K) (G : ℝ) (hG : 1 ≤ G)
    (hentry : ∀ i j, ‖A⁻¹ i j‖ ≤ G) (J b : Vars6 m →₀ ℕ) :
    ‖(expansion A J P).coeff b‖ ≤ (768 * D * G) ^ (∑ h, r h) := by
  have hDpos : 0 ≤ D := by linarith
  have hGpos : 0 ≤ G := by linarith
  apply (coeff_le_mass _ _).trans
  rw [expansion_sum]
  calc
    _ ≤ ∑ d ∈ P.support, mass (expansion A J (MvPolynomial.monomial d (P.coeff d))) := mass_sum _ _
    _ ≤ ∑ _d ∈ P.support, D^(∑ h, r h) * (12*G)^(∑ h, r h) := by
      apply Finset.sum_le_sum
      intro d hd
      obtain ⟨a,ha⟩ := support_index r P hP d hd
      have hc : ((P.coeff d).natAbs : ℝ) ≤ D^(∑ h, r h) := by
        have hh : (P.coeff d).natAbs ≤ height6 P := Finset.le_sup (f := fun e => (P.coeff e).natAbs) hd
        exact (by exact_mod_cast hh : ((P.coeff d).natAbs : ℝ) ≤ (height6 P : ℝ)).trans hheight
      have hm := monomial_mass A G hG hentry a J (P.coeff d)
      rw [ha] at hm
      exact hm.trans (mul_le_mul_of_nonneg_right hc (by positivity))
    _ = (P.support.card : ℝ) * (D^(∑ h, r h) * (12*G)^(∑ h, r h)) := by simp
    _ ≤ (64 : ℝ)^(∑ h, r h) * (D^(∑ h, r h) * (12*G)^(∑ h, r h)) := by
      have hc : (P.support.card : ℝ) ≤ (64 : ℝ)^(∑ h, r h) := by exact_mod_cast support_card r hr P hP
      exact mul_le_mul_of_nonneg_right hc (by positivity)
    _ = _ := by rw [← mul_pow, ← mul_pow]; congr 1; ring



def finiteMatrix (p : ℕ) [Fact p.Prime] (A : Matrix (Fin 4) (Fin 4) ℚ) :
    Matrix (Fin 6) (Fin 6) ℚ_[p] := (compound A).map (algebraMap ℚ ℚ_[p])

def inverseBudget {K : Type*} [NormedField K] (A : Matrix (Fin 6) (Fin 6) K) : ℝ :=
  1 + ∑ i : Fin 6, ∑ j : Fin 6, ‖A⁻¹ i j‖

theorem inverseBudget_one {K : Type*} [NormedField K]
    (A : Matrix (Fin 6) (Fin 6) K) : 1 ≤ inverseBudget A := by
  unfold inverseBudget
  exact le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => norm_nonneg _)))

theorem inverseBudget_entry {K : Type*} [NormedField K]
    (A : Matrix (Fin 6) (Fin 6) K) (i j : Fin 6) : ‖A⁻¹ i j‖ ≤ inverseBudget A := by
  have hrow : ‖A⁻¹ i j‖ ≤ ∑ k : Fin 6, ‖A⁻¹ i k‖ :=
    Finset.single_le_sum (fun _ _ => norm_nonneg _) (Finset.mem_univ j)
  have hall : (∑ k : Fin 6, ‖A⁻¹ i k‖) ≤ ∑ h : Fin 6, ∑ k : Fin 6, ‖A⁻¹ h k‖ :=
    Finset.single_le_sum (fun _ _ => Finset.sum_nonneg (fun _ _ => norm_nonneg _)) (Finset.mem_univ i)
  unfold inverseBudget
  linarith

theorem finite_norm (p : ℕ) [Fact p.Prime] (q : ℚ) :
    ‖(algebraMap ℚ ℚ_[p]) q‖ = padicNorm p q := by
  exact padicNormE.eq_padicNorm _

theorem source_coefficient_bounds (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (D : ℝ) (hD : 1 ≤ D) :
    ∃ E : ℝ, 1 ≤ E ∧ ∀ (m : ℕ) (r : Fin m → ℕ), (∀ h, 0 < r h) →
      ∀ P : MvPolynomial (Vars6 m) ℤ, homogeneous6 r P →
      (height6 P : ℝ) ≤ D^(∑ h, r h) → ∀ J b : Vars6 m →₀ ℕ,
      ‖(expansion (compound L) J P).coeff b‖ ≤ E^(∑ h, r h) ∧
      ‖(expansion (finiteMatrix 2 A2) J P).coeff b‖ ≤ E^(∑ h, r h) ∧
      ‖(expansion (finiteMatrix 3 A3) J P).coeff b‖ ≤ E^(∑ h, r h) := by
  let G := max (inverseBudget (compound L))
    (max (inverseBudget (finiteMatrix 2 A2)) (inverseBudget (finiteMatrix 3 A3)))
  have h0 : inverseBudget (compound L) ≤ G := le_max_left _ _
  have h2 : inverseBudget (finiteMatrix 2 A2) ≤ G := (le_max_left _ _).trans (le_max_right _ _)
  have h3 : inverseBudget (finiteMatrix 3 A3) ≤ G := (le_max_right _ _).trans (le_max_right _ _)
  have hG : 1 ≤ G := (inverseBudget_one _).trans h0
  refine ⟨768 * D * G, by nlinarith, ?_⟩
  intro m r hr P hP hheight J b
  exact ⟨coefficient_bound r hr P hP D hD hheight _ G hG
      (fun i j => (inverseBudget_entry _ i j).trans h0) J b,
    coefficient_bound r hr P hP D hD hheight _ G hG
      (fun i j => (inverseBudget_entry _ i j).trans h2) J b,
    coefficient_bound r hr P hP D hD hheight _ G hG
      (fun i j => (inverseBudget_entry _ i j).trans h3) J b⟩

end CompoundFeasibility.Auxiliary6.SourceExpansion
