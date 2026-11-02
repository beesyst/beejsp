import SubspaceBridge.BinaryLocalIndex2
open scoped BigOperators Classical
namespace JSP000334
noncomputable def binaryLocalInverseBound
    (L : Fin 3 → Matrix (Fin 2) (Fin 2) ℤ) : ℝ :=
  max 1 (Finset.univ.sup' Finset.univ_nonempty
    (fun u : Fin 3 × Fin 2 × Fin 2 =>
      rothLocalAbs u.1 ((binaryLocalRationalMatrix (L u.1))⁻¹ u.2.1 u.2.2)))

theorem binaryLocalInverseBound_one_le (L : Fin 3 → Matrix (Fin 2) (Fin 2) ℤ) :
    1 ≤ binaryLocalInverseBound L := le_max_left _ _

theorem binaryLocalInverseBound_entry (L : Fin 3 → Matrix (Fin 2) (Fin 2) ℤ)
    (tau : Fin 3) (i j : Fin 2) :
    rothLocalAbs tau ((binaryLocalRationalMatrix (L tau))⁻¹ i j) ≤ binaryLocalInverseBound L := by
  exact (Finset.le_sup' (fun u : Fin 3 × Fin 2 × Fin 2 =>
    rothLocalAbs u.1 ((binaryLocalRationalMatrix (L u.1))⁻¹ u.2.1 u.2.2))
      (Finset.mem_univ (tau,i,j))).trans (le_max_right _ _)

theorem binaryLocal_chart_mass {m : ℕ} (tau : Fin 3) (B : Matrix (Fin 2) (Fin 2) ℚ)
    (G : ℝ) (hB : ∀ i j, rothLocalAbs tau (B i j) ≤ G) (u : RothBlockVars2 m) :
    rothLocalMass tau (binaryLocalLinearChart B u) ≤ 2 * G := by
  calc
    _ ≤ ∑ j : Fin 2, rothLocalMass tau (MvPolynomial.C (B u.2 j) * MvPolynomial.X (u.1,j)) :=
      rothLocalMass_sum _ _ _
    _ ≤ ∑ _j : Fin 2, G := by
      apply Finset.sum_le_sum
      intro j _
      rw [rothLocalMass_C_mul_X]
      exact hB _ _
    _ = _ := by simp

theorem binaryLocal_support_index {m : ℕ} (r : Fin m → ℕ)
    (P : MvPolynomial (RothBlockVars2 m) ℤ) (hP : binaryBlockHomogeneous r P)
    (d : RothBlockVars2 m →₀ ℕ) (hd : d ∈ P.support) :
    ∃ b : BinaryAuxCoefficients r, binaryAuxExponent b = d := by
  classical
  have hdeg := hP d hd
  have hle (h : Fin m) : d (h,0) ≤ r h := by
    have hh := hdeg h
    rw [Fin.sum_univ_two] at hh
    omega
  refine ⟨fun h => ⟨d (h,0), by have hh := hle h; omega⟩, ?_⟩
  ext ⟨h,i⟩
  have hh := hdeg h
  rw [Fin.sum_univ_two] at hh
  fin_cases i <;> simp [binaryAuxExponent] <;> omega

theorem binaryLocal_support_card {m : ℕ} (r : Fin m → ℕ)
    (P : MvPolynomial (RothBlockVars2 m) ℤ) (hP : binaryBlockHomogeneous r P) :
    P.support.card ≤ 2 ^ (∑ h, r h) := by
  classical
  have hs : P.support ⊆ Finset.univ.image (@binaryAuxExponent m r) := by
    intro d hd
    obtain ⟨b,hb⟩ := binaryLocal_support_index r P hP d hd
    exact Finset.mem_image.mpr ⟨b,Finset.mem_univ _,hb⟩
  calc
    _ ≤ (Finset.univ.image (@binaryAuxExponent m r)).card := Finset.card_le_card hs
    _ ≤ Fintype.card (BinaryAuxCoefficients r) := by simpa using Finset.card_image_le (s := Finset.univ) (f := @binaryAuxExponent m r)
    _ ≤ _ := binary_dimension_pow_bound r


theorem binaryLocal_transformed_monomial_mass {m : ℕ} {r : Fin m → ℕ}
    (tau : Fin 3) (L : Matrix (Fin 2) (Fin 2) ℤ) (G : ℝ) (hG : 1 ≤ G)
    (hentry : ∀ i j, rothLocalAbs tau ((binaryLocalRationalMatrix L)⁻¹ i j) ≤ G)
    (b : BinaryAuxCoefficients r) (J : RothBlockVars2 m →₀ ℕ) (c : ℤ) :
    rothLocalMass tau (binaryLocalExpansion L J (MvPolynomial.monomial (binaryAuxExponent b) c)) ≤
      (c.natAbs : ℝ) * (4 * G) ^ (∑ h, r h) := by
  classical
  let R := ∑ h, r h
  let B := (binaryLocalRationalMatrix L)⁻¹
  let a : ℤ := ∏ u : RothBlockVars2 m, (Nat.choose (binaryAuxExponent b u) (J u) : ℤ)
  have hbase : 1 ≤ 2 * G := by linarith
  have hsum : (∑ u : RothBlockVars2 m, (binaryAuxExponent b - J) u) ≤ R := by
    change (∑ u : RothBlockVars2 m, (binaryAuxExponent b - J) u) ≤ ∑ h, r h
    rw [← binary_exponent_sum b]
    exact Finset.sum_le_sum (fun u _ => Nat.sub_le _ _)
  have hprod : rothLocalMass tau (∏ u : RothBlockVars2 m,
      binaryLocalLinearChart B u ^ (binaryAuxExponent b - J) u) ≤ (2 * G) ^ R := by
    calc
      _ ≤ ∏ u : RothBlockVars2 m,
          rothLocalMass tau (binaryLocalLinearChart B u ^ (binaryAuxExponent b - J) u) :=
        rothLocalMass_prod _ _ _
      _ ≤ ∏ u : RothBlockVars2 m, (2 * G) ^ (binaryAuxExponent b - J) u := by
        apply Finset.prod_le_prod
        · intro u _; exact rothLocalMass_nonneg _ _
        · intro u _
          exact (rothLocalMass_pow tau _ _).trans
            (pow_le_pow_left₀ (rothLocalMass_nonneg _ _) (binaryLocal_chart_mass tau B G hentry u) _)
      _ = (2 * G) ^ (∑ u : RothBlockVars2 m, (binaryAuxExponent b - J) u) :=
        Finset.prod_pow_eq_pow_sum _ _ _
      _ ≤ _ := pow_le_pow_right₀ hbase hsum
  have hbin : rothLocalAbs tau (a : ℚ) ≤ (2 : ℝ) ^ R := by
    have h := binary_binomial_bound b J
    change |a| ≤ (2 : ℤ) ^ R at h
    rw [← Int.natCast_natAbs] at h
    have h' : (a.natAbs : ℝ) ≤ (2 : ℝ) ^ R := by exact_mod_cast h
    exact (rothLocalAbs_int tau a).trans h'
  have hconst : rothLocalAbs tau ((c * a : ℤ) : ℚ) ≤ (c.natAbs : ℝ) * (2 : ℝ) ^ R := by
    rw [Int.cast_mul, rothLocalAbs_mul]
    exact mul_le_mul (rothLocalAbs_int tau c) hbin (rothLocalAbs_nonneg _ _) (Nat.cast_nonneg _)
  have he : binaryLocalExpansion L J (MvPolynomial.monomial (binaryAuxExponent b) c) =
      MvPolynomial.C (((c * a : ℤ) : ℚ)) *
        ∏ u : RothBlockVars2 m, binaryLocalLinearChart B u ^ (binaryAuxExponent b - J) u := by
    rw [binaryLocalExpansion, binary_derivative_monomial, MvPolynomial.eval₂Hom_monomial,
      Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
    rfl
  rw [he]
  calc
    _ ≤ rothLocalMass tau (MvPolynomial.C (((c * a : ℤ) : ℚ))) *
        rothLocalMass tau (∏ u : RothBlockVars2 m,
          binaryLocalLinearChart B u ^ (binaryAuxExponent b - J) u) := rothLocalMass_mul _ _ _
    _ ≤ ((c.natAbs : ℝ) * (2 : ℝ) ^ R) * (2 * G) ^ R := by
      rw [rothLocalMass_C]
      exact mul_le_mul hconst hprod (rothLocalMass_nonneg _ _) (by positivity)
    _ = _ := by rw [mul_assoc, ← mul_pow]; congr 2; ring


theorem binaryLocal_expansion_coeff_bound {m : ℕ} (r : Fin m → ℕ)
    (P : MvPolynomial (RothBlockVars2 m) ℤ) (hP : binaryBlockHomogeneous r P)
    (D : ℝ) (hD : 1 ≤ D) (hheight : (binaryPolynomialHeight P : ℝ) ≤ D ^ (∑ h, r h))
    (tau : Fin 3) (L : Matrix (Fin 2) (Fin 2) ℤ) (G : ℝ) (hG : 1 ≤ G)
    (hentry : ∀ i j, rothLocalAbs tau ((binaryLocalRationalMatrix L)⁻¹ i j) ≤ G)
    (J b : RothBlockVars2 m →₀ ℕ) :
    rothLocalAbs tau ((binaryLocalExpansion L J P).coeff b) ≤
      (8 * D * G) ^ (∑ h, r h) := by
  classical
  let R := ∑ h, r h
  have hDpos : 0 ≤ D := le_trans (by norm_num) hD
  have hGpos : 0 ≤ G := le_trans (by norm_num) hG
  have hexp : binaryLocalExpansion L J P =
      ∑ d ∈ P.support, binaryLocalExpansion L J (MvPolynomial.monomial d (P.coeff d)) := by
    change MvPolynomial.eval₂Hom (Int.castRingHom _)
      (binaryLocalLinearChart (binaryLocalRationalMatrix L)⁻¹)
      (P.sum fun d c => MvPolynomial.monomial (d - J)
        (c * ∏ u : RothBlockVars2 m, (Nat.choose (d u) (J u) : ℤ))) = _
    rw [MvPolynomial.sum_def, map_sum]
    apply Finset.sum_congr rfl
    intro d hd
    rw [binaryLocalExpansion, binary_derivative_monomial]
  have hmass : rothLocalMass tau (binaryLocalExpansion L J P) ≤ (8 * D * G) ^ R := by
    rw [hexp]
    calc
      _ ≤ ∑ d ∈ P.support,
          rothLocalMass tau (binaryLocalExpansion L J (MvPolynomial.monomial d (P.coeff d))) :=
        rothLocalMass_sum _ _ _
      _ ≤ ∑ _d ∈ P.support, D ^ R * (4 * G) ^ R := by
        apply Finset.sum_le_sum
        intro d hd
        obtain ⟨a,ha⟩ := binaryLocal_support_index r P hP d hd
        have hc : ((P.coeff d).natAbs : ℝ) ≤ D ^ R := by
          have hnat : (P.coeff d).natAbs ≤ binaryPolynomialHeight P :=
            Finset.le_sup (f := fun e => (P.coeff e).natAbs) hd
          have hreal : ((P.coeff d).natAbs : ℝ) ≤ (binaryPolynomialHeight P : ℝ) := by
            exact_mod_cast hnat
          exact hreal.trans hheight
        have hm := binaryLocal_transformed_monomial_mass tau L G hG hentry a J (P.coeff d)
        rw [ha] at hm
        exact hm.trans (mul_le_mul_of_nonneg_right hc (by positivity))
      _ = (P.support.card : ℝ) * (D ^ R * (4 * G) ^ R) := by simp
      _ ≤ (2 : ℝ) ^ R * (D ^ R * (4 * G) ^ R) := by
        have hcard : (P.support.card : ℝ) ≤ (2 : ℝ) ^ R := by
          exact_mod_cast binaryLocal_support_card r P hP
        exact mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = _ := by rw [← mul_pow, ← mul_pow]; congr 1; ring
  exact (rothLocal_coeff_le_mass tau _ b).trans hmass


end JSP000334
