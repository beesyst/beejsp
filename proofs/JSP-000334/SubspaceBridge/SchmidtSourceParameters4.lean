import SubspaceBridge.SourceNormalHeight4
import SubspaceBridge.SchmidtParameters6
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SchmidtSourceParameters4
open SourceMultiblock4 SourceNormalIndex4 Auxiliary4 SchmidtNormalCoordinates4 SchmidtScalarReduction4
theorem eta_m_theta4 (delta : ℝ) (hd : 0 < delta) (hd1 : delta < 1)
    (K : IntermediateField ℚ ℝ) :
    ∃ eta theta : ℝ, ∃ m : ℕ, eta = delta/3456 ∧ theta = eta/2 ∧
      0 < eta ∧ eta < 1 ∧ 1728*eta < delta ∧ 0 < m ∧
      4*(eta^2)⁻¹*Real.log (24*(Module.finrank ℚ K : ℝ)) ≤ (m : ℝ) ∧
      0 < theta ∧ theta < 1/12 ∧ theta < (m : ℝ)*eta ∧ 0 < JSP000334.omega65 m theta := by
  let eta := delta/3456
  let theta := eta/2
  have he : 0 < eta := by dsimp [eta]; positivity
  obtain ⟨m,hm⟩ := exists_nat_gt (max 1 (4*(eta^2)⁻¹*Real.log (24*(Module.finrank ℚ K : ℝ))))
  have hm1 : (1 : ℝ) < m := lt_of_le_of_lt (le_max_left _ _) hm
  have hmn : 0 < m := by exact_mod_cast (lt_trans zero_lt_one hm1)
  have ht : 0 < theta := by dsimp [theta]; positivity
  refine ⟨eta,theta,m,rfl,rfl,he,?_,?_,hmn,
    (lt_of_le_of_lt (le_max_right _ _) hm).le,ht,?_,?_,JSP000334.omega65_pos m theta ht⟩
  · dsimp [eta]; linarith
  · dsimp [eta]; linarith
  · dsimp [theta,eta]; linarith
  · dsimp [theta]; nlinarith

theorem positive_gamma4 (alpha eta : ℝ) (ha : 0 < alpha) (he : 0 < eta) :
    ∃ gamma : ℝ, 0 < gamma ∧ gamma ≤ 3 ∧ 4*gamma*(1+eta) ≤ alpha ∧ 4*gamma ≤ alpha := by
  let gamma := min 1 (alpha/(4*(1+eta)))
  have hg : 0 < gamma := lt_min zero_lt_one (div_pos ha (by positivity))
  have hc : gamma ≤ alpha/(4*(1+eta)) := min_le_right _ _
  have hb : gamma*(4*(1+eta)) ≤ alpha := (le_div_iff₀ (by positivity)).mp hc
  refine ⟨gamma,hg,(min_le_left _ _).trans (by norm_num),?_,?_⟩
  · nlinarith
  · nlinarith [mul_pos hg he]

theorem height_comparison4 (m : ℕ) (hm : 0 < m) (alpha gamma : ℝ)
    (ha : 0 < alpha) (hg : 0 < gamma) (hcompat : 4*gamma ≤ alpha)
    (Q H : Fin m → ℝ) (hQ : ∀ h, 1 < Q h)
    (henv : ∀ h, Q h^alpha ≤ H h ∧ H h ≤ Q h^(4 : ℝ)) (r : Fin m → ℕ)
    (hbal : ∀ h, (r ⟨0,hm⟩ : ℝ)*Real.log (Q ⟨0,hm⟩) ≤ (r h : ℝ)*Real.log (Q h)) :
    ∀ h, H ⟨0,hm⟩^(gamma*(r ⟨0,hm⟩ : ℝ)) ≤ H h^(r h) := by
  simpa only [mul_comm] using JSP000334.parameter_roth_growth m hm alpha 4 gamma ha.le hg
    hcompat Q H hQ henv r hbal

theorem normal_budget4 (m : ℕ) (alpha omega gamma Q H : ℝ)
    (ho : 0 < omega) (hg : 0 < gamma) (hQ : 1 < Q) (henv : Q^alpha ≤ H)
    (hcut : (27*m : ℕ)*Real.log 2 ≤ alpha*omega*gamma*Real.log Q) :
    (2 : ℝ)^(27*m) ≤ H^(omega*gamma) := by
  have hq : 0 < Q := lt_trans zero_lt_one hQ
  have hh : 0 < H := (Real.rpow_pos_of_pos hq _).trans_le henv
  apply (Real.log_le_log_iff (by positivity : (0 : ℝ) < 2^(27*m)) (Real.rpow_pos_of_pos hh _)).mp
  rw [Real.log_pow,Real.log_rpow hh]
  have hl : alpha*Real.log Q ≤ Real.log H := by
    simpa only [Real.log_rpow hq] using Real.log_le_log (Real.rpow_pos_of_pos hq _) henv
  have hb := mul_le_mul_of_nonneg_left hl (mul_pos ho hg).le
  nlinarith

theorem polynomial_budget4 (m r0 N : ℕ) (eta alpha omega gamma D Q H X : ℝ)
    (ho : 0 < omega) (hg : 0 < gamma) (hD : 1 ≤ D) (hQ : 1 < Q)
    (henv : Q^alpha ≤ H) (hX : 0 ≤ X) (hheight : X ≤ D^N)
    (hsum : (N : ℝ) ≤ (m : ℝ)*(1+eta)*(r0 : ℝ))
    (hcut : 9*(m : ℝ)*(1+eta)*Real.log D ≤ alpha*omega*gamma*Real.log Q) :
    X^(9 : ℕ) ≤ H^(omega*gamma*(r0 : ℝ)) := by
  have hd : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have hlogD := Real.log_nonneg hD
  have hh : 0 < H := (Real.rpow_pos_of_pos (lt_trans zero_lt_one hQ) _).trans_le henv
  have hbudget : (D^N)^(9 : ℕ) ≤ H^(omega*gamma*(r0 : ℝ)) := by
    apply (Real.log_le_log_iff (by positivity : 0 < (D^N)^(9 : ℕ))
      (Real.rpow_pos_of_pos hh _)).mp
    rw [Real.log_pow,Real.log_pow,Real.log_rpow hh]
    have hl : alpha*Real.log Q ≤ Real.log H := by
      simpa only [Real.log_rpow (lt_trans zero_lt_one hQ)] using
        Real.log_le_log (Real.rpow_pos_of_pos (lt_trans zero_lt_one hQ) _) henv
    have h1 := mul_le_mul_of_nonneg_right hsum (by positivity : 0 ≤ 9*Real.log D)
    have h2 := mul_le_mul_of_nonneg_right hcut (Nat.cast_nonneg r0)
    have h3 := mul_le_mul_of_nonneg_left hl (by positivity : 0 ≤ omega*gamma*(r0 : ℝ))
    norm_num only [Nat.cast_ofNat] at *
    nlinarith
  exact (pow_le_pow_left₀ hX hheight 9).trans hbudget

theorem denominator_growth4 (H0 H Q0 Q gamma : ℝ) (r0 r : ℕ)
    (hH0 : 0 ≤ H0) (hH : 0 ≤ H) (hQ0 : 0 ≤ Q0) (hg : 0 ≤ gamma)
    (hupper : Q0 ≤ H0) (hlower : H^(1/3 : ℝ) ≤ Q)
    (hcompare : H0^(gamma*(r0 : ℝ)) ≤ H^(r : ℝ)) :
    Q0^((r0 : ℝ)*(gamma/3)) ≤ Q^(r : ℝ) := by
  calc
    Q0^((r0 : ℝ)*(gamma/3)) ≤ H0^((r0 : ℝ)*(gamma/3)) :=
      Real.rpow_le_rpow hQ0 hupper (by positivity)
    _ = (H0^(gamma*(r0 : ℝ)))^(1/3 : ℝ) := by
      rw [← Real.rpow_mul hH0]
      congr 1
      ring
    _ ≤ (H^(r : ℝ))^(1/3 : ℝ) :=
      Real.rpow_le_rpow (Real.rpow_nonneg hH0 _) hcompare (by norm_num)
    _ = (H^(1/3 : ℝ))^(r : ℝ) := by
      rw [← Real.rpow_mul hH,← Real.rpow_mul hH]
      congr 1
      ring
    _ ≤ Q^(r : ℝ) := Real.rpow_le_rpow (Real.rpow_nonneg hH _) hlower (Nat.cast_nonneg r)

theorem third_budget4 (H Q a : ℝ) (hH : 0 ≤ H) (hQ : 0 ≤ Q) (ha : 0 ≤ a)
    (hroot : H^(1/3 : ℝ) ≤ Q) : H^a ≤ (Q^(a/3))^9 := by
  calc
    H^a = (H^(1/3 : ℝ))^(3*a) := by
      rw [← Real.rpow_mul hH]
      congr 1
      ring
    _ ≤ Q^(3*a) := Real.rpow_le_rpow (Real.rpow_nonneg hH _) hroot (by positivity)
    _ = (Q^(a/3))^9 := by
      rw [← Real.rpow_mul_natCast hQ]
      congr 1
      norm_num
      ring

theorem denominator_absolute4 (m : ℕ) (H Q omega gamma : ℝ)
    (hH : 0 ≤ H) (hQ : 0 ≤ Q) (ho : 0 ≤ omega) (hg : 0 ≤ gamma)
    (hroot : H^(1/3 : ℝ) ≤ Q) (hbudget : (2 : ℝ)^(27*m) ≤ H^(omega*gamma)) :
    (2 : ℝ)^(3*m) ≤ Q^(omega*(gamma/3)) := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (9 : ℕ) ≠ 0) (Real.rpow_nonneg hQ _)
  calc
    ((2 : ℝ)^(3*m))^9 = (2 : ℝ)^(27*m) := by
      rw [← pow_mul]
      congr 1
      omega
    _ ≤ H^(omega*gamma) := hbudget
    _ ≤ (Q^((omega*gamma)/3))^9 := third_budget4 H Q _ hH hQ (mul_nonneg ho hg) hroot
    _ = (Q^(omega*(gamma/3)))^9 := by congr 2; ring

theorem polynomial_height4 (A B H Q omega gamma : ℝ) (r0 : ℕ)
    (hA : 0 ≤ A) (hH : 0 ≤ H) (hQ : 0 ≤ Q) (ho : 0 ≤ omega) (hg : 0 ≤ gamma)
    (hAB : A ≤ B) (hroot : H^(1/3 : ℝ) ≤ Q)
    (hbudget : B^9 ≤ H^(omega*gamma*(r0 : ℝ))) :
    A ≤ Q^(omega*(r0 : ℝ)*(gamma/3)) := by
  apply le_of_pow_le_pow_left₀ (by norm_num : (9 : ℕ) ≠ 0) (Real.rpow_nonneg hQ _)
  calc
    A^9 ≤ B^9 := pow_le_pow_left₀ hA hAB 9
    _ ≤ H^(omega*gamma*(r0 : ℝ)) := hbudget
    _ ≤ (Q^((omega*gamma*(r0 : ℝ))/3))^9 :=
      third_budget4 H Q _ hH hQ (by positivity) hroot
    _ = (Q^(omega*(r0 : ℝ)*(gamma/3)))^9 := by congr 2; ring



theorem primitive_high_index_contradiction4 (m : ℕ) (hm : 0 < m)
    (M : Fin m → Fin 4 → ℤ) (hM : ∀ h, Ideal.span (Set.range (M h)) = ⊤)
    (theta gamma c : ℝ) (ht : 0 < theta) (ht1 : theta < 1/12)
    (hg : 0 < gamma) (hg3 : gamma ≤ 3) (hc : theta < c)
    (r : Fin m → ℕ) (hr : ∀ h, 0 < r h)
    (hsep : ∀ (h : Fin m) (hh : h.val+1 < m),
      (r ⟨h.val+1,hh⟩ : ℝ) ≤ JSP000334.omega65 m theta*(r h : ℝ))
    (P : MvPolynomial (Vars4 m) ℤ) (hn : P ≠ 0) (hh : homogeneous4 r P)
    (hindex : P.map (Int.castRingHom ℝ) ∈ sourceNormalIdeal4 M r c)
    (hcompare : ∀ h, (normalHeight4 (M ⟨0,hm⟩) : ℝ)^(gamma*(r ⟨0,hm⟩ : ℝ)) ≤
      (normalHeight4 (M h) : ℝ)^(r h))
    (hbudget : ∀ h, (2 : ℝ)^(27*m) ≤
      (normalHeight4 (M h) : ℝ)^(JSP000334.omega65 m theta*gamma))
    (hpoly : (height4 P : ℝ)^9 ≤ (normalHeight4 (M ⟨0,hm⟩) : ℝ)^
      (JSP000334.omega65 m theta*gamma*(r ⟨0,hm⟩ : ℝ))) : False := by
  let C : (h : Fin m) → NormalCoordinateChoice4 (M h) :=
    fun h => (normal_coordinate_choice4 (M h) (hM h)).some
  let e := fun h => (C h).e
  let N := permutedNormals4 M e
  let P' := transport4 ℤ e P
  have hN (h) : N h 0 ≠ 0 := by
    change M h ((C h).e 0) ≠ 0
    rw [(C h).e_zero]
    exact (C h).first_nonzero
  have hNH (h) : normalHeight4 (M h) = (N h 0).natAbs := by
    change normalHeight4 (M h) = (M h ((C h).e 0)).natAbs
    rw [(C h).e_zero]
    exact (C h).height_attains
  have hroot (h) : (normalHeight4 (M h) : ℝ)^(1/3 : ℝ) ≤
      |(SchmidtRationalNormalization6.rootDenominator6 (N h 0) (N h 1) : ℝ)| ∧
      |(SchmidtRationalNormalization6.rootDenominator6 (N h 0) (N h 1) : ℝ)| ≤
        (normalHeight4 (M h) : ℝ) := by
    have hb : Int.gcd (N h 0) (N h 1)^3 ≤ (N h 0).natAbs^2 := by
      change Int.gcd (M h ((C h).e 0)) (M h ((C h).e 1))^3 ≤
        (M h ((C h).e 0)).natAbs^2
      rw [(C h).e_zero,(C h).e_one]
      exact (C h).gcd_bound
    have hx := denominator_real_bounds4 (N h 0) (N h 1) (hN h) hb
    have ha : |(N h 0 : ℝ)| = (normalHeight4 (M h) : ℝ) := by
      rw [hNH h]
      rw [← Int.cast_natCast,Int.natCast_natAbs,Int.cast_abs]
    rwa [ha] at hx
  have hPindex : P'.map (Int.castRingHom ℝ) ∈ sourceNormalIdeal4 N r c := by
    dsimp only [P']
    rw [transport4_map]
    exact (transport4_normalIdeal_iff e M r c _).mp hindex
  have ho := JSP000334.omega65_pos m theta ht
  apply high_index_scalar_contradiction4 m hm N hN theta (gamma/3) c ht ht1
    (by positivity) (by linarith) hc r hr hsep P' ((transport4_nonzero e P).mpr hn)
    ((transport4_homogeneous e r P).mpr hh) hPindex
  · intro h
    simpa only [Real.rpow_natCast] using denominator_growth4
      (normalHeight4 (M ⟨0,hm⟩) : ℝ) (normalHeight4 (M h) : ℝ) _ _ gamma
      (r ⟨0,hm⟩) (r h) (Nat.cast_nonneg _) (Nat.cast_nonneg _) (abs_nonneg _) hg.le
      (hroot _).2 (hroot h).1 (by simpa only [Real.rpow_natCast] using hcompare h)
  · intro h
    exact denominator_absolute4 m _ _ _ gamma (Nat.cast_nonneg _) (abs_nonneg _)
      ho.le hg.le (hroot h).1 (hbudget h)
  · dsimp only [P']
    rw [transport4_height]
    exact polynomial_height4 (height4 P : ℝ) (height4 P : ℝ) _ _ _ gamma (r ⟨0,hm⟩)
      (Nat.cast_nonneg _) (Nat.cast_nonneg _) (abs_nonneg _) ho.le hg.le le_rfl (hroot _).1 hpoly

theorem original_blocks_cutoff4 (U : Set ℝ) (hU : ¬ BddAbove U)
    (cut eta E rho : ℝ) (he : 0 < eta) (hE : 1 ≤ E) (hp : 0 < rho) (m : ℕ) :
    ∃ t : Fin m → U, StrictMono (fun h => (t h).val) ∧ Set.Finite (Set.range t) ∧
      (∀ h, cut < (t h).val ∧ 1 < (t h).val^(5 : ℕ) ∧
        16*E < ((t h).val^(5 : ℕ))^eta ∧
        4*(eta⁻¹+1) < ((t h).val^(5 : ℕ))^eta) ∧
      ∀ (h : Fin m) (hh : h.val+1 < m),
        (1+eta)*Real.log ((t h).val^(5 : ℕ)) ≤
          rho*Real.log ((t ⟨h.val+1,hh⟩).val^(5 : ℕ)) := by
  let B := max (Real.log (16*E)/eta) (Real.log (4*(eta⁻¹+1))/eta)
  obtain ⟨q,hq,hmono,hsep⟩ := JSP000334.parameter_sparse_Q U hU (max cut (Real.exp B))
    ((1+eta)/rho) m
  let t : Fin m → U := fun h => ⟨q h,(hq h).1⟩
  have hlog (h) : B < Real.log (q h) := by
    have ht : Real.exp B < q h := lt_of_le_of_lt (le_max_right _ _) (hq h).2.1
    simpa only [Real.log_exp] using Real.log_lt_log (Real.exp_pos B) ht
  have hQ (h) : 1 < (q h)^(5 : ℕ) := one_lt_pow₀ (hq h).2.2 (by decide)
  have hlogpow (h) : B < Real.log ((q h)^(5 : ℕ)) := by
    rw [Real.log_pow]
    have hl := Real.log_pos (hq h).2.2
    norm_num only [Nat.cast_ofNat]
    linarith [hlog h]
  refine ⟨t,hmono,Set.finite_range t,?_,?_⟩
  · intro h
    refine ⟨lt_of_le_of_lt (le_max_left _ _) (hq h).2.1,hQ h,?_,?_⟩
    · exact JSP000334.parameter_rpow_threshold _ eta _ (hQ h) he (by linarith)
        (lt_of_le_of_lt (le_max_left _ _) (hlogpow h))
    · exact JSP000334.parameter_rpow_threshold _ eta _ (hQ h) he (by positivity)
        (lt_of_le_of_lt (le_max_right _ _) (hlogpow h))
  · intro h hh
    have hs0 := hsep h hh
    rw [div_mul_eq_mul_div] at hs0
    have hs := (div_lt_iff₀ hp).mp hs0
    dsimp [t]
    rw [Real.log_pow,Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    nlinarith

def budgetLog4 (m : ℕ) (eta alpha omega gamma D E : ℝ) : ℝ :=
  max (max (Real.log (16*E)/eta) (Real.log (4*(eta⁻¹+1))/eta))
    (max (((27*m : ℕ) : ℝ)*Real.log 2/(alpha*omega*gamma))
      (9*(m : ℝ)*(1+eta)*Real.log D/(alpha*omega*gamma)))

def originalCutoff4 (T : ℝ) (m : ℕ) (eta alpha omega gamma D E : ℝ) : ℝ :=
  max (max T 1) (Real.exp (budgetLog4 m eta alpha omega gamma D E))

theorem cutoff_budgets4 (T : ℝ) (m : ℕ) (eta alpha omega gamma D E q : ℝ)
    (ha : 0 < alpha) (ho : 0 < omega) (hg : 0 < gamma)
    (hq : originalCutoff4 T m eta alpha omega gamma D E < q) :
    T < q ∧ 1 < q^(5 : ℕ) ∧
      (27*m : ℕ)*Real.log 2 ≤ alpha*omega*gamma*Real.log (q^(5 : ℕ)) ∧
      9*(m : ℝ)*(1+eta)*Real.log D ≤ alpha*omega*gamma*Real.log (q^(5 : ℕ)) := by
  have hT : T < q := lt_of_le_of_lt ((le_max_left T 1).trans (le_max_left _ _)) hq
  have hq1 : 1 < q := lt_of_le_of_lt ((le_max_right T 1).trans (le_max_left _ _)) hq
  have hex : Real.exp (budgetLog4 m eta alpha omega gamma D E) < q :=
    lt_of_le_of_lt (le_max_right _ _) hq
  have hl : budgetLog4 m eta alpha omega gamma D E < Real.log q := by
    simpa only [Real.log_exp] using Real.log_lt_log (Real.exp_pos _) hex
  have hlQ : budgetLog4 m eta alpha omega gamma D E < Real.log (q^(5 : ℕ)) := by
    rw [Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith [Real.log_pos hq1]
  have hn : ((27*m : ℕ) : ℝ)*Real.log 2/(alpha*omega*gamma) < Real.log (q^(5 : ℕ)) :=
    lt_of_le_of_lt ((le_max_left _ _).trans (le_max_right _ _)) hlQ
  have hp : 9*(m : ℝ)*(1+eta)*Real.log D/(alpha*omega*gamma) < Real.log (q^(5 : ℕ)) :=
    lt_of_le_of_lt ((le_max_right _ _).trans (le_max_right _ _)) hlQ
  have hden : 0 < alpha*omega*gamma := mul_pos (mul_pos ha ho) hg
  exact ⟨hT,one_lt_pow₀ hq1 (by decide),
    (by nlinarith [(div_lt_iff₀ hden).mp hn]),(by nlinarith [(div_lt_iff₀ hden).mp hp])⟩


end CompoundFeasibility.SchmidtSourceParameters4
