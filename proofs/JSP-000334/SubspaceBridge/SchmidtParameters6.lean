import SubspaceBridge.SourceReadiness6
import SubspaceBridge.SchmidtOmega6
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SchmidtParameters6
open SourceReadiness6 SourceNormalHeight SourceHeightEnvelopes6 SourceMixed6 SourceBlocks
open Auxiliary6 Auxiliary6.SourceExpansion

theorem normal_height_convention6 (M : Fin 6 → ℤ) (hM : M ≠ 0) :
    max 1 (normalHeight6 M : ℝ) = (normalHeight6 M : ℝ) := by
  apply max_eq_right
  exact_mod_cast normalHeight6_pos M hM

theorem polynomial_height_bound6 {m : ℕ} (P : MvPolynomial (Vars6 m) ℤ) (H : ℕ) :
    height6 P ≤ H ↔ ∀ d, (P.coeff d).natAbs ≤ H := by
  classical
  unfold height6
  rw [Finset.sup_le_iff]
  constructor
  · intro h d
    by_cases hd : d ∈ P.support
    · exact h d hd
    · simp only [MvPolynomial.mem_support_iff, ne_eq, not_not] at hd
      simp [hd]
  · intro h d _
    exact h d

theorem polynomial_coefficient_bound6 {m : ℕ} (P : MvPolynomial (Vars6 m) ℤ)
    (d : Vars6 m →₀ ℕ) : |((P.coeff d : ℤ) : ℝ)| ≤ (height6 P : ℝ) := by
  have h := (polynomial_height_bound6 P (height6 P)).mp le_rfl d
  have he : ((P.coeff d).natAbs : ℝ) = |((P.coeff d : ℤ) : ℝ)| := by
    rw [← Int.cast_natCast,Int.natCast_natAbs,Int.cast_abs]
  rw [← he]
  exact_mod_cast h

theorem polynomial_height_pos6 {m : ℕ} (P : MvPolynomial (Vars6 m) ℤ) (hP : P ≠ 0) :
    0 < height6 P := by
  by_contra hn
  have hz : height6 P = 0 := by omega
  apply hP
  ext d
  have hc := (polynomial_height_bound6 P (height6 P)).mp le_rfl d
  rw [hz] at hc
  exact Int.natAbs_eq_zero.mp (Nat.eq_zero_of_le_zero hc)

theorem polynomial_height_convention6 {m : ℕ} (P : MvPolynomial (Vars6 m) ℤ) (hP : P ≠ 0) :
    max 1 (height6 P : ℝ) = (height6 P : ℝ) := by
  apply max_eq_right
  exact_mod_cast polynomial_height_pos6 P hP

theorem eta_m_theta6 (delta : ℝ) (hd : 0 < delta) (hd1 : delta < 1)
    (K : IntermediateField ℚ ℝ) :
    ∃ eta theta : ℝ, ∃ m : ℕ, eta = delta/3456 ∧ theta = eta/2 ∧
      0 < eta ∧ eta < 1 ∧ 1728*eta < delta ∧ 0 < m ∧
      4*(eta^2)⁻¹*Real.log (36*(Module.finrank ℚ K : ℝ)) ≤ (m : ℝ) ∧
      0 < theta ∧ theta < 1/12 ∧ theta < (m : ℝ)*eta ∧ 0 < JSP000334.omega65 m theta := by
  let eta := delta/3456
  let theta := eta/2
  have he : 0 < eta := by dsimp [eta]; positivity
  obtain ⟨m,hm⟩ := exists_nat_gt (max 1 (4*(eta^2)⁻¹*Real.log (36*(Module.finrank ℚ K : ℝ))))
  have hm1 : (1 : ℝ) < m := lt_of_le_of_lt (le_max_left _ _) hm
  have hmn : 0 < m := by exact_mod_cast (lt_trans zero_lt_one hm1)
  have ht : 0 < theta := by dsimp [theta]; positivity
  refine ⟨eta,theta,m,rfl,rfl,he,?_,?_,hmn,
    (lt_of_le_of_lt (le_max_right _ _) hm).le,ht,?_,?_,JSP000334.omega65_pos m theta ht⟩
  · dsimp [eta]; linarith
  · dsimp [eta]; linarith
  · dsimp [theta,eta]; linarith
  · dsimp [theta]; nlinarith

theorem positive_gamma6 (alpha eta : ℝ) (ha : 0 < alpha) (he : 0 < eta) :
    ∃ gamma : ℝ, 0 < gamma ∧ gamma ≤ 5 ∧ 6*gamma*(1+eta) ≤ alpha ∧ 6*gamma ≤ alpha := by
  let gamma := min 1 (alpha/(6*(1+eta)))
  have hg : 0 < gamma := lt_min zero_lt_one (div_pos ha (by positivity))
  have hc : gamma ≤ alpha/(6*(1+eta)) := min_le_right _ _
  have hb : gamma*(6*(1+eta)) ≤ alpha := (le_div_iff₀ (by positivity)).mp hc
  refine ⟨gamma,hg,(min_le_left _ _).trans (by norm_num),?_,?_⟩
  · nlinarith
  · nlinarith [mul_pos hg he]

theorem original_blocks_cutoff6 (U : Set ℝ) (hU : ¬ BddAbove U)
    (cut eta E rho : ℝ) (he : 0 < eta) (hE : 1 ≤ E) (hp : 0 < rho) (m : ℕ) :
    ∃ t : Fin m → U, StrictMono (fun h => (t h).val) ∧ Set.Finite (Set.range t) ∧
      (∀ h, cut < (t h).val ∧ 1 < (t h).val^(11 : ℕ) ∧
        64*E < ((t h).val^(11 : ℕ))^eta ∧
        6*(eta⁻¹+1) < ((t h).val^(11 : ℕ))^eta) ∧
      ∀ (h : Fin m) (hh : h.val+1 < m),
        (1+eta)*Real.log ((t h).val^(11 : ℕ)) ≤
          rho*Real.log ((t ⟨h.val+1,hh⟩).val^(11 : ℕ)) := by
  let B := max (Real.log (64*E)/eta) (Real.log (6*(eta⁻¹+1))/eta)
  obtain ⟨q,hq,hmono,hsep⟩ := JSP000334.parameter_sparse_Q U hU (max cut (Real.exp B))
    ((1+eta)/rho) m
  let t : Fin m → U := fun h => ⟨q h,(hq h).1⟩
  have hlog (h) : B < Real.log (q h) := by
    have ht : Real.exp B < q h := lt_of_le_of_lt (le_max_right _ _) (hq h).2.1
    simpa only [Real.log_exp] using Real.log_lt_log (Real.exp_pos B) ht
  have hQ (h) : 1 < (q h)^(11 : ℕ) := one_lt_pow₀ (hq h).2.2 (by decide)
  have hlogpow (h) : B < Real.log ((q h)^(11 : ℕ)) := by
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

theorem anchored_degrees6 (m : ℕ) (hm : 0 < m) (eta omega : ℝ)
    (he : 0 < eta) (ho : 0 < omega) (Q : Fin m → ℝ) (hQ : ∀ h, 1 < Q h)
    (hmono : Monotone Q)
    (hsep : ∀ (h : Fin m) (hh : h.val+1 < m),
      (1+eta)*Real.log (Q h) ≤ omega*Real.log (Q ⟨h.val+1,hh⟩)) :
    ∃ r : Fin m → ℕ, (∀ h, 0 < r h) ∧
      (∀ (h : Fin m) (hh : h.val+1 < m), (r ⟨h.val+1,hh⟩ : ℝ) ≤ omega*(r h : ℝ)) ∧
      (∀ h, (r ⟨0,hm⟩ : ℝ)*Real.log (Q ⟨0,hm⟩) ≤ (r h : ℝ)*Real.log (Q h) ∧
        (r h : ℝ)*Real.log (Q h) ≤ (1+eta)*((r ⟨0,hm⟩ : ℝ)*Real.log (Q ⟨0,hm⟩))) ∧
      ((∑ h, r h : ℕ) : ℝ) ≤ (m : ℝ)*(1+eta)*(r ⟨0,hm⟩ : ℝ) := by
  obtain ⟨r,hr,hgap,hbal⟩ := JSP000334.parameter_integer_degrees m hm eta omega he ho Q hQ hsep
  refine ⟨r,hr,hgap,?_,JSP000334.parameter_degree_sum m hm eta he Q hQ hmono r (fun h => (hbal h).2)⟩
  intro h
  exact ⟨(hbal h).1,by simpa only [mul_assoc] using (hbal h).2⟩

theorem height_comparison6 (m : ℕ) (hm : 0 < m) (alpha gamma : ℝ)
    (ha : 0 < alpha) (hg : 0 < gamma) (hcompat : 6*gamma ≤ alpha)
    (Q H : Fin m → ℝ) (hQ : ∀ h, 1 < Q h)
    (henv : ∀ h, Q h^alpha ≤ H h ∧ H h ≤ Q h^(6 : ℝ)) (r : Fin m → ℕ)
    (hbal : ∀ h, (r ⟨0,hm⟩ : ℝ)*Real.log (Q ⟨0,hm⟩) ≤ (r h : ℝ)*Real.log (Q h)) :
    ∀ h, H ⟨0,hm⟩^(gamma*(r ⟨0,hm⟩ : ℝ)) ≤ H h^(r h) := by
  simpa only [mul_comm] using JSP000334.parameter_roth_growth m hm alpha 6 gamma ha.le hg
    hcompat Q H hQ henv r hbal

theorem normal_budget6 (m : ℕ) (alpha omega gamma Q H : ℝ)
    (ho : 0 < omega) (hg : 0 < gamma) (hQ : 1 < Q) (henv : Q^alpha ≤ H)
    (hcut : (75*m : ℕ)*Real.log 2 ≤ alpha*omega*gamma*Real.log Q) :
    (2 : ℝ)^(75*m) ≤ H^(omega*gamma) := by
  have hq : 0 < Q := lt_trans zero_lt_one hQ
  have hh : 0 < H := (Real.rpow_pos_of_pos hq _).trans_le henv
  apply (Real.log_le_log_iff (by positivity : (0 : ℝ) < 2^(75*m)) (Real.rpow_pos_of_pos hh _)).mp
  rw [Real.log_pow,Real.log_rpow hh]
  have hl : alpha*Real.log Q ≤ Real.log H := by
    simpa only [Real.log_rpow hq] using Real.log_le_log (Real.rpow_pos_of_pos hq _) henv
  have hb := mul_le_mul_of_nonneg_left hl (mul_pos ho hg).le
  nlinarith

theorem polynomial_budget6 (m r0 N : ℕ) (eta alpha omega gamma D Q H X : ℝ)
    (ho : 0 < omega) (hg : 0 < gamma) (hD : 1 ≤ D) (hQ : 1 < Q)
    (henv : Q^alpha ≤ H) (hX : 0 ≤ X) (hheight : X ≤ D^N)
    (hsum : (N : ℝ) ≤ (m : ℝ)*(1+eta)*(r0 : ℝ))
    (hcut : 25*(m : ℝ)*(1+eta)*Real.log D ≤ alpha*omega*gamma*Real.log Q) :
    X^(25 : ℕ) ≤ H^(omega*gamma*(r0 : ℝ)) := by
  have hd : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have hlogD := Real.log_nonneg hD
  have hh : 0 < H := (Real.rpow_pos_of_pos (lt_trans zero_lt_one hQ) _).trans_le henv
  have hbudget : (D^N)^(25 : ℕ) ≤ H^(omega*gamma*(r0 : ℝ)) := by
    apply (Real.log_le_log_iff (by positivity : 0 < (D^N)^(25 : ℕ))
      (Real.rpow_pos_of_pos hh _)).mp
    rw [Real.log_pow,Real.log_pow,Real.log_rpow hh]
    have hl : alpha*Real.log Q ≤ Real.log H := by
      simpa only [Real.log_rpow (lt_trans zero_lt_one hQ)] using
        Real.log_le_log (Real.rpow_pos_of_pos (lt_trans zero_lt_one hQ) _) henv
    have h1 := mul_le_mul_of_nonneg_right hsum (by positivity : 0 ≤ 25*Real.log D)
    have h2 := mul_le_mul_of_nonneg_right hcut (Nat.cast_nonneg r0)
    have h3 := mul_le_mul_of_nonneg_left hl (by positivity : 0 ≤ omega*gamma*(r0 : ℝ))
    norm_num only [Nat.cast_ofNat] at *
    nlinarith
  exact (pow_le_pow_left₀ hX hheight 25).trans hbudget

def budgetLog6 (m : ℕ) (eta alpha omega gamma D E : ℝ) : ℝ :=
  max (max (Real.log (64*E)/eta) (Real.log (6*(eta⁻¹+1))/eta))
    (max (((75*m : ℕ) : ℝ)*Real.log 2/(alpha*omega*gamma))
      (25*(m : ℝ)*(1+eta)*Real.log D/(alpha*omega*gamma)))

def originalCutoff6 (T : ℝ) (m : ℕ) (eta alpha omega gamma D E : ℝ) : ℝ :=
  max (max T 1) (Real.exp (budgetLog6 m eta alpha omega gamma D E))

theorem cutoff_budgets6 (T : ℝ) (m : ℕ) (eta alpha omega gamma D E q : ℝ)
    (ha : 0 < alpha) (ho : 0 < omega) (hg : 0 < gamma)
    (hq : originalCutoff6 T m eta alpha omega gamma D E < q) :
    T < q ∧ 1 < q^(11 : ℕ) ∧
      (75*m : ℕ)*Real.log 2 ≤ alpha*omega*gamma*Real.log (q^(11 : ℕ)) ∧
      25*(m : ℝ)*(1+eta)*Real.log D ≤ alpha*omega*gamma*Real.log (q^(11 : ℕ)) := by
  have hT : T < q := lt_of_le_of_lt ((le_max_left T 1).trans (le_max_left _ _)) hq
  have hq1 : 1 < q := lt_of_le_of_lt ((le_max_right T 1).trans (le_max_left _ _)) hq
  have hex : Real.exp (budgetLog6 m eta alpha omega gamma D E) < q :=
    lt_of_le_of_lt (le_max_right _ _) hq
  have hl : budgetLog6 m eta alpha omega gamma D E < Real.log q := by
    simpa only [Real.log_exp] using Real.log_lt_log (Real.exp_pos _) hex
  have hlQ : budgetLog6 m eta alpha omega gamma D E < Real.log (q^(11 : ℕ)) := by
    rw [Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith [Real.log_pos hq1]
  have hn : ((75*m : ℕ) : ℝ)*Real.log 2/(alpha*omega*gamma) < Real.log (q^(11 : ℕ)) :=
    lt_of_le_of_lt ((le_max_left _ _).trans (le_max_right _ _)) hlQ
  have hp : 25*(m : ℝ)*(1+eta)*Real.log D/(alpha*omega*gamma) < Real.log (q^(11 : ℕ)) :=
    lt_of_le_of_lt ((le_max_right _ _).trans (le_max_right _ _)) hlQ
  have hden : 0 < alpha*omega*gamma := mul_pos (mul_pos ha ho) hg
  exact ⟨hT,one_lt_pow₀ hq1 (by decide),
    (by nlinarith [(div_lt_iff₀ hden).mp hn]),(by nlinarith [(div_lt_iff₀ hden).mp hp])⟩

end CompoundFeasibility.SchmidtParameters6
