import SubspaceBridge.ParameterSelection3
import SubspaceBridge.BinaryCanonicalNormal2
open scoped BigOperators Classical
namespace JSP000334

theorem binary_parameter_selection (D E delta : ℝ) (hD : 1≤D) (hE : 1≤E)
    (hd : 0<delta) (hd1 : delta<1) :
    ∃ eta theta : ℝ,∃ m : ℕ,∃ hm : 0<m,
    0<eta ∧ eta<1/2 ∧ 0<theta ∧ theta<1/12 ∧ theta≤2*eta*m ∧ 40*eta<delta ∧
    4*(eta^2)⁻¹*Real.log 12≤(m : ℝ) ∧
    ∀ U : Set ℝ,¬BddAbove U → ∀ cut : ℝ,
    ∃ Q : Fin m → ℝ,∃ r : Fin m → ℕ,
    (∀ h,Q h ∈ U ∧ cut<Q h ∧ 1<Q h) ∧ (∀ h,0<r h) ∧
    (∀ (h : Fin m) (hh : h.val+1<m),(r ⟨h.val+1,hh⟩ : ℝ)≤rothInductionOmega m theta*(r h : ℝ)) ∧
    (∀ h,(r ⟨0,hm⟩ : ℝ)*Real.log (Q ⟨0,hm⟩)≤(r h : ℝ)*Real.log (Q h) ∧
      (r h : ℝ)*Real.log (Q h)≤(1+eta)*(r ⟨0,hm⟩ : ℝ)*Real.log (Q ⟨0,hm⟩)) ∧
    (∀ h,2*E<Real.rpow (Q h) eta) ∧
    ∀ H : Fin m → ℝ,(∀ h,H h=(Q h)^((1 : ℝ)/4)) →
    (∀ h,Real.rpow (H ⟨0,hm⟩) ((r ⟨0,hm⟩ : ℝ)*1)≤H h^r h) ∧
    (∀ h,(2 : ℝ)^(3*m)≤Real.rpow (H h) (rothInductionOmega m theta*1)) ∧
    D^(∑ h,r h)≤Real.rpow (H ⟨0,hm⟩) (rothInductionOmega m theta*(r ⟨0,hm⟩ : ℝ)*1) := by
  let eta := delta/1000
  let theta := eta/2
  obtain ⟨m,hm⟩ := exists_nat_gt (max 1 (4*(eta^2)⁻¹*Real.log 12))
  have he : 0<eta := by dsimp [eta];positivity
  have ht : 0<theta := by dsimp [theta];positivity
  have hm1 : (1 : ℝ)<m := lt_of_le_of_lt (le_max_left _ _) hm
  have hmn : 0<m := by exact_mod_cast (lt_trans zero_lt_one hm1)
  have heta1 : eta<1/2 := by dsimp [eta];linarith
  have ht1 : theta<1/12 := by dsimp [theta,eta];linarith
  have htb : theta≤2*eta*m := by dsimp [theta];nlinarith
  have hed : 40*eta<delta := by dsimp [eta];linarith
  let rho := rothInductionOmega m theta
  have hrho : 0<rho := rothInductionOmega_pos m theta ht
  refine ⟨eta,theta,m,hmn,he,heta1,ht,ht1,htb,hed,(lt_of_le_of_lt (le_max_right _ _) hm).le,?_⟩
  intro U hU cut
  let B1 := Real.log (2*E)/eta
  let B2 := ((12*m : ℕ)*Real.log 2)/((1/4)*rho)
  let B3 := ((m : ℝ)*(1+eta)*Real.log D)/((1/4)*rho)
  let B := max B1 (max B2 B3)
  obtain ⟨Q,hQ,hmono,hgap⟩ := parameter_sparse_Q U hU (max cut (Real.exp B)) ((1+eta)/rho) m
  have hQone (h) : 1<Q h := (hQ h).2.2
  have hlog (h) : B<Real.log (Q h) := by
    have hh : Real.exp B<Q h := lt_of_le_of_lt (le_max_right _ _) (hQ h).2.1
    simpa only [Real.log_exp] using Real.log_lt_log (Real.exp_pos B) hh
  have hb1 (h) : B1<Real.log (Q h) := lt_of_le_of_lt (le_max_left _ _) (hlog h)
  have hb2 (h) : B2<Real.log (Q h) :=
    lt_of_le_of_lt ((le_max_left _ _).trans (le_max_right _ _)) (hlog h)
  have hb3 (h) : B3<Real.log (Q h) :=
    lt_of_le_of_lt ((le_max_right _ _).trans (le_max_right _ _)) (hlog h)
  have hgap' (h : Fin m) (hh : h.val+1<m) :
      (1+eta)*Real.log (Q h)≤rho*Real.log (Q ⟨h.val+1,hh⟩) := by
    have hx := mul_lt_mul_of_pos_left (hgap h hh) hrho
    have hx' : rho*((1+eta)/rho*Real.log (Q h))=(1+eta)*Real.log (Q h) := by field_simp
    rw [hx'] at hx
    exact hx.le
  obtain ⟨r,hr,hsep,hbal⟩ := parameter_integer_degrees m hmn eta rho he hrho Q hQone hgap'
  refine ⟨Q,r,?_,hr,hsep,hbal,?_,?_⟩
  · intro h
    exact ⟨(hQ h).1,lt_of_le_of_lt (le_max_left _ _) (hQ h).2.1,hQone h⟩
  · intro h
    exact parameter_rpow_threshold _ _ _ (hQone h) he (by linarith) (hb1 h)
  · intro H hH
    have hHb (h) : Q h^((1 : ℝ)/4)≤H h ∧ H h≤Q h^((1 : ℝ)/4) := by rw [hH h];exact ⟨le_rfl,le_rfl⟩
    have hHpos (h) : 0<H h := by rw [hH h];exact Real.rpow_pos_of_pos (lt_trans zero_lt_one (hQone h)) _
    have hHlog (h) : Real.log (H h)=(1/4)*Real.log (Q h) := by
      rw [hH h,Real.log_rpow (lt_trans zero_lt_one (hQone h))]
    refine ⟨parameter_roth_growth m hmn (1/4) (1/4) 1 (by norm_num) (by norm_num) (by norm_num)
      Q H hQone hHb r (fun h => (hbal h).1),?_,?_⟩
    · intro h
      have hc : (12*m : ℕ)*Real.log 2≤(1/4)*rho*1*Real.log (Q h) := by
        have hh := (div_lt_iff₀ (mul_pos (by norm_num : (0 : ℝ)<1/4) hrho)).mp (hb2 h)
        nlinarith
      have hh := parameter_roth_denominator m (1/4) rho 1 hrho (by norm_num) (Q h) (H h) (hQone h) (hHb h).1 hc
      exact (pow_le_pow_right₀ (by norm_num : (1 : ℝ)≤2) (by omega : 3*m≤12*m)).trans hh
    · have hsum := parameter_degree_sum m hmn eta he Q hQone hmono.monotone r (fun h => (hbal h).2)
      have hc := (div_lt_iff₀ (mul_pos (by norm_num : (0 : ℝ)<1/4) hrho)).mp (hb3 ⟨0,hmn⟩)
      apply (Real.log_le_log_iff (pow_pos (lt_of_lt_of_le zero_lt_one hD) _)
        (Real.rpow_pos_of_pos (hHpos _) _)).mp
      rw [Real.log_pow,Real.log_rpow (hHpos _),hHlog]
      have h1 := mul_le_mul_of_nonneg_right hsum (Real.log_nonneg hD)
      have h2 := mul_le_mul_of_nonneg_right hc.le (Nat.cast_nonneg (r ⟨0,hmn⟩) : (0 : ℝ)≤r ⟨0,hmn⟩)
      change ((∑ h,r h : ℕ) : ℝ)*Real.log D≤(rho*(r ⟨0,hmn⟩ : ℝ)*1)*((1/4)*Real.log (Q ⟨0,hmn⟩))
      nlinarith

end JSP000334
