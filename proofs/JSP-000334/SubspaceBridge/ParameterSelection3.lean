import SubspaceBridge.ConditionalNormalHeight3
open scoped BigOperators
namespace JSP000334

theorem parameter_eta_theta_m (delta : ℝ) (hd : 0 < delta) (hd' : delta < 1) :
    ∃ eta theta : ℝ, ∃ m : ℕ, 0 < eta ∧ 0 < theta ∧ theta < 1/12 ∧
      432*eta < delta ∧ 0 < m ∧ theta < (m : ℝ)*eta ∧
      4*(eta^2)⁻¹*Real.log 18 ≤ (m : ℝ) ∧ 0 < rothInductionOmega m theta := by
  let eta := delta / 1000
  let theta := eta / 2
  obtain ⟨m, hm⟩ := exists_nat_gt (max 1 (4*(eta^2)⁻¹*Real.log 18))
  have he : 0 < eta := by dsimp [eta]; positivity
  have ht : 0 < theta := by dsimp [theta]; positivity
  have hm1 : (1 : ℝ) < m := lt_of_le_of_lt (le_max_left _ _) hm
  have hmn : 0 < m := by exact_mod_cast (lt_trans zero_lt_one hm1)
  refine ⟨eta,theta,m,he,ht,?_,?_,hmn,?_,?_,rothInductionOmega_pos m theta ht⟩
  · dsimp [theta, eta]; linarith
  · dsimp [eta]; linarith
  · dsimp [theta]; nlinarith
  · exact (lt_of_le_of_lt (le_max_right _ _) hm).le

theorem parameter_gamma (delta : ℝ) (hd : 0 < delta) (hd' : delta < 1) :
    0 < delta/144 ∧ delta/144 ≤ 2 ∧ 9*(delta/144) ≤ delta/16 := by
  constructor
  · positivity
  constructor <;> linarith

theorem parameter_sparse_Q (U : Set ℝ) (hU : ¬ BddAbove U)
    (cut K : ℝ) (m : ℕ) :
    ∃ Q : Fin m → ℝ, (∀ h, Q h ∈ U ∧ cut < Q h ∧ 1 < Q h) ∧
      StrictMono Q ∧
      ∀ (h : Fin m) (hh : h.val+1 < m), K*Real.log (Q h) < Real.log (Q ⟨h.val+1,hh⟩) := by
  have step : ∀ x : ℝ, ∃ y ∈ U, cut < y ∧ 1 < y ∧ x < y ∧
      K*Real.log x < Real.log y := by
    intro x
    obtain ⟨y, hy, hbound⟩ := not_bddAbove_iff.mp hU
      (max (max cut 1) (max x (Real.exp (K*Real.log x))))
    have hb : Real.exp (K*Real.log x) < y :=
      lt_of_le_of_lt ((le_max_right x _).trans (le_max_right _ _)) hbound
    refine ⟨y,hy,?_,?_,?_,?_⟩
    · exact lt_of_le_of_lt ((le_max_left cut 1).trans (le_max_left _ _)) hbound
    · exact lt_of_le_of_lt ((le_max_right cut 1).trans (le_max_left _ _)) hbound
    · exact lt_of_le_of_lt ((le_max_left x _).trans (le_max_right _ _)) hbound
    · simpa only [Real.log_exp] using Real.log_lt_log (Real.exp_pos _) hb
  choose next hn using step
  let q : ℕ → ℝ := fun n => Nat.rec (next 1) (fun _ x => next x) n
  have hq (n : ℕ) : q (n+1) = next (q n) := rfl
  have hspec (n : ℕ) : q n ∈ U ∧ cut < q n ∧ 1 < q n := by
    cases n with
    | zero => exact ⟨(hn 1).1,(hn 1).2.1,(hn 1).2.2.1⟩
    | succ n => exact ⟨(hn (q n)).1,(hn (q n)).2.1,(hn (q n)).2.2.1⟩
  have hmono : StrictMono q := strictMono_nat_of_lt_succ (fun n => (hn (q n)).2.2.2.1)
  refine ⟨fun h => q h.val,fun h => hspec h.val,?_,?_⟩
  · intro i j hij
    exact hmono hij
  · intro h hh
    exact (hn (q h.val)).2.2.2.2

theorem parameter_integer_degrees (m : ℕ) (hm : 0 < m) (eta rho : ℝ)
    (he : 0 < eta) (hp : 0 < rho) (Q : Fin m → ℝ)
    (hQ : ∀ h, 1 < Q h)
    (hgap : ∀ (h : Fin m) (hh : h.val+1 < m),
      (1+eta)*Real.log (Q h) ≤ rho*Real.log (Q ⟨h.val+1,hh⟩)) :
    ∃ r : Fin m → ℕ, (∀ h, 0 < r h) ∧
      (∀ (h : Fin m) (hh : h.val+1 < m),
        (r ⟨h.val+1,hh⟩ : ℝ) ≤ rho*(r h : ℝ)) ∧
      ∀ h, (r ⟨0,hm⟩ : ℝ)*Real.log (Q ⟨0,hm⟩) ≤ (r h : ℝ)*Real.log (Q h) ∧
        (r h : ℝ)*Real.log (Q h) ≤ (1+eta)*(r ⟨0,hm⟩ : ℝ)*Real.log (Q ⟨0,hm⟩) := by
  classical
  let l := fun h => Real.log (Q h)
  let o : Fin m := ⟨0,hm⟩
  have hl (h) : 0 < l h := Real.log_pos (hQ h)
  let L := ∑ h, l h
  obtain ⟨N,hN⟩ := exists_nat_gt (max 0 (L/(eta*l o)))
  have hNp : (0 : ℝ) < N := lt_of_le_of_lt (le_max_left _ _) hN
  have hlarge : L < (N : ℝ)*(eta*l o) :=
    (div_lt_iff₀ (mul_pos he (hl o))).mp (lt_of_le_of_lt (le_max_right _ _) hN)
  have hterm (h) : l h ≤ L := Finset.single_le_sum (fun i _ => (hl i).le) (Finset.mem_univ h)
  let A := (N : ℝ)*l o
  have hA : 0 < A := mul_pos hNp (hl o)
  have herr (h) : l h ≤ eta*A := by dsimp [A]; nlinarith [hterm h]
  let r : Fin m → ℕ := fun h => ⌈A/l h⌉₊
  have hr (h) : 0 < r h := Nat.ceil_pos.mpr (div_pos hA (hl h))
  have ho : r o = N := by
    dsimp [r,A]
    rw [mul_div_cancel_right₀ _ (hl o).ne', Nat.ceil_natCast]
  have hlow (h) : A ≤ (r h : ℝ)*l h :=
    (div_le_iff₀ (hl h)).mp (Nat.le_ceil _)
  have hupp (h) : (r h : ℝ)*l h ≤ (1+eta)*A := by
    have hc := (mul_lt_mul_of_pos_right
      (Nat.ceil_lt_add_one (div_pos hA (hl h)).le) (hl h))
    have hc' : (r h : ℝ)*l h < A+l h := by
      simpa only [add_mul, div_mul_cancel₀ _ (hl h).ne', one_mul] using hc
    nlinarith [herr h]
  refine ⟨r,hr,?_,?_⟩
  · intro h hh
    have hg := hgap h hh
    change (1+eta)*l h ≤ rho*l ⟨h.val+1,hh⟩ at hg
    have hcancel : ((r ⟨h.val+1,hh⟩ : ℝ)*l ⟨h.val+1,hh⟩)*l h ≤
        (rho*(r h : ℝ))*(l ⟨h.val+1,hh⟩*l h) := by
      calc
        _ ≤ ((1+eta)*A)*l h := mul_le_mul_of_nonneg_right (hupp _) (hl h).le
        _ = A*((1+eta)*l h) := by ring
        _ ≤ A*(rho*l ⟨h.val+1,hh⟩) := mul_le_mul_of_nonneg_left hg hA.le
        _ ≤ ((r h : ℝ)*l h)*(rho*l ⟨h.val+1,hh⟩) :=
          mul_le_mul_of_nonneg_right (hlow h) (mul_pos hp (hl _)).le
        _ = _ := by ring
    exact (mul_le_mul_right (mul_pos (hl ⟨h.val+1,hh⟩) (hl h))).mp
      (by convert hcancel using 1; ring)
  · intro h
    change (r o : ℝ)*l o ≤ (r h : ℝ)*l h ∧ (r h : ℝ)*l h ≤ (1+eta)*(r o : ℝ)*l o
    rw [ho]
    exact ⟨hlow h, by simpa only [A, mul_assoc] using hupp h⟩

theorem parameter_degree_sum (m : ℕ) (hm : 0 < m) (eta : ℝ) (_he : 0 < eta)
    (Q : Fin m → ℝ) (hQ : ∀ h, 1 < Q h) (hmono : Monotone Q)
    (r : Fin m → ℕ)
    (hbal : ∀ h, (r h : ℝ)*Real.log (Q h) ≤
      (1+eta)*(r ⟨0,hm⟩ : ℝ)*Real.log (Q ⟨0,hm⟩)) :
    ((∑ h, r h : ℕ) : ℝ) ≤ (m : ℝ)*(1+eta)*(r ⟨0,hm⟩ : ℝ) := by
  have hb (h) : (r h : ℝ) ≤ (1+eta)*(r ⟨0,hm⟩ : ℝ) := by
    have hl : Real.log (Q ⟨0,hm⟩) ≤ Real.log (Q h) :=
      Real.log_le_log (by linarith [hQ ⟨0,hm⟩]) (hmono (show (⟨0,hm⟩ : Fin m) ≤ h from Nat.zero_le h.val))
    have hh := (mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg (r h))).trans (hbal h)
    exact (mul_le_mul_right (Real.log_pos (hQ ⟨0,hm⟩))).mp hh
  have hs := Finset.sum_le_sum (fun h (_ : h ∈ (Finset.univ : Finset (Fin m))) => hb h)
  simpa only [Nat.cast_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_assoc] using hs

theorem parameter_height_logs (Q H C1 C2 : ℝ) (hQ : 1 < Q)
    (hl : Q^C1 ≤ H) (hu : H ≤ Q^C2) :
    0 < H ∧ C1*Real.log Q ≤ Real.log H ∧ Real.log H ≤ C2*Real.log Q := by
  have hp := lt_trans zero_lt_one hQ
  have hH : 0 < H := (Real.rpow_pos_of_pos hp _).trans_le hl
  refine ⟨hH,?_,?_⟩
  · simpa only [Real.log_rpow hp] using Real.log_le_log (Real.rpow_pos_of_pos hp _) hl
  · simpa only [Real.log_rpow hp] using Real.log_le_log hH hu

theorem parameter_roth_growth (m : ℕ) (hm : 0 < m) (C1 C2 Gamma : ℝ)
    (hC : 0 ≤ C1) (hG : 0 < Gamma) (hCG : C2*Gamma ≤ C1)
    (Q H : Fin m → ℝ) (hQ : ∀ h, 1 < Q h)
    (hH : ∀ h, Q h^C1 ≤ H h ∧ H h ≤ Q h^C2)
    (r : Fin m → ℕ)
    (hbal : ∀ h, (r ⟨0,hm⟩ : ℝ)*Real.log (Q ⟨0,hm⟩) ≤ (r h : ℝ)*Real.log (Q h)) :
    ∀ h, (H ⟨0,hm⟩)^((r ⟨0,hm⟩ : ℝ)*Gamma) ≤ (H h)^(r h) := by
  intro h
  have hlogs (i) := parameter_height_logs (Q i) (H i) C1 C2 (hQ i) (hH i).1 (hH i).2
  apply (Real.log_le_log_iff (Real.rpow_pos_of_pos (hlogs _).1 _)
    (pow_pos (hlogs h).1 _)).mp
  rw [Real.log_rpow (hlogs _).1, Real.log_pow]
  have h1 := mul_le_mul_of_nonneg_left (hlogs ⟨0,hm⟩).2.2
    (mul_nonneg (Nat.cast_nonneg (r ⟨0,hm⟩)) hG.le)
  have h2 := mul_le_mul_of_nonneg_right hCG
    (mul_nonneg (Nat.cast_nonneg (r ⟨0,hm⟩)) (Real.log_pos (hQ ⟨0,hm⟩)).le)
  have h3 := mul_le_mul_of_nonneg_left (hlogs h).2.1 (Nat.cast_nonneg (r h))
  have h4 := mul_le_mul_of_nonneg_left (hbal h) hC
  nlinarith

theorem parameter_roth_denominator (m : ℕ) (C1 rho Gamma : ℝ)
    (hp : 0 < rho) (hG : 0 < Gamma) (Q H : ℝ) (hQ : 1 < Q)
    (hH : Q^C1 ≤ H)
    (hcut : (12*m : ℕ)*Real.log 2 ≤ C1*rho*Gamma*Real.log Q) :
    (2 : ℝ)^(12*m) ≤ H^(rho*Gamma) := by
  have hpQ := lt_trans zero_lt_one hQ
  have hpH := (Real.rpow_pos_of_pos hpQ C1).trans_le hH
  apply (Real.log_le_log_iff (by positivity : (0 : ℝ) < 2^(12*m))
    (Real.rpow_pos_of_pos hpH _)).mp
  rw [Real.log_pow, Real.log_rpow hpH]
  have hl : C1*Real.log Q ≤ Real.log H := by
    simpa only [Real.log_rpow hpQ] using Real.log_le_log (Real.rpow_pos_of_pos hpQ _) hH
  have hh := mul_le_mul_of_nonneg_left hl (mul_pos hp hG).le
  nlinarith

theorem parameter_roth_polynomial_height (m : ℕ) (hm : 0 < m) (eta C1 rho Gamma D : ℝ)
    (he : 0 < eta) (hp : 0 < rho) (hG : 0 < Gamma) (hD : 1 ≤ D)
    (Q H : Fin m → ℝ) (hQ : ∀ h, 1 < Q h) (hmono : Monotone Q)
    (hH : ∀ h, Q h^C1 ≤ H h) (r : Fin m → ℕ)
    (hbal : ∀ h, (r h : ℝ)*Real.log (Q h) ≤
      (1+eta)*(r ⟨0,hm⟩ : ℝ)*Real.log (Q ⟨0,hm⟩))
    (hcut : 4*(m : ℝ)*(1+eta)*Real.log D ≤ C1*rho*Gamma*Real.log (Q ⟨0,hm⟩))
    (P : MvPolynomial (RothBlockVars m) ℤ)
    (hheight : (rothKernelBlockHeight P : ℝ) ≤ D^(∑ h, r h)) :
    (rothKernelBlockHeight P : ℝ)^4 ≤
      (H ⟨0,hm⟩)^(rho*(r ⟨0,hm⟩ : ℝ)*Gamma) := by
  have hDp : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have hHp := (Real.rpow_pos_of_pos (lt_trans zero_lt_one (hQ ⟨0,hm⟩)) C1).trans_le (hH ⟨0,hm⟩)
  have hsum := parameter_degree_sum m hm eta he Q hQ hmono r hbal
  have hlogD := Real.log_nonneg hD
  have hcoeff : (D^(∑ h, r h))^4 ≤ (H ⟨0,hm⟩)^(rho*(r ⟨0,hm⟩ : ℝ)*Gamma) := by
    apply (Real.log_le_log_iff (by positivity : 0 < (D^(∑ h, r h))^4)
      (Real.rpow_pos_of_pos hHp _)).mp
    rw [Real.log_pow, Real.log_pow, Real.log_rpow hHp]
    have hl : C1*Real.log (Q ⟨0,hm⟩) ≤ Real.log (H ⟨0,hm⟩) := by
      simpa only [Real.log_rpow (lt_trans zero_lt_one (hQ ⟨0,hm⟩))] using
        Real.log_le_log (Real.rpow_pos_of_pos (lt_trans zero_lt_one (hQ ⟨0,hm⟩)) _) (hH ⟨0,hm⟩)
    have h1 := mul_le_mul_of_nonneg_right hsum (by positivity : 0 ≤ 4*Real.log D)
    have h2 := mul_le_mul_of_nonneg_right hcut (Nat.cast_nonneg (r ⟨0,hm⟩))
    have h3 := mul_le_mul_of_nonneg_left hl
      (mul_nonneg (mul_nonneg hp.le (Nat.cast_nonneg (r ⟨0,hm⟩))) hG.le)
    norm_num only [Nat.cast_ofNat] at *
    nlinarith
  exact (pow_le_pow_left₀ (Nat.cast_nonneg _) hheight 4).trans hcoeff

theorem parameter_rpow_threshold (Q eta X : ℝ) (hQ : 1 < Q)
    (he : 0 < eta) (hX : 0 < X) (hcut : Real.log X/eta < Real.log Q) :
    X < Q^eta := by
  apply (Real.log_lt_log_iff hX (Real.rpow_pos_of_pos (lt_trans zero_lt_one hQ) _)).mp
  rw [Real.log_rpow (lt_trans zero_lt_one hQ)]
  simpa only [mul_comm] using (div_lt_iff₀ he).mp hcut

theorem parameter_Q_degrees_budgets (m : ℕ) (hm : 0 < m) (eta C1 C2 rho Gamma D E C3 : ℝ)
    (he : 0 < eta) (hC : 0 < C1) (hp : 0 < rho) (hG : 0 < Gamma)
    (hCG : C2*Gamma ≤ C1) (hD : 1 ≤ D) (hE : 1 ≤ E)
    (U : Set ℝ) (hU : ¬ BddAbove U) :
    ∃ (Q : Fin m → ℝ) (r : Fin m → ℕ),
      (∀ h, Q h ∈ U ∧ C3 < Q h ∧ 1 < Q h) ∧ StrictMono Q ∧
      (∀ (h : Fin m) (hh : h.val+1 < m),
        (1+eta)*Real.log (Q h) ≤ rho*Real.log (Q ⟨h.val+1,hh⟩)) ∧
      (∀ h, 8*E < (Q h)^eta ∧ 3*(eta⁻¹+1) < (Q h)^eta) ∧
      (∀ h, 0 < r h) ∧
      (∀ (h : Fin m) (hh : h.val+1 < m), (r ⟨h.val+1,hh⟩ : ℝ) ≤ rho*(r h : ℝ)) ∧
      (∀ h, (r ⟨0,hm⟩ : ℝ)*Real.log (Q ⟨0,hm⟩) ≤ (r h : ℝ)*Real.log (Q h) ∧
        (r h : ℝ)*Real.log (Q h) ≤ (1+eta)*(r ⟨0,hm⟩ : ℝ)*Real.log (Q ⟨0,hm⟩)) ∧
      (((∑ h, r h : ℕ) : ℝ)/(r ⟨0,hm⟩ : ℝ) ≤ (m : ℝ)*(1+eta)) ∧
      ∀ H : Fin m → ℝ, (∀ h, (Q h)^C1 ≤ H h ∧ H h ≤ (Q h)^C2) →
        (∀ h, (H ⟨0,hm⟩)^((r ⟨0,hm⟩ : ℝ)*Gamma) ≤ (H h)^(r h)) ∧
        (∀ h, (2 : ℝ)^(12*m) ≤ (H h)^(rho*Gamma)) ∧
        ∀ P : MvPolynomial (RothBlockVars m) ℤ,
          (rothKernelBlockHeight P : ℝ) ≤ D^(∑ h, r h) →
          (rothKernelBlockHeight P : ℝ)^4 ≤ (H ⟨0,hm⟩)^(rho*(r ⟨0,hm⟩ : ℝ)*Gamma) := by
  let B1 := Real.log (8*E)/eta
  let B2 := Real.log (3*(eta⁻¹+1))/eta
  let B3 := ((12*m : ℕ)*Real.log 2)/(C1*rho*Gamma)
  let B4 := (4*(m : ℝ)*(1+eta)*Real.log D)/(C1*rho*Gamma)
  let B := max B1 (max B2 (max B3 B4))
  obtain ⟨Q,hQ,hmono,hgap⟩ := parameter_sparse_Q U hU (max C3 (Real.exp B)) ((1+eta)/rho) m
  have hQone (h) := (hQ h).2.2
  have hlog (h) : B < Real.log (Q h) := by
    have hx : Real.exp B < Q h := lt_of_le_of_lt (le_max_right _ _) (hQ h).2.1
    simpa only [Real.log_exp] using Real.log_lt_log (Real.exp_pos B) hx
  have hb1 (h) : B1 < Real.log (Q h) := lt_of_le_of_lt (le_max_left _ _) (hlog h)
  have hb2 (h) : B2 < Real.log (Q h) :=
    lt_of_le_of_lt ((le_max_left _ _).trans (le_max_right _ _)) (hlog h)
  have hb3 (h) : B3 < Real.log (Q h) :=
    lt_of_le_of_lt ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))) (hlog h)
  have hb4 (h) : B4 < Real.log (Q h) :=
    lt_of_le_of_lt ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))) (hlog h)
  have hsepgap (h : Fin m) (hh : h.val+1 < m) :
      (1+eta)*Real.log (Q h) ≤ rho*Real.log (Q ⟨h.val+1,hh⟩) := by
    have hx := mul_lt_mul_of_pos_left (hgap h hh) hp
    have heq : rho*((1+eta)/rho*Real.log (Q h)) = (1+eta)*Real.log (Q h) := by field_simp
    rw [heq] at hx
    exact hx.le
  obtain ⟨r,hr,hsep,hbal⟩ := parameter_integer_degrees m hm eta rho he hp Q hQone hsepgap
  have hsum := parameter_degree_sum m hm eta he Q hQone hmono.monotone r (fun h => (hbal h).2)
  refine ⟨Q,r,?_,hmono,hsepgap,?_,hr,hsep,hbal,?_,?_⟩
  · intro h
    exact ⟨(hQ h).1,lt_of_le_of_lt (le_max_left _ _) (hQ h).2.1,hQone h⟩
  · intro h
    exact ⟨parameter_rpow_threshold _ _ _ (hQone h) he (by linarith) (hb1 h),
      parameter_rpow_threshold _ _ _ (hQone h) he (by positivity) (hb2 h)⟩
  · exact (div_le_iff₀ (show (0 : ℝ) < r ⟨0,hm⟩ by exact_mod_cast hr ⟨0,hm⟩)).mpr hsum
  · intro H hH
    refine ⟨parameter_roth_growth m hm C1 C2 Gamma hC.le hG hCG Q H hQone hH r
      (fun h => (hbal h).1),?_,?_⟩
    · intro h
      apply parameter_roth_denominator m C1 rho Gamma hp hG (Q h) (H h) (hQone h) (hH h).1
      have hh := (div_lt_iff₀ (mul_pos (mul_pos hC hp) hG)).mp (hb3 h)
      nlinarith
    · intro P hP
      apply parameter_roth_polynomial_height m hm eta C1 rho Gamma D he hp hG hD Q H hQone
        hmono.monotone (fun h => (hH h).1) r (fun h => (hbal h).2) _ P hP
      have hh := (div_lt_iff₀ (mul_pos (mul_pos hC hp) hG)).mp (hb4 ⟨0,hm⟩)
      nlinarith

theorem source_compatible_parameter_selection3 (D E delta : ℝ)
    (hD : 1 ≤ D) (hE : 1 ≤ E) (hd : 0 < delta) (hd' : delta < 1) :
    ∃ eta theta : ℝ, ∃ (m : ℕ) (hm : 0 < m), ∃ Gamma : ℝ,
      0 < eta ∧ 0 < theta ∧ theta < 1/12 ∧ 432*eta < delta ∧
      theta < (m : ℝ)*eta ∧ 4*(eta^2)⁻¹*Real.log 18 ≤ (m : ℝ) ∧
      0 < Gamma ∧ Gamma ≤ 2 ∧ 9*Gamma ≤ delta/16 ∧ 0 < rothInductionOmega m theta ∧
      ∀ U : Set ℝ, ¬ BddAbove U →
    ∃ (Q : Fin m → ℝ) (r : Fin m → ℕ),
      (∀ h, Q h ∈ U ∧ (max 108 ((18 : ℝ)^(16/delta))) < Q h ∧ 1 < Q h) ∧ StrictMono Q ∧
      (∀ (h : Fin m) (hh : h.val+1 < m),
        (1+eta)*Real.log (Q h) ≤ (rothInductionOmega m theta)*Real.log (Q ⟨h.val+1,hh⟩)) ∧
      (∀ h, 8*E < (Q h)^eta ∧ 3*(eta⁻¹+1) < (Q h)^eta) ∧
      (∀ h, 0 < r h) ∧
      (∀ (h : Fin m) (hh : h.val+1 < m), (r ⟨h.val+1,hh⟩ : ℝ) ≤ (rothInductionOmega m theta)*(r h : ℝ)) ∧
      (∀ h, (r ⟨0,hm⟩ : ℝ)*Real.log (Q ⟨0,hm⟩) ≤ (r h : ℝ)*Real.log (Q h) ∧
        (r h : ℝ)*Real.log (Q h) ≤ (1+eta)*(r ⟨0,hm⟩ : ℝ)*Real.log (Q ⟨0,hm⟩)) ∧
      (((∑ h, r h : ℕ) : ℝ)/(r ⟨0,hm⟩ : ℝ) ≤ (m : ℝ)*(1+eta)) ∧
      ∀ H : Fin m → ℝ, (∀ h, (Q h)^(delta/16) ≤ H h ∧ H h ≤ (Q h)^(9 : ℝ)) →
        (∀ h, (H ⟨0,hm⟩)^((r ⟨0,hm⟩ : ℝ)*Gamma) ≤ (H h)^(r h)) ∧
        (∀ h, (2 : ℝ)^(12*m) ≤ (H h)^((rothInductionOmega m theta)*Gamma)) ∧
        ∀ P : MvPolynomial (RothBlockVars m) ℤ,
          (rothKernelBlockHeight P : ℝ) ≤ D^(∑ h, r h) →
          (rothKernelBlockHeight P : ℝ)^4 ≤ (H ⟨0,hm⟩)^((rothInductionOmega m theta)*(r ⟨0,hm⟩ : ℝ)*Gamma) := by
  obtain ⟨eta,theta,m,he,ht,ht',hed,hm,hmt,hcount,hp⟩ := parameter_eta_theta_m delta hd hd'
  obtain ⟨hG,hG',hCG⟩ := parameter_gamma delta hd hd'
  refine ⟨eta,theta,m,hm,delta/144,he,ht,ht',hed,hmt,hcount,hG,hG',hCG,hp,?_⟩
  intro U hU
  exact parameter_Q_degrees_budgets m hm eta (delta/16) 9 (rothInductionOmega m theta) (delta/144) D E
    (max 108 ((18 : ℝ)^(16/delta))) he (by positivity) hp hG hCG hD hE U hU

end JSP000334
