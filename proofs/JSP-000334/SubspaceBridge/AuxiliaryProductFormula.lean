import SubspaceBridge.AuxiliaryLocalEstimates
import Mathlib.Data.Nat.Factorization.Induction

open scoped BigOperators Classical
namespace JSP000334

local instance : Fact (Nat.Prime 2) := ⟨by decide⟩
local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

theorem rothInteger_nat_three_place_lower (n : ℕ) (hn : n ≠ 0) :
    (1 : ℚ) ≤ threePlaceProduct (n : ℚ) := by
  refine Nat.recOnMul (P := fun n => n ≠ 0 → (1 : ℚ) ≤ threePlaceProduct (n : ℚ)) ?_ ?_ ?_ ?_ n hn
  · intro h
    exact (h rfl).elim
  · intro _
    norm_num [threePlaceProduct, padicNorm.one]
  · intro p hp _
    letI : Fact p.Prime := ⟨hp⟩
    by_cases h2 : p = 2
    · subst p
      have h32 : padicNorm 3 (2 : ℚ) = 1 := padicNorm.padicNorm_of_prime_of_ne (by decide)
      have h22 : padicNorm 2 (2 : ℚ) = (2 : ℚ)⁻¹ := by
        convert padicNorm.padicNorm_p (p := 2) (by decide) using 1
      norm_num only [Nat.cast_ofNat]
      unfold threePlaceProduct
      rw [h22, h32]
      norm_num
    · by_cases h3 : p = 3
      · subst p
        have h23 : padicNorm 2 (3 : ℚ) = 1 := padicNorm.padicNorm_of_prime_of_ne (by decide)
        have h33 : padicNorm 3 (3 : ℚ) = (3 : ℚ)⁻¹ := by
          convert padicNorm.padicNorm_p (p := 3) (by decide) using 1
        norm_num only [Nat.cast_ofNat]
        unfold threePlaceProduct
        rw [h33, h23]
        norm_num
      · have h2p : padicNorm 2 (p : ℚ) = 1 := padicNorm.padicNorm_of_prime_of_ne (Ne.symm h2)
        have h3p : padicNorm 3 (p : ℚ) = 1 := padicNorm.padicNorm_of_prime_of_ne (Ne.symm h3)
        simpa [threePlaceProduct, h2p, h3p] using
          (show (1 : ℚ) ≤ (p : ℚ) by exact_mod_cast hp.one_lt.le)
  · intro a b ha hb hab
    have ha' := ha (left_ne_zero_of_mul hab)
    have hb' := hb (right_ne_zero_of_mul hab)
    rw [Nat.cast_mul, threePlaceProduct_mul]
    have := mul_le_mul ha' hb' (by norm_num : (0:ℚ) ≤ 1) (le_trans (by norm_num) ha')
    simpa using this

theorem rothInteger_three_place_lower (z : ℤ) (hz : z ≠ 0) :
    1 ≤ rothLocalAbs 0 (z : ℚ) * rothLocalAbs 1 (z : ℚ) * rothLocalAbs 2 (z : ℚ) := by
  have hn := rothInteger_nat_three_place_lower z.natAbs (Int.natAbs_ne_zero.mpr hz)
  have habs : (z.natAbs : ℚ) = |(z : ℚ)| := by
    rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
  have he : threePlaceProduct (z : ℚ) = threePlaceProduct (z.natAbs : ℚ) := by
    rw [habs]
    by_cases h : 0 ≤ (z : ℚ)
    · rw [abs_of_nonneg h]
    · rw [abs_of_neg (lt_of_not_ge h)]
      simp [threePlaceProduct]
  rw [← he] at hn
  change (1 : ℝ) ≤ |((z : ℚ) : ℝ)| * (padicNorm 2 (z : ℚ) : ℝ) * (padicNorm 3 (z : ℚ) : ℝ)
  unfold threePlaceProduct at hn
  exact_mod_cast hn
theorem rothNormalSourceBound_nonneg {m : ℕ} (tau : Fin 3) (E eta : ℝ)
    (hE : 0 ≤ E) (r : Fin m → ℕ) (Q : Fin m → ℝ) (h0 : Fin m)
    (c : Fin 3 → Fin 3 → ℝ) : 0 ≤ rothNormalSourceBound tau E eta r Q h0 c := by
  unfold rothNormalSourceBound
  split_ifs <;> positivity

theorem rothInteger_three_place_upper {m : ℕ} (z : ℤ) (E eta : ℝ) (hE : 0 ≤ E)
    (r : Fin m → ℕ) (Q : Fin m → ℝ) (h0 : Fin m) (c : Fin 3 → Fin 3 → ℝ)
    (hcsum : (∑ tau : Fin 3, ∑ i : Fin 3, c tau i) = 0)
    (hz : ∀ tau : Fin 3, rothLocalAbs tau (z : ℚ) ≤ rothNormalSourceBound tau E eta r Q h0 c) :
    rothLocalAbs 0 (z : ℚ) * rothLocalAbs 1 (z : ℚ) * rothLocalAbs 2 (z : ℚ) ≤
      (8*E^3)^(∑ h, r h) * Real.exp (-27*((r h0 : ℝ)*Real.log (Q h0))*m*eta) := by
  have h0nn := rothNormalSourceBound_nonneg 0 E eta hE r Q h0 c
  have h1nn := rothNormalSourceBound_nonneg 1 E eta hE r Q h0 c
  have hs : (∑ i : Fin 3, c 0 i) + (∑ i : Fin 3, c 1 i) + (∑ i : Fin 3, c 2 i) = 0 := by
    simpa only [Fin.sum_univ_three] using hcsum
  calc
    _ ≤ rothNormalSourceBound 0 E eta r Q h0 c * rothNormalSourceBound 1 E eta r Q h0 c *
        rothNormalSourceBound 2 E eta r Q h0 c :=
      mul_le_mul (mul_le_mul (hz 0) (hz 1) (rothLocalAbs_nonneg 1 _) h0nn) (hz 2)
        (rothLocalAbs_nonneg 2 _) (mul_nonneg h0nn h1nn)
    _ = _ := by
      let A := (r h0 : ℝ)*Real.log (Q h0)
      let R := ∑ h, r h
      let x := fun tau : Fin 3 => A*m*((∑ i : Fin 3, c tau i)/3 + if tau = 0 then -279*eta else 126*eta)
      have he : x 0 + x 1 + x 2 = -27*A*m*eta := by
        simp only [x, Fin.isValue, Fin.reduceEq, ite_true, ite_false]
        calc
          _ = A*m*(((∑ i : Fin 3, c 0 i)+(∑ i : Fin 3, c 1 i)+(∑ i : Fin 3, c 2 i))/3-27*eta) := by ring
          _ = _ := by rw [hs]; ring
      change ((8*E)^R*Real.exp (x 0)) * (E^R*Real.exp (x 1)) * (E^R*Real.exp (x 2)) = _
      calc
        _ = ((8*E)^R*E^R*E^R) * Real.exp (x 0+x 1+x 2) := by
          rw [Real.exp_add, Real.exp_add]
          ring
        _ = _ := by
          rw [he, ← mul_pow, ← mul_pow]
          congr 2
          ring

theorem rothSource_product_bound_lt_one {m : ℕ} (r : Fin m → ℕ)
    (hr : ∀ h, 0 < r h) (Q : Fin m → ℝ) (h0 : Fin m)
    (E eta delta : ℝ) (hE : 1 ≤ E) (heta : 0 < eta)
    (hdelta : 432*eta < delta) (hdeltalt : delta < 1)
    (hQ : ∀ h, 1 < Q h) (hthreshold : ∀ h, 8*E < Real.rpow (Q h) eta)
    (hlog : ∀ h, (r h : ℝ)*Real.log (Q h) ≤ (1+eta)*(r h0 : ℝ)*Real.log (Q h0)) :
    (8*E^3)^(∑ h, r h) * Real.exp (-27*((r h0 : ℝ)*Real.log (Q h0))*m*eta) < 1 := by
  let A := (r h0 : ℝ)*Real.log (Q h0)
  let R := ∑ h, r h
  have hm : 0 < m := by have hh := h0.isLt; omega
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hA : 0 < A := mul_pos (by exact_mod_cast hr h0) (Real.log_pos (hQ h0))
  have hR : 0 < R := Finset.sum_pos (fun h _ => hr h) ⟨h0,Finset.mem_univ _⟩
  have hEpos : 0 < E := lt_of_lt_of_le zero_lt_one hE
  have h8E : 0 < 8*E := by positivity
  have hgrowth (h : Fin m) : Real.log (8*E) < eta*Real.log (Q h) := by
    have ht := Real.log_lt_log h8E (hthreshold h)
    simpa only [Real.rpow_eq_pow, Real.log_rpow (lt_trans zero_lt_one (hQ h))] using ht
  have hterm (h : Fin m) : (r h : ℝ)*Real.log (8*E) < (r h : ℝ)*(eta*Real.log (Q h)) :=
    mul_lt_mul_of_pos_left (hgrowth h) (by exact_mod_cast hr h)
  have hsum := Finset.sum_lt_sum_of_nonempty (s := Finset.univ)
    (⟨h0,Finset.mem_univ _⟩ : (Finset.univ : Finset (Fin m)).Nonempty)
    (fun h _ => hterm h)
  have hstrict : (R : ℝ)*Real.log (8*E) < eta*(∑ h : Fin m, (r h : ℝ)*Real.log (Q h)) := by
    simpa only [← Finset.sum_mul, mul_left_comm, ← Finset.mul_sum, ← Nat.cast_sum, R] using hsum
  have hsumupper : (∑ h : Fin m, (r h : ℝ)*Real.log (Q h)) ≤ (1+eta)*A*m := by
    have hs := Finset.sum_le_sum (fun h (_ : h ∈ (Finset.univ : Finset (Fin m))) => hlog h)
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, A, mul_assoc, mul_comm, mul_left_comm] using hs
  have hlogcube : Real.log (8*E^3) ≤ 3*Real.log (8*E) := by
    calc
      _ ≤ Real.log ((8*E)^3) := Real.log_le_log (by positivity) (by nlinarith [pow_nonneg hEpos.le 3])
      _ = _ := by rw [Real.log_pow]; norm_num
  have hscaled := mul_le_mul_of_nonneg_left hlogcube (Nat.cast_nonneg R)
  have hscaledstrict := mul_lt_mul_of_pos_left hstrict (by norm_num : (0:ℝ) < 3)
  have hscaledupper := mul_le_mul_of_nonneg_left hsumupper (by positivity : 0 ≤ 3*eta)
  have hsmall : 3*(1+eta) < 27 := by linarith
  have hpositive : 0 < A*m*eta := mul_pos (mul_pos hA hmR) heta
  have hgap := mul_lt_mul_of_pos_right hsmall hpositive
  have hexp : (R : ℝ)*Real.log (8*E^3) - 27*A*m*eta < 0 := by nlinarith
  have hbase : 0 < 8*E^3 := by positivity
  calc
    _ = Real.exp ((R : ℝ)*Real.log (8*E^3) - 27*A*m*eta) := by
      rw [Real.exp_sub, Real.exp_nat_mul, Real.exp_log hbase]
      change (8*E^3)^R * Real.exp (-27*A*m*eta) = (8*E^3)^R / Real.exp (27*A*m*eta)
      rw [div_eq_mul_inv, ← Real.exp_neg]
      congr 2
      ring
    _ < 1 := Real.exp_lt_one_iff.mpr hexp

theorem rothInteger_three_place_contradiction {m : ℕ} (r : Fin m → ℕ)
    (hr : ∀ h, 0 < r h) (Q : Fin m → ℝ) (h0 : Fin m)
    (E eta delta : ℝ) (hE : 1 ≤ E) (heta : 0 < eta)
    (hdelta : 432*eta < delta) (hdeltalt : delta < 1)
    (hQ : ∀ h, 1 < Q h) (hthreshold : ∀ h, 8*E < Real.rpow (Q h) eta)
    (hlog : ∀ h, (r h : ℝ)*Real.log (Q h) ≤ (1+eta)*(r h0 : ℝ)*Real.log (Q h0))
    (c : Fin 3 → Fin 3 → ℝ) (hcsum : (∑ tau : Fin 3, ∑ i : Fin 3, c tau i) = 0)
    (z : ℤ) (hz : z ≠ 0)
    (hbound : ∀ tau : Fin 3, rothLocalAbs tau (z : ℚ) ≤ rothNormalSourceBound tau E eta r Q h0 c) :
    False := by
  have hlo := rothInteger_three_place_lower z hz
  have hhi := rothInteger_three_place_upper z E eta (by linarith) r Q h0 c hcsum hbound
  have hstrict := rothSource_product_bound_lt_one r hr Q h0 E eta delta hE heta hdelta hdeltalt hQ hthreshold hlog
  exact (not_lt_of_ge hlo) (lt_of_le_of_lt hhi hstrict)

theorem roth_auxiliary_integer_satz34
    (L : Fin 3 → Matrix (Fin 3) (Fin 3) ℤ)
    (hL : ∀ tau, (rothLocalRationalMatrix (L tau)).det ≠ 0) :
    ∃ D E : ℝ, 1 ≤ D ∧ 1 ≤ E ∧
      ∀ eta : ℝ, 0 < eta →
      ∀ m : ℕ, 4*(eta^2)⁻¹*Real.log 18 ≤ (m : ℝ) →
      ∀ r : Fin m → ℕ, (∀ h, 0 < r h) →
      ∃ P : MvPolynomial (RothBlockVars m) ℤ,
        P ≠ 0 ∧ rothBlockHomogeneous r P ∧
        (rothKernelBlockHeight P : ℝ) ≤ D^(∑ h, r h) ∧
        (∀ tau i, rothSourceHighIndex r (fun _ => L tau i) ((1/3-eta)*m) P) ∧
        ∀ (delta : ℝ) (c : Fin 3 → Fin 3 → ℝ) (Q : Fin m → ℝ) (h0 : Fin m),
          (∑ tau : Fin 3, ∑ i : Fin 3, c tau i) = 0 →
          (∀ tau i, |c tau i| ≤ 1) → 432*eta < delta → delta < 1 →
          (∀ h, 1 < Q h) →
          (∀ h, 8*E < Real.rpow (Q h) eta) →
          (∀ h, 3*(eta⁻¹+1) < Real.rpow (Q h) eta) →
          (∀ h, (r h0 : ℝ)*Real.log (Q h0) ≤ (r h : ℝ)*Real.log (Q h) ∧
            (r h : ℝ)*Real.log (Q h) ≤ (1+eta)*(r h0 : ℝ)*Real.log (Q h0)) →
          ∀ w : Fin m → Fin 2 → Fin 3 → ℤ,
            (∀ h j i, rothLocalAbs 0 (rothNormalLocalValue (L 0) (w h j) i) ≤
              Real.rpow (Q h) (c 0 i-delta)) →
            (∀ h j i, rothLocalAbs 1 (rothNormalLocalValue (L 1) (w h j) i) ≤ Real.rpow (Q h) (c 1 i)) →
            (∀ h j i, rothLocalAbs 2 (rothNormalLocalValue (L 2) (w h j) i) ≤ Real.rpow (Q h) (c 2 i)) →
            ∀ V : Fin m → Fin 3 → ℤ,
              (∀ h, (∃ i, V h i ≠ 0) ∧ Ideal.span (Set.range (V h)) = ⊤) →
              (∀ h, LinearIndependent ℚ (fun j : Fin 2 => fun i : Fin 3 => (w h j i : ℚ))) →
              (∀ h j, (∑ i : Fin 3, V h i * w h j i) = 0) →
              rothSourceHighIndex r V (m*eta) P := by
  obtain ⟨D,E,hD,hE,hconstruction⟩ := roth_auxiliary_integer_satz34_normal_coefficients L hL
  refine ⟨D,E,hD,hE,?_⟩
  intro eta heta m hm r hr
  obtain ⟨P,hn,hP,hheight,hindex,hbounds⟩ := hconstruction eta heta m hm r hr
  refine ⟨P,hn,hP,hheight,hindex,?_⟩
  intro delta c Q h0 hcsum hc hdelta hdeltalt hQ hEth hgrid hlog w hw0 hw1 hw2
  intro V hrow hli horth J hJ k hk
  by_contra hnonzero
  have hJ' : rothSourceDerivativeWeight r J ≤ 2*eta*m := by
    have hmeta : 0 ≤ eta*(m : ℝ) := mul_nonneg heta.le (Nat.cast_nonneg _)
    nlinarith
  obtain ⟨e,z,_he,hnz,_hz,hzbound⟩ := hbounds delta c Q h0 hcsum hc hdelta hdeltalt hQ hEth hgrid hlog
    w hw0 hw1 hw2 V hrow hli horth J hJ' k hk hnonzero
  exact rothInteger_three_place_contradiction r hr Q h0 E eta delta hE heta hdelta hdeltalt hQ hEth
    (fun h => (hlog h).2) c hcsum z hnz hzbound


end JSP000334
