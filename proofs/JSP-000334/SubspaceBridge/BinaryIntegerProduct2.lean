import SubspaceBridge.BinaryIntegerLocalBound2
open scoped BigOperators Classical
namespace JSP000334
noncomputable def binarySourceBound {m : ℕ} (tau : Fin 3) (E eta A : ℝ)
    (r : Fin m → ℕ) (c : Fin 3 → Fin 2 → ℝ) : ℝ :=
  (2*E)^(∑ h,r h)*Real.exp (A*m*((∑ i : Fin 2,c tau i)/2+if tau=0 then -30*eta else 8*eta))

theorem binary_integer_three_place_upper {m : ℕ} (z : ℤ) (E eta A : ℝ) (hE : 0≤E)
    (r : Fin m → ℕ) (c : Fin 3 → Fin 2 → ℝ)
    (hcsum : (∑ tau : Fin 3,∑ i : Fin 2,c tau i)=0)
    (hz : ∀ tau,rothLocalAbs tau (z : ℚ)≤binarySourceBound tau E eta A r c) :
    rothLocalAbs 0 (z : ℚ)*rothLocalAbs 1 (z : ℚ)*rothLocalAbs 2 (z : ℚ) ≤
      (8*E^3)^(∑ h,r h)*Real.exp (-14*A*m*eta) := by
  have hn (tau : Fin 3) : 0≤binarySourceBound tau E eta A r c := by
    unfold binarySourceBound
    positivity
  have hs : (∑ i : Fin 2,c 0 i)+(∑ i : Fin 2,c 1 i)+(∑ i : Fin 2,c 2 i)=0 := by
    simpa only [Fin.sum_univ_three] using hcsum
  calc
    _ ≤ binarySourceBound 0 E eta A r c*binarySourceBound 1 E eta A r c*binarySourceBound 2 E eta A r c :=
      mul_le_mul (mul_le_mul (hz 0) (hz 1) (rothLocalAbs_nonneg 1 _) (hn 0)) (hz 2)
        (rothLocalAbs_nonneg 2 _) (mul_nonneg (hn 0) (hn 1))
    _ = _ := by
      let R := ∑ h,r h
      let x := fun tau : Fin 3 => A*m*((∑ i : Fin 2,c tau i)/2+if tau=0 then -30*eta else 8*eta)
      have he : x 0+x 1+x 2 = -14*A*m*eta := by
        simp only [x,Fin.isValue,Fin.reduceEq,ite_true,ite_false]
        calc
          _ = A*m*(((∑ i : Fin 2,c 0 i)+(∑ i : Fin 2,c 1 i)+(∑ i : Fin 2,c 2 i))/2-14*eta) := by ring
          _ = _ := by rw [hs];ring
      change ((2*E)^R*Real.exp (x 0))*((2*E)^R*Real.exp (x 1))*((2*E)^R*Real.exp (x 2)) = _
      calc
        _ = ((2*E)^R*(2*E)^R*(2*E)^R)*Real.exp (x 0+x 1+x 2) := by
          rw [Real.exp_add,Real.exp_add]
          ring
        _ = _ := by
          rw [he,← mul_pow,← mul_pow]
          congr 2
          ring

theorem binary_product_bound_lt_one {m : ℕ} (r : Fin m → ℕ)
    (hr : ∀ h, 0 < r h) (Q : Fin m → ℝ) (h0 : Fin m)
    (E eta delta : ℝ) (hE : 1 ≤ E) (heta : 0 < eta)
    (hdelta : 40*eta < delta) (hdeltalt : delta < 1)
    (hQ : ∀ h, 1 < Q h) (hthreshold : ∀ h, 2*E < Real.rpow (Q h) eta)
    (hlog : ∀ h, (r h : ℝ)*Real.log (Q h) ≤ (1+eta)*(r h0 : ℝ)*Real.log (Q h0)) :
    (8*E^3)^(∑ h, r h) * Real.exp (-14*((r h0 : ℝ)*Real.log (Q h0))*m*eta) < 1 := by
  let A := (r h0 : ℝ)*Real.log (Q h0)
  let R := ∑ h, r h
  have hm : 0 < m := by have hh := h0.isLt; omega
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hA : 0 < A := mul_pos (by exact_mod_cast hr h0) (Real.log_pos (hQ h0))
  have hR : 0 < R := Finset.sum_pos (fun h _ => hr h) ⟨h0,Finset.mem_univ _⟩
  have hEpos : 0 < E := lt_of_lt_of_le zero_lt_one hE
  have h8E : 0 < 2*E := by positivity
  have hgrowth (h : Fin m) : Real.log (2*E) < eta*Real.log (Q h) := by
    have ht := Real.log_lt_log h8E (hthreshold h)
    simpa only [Real.rpow_eq_pow, Real.log_rpow (lt_trans zero_lt_one (hQ h))] using ht
  have hterm (h : Fin m) : (r h : ℝ)*Real.log (2*E) < (r h : ℝ)*(eta*Real.log (Q h)) :=
    mul_lt_mul_of_pos_left (hgrowth h) (by exact_mod_cast hr h)
  have hsum := Finset.sum_lt_sum_of_nonempty (s := Finset.univ)
    (⟨h0,Finset.mem_univ _⟩ : (Finset.univ : Finset (Fin m)).Nonempty)
    (fun h _ => hterm h)
  have hstrict : (R : ℝ)*Real.log (2*E) < eta*(∑ h : Fin m, (r h : ℝ)*Real.log (Q h)) := by
    simpa only [← Finset.sum_mul, mul_left_comm, ← Finset.mul_sum, ← Nat.cast_sum, R] using hsum
  have hsumupper : (∑ h : Fin m, (r h : ℝ)*Real.log (Q h)) ≤ (1+eta)*A*m := by
    have hs := Finset.sum_le_sum (fun h (_ : h ∈ (Finset.univ : Finset (Fin m))) => hlog h)
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, A, mul_assoc, mul_comm, mul_left_comm] using hs
  have hlogcube : Real.log (8*E^3) ≤ 3*Real.log (2*E) := by
    calc
      _ ≤ Real.log ((2*E)^3) := Real.log_le_log (by positivity) (by nlinarith [pow_nonneg hEpos.le 3])
      _ = _ := by rw [Real.log_pow]; norm_num
  have hscaled := mul_le_mul_of_nonneg_left hlogcube (Nat.cast_nonneg R)
  have hscaledstrict := mul_lt_mul_of_pos_left hstrict (by norm_num : (0:ℝ) < 3)
  have hscaledupper := mul_le_mul_of_nonneg_left hsumupper (by positivity : 0 ≤ 3*eta)
  have hsmall : 3*(1+eta) < 14 := by linarith
  have hpositive : 0 < A*m*eta := mul_pos (mul_pos hA hmR) heta
  have hgap := mul_lt_mul_of_pos_right hsmall hpositive
  have hexp : (R : ℝ)*Real.log (8*E^3) - 14*A*m*eta < 0 := by nlinarith
  have hbase : 0 < 8*E^3 := by positivity
  calc
    _ = Real.exp ((R : ℝ)*Real.log (8*E^3) - 14*A*m*eta) := by
      rw [Real.exp_sub, Real.exp_nat_mul, Real.exp_log hbase]
      change (8*E^3)^R * Real.exp (-14*A*m*eta) = (8*E^3)^R / Real.exp (14*A*m*eta)
      rw [div_eq_mul_inv, ← Real.exp_neg]
      congr 2
      ring
    _ < 1 := Real.exp_lt_one_iff.mpr hexp

end JSP000334
