import SubspaceBridge.SourceSatz51Rounding218
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceSatz51Entry218

def sourceSet218 (q delta : ℝ) (A c2 c3 : Fin 10 → ℝ) : Finset (Fin 3 → Fin 10) :=
  Finset.univ.filter (fun s => 1 ≤ A (s 0)*q^(c2 (s 1))*q^(c3 (s 2))*q^(delta/4))

theorem source_set_nonempty218 (q delta : ℝ) (hq : 1 < q) (hd : 0 < delta)
    (A c2 c3 : Fin 10 → ℝ) (hA : ∀ i, 0 < A i)
    (hbal : (∏ i, A i*q^(c2 i)*q^(c3 i)) = 1) : (sourceSet218 q delta A c2 c3).Nonempty := by
  have hp (i : Fin 10) : 0 < A i*q^(c2 i)*q^(c3 i) :=
    mul_pos (mul_pos (hA i) (Real.rpow_pos_of_pos (zero_lt_one.trans hq) _))
      (Real.rpow_pos_of_pos (zero_lt_one.trans hq) _)
  have hi : ∃ i, 1 ≤ A i*q^(c2 i)*q^(c3 i) := by
    by_contra hh
    push_neg at hh
    have h := Finset.prod_lt_prod_of_nonempty (s := Finset.univ)
      (f := fun i => A i*q^(c2 i)*q^(c3 i)) (g := fun _ => (1 : ℝ))
      (fun i _ => hp i) (fun i _ => hh i) Finset.univ_nonempty
    simp [hbal] at h
  obtain ⟨i,hi⟩ := hi
  refine ⟨fun _ => i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩⟩
  have hr := Real.one_le_rpow hq.le (show (0 : ℝ) ≤ delta/4 by linarith)
  nlinarith

theorem source_set_unbounded_selection218 (Omega : Set ℝ) (hO : ¬ BddAbove Omega)
    (delta : ℝ) (A : ℝ → Fin 10 → ℝ) (c2 c3 : Fin 10 → ℝ)
    (hne : ∀ q ∈ Omega, (sourceSet218 q delta (A q) c2 c3).Nonempty) :
    ∃ S0 : Finset (Fin 3 → Fin 10), S0.Nonempty ∧
      ∃ U : Set ℝ, U ⊆ Omega ∧ ¬ BddAbove U ∧ ∀ q ∈ U, sourceSet218 q delta (A q) c2 c3 = S0 := by
  by_contra hn
  have hb (S0 : Finset (Fin 3 → Fin 10)) :
      BddAbove {q | q ∈ Omega ∧ sourceSet218 q delta (A q) c2 c3 = S0} := by
    by_contra hu
    obtain ⟨q,hq,hS⟩ := nonempty_of_not_bddAbove hu
    exact hn ⟨S0,hS ▸ hne q hq,_,fun _ h => h.1,hu,fun _ h => h.2⟩
  choose b hb using hb
  obtain ⟨B,hB⟩ := (Set.finite_range b).bddAbove
  apply hO
  refine ⟨B,?_⟩
  intro q hq
  exact (hb _ (show q ∈ {x | x ∈ Omega ∧ sourceSet218 x delta (A x) c2 c3 =
    sourceSet218 q delta (A q) c2 c3} from ⟨hq,rfl⟩)).trans (hB (Set.mem_range_self _))

theorem rounded_inverse_upper218 (p : ℕ) (hp : 1 < p) (q c : ℝ)
    (hq : 1 < q) (hc : -1 ≤ c ∧ c ≤ 0) :
    (p : ℝ)^(-roundedExponent218 p q c) < (p : ℝ)*q := by
  have h := rounded_local218 p hp q c hq hc.2
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (lt_trans Nat.zero_lt_one hp)
  have hq0 := zero_lt_one.trans hq
  have hi : (p : ℝ)^(-roundedExponent218 p q c) < (p : ℝ)/q^c := by
    rw [zpow_neg]
    rw [← one_div]
    apply (div_lt_div_iff₀ (zpow_pos hp0 _) (Real.rpow_pos_of_pos hq0 _)).mpr
    simpa only [one_mul] using (div_lt_iff₀ (zpow_pos hp0 _)).mp h.2.2.2.2
  apply hi.trans_le
  rw [div_eq_mul_inv,← Real.rpow_neg hq0.le]
  apply mul_le_mul_of_nonneg_left _ hp0.le
  calc
    q^(-c) ≤ q^(1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hq.le (by linarith [hc.1])
    _ = q := Real.rpow_one q

theorem corrected_sizes218 (q : ℝ) (hq : 6 < q) (c2 c3 A : Fin 10 → ℝ)
    (h2 : ∀ i, -1 ≤ c2 i ∧ c2 i ≤ 0) (h3 : ∀ i, -1 ≤ c3 i ∧ c3 i ≤ 0)
    (hA : ∀ i, 0 < A i) (hs : ∀ i, A i < q ∧ (A i)⁻¹ < q) (i : Fin 10) :
    widthScale218 q c2 c3*A i < q^2 ∧ (widthScale218 q c2 c3*A i)⁻¹ < q^2 ∧
      (2 : ℝ)^(-roundedExponent218 2 q (c2 i)) < q^2 ∧
      (3 : ℝ)^(-roundedExponent218 3 q (c3 i)) < q^2 := by
  have hq1 : 1 < q := by linarith
  have ht := width_scale_bounds218 q hq1 c2 c3 (fun i => (h2 i).2) (fun i => (h3 i).2)
  have hpos := mul_pos ht.2.2.1 (hA i)
  have hupper : widthScale218 q c2 c3*A i < 6*q := by
    have hh := mul_lt_mul_of_pos_right ht.2.1 (hA i)
    have hh' := mul_lt_mul_of_pos_left (hs i).1 (by norm_num : (0 : ℝ) < 6)
    exact hh.trans hh'
  have hA_scale : A i ≤ widthScale218 q c2 c3*A i := by nlinarith [ht.1,hA i]
  have hinv : (widthScale218 q c2 c3*A i)⁻¹ ≤ (A i)⁻¹ :=
    (inv_le_inv₀ hpos (hA i)).mpr hA_scale
  have hi2 := rounded_inverse_upper218 2 (by decide) q (c2 i) hq1 (h2 i)
  have hi3 := rounded_inverse_upper218 3 (by decide) q (c3 i) hq1 (h3 i)
  norm_num only [Nat.cast_ofNat] at hi2 hi3
  refine ⟨?_,?_,?_,?_⟩ <;> nlinarith [(hs i).2]

theorem source_set_selected218 (q delta : ℝ) (hq : 1 < q) (c2 c3 A : Fin 10 → ℝ)
    (h2 : ∀ i, c2 i ≤ 0) (h3 : ∀ i, c3 i ≤ 0) (hA : ∀ i, 0 < A i)
    (hslack : 6 ≤ q^(delta/4)) (s : Fin 3 → Fin 10) (hs : s ∈ sourceSet218 q delta A c2 c3) :
    1 ≤ (widthScale218 q c2 c3*A (s 0))*(2 : ℝ)^(roundedExponent218 2 q (c2 (s 1)))*
      (3 : ℝ)^(roundedExponent218 3 q (c3 (s 2)))*(q^2)^((delta/2)/2) := by
  have hq0 := zero_lt_one.trans hq
  have ht := width_scale_bounds218 q hq c2 c3 h2 h3
  have ha := rounded_local218 2 (by decide) q (c2 (s 1)) hq (h2 _)
  have hb := rounded_local218 3 (by decide) q (c3 (s 2)) hq (h3 _)
  have h2p : q^(c2 (s 1)) ≤ 2*(2 : ℝ)^(roundedExponent218 2 q (c2 (s 1))) :=
    by simpa only [Nat.cast_ofNat,mul_comm] using ((div_lt_iff₀ (by norm_num : (0 : ℝ) < 2)).mp ha.2.1).le
  have h3p : q^(c3 (s 2)) ≤ 3*(3 : ℝ)^(roundedExponent218 3 q (c3 (s 2))) :=
    by simpa only [Nat.cast_ofNat,mul_comm] using ((div_lt_iff₀ (by norm_num : (0 : ℝ) < 3)).mp hb.2.1).le
  have hm := mul_le_mul h2p h3p (Real.rpow_pos_of_pos hq0 _).le (by positivity)
  have hm' := mul_le_mul_of_nonneg_left hm (mul_pos (hA (s 0)) (Real.rpow_pos_of_pos hq0 (delta/4))).le
  have htq : 6 ≤ widthScale218 q c2 c3*q^(delta/4) := by
    have hh := mul_le_mul_of_nonneg_right ht.1 (Real.rpow_pos_of_pos hq0 (delta/4)).le
    nlinarith
  have hA0 := hA (s 0)
  have htq' := mul_le_mul_of_nonneg_right htq
    (by positivity : 0 ≤ A (s 0)*(2 : ℝ)^(roundedExponent218 2 q (c2 (s 1)))*
      (3 : ℝ)^(roundedExponent218 3 q (c3 (s 2)))*q^(delta/4))
  have hmem := (Finset.mem_filter.mp hs).2
  have hp : (q^2)^((delta/2)/2) = q^(delta/4)*q^(delta/4) := by
    rw [← Real.rpow_natCast_mul hq0.le,← Real.rpow_add hq0]
    congr 1
    ring
  rw [hp]
  nlinarith

end CompoundFeasibility.SourceSatz51Entry218
