import SubspaceBridge.AuxiliaryMatrixSupport
import Mathlib.NumberTheory.SiegelsLemma

open scoped BigOperators Classical
attribute [local instance] Matrix.seminormedAddCommGroup
namespace JSP000334

theorem rothAux_block_choose_le_pow (r : ℕ) : (r + 2).choose 2 ≤ 3 ^ r := by
  have hlinear (n : ℕ) : n + 1 ≤ (n + 2).choose 2 := by
    induction n with
    | zero => norm_num
    | succ n ih =>
      rw [show n + 1 + 2 = (n + 2) + 1 by omega, Nat.choose_succ_succ', Nat.choose_one_right]
      omega
  induction r with
  | zero => norm_num
  | succ r ih =>
    rw [show r + 1 + 2 = (r + 2) + 1 by omega, Nat.choose_succ_succ', Nat.choose_one_right]
    have h := hlinear r
    calc
      _ ≤ 3 * (r + 2).choose 2 := by
        change (r + 2) + (r + 2).choose 2 ≤ 3 * (r + 2).choose 2
        omega
      _ ≤ 3 * 3 ^ r := Nat.mul_le_mul_left 3 ih
      _ = _ := by simp [pow_succ, Nat.mul_comm]

theorem rothAuxDimension_le_three_pow {m : ℕ} (r : Fin m → ℕ) :
    rothAuxDimension r ≤ 3 ^ (∑ h, r h) := by
  rw [rothAuxDimension_eq]
  calc
    _ ≤ ∏ h : Fin m, 3 ^ r h := by
      exact Finset.prod_le_prod (fun _ _ => Nat.zero_le _) (fun h _ => rothAux_block_choose_le_pow (r h))
    _ = _ := Finset.prod_pow_eq_pow_sum _ _ _

theorem rothAuxMatrix_norm_bound {m : ℕ} (r : Fin m → ℕ) (eta : ℝ)
    (L : Fin 3 → Fin 3 → Fin 3 → ℤ) (hL : ∀ tau i, ∃ j, L tau i j ≠ 0) :
    ‖rothAuxMatrix r eta L hL‖ ≤ ((6 * rothAuxSourceHeight L) ^ (∑ h, r h) : ℕ) := by
  apply (Matrix.norm_le_iff (by positivity)).mpr
  intro q b
  rw [Int.norm_eq_abs, ← Int.cast_abs]
  exact_mod_cast rothAuxMatrix_entry_bound r eta L hL q b

theorem rothAuxMatrix_siegel_base_bound {m : ℕ} (r : Fin m → ℕ) (eta : ℝ)
    (L : Fin 3 → Fin 3 → Fin 3 → ℤ) (hL : ∀ tau i, ∃ j, L tau i j ≠ 0) :
    (Fintype.card (RothAuxCoefficients r) : ℝ) * max 1 ‖rothAuxMatrix r eta L hL‖ ≤
      ((18 * rothAuxSourceHeight L) ^ (∑ h, r h) : ℕ) := by
  have hA := rothAuxSourceHeight_one_le L
  have hone : 1 ≤ ((6 * rothAuxSourceHeight L) ^ (∑ h, r h) : ℕ) := by
    have hp : 0 < (6 * rothAuxSourceHeight L) ^ (∑ h, r h) := pow_pos (by omega) _
    omega
  have hmax : max 1 ‖rothAuxMatrix r eta L hL‖ ≤
      ((6 * rothAuxSourceHeight L) ^ (∑ h, r h) : ℕ) :=
    max_le (by exact_mod_cast hone) (rothAuxMatrix_norm_bound r eta L hL)
  have hdim : (Fintype.card (RothAuxCoefficients r) : ℝ) ≤ (3 : ℝ) ^ (∑ h, r h) := by
    exact_mod_cast rothAuxDimension_le_three_pow r
  calc
    _ ≤ (3 : ℝ) ^ (∑ h, r h) * ((6 * rothAuxSourceHeight L) ^ (∑ h, r h) : ℕ) :=
      mul_le_mul hdim hmax (by positivity) (by positivity)
    _ = _ := by push_cast; rw [← mul_pow]; congr 1; ring

noncomputable def rothAuxRowsEquivFin {m : ℕ} (r : Fin m → ℕ) (eta : ℝ) :
    RothAuxEquations r eta ≃ Fin (Fintype.card (RothAuxEquations r eta)) :=
  Fintype.equivFin _

noncomputable def rothAuxColsEquivFin {m : ℕ} (r : Fin m → ℕ) :
    RothAuxCoefficients r ≃ Fin (Fintype.card (RothAuxCoefficients r)) :=
  Fintype.equivFin _

noncomputable def rothAuxFinMatrix {m : ℕ} (r : Fin m → ℕ) (eta : ℝ)
    (L : Fin 3 → Fin 3 → Fin 3 → ℤ) (hL : ∀ tau i, ∃ j, L tau i j ≠ 0) :
    Matrix (Fin (Fintype.card (RothAuxEquations r eta)))
      (Fin (Fintype.card (RothAuxCoefficients r))) ℤ :=
  Matrix.reindex (rothAuxRowsEquivFin r eta) (rothAuxColsEquivFin r)
    (rothAuxMatrix r eta L hL)

theorem rothAuxFinMatrix_mulVec {m : ℕ} (r : Fin m → ℕ) (eta : ℝ)
    (L : Fin 3 → Fin 3 → Fin 3 → ℤ) (hL : ∀ tau i, ∃ j, L tau i j ≠ 0)
    (t : Fin (Fintype.card (RothAuxCoefficients r)) → ℤ) :
    (rothAuxFinMatrix r eta L hL).mulVec t =
      ((rothAuxMatrix r eta L hL).mulVec (t ∘ rothAuxColsEquivFin r)) ∘
        (rothAuxRowsEquivFin r eta).symm := by
  exact Matrix.submatrix_mulVec_equiv (rothAuxMatrix r eta L hL) t
    (rothAuxRowsEquivFin r eta).symm (rothAuxColsEquivFin r).symm

theorem rothAuxFinVector_transport {m : ℕ} (r : Fin m → ℕ)
    (t : Fin (Fintype.card (RothAuxCoefficients r)) → ℤ) :
    (t ∘ rothAuxColsEquivFin r ≠ 0 ↔ t ≠ 0) ∧
      ‖t ∘ rothAuxColsEquivFin r‖ = ‖t‖ := by
  constructor
  · constructor
    · intro h ht
      exact h (by simp [ht])
    · intro h hc
      apply h
      funext j
      have hj := congrFun hc ((rothAuxColsEquivFin r).symm j)
      simpa using hj
  · apply le_antisymm
    · exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
        (fun b => norm_le_pi_norm t (rothAuxColsEquivFin r b))
    · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
      intro j
      simpa using norm_le_pi_norm (t ∘ rothAuxColsEquivFin r)
        ((rothAuxColsEquivFin r).symm j)

theorem rothAuxFinMatrix_norm {m : ℕ} (r : Fin m → ℕ) (eta : ℝ)
    (L : Fin 3 → Fin 3 → Fin 3 → ℤ) (hL : ∀ tau i, ∃ j, L tau i j ≠ 0) :
    ‖rothAuxFinMatrix r eta L hL‖ = ‖rothAuxMatrix r eta L hL‖ := by
  apply le_antisymm
  · apply (Matrix.norm_le_iff (norm_nonneg _)).mpr
    intro q b
    exact Matrix.norm_entry_le_entrywise_sup_norm (rothAuxMatrix r eta L hL)
      (i := (rothAuxRowsEquivFin r eta).symm q) (j := (rothAuxColsEquivFin r).symm b)
  · apply (Matrix.norm_le_iff (norm_nonneg _)).mpr
    intro q b
    have h := Matrix.norm_entry_le_entrywise_sup_norm (rothAuxFinMatrix r eta L hL)
      (i := rothAuxRowsEquivFin r eta q) (j := rothAuxColsEquivFin r b)
    simpa [rothAuxFinMatrix, Matrix.reindex_apply] using h

theorem rothAuxMatrix_exists_bounded_int_kernel {m : ℕ} (r : Fin m → ℕ)
    (hr : ∀ h, 0 < r h) (eta : ℝ) (heta : 0 < eta)
    (hm : 4 * (eta ^ 2)⁻¹ * Real.log 18 ≤ (m : ℝ))
    (L : Fin 3 → Fin 3 → Fin 3 → ℤ) (hL : ∀ tau i, ∃ j, L tau i j ≠ 0) :
    ∃ c : RothAuxCoefficients r → ℤ, c ≠ 0 ∧
      (rothAuxMatrix r eta L hL).mulVec c = 0 ∧
      ∀ b, |c b| ≤ (18 * (rothAuxSourceHeight L : ℤ)) ^ (∑ h, r h) := by
  classical
  have hcard := rothAuxMatrix_cardinalities r hr eta heta hm
  have hN := hcard.2.1
  have hhalf := hcard.2.2.2
  have hA := rothAuxSourceHeight_one_le L
  have hbudget : (1 : ℤ) ≤ (18 * (rothAuxSourceHeight L : ℤ)) ^ (∑ h, r h) := by
    have hb : (1 : ℤ) ≤ 18 * (rothAuxSourceHeight L : ℤ) := by exact_mod_cast (show 1 ≤ 18 * rothAuxSourceHeight L by omega)
    exact one_le_pow₀ hb
  by_cases hM : Fintype.card (RothAuxEquations r eta) = 0
  · obtain ⟨b₀⟩ := Fintype.card_pos_iff.mp hN
    let c : RothAuxCoefficients r → ℤ := fun b => if b = b₀ then 1 else 0
    refine ⟨c, ?_, ?_, ?_⟩
    · intro hc
      have hc₀ := congrFun hc b₀
      simp [c] at hc₀
    · funext q
      have hp := Fintype.card_pos_iff.mpr (Nonempty.intro q)
      omega
    · intro b
      dsimp [c]
      split_ifs
      · simpa using hbudget
      · simp only [abs_zero]; exact le_trans zero_le_one hbudget
  · have hMpos : 0 < Fintype.card (RothAuxEquations r eta) := Nat.pos_of_ne_zero hM
    have hNreal : 0 < (Fintype.card (RothAuxCoefficients r) : ℝ) := by exact_mod_cast hN
    have hltreal : (Fintype.card (RothAuxEquations r eta) : ℝ) <
        (Fintype.card (RothAuxCoefficients r) : ℝ) := by linarith
    have hlt : Fintype.card (RothAuxEquations r eta) < Fintype.card (RothAuxCoefficients r) := by exact_mod_cast hltreal
    obtain ⟨t, ht, hker, hnorm⟩ := Int.Matrix.exists_ne_zero_int_vec_norm_le
      (rothAuxFinMatrix r eta L hL) (by simpa using hlt) (by simpa using hMpos)
    let c := t ∘ rothAuxColsEquivFin r
    have hc : c ≠ 0 := (rothAuxFinVector_transport r t).1.mpr ht
    have hkernel : (rothAuxMatrix r eta L hL).mulVec c = 0 := by
      funext q
      rw [rothAuxFinMatrix_mulVec] at hker
      have hq := congrFun hker (rothAuxRowsEquivFin r eta q)
      simpa [c] using hq
    simp only [Fintype.card_fin, rothAuxFinMatrix_norm] at hnorm
    refine ⟨c, hc, hkernel, ?_⟩
    have hdenom : 0 < (Fintype.card (RothAuxCoefficients r) : ℝ) -
        (Fintype.card (RothAuxEquations r eta) : ℝ) := sub_pos.mpr hltreal
    have hexp : (Fintype.card (RothAuxEquations r eta) : ℝ) /
        ((Fintype.card (RothAuxCoefficients r) : ℝ) -
        (Fintype.card (RothAuxEquations r eta) : ℝ)) ≤ 1 := by
      apply (div_le_one hdenom).mpr
      linarith
    have hbase : 1 ≤ (Fintype.card (RothAuxCoefficients r) : ℝ) *
        max 1 ‖rothAuxMatrix r eta L hL‖ := by
      have hn : (1 : ℝ) ≤ Fintype.card (RothAuxCoefficients r) := by exact_mod_cast hN
      nlinarith [le_max_left (1 : ℝ) ‖rothAuxMatrix r eta L hL‖]
    have hnorm' := hnorm.trans ((Real.rpow_le_self_of_one_le hbase hexp).trans
      (rothAuxMatrix_siegel_base_bound r eta L hL))
    intro b
    have hcnorm : ‖c‖ = ‖t‖ := (rothAuxFinVector_transport r t).2
    have hb := (norm_le_pi_norm c b).trans (hcnorm.le.trans hnorm')
    rw [Int.norm_eq_abs, ← Int.cast_abs] at hb
    exact_mod_cast hb

end JSP000334
