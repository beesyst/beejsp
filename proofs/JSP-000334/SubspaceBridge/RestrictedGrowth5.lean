import SubspaceBridge.MinimaMultiplicative5
import SubspaceBridge.RestrictedLower5
open scoped BigOperators
namespace CompoundFeasibility.RestrictedGrowth5
open MinimaPower5 RestrictedGeometry5
noncomputable section

def growthConstant5 (j : Fin 4) (C5 : ℝ) : ℝ :=
  ((2 : ℝ)^(j.val+1) / (Nat.factorial (j.val+1) : ℝ)) /
    C5^(((j.val+1 : ℕ) : ℝ)/5)

theorem growthConstant5_pos (j : Fin 4) (C5 : ℝ) (hC5 : 0 < C5) :
    0 < growthConstant5 j C5 := by
  unfold growthConstant5
  exact div_pos (div_pos (by positivity) (by positivity)) (Real.rpow_pos_of_pos hC5 _)

theorem ambient_prefix_product_eq5 (P : Submodule ℚ (Fin 5 → ℚ))
    (hP : Module.finrank ℚ P ≤ 4) (j : Fin 4)
    (hdim : Module.finrank ℚ P = j.val+1) (lam : Fin 5 → ℝ) :
    (∏ i : Fin (Module.finrank ℚ P), lam (ambientPrefixIndex5 P hP i)) =
      prefixProduct5 j lam := by
  apply Fintype.prod_equiv (finCongr hdim)
  intro i
  congr 1


def quantitativeOriginalPoint5 (P : Submodule ℚ (Fin 5 → ℚ))
    (hP : Module.finrank ℚ P ≤ 4) (j : Fin 4)
    (A₂ A₃ : Matrix (Fin 5) (Fin 5) ℚ) (L : Matrix (Fin 5) (Fin 5) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c₀ c₂ c₃ : Fin 5 → ℝ) (delta C5 : ℝ) : Prop :=
    (∀ i : Fin 5, i.val < j.val+1 →
      sourceMinima5 A₂ A₃ L hL Q hQ c₀ c₂ c₃ i <
        (tailProduct5 j (sourceMinima5 A₂ A₃ L hL Q hQ c₀ c₂ c₃))^
          (1/(5-((j.val+1 : ℕ) : ℝ))) * Q^(-delta)) ∧
    prefixProduct5 j (sourceMinima5 A₂ A₃ L hL Q hQ c₀ c₂ c₃) ≤
      C5^(((j.val+1 : ℕ) : ℝ)/5) * Q^(-decayExponent5 j delta) ∧
    (∏ i, restrictedMinima5 P A₂ A₃ L hL Q hQ c₀ c₂ c₃ i) =
      prefixProduct5 j (sourceMinima5 A₂ A₃ L hL Q hQ c₀ c₂ c₃) ∧
    (∏ i, restrictedMinima5 P A₂ A₃ L hL Q hQ c₀ c₂ c₃ i) ≤
      C5^(((j.val+1 : ℕ) : ℝ)/5) * Q^(-decayExponent5 j delta) ∧
    Module.finrank ℝ (rationalRealSpan5 P) = j.val+1 ∧
    Module.finrank ℤ (restrictedLattice5 P A₂ A₃ Q c₂ c₃) = j.val+1 ∧
    0 < (restrictedMeasure5 P).real (restrictedBody5 P L Q c₀) ∧
    (restrictedMeasure5 P) (restrictedBody5 P L Q c₀) < ⊤ ∧
    0 < ZLattice.covolume (restrictedLattice5 P A₂ A₃ Q c₂ c₃) (restrictedMeasure5 P) ∧
    (2 : ℝ)^(j.val+1) / (Nat.factorial (j.val+1) : ℝ) ≤
      (∏ i, restrictedMinima5 P A₂ A₃ L hL Q hQ c₀ c₂ c₃ i) *
        (restrictedMeasure5 P).real (restrictedBody5 P L Q c₀) /
          ZLattice.covolume (restrictedLattice5 P A₂ A₃ Q c₂ c₃) (restrictedMeasure5 P) ∧
    growthConstant5 j C5 * Q^(decayExponent5 j delta) ≤
      (restrictedMeasure5 P).real (restrictedBody5 P L Q c₀) /
        ZLattice.covolume (restrictedLattice5 P A₂ A₃ Q c₂ c₃) (restrictedMeasure5 P)

theorem power_growth_of_product_decay5 (j : Fin 4) (Q delta C5 p volume covol : ℝ)
    (hQ : 0 < Q) (hC5 : 0 < C5) (hv : 0 < volume) (hc : 0 < covol)
    (hdec : p ≤ C5^(((j.val+1 : ℕ) : ℝ)/5) * Q^(-decayExponent5 j delta))
    (hmink : (2 : ℝ)^(j.val+1) / (Nat.factorial (j.val+1) : ℝ) ≤ p*volume/covol) :
    growthConstant5 j C5 * Q^(decayExponent5 j delta) ≤ volume/covol := by
  have hpow : Q^(-decayExponent5 j delta) * Q^(decayExponent5 j delta) = 1 := by
    rw [← Real.rpow_add hQ]
    simp
  have hstep : (2 : ℝ)^(j.val+1) / (Nat.factorial (j.val+1) : ℝ) ≤
      (C5^(((j.val+1 : ℕ) : ℝ)/5) * Q^(-decayExponent5 j delta))*(volume/covol) := by
    calc
      _ ≤ p*(volume/covol) := by simpa [mul_div_assoc] using hmink
      _ ≤ _ := mul_le_mul_of_nonneg_right hdec (le_of_lt (div_pos hv hc))
  have h := mul_le_mul_of_nonneg_right hstep
    (le_of_lt (Real.rpow_pos_of_pos hQ (decayExponent5 j delta)))
  have hcancel :
      (C5^(((j.val+1 : ℕ) : ℝ)/5) * Q^(-decayExponent5 j delta)) *
        (volume/covol) * Q^(decayExponent5 j delta) =
      (volume/covol) * C5^(((j.val+1 : ℕ) : ℝ)/5) := by
    calc
      _ = (volume/covol) * C5^(((j.val+1 : ℕ) : ℝ)/5) *
          (Q^(-decayExponent5 j delta)*Q^(decayExponent5 j delta)) := by ring
      _ = _ := by rw [hpow, mul_one]
  rw [hcancel] at h
  unfold growthConstant5
  rw [div_mul_eq_mul_div]
  exact (div_le_iff₀ (Real.rpow_pos_of_pos hC5 _)).mpr h

theorem source_quantitative_original_point5 (P : Submodule ℚ (Fin 5 → ℚ))
    (hPlo : 1 ≤ Module.finrank ℚ P) (hP : Module.finrank ℚ P ≤ 4)
    (j : Fin 4) (hdim : Module.finrank ℚ P = j.val+1)
    (A₂ A₃ : Matrix (Fin 5) (Fin 5) ℚ) (L : Matrix (Fin 5) (Fin 5) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c₀ c₂ c₃ : Fin 5 → ℝ) (delta C5 : ℝ) (hC5 : 0 < C5)
    (hg : sourceMinima5 A₂ A₃ L hL Q hQ c₀ c₂ c₃ j.castSucc <
      sourceMinima5 A₂ A₃ L hL Q hQ c₀ c₂ c₃ j.succ * Q^(-delta))
    (hprod : ∏ i, sourceMinima5 A₂ A₃ L hL Q hQ c₀ c₂ c₃ i ≤ C5)
    (hEq : ∀ i, restrictedMinima5 P A₂ A₃ L hL Q hQ c₀ c₂ c₃ i =
      sourceMinima5 A₂ A₃ L hL Q hQ c₀ c₂ c₃ (ambientPrefixIndex5 P hP i)) :
    quantitativeOriginalPoint5 P hP j A₂ A₃ L hL Q hQ c₀ c₂ c₃ delta C5 := by
  obtain ⟨hp,hm⟩ := sourceMinima5_pos_mono A₂ A₃ L hL Q hQ c₀ c₂ c₃
  have hQpos : 0 < Q := lt_trans zero_lt_one hQ
  have h718 := source_gap_geometric_mean5 j _ Q delta hQpos hp hm hg
  have h719 := source_prefix_product_decay5 j _ Q delta C5 hQpos hC5 hp hm hg hprod
  have heq : (∏ i, restrictedMinima5 P A₂ A₃ L hL Q hQ c₀ c₂ c₃ i) =
      prefixProduct5 j (sourceMinima5 A₂ A₃ L hL Q hQ c₀ c₂ c₃) := by
    calc
      _ = ∏ i, sourceMinima5 A₂ A₃ L hL Q hQ c₀ c₂ c₃ (ambientPrefixIndex5 P hP i) :=
        Finset.prod_congr rfl (fun i _ => hEq i)
      _ = _ := ambient_prefix_product_eq5 P hP j hdim _
  have hdec : (∏ i, restrictedMinima5 P A₂ A₃ L hL Q hQ c₀ c₂ c₃ i) ≤
      C5^(((j.val+1 : ℕ) : ℝ)/5) * Q^(-decayExponent5 j delta) := by
    rw [heq]
    exact h719
  have hReal := rationalRealSpan5_finrank P hP
  have hInt := restrictedLattice5_rank P hP A₂ A₃ Q c₂ c₃
  have hVolume := restrictedBody5_volume_pos_finite P L hL Q hQ c₀
  have hVol := hVolume.1
  have hFinite := hVolume.2
  have hCov := restrictedLattice5_covolume_pos P A₂ A₃ Q c₂ c₃
  have hMlower := source_restricted_minkowski_lower5 P hPlo hP A₂ A₃ L hL Q hQ c₀ c₂ c₃
  have hM : (2 : ℝ)^(j.val+1) / (Nat.factorial (j.val+1) : ℝ) ≤
      (∏ i, restrictedMinima5 P A₂ A₃ L hL Q hQ c₀ c₂ c₃ i) *
        (restrictedMeasure5 P).real (restrictedBody5 P L Q c₀) /
          ZLattice.covolume (restrictedLattice5 P A₂ A₃ Q c₂ c₃) (restrictedMeasure5 P) := by
    calc
      _ = (2 : ℝ)^(Module.finrank ℚ P) / (Nat.factorial (Module.finrank ℚ P) : ℝ) := by rw [hdim]
      _ ≤ _ := hMlower
  exact ⟨h718,h719,heq,hdec,hReal.trans hdim,hInt.trans hdim,hVol,hFinite,hCov,hM,
    power_growth_of_product_decay5 j Q delta C5 _ _ _ hQpos hC5 hVol hCov hdec hM⟩

end
end CompoundFeasibility.RestrictedGrowth5
