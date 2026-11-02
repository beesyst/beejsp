import SubspaceBridge.MinimaPower4
import SubspaceBridge.RestrictedSource4
open scoped BigOperators
namespace CompoundFeasibility.RestrictedGrowth4
open MinimaPower4 RestrictedGeometry4
noncomputable section

def growthConstant4 (j : Fin 3) (C4 : ℝ) : ℝ :=
  ((2 : ℝ)^(j.val+1) / (Nat.factorial (j.val+1) : ℝ)) /
    C4^(((j.val+1 : ℕ) : ℝ)/4)

theorem growthConstant4_pos (j : Fin 3) (C4 : ℝ) (hC4 : 0 < C4) :
    0 < growthConstant4 j C4 := by
  unfold growthConstant4
  exact div_pos (div_pos (by positivity) (by positivity)) (Real.rpow_pos_of_pos hC4 _)

theorem ambient_prefix_product_eq4 (P : Submodule ℚ (Fin 4 → ℚ))
    (hP : Module.finrank ℚ P ≤ 3) (j : Fin 3)
    (hdim : Module.finrank ℚ P = j.val+1) (lam : Fin 4 → ℝ) :
    (∏ i : Fin (Module.finrank ℚ P), lam (ambientPrefixIndex4 P hP i)) =
      prefixProduct4 j lam := by
  apply Fintype.prod_equiv (finCongr hdim)
  intro i
  congr 1


def quantitativeOriginalPoint4 (P : Submodule ℚ (Fin 4 → ℚ))
    (hP : Module.finrank ℚ P ≤ 3) (j : Fin 3)
    (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c₀ c₂ c₃ : Fin 4 → ℝ) (delta C4 : ℝ) : Prop :=
    (∀ i : Fin 4, i.val < j.val+1 →
      sourceMinima4 A₂ A₃ L hL Q hQ c₀ c₂ c₃ i <
        (tailProduct4 j (sourceMinima4 A₂ A₃ L hL Q hQ c₀ c₂ c₃))^
          (1/(4-((j.val+1 : ℕ) : ℝ))) * Q^(-delta)) ∧
    prefixProduct4 j (sourceMinima4 A₂ A₃ L hL Q hQ c₀ c₂ c₃) ≤
      C4^(((j.val+1 : ℕ) : ℝ)/4) * Q^(-decayExponent4 j delta) ∧
    (∏ i, restrictedMinima4 P A₂ A₃ L hL Q hQ c₀ c₂ c₃ i) =
      prefixProduct4 j (sourceMinima4 A₂ A₃ L hL Q hQ c₀ c₂ c₃) ∧
    (∏ i, restrictedMinima4 P A₂ A₃ L hL Q hQ c₀ c₂ c₃ i) ≤
      C4^(((j.val+1 : ℕ) : ℝ)/4) * Q^(-decayExponent4 j delta) ∧
    Module.finrank ℝ (rationalRealSpan4 P) = j.val+1 ∧
    Module.finrank ℤ (restrictedLattice4 P A₂ A₃ Q c₂ c₃) = j.val+1 ∧
    0 < (restrictedMeasure4 P).real (restrictedBody4 P L Q c₀) ∧
    (restrictedMeasure4 P) (restrictedBody4 P L Q c₀) < ⊤ ∧
    0 < ZLattice.covolume (restrictedLattice4 P A₂ A₃ Q c₂ c₃) (restrictedMeasure4 P) ∧
    (2 : ℝ)^(j.val+1) / (Nat.factorial (j.val+1) : ℝ) ≤
      (∏ i, restrictedMinima4 P A₂ A₃ L hL Q hQ c₀ c₂ c₃ i) *
        (restrictedMeasure4 P).real (restrictedBody4 P L Q c₀) /
          ZLattice.covolume (restrictedLattice4 P A₂ A₃ Q c₂ c₃) (restrictedMeasure4 P) ∧
    growthConstant4 j C4 * Q^(decayExponent4 j delta) ≤
      (restrictedMeasure4 P).real (restrictedBody4 P L Q c₀) /
        ZLattice.covolume (restrictedLattice4 P A₂ A₃ Q c₂ c₃) (restrictedMeasure4 P)

theorem power_growth_of_product_decay4 (j : Fin 3) (Q delta C4 p volume covol : ℝ)
    (hQ : 0 < Q) (hC4 : 0 < C4) (hv : 0 < volume) (hc : 0 < covol)
    (hdec : p ≤ C4^(((j.val+1 : ℕ) : ℝ)/4) * Q^(-decayExponent4 j delta))
    (hmink : (2 : ℝ)^(j.val+1) / (Nat.factorial (j.val+1) : ℝ) ≤ p*volume/covol) :
    growthConstant4 j C4 * Q^(decayExponent4 j delta) ≤ volume/covol := by
  have hpow : Q^(-decayExponent4 j delta) * Q^(decayExponent4 j delta) = 1 := by
    rw [← Real.rpow_add hQ]
    simp
  have hstep : (2 : ℝ)^(j.val+1) / (Nat.factorial (j.val+1) : ℝ) ≤
      (C4^(((j.val+1 : ℕ) : ℝ)/4) * Q^(-decayExponent4 j delta))*(volume/covol) := by
    calc
      _ ≤ p*(volume/covol) := by simpa [mul_div_assoc] using hmink
      _ ≤ _ := mul_le_mul_of_nonneg_right hdec (le_of_lt (div_pos hv hc))
  have h := mul_le_mul_of_nonneg_right hstep
    (le_of_lt (Real.rpow_pos_of_pos hQ (decayExponent4 j delta)))
  have hcancel :
      (C4^(((j.val+1 : ℕ) : ℝ)/4) * Q^(-decayExponent4 j delta)) *
        (volume/covol) * Q^(decayExponent4 j delta) =
      (volume/covol) * C4^(((j.val+1 : ℕ) : ℝ)/4) := by
    calc
      _ = (volume/covol) * C4^(((j.val+1 : ℕ) : ℝ)/4) *
          (Q^(-decayExponent4 j delta)*Q^(decayExponent4 j delta)) := by ring
      _ = _ := by rw [hpow, mul_one]
  rw [hcancel] at h
  unfold growthConstant4
  rw [div_mul_eq_mul_div]
  exact (div_le_iff₀ (Real.rpow_pos_of_pos hC4 _)).mpr h

theorem source_quantitative_original_point4 (P : Submodule ℚ (Fin 4 → ℚ))
    (hPlo : 1 ≤ Module.finrank ℚ P) (hP : Module.finrank ℚ P ≤ 3)
    (j : Fin 3) (hdim : Module.finrank ℚ P = j.val+1)
    (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c₀ c₂ c₃ : Fin 4 → ℝ) (delta C4 : ℝ) (hC4 : 0 < C4)
    (hg : sourceMinima4 A₂ A₃ L hL Q hQ c₀ c₂ c₃ j.castSucc <
      sourceMinima4 A₂ A₃ L hL Q hQ c₀ c₂ c₃ j.succ * Q^(-delta))
    (hprod : ∏ i, sourceMinima4 A₂ A₃ L hL Q hQ c₀ c₂ c₃ i ≤ C4)
    (hEq : ∀ i, restrictedMinima4 P A₂ A₃ L hL Q hQ c₀ c₂ c₃ i =
      sourceMinima4 A₂ A₃ L hL Q hQ c₀ c₂ c₃ (ambientPrefixIndex4 P hP i)) :
    quantitativeOriginalPoint4 P hP j A₂ A₃ L hL Q hQ c₀ c₂ c₃ delta C4 := by
  obtain ⟨hp,hm⟩ := sourceMinima4_pos_mono A₂ A₃ L hL Q hQ c₀ c₂ c₃
  have hQpos : 0 < Q := lt_trans zero_lt_one hQ
  have h718 := source_gap_geometric_mean4 j _ Q delta hQpos hp hm hg
  have h719 := source_prefix_product_decay4 j _ Q delta C4 hQpos hC4 hp hm hg hprod
  have heq : (∏ i, restrictedMinima4 P A₂ A₃ L hL Q hQ c₀ c₂ c₃ i) =
      prefixProduct4 j (sourceMinima4 A₂ A₃ L hL Q hQ c₀ c₂ c₃) := by
    calc
      _ = ∏ i, sourceMinima4 A₂ A₃ L hL Q hQ c₀ c₂ c₃ (ambientPrefixIndex4 P hP i) :=
        Finset.prod_congr rfl (fun i _ => hEq i)
      _ = _ := ambient_prefix_product_eq4 P hP j hdim _
  have hdec : (∏ i, restrictedMinima4 P A₂ A₃ L hL Q hQ c₀ c₂ c₃ i) ≤
      C4^(((j.val+1 : ℕ) : ℝ)/4) * Q^(-decayExponent4 j delta) := by
    rw [heq]
    exact h719
  obtain ⟨hReal,hInt,hVol,hFinite,hCov,vmin,hvmin,hvminL,hminPos,hminMono,
    hminAtt,hminShort,hMlower,hMupper⟩ :=
    source_restricted_minkowski4 P hPlo hP A₂ A₃ L hL Q hQ c₀ c₂ c₃
  have hM : (2 : ℝ)^(j.val+1) / (Nat.factorial (j.val+1) : ℝ) ≤
      (∏ i, restrictedMinima4 P A₂ A₃ L hL Q hQ c₀ c₂ c₃ i) *
        (restrictedMeasure4 P).real (restrictedBody4 P L Q c₀) /
          ZLattice.covolume (restrictedLattice4 P A₂ A₃ Q c₂ c₃) (restrictedMeasure4 P) := by
    calc
      _ = (2 : ℝ)^(Module.finrank ℚ P) / (Nat.factorial (Module.finrank ℚ P) : ℝ) := by rw [hdim]
      _ ≤ _ := hMlower
  exact ⟨h718,h719,heq,hdec,hReal.trans hdim,hInt.trans hdim,hVol,hFinite,hCov,hM,
    power_growth_of_product_decay4 j Q delta C4 _ _ _ hQpos hC4 hVol hCov hdec hM⟩

end
end CompoundFeasibility.RestrictedGrowth4
