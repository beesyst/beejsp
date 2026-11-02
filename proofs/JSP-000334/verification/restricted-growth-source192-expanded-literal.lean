import SubspaceBridge.NonrothAttainmentFlag4
import SubspaceBridge.RestrictedSource4

open scoped BigOperators
namespace CompoundFeasibility.M192LiteralMinimaPower4
noncomputable section

def prefixProduct4 (j : Fin 3) (lam : Fin 4 → ℝ) : ℝ :=
  ∏ i : Fin (j.val+1), lam ⟨i.val, by omega⟩

def tailProduct4 (j : Fin 3) (lam : Fin 4 → ℝ) : ℝ :=
  ∏ i : Fin (3-j.val), lam ⟨j.val+1+i.val, by omega⟩

def decayExponent4 (j : Fin 3) (delta : ℝ) : ℝ :=
  delta * (j.val+1) * (4-(j.val+1)) / 4

theorem selectedDimension4_cases (j : Fin 3) :
    j.val+1 = 1 ∨ j.val+1 = 2 ∨ j.val+1 = 3 := by
  omega

theorem decayExponent4_pos (j : Fin 3) (delta : ℝ) (hd : 0 < delta) :
    0 < decayExponent4 j delta := by
  unfold decayExponent4
  have hj : (j.val : ℝ) < 3 := by exact_mod_cast j.isLt
  have hx : 0 < 4 - ((j.val : ℝ)+1) := by linarith
  exact div_pos (mul_pos (mul_pos hd (by positivity)) hx) (by norm_num)

theorem log_gap_average4 (j : Fin 3) (a : Fin 4 → ℝ) (t : ℝ)
    (hm : Monotone a) (hg : a j.castSucc < a j.succ-t) :
    a j.castSucc < (∑ i : Fin (3-j.val), a ⟨j.val+1+i.val, by omega⟩) /
      (4-((j.val+1 : ℕ) : ℝ)) - t := by
  have h01 := hm (show (0 : Fin 4) ≤ 1 by decide)
  have h12 := hm (show (1 : Fin 4) ≤ 2 by decide)
  have h23 := hm (show (2 : Fin 4) ≤ 3 by decide)
  fin_cases j <;> norm_num at * <;> simp [Fin.sum_univ_succ, Fin.succ_mk] at * <;> norm_num at * <;> linarith

theorem log_prefix_decay4 (j : Fin 3) (a : Fin 4 → ℝ) (t z : ℝ)
    (hm : Monotone a) (hg : a j.castSucc < a j.succ-t)
    (hprod : ∑ i, a i ≤ z) :
    (∑ i : Fin (j.val+1), a ⟨i.val, by omega⟩) ≤
      ((j.val+1 : ℕ) : ℝ)/4*z - t*((j.val+1 : ℕ) : ℝ)*(4-((j.val+1 : ℕ) : ℝ))/4 := by
  have h01 := hm (show (0 : Fin 4) ≤ 1 by decide)
  have h12 := hm (show (1 : Fin 4) ≤ 2 by decide)
  have h23 := hm (show (2 : Fin 4) ≤ 3 by decide)
  fin_cases j <;> norm_num at * <;> simp [Fin.sum_univ_succ, Fin.succ_mk] at * <;> norm_num at * <;> linarith

theorem prefixProduct4_pos (j : Fin 3) (lam : Fin 4 → ℝ) (hp : ∀ i, 0 < lam i) :
    0 < prefixProduct4 j lam := by
  exact Finset.prod_pos (fun _ _ => hp _)

theorem tailProduct4_pos (j : Fin 3) (lam : Fin 4 → ℝ) (hp : ∀ i, 0 < lam i) :
    0 < tailProduct4 j lam := by
  exact Finset.prod_pos (fun _ _ => hp _)

theorem log_prefixProduct4 (j : Fin 3) (lam : Fin 4 → ℝ) (hp : ∀ i, 0 < lam i) :
    Real.log (prefixProduct4 j lam) =
      ∑ i : Fin (j.val+1), Real.log (lam ⟨i.val, by omega⟩) := by
  exact Real.log_prod _ _ (fun _ _ => ne_of_gt (hp _))

theorem log_tailProduct4 (j : Fin 3) (lam : Fin 4 → ℝ) (hp : ∀ i, 0 < lam i) :
    Real.log (tailProduct4 j lam) =
      ∑ i : Fin (3-j.val), Real.log (lam ⟨j.val+1+i.val, by omega⟩) := by
  exact Real.log_prod _ _ (fun _ _ => ne_of_gt (hp _))

theorem source_gap_geometric_mean4 (j : Fin 3) (lam : Fin 4 → ℝ)
    (Q delta : ℝ) (hQ : 0 < Q) (hp : ∀ i, 0 < lam i) (hm : Monotone lam)
    (hg : lam j.castSucc < lam j.succ * Q^(-delta)) :
    ∀ i : Fin 4, i.val < j.val+1 →
      lam i < (tailProduct4 j lam)^(1/(4-((j.val+1 : ℕ) : ℝ))) * Q^(-delta) := by
  have hlogmono : Monotone (fun i => Real.log (lam i)) :=
    fun i k hik => Real.log_le_log (hp i) (hm hik)
  have hgap := Real.log_lt_log (hp j.castSucc) hg
  rw [Real.log_mul (ne_of_gt (hp _)) (ne_of_gt (Real.rpow_pos_of_pos hQ _)),
    Real.log_rpow hQ] at hgap
  have havg := log_gap_average4 j (fun i => Real.log (lam i))
    (delta * Real.log Q) hlogmono (by linarith)
  intro i hi
  apply (Real.log_lt_log_iff (hp i)
    (mul_pos (Real.rpow_pos_of_pos (tailProduct4_pos j lam hp) _)
      (Real.rpow_pos_of_pos hQ _))).mp
  rw [Real.log_mul (ne_of_gt (Real.rpow_pos_of_pos (tailProduct4_pos j lam hp) _))
    (ne_of_gt (Real.rpow_pos_of_pos hQ _)),
    Real.log_rpow (tailProduct4_pos j lam hp), Real.log_rpow hQ,
    log_tailProduct4 j lam hp]
  have hle := hlogmono (show i ≤ j.castSucc from Fin.le_iff_val_le_val.mpr (by simpa using Nat.le_of_lt_succ hi))
  convert lt_of_le_of_lt hle havg using 1 <;> ring

theorem source_prefix_product_decay4 (j : Fin 3) (lam : Fin 4 → ℝ)
    (Q delta C4 : ℝ) (hQ : 0 < Q) (hC4 : 0 < C4)
    (hp : ∀ i, 0 < lam i) (hm : Monotone lam)
    (hg : lam j.castSucc < lam j.succ * Q^(-delta))
    (hprod : ∏ i, lam i ≤ C4) :
    prefixProduct4 j lam ≤ C4^(((j.val+1 : ℕ) : ℝ)/4) * Q^(-decayExponent4 j delta) := by
  have hlogmono : Monotone (fun i => Real.log (lam i)) :=
    fun i k hik => Real.log_le_log (hp i) (hm hik)
  have hgap := Real.log_lt_log (hp j.castSucc) hg
  rw [Real.log_mul (ne_of_gt (hp _)) (ne_of_gt (Real.rpow_pos_of_pos hQ _)),
    Real.log_rpow hQ] at hgap
  have hall := Real.log_le_log (Finset.prod_pos (fun i _ => hp i)) hprod
  rw [Real.log_prod _ _ (fun i _ => ne_of_gt (hp i))] at hall
  have hdec := log_prefix_decay4 j (fun i => Real.log (lam i)) (delta*Real.log Q)
    (Real.log C4) hlogmono (by linarith) hall
  apply (Real.log_le_log_iff (prefixProduct4_pos j lam hp)
    (mul_pos (Real.rpow_pos_of_pos hC4 _) (Real.rpow_pos_of_pos hQ _))).mp
  rw [log_prefixProduct4 j lam hp,
    Real.log_mul (ne_of_gt (Real.rpow_pos_of_pos hC4 _)) (ne_of_gt (Real.rpow_pos_of_pos hQ _)),
    Real.log_rpow hC4, Real.log_rpow hQ]
  convert hdec using 1 <;> push_cast <;> unfold decayExponent4 <;> ring

end
end CompoundFeasibility.M192LiteralMinimaPower4

open scoped BigOperators
namespace CompoundFeasibility.M192LiteralRestrictedGrowth4
open M192LiteralMinimaPower4 RestrictedGeometry4
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
end CompoundFeasibility.M192LiteralRestrictedGrowth4

open scoped BigOperators Classical Matrix
namespace CompoundFeasibility.M192LiteralNonrothVolumeGrowth4
open Exterior3 OriginalLastDual4 OriginalFlagAssembly4 BoundedWeights4 OriginalAttainmentFlag4 OriginalAttainmentTransport4 NonrothAttainmentFlag4 M192LiteralMinimaPower4 M192LiteralRestrictedGrowth4
noncomputable section

def selectedM192LiteralRestrictedGrowth4 (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : L.det = 1) (c₀ c₂ c₃ : Fin 4 → ℝ)
    (epsilon delta c4 C4 B : ℝ) (U V : Set ℝ) (j : Fin 3) (hQV : ∀ Q ∈ V, 1 < Q) : Prop :=
    ∃ (N : ℕ) (hN : 1 ≤ N),
      (∀ i, |c₀ i| ≤ (N : ℝ) ∧ (-(N : ℝ) ≤ c₂ i ∧ c₂ i ≤ 0) ∧ (-(N : ℝ) ≤ c₃ i ∧ c₃ i ≤ 0)) ∧
      (∀ i, |scaledWeights4 N c₀ i| ≤ 1) ∧
      (∀ i, -1 ≤ scaledWeights4 N c₂ i ∧ scaledWeights4 N c₂ i ≤ 0) ∧
      (∀ i, -1 ≤ scaledWeights4 N c₃ i ∧ scaledWeights4 N c₃ i ≤ 0) ∧
      (∑ i, (scaledWeights4 N c₀ i+scaledWeights4 N c₂ i+scaledWeights4 N c₃ i) = 0) ∧
      exactNormalization4 N hN A₂ A₃ L (sourceUnit42 L hL) c₀ c₂ c₃ ∧
      0 < delta/(N : ℝ) ∧
      (∀ Q ∈ V, Q^(-delta) = (Q^N)^(-(delta/(N : ℝ)))) ∧
      ¬ BddAbove (powerImage4 N V) ∧
      ∃ hWR : ∀ R ∈ powerImage4 N V, 1 < R,
        (∀ (R : ℝ) (hR : R ∈ powerImage4 N V),
          sourceMinima4 A₂ A₃ L (sourceUnit42 L hL) R (hWR R hR)
            (scaledWeights4 N c₀) (scaledWeights4 N c₂) (scaledWeights4 N c₃) j.castSucc <
          sourceMinima4 A₂ A₃ L (sourceUnit42 L hL) R (hWR R hR)
            (scaledWeights4 N c₀) (scaledWeights4 N c₂) (scaledWeights4 N c₃) j.succ*R^(-(delta/(N : ℝ)))) ∧
        ∃ (Wfixed : Set ℝ) (hWsub : Wfixed ⊆ powerImage4 N V), ¬ BddAbove Wfixed ∧
          ∃ P : Submodule ℚ (Fin 4 → ℚ), Module.finrank ℚ P = j.val+1 ∧
            ∃ hPbounds : 1 ≤ Module.finrank ℚ P ∧ Module.finrank ℚ P ≤ 3, P ≠ ⊤ ∧
            ∃ v : (r : Wfixed) → Fin 4 → originalSourceGroup4 A₂ A₃ r.val (scaledWeights4 N c₂) (scaledWeights4 N c₃),
              (∀ r : Wfixed, P = originalFirstFlag4 j.succ (fun i => (v r i : Fin 4 → ℤ))) ∧
              (∀ r : Wfixed, ambientFrame4 A₂ A₃ L (sourceUnit42 L hL) r.val (hWR r.val (hWsub r.property))
                (scaledWeights4 N c₀) (scaledWeights4 N c₂) (scaledWeights4 N c₃) (v r)) ∧
              originalPreimage4 N V Wfixed ⊆ V ∧ ¬ BddAbove (originalPreimage4 N V Wfixed) ∧
              ∃ u : (q : originalPreimage4 N V Wfixed) → Fin 4 → originalSourceGroup4 A₂ A₃ q.val c₂ c₃,
                (∀ q i, (u q i : Fin 4 → ℤ) = (v ⟨q.val^N,q.property.2⟩ i : Fin 4 → ℤ)) ∧
                (∀ q, P = originalFirstFlag4 j.succ (fun i => (u q i : Fin 4 → ℤ))) ∧
                (∀ q : originalPreimage4 N V Wfixed, ambientFrame4 A₂ A₃ L (sourceUnit42 L hL) q.val (hQV q.val q.property.1)
                  c₀ c₂ c₃ (u q)) ∧
                (∀ (q : originalPreimage4 N V Wfixed) (k : Fin (Module.finrank ℚ P)),
                  RestrictedGeometry4.restrictedMinima4 P A₂ A₃ L (sourceUnit42 L hL) q.val
                    (hQV q.val q.property.1) c₀ c₂ c₃ k =
                  sourceMinima4 A₂ A₃ L (sourceUnit42 L hL) q.val (hQV q.val q.property.1) c₀ c₂ c₃
                    (RestrictedGeometry4.ambientPrefixIndex4 P hPbounds.2 k)) ∧
                originalPreimage4 N V Wfixed ⊆ U ∧
                (∀ q : originalPreimage4 N V Wfixed,
                  1 < q.val ∧ B < q.val ∧
                  sourceMinima4 A₂ A₃ L (sourceUnit42 L hL) q.val (hQV q.val q.property.1) c₀ c₂ c₃ j.castSucc <
                    sourceMinima4 A₂ A₃ L (sourceUnit42 L hL) q.val (hQV q.val q.property.1) c₀ c₂ c₃ j.succ*q.val^(-delta) ∧
                  c4 ≤ (∏ i : Fin 4, sourceMinima4 A₂ A₃ L (sourceUnit42 L hL) q.val (hQV q.val q.property.1) c₀ c₂ c₃ i) ∧
                  (∏ i : Fin 4, sourceMinima4 A₂ A₃ L (sourceUnit42 L hL) q.val (hQV q.val q.property.1) c₀ c₂ c₃ i) ≤ C4) ∧
                (∀ Q ∈ originalPreimage4 N V Wfixed, ∃ hQ : 1 < Q, ∃ x : Fin 4 → ℤ,
                  OriginalVariableGap4.originalSourceSolution4 A₂ A₃ L c₀ c₂ c₃ Q epsilon x ∧
                  x ∈ originalSourceGroup4 A₂ A₃ Q c₂ c₃ ∧
                  coordinateGauge4 (originalCoordinates4 L (sourceUnit42 L hL) Q hQ c₀) (integerReal x) ≤ Q^(-epsilon) ∧
                  sourceMinima4 A₂ A₃ L (sourceUnit42 L hL) Q hQ c₀ c₂ c₃ 0 < Q^(-(epsilon/2))) ∧
                0 < decayExponent4 j delta ∧ 0 < growthConstant4 j C4 ∧
                ∀ q : originalPreimage4 N V Wfixed,
                  quantitativeOriginalPoint4 P hPbounds.2 j A₂ A₃ L (sourceUnit42 L hL)
                    q.val (hQV q.val q.property.1) c₀ c₂ c₃ delta C4

theorem source_restricted_volume_growth4 (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (h₂ : A₂.det = 1) (h₃ : A₃.det = 1) (hL : L.det = 1)
    (hAlg : ∀ i j, IsAlgebraic ℚ (L i j))
    (c₀ c₂ c₃ : Fin 4 → ℝ) (hc₂ : ∀ i, c₂ i ≤ 0) (hc₃ : ∀ i, c₃ i ≤ 0)
    (hb : ∑ i, (c₀ i+c₂ i+c₃ i) = 0)
    (hn : ¬ OriginalVariableGap4.originalRothProperty4 A₂ A₃ L c₀ c₂ c₃) :
    ∃ epsilon deltaGap c4 C4 B : ℝ, ∃ U V : Set ℝ, ∃ j : Fin 3,
      0 < epsilon ∧ deltaGap = (epsilon/2)/4 ∧ 0 < deltaGap ∧
      0 < c4 ∧ 0 < C4 ∧ 1 < B ∧
      U = {Q : ℝ | ∃ x : Fin 4 → ℤ,
        OriginalVariableGap4.originalSourceSolution4 A₂ A₃ L c₀ c₂ c₃ Q epsilon x} ∧
      ¬ BddAbove U ∧
      (∀ Q ∈ U, ∃ hQ : 1 < Q, ∃ x : Fin 4 → ℤ,
        OriginalVariableGap4.originalSourceSolution4 A₂ A₃ L c₀ c₂ c₃ Q epsilon x ∧
        x ∈ originalSourceGroup4 A₂ A₃ Q c₂ c₃ ∧
        coordinateGauge4 (originalCoordinates4 L (sourceUnit42 L hL) Q hQ c₀) (integerReal x) ≤ Q^(-epsilon) ∧
        sourceMinima4 A₂ A₃ L (sourceUnit42 L hL) Q hQ c₀ c₂ c₃ 0 < Q^(-(epsilon/2))) ∧
      (∀ (Q : ℝ) (hQ : 1 < Q),
        c4 ≤ (∏ i : Fin 4, sourceMinima4 A₂ A₃ L (sourceUnit42 L hL) Q hQ c₀ c₂ c₃ i) ∧
        (∏ i : Fin 4, sourceMinima4 A₂ A₃ L (sourceUnit42 L hL) Q hQ c₀ c₂ c₃ i) ≤ C4) ∧
      V ⊆ U ∧ ¬ BddAbove V ∧
      ∃ hQV : ∀ Q ∈ V, 1 < Q,
        (∀ (Q : ℝ) (hq : Q ∈ V), B < Q ∧
          sourceMinima4 A₂ A₃ L (sourceUnit42 L hL) Q (hQV Q hq) c₀ c₂ c₃ j.castSucc <
          sourceMinima4 A₂ A₃ L (sourceUnit42 L hL) Q (hQV Q hq) c₀ c₂ c₃ j.succ*Q^(-deltaGap)) ∧
        selectedM192LiteralRestrictedGrowth4 A₂ A₃ L hL c₀ c₂ c₃ epsilon deltaGap c4 C4 B U V j hQV := by
  obtain ⟨epsilon,deltaGap,c4,C4,B,U,V,j,he,hdelta,hd,hc4,hC4,hB,hUeq,hU,hsol,hprod,hVU,hV,hQV,hpoints,hselected⟩ :=
    source_nonroth_attaining_fixed_flag4 A₂ A₃ L h₂ h₃ hL hAlg c₀ c₂ c₃ hc₂ hc₃ hb hn
  obtain ⟨N,hN,hc,ha₀,ha₂,ha₃,hab,hcert,hdn,hpower,himage,hWR,hgapn,
    Wfixed,hWsub,hW,P,hPdim,hPbounds,hproper,v,hv,hvAtt,hFinalV,hFinal,
    u,hvalues,hflag,hAtt,hEq,hFinalU,hFinalpoints,hFinalsol⟩ := hselected
  refine ⟨epsilon,deltaGap,c4,C4,B,U,V,j,he,hdelta,hd,hc4,hC4,hB,hUeq,hU,hsol,hprod,hVU,hV,hQV,hpoints,?_⟩
  refine ⟨N,hN,hc,ha₀,ha₂,ha₃,hab,hcert,hdn,hpower,himage,hWR,hgapn,?_⟩
  refine ⟨Wfixed,hWsub,hW,P,hPdim,hPbounds,hproper,v,hv,hvAtt,hFinalV,hFinal,?_⟩
  refine ⟨u,hvalues,hflag,hAtt,hEq,hFinalU,hFinalpoints,hFinalsol,
    decayExponent4_pos j deltaGap hd,growthConstant4_pos j C4 hC4,?_⟩
  intro q
  exact source_quantitative_original_point4 P hPbounds.1 hPbounds.2 j hPdim
    A₂ A₃ L (sourceUnit42 L hL) q.val (hQV q.val q.property.1) c₀ c₂ c₃ deltaGap C4 hC4
    (hFinalpoints q).2.2.1 (hFinalpoints q).2.2.2.2 (hEq q)

end
end CompoundFeasibility.M192LiteralNonrothVolumeGrowth4

#check CompoundFeasibility.M192LiteralMinimaPower4.prefixProduct4
#print axioms CompoundFeasibility.M192LiteralMinimaPower4.prefixProduct4

#check CompoundFeasibility.M192LiteralMinimaPower4.tailProduct4
#print axioms CompoundFeasibility.M192LiteralMinimaPower4.tailProduct4

#check CompoundFeasibility.M192LiteralMinimaPower4.decayExponent4
#print axioms CompoundFeasibility.M192LiteralMinimaPower4.decayExponent4

#check CompoundFeasibility.M192LiteralMinimaPower4.selectedDimension4_cases
#print axioms CompoundFeasibility.M192LiteralMinimaPower4.selectedDimension4_cases

#check CompoundFeasibility.M192LiteralMinimaPower4.decayExponent4_pos
#print axioms CompoundFeasibility.M192LiteralMinimaPower4.decayExponent4_pos

#check CompoundFeasibility.M192LiteralMinimaPower4.log_gap_average4
#print axioms CompoundFeasibility.M192LiteralMinimaPower4.log_gap_average4

#check CompoundFeasibility.M192LiteralMinimaPower4.log_prefix_decay4
#print axioms CompoundFeasibility.M192LiteralMinimaPower4.log_prefix_decay4

#check CompoundFeasibility.M192LiteralMinimaPower4.prefixProduct4_pos
#print axioms CompoundFeasibility.M192LiteralMinimaPower4.prefixProduct4_pos

#check CompoundFeasibility.M192LiteralMinimaPower4.tailProduct4_pos
#print axioms CompoundFeasibility.M192LiteralMinimaPower4.tailProduct4_pos

#check CompoundFeasibility.M192LiteralMinimaPower4.log_prefixProduct4
#print axioms CompoundFeasibility.M192LiteralMinimaPower4.log_prefixProduct4

#check CompoundFeasibility.M192LiteralMinimaPower4.log_tailProduct4
#print axioms CompoundFeasibility.M192LiteralMinimaPower4.log_tailProduct4

#check CompoundFeasibility.M192LiteralMinimaPower4.source_gap_geometric_mean4
#print axioms CompoundFeasibility.M192LiteralMinimaPower4.source_gap_geometric_mean4

#check CompoundFeasibility.M192LiteralMinimaPower4.source_prefix_product_decay4
#print axioms CompoundFeasibility.M192LiteralMinimaPower4.source_prefix_product_decay4

#check CompoundFeasibility.M192LiteralRestrictedGrowth4.growthConstant4
#print axioms CompoundFeasibility.M192LiteralRestrictedGrowth4.growthConstant4

#check CompoundFeasibility.M192LiteralRestrictedGrowth4.growthConstant4_pos
#print axioms CompoundFeasibility.M192LiteralRestrictedGrowth4.growthConstant4_pos

#check CompoundFeasibility.M192LiteralRestrictedGrowth4.ambient_prefix_product_eq4
#print axioms CompoundFeasibility.M192LiteralRestrictedGrowth4.ambient_prefix_product_eq4

#check CompoundFeasibility.M192LiteralRestrictedGrowth4.quantitativeOriginalPoint4
#print axioms CompoundFeasibility.M192LiteralRestrictedGrowth4.quantitativeOriginalPoint4

#check CompoundFeasibility.M192LiteralRestrictedGrowth4.power_growth_of_product_decay4
#print axioms CompoundFeasibility.M192LiteralRestrictedGrowth4.power_growth_of_product_decay4

#check CompoundFeasibility.M192LiteralRestrictedGrowth4.source_quantitative_original_point4
#print axioms CompoundFeasibility.M192LiteralRestrictedGrowth4.source_quantitative_original_point4

#check CompoundFeasibility.M192LiteralNonrothVolumeGrowth4.selectedM192LiteralRestrictedGrowth4
#print axioms CompoundFeasibility.M192LiteralNonrothVolumeGrowth4.selectedM192LiteralRestrictedGrowth4

#check CompoundFeasibility.M192LiteralNonrothVolumeGrowth4.source_restricted_volume_growth4
#print axioms CompoundFeasibility.M192LiteralNonrothVolumeGrowth4.source_restricted_volume_growth4
