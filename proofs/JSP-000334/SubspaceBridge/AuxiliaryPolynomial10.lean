import SubspaceBridge.AuxiliaryCount10
import SubspaceBridge.SchmidtPolynomial10
import SubspaceBridge.AuxiliaryFeasibility6

open scoped BigOperators Matrix Classical
noncomputable section
namespace CompoundFeasibility.Auxiliary10
open SourceMultiblock10 SourceNormalHighIndex10 SchmidtPolynomial10

def exponent10 {m : ℕ} {r : Fin m → ℕ} (b : RothAuxCoefficients r) : Vars10 m →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun u => ((b u.1).val u.2).val)

theorem exponent10_injective {m : ℕ} (r : Fin m → ℕ) : Function.Injective (@exponent10 m r) := by
  intro b c h
  funext g
  apply Subtype.ext
  funext j
  apply Fin.ext
  exact congrArg (fun e : Vars10 m →₀ ℕ => e (g,j)) h

def polynomial10 {m : ℕ} {r : Fin m → ℕ} {R : Type*} [CommRing R] (c : RothAuxCoefficients r → R) : MvPolynomial (Vars10 m) R :=
  ∑ b, MvPolynomial.monomial (exponent10 b) (c b)

theorem polynomial10_coeff {m : ℕ} {r : Fin m → ℕ} {R : Type*} [CommRing R] (c : RothAuxCoefficients r → R) (b : RothAuxCoefficients r) :
    (polynomial10 c).coeff (exponent10 b) = c b := by
  simp only [polynomial10,MvPolynomial.coeff_sum,MvPolynomial.coeff_monomial,(exponent10_injective r).eq_iff]
  simp

theorem polynomial10_homogeneous {m : ℕ} {r : Fin m → ℕ} {R : Type*} [CommRing R] (c : RothAuxCoefficients r → R) : homogeneous10 r (polynomial10 c) := by
  intro d hd h
  obtain ⟨b,_,hb⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hd)
  have hab := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hb)
  subst d
  exact (b h).property


variable {R : Type*} [CommRing R]

def chart10 {m : ℕ} (a : Fin 10 → R) (k : Fin 10) (u : Vars10 m) : MvPolynomial (Vars10 m) R :=
  if u.2 = k then -(∑ j ∈ Finset.univ.erase k, MvPolynomial.C (a j) * MvPolynomial.X (u.1,j))
  else MvPolynomial.C (a k) * MvPolynomial.X u

def substitute10 {m : ℕ} (a : Fin 10 → R) (k : Fin 10) : MvPolynomial (Vars10 m) R →+* MvPolynomial (Vars10 m) R :=
  MvPolynomial.eval₂Hom MvPolynomial.C (chart10 a k)

def pivotDerivative10 {m : ℕ} (k : Fin 10) (i : Fin m → ℕ) : Vars10 m →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun u => if u.2 = k then i u.1 else 0)

theorem transformed_monomial10 {m : ℕ} (a : Fin 10 → R) (k : Fin 10) (J b : Vars10 m →₀ ℕ) :
    substitute10 a k (derivative10 J (MvPolynomial.monomial b 1)) =
      MvPolynomial.C (∏ u : Vars10 m, (Nat.choose (b u) (J u) : R)) *
        ∏ u : Vars10 m, chart10 a k u ^ (b-J) u := by
  rw [derivative10_monomial]
  change MvPolynomial.eval₂ MvPolynomial.C (chart10 a k) (MvPolynomial.monomial (b-J)
    (1 * ∏ u : Vars10 m, (Nat.choose (b u) (J u) : R))) = _
  rw [MvPolynomial.eval₂_monomial,one_mul]
  congr 1
  exact Finsupp.prod_fintype _ _ (fun _ => pow_zero _)

theorem exponent10_sum {m : ℕ} {r : Fin m → ℕ} (b : RothAuxCoefficients r) :
    (∑ u : Vars10 m, exponent10 b u) = ∑ h, r h := by
  rw [Fintype.sum_prod_type]
  exact Finset.sum_congr rfl (fun h _ => (b h).property)


theorem transformed_coeff_sum10 {m : ℕ} {ι : Type*} [Fintype ι]
    (e : ι → Vars10 m →₀ ℕ) (c : ι → R)
    (J d : Vars10 m →₀ ℕ)
    (a : Fin 10 → R) (k : Fin 10) :
    let S := substitute10 (m := m) a k;
    (S (derivative10 J (∑ b, MvPolynomial.monomial (e b) (c b)))).coeff d =
      ∑ b, c b * (S (derivative10 J
        (MvPolynomial.monomial (e b) 1))).coeff d := by
  dsimp only
  let S := substitute10 (m := m) a k
  have hadd : derivative10 J
      (∑ b, MvPolynomial.monomial (e b) (c b)) =
      ∑ b, derivative10 J (MvPolynomial.monomial (e b) (c b)) := by
    apply MvPolynomial.ext
    intro a
    simp only [derivative10_coeff, MvPolynomial.coeff_sum,
      Finset.sum_mul]
  rw [hadd, map_sum, MvPolynomial.coeff_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [derivative10_monomial, derivative10_monomial]
  simp only [one_mul]
  have hc : MvPolynomial.monomial (e b - J)
      (c b * ∏ u : Vars10 m, (Nat.choose (e b u) (J u) : R)) =
      MvPolynomial.C (c b) * MvPolynomial.monomial (e b - J)
        (∏ u : Vars10 m, (Nat.choose (e b u) (J u) : R)) := by
    rw [MvPolynomial.C_mul_monomial]
  rw [hc, map_mul]
  have hC : S (MvPolynomial.C (c b)) = MvPolynomial.C (c b) := by
    simp [S,substitute10]
  rw [hC, MvPolynomial.coeff_C_mul]


theorem rothAux_weight_pivot {m : ℕ} (d : Vars10 m →₀ ℕ) (k : Fin 10) :
    Finsupp.weight (fun u : Vars10 m => if u.2 = k then 1 else 0) d =
      ∑ h : Fin m, d (h,k) := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  simp [Fintype.sum_prod_type, nsmul_eq_mul]

theorem weighted_neg_ring10 {m : ℕ} (w : Vars10 m → ℕ)
    (P : MvPolynomial (Vars10 m) R) (n : ℕ)
    (hP : MvPolynomial.IsWeightedHomogeneous w P n) :
    MvPolynomial.IsWeightedHomogeneous w (-P) n := by
  intro d hd
  apply hP
  simpa using hd

theorem chart10_block_weight {m : ℕ} (a : Fin 10 → R) (k : Fin 10)
    (h : Fin m) (u : Vars10 m) :
    MvPolynomial.IsWeightedHomogeneous (fun v : Vars10 m => if v.1 = h then 1 else 0)
      (chart10 a k u) (if u.1 = h then 1 else 0) := by
  let w := fun v : Vars10 m => if v.1 = h then 1 else 0
  have hx (j : Fin 10) : MvPolynomial.IsWeightedHomogeneous w
      (MvPolynomial.C (a j) * MvPolynomial.X (u.1,j)) (if u.1 = h then 1 else 0) := by
    simpa only [zero_add] using
      (MvPolynomial.isWeightedHomogeneous_C w (a j)).mul (MvPolynomial.isWeightedHomogeneous_X R w (u.1,j))
  unfold chart10
  by_cases hu : u.2 = k
  · rw [if_pos hu]
    exact weighted_neg_ring10 w _ _
      (MvPolynomial.IsWeightedHomogeneous.sum _ _ _ (fun j _ => hx j))
  · rw [if_neg hu]
    simpa only [zero_add] using
      (MvPolynomial.isWeightedHomogeneous_C w (a k)).mul (MvPolynomial.isWeightedHomogeneous_X R w u)

theorem chart10_pivot_weight {m : ℕ} (a : Fin 10 → R) (k : Fin 10)
    (u : Vars10 m) :
    MvPolynomial.IsWeightedHomogeneous (fun v : Vars10 m => if v.2 = k then 1 else 0)
      (chart10 a k u) 0 := by
  let w := fun v : Vars10 m => if v.2 = k then 1 else 0
  have hx (j : Fin 10) (hj : j ≠ k) : MvPolynomial.IsWeightedHomogeneous w
      (MvPolynomial.C (a j) * MvPolynomial.X (u.1,j)) 0 := by
    simpa only [w, hj, if_false, zero_add] using
      (MvPolynomial.isWeightedHomogeneous_C w (a j)).mul (MvPolynomial.isWeightedHomogeneous_X R w (u.1,j))
  unfold chart10
  split_ifs with hu
  · exact weighted_neg_ring10 w _ 0
      (MvPolynomial.IsWeightedHomogeneous.sum _ _ 0 (fun j hj => hx j (Finset.mem_erase.mp hj).1))
  · simpa only [w, hu, if_false, zero_add] using
      (MvPolynomial.isWeightedHomogeneous_C w (a k)).mul (MvPolynomial.isWeightedHomogeneous_X R w u)

theorem rothAux_scaled_monomial_weighted {m : ℕ} (a : Fin 10 → R) (k : Fin 10)
    (J b : Vars10 m →₀ ℕ) (w : Vars10 m → ℕ) (v : Vars10 m → ℕ)
    (hv : ∀ u, MvPolynomial.IsWeightedHomogeneous w (chart10 a k u) (v u)) :
    MvPolynomial.IsWeightedHomogeneous w
      (substitute10 a k
        (derivative10 J (MvPolynomial.monomial b 1)))
      (∑ u : Vars10 m, (b - J) u * v u) := by
  rw [transformed_monomial10]
  have hp := MvPolynomial.IsWeightedHomogeneous.prod Finset.univ
    (fun u : Vars10 m => chart10 a k u ^ (b - J) u)
    (fun u => (b - J) u * v u) (fun u _ => by simpa only [nsmul_eq_mul] using (hv u).pow ((b - J) u))
  simpa only [zero_add] using (MvPolynomial.isWeightedHomogeneous_C w _).mul hp



theorem rothAux_transformed_polynomial {m : ℕ} {r : Fin m → ℕ}
    (a : Fin 10 → R) (k : Fin 10) (J : Vars10 m →₀ ℕ)
    (c : RothAuxCoefficients r → R) :
    substitute10 a k (derivative10 J (polynomial10 c)) =
      ∑ b, MvPolynomial.C (c b) * substitute10 a k
        (derivative10 J (MvPolynomial.monomial (exponent10 b) 1)) := by
  apply MvPolynomial.ext
  intro d
  rw [polynomial10, transformed_coeff_sum10]
  simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul]

theorem rothAux_pivot_monomial_block_weight {m : ℕ} {r : Fin m → ℕ}
    (a : Fin 10 → R) (k : Fin 10) (i : Fin m → ℕ) (b : RothAuxCoefficients r) (h : Fin m) :
    MvPolynomial.IsWeightedHomogeneous (fun u : Vars10 m => if u.1 = h then 1 else 0)
      (substitute10 a k (derivative10
        (pivotDerivative10 k i) (MvPolynomial.monomial (exponent10 b) 1)))
      (r h - i h) := by
  let J := pivotDerivative10 k i
  let w := fun u : Vars10 m => if u.1 = h then 1 else 0
  by_cases hle : J ≤ exponent10 b
  · have hw := rothAux_scaled_monomial_weighted a k J (exponent10 b) w w
      (chart10_block_weight a k h)
    have heq : (∑ u : Vars10 m, (exponent10 b - J) u * w u) =
        ∑ j : Fin 10, (exponent10 b - J) (h,j) := by
      have he := rothAux_weight_block (exponent10 b - J) h
      rw [Finsupp.weight_apply] at he
      rw [Finsupp.sum_fintype (exponent10 b - J)
        (fun u (n : ℕ) => n • w u) (by intro u; simp)] at he
      simpa only [nsmul_eq_mul, Nat.cast_id, w] using he
    have hdeg : (∑ j : Fin 10, (exponent10 b - J) (h,j)) = r h - i h := by
      change (∑ j : Fin 10, (exponent10 b (h,j) - J (h,j))) = _
      rw [Finset.sum_tsub_distrib _ (fun j _ => hle (h,j))]
      have hb : (∑ j : Fin 10, exponent10 b (h,j)) = r h := (b h).property
      rw [hb]
      congr 1
      simp [J, pivotDerivative10]
    rw [heq, hdeg] at hw
    exact hw
  · change ¬ ∀ u, J u ≤ exponent10 b u at hle
    push_neg at hle
    obtain ⟨u, hu⟩ := hle
    have hz : (∏ v : Vars10 m, (Nat.choose (exponent10 b v) (J v) : R)) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ u)
      simp [Nat.choose_eq_zero_of_lt hu]
    rw [transformed_monomial10, hz, map_zero, zero_mul]
    exact MvPolynomial.isWeightedHomogeneous_zero R w _

theorem rothAux_transformed_block_weight {m : ℕ} {r : Fin m → ℕ}
    (a : Fin 10 → R) (k : Fin 10) (i : Fin m → ℕ)
    (c : RothAuxCoefficients r → R) (h : Fin m) :
    MvPolynomial.IsWeightedHomogeneous (fun u : Vars10 m => if u.1 = h then 1 else 0)
      (substitute10 a k (derivative10
        (pivotDerivative10 k i) (polynomial10 c))) (r h - i h) := by
  rw [rothAux_transformed_polynomial]
  apply MvPolynomial.IsWeightedHomogeneous.sum
  intro b _
  simpa only [zero_add] using (MvPolynomial.isWeightedHomogeneous_C _ (c b)).mul
    (rothAux_pivot_monomial_block_weight a k i b h)

theorem rothAux_transformed_block_homogeneous {m : ℕ} {r : Fin m → ℕ}
    (a : Fin 10 → R) (k : Fin 10) (i : Fin m → ℕ)
    (c : RothAuxCoefficients r → R) :
    homogeneous10 (fun h => r h - i h)
      (substitute10 a k (derivative10
        (pivotDerivative10 k i) (polynomial10 c))) := by
  intro d hd h
  rw [← rothAux_weight_block]
  exact rothAux_transformed_block_weight a k i c h (MvPolynomial.mem_support_iff.mp hd)

theorem rothAux_transformed_pivot_weight {m : ℕ} {r : Fin m → ℕ}
    (a : Fin 10 → R) (k : Fin 10) (J : Vars10 m →₀ ℕ)
    (c : RothAuxCoefficients r → R) :
    MvPolynomial.IsWeightedHomogeneous (fun u : Vars10 m => if u.2 = k then 1 else 0)
      (substitute10 a k (derivative10 J (polynomial10 c))) 0 := by
  rw [rothAux_transformed_polynomial]
  apply MvPolynomial.IsWeightedHomogeneous.sum
  intro b _
  have hb := rothAux_scaled_monomial_weighted a k J (exponent10 b)
    (fun u : Vars10 m => if u.2 = k then 1 else 0) (fun _ => 0)
    (chart10_pivot_weight a k)
  simp only [mul_zero, Finset.sum_const_zero] at hb
  simpa only [zero_add] using (MvPolynomial.isWeightedHomogeneous_C _ (c b)).mul hb

theorem rothAux_transformed_pivot_zero {m : ℕ} {r : Fin m → ℕ}
    (a : Fin 10 → R) (k : Fin 10) (J : Vars10 m →₀ ℕ)
    (c : RothAuxCoefficients r → R) (d : Vars10 m →₀ ℕ)
    (hd : (substitute10 a k
      (derivative10 J (polynomial10 c))).coeff d ≠ 0) (h : Fin m) :
    d (h,k) = 0 := by
  have hw := rothAux_transformed_pivot_weight a k J c hd
  rw [rothAux_weight_pivot] at hw
  have hle : d (h,k) ≤ ∑ g : Fin m, d (g,k) :=
    Finset.single_le_sum (fun g _ => Nat.zero_le (d (g,k))) (Finset.mem_univ h)
  omega



def freeExponent10 {m : ℕ} (s : Fin m → ℕ) (k : Fin 10)
    (j : (h : Fin m) → Block9 (s h)) : Vars10 m →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun u => Fin.insertNth (α := fun _ : Fin 10 => ℕ) k 0 (fun t : Fin 9 => ((j u.1).val t).val) u.2)

theorem freeExponent10_reconstruct {m : ℕ} (s : Fin m → ℕ) (k : Fin 10)
    (d : Vars10 m →₀ ℕ) (hs : ∀ h, ∑ t : Fin 10, d (h,t) = s h)
    (hz : ∀ h, d (h,k) = 0) :
    ∃ j : (h : Fin m) → Block9 (s h), freeExponent10 s k j = d := by
  have hsum (h : Fin m) : (∑ t : Fin 9, d (h,k.succAbove t)) = s h := by
    have he := Fin.sum_univ_succAbove (fun t => d (h,t)) k
    rw [hs h,hz h,zero_add] at he
    exact he.symm
  let j : (h : Fin m) → Block9 (s h) := fun h => ⟨fun t => ⟨d (h,k.succAbove t),by
    have hh : d (h,k.succAbove t) ≤ ∑ u : Fin 10, d (h,u) :=
      Finset.single_le_sum (s := Finset.univ) (f := fun u : Fin 10 => d (h,u)) (fun u _ => Nat.zero_le _) (Finset.mem_univ _)
    rw [hs h] at hh
    omega⟩,hsum h⟩
  refine ⟨j,?_⟩
  ext u
  rcases u with ⟨h,t⟩
  change Fin.insertNth (α := fun _ : Fin 10 => ℕ) k 0 (fun v : Fin 9 => ((j h).val v).val) t = d (h,t)
  refine Fin.succAboveCases k ?_ (fun v => ?_) t
  · simpa only [Fin.insertNth_apply_same] using (hz h).symm
  · rw [Fin.insertNth_apply_succAbove]



end CompoundFeasibility.Auxiliary10
namespace Aux10Height
open CompoundFeasibility.SourceMultiblock10 CompoundFeasibility.SourceNormalHighIndex10 CompoundFeasibility.SchmidtPolynomial10
open CompoundFeasibility.Auxiliary10 Aux6Mass
variable {R : Type*} [NormedCommRing R] [NormOneClass R]

theorem chart_mass10 {m : ℕ} (a : Fin 10 → R) (k : Fin 10)
    (A : ℝ) (hA : 1 ≤ A) (ha : ∀ j, ‖a j‖ ≤ A) (u : Vars10 m) :
    mass (chart10 a k u) ≤ 10 * A := by
  unfold chart10
  split_ifs
  · rw [mass_neg]
    calc
      _ ≤ ∑ j ∈ Finset.univ.erase k, mass (MvPolynomial.C (a j) * MvPolynomial.X (u.1,j)) := mass_sum _ _
      _ ≤ ∑ _j ∈ Finset.univ.erase k, A := by
        apply Finset.sum_le_sum
        intro j _
        rw [mass_C_mul_X]
        exact ha j
      _ ≤ 10 * A := by simp; linarith
  · rw [mass_C_mul_X]
    exact (ha k).trans (by linarith)

theorem binomial_norm10 {m : ℕ} {r : Fin m → ℕ} (b : RothAuxCoefficients r) (J : Vars10 m →₀ ℕ) :
    ‖∏ u : Vars10 m, (Nat.choose (exponent10 b u) (J u) : R)‖ ≤ (2 : ℝ)^(∑ h, r h) := by
  have hnat (n : ℕ) : ‖(n : R)‖ ≤ (n : ℝ) := by
    rw [← nsmul_one]
    exact (norm_nsmul_le (n := n) (a := (1 : R))).trans_eq (by simp)
  calc
    _ ≤ ∏ u : Vars10 m, ‖(Nat.choose (exponent10 b u) (J u) : R)‖ := Finset.norm_prod_le _ _
    _ ≤ ∏ u : Vars10 m, (2 : ℝ)^exponent10 b u := by
      apply Finset.prod_le_prod
      · intro u _; exact norm_nonneg _
      · intro u _
        apply (hnat _).trans
        have hc : (exponent10 b u).choose (J u) ≤ 2 ^ exponent10 b u := by
          rcases Nat.eq_zero_or_pos (exponent10 b u) with hz | hp
          · rw [hz]; cases J u <;> simp
          · exact (Nat.choose_le_two_pow _ _ hp).le
        exact_mod_cast hc
    _ = _ := by rw [Finset.prod_pow_eq_pow_sum,exponent10_sum]

theorem transformed_entry_norm10 {m : ℕ} {r : Fin m → ℕ}
    (a : Fin 10 → R) (k : Fin 10) (A : ℝ) (hA : 1 ≤ A) (ha : ∀ j, ‖a j‖ ≤ A)
    (b : RothAuxCoefficients r) (J d : Vars10 m →₀ ℕ) :
    ‖(substitute10 a k (derivative10 J (MvPolynomial.monomial (exponent10 b) 1))).coeff d‖ ≤
      (20 * A)^(∑ h, r h) := by
  have hbase : 1 ≤ 10 * A := by linarith
  have hsum : (∑ u : Vars10 m, (exponent10 b-J) u) ≤ ∑ h, r h := by
    rw [← exponent10_sum b]
    exact Finset.sum_le_sum (fun u _ => Nat.sub_le _ _)
  rw [transformed_monomial10]
  calc
    _ ≤ mass (MvPolynomial.C (∏ u : Vars10 m, (Nat.choose (exponent10 b u) (J u) : R)) *
        ∏ u : Vars10 m, chart10 a k u ^ (exponent10 b-J) u) := coeff_le_mass _ _
    _ ≤ mass (MvPolynomial.C (∏ u : Vars10 m, (Nat.choose (exponent10 b u) (J u) : R))) *
        mass (∏ u : Vars10 m, chart10 a k u ^ (exponent10 b-J) u) := mass_mul _ _
    _ ≤ (2 : ℝ)^(∑ h, r h) * (10*A)^(∑ h, r h) := by
      apply mul_le_mul
      · simpa only [MvPolynomial.C_apply,mass_monomial] using binomial_norm10 (R := R) b J
      · calc
          _ ≤ ∏ u : Vars10 m, mass (chart10 a k u ^ (exponent10 b-J) u) := mass_prod _ _
          _ ≤ ∏ u : Vars10 m, (10*A)^(exponent10 b-J) u := by
            apply Finset.prod_le_prod
            · intro u _; exact mass_nonneg _
            · intro u _
              exact (mass_pow _ _).trans (pow_le_pow_left₀ (mass_nonneg _) (chart_mass10 a k A hA ha u) _)
          _ = (10*A)^(∑ u : Vars10 m, (exponent10 b-J) u) := Finset.prod_pow_eq_pow_sum _ _ _
          _ ≤ _ := pow_le_pow_right₀ hbase hsum
      · exact mass_nonneg _
      · positivity
    _ = _ := by rw [← mul_pow]; congr 1; ring

end Aux10Height

namespace CompoundFeasibility.Auxiliary10
open SourceMultiblock10 SourceNormalHighIndex10 SchmidtPolynomial10
variable {K : Type*} [CommRing K]

noncomputable def formEquiv10 : Fin 30 ≃ Fin 3 × Fin 10 :=
  (finProdFinEquiv : Fin 3 × Fin 10 ≃ Fin (3 * 10)).symm

noncomputable def equation10 {m : ℕ} {r : Fin m → ℕ} {eta : ℝ}
    (a : Fin 3 → Fin 10 → Fin 10 → K) (p : Fin 3 → Fin 10 → Fin 10)
    (f : Fin 30) (i : {i : RothAuxPivots r // rothAuxPivotCondition r eta i})
    (j : (h : Fin m) → Block9 (r h - (i.val h).val))
    (P : MvPolynomial (Vars10 m) K) : K :=
  (substitute10 (a (formEquiv10 f).1 (formEquiv10 f).2)
    (p (formEquiv10 f).1 (formEquiv10 f).2)
    (derivative10 (pivotDerivative10 (p (formEquiv10 f).1 (formEquiv10 f).2)
      (fun h => (i.val h).val)) P)).coeff
    (freeExponent10 (fun h => r h - (i.val h).val)
      (p (formEquiv10 f).1 (formEquiv10 f).2) j)

noncomputable def matrix10 {m : ℕ} (r : Fin m → ℕ) (eta : ℝ)
    (a : Fin 3 → Fin 10 → Fin 10 → K) (p : Fin 3 → Fin 10 → Fin 10) :
    Matrix (Equations10 r eta) (RothAuxCoefficients r) K :=
  fun q b => equation10 a p q.1 (badPivotEquiv4 r eta q.2).1
    (badPivotEquiv4 r eta q.2).2 (MvPolynomial.monomial (exponent10 b) 1)

theorem matrix10_mulVec {m : ℕ} (r : Fin m → ℕ) (eta : ℝ)
    (a : Fin 3 → Fin 10 → Fin 10 → K) (p : Fin 3 → Fin 10 → Fin 10)
    (c : RothAuxCoefficients r → K) (q : Equations10 r eta) :
    (matrix10 r eta a p).mulVec c q =
      equation10 a p q.1 (badPivotEquiv4 r eta q.2).1
        (badPivotEquiv4 r eta q.2).2 (polynomial10 c) := by
  unfold equation10 polynomial10
  rw [transformed_coeff_sum10]
  simp only [Matrix.mulVec, dotProduct, matrix10, equation10]
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem matrix10_kernel_iff_coefficients {m : ℕ} (r : Fin m → ℕ) (eta : ℝ)
    (a : Fin 3 → Fin 10 → Fin 10 → K) (p : Fin 3 → Fin 10 → Fin 10)
    (c : RothAuxCoefficients r → K) :
    (matrix10 r eta a p).mulVec c = 0 ↔
      ∀ (f : Fin 30) (i : {i : RothAuxPivots r // rothAuxPivotCondition r eta i})
        (j : (h : Fin m) → Block9 (r h - (i.val h).val)),
        equation10 a p f i j (polynomial10 c) = 0 := by
  constructor
  · intro hz f i j
    have h := congrFun hz (f, (badPivotEquiv4 r eta).symm ⟨i,j⟩)
    rw [matrix10_mulVec] at h
    simpa only [Equiv.apply_symm_apply, Pi.zero_apply] using h
  · intro hz
    funext q
    rw [matrix10_mulVec]
    exact hz q.1 (badPivotEquiv4 r eta q.2).1 (badPivotEquiv4 r eta q.2).2

theorem restriction10_zero_iff_coefficients {m : ℕ} {r : Fin m → ℕ}
    (a : Fin 10 → K) (k : Fin 10) (i : RothAuxPivots r)
    (c : RothAuxCoefficients r → K) :
    substitute10 a k (derivative10 (pivotDerivative10 k (fun h => (i h).val))
      (polynomial10 c)) = 0 ↔
      ∀ j : (h : Fin m) → Block9 (r h - (i h).val),
        (substitute10 a k (derivative10 (pivotDerivative10 k (fun h => (i h).val))
          (polynomial10 c))).coeff
          (freeExponent10 (fun h => r h - (i h).val) k j) = 0 := by
  constructor
  · intro hz j
    rw [hz, MvPolynomial.coeff_zero]
  · intro hz
    apply MvPolynomial.ext
    intro d
    by_cases hd : (substitute10 a k (derivative10 (pivotDerivative10 k (fun h => (i h).val))
        (polynomial10 c))).coeff d = 0
    · exact hd
    · have hhom := rothAux_transformed_block_homogeneous a k (fun h => (i h).val) c
      have hdeg := hhom d (MvPolynomial.mem_support_iff.mpr hd)
      have hp := rothAux_transformed_pivot_zero a k
        (pivotDerivative10 k (fun h => (i h).val)) c d hd
      obtain ⟨j, hj⟩ := freeExponent10_reconstruct (fun h => r h - (i h).val) k d hdeg hp
      rw [← hj]
      exact hz j

theorem matrix10_kernel_iff_restrictions {m : ℕ} (r : Fin m → ℕ) (eta : ℝ)
    (a : Fin 3 → Fin 10 → Fin 10 → K) (p : Fin 3 → Fin 10 → Fin 10)
    (c : RothAuxCoefficients r → K) :
    (matrix10 r eta a p).mulVec c = 0 ↔
      ∀ (tau : Fin 3) (s : Fin 10)
        (i : {i : RothAuxPivots r // rothAuxPivotCondition r eta i}),
        substitute10 (a tau s) (p tau s)
          (derivative10 (pivotDerivative10 (p tau s) (fun h => (i.val h).val))
            (polynomial10 c)) = 0 := by
  rw [matrix10_kernel_iff_coefficients]
  constructor
  · intro hz tau s i
    apply (restriction10_zero_iff_coefficients (a tau s) (p tau s) i.val c).mpr
    intro j
    have hh := hz (formEquiv10.symm (tau,s)) i j
    simpa only [equation10, Equiv.apply_symm_apply] using hh
  · intro hz f i j
    exact (restriction10_zero_iff_coefficients _ _ i.val c).mp
      (hz (formEquiv10 f).1 (formEquiv10 f).2 i) j

end CompoundFeasibility.Auxiliary10

namespace CompoundFeasibility.Auxiliary10
open SourceMultiblock10 SourceNormalHighIndex10 SchmidtPolynomial10
variable {𝕂 : Type*} [Field 𝕂] [CharZero 𝕂]

theorem rothSource_scaled_chart_pderiv {m : ℕ} (a : Fin 10 → 𝕂) (k j : Fin 10)
    (h : Fin m) (hj : j ≠ k) (v : Vars10 m) :
    MvPolynomial.pderiv (h,j) (chart10 a k v) =
      MvPolynomial.C (a k) * (if v = (h,j) then 1 else 0) -
        MvPolynomial.C (a j) * (if v = (h,k) then 1 else 0) := by
  classical
  rcases v with ⟨g,l⟩
  by_cases hg : g = h
  · subst g
    by_cases hl : l = k
    · subst l
      simp [chart10, MvPolynomial.pderiv_C_mul, MvPolynomial.pderiv_X,
        Pi.single_apply, Prod.mk.injEq, hj, Ne.symm hj, map_sum, mul_ite,
        Finset.sum_ite_eq', Finset.sum_ite_eq, eq_comm]
    · simp [chart10, hl, MvPolynomial.pderiv_C_mul, MvPolynomial.pderiv_X,
        Pi.single_apply, Prod.mk.injEq, hl, Ne.symm hl, eq_comm]
  · by_cases hl : l = k <;>
      simp [chart10, hl, MvPolynomial.pderiv_C_mul, MvPolynomial.pderiv_X,
        Pi.single_apply, Prod.mk.injEq, hg, Ne.symm hg, map_sum]

theorem rothSource_scaled_chain {m : ℕ} (a : Fin 10 → 𝕂) (k j : Fin 10)
    (h : Fin m) (hj : j ≠ k) (P : MvPolynomial (Vars10 m) 𝕂) :
    MvPolynomial.pderiv (h,j) (substitute10 a k P) =
      MvPolynomial.C (a k) * substitute10 a k (MvPolynomial.pderiv (h,j) P) -
        MvPolynomial.C (a j) * substitute10 a k (MvPolynomial.pderiv (h,k) P) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C c => simp [substitute10]
  | add P Q hP hQ => simp only [map_add, hP, hQ]; ring
  | mul_X P v hP =>
    simp only [map_mul, MvPolynomial.pderiv_mul, map_add, hP]
    rw [show substitute10 a k (MvPolynomial.X v) = chart10 a k v by simp [substitute10],
      rothSource_scaled_chart_pderiv a k j h hj v]
    simp only [MvPolynomial.pderiv_X, Pi.single_apply, apply_ite, map_one, map_zero]
    split_ifs <;> simp_all <;> ring

theorem rothSource_weight_mono {m : ℕ} (r : Fin m → ℕ)
    (J K : Vars10 m →₀ ℕ) (hJK : J ≤ K) :
    rothSourceDerivativeWeight r J ≤ rothSourceDerivativeWeight r K := by
  apply Finset.sum_le_sum
  intro h _
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply Finset.sum_le_sum
  intro i _
  exact_mod_cast hJK (h,i)

theorem rothSource_weight_pivot {m : ℕ} (r : Fin m → ℕ) (k : Fin 10) (i : Fin m → ℕ) :
    rothSourceDerivativeWeight r (pivotDerivative10 k i) = ∑ h, (i h : ℝ) / r h := by
  simp [rothSourceDerivativeWeight, pivotDerivative10, Finset.sum_ite_eq,
    Finset.sum_ite_eq']

noncomputable def rothSourceFreeOrder {m : ℕ} (k : Fin 10) (J : Vars10 m →₀ ℕ) : ℕ :=
  ∑ u ∈ Finset.univ.filter (fun u : Vars10 m => u.2 ≠ k), J u

theorem rothSource_free_add {m : ℕ} (k : Fin 10) (J K : Vars10 m →₀ ℕ) :
    rothSourceFreeOrder k (J + K) = rothSourceFreeOrder k J + rothSourceFreeOrder k K := by
  simp [rothSourceFreeOrder, Finsupp.add_apply, Finset.sum_add_distrib]

theorem rothSource_free_single {m : ℕ} (k : Fin 10) (u : Vars10 m) :
    rothSourceFreeOrder k (Finsupp.single u 1) = if u.2 = k then 0 else 1 := by
  classical
  simp [rothSourceFreeOrder, Finsupp.single_apply, Finset.sum_ite_eq', Finset.sum_ite_eq]

theorem rothSource_free_zero_pivot {m : ℕ} (k : Fin 10) (J : Vars10 m →₀ ℕ)
    (hJ : rothSourceFreeOrder k J = 0) :
    J = pivotDerivative10 k (fun h => J (h,k)) := by
  classical
  ext u
  by_cases hu : u.2 = k
  · have he : u = (u.1,k) := Prod.ext rfl hu
    simpa [pivotDerivative10, hu] using congrArg J he
  · have hle : J u ≤ rothSourceFreeOrder k J :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_filter.mpr ⟨Finset.mem_univ u,hu⟩)
    have hz : J u = 0 := by omega
    simp [pivotDerivative10, hu, hz]

theorem rothSource_scaled_mixed_vanishing {m : ℕ} (r : Fin m → ℕ)
    (a : Fin 10 → 𝕂) (k : Fin 10) (ha : a k ≠ 0) (T : ℝ)
    (P : MvPolynomial (Vars10 m) 𝕂)
    (hpivot : ∀ i : Fin m → ℕ, (∑ h, (i h : ℝ) / r h) < T →
      substitute10 a k
        (derivative10 (pivotDerivative10 k i) P) = 0)
    (J : Vars10 m →₀ ℕ) (hw : rothSourceDerivativeWeight r J < T) :
    substitute10 a k (derivative10 J P) = 0 := by
  classical
  have go : ∀ n : ℕ, ∀ J : Vars10 m →₀ ℕ,
      rothSourceFreeOrder k J = n → rothSourceDerivativeWeight r J < T →
      substitute10 a k (derivative10 J P) = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro J hn hw
      by_cases hz : n = 0
      · have he := rothSource_free_zero_pivot k J (hn.trans hz)
        have hweight : (∑ h, (J (h,k) : ℝ) / r h) < T := by
          rw [← rothSource_weight_pivot r k, ← he]
          exact hw
        rw [he]
        exact hpivot _ hweight
      · have hex : ∃ u : Vars10 m, u.2 ≠ k ∧ J u ≠ 0 := by
          by_contra! hno
          have hzero : rothSourceFreeOrder k J = 0 := by
            apply Finset.sum_eq_zero
            intro u hu
            exact hno u (Finset.mem_filter.mp hu).2
          omega
        obtain ⟨u, hu, hJu⟩ := hex
        let K := J - Finsupp.single u 1
        let Kp := K + Finsupp.single (u.1,k) 1
        have hle : Finsupp.single u 1 ≤ J := by
          rw [Finsupp.single_le_iff]
          omega
        have hKeq : K + Finsupp.single u 1 = J := tsub_add_cancel_of_le hle
        have hKcount : rothSourceFreeOrder k K + 1 = n := by
          have hc := congrArg (rothSourceFreeOrder k) hKeq
          simpa [rothSource_free_add, rothSource_free_single, hu, hn] using hc
        have hKpcount : rothSourceFreeOrder k Kp = rothSourceFreeOrder k K := by
          simp [Kp, rothSource_free_add, rothSource_free_single]
        have hKweight : rothSourceDerivativeWeight r K ≤ rothSourceDerivativeWeight r J :=
          rothSource_weight_mono r K J tsub_le_self
        have hKpweight : rothSourceDerivativeWeight r Kp = rothSourceDerivativeWeight r J := by
          calc
            _ = rothSourceDerivativeWeight r K + 1 / (r u.1 : ℝ) := by
              rw [rothSource_weight_add, rothSource_weight_single]
            _ = _ := by rw [← hKeq, rothSource_weight_add, rothSource_weight_single]
        have hK := ih (rothSourceFreeOrder k K) (by omega) K rfl (lt_of_le_of_lt hKweight hw)
        have hKp := ih (rothSourceFreeOrder k Kp) (by omega) Kp rfl (hKpweight ▸ hw)
        change substitute10 a k
          (derivative10 (K + Finsupp.single (u.1,k) 1) P) = 0 at hKp
        have hc := rothSource_scaled_chain a k u.2 u.1 hu
          (derivative10 K P)
        rw [SourceMultiblock10.source10_pderiv_hasse, SourceMultiblock10.source10_pderiv_hasse] at hc
        simp only [hK, map_zero, map_nsmul, hKp, nsmul_zero, mul_zero, sub_zero] at hc
        rw [hKeq] at hc
        have hcoeff : (MvPolynomial.C (a k) : MvPolynomial (Vars10 m) 𝕂) ≠ 0 := by
          intro hz
          apply ha
          apply MvPolynomial.C_injective (σ := Vars10 m)
          simpa only [map_zero] using hz
        have hsm := (mul_eq_zero.mp hc.symm).resolve_left hcoeff
        rw [nsmul_eq_mul] at hsm
        exact (mul_eq_zero.mp hsm).resolve_left (by
          intro hh
          have hz : ((K (u.1,u.2) + 1 : ℕ) : 𝕂) = 0 := by
            apply MvPolynomial.C_injective (σ := Vars10 m)
            simpa only [map_natCast, map_zero] using hh
          exact (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero _)) hz)
  exact go _ J rfl hw


end CompoundFeasibility.Auxiliary10

namespace CompoundFeasibility.Auxiliary10
open SourceMultiblock10 SourceNormalHighIndex10 SchmidtPolynomial10
variable {𝕂 : Type*} [Field 𝕂] [CharZero 𝕂]

def kernelChart10 {m : ℕ} (a : Fin 10 → 𝕂) (k : Fin m → Fin 10)
    (u : Vars10 m) : MvPolynomial (Vars10 m) 𝕂 :=
  if u.2 = k u.1 then
    -(∑ j ∈ Finset.univ.erase (k u.1),
      MvPolynomial.C (a j / a (k u.1)) * MvPolynomial.X (u.1,j))
  else MvPolynomial.X u

def kernelRestriction10 {m : ℕ} (a : Fin 10 → 𝕂) (k : Fin m → Fin 10) :
    MvPolynomial (Vars10 m) 𝕂 →+* MvPolynomial (Vars10 m) 𝕂 :=
  MvPolynomial.eval₂Hom MvPolynomial.C (kernelChart10 a k)

theorem kernelChart10_form {m : ℕ} (a : Fin 10 → 𝕂)
    (k : Fin m → Fin 10) (hk : ∀ h, a (k h) ≠ 0) (h : Fin m) :
    (∑ j : Fin 10, MvPolynomial.C (a j) * kernelChart10 a k (h,j)) = 0 := by
  rw [← Finset.sum_erase_add Finset.univ _ (Finset.mem_univ (k h))]
  have hfree : (∑ j ∈ Finset.univ.erase (k h), MvPolynomial.C (a j) *
      kernelChart10 a k (h,j)) =
      ∑ j ∈ Finset.univ.erase (k h), MvPolynomial.C (a j) * MvPolynomial.X (h,j) := by
    apply Finset.sum_congr rfl
    intro j hj
    simp [kernelChart10, (Finset.mem_erase.mp hj).1]
  rw [hfree]
  have hpivot : MvPolynomial.C (a (k h)) * kernelChart10 a k (h,k h) =
      -(∑ j ∈ Finset.univ.erase (k h), MvPolynomial.C (a j) * MvPolynomial.X (h,j)) := by
    simp only [kernelChart10, Prod.fst, Prod.snd, if_pos rfl, ite_true, mul_neg, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    rw [← mul_assoc, ← MvPolynomial.C_mul]
    congr 1
    field_simp [hk h]
  rw [hpivot]
  ring

def chartTransport10 {m : ℕ} (a : Fin 10 → 𝕂) (p : Fin 10) (k : Fin m → Fin 10) :
    MvPolynomial (Vars10 m) 𝕂 →+* MvPolynomial (Vars10 m) 𝕂 :=
  MvPolynomial.eval₂Hom MvPolynomial.C (fun u =>
    MvPolynomial.C ((a p)⁻¹) * kernelChart10 a k u)

theorem chartTransport10_variable {m : ℕ} (a : Fin 10 → 𝕂)
    (p : Fin 10) (hp : a p ≠ 0) (k : Fin m → Fin 10)
    (hk : ∀ h, a (k h) ≠ 0) (u : Vars10 m) :
    chartTransport10 a p k (chart10 a p u) = kernelChart10 a k u := by
  have hcancel : (MvPolynomial.C (a p) : MvPolynomial (Vars10 m) 𝕂) *
      MvPolynomial.C ((a p)⁻¹) = 1 := by
    rw [← MvPolynomial.C_mul, mul_inv_cancel₀ hp, map_one]
  by_cases hu : u.2 = p
  · have hsum := kernelChart10_form a k hk u.1
    rw [← Finset.sum_erase_add Finset.univ _ (Finset.mem_univ p)] at hsum
    have hrel : -(∑ j ∈ Finset.univ.erase p, MvPolynomial.C (a j) *
        kernelChart10 a k (u.1,j)) =
        MvPolynomial.C (a p) * kernelChart10 a k (u.1,p) := by
      linear_combination -hsum
    simp only [chart10, if_pos hu, map_neg, map_sum, map_mul]
    simp only [chartTransport10, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X']
    calc
      _ = MvPolynomial.C ((a p)⁻¹) *
          -(∑ j ∈ Finset.univ.erase p, MvPolynomial.C (a j) *
            kernelChart10 a k (u.1,j)) := by
        rw [mul_neg, Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = _ := by
        rw [hrel, ← mul_assoc, mul_comm _ (MvPolynomial.C (a p)), hcancel]
        simp [← hu]
  · simp only [chart10, if_neg hu, map_mul]
    simp only [chartTransport10, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X']
    rw [← mul_assoc, hcancel, one_mul]

theorem chartTransport10_substitute {m : ℕ} (a : Fin 10 → 𝕂)
    (p : Fin 10) (hp : a p ≠ 0) (k : Fin m → Fin 10)
    (hk : ∀ h, a (k h) ≠ 0) (P : MvPolynomial (Vars10 m) 𝕂) :
    chartTransport10 a p k (substitute10 a p P) = kernelRestriction10 a k P := by
  have he : (chartTransport10 a p k).comp (substitute10 a p) = kernelRestriction10 a k := by
    apply MvPolynomial.ringHom_ext
    · intro z
      simp [substitute10, chartTransport10, kernelRestriction10]
    · intro u
      simpa [substitute10, kernelRestriction10] using chartTransport10_variable a p hp k hk u
  exact congrArg (fun f => f P) he

theorem derivative10_zero_of_block_excess {m : ℕ} (r : Fin m → ℕ)
    (P : MvPolynomial (Vars10 m) 𝕂) (hP : homogeneous10 r P)
    (J : Vars10 m →₀ ℕ) (h : Fin m) (hJ : r h < ∑ j : Fin 10, J (h,j)) :
    derivative10 J P = 0 := by
  apply MvPolynomial.ext
  intro d
  rw [derivative10_coeff, MvPolynomial.coeff_zero]
  have hz : P.coeff (d + J) = 0 := by
    by_contra hn
    have hdegree := hP (d + J) (MvPolynomial.mem_support_iff.mpr hn) h
    have hle : (∑ j : Fin 10, J (h,j)) ≤ ∑ j : Fin 10, (d + J) (h,j) := by
      apply Finset.sum_le_sum
      intro j _
      simp only [Finsupp.add_apply]
      omega
    omega
  rw [hz, zero_mul]

theorem matrix10_kernel_all_derivatives {m : ℕ} (r : Fin m → ℕ) (eta : ℝ)
    (a : Fin 3 → Fin 10 → Fin 10 → 𝕂) (p : Fin 3 → Fin 10 → Fin 10)
    (hp : ∀ tau s, a tau s (p tau s) ≠ 0)
    (c : RothAuxCoefficients r → 𝕂)
    (hc : (matrix10 r eta a p).mulVec c = 0)
    (tau : Fin 3) (s : Fin 10) (J : Vars10 m →₀ ℕ)
    (hJ : rothSourceDerivativeWeight r J < (1 / 10 - eta) * m)
    (k : Fin m → Fin 10) (hk : ∀ h, a tau s (k h) ≠ 0) :
    kernelRestriction10 (a tau s) k (derivative10 J (polynomial10 c)) = 0 := by
  have hpivot := (matrix10_kernel_iff_restrictions r eta a p c).mp hc
  have hall : ∀ i : Fin m → ℕ, (∑ h, (i h : ℝ) / r h) < (1 / 10 - eta) * m →
      substitute10 (a tau s) (p tau s)
        (derivative10 (pivotDerivative10 (p tau s) i) (polynomial10 c)) = 0 := by
    intro i hi
    by_cases hb : ∀ h, i h ≤ r h
    · let iFin : RothAuxPivots r := fun h => ⟨i h, by have hh := hb h; omega⟩
      exact hpivot tau s ⟨iFin, hi⟩
    · push_neg at hb
      obtain ⟨h, hh⟩ := hb
      have hsum : (∑ j : Fin 10, pivotDerivative10 (p tau s) i (h,j)) = i h := by
        simp [pivotDerivative10, Finset.sum_ite_eq, Finset.sum_ite_eq']
      have hz := derivative10_zero_of_block_excess r (polynomial10 c) (polynomial10_homogeneous c)
        (pivotDerivative10 (p tau s) i) h (by rw [hsum]; exact hh)
      simp [hz]
  rw [← chartTransport10_substitute (a tau s) (p tau s) (hp tau s) k hk]
  rw [rothSource_scaled_mixed_vanishing r (a tau s) (p tau s) (hp tau s) _
    (polynomial10 c) hall J hJ, map_zero]

end CompoundFeasibility.Auxiliary10
namespace CompoundFeasibility.Auxiliary10
open SourceMultiblock10 SourceNormalHighIndex10 SchmidtPolynomial10
variable {R S : Type*} [CommRing R] [CommRing S]

theorem chart10_map {m : ℕ} (f : R →+* S) (a : Fin 10 → R) (k : Fin 10) (u : Vars10 m) :
    (chart10 a k u).map f = chart10 (fun j => f (a j)) k u := by
  unfold chart10
  split_ifs <;> simp [map_sum, map_mul]

theorem substitute10_map {m : ℕ} (f : R →+* S) (a : Fin 10 → R) (k : Fin 10)
    (P : MvPolynomial (Vars10 m) R) :
    (substitute10 a k P).map f = substitute10 (fun j => f (a j)) k (P.map f) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [substitute10]
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P v hP =>
    simp only [map_mul, hP]
    rw [show substitute10 a k (MvPolynomial.X v) = chart10 a k v by simp [substitute10]]
    rw [chart10_map]
    simp [substitute10]

theorem polynomial10_map {m : ℕ} {r : Fin m → ℕ} (f : R →+* S)
    (c : RothAuxCoefficients r → R) :
    (polynomial10 c).map f = polynomial10 (fun b => f (c b)) := by
  simp [polynomial10]

theorem matrix10_map {m : ℕ} (f : R →+* S) (r : Fin m → ℕ) (eta : ℝ)
    (a : Fin 3 → Fin 10 → Fin 10 → R) (p : Fin 3 → Fin 10 → Fin 10)
    (q : Equations10 r eta) (b : RothAuxCoefficients r) :
    f (matrix10 r eta a p q b) = matrix10 r eta (fun tau s j => f (a tau s j)) p q b := by
  unfold matrix10 equation10
  rw [← MvPolynomial.coeff_map, substitute10_map, derivative10_map]
  simp

end CompoundFeasibility.Auxiliary10
