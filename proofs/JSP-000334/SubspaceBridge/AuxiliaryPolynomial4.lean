import SubspaceBridge.AuxiliaryCount4
import SubspaceBridge.SourceForms4
import SubspaceBridge.SourceMultiblock4
open scoped BigOperators Matrix Classical
noncomputable section
namespace CompoundFeasibility.Auxiliary4
open SourceMultiblock4

noncomputable def rothSourceDerivativeWeight {m : ℕ} (r : Fin m → ℕ)
    (J : Vars4 m →₀ ℕ) : ℝ := ∑ h, (∑ i : Fin 4, (J (h,i) : ℝ))/(r h : ℝ)

def exponent4 {m : ℕ} {r : Fin m → ℕ} (b : RothAuxCoefficients r) : Vars4 m →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun u => ((b u.1).val u.2).val)

theorem exponent4_injective {m : ℕ} (r : Fin m → ℕ) : Function.Injective (@exponent4 m r) := by
  intro b c h
  funext g
  apply Subtype.ext
  funext j
  apply Fin.ext
  exact congrArg (fun e : Vars4 m →₀ ℕ => e (g,j)) h

def polynomial4 {m : ℕ} {r : Fin m → ℕ} {R : Type*} [CommRing R] (c : RothAuxCoefficients r → R) : MvPolynomial (Vars4 m) R :=
  ∑ b, MvPolynomial.monomial (exponent4 b) (c b)

theorem polynomial4_coeff {m : ℕ} {r : Fin m → ℕ} {R : Type*} [CommRing R] (c : RothAuxCoefficients r → R) (b : RothAuxCoefficients r) :
    (polynomial4 c).coeff (exponent4 b) = c b := by
  simp only [polynomial4,MvPolynomial.coeff_sum,MvPolynomial.coeff_monomial,(exponent4_injective r).eq_iff]
  simp

def homogeneous4 {m : ℕ} {R : Type*} [CommRing R] (r : Fin m → ℕ) (P : MvPolynomial (Vars4 m) R) : Prop :=
  ∀ d ∈ P.support, ∀ h, ∑ j : Fin 4, d (h,j) = r h

theorem polynomial4_homogeneous {m : ℕ} {r : Fin m → ℕ} {R : Type*} [CommRing R] (c : RothAuxCoefficients r → R) : homogeneous4 r (polynomial4 c) := by
  intro d hd h
  obtain ⟨b,_,hb⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hd)
  have hab := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hb)
  subst d
  exact (b h).property


variable {R : Type*} [CommRing R]

def chart4 {m : ℕ} (a : Fin 4 → R) (k : Fin 4) (u : Vars4 m) : MvPolynomial (Vars4 m) R :=
  if u.2 = k then -(∑ j ∈ Finset.univ.erase k, MvPolynomial.C (a j) * MvPolynomial.X (u.1,j))
  else MvPolynomial.C (a k) * MvPolynomial.X u

def substitute4 {m : ℕ} (a : Fin 4 → R) (k : Fin 4) : MvPolynomial (Vars4 m) R →+* MvPolynomial (Vars4 m) R :=
  MvPolynomial.eval₂Hom MvPolynomial.C (chart4 a k)

def pivotDerivative4 {m : ℕ} (k : Fin 4) (i : Fin m → ℕ) : Vars4 m →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun u => if u.2 = k then i u.1 else 0)

theorem transformed_monomial4 {m : ℕ} (a : Fin 4 → R) (k : Fin 4) (J b : Vars4 m →₀ ℕ) :
    substitute4 a k (derivative4 J (MvPolynomial.monomial b 1)) =
      MvPolynomial.C (∏ u : Vars4 m, (Nat.choose (b u) (J u) : R)) *
        ∏ u : Vars4 m, chart4 a k u ^ (b-J) u := by
  rw [derivative4_monomial]
  change MvPolynomial.eval₂ MvPolynomial.C (chart4 a k) (MvPolynomial.monomial (b-J)
    (1 * ∏ u : Vars4 m, (Nat.choose (b u) (J u) : R))) = _
  rw [MvPolynomial.eval₂_monomial,one_mul]
  congr 1
  exact Finsupp.prod_fintype _ _ (fun _ => pow_zero _)

theorem exponent4_sum {m : ℕ} {r : Fin m → ℕ} (b : RothAuxCoefficients r) :
    (∑ u : Vars4 m, exponent4 b u) = ∑ h, r h := by
  rw [Fintype.sum_prod_type]
  exact Finset.sum_congr rfl (fun h _ => (b h).property)


theorem transformed_coeff_sum4 {m : ℕ} {ι : Type*} [Fintype ι]
    (e : ι → Vars4 m →₀ ℕ) (c : ι → R)
    (J d : Vars4 m →₀ ℕ)
    (a : Fin 4 → R) (k : Fin 4) :
    let S := substitute4 (m := m) a k;
    (S (derivative4 J (∑ b, MvPolynomial.monomial (e b) (c b)))).coeff d =
      ∑ b, c b * (S (derivative4 J
        (MvPolynomial.monomial (e b) 1))).coeff d := by
  dsimp only
  let S := substitute4 (m := m) a k
  have hadd : derivative4 J
      (∑ b, MvPolynomial.monomial (e b) (c b)) =
      ∑ b, derivative4 J (MvPolynomial.monomial (e b) (c b)) := by
    apply MvPolynomial.ext
    intro a
    simp only [derivative4_coeff, MvPolynomial.coeff_sum,
      Finset.sum_mul]
  rw [hadd, map_sum, MvPolynomial.coeff_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [derivative4_monomial, derivative4_monomial]
  simp only [one_mul]
  have hc : MvPolynomial.monomial (e b - J)
      (c b * ∏ u : Vars4 m, (Nat.choose (e b u) (J u) : R)) =
      MvPolynomial.C (c b) * MvPolynomial.monomial (e b - J)
        (∏ u : Vars4 m, (Nat.choose (e b u) (J u) : R)) := by
    rw [MvPolynomial.C_mul_monomial]
  rw [hc, map_mul]
  have hC : S (MvPolynomial.C (c b)) = MvPolynomial.C (c b) := by
    simp [S,substitute4]
  rw [hC, MvPolynomial.coeff_C_mul]


theorem rothAux_weight_block {m : ℕ} (d : Vars4 m →₀ ℕ) (h : Fin m) :
    Finsupp.weight (fun u : Vars4 m => if u.1 = h then 1 else 0) d =
      ∑ j : Fin 4, d (h,j) := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  simp only [Fintype.sum_prod_type, nsmul_eq_mul]
  simp only [mul_ite, ite_mul, one_mul, zero_mul, mul_one, mul_zero]
  calc
    (∑ x : Fin m, ∑ j : Fin 4,
        if x = h then d (x,j) else 0) =
      ∑ x : Fin m,
        if x = h then (∑ j : Fin 4, d (x,j)) else 0 := by
          apply Finset.sum_congr rfl
          intro x _
          by_cases hx : x = h
          · simp [hx]
          · simp [hx]
    _ = ∑ j : Fin 4, d (h,j) := by simp

theorem rothAux_weight_pivot {m : ℕ} (d : Vars4 m →₀ ℕ) (k : Fin 4) :
    Finsupp.weight (fun u : Vars4 m => if u.2 = k then 1 else 0) d =
      ∑ h : Fin m, d (h,k) := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  simp [Fintype.sum_prod_type, nsmul_eq_mul]

theorem rothAux_weighted_neg {m : ℕ} (w : Vars4 m → ℕ)
    (P : MvPolynomial (Vars4 m) R) (n : ℕ)
    (hP : MvPolynomial.IsWeightedHomogeneous w P n) :
    MvPolynomial.IsWeightedHomogeneous w (-P) n := by
  intro d hd
  apply hP
  simpa using hd

theorem chart4_block_weight {m : ℕ} (a : Fin 4 → R) (k : Fin 4)
    (h : Fin m) (u : Vars4 m) :
    MvPolynomial.IsWeightedHomogeneous (fun v : Vars4 m => if v.1 = h then 1 else 0)
      (chart4 a k u) (if u.1 = h then 1 else 0) := by
  let w := fun v : Vars4 m => if v.1 = h then 1 else 0
  have hx (j : Fin 4) : MvPolynomial.IsWeightedHomogeneous w
      (MvPolynomial.C (a j) * MvPolynomial.X (u.1,j)) (if u.1 = h then 1 else 0) := by
    simpa only [zero_add] using
      (MvPolynomial.isWeightedHomogeneous_C w (a j)).mul (MvPolynomial.isWeightedHomogeneous_X R w (u.1,j))
  unfold chart4
  by_cases hu : u.2 = k
  · rw [if_pos hu]
    exact rothAux_weighted_neg w _ _
      (MvPolynomial.IsWeightedHomogeneous.sum _ _ _ (fun j _ => hx j))
  · rw [if_neg hu]
    simpa only [zero_add] using
      (MvPolynomial.isWeightedHomogeneous_C w (a k)).mul (MvPolynomial.isWeightedHomogeneous_X R w u)

theorem chart4_pivot_weight {m : ℕ} (a : Fin 4 → R) (k : Fin 4)
    (u : Vars4 m) :
    MvPolynomial.IsWeightedHomogeneous (fun v : Vars4 m => if v.2 = k then 1 else 0)
      (chart4 a k u) 0 := by
  let w := fun v : Vars4 m => if v.2 = k then 1 else 0
  have hx (j : Fin 4) (hj : j ≠ k) : MvPolynomial.IsWeightedHomogeneous w
      (MvPolynomial.C (a j) * MvPolynomial.X (u.1,j)) 0 := by
    simpa only [w, hj, if_false, zero_add] using
      (MvPolynomial.isWeightedHomogeneous_C w (a j)).mul (MvPolynomial.isWeightedHomogeneous_X R w (u.1,j))
  unfold chart4
  split_ifs with hu
  · exact rothAux_weighted_neg w _ 0
      (MvPolynomial.IsWeightedHomogeneous.sum _ _ 0 (fun j hj => hx j (Finset.mem_erase.mp hj).1))
  · simpa only [w, hu, if_false, zero_add] using
      (MvPolynomial.isWeightedHomogeneous_C w (a k)).mul (MvPolynomial.isWeightedHomogeneous_X R w u)

theorem rothAux_scaled_monomial_weighted {m : ℕ} (a : Fin 4 → R) (k : Fin 4)
    (J b : Vars4 m →₀ ℕ) (w : Vars4 m → ℕ) (v : Vars4 m → ℕ)
    (hv : ∀ u, MvPolynomial.IsWeightedHomogeneous w (chart4 a k u) (v u)) :
    MvPolynomial.IsWeightedHomogeneous w
      (substitute4 a k
        (derivative4 J (MvPolynomial.monomial b 1)))
      (∑ u : Vars4 m, (b - J) u * v u) := by
  rw [transformed_monomial4]
  have hp := MvPolynomial.IsWeightedHomogeneous.prod Finset.univ
    (fun u : Vars4 m => chart4 a k u ^ (b - J) u)
    (fun u => (b - J) u * v u) (fun u _ => by simpa only [nsmul_eq_mul] using (hv u).pow ((b - J) u))
  simpa only [zero_add] using (MvPolynomial.isWeightedHomogeneous_C w _).mul hp



theorem rothAux_transformed_polynomial {m : ℕ} {r : Fin m → ℕ}
    (a : Fin 4 → R) (k : Fin 4) (J : Vars4 m →₀ ℕ)
    (c : RothAuxCoefficients r → R) :
    substitute4 a k (derivative4 J (polynomial4 c)) =
      ∑ b, MvPolynomial.C (c b) * substitute4 a k
        (derivative4 J (MvPolynomial.monomial (exponent4 b) 1)) := by
  apply MvPolynomial.ext
  intro d
  rw [polynomial4, transformed_coeff_sum4]
  simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul]

theorem rothAux_pivot_monomial_block_weight {m : ℕ} {r : Fin m → ℕ}
    (a : Fin 4 → R) (k : Fin 4) (i : Fin m → ℕ) (b : RothAuxCoefficients r) (h : Fin m) :
    MvPolynomial.IsWeightedHomogeneous (fun u : Vars4 m => if u.1 = h then 1 else 0)
      (substitute4 a k (derivative4
        (pivotDerivative4 k i) (MvPolynomial.monomial (exponent4 b) 1)))
      (r h - i h) := by
  let J := pivotDerivative4 k i
  let w := fun u : Vars4 m => if u.1 = h then 1 else 0
  by_cases hle : J ≤ exponent4 b
  · have hw := rothAux_scaled_monomial_weighted a k J (exponent4 b) w w
      (chart4_block_weight a k h)
    have heq : (∑ u : Vars4 m, (exponent4 b - J) u * w u) =
        ∑ j : Fin 4, (exponent4 b - J) (h,j) := by
      have he := rothAux_weight_block (exponent4 b - J) h
      rw [Finsupp.weight_apply] at he
      rw [Finsupp.sum_fintype (exponent4 b - J)
        (fun u (n : ℕ) => n • w u) (by intro u; simp)] at he
      simpa only [nsmul_eq_mul, Nat.cast_id, w] using he
    have hdeg : (∑ j : Fin 4, (exponent4 b - J) (h,j)) = r h - i h := by
      change (∑ j : Fin 4, (exponent4 b (h,j) - J (h,j))) = _
      rw [Finset.sum_tsub_distrib _ (fun j _ => hle (h,j))]
      have hb : (∑ j : Fin 4, exponent4 b (h,j)) = r h := (b h).property
      rw [hb]
      congr 1
      simp [J, pivotDerivative4]
    rw [heq, hdeg] at hw
    exact hw
  · change ¬ ∀ u, J u ≤ exponent4 b u at hle
    push_neg at hle
    obtain ⟨u, hu⟩ := hle
    have hz : (∏ v : Vars4 m, (Nat.choose (exponent4 b v) (J v) : R)) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ u)
      simp [Nat.choose_eq_zero_of_lt hu]
    rw [transformed_monomial4, hz, map_zero, zero_mul]
    exact MvPolynomial.isWeightedHomogeneous_zero R w _

theorem rothAux_transformed_block_weight {m : ℕ} {r : Fin m → ℕ}
    (a : Fin 4 → R) (k : Fin 4) (i : Fin m → ℕ)
    (c : RothAuxCoefficients r → R) (h : Fin m) :
    MvPolynomial.IsWeightedHomogeneous (fun u : Vars4 m => if u.1 = h then 1 else 0)
      (substitute4 a k (derivative4
        (pivotDerivative4 k i) (polynomial4 c))) (r h - i h) := by
  rw [rothAux_transformed_polynomial]
  apply MvPolynomial.IsWeightedHomogeneous.sum
  intro b _
  simpa only [zero_add] using (MvPolynomial.isWeightedHomogeneous_C _ (c b)).mul
    (rothAux_pivot_monomial_block_weight a k i b h)

theorem rothAux_transformed_block_homogeneous {m : ℕ} {r : Fin m → ℕ}
    (a : Fin 4 → R) (k : Fin 4) (i : Fin m → ℕ)
    (c : RothAuxCoefficients r → R) :
    homogeneous4 (fun h => r h - i h)
      (substitute4 a k (derivative4
        (pivotDerivative4 k i) (polynomial4 c))) := by
  intro d hd h
  rw [← rothAux_weight_block]
  exact rothAux_transformed_block_weight a k i c h (MvPolynomial.mem_support_iff.mp hd)

theorem rothAux_transformed_pivot_weight {m : ℕ} {r : Fin m → ℕ}
    (a : Fin 4 → R) (k : Fin 4) (J : Vars4 m →₀ ℕ)
    (c : RothAuxCoefficients r → R) :
    MvPolynomial.IsWeightedHomogeneous (fun u : Vars4 m => if u.2 = k then 1 else 0)
      (substitute4 a k (derivative4 J (polynomial4 c))) 0 := by
  rw [rothAux_transformed_polynomial]
  apply MvPolynomial.IsWeightedHomogeneous.sum
  intro b _
  have hb := rothAux_scaled_monomial_weighted a k J (exponent4 b)
    (fun u : Vars4 m => if u.2 = k then 1 else 0) (fun _ => 0)
    (chart4_pivot_weight a k)
  simp only [mul_zero, Finset.sum_const_zero] at hb
  simpa only [zero_add] using (MvPolynomial.isWeightedHomogeneous_C _ (c b)).mul hb

theorem rothAux_transformed_pivot_zero {m : ℕ} {r : Fin m → ℕ}
    (a : Fin 4 → R) (k : Fin 4) (J : Vars4 m →₀ ℕ)
    (c : RothAuxCoefficients r → R) (d : Vars4 m →₀ ℕ)
    (hd : (substitute4 a k
      (derivative4 J (polynomial4 c))).coeff d ≠ 0) (h : Fin m) :
    d (h,k) = 0 := by
  have hw := rothAux_transformed_pivot_weight a k J c hd
  rw [rothAux_weight_pivot] at hw
  have hle : d (h,k) ≤ ∑ g : Fin m, d (g,k) :=
    Finset.single_le_sum (fun g _ => Nat.zero_le (d (g,k))) (Finset.mem_univ h)
  omega



def freeExponent4 {m : ℕ} (s : Fin m → ℕ) (k : Fin 4)
    (j : (h : Fin m) → Block3 (s h)) : Vars4 m →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun u => Fin.insertNth (α := fun _ : Fin 4 => ℕ) k 0 (fun t : Fin 3 => ((j u.1).val t).val) u.2)

theorem freeExponent4_reconstruct {m : ℕ} (s : Fin m → ℕ) (k : Fin 4)
    (d : Vars4 m →₀ ℕ) (hs : ∀ h, ∑ t : Fin 4, d (h,t) = s h)
    (hz : ∀ h, d (h,k) = 0) :
    ∃ j : (h : Fin m) → Block3 (s h), freeExponent4 s k j = d := by
  have hsum (h : Fin m) : (∑ t : Fin 3, d (h,k.succAbove t)) = s h := by
    have he := Fin.sum_univ_succAbove (fun t => d (h,t)) k
    rw [hs h,hz h,zero_add] at he
    exact he.symm
  let j : (h : Fin m) → Block3 (s h) := fun h => ⟨fun t => ⟨d (h,k.succAbove t),by
    have hh : d (h,k.succAbove t) ≤ ∑ u : Fin 4, d (h,u) :=
      Finset.single_le_sum (s := Finset.univ) (f := fun u : Fin 4 => d (h,u)) (fun u _ => Nat.zero_le _) (Finset.mem_univ _)
    rw [hs h] at hh
    omega⟩,hsum h⟩
  refine ⟨j,?_⟩
  ext u
  rcases u with ⟨h,t⟩
  change Fin.insertNth (α := fun _ : Fin 4 => ℕ) k 0 (fun v : Fin 3 => ((j h).val v).val) t = d (h,t)
  refine Fin.succAboveCases k ?_ (fun v => ?_) t
  · simpa only [Fin.insertNth_apply_same] using (hz h).symm
  · rw [Fin.insertNth_apply_succAbove]



end CompoundFeasibility.Auxiliary4
namespace Aux4Height
open CompoundFeasibility.SourceMultiblock4
open CompoundFeasibility.Auxiliary4 Aux6Mass
variable {R : Type*} [NormedCommRing R] [NormOneClass R]

theorem chart_mass4 {m : ℕ} (a : Fin 4 → R) (k : Fin 4)
    (A : ℝ) (hA : 1 ≤ A) (ha : ∀ j, ‖a j‖ ≤ A) (u : Vars4 m) :
    mass (chart4 a k u) ≤ 4 * A := by
  unfold chart4
  split_ifs
  · rw [mass_neg]
    calc
      _ ≤ ∑ j ∈ Finset.univ.erase k, mass (MvPolynomial.C (a j) * MvPolynomial.X (u.1,j)) := mass_sum _ _
      _ ≤ ∑ _j ∈ Finset.univ.erase k, A := by
        apply Finset.sum_le_sum
        intro j _
        rw [mass_C_mul_X]
        exact ha j
      _ ≤ 4 * A := by simp; linarith
  · rw [mass_C_mul_X]
    exact (ha k).trans (by linarith)

theorem binomial_norm4 {m : ℕ} {r : Fin m → ℕ} (b : RothAuxCoefficients r) (J : Vars4 m →₀ ℕ) :
    ‖∏ u : Vars4 m, (Nat.choose (exponent4 b u) (J u) : R)‖ ≤ (2 : ℝ)^(∑ h, r h) := by
  have hnat (n : ℕ) : ‖(n : R)‖ ≤ (n : ℝ) := by
    rw [← nsmul_one]
    exact (norm_nsmul_le (n := n) (a := (1 : R))).trans_eq (by simp)
  calc
    _ ≤ ∏ u : Vars4 m, ‖(Nat.choose (exponent4 b u) (J u) : R)‖ := Finset.norm_prod_le _ _
    _ ≤ ∏ u : Vars4 m, (2 : ℝ)^exponent4 b u := by
      apply Finset.prod_le_prod
      · intro u _; exact norm_nonneg _
      · intro u _
        apply (hnat _).trans
        have hc : (exponent4 b u).choose (J u) ≤ 2 ^ exponent4 b u := by
          rcases Nat.eq_zero_or_pos (exponent4 b u) with hz | hp
          · rw [hz]; cases J u <;> simp
          · exact (Nat.choose_le_two_pow _ _ hp).le
        exact_mod_cast hc
    _ = _ := by rw [Finset.prod_pow_eq_pow_sum,exponent4_sum]

theorem transformed_entry_norm4 {m : ℕ} {r : Fin m → ℕ}
    (a : Fin 4 → R) (k : Fin 4) (A : ℝ) (hA : 1 ≤ A) (ha : ∀ j, ‖a j‖ ≤ A)
    (b : RothAuxCoefficients r) (J d : Vars4 m →₀ ℕ) :
    ‖(substitute4 a k (derivative4 J (MvPolynomial.monomial (exponent4 b) 1))).coeff d‖ ≤
      (8 * A)^(∑ h, r h) := by
  have hbase : 1 ≤ 4 * A := by linarith
  have hsum : (∑ u : Vars4 m, (exponent4 b-J) u) ≤ ∑ h, r h := by
    rw [← exponent4_sum b]
    exact Finset.sum_le_sum (fun u _ => Nat.sub_le _ _)
  rw [transformed_monomial4]
  calc
    _ ≤ mass (MvPolynomial.C (∏ u : Vars4 m, (Nat.choose (exponent4 b u) (J u) : R)) *
        ∏ u : Vars4 m, chart4 a k u ^ (exponent4 b-J) u) := coeff_le_mass _ _
    _ ≤ mass (MvPolynomial.C (∏ u : Vars4 m, (Nat.choose (exponent4 b u) (J u) : R))) *
        mass (∏ u : Vars4 m, chart4 a k u ^ (exponent4 b-J) u) := mass_mul _ _
    _ ≤ (2 : ℝ)^(∑ h, r h) * (4*A)^(∑ h, r h) := by
      apply mul_le_mul
      · simpa only [MvPolynomial.C_apply,mass_monomial] using binomial_norm4 (R := R) b J
      · calc
          _ ≤ ∏ u : Vars4 m, mass (chart4 a k u ^ (exponent4 b-J) u) := mass_prod _ _
          _ ≤ ∏ u : Vars4 m, (4*A)^(exponent4 b-J) u := by
            apply Finset.prod_le_prod
            · intro u _; exact mass_nonneg _
            · intro u _
              exact (mass_pow _ _).trans (pow_le_pow_left₀ (mass_nonneg _) (chart_mass4 a k A hA ha u) _)
          _ = (4*A)^(∑ u : Vars4 m, (exponent4 b-J) u) := Finset.prod_pow_eq_pow_sum _ _ _
          _ ≤ _ := pow_le_pow_right₀ hbase hsum
      · exact mass_nonneg _
      · positivity
    _ = _ := by rw [← mul_pow]; congr 1; ring

end Aux4Height

namespace CompoundFeasibility.Auxiliary4
open SourceMultiblock4
variable {K : Type*} [CommRing K]

noncomputable def formEquiv4 : Fin 12 ≃ Fin 3 × Fin 4 :=
  (finProdFinEquiv : Fin 3 × Fin 4 ≃ Fin (3 * 4)).symm

noncomputable def equation4 {m : ℕ} {r : Fin m → ℕ} {eta : ℝ}
    (a : Fin 3 → Fin 4 → Fin 4 → K) (p : Fin 3 → Fin 4 → Fin 4)
    (f : Fin 12) (i : {i : RothAuxPivots r // rothAuxPivotCondition r eta i})
    (j : (h : Fin m) → Block3 (r h - (i.val h).val))
    (P : MvPolynomial (Vars4 m) K) : K :=
  (substitute4 (a (formEquiv4 f).1 (formEquiv4 f).2)
    (p (formEquiv4 f).1 (formEquiv4 f).2)
    (derivative4 (pivotDerivative4 (p (formEquiv4 f).1 (formEquiv4 f).2)
      (fun h => (i.val h).val)) P)).coeff
    (freeExponent4 (fun h => r h - (i.val h).val)
      (p (formEquiv4 f).1 (formEquiv4 f).2) j)

noncomputable def matrix4 {m : ℕ} (r : Fin m → ℕ) (eta : ℝ)
    (a : Fin 3 → Fin 4 → Fin 4 → K) (p : Fin 3 → Fin 4 → Fin 4) :
    Matrix (Equations4 r eta) (RothAuxCoefficients r) K :=
  fun q b => equation4 a p q.1 (badPivotEquiv4 r eta q.2).1
    (badPivotEquiv4 r eta q.2).2 (MvPolynomial.monomial (exponent4 b) 1)

theorem matrix4_mulVec {m : ℕ} (r : Fin m → ℕ) (eta : ℝ)
    (a : Fin 3 → Fin 4 → Fin 4 → K) (p : Fin 3 → Fin 4 → Fin 4)
    (c : RothAuxCoefficients r → K) (q : Equations4 r eta) :
    (matrix4 r eta a p).mulVec c q =
      equation4 a p q.1 (badPivotEquiv4 r eta q.2).1
        (badPivotEquiv4 r eta q.2).2 (polynomial4 c) := by
  unfold equation4 polynomial4
  rw [transformed_coeff_sum4]
  simp only [Matrix.mulVec, dotProduct, matrix4, equation4]
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem matrix4_kernel_iff_coefficients {m : ℕ} (r : Fin m → ℕ) (eta : ℝ)
    (a : Fin 3 → Fin 4 → Fin 4 → K) (p : Fin 3 → Fin 4 → Fin 4)
    (c : RothAuxCoefficients r → K) :
    (matrix4 r eta a p).mulVec c = 0 ↔
      ∀ (f : Fin 12) (i : {i : RothAuxPivots r // rothAuxPivotCondition r eta i})
        (j : (h : Fin m) → Block3 (r h - (i.val h).val)),
        equation4 a p f i j (polynomial4 c) = 0 := by
  constructor
  · intro hz f i j
    have h := congrFun hz (f, (badPivotEquiv4 r eta).symm ⟨i,j⟩)
    rw [matrix4_mulVec] at h
    simpa only [Equiv.apply_symm_apply, Pi.zero_apply] using h
  · intro hz
    funext q
    rw [matrix4_mulVec]
    exact hz q.1 (badPivotEquiv4 r eta q.2).1 (badPivotEquiv4 r eta q.2).2

theorem restriction4_zero_iff_coefficients {m : ℕ} {r : Fin m → ℕ}
    (a : Fin 4 → K) (k : Fin 4) (i : RothAuxPivots r)
    (c : RothAuxCoefficients r → K) :
    substitute4 a k (derivative4 (pivotDerivative4 k (fun h => (i h).val))
      (polynomial4 c)) = 0 ↔
      ∀ j : (h : Fin m) → Block3 (r h - (i h).val),
        (substitute4 a k (derivative4 (pivotDerivative4 k (fun h => (i h).val))
          (polynomial4 c))).coeff
          (freeExponent4 (fun h => r h - (i h).val) k j) = 0 := by
  constructor
  · intro hz j
    rw [hz, MvPolynomial.coeff_zero]
  · intro hz
    apply MvPolynomial.ext
    intro d
    by_cases hd : (substitute4 a k (derivative4 (pivotDerivative4 k (fun h => (i h).val))
        (polynomial4 c))).coeff d = 0
    · exact hd
    · have hhom := rothAux_transformed_block_homogeneous a k (fun h => (i h).val) c
      have hdeg := hhom d (MvPolynomial.mem_support_iff.mpr hd)
      have hp := rothAux_transformed_pivot_zero a k
        (pivotDerivative4 k (fun h => (i h).val)) c d hd
      obtain ⟨j, hj⟩ := freeExponent4_reconstruct (fun h => r h - (i h).val) k d hdeg hp
      rw [← hj]
      exact hz j

theorem matrix4_kernel_iff_restrictions {m : ℕ} (r : Fin m → ℕ) (eta : ℝ)
    (a : Fin 3 → Fin 4 → Fin 4 → K) (p : Fin 3 → Fin 4 → Fin 4)
    (c : RothAuxCoefficients r → K) :
    (matrix4 r eta a p).mulVec c = 0 ↔
      ∀ (tau : Fin 3) (s : Fin 4)
        (i : {i : RothAuxPivots r // rothAuxPivotCondition r eta i}),
        substitute4 (a tau s) (p tau s)
          (derivative4 (pivotDerivative4 (p tau s) (fun h => (i.val h).val))
            (polynomial4 c)) = 0 := by
  rw [matrix4_kernel_iff_coefficients]
  constructor
  · intro hz tau s i
    apply (restriction4_zero_iff_coefficients (a tau s) (p tau s) i.val c).mpr
    intro j
    have hh := hz (formEquiv4.symm (tau,s)) i j
    simpa only [equation4, Equiv.apply_symm_apply] using hh
  · intro hz f i j
    exact (restriction4_zero_iff_coefficients _ _ i.val c).mp
      (hz (formEquiv4 f).1 (formEquiv4 f).2 i) j

end CompoundFeasibility.Auxiliary4

namespace CompoundFeasibility.Auxiliary4
open SourceMultiblock4
variable {𝕂 : Type*} [Field 𝕂] [CharZero 𝕂]

theorem rothSource_scaled_chart_pderiv {m : ℕ} (a : Fin 4 → 𝕂) (k j : Fin 4)
    (h : Fin m) (hj : j ≠ k) (v : Vars4 m) :
    MvPolynomial.pderiv (h,j) (chart4 a k v) =
      MvPolynomial.C (a k) * (if v = (h,j) then 1 else 0) -
        MvPolynomial.C (a j) * (if v = (h,k) then 1 else 0) := by
  classical
  rcases v with ⟨g,l⟩
  by_cases hg : g = h
  · subst g
    by_cases hl : l = k
    · subst l
      simp [chart4, MvPolynomial.pderiv_C_mul, MvPolynomial.pderiv_X,
        Pi.single_apply, Prod.mk.injEq, hj, Ne.symm hj, map_sum, mul_ite,
        Finset.sum_ite_eq', Finset.sum_ite_eq, eq_comm]
    · simp [chart4, hl, MvPolynomial.pderiv_C_mul, MvPolynomial.pderiv_X,
        Pi.single_apply, Prod.mk.injEq, hl, Ne.symm hl, eq_comm]
  · by_cases hl : l = k <;>
      simp [chart4, hl, MvPolynomial.pderiv_C_mul, MvPolynomial.pderiv_X,
        Pi.single_apply, Prod.mk.injEq, hg, Ne.symm hg, map_sum]

theorem rothSource_scaled_chain {m : ℕ} (a : Fin 4 → 𝕂) (k j : Fin 4)
    (h : Fin m) (hj : j ≠ k) (P : MvPolynomial (Vars4 m) 𝕂) :
    MvPolynomial.pderiv (h,j) (substitute4 a k P) =
      MvPolynomial.C (a k) * substitute4 a k (MvPolynomial.pderiv (h,j) P) -
        MvPolynomial.C (a j) * substitute4 a k (MvPolynomial.pderiv (h,k) P) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C c => simp [substitute4]
  | add P Q hP hQ => simp only [map_add, hP, hQ]; ring
  | mul_X P v hP =>
    simp only [map_mul, MvPolynomial.pderiv_mul, map_add, hP]
    rw [show substitute4 a k (MvPolynomial.X v) = chart4 a k v by simp [substitute4],
      rothSource_scaled_chart_pderiv a k j h hj v]
    simp only [MvPolynomial.pderiv_X, Pi.single_apply, apply_ite, map_one, map_zero]
    split_ifs <;> simp_all <;> ring

theorem rothSource_weight_add {m : ℕ} (r : Fin m → ℕ) (J K : Vars4 m →₀ ℕ) :
    rothSourceDerivativeWeight r (J + K) =
      rothSourceDerivativeWeight r J + rothSourceDerivativeWeight r K := by
  simp [rothSourceDerivativeWeight, Finsupp.add_apply, Nat.cast_add,
    Finset.sum_add_distrib, add_div]

theorem rothSource_weight_mono {m : ℕ} (r : Fin m → ℕ)
    (J K : Vars4 m →₀ ℕ) (hJK : J ≤ K) :
    rothSourceDerivativeWeight r J ≤ rothSourceDerivativeWeight r K := by
  apply Finset.sum_le_sum
  intro h _
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply Finset.sum_le_sum
  intro i _
  exact_mod_cast hJK (h,i)

theorem rothSource_weight_single {m : ℕ} (r : Fin m → ℕ) (u : Vars4 m) :
    rothSourceDerivativeWeight r (Finsupp.single u 1) = 1 / (r u.1 : ℝ) := by
  classical
  rcases u with ⟨h,j⟩
  simp [rothSourceDerivativeWeight, Finsupp.single_apply, Prod.mk.injEq, ite_and,
    Finset.sum_ite_eq, Finset.sum_ite_eq']
  simp [ite_div, Finset.sum_ite_eq', Finset.sum_ite_eq]

theorem rothSource_weight_pivot {m : ℕ} (r : Fin m → ℕ) (k : Fin 4) (i : Fin m → ℕ) :
    rothSourceDerivativeWeight r (pivotDerivative4 k i) = ∑ h, (i h : ℝ) / r h := by
  simp [rothSourceDerivativeWeight, pivotDerivative4, Finset.sum_ite_eq,
    Finset.sum_ite_eq']

noncomputable def rothSourceFreeOrder {m : ℕ} (k : Fin 4) (J : Vars4 m →₀ ℕ) : ℕ :=
  ∑ u ∈ Finset.univ.filter (fun u : Vars4 m => u.2 ≠ k), J u

theorem rothSource_free_add {m : ℕ} (k : Fin 4) (J K : Vars4 m →₀ ℕ) :
    rothSourceFreeOrder k (J + K) = rothSourceFreeOrder k J + rothSourceFreeOrder k K := by
  simp [rothSourceFreeOrder, Finsupp.add_apply, Finset.sum_add_distrib]

theorem rothSource_free_single {m : ℕ} (k : Fin 4) (u : Vars4 m) :
    rothSourceFreeOrder k (Finsupp.single u 1) = if u.2 = k then 0 else 1 := by
  classical
  simp [rothSourceFreeOrder, Finsupp.single_apply, Finset.sum_ite_eq', Finset.sum_ite_eq]

theorem rothSource_free_zero_pivot {m : ℕ} (k : Fin 4) (J : Vars4 m →₀ ℕ)
    (hJ : rothSourceFreeOrder k J = 0) :
    J = pivotDerivative4 k (fun h => J (h,k)) := by
  classical
  ext u
  by_cases hu : u.2 = k
  · have he : u = (u.1,k) := Prod.ext rfl hu
    simpa [pivotDerivative4, hu] using congrArg J he
  · have hle : J u ≤ rothSourceFreeOrder k J :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_filter.mpr ⟨Finset.mem_univ u,hu⟩)
    have hz : J u = 0 := by omega
    simp [pivotDerivative4, hu, hz]

theorem rothSource_scaled_mixed_vanishing {m : ℕ} (r : Fin m → ℕ)
    (a : Fin 4 → 𝕂) (k : Fin 4) (ha : a k ≠ 0) (T : ℝ)
    (P : MvPolynomial (Vars4 m) 𝕂)
    (hpivot : ∀ i : Fin m → ℕ, (∑ h, (i h : ℝ) / r h) < T →
      substitute4 a k
        (derivative4 (pivotDerivative4 k i) P) = 0)
    (J : Vars4 m →₀ ℕ) (hw : rothSourceDerivativeWeight r J < T) :
    substitute4 a k (derivative4 J P) = 0 := by
  classical
  have go : ∀ n : ℕ, ∀ J : Vars4 m →₀ ℕ,
      rothSourceFreeOrder k J = n → rothSourceDerivativeWeight r J < T →
      substitute4 a k (derivative4 J P) = 0 := by
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
      · have hex : ∃ u : Vars4 m, u.2 ≠ k ∧ J u ≠ 0 := by
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
        change substitute4 a k
          (derivative4 (K + Finsupp.single (u.1,k) 1) P) = 0 at hKp
        have hc := rothSource_scaled_chain a k u.2 u.1 hu
          (derivative4 K P)
        rw [SourceMultiblock4.source4_pderiv_hasse, SourceMultiblock4.source4_pderiv_hasse] at hc
        simp only [hK, map_zero, map_nsmul, hKp, nsmul_zero, mul_zero, sub_zero] at hc
        rw [hKeq] at hc
        have hcoeff : (MvPolynomial.C (a k) : MvPolynomial (Vars4 m) 𝕂) ≠ 0 := by
          intro hz
          apply ha
          apply MvPolynomial.C_injective (σ := Vars4 m)
          simpa only [map_zero] using hz
        have hsm := (mul_eq_zero.mp hc.symm).resolve_left hcoeff
        rw [nsmul_eq_mul] at hsm
        exact (mul_eq_zero.mp hsm).resolve_left (by
          intro hh
          have hz : ((K (u.1,u.2) + 1 : ℕ) : 𝕂) = 0 := by
            apply MvPolynomial.C_injective (σ := Vars4 m)
            simpa only [map_natCast, map_zero] using hh
          exact (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero _)) hz)
  exact go _ J rfl hw


end CompoundFeasibility.Auxiliary4

namespace CompoundFeasibility.Auxiliary4
open SourceMultiblock4
variable {𝕂 : Type*} [Field 𝕂] [CharZero 𝕂]

def kernelChart4 {m : ℕ} (a : Fin 4 → 𝕂) (k : Fin m → Fin 4)
    (u : Vars4 m) : MvPolynomial (Vars4 m) 𝕂 :=
  if u.2 = k u.1 then
    -(∑ j ∈ Finset.univ.erase (k u.1),
      MvPolynomial.C (a j / a (k u.1)) * MvPolynomial.X (u.1,j))
  else MvPolynomial.X u

def kernelRestriction4 {m : ℕ} (a : Fin 4 → 𝕂) (k : Fin m → Fin 4) :
    MvPolynomial (Vars4 m) 𝕂 →+* MvPolynomial (Vars4 m) 𝕂 :=
  MvPolynomial.eval₂Hom MvPolynomial.C (kernelChart4 a k)

theorem kernelChart4_form {m : ℕ} (a : Fin 4 → 𝕂)
    (k : Fin m → Fin 4) (hk : ∀ h, a (k h) ≠ 0) (h : Fin m) :
    (∑ j : Fin 4, MvPolynomial.C (a j) * kernelChart4 a k (h,j)) = 0 := by
  rw [← Finset.sum_erase_add Finset.univ _ (Finset.mem_univ (k h))]
  have hfree : (∑ j ∈ Finset.univ.erase (k h), MvPolynomial.C (a j) *
      kernelChart4 a k (h,j)) =
      ∑ j ∈ Finset.univ.erase (k h), MvPolynomial.C (a j) * MvPolynomial.X (h,j) := by
    apply Finset.sum_congr rfl
    intro j hj
    simp [kernelChart4, (Finset.mem_erase.mp hj).1]
  rw [hfree]
  have hpivot : MvPolynomial.C (a (k h)) * kernelChart4 a k (h,k h) =
      -(∑ j ∈ Finset.univ.erase (k h), MvPolynomial.C (a j) * MvPolynomial.X (h,j)) := by
    simp only [kernelChart4, Prod.fst, Prod.snd, if_pos rfl, ite_true, mul_neg, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    rw [← mul_assoc, ← MvPolynomial.C_mul]
    congr 1
    field_simp [hk h]
  rw [hpivot]
  ring

def chartTransport4 {m : ℕ} (a : Fin 4 → 𝕂) (p : Fin 4) (k : Fin m → Fin 4) :
    MvPolynomial (Vars4 m) 𝕂 →+* MvPolynomial (Vars4 m) 𝕂 :=
  MvPolynomial.eval₂Hom MvPolynomial.C (fun u =>
    MvPolynomial.C ((a p)⁻¹) * kernelChart4 a k u)

theorem chartTransport4_variable {m : ℕ} (a : Fin 4 → 𝕂)
    (p : Fin 4) (hp : a p ≠ 0) (k : Fin m → Fin 4)
    (hk : ∀ h, a (k h) ≠ 0) (u : Vars4 m) :
    chartTransport4 a p k (chart4 a p u) = kernelChart4 a k u := by
  have hcancel : (MvPolynomial.C (a p) : MvPolynomial (Vars4 m) 𝕂) *
      MvPolynomial.C ((a p)⁻¹) = 1 := by
    rw [← MvPolynomial.C_mul, mul_inv_cancel₀ hp, map_one]
  by_cases hu : u.2 = p
  · have hsum := kernelChart4_form a k hk u.1
    rw [← Finset.sum_erase_add Finset.univ _ (Finset.mem_univ p)] at hsum
    have hrel : -(∑ j ∈ Finset.univ.erase p, MvPolynomial.C (a j) *
        kernelChart4 a k (u.1,j)) =
        MvPolynomial.C (a p) * kernelChart4 a k (u.1,p) := by
      linear_combination -hsum
    simp only [chart4, if_pos hu, map_neg, map_sum, map_mul]
    simp only [chartTransport4, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X']
    calc
      _ = MvPolynomial.C ((a p)⁻¹) *
          -(∑ j ∈ Finset.univ.erase p, MvPolynomial.C (a j) *
            kernelChart4 a k (u.1,j)) := by
        rw [mul_neg, Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = _ := by
        rw [hrel, ← mul_assoc, mul_comm _ (MvPolynomial.C (a p)), hcancel]
        simp [← hu]
  · simp only [chart4, if_neg hu, map_mul]
    simp only [chartTransport4, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X']
    rw [← mul_assoc, hcancel, one_mul]

theorem chartTransport4_substitute {m : ℕ} (a : Fin 4 → 𝕂)
    (p : Fin 4) (hp : a p ≠ 0) (k : Fin m → Fin 4)
    (hk : ∀ h, a (k h) ≠ 0) (P : MvPolynomial (Vars4 m) 𝕂) :
    chartTransport4 a p k (substitute4 a p P) = kernelRestriction4 a k P := by
  have he : (chartTransport4 a p k).comp (substitute4 a p) = kernelRestriction4 a k := by
    apply MvPolynomial.ringHom_ext
    · intro z
      simp [substitute4, chartTransport4, kernelRestriction4]
    · intro u
      simpa [substitute4, kernelRestriction4] using chartTransport4_variable a p hp k hk u
  exact congrArg (fun f => f P) he

theorem derivative4_zero_of_block_excess {m : ℕ} (r : Fin m → ℕ)
    (P : MvPolynomial (Vars4 m) 𝕂) (hP : homogeneous4 r P)
    (J : Vars4 m →₀ ℕ) (h : Fin m) (hJ : r h < ∑ j : Fin 4, J (h,j)) :
    derivative4 J P = 0 := by
  apply MvPolynomial.ext
  intro d
  rw [derivative4_coeff, MvPolynomial.coeff_zero]
  have hz : P.coeff (d + J) = 0 := by
    by_contra hn
    have hdegree := hP (d + J) (MvPolynomial.mem_support_iff.mpr hn) h
    have hle : (∑ j : Fin 4, J (h,j)) ≤ ∑ j : Fin 4, (d + J) (h,j) := by
      apply Finset.sum_le_sum
      intro j _
      simp only [Finsupp.add_apply]
      omega
    omega
  rw [hz, zero_mul]

theorem matrix4_kernel_all_derivatives {m : ℕ} (r : Fin m → ℕ) (eta : ℝ)
    (a : Fin 3 → Fin 4 → Fin 4 → 𝕂) (p : Fin 3 → Fin 4 → Fin 4)
    (hp : ∀ tau s, a tau s (p tau s) ≠ 0)
    (c : RothAuxCoefficients r → 𝕂)
    (hc : (matrix4 r eta a p).mulVec c = 0)
    (tau : Fin 3) (s : Fin 4) (J : Vars4 m →₀ ℕ)
    (hJ : rothSourceDerivativeWeight r J < (1 / 4 - eta) * m)
    (k : Fin m → Fin 4) (hk : ∀ h, a tau s (k h) ≠ 0) :
    kernelRestriction4 (a tau s) k (derivative4 J (polynomial4 c)) = 0 := by
  have hpivot := (matrix4_kernel_iff_restrictions r eta a p c).mp hc
  have hall : ∀ i : Fin m → ℕ, (∑ h, (i h : ℝ) / r h) < (1 / 4 - eta) * m →
      substitute4 (a tau s) (p tau s)
        (derivative4 (pivotDerivative4 (p tau s) i) (polynomial4 c)) = 0 := by
    intro i hi
    by_cases hb : ∀ h, i h ≤ r h
    · let iFin : RothAuxPivots r := fun h => ⟨i h, by have hh := hb h; omega⟩
      exact hpivot tau s ⟨iFin, hi⟩
    · push_neg at hb
      obtain ⟨h, hh⟩ := hb
      have hsum : (∑ j : Fin 4, pivotDerivative4 (p tau s) i (h,j)) = i h := by
        simp [pivotDerivative4, Finset.sum_ite_eq, Finset.sum_ite_eq']
      have hz := derivative4_zero_of_block_excess r (polynomial4 c) (polynomial4_homogeneous c)
        (pivotDerivative4 (p tau s) i) h (by rw [hsum]; exact hh)
      simp [hz]
  rw [← chartTransport4_substitute (a tau s) (p tau s) (hp tau s) k hk]
  rw [rothSource_scaled_mixed_vanishing r (a tau s) (p tau s) (hp tau s) _
    (polynomial4 c) hall J hJ, map_zero]

end CompoundFeasibility.Auxiliary4
namespace CompoundFeasibility.Auxiliary4
open SourceMultiblock4
variable {R S : Type*} [CommRing R] [CommRing S]

theorem derivative4_map {m : ℕ} (f : R →+* S) (J : Vars4 m →₀ ℕ)
    (P : MvPolynomial (Vars4 m) R) :
    (derivative4 J P).map f = derivative4 J (P.map f) := by
  apply MvPolynomial.ext
  intro d
  simp only [MvPolynomial.coeff_map, derivative4_coeff, map_mul, map_prod, map_natCast]

theorem chart4_map {m : ℕ} (f : R →+* S) (a : Fin 4 → R) (k : Fin 4) (u : Vars4 m) :
    (chart4 a k u).map f = chart4 (fun j => f (a j)) k u := by
  unfold chart4
  split_ifs <;> simp [map_sum, map_mul]

theorem substitute4_map {m : ℕ} (f : R →+* S) (a : Fin 4 → R) (k : Fin 4)
    (P : MvPolynomial (Vars4 m) R) :
    (substitute4 a k P).map f = substitute4 (fun j => f (a j)) k (P.map f) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [substitute4]
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P v hP =>
    simp only [map_mul, hP]
    rw [show substitute4 a k (MvPolynomial.X v) = chart4 a k v by simp [substitute4]]
    rw [chart4_map]
    simp [substitute4]

theorem polynomial4_map {m : ℕ} {r : Fin m → ℕ} (f : R →+* S)
    (c : RothAuxCoefficients r → R) :
    (polynomial4 c).map f = polynomial4 (fun b => f (c b)) := by
  simp [polynomial4]

theorem matrix4_map {m : ℕ} (f : R →+* S) (r : Fin m → ℕ) (eta : ℝ)
    (a : Fin 3 → Fin 4 → Fin 4 → R) (p : Fin 3 → Fin 4 → Fin 4)
    (q : Equations4 r eta) (b : RothAuxCoefficients r) :
    f (matrix4 r eta a p q b) = matrix4 r eta (fun tau s j => f (a tau s j)) p q b := by
  unfold matrix4 equation4
  rw [← MvPolynomial.coeff_map, substitute4_map, derivative4_map]
  simp

end CompoundFeasibility.Auxiliary4
