import SubspaceBridge.NormalIndex10
import SubspaceBridge.SourceMultiblock10
import Mathlib.Algebra.MvPolynomial.Funext
open scoped BigOperators Classical Matrix
namespace CompoundFeasibility.SourceNormalHighIndex10
open SourceMultiblock10 SchmidtNormal10
noncomputable section
variable {K : Type*} [Field K]

def homogeneous10 {m : ℕ} {R : Type*} [CommRing R] (r : Fin m → ℕ) (P : MvPolynomial (SourceMultiblock10.Vars10 m) R) : Prop :=
  ∀ d ∈ P.support, ∀ h, ∑ j : Fin 10, d (h,j) = r h

noncomputable def rothSourceDerivativeWeight {m : ℕ} (r : Fin m → ℕ)
    (J : SourceMultiblock10.Vars10 m →₀ ℕ) : ℝ := ∑ h, (∑ i : Fin 10, (J (h,i) : ℝ))/(r h : ℝ)

theorem rothSource_weight_add {m : ℕ} (r : Fin m → ℕ) (J K : SourceMultiblock10.Vars10 m →₀ ℕ) :
    rothSourceDerivativeWeight r (J + K) =
      rothSourceDerivativeWeight r J + rothSourceDerivativeWeight r K := by
  simp [rothSourceDerivativeWeight, Finsupp.add_apply, Nat.cast_add,
    Finset.sum_add_distrib, add_div]

theorem rothSource_weight_single {m : ℕ} (r : Fin m → ℕ) (u : SourceMultiblock10.Vars10 m) :
    rothSourceDerivativeWeight r (Finsupp.single u 1) = 1 / (r u.1 : ℝ) := by
  classical
  rcases u with ⟨h,j⟩
  simp [rothSourceDerivativeWeight, Finsupp.single_apply, Prod.mk.injEq, ite_and,
    Finset.sum_ite_eq, Finset.sum_ite_eq']
  simp [ite_div, Finset.sum_ite_eq', Finset.sum_ite_eq]

theorem derivative10_map {R S : Type*} [CommRing R] [CommRing S] {m : ℕ} (f : R →+* S) (J : SourceMultiblock10.Vars10 m →₀ ℕ)
    (P : MvPolynomial (SourceMultiblock10.Vars10 m) R) :
    (derivative10 J P).map f = derivative10 J (P.map f) := by
  apply MvPolynomial.ext
  intro d
  simp only [MvPolynomial.coeff_map, derivative10_coeff, map_mul, map_prod, map_natCast]

def integerValue {m : ℕ} (J : SourceMultiblock10.Vars10 m →₀ ℕ) (P : MvPolynomial (SourceMultiblock10.Vars10 m) ℤ)
    (v : Fin m → Fin 10 → ℤ) : ℤ :=
  MvPolynomial.eval (fun u => v u.1 u.2) (derivative10 J P)

theorem integerValue_cast {K : Type*} [CommRing K] {m : ℕ}
    (J : SourceMultiblock10.Vars10 m →₀ ℕ) (P : MvPolynomial (SourceMultiblock10.Vars10 m) ℤ) (v : Fin m → Fin 10 → ℤ) :
    (integerValue J P v : K) = MvPolynomial.eval (fun u => (v u.1 u.2 : K))
      (derivative10 J (P.map (Int.castRingHom K))) := by
  rw [← derivative10_map, MvPolynomial.eval_map]
  exact MvPolynomial.eval₂_comp (Int.castRingHom K) _ _

def gridPoint {m : ℕ} (w : Fin m → Fin 9 → Fin 10 → ℤ)
    (a : Fin m → Fin 9 → ℕ) : Fin m → Fin 10 → ℤ := fun h i => ∑ j, (a h j : ℤ)*w h j i

theorem pderiv_coeff {m : ℕ} (u : SourceMultiblock10.Vars10 m)
    (Q : MvPolynomial (SourceMultiblock10.Vars10 m) K) (b : SourceMultiblock10.Vars10 m →₀ ℕ) :
    (MvPolynomial.pderiv u Q).coeff b =
      (b u + 1 : ℕ) * Q.coeff (b + Finsupp.single u 1) := by
  classical
  induction Q using MvPolynomial.induction_on' with
  | add P Q hP hQ => simp only [map_add, MvPolynomial.coeff_add, hP, hQ]; ring
  | monomial a c =>
    by_cases ha : a u = 0
    · have hab : a ≠ b + Finsupp.single u 1 := by
        intro he
        have h := congrArg (fun d : SourceMultiblock10.Vars10 m →₀ ℕ => d u) he
        simp [ha, Finsupp.add_apply, Finsupp.single_apply] at h
      simp [MvPolynomial.pderiv_monomial, ha, MvPolynomial.coeff_monomial, hab]
    · have hle : Finsupp.single u 1 ≤ a := by rw [Finsupp.single_le_iff]; omega
      have heq : a - Finsupp.single u 1 = b ↔ a = b + Finsupp.single u 1 := by
        constructor
        · intro he
          rw [← he]
          exact (tsub_add_cancel_of_le hle).symm
        · intro he
          rw [he, add_tsub_cancel_right]
      simp only [MvPolynomial.pderiv_monomial, MvPolynomial.coeff_monomial, heq]
      split_ifs with he
      · subst a
        simp only [Finsupp.add_apply, Finsupp.single_eq_same, Nat.cast_add, Nat.cast_one]
        ring
      · simp

theorem hermite_sizes10 (eta : ℝ) (heta : 0 < eta) (r : ℕ) (hr : 0 < r) :
    eta⁻¹ < (Nat.floor eta⁻¹+1 : ℕ) ∧
    (r : ℝ)*eta < (Nat.floor ((r : ℝ)*eta)+1 : ℕ) ∧
    (r : ℝ) < (Nat.floor eta⁻¹+1 : ℕ)*(Nat.floor ((r : ℝ)*eta)+1 : ℕ) := by
  have hs := Nat.lt_floor_add_one eta⁻¹
  have ht := Nat.lt_floor_add_one ((r : ℝ)*eta)
  have hs' : eta⁻¹ < ((Nat.floor eta⁻¹+1 : ℕ) : ℝ) := by exact_mod_cast hs
  have ht' : (r : ℝ)*eta < ((Nat.floor ((r : ℝ)*eta)+1 : ℕ) : ℝ) := by exact_mod_cast ht
  refine ⟨hs',ht',?_⟩
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have he : eta⁻¹*((r : ℝ)*eta) = r := by field_simp
  calc
    (r : ℝ) = eta⁻¹*((r : ℝ)*eta) := he.symm
    _ < _ := mul_lt_mul hs' ht'.le (mul_pos hr' heta) (by positivity)

theorem additional_weight10 {m : ℕ} (r : Fin m → ℕ) (hr : ∀ h, 0 < r h)
    (eta : ℝ) (heta : 0 < eta) (K : SourceMultiblock10.Vars10 m →₀ ℕ)
    (hK : ∀ h, (∑ i : Fin 10, K (h,i)) ≤ Nat.floor ((r h : ℝ)*eta)) :
    rothSourceDerivativeWeight r K ≤ (m : ℝ)*eta := by
  unfold rothSourceDerivativeWeight
  calc
    _ ≤ ∑ h : Fin m, eta := by
      apply Finset.sum_le_sum
      intro h _
      apply (div_le_iff₀ (show (0 : ℝ) < r h by exact_mod_cast hr h)).mpr
      have hk : (∑ i : Fin 10, (K (h,i) : ℝ)) ≤ (Nat.floor ((r h : ℝ)*eta) : ℝ) := by
        exact_mod_cast hK h
      exact hk.trans (by simpa [mul_comm] using Nat.floor_le (le_of_lt (mul_pos (by exact_mod_cast hr h) heta)))
    _ = _ := by simp

theorem additional_cutoff10 {m : ℕ} (r : Fin m → ℕ) (hr : ∀ h, 0 < r h)
    (eta : ℝ) (heta : 0 < eta) (J K : SourceMultiblock10.Vars10 m →₀ ℕ)
    (hJ : rothSourceDerivativeWeight r J < (m : ℝ)*eta)
    (hK : ∀ h, (∑ i : Fin 10, K (h,i)) ≤ Nat.floor ((r h : ℝ)*eta)) :
    rothSourceDerivativeWeight r (K+J) < 2*eta*m := by
  rw [rothSource_weight_add]
  have hk := additional_weight10 r hr eta heta K hK
  nlinarith

theorem hasse_grid_composition10 {m : ℕ} (P : MvPolynomial (SourceMultiblock10.Vars10 m) ℤ)
    (J K : SourceMultiblock10.Vars10 m →₀ ℕ) (x : Fin m → Fin 10 → ℤ)
    (hz : integerValue (K+J) P x = 0) :
    integerValue K (derivative10 J P) x = 0 := by
  apply Int.cast_injective (α := ℚ)
  rw [Int.cast_zero,integerValue_cast,derivative10_map,source10_derivative_comp]
  rw [MvPolynomial.smul_eq_C_mul,map_mul,MvPolynomial.eval_C,← integerValue_cast, hz]
  simp


theorem homogeneous10_map {R : Type*} [CommRing R] (f : R →+* K) {m : ℕ}
    (r : Fin m → ℕ) (P : MvPolynomial (SourceMultiblock10.Vars10 m) R) (hP : homogeneous10 r P) :
    homogeneous10 r (P.map f) := by
  intro d hd h
  have hn : P.coeff d ≠ 0 := by
    intro hz
    have hn := MvPolynomial.mem_support_iff.mp hd
    apply hn
    rw [MvPolynomial.coeff_map,hz,map_zero]
  exact hP d (MvPolynomial.mem_support_iff.mpr hn) h

theorem integer_grid_rational_restriction10 {m : ℕ} (r : Fin m → ℕ) (hr : ∀ h, 0 < r h)
    (P : MvPolynomial (SourceMultiblock10.Vars10 m) ℤ) (hP : homogeneous10 r P) (J : SourceMultiblock10.Vars10 m →₀ ℕ)
    (w : Fin m → Fin 9 → Fin 10 → ℤ) (eta : ℝ) (heta : 0 < eta)
    (hgrid : ∀ a : Fin m → Fin 9 → ℕ, (∀ h j, 1 ≤ a h j ∧ a h j ≤ Nat.floor eta⁻¹+1) →
      ∀ B : SourceMultiblock10.Vars10 m →₀ ℕ, (∀ h, (∑ i : Fin 10, B (h,i)) ≤ Nat.floor ((r h : ℝ)*eta)) →
      integerValue B (derivative10 J P) (gridPoint w a) = 0) :
    ∀ y : Fin m → Fin 10 → ℚ,
      (∀ h, y h ∈ Submodule.span ℚ (Set.range (fun j i => (w h j i : ℚ)))) →
      MvPolynomial.eval (fun u => y u.1 u.2) (derivative10 J (P.map (Int.castRingHom ℚ))) = 0 := by
  classical
  let N := Nat.floor eta⁻¹+1
  let S : Fin m → Fin 9 → Finset ℚ := fun _ _ => (Finset.Icc 1 N).image (fun n : ℕ => (n : ℚ))
  have hcard : ∀ h j, (S h j).card = N := by
    intro h j
    dsimp [S]
    rw [Finset.card_image_of_injective _ (Nat.cast_injective)]
    simp
  have hdeg : ∀ d ∈ (derivative10 J (P.map (Int.castRingHom ℚ))).support, ∀ h,
      (∑ i : Fin 10, d (h,i)) ≤ r h :=
    derivative10_block_degree_bound r _ (fun d hd h => (homogeneous10_map _ r P hP d hd h).le) J
  have hsize : ∀ h, r h < N*(Nat.floor ((r h : ℝ)*eta)+1) := by
    intro h
    have he := (hermite_sizes10 eta heta (r h) (hr h)).2.2
    exact_mod_cast he
  apply multiblock_span_hermite10 _ (fun h j i => (w h j i : ℚ)) S (fun _ => N)
    (fun h => Nat.floor ((r h : ℝ)*eta)) r hcard hdeg hsize
  intro a ha B hB
  have hex : ∀ h j, ∃ n : ℕ, n ∈ Finset.Icc 1 N ∧ (n : ℚ) = a h j := by
    intro h j
    exact Finset.mem_image.mp (ha h j)
  choose n hn hna using hex
  have hn' : ∀ h j, 1 ≤ n h j ∧ n h j ≤ Nat.floor eta⁻¹+1 := by
    intro h j
    exact Finset.mem_Icc.mp (hn h j)
  have hz := congrArg (fun z : ℤ => (z : ℚ)) (hgrid n hn' B hB)
  change (integerValue B (derivative10 J P) (gridPoint w n) : ℚ) = 0 at hz
  rw [integerValue_cast,derivative10_map] at hz
  have he : blockFramePoint10 (fun h j i => (w h j i : ℚ)) a =
      (fun u : SourceMultiblock10.Vars10 m => (gridPoint w n u.1 u.2 : ℚ)) := by
    funext u
    rcases u with ⟨h,i⟩
    simp only [blockFramePoint10,gridPoint,Int.cast_sum,Int.cast_mul,Int.cast_natCast]
    apply Finset.sum_congr rfl
    intro j _
    rw [hna h j]
  rw [he]
  exact hz


theorem integer_grid_real_restriction10 {m : ℕ} (r : Fin m → ℕ) (hr : ∀ h, 0 < r h)
    (P : MvPolynomial (SourceMultiblock10.Vars10 m) ℤ) (hP : homogeneous10 r P) (J : SourceMultiblock10.Vars10 m →₀ ℕ)
    (w : Fin m → Fin 9 → Fin 10 → ℤ) (eta : ℝ) (heta : 0 < eta)
    (hgrid : ∀ a : Fin m → Fin 9 → ℕ, (∀ h j, 1 ≤ a h j ∧ a h j ≤ Nat.floor eta⁻¹+1) →
      ∀ B : SourceMultiblock10.Vars10 m →₀ ℕ, (∀ h, (∑ i : Fin 10, B (h,i)) ≤ Nat.floor ((r h : ℝ)*eta)) →
      integerValue B (derivative10 J P) (gridPoint w a) = 0) :
    ∀ y : Fin m → Fin 10 → ℝ,
      (∀ h, y h ∈ Submodule.span ℝ (Set.range (fun j i => (w h j i : ℝ)))) →
      MvPolynomial.eval (fun u => y u.1 u.2) (derivative10 J (P.map (Int.castRingHom ℝ))) = 0 := by
  classical
  let N := Nat.floor eta⁻¹+1
  let S : Fin m → Fin 9 → Finset ℝ := fun _ _ => (Finset.Icc 1 N).image (fun n : ℕ => (n : ℝ))
  have hcard : ∀ h j, (S h j).card = N := by
    intro h j
    dsimp [S]
    rw [Finset.card_image_of_injective _ (Nat.cast_injective)]
    simp
  have hdeg : ∀ d ∈ (derivative10 J (P.map (Int.castRingHom ℝ))).support, ∀ h,
      (∑ i : Fin 10, d (h,i)) ≤ r h :=
    derivative10_block_degree_bound r _ (fun d hd h => (homogeneous10_map _ r P hP d hd h).le) J
  have hsize : ∀ h, r h < N*(Nat.floor ((r h : ℝ)*eta)+1) := by
    intro h
    have he := (hermite_sizes10 eta heta (r h) (hr h)).2.2
    exact_mod_cast he
  apply multiblock_span_hermite10 _ (fun h j i => (w h j i : ℝ)) S (fun _ => N)
    (fun h => Nat.floor ((r h : ℝ)*eta)) r hcard hdeg hsize
  intro a ha B hB
  have hex : ∀ h j, ∃ n : ℕ, n ∈ Finset.Icc 1 N ∧ (n : ℝ) = a h j := by
    intro h j
    exact Finset.mem_image.mp (ha h j)
  choose n hn hna using hex
  have hn' : ∀ h j, 1 ≤ n h j ∧ n h j ≤ Nat.floor eta⁻¹+1 := by
    intro h j
    exact Finset.mem_Icc.mp (hn h j)
  have hz := congrArg (fun z : ℤ => (z : ℝ)) (hgrid n hn' B hB)
  have hz0 : ((0 : ℤ) : ℝ) = (0 : ℝ) := by norm_num
  change (integerValue B (derivative10 J P) (gridPoint w n) : ℝ) = ((0 : ℤ) : ℝ) at hz
  rw [hz0] at hz
  rw [integerValue_cast,derivative10_map] at hz
  have he : blockFramePoint10 (fun h j i => (w h j i : ℝ)) a =
      (fun u : SourceMultiblock10.Vars10 m => (gridPoint w n u.1 u.2 : ℝ)) := by
    funext u
    rcases u with ⟨h,i⟩
    simp only [blockFramePoint10,gridPoint,Int.cast_sum,Int.cast_mul,Int.cast_natCast]
    apply Finset.sum_congr rfl
    intro j _
    rw [hna h j]
  rw [he]
  exact hz


noncomputable def zeroNormalCoordinates10 {m : ℕ} (k : Fin m → Fin 10) :
    MvPolynomial (SourceMultiblock10.Vars10 m) K →+* MvPolynomial (SourceMultiblock10.Vars10 m) K :=
  MvPolynomial.eval₂Hom MvPolynomial.C (fun u => if u.2 = k u.1 then 0 else MvPolynomial.X u)

theorem zeroNormalCoordinates10_monomial {m : ℕ} (k : Fin m → Fin 10)
    (b : SourceMultiblock10.Vars10 m →₀ ℕ) (c : K) :
    zeroNormalCoordinates10 k (MvPolynomial.monomial b c) =
      if (∀ h, b (h,k h) = 0) then MvPolynomial.monomial b c else 0 := by
  classical
  rw [zeroNormalCoordinates10, MvPolynomial.eval₂Hom_monomial]
  rw [Finsupp.prod_fintype _ _ (fun _ => by simp)]
  by_cases hb : ∀ h, b (h,k h) = 0
  · rw [if_pos hb, MvPolynomial.monomial_eq]
    congr 1
    rw [Finsupp.prod_fintype _ _ (fun _ => by simp)]
    apply Finset.prod_congr rfl
    intro u _
    by_cases hu : u.2 = k u.1
    · have he : u = (u.1,k u.1) := Prod.ext rfl hu
      have hz : b u = 0 := (congrArg b he).trans (hb u.1)
      simp [hu, hz]
    · simp [hu]
  · rw [if_neg hb]
    push_neg at hb
    obtain ⟨h, hh⟩ := hb
    have hz : (∏ u : SourceMultiblock10.Vars10 m, (if u.2 = k u.1 then 0 else MvPolynomial.X u) ^ b u) =
        (0 : MvPolynomial (SourceMultiblock10.Vars10 m) K) := by
      apply Finset.prod_eq_zero (Finset.mem_univ (h,k h))
      simp [hh]
    rw [hz, mul_zero]

theorem zeroNormalCoordinates10_coeff {m : ℕ} (k : Fin m → Fin 10)
    (Q : MvPolynomial (SourceMultiblock10.Vars10 m) K) (b : SourceMultiblock10.Vars10 m →₀ ℕ) :
    (zeroNormalCoordinates10 k Q).coeff b = if (∀ h, b (h,k h) = 0) then Q.coeff b else 0 := by
  classical
  induction Q using MvPolynomial.induction_on' with
  | monomial a c =>
    rw [zeroNormalCoordinates10_monomial]
    by_cases ha : ∀ h, a (h,k h) = 0
    · rw [if_pos ha]
      by_cases hb : ∀ h, b (h,k h) = 0
      · simp [hb]
      · have hab : a ≠ b := by intro he; subst a; exact hb ha
        simp [hb, hab]
    · rw [if_neg ha]
      by_cases hb : ∀ h, b (h,k h) = 0
      · have hab : a ≠ b := by intro he; subst a; exact ha hb
        simp [hb, hab]
      · simp [hb]
  | add P Q hP hQ =>
    rw [map_add, MvPolynomial.coeff_add, hP, hQ, MvPolynomial.coeff_add]
    split_ifs <;> simp


theorem normal_zero_restriction10 {m : ℕ} (M : Fin m → Fin 10 → ℤ)
    (k : Fin m → Fin 10) (hk : ∀ h, M h (k h) ≠ 0)
    (P : MvPolynomial (SourceMultiblock10.Vars10 m) ℝ)
    (hzero : ∀ y : Fin m → Fin 10 → ℝ,
      (∀ h, y h ∈ LinearMap.ker (realNormalForm10 (M h))) →
      MvPolynomial.eval (fun u => y u.1 u.2) P = 0) :
    zeroNormalCoordinates10 k (inverse10 M k P) = 0 := by
  classical
  apply MvPolynomial.funext
  intro z
  let H := (zeroNormalCoordinates10 (K := ℝ) k).comp (inverse10 M k)
  let y : Fin m → Fin 10 → ℝ := fun h i => MvPolynomial.eval z (H (MvPolynomial.X (h,i)))
  have he : (MvPolynomial.eval z).comp H = MvPolynomial.eval (fun u => y u.1 u.2) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [H,inverse10,zeroNormalCoordinates10]
    · intro u
      simp [y]
  have hker : ∀ h, y h ∈ LinearMap.ker (realNormalForm10 (M h)) := by
    intro h
    have hn := inverse6_forward10 (K := ℝ) M k hk (MvPolynomial.X (h,k h))
    simp only [forward10,MvPolynomial.eval₂Hom_X',Prod.fst,Prod.snd,ite_true] at hn
    have hz := congrArg (fun Q => MvPolynomial.eval z (zeroNormalCoordinates10 k Q)) hn
    simp only [zeroNormalCoordinates10,MvPolynomial.eval₂Hom_X',Prod.fst,Prod.snd,
      ite_true,map_zero] at hz
    have hp := congrArg (fun f : MvPolynomial (SourceMultiblock10.Vars10 m) ℝ →+* ℝ => f (linearNormal10 (K := ℝ) M h)) he
    change MvPolynomial.eval z (H (linearNormal10 (K := ℝ) M h)) = _ at hp
    change MvPolynomial.eval z (H (linearNormal10 (K := ℝ) M h)) = 0 at hz
    rw [hp] at hz
    simpa [LinearMap.mem_ker,realNormalForm10,linearNormal10,map_sum,map_mul,y] using hz
  have hp := congrArg (fun f : MvPolynomial (SourceMultiblock10.Vars10 m) ℝ →+* ℝ => f P) he
  change MvPolynomial.eval z (zeroNormalCoordinates10 k (inverse10 M k P)) =
    MvPolynomial.eval (fun u => y u.1 u.2) P at hp
  rw [hp,hzero y hker,map_zero]

theorem inverse10_pderiv_X {m : ℕ} (M : Fin m → Fin 10 → ℤ)
    (k : Fin m → Fin 10) (h : Fin m) (u : SourceMultiblock10.Vars10 m) :
    MvPolynomial.pderiv (h,k h) (inverse10 M k (MvPolynomial.X u)) =
      MvPolynomial.C ((M h (k h) : ℝ)⁻¹) * (if (h,k h) = u then 1 else 0) := by
  classical
  rcases u with ⟨g,i⟩
  by_cases hg : g = h
  · subst g
    by_cases hi : i = k h
    · subst i
      have hs : MvPolynomial.pderiv (h,k h)
          (∑ j ∈ Finset.univ.erase (k h),
            MvPolynomial.C (M h j : ℝ) * MvPolynomial.X (h,j)) = 0 := by
        rw [map_sum]
        apply Finset.sum_eq_zero
        intro j hj
        simp [MvPolynomial.pderiv_C_mul,MvPolynomial.pderiv_X,Pi.single_apply,
          Prod.mk.injEq,Ne.symm (Finset.mem_erase.mp hj).1]
      simp only [inverse10,MvPolynomial.eval₂Hom_X',Prod.fst,Prod.snd,ite_true,
        MvPolynomial.pderiv_C_mul,map_sub,hs,MvPolynomial.pderiv_X,Pi.single_eq_same]
      simp
    · simp [inverse10,hi,MvPolynomial.pderiv_X,Pi.single_apply,Prod.mk.injEq,Ne.symm hi]
  · by_cases hi : i = k g <;>
      simp [inverse10,hi,MvPolynomial.pderiv_C_mul,MvPolynomial.pderiv_X,map_sum,
        Pi.single_apply,Prod.mk.injEq,hg,Ne.symm hg]

theorem inverse10_chain {m : ℕ} (M : Fin m → Fin 10 → ℤ)
    (k : Fin m → Fin 10) (h : Fin m) (P : MvPolynomial (SourceMultiblock10.Vars10 m) ℝ) :
    MvPolynomial.pderiv (h,k h) (inverse10 M k P) =
      MvPolynomial.C ((M h (k h) : ℝ)⁻¹) * inverse10 M k (MvPolynomial.pderiv (h,k h) P) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C c => simp [inverse10]
  | add P Q hP hQ => simp only [map_add,hP,hQ,mul_add]
  | mul_X P u hP =>
    rw [map_mul,MvPolynomial.pderiv_mul,hP,inverse10_pderiv_X,
      MvPolynomial.pderiv_mul,map_add,map_mul,MvPolynomial.pderiv_X]
    simp only [Pi.single_apply,apply_ite,map_one,map_zero]
    by_cases hu : u = (h,k h)
    · subst u
      simp
      ring
    · simp [hu,Ne.symm hu]
      ring

def normalCoordinateWeight10 {m : ℕ} (r : Fin m → ℕ) (k : Fin m → Fin 10)
    (b : SourceMultiblock10.Vars10 m →₀ ℕ) : ℝ := ∑ h, (b (h,k h) : ℝ) / r h

theorem normalCoordinateWeight10_add {m : ℕ} (r : Fin m → ℕ) (k : Fin m → Fin 10)
    (b c : SourceMultiblock10.Vars10 m →₀ ℕ) :
    normalCoordinateWeight10 r k (b+c) = normalCoordinateWeight10 r k b + normalCoordinateWeight10 r k c := by
  simp [normalCoordinateWeight10,Finsupp.add_apply,Nat.cast_add,add_div,Finset.sum_add_distrib]

theorem normalCoordinateWeight10_single {m : ℕ} (r : Fin m → ℕ) (k : Fin m → Fin 10) (h : Fin m) :
    normalCoordinateWeight10 r k (Finsupp.single (h,k h) 1) = 1/(r h : ℝ) := by
  have he (g : Fin m) : (Finsupp.single (h,k h) 1 : SourceMultiblock10.Vars10 m →₀ ℕ) (g,k g) =
      if g = h then 1 else 0 := by
    by_cases hg : g = h
    · subst g; simp
    · simp [Finsupp.single_apply,Prod.mk.injEq,Ne.symm hg,hg]
  simp only [normalCoordinateWeight10]
  simp_rw [he]
  simp [ite_div,Finset.sum_ite_eq,Finset.sum_ite_eq']

theorem inverse10_coeff_zero {m : ℕ} (M : Fin m → Fin 10 → ℤ)
    (k : Fin m → Fin 10) (hk : ∀ h, M h (k h) ≠ 0)
    (r : Fin m → ℕ) (c : ℝ) (P : MvPolynomial (SourceMultiblock10.Vars10 m) ℝ)
    (hindex : ∀ J : SourceMultiblock10.Vars10 m →₀ ℕ, rothSourceDerivativeWeight r J < c →
      ∀ y : Fin m → Fin 10 → ℝ, (∀ h, y h ∈ LinearMap.ker (realNormalForm10 (M h))) →
        MvPolynomial.eval (fun u => y u.1 u.2) (derivative10 J P) = 0)
    (J b : SourceMultiblock10.Vars10 m →₀ ℕ)
    (hbad : rothSourceDerivativeWeight r J + normalCoordinateWeight10 r k b < c) :
    (inverse10 M k (derivative10 J P)).coeff b = 0 := by
  classical
  have go : ∀ n : ℕ, ∀ J b : SourceMultiblock10.Vars10 m →₀ ℕ,
      (∑ h : Fin m, b (h,k h)) = n →
      rothSourceDerivativeWeight r J + normalCoordinateWeight10 r k b < c →
      (inverse10 M k (derivative10 J P)).coeff b = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro J b hn hw
      by_cases hnzero : n = 0
      · have hbzero : ∀ h, b (h,k h) = 0 := by
          intro h
          have hle : b (h,k h) ≤ ∑ g : Fin m, b (g,k g) :=
            Finset.single_le_sum (f := fun g : Fin m => b (g,k g)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ h)
          omega
        have hnonneg : 0 ≤ normalCoordinateWeight10 r k b := by
          unfold normalCoordinateWeight10
          positivity
        have hJ : rothSourceDerivativeWeight r J < c := by linarith
        have hz := normal_zero_restriction10 M k hk (derivative10 J P) (hindex J hJ)
        have he := congrArg (MvPolynomial.coeff b) hz
        rw [zeroNormalCoordinates10_coeff,if_pos hbzero,MvPolynomial.coeff_zero] at he
        exact he
      · have hex : ∃ h : Fin m, b (h,k h) ≠ 0 := by
          by_contra! hzero
          have hs : (∑ h : Fin m, b (h,k h)) = 0 := Finset.sum_eq_zero (fun h _ => hzero h)
          omega
        obtain ⟨h,hh⟩ := hex
        let d := b - Finsupp.single (h,k h) 1
        have hle : Finsupp.single (h,k h) 1 ≤ b := by rw [Finsupp.single_le_iff]; omega
        have hdeq : d + Finsupp.single (h,k h) 1 = b := tsub_add_cancel_of_le hle
        have hcount : (∑ g : Fin m, d (g,k g)) + 1 = n := by
          have hs := congrArg (fun b : SourceMultiblock10.Vars10 m →₀ ℕ => ∑ g : Fin m, b (g,k g)) hdeq
          have he (g : Fin m) : (Finsupp.single (h,k h) 1 : SourceMultiblock10.Vars10 m →₀ ℕ) (g,k g) =
              if g = h then 1 else 0 := by
            by_cases hg : g = h
            · subst g; simp
            · simp [Finsupp.single_apply,Prod.mk.injEq,Ne.symm hg,hg]
          simp_rw [Finsupp.add_apply,he] at hs
          simpa [Finset.sum_add_distrib,Finset.sum_ite_eq,Finset.sum_ite_eq',hn] using hs
        have hcoord : normalCoordinateWeight10 r k d + 1/(r h : ℝ) = normalCoordinateWeight10 r k b := by
          rw [← normalCoordinateWeight10_single r k h,← normalCoordinateWeight10_add,hdeq]
        have hz : (inverse10 M k (derivative10 (J+Finsupp.single (h,k h) 1) P)).coeff d = 0 := by
          apply ih (∑ g : Fin m, d (g,k g)) (by omega) _ d rfl
          rw [rothSource_weight_add,rothSource_weight_single]
          linarith
        have hd : (MvPolynomial.pderiv (h,k h) (inverse10 M k (derivative10 J P))).coeff d = 0 := by
          rw [inverse10_chain,source10_pderiv_hasse,map_nsmul,
            MvPolynomial.coeff_C_mul,MvPolynomial.coeff_smul,hz,smul_zero,mul_zero]
        rw [pderiv_coeff,hdeq] at hd
        exact (mul_eq_zero.mp hd).resolve_left (Nat.cast_ne_zero.mpr (by omega))
  exact go _ J b rfl hbad

theorem forward10_monomial {m : ℕ} (M : Fin m → Fin 10 → ℤ)
    (k : Fin m → Fin 10) (b : SourceMultiblock10.Vars10 m →₀ ℕ) (a : ℝ) :
    forward10 M k (MvPolynomial.monomial b a) =
      MvPolynomial.C a * ((∏ h, (linearNormal10 (K := ℝ) M h) ^ b (h,k h)) *
        (∏ h, ∏ i ∈ Finset.univ.erase (k h), MvPolynomial.X (h,i) ^ b (h,i))) := by
  classical
  rw [forward10,MvPolynomial.eval₂Hom_monomial]
  rw [Finsupp.prod_fintype _ _ (fun _ => by simp),Fintype.prod_prod_type,
    ← Finset.prod_mul_distrib]
  congr 1
  apply Finset.prod_congr rfl
  intro h hh
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ (k h))]
  simp only [Prod.fst,Prod.snd,ite_true]
  have he : (∏ i ∈ Finset.univ.erase (k h),
      (if i = k h then linearNormal10 (K := ℝ) M h else MvPolynomial.X (h,i)) ^ b (h,i)) =
      ∏ i ∈ Finset.univ.erase (k h), MvPolynomial.X (h,i) ^ b (h,i) := by
    apply Finset.prod_congr rfl
    intro i hi
    rw [if_neg (Finset.mem_erase.mp hi).1]
  rw [he]
  ring

theorem forward10_monomial_mem {m : ℕ} (M : Fin m → Fin 10 → ℤ)
    (k : Fin m → Fin 10) (r : Fin m → ℕ) (c : ℝ)
    (b : SourceMultiblock10.Vars10 m →₀ ℕ) (a : ℝ) (hb : c ≤ normalCoordinateWeight10 r k b) :
    forward10 M k (MvPolynomial.monomial b a) ∈ sourceNormalIdeal10 M r c := by
  have hg : (∏ h, (linearNormal10 (K := ℝ) M h) ^ b (h,k h)) ∈ sourceNormalIdeal10 M r c :=
    Ideal.subset_span ⟨fun h => b (h,k h),hb,rfl⟩
  rw [forward10_monomial]
  have hm := Ideal.mul_mem_left (sourceNormalIdeal10 M r c)
    (MvPolynomial.C a * (∏ h, ∏ i ∈ Finset.univ.erase (k h), MvPolynomial.X (h,i) ^ b (h,i))) hg
  convert hm using 1
  ring

theorem sourceNormalIdeal10_of_derivative_restrictions {m : ℕ}
    (M : Fin m → Fin 10 → ℤ) (hM : ∀ h, M h ≠ 0)
    (r : Fin m → ℕ) (c : ℝ) (P : MvPolynomial (SourceMultiblock10.Vars10 m) ℝ)
    (hindex : ∀ J : SourceMultiblock10.Vars10 m →₀ ℕ, rothSourceDerivativeWeight r J < c →
      ∀ y : Fin m → Fin 10 → ℝ, (∀ h, y h ∈ LinearMap.ker (realNormalForm10 (M h))) →
        MvPolynomial.eval (fun u => y u.1 u.2) (derivative10 J P) = 0) :
    P ∈ sourceNormalIdeal10 M r c := by
  classical
  have hex (h : Fin m) : ∃ i : Fin 10, M h i ≠ 0 := by
    by_contra! hz
    exact hM h (funext hz)
  choose k hk using hex
  have hcoeff (b : SourceMultiblock10.Vars10 m →₀ ℕ) (hb : normalCoordinateWeight10 r k b < c) :
      (inverse10 M k P).coeff b = 0 := by
    have hz := inverse10_coeff_zero M k hk r c P hindex 0 b
      (by simpa [rothSourceDerivativeWeight] using hb)
    simpa only [derivative10_zero_index] using hz
  have hsupport (b) (hb : b ∈ (inverse10 M k P).support) :
      c ≤ normalCoordinateWeight10 r k b := by
    by_contra! hlt
    exact (MvPolynomial.mem_support_iff.mp hb) (hcoeff b hlt)
  have hsum := congrArg (forward10 M k) (inverse10 M k P).as_sum
  rw [forward6_inverse10 M k hk P,map_sum] at hsum
  rw [hsum]
  apply Ideal.sum_mem
  intro b hb
  exact forward10_monomial_mem M k r c b _ (hsupport b hb)

theorem integer_grid_high_normal_index10 {m : ℕ} (r : Fin m → ℕ) (hr : ∀ h, 0 < r h)
    (P : MvPolynomial (SourceMultiblock10.Vars10 m) ℤ) (hP : homogeneous10 r P)
    (w : Fin m → Fin 9 → Fin 10 → ℤ) (M : Fin m → Fin 10 → ℤ)
    (hM : ∀ h, M h ≠ 0)
    (hQ : ∀ h, LinearMap.ker (normalForm10 (M h)) =
      Submodule.span ℚ (Set.range (fun j i => (w h j i : ℚ))))
    (hR : ∀ h, LinearMap.ker (realNormalForm10 (M h)) =
      Submodule.span ℝ (Set.range (fun j i => (w h j i : ℝ))))
    (eta : ℝ) (heta : 0 < eta)
    (hgrid : ∀ a : Fin m → Fin 9 → ℕ, (∀ h j, 1 ≤ a h j ∧ a h j ≤ Nat.floor eta⁻¹+1) →
      ∀ J : SourceMultiblock10.Vars10 m →₀ ℕ, rothSourceDerivativeWeight r J < 2*eta*m →
        integerValue J P (gridPoint w a) = 0) :
    (∀ J : SourceMultiblock10.Vars10 m →₀ ℕ, rothSourceDerivativeWeight r J < (m : ℝ)*eta →
      (∀ y : Fin m → Fin 10 → ℚ, (∀ h, y h ∈ LinearMap.ker (normalForm10 (M h))) →
        MvPolynomial.eval (fun u => y u.1 u.2) (derivative10 J (P.map (Int.castRingHom ℚ))) = 0) ∧
      (∀ y : Fin m → Fin 10 → ℝ, (∀ h, y h ∈ LinearMap.ker (realNormalForm10 (M h))) →
        MvPolynomial.eval (fun u => y u.1 u.2) (derivative10 J (P.map (Int.castRingHom ℝ))) = 0)) ∧
    P.map (Int.castRingHom ℝ) ∈ sourceNormalIdeal10 M r ((m : ℝ)*eta) := by
  have hrestr : ∀ J : SourceMultiblock10.Vars10 m →₀ ℕ, rothSourceDerivativeWeight r J < (m : ℝ)*eta →
      (∀ y : Fin m → Fin 10 → ℚ, (∀ h, y h ∈ LinearMap.ker (normalForm10 (M h))) →
        MvPolynomial.eval (fun u => y u.1 u.2) (derivative10 J (P.map (Int.castRingHom ℚ))) = 0) ∧
      (∀ y : Fin m → Fin 10 → ℝ, (∀ h, y h ∈ LinearMap.ker (realNormalForm10 (M h))) →
        MvPolynomial.eval (fun u => y u.1 u.2) (derivative10 J (P.map (Int.castRingHom ℝ))) = 0) := by
    intro J hJ
    have hc : ∀ a : Fin m → Fin 9 → ℕ, (∀ h j, 1 ≤ a h j ∧ a h j ≤ Nat.floor eta⁻¹+1) →
        ∀ B : SourceMultiblock10.Vars10 m →₀ ℕ, (∀ h, (∑ i : Fin 10, B (h,i)) ≤ Nat.floor ((r h : ℝ)*eta)) →
          integerValue B (derivative10 J P) (gridPoint w a) = 0 := by
      intro a ha B hB
      exact hasse_grid_composition10 P J B _
        (hgrid a ha (B+J) (additional_cutoff10 r hr eta heta J B hJ hB))
    constructor
    · intro y hy
      apply integer_grid_rational_restriction10 r hr P hP J w eta heta hc y
      intro h
      rw [← hQ h]
      exact hy h
    · intro y hy
      exact integer_grid_real_restriction10 r hr P hP J w eta heta hc y
        (fun h => (hR h) ▸ hy h)

  exact ⟨hrestr,sourceNormalIdeal10_of_derivative_restrictions M hM r ((m : ℝ)*eta)
    (P.map (Int.castRingHom ℝ)) (fun J hJ => (hrestr J hJ).2)⟩




end
end CompoundFeasibility.SourceNormalHighIndex10
