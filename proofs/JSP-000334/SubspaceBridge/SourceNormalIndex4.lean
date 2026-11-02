import SubspaceBridge.SourceBlocks4
import SubspaceBridge.OriginalSelectedInputs4
import Mathlib.Algebra.MvPolynomial.Funext
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceNormalIndex4
open SourceMultiblock4 OriginalLastDual4 OriginalAuxiliaryDual4 OriginalDeformedSource4
open Auxiliary4 Auxiliary4.SourceEvaluation4 Auxiliary4.SourceGrid4 Auxiliary4.SourceSupport4
variable {K : Type*} [Field K]

theorem primitive_integer4 (z : Fin 4 → ℤ) (hz : z ≠ 0) :
    ∃ (g : ℤ) (M a : Fin 4 → ℤ), g ≠ 0 ∧ M ≠ 0 ∧
      (∀ i, z i = g*M i) ∧ (∑ i, a i*M i) = 1 ∧ Ideal.span (Set.range M) = ⊤ := by
  let I : Ideal ℤ := Ideal.span (Set.range z)
  let g := Submodule.IsPrincipal.generator I
  have hdiv (i : Fin 4) : g ∣ z i :=
    (Submodule.IsPrincipal.mem_iff_generator_dvd I).mp
      (Ideal.subset_span (Set.mem_range_self i))
  choose M hM using hdiv
  have hg : g ≠ 0 := by
    intro he
    apply hz
    ext i
    rw [hM i,he,zero_mul]
    rfl
  have hgm : g ∈ Submodule.span ℤ (Set.range z) := by
    rw [Ideal.submodule_span_eq]
    exact Submodule.IsPrincipal.generator_mem I
  obtain ⟨a,ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hgm
  simp only [smul_eq_mul] at ha
  have hsum : ∑ i, a i*M i = 1 := by
    apply mul_left_cancel₀ hg
    calc
      g*(∑ i, a i*M i) = ∑ i, a i*z i := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [hM i]
        ring
      _ = g*1 := by simpa using ha
  have hspan : Ideal.span (Set.range M) = ⊤ := by
    apply (Ideal.eq_top_iff_one _).mpr
    rw [← hsum]
    apply Ideal.sum_mem
    intro i _
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_range_self i))
  have hMn : M ≠ 0 := by
    intro he
    apply hz
    ext i
    rw [hM i,he]
    simp
  exact ⟨g,M,a,hg,hMn,hM,hsum,hspan⟩

def realNormalForm4 (M : Fin 4 → ℤ) : Module.Dual ℝ (Fin 4 → ℝ) :=
  ∑ i, (M i : ℝ) • LinearMap.proj i

theorem realNormalForm4_apply (M : Fin 4 → ℤ) (x : Fin 4 → ℝ) :
    realNormalForm4 M x = ∑ i, (M i : ℝ)*x i := by
  simp [realNormalForm4]

theorem real_normal_kernel4 (v : Fin 4 → Fin 4 → ℤ)
    (hv : LinearIndependent ℝ (fun j i => (v j i : ℝ)))
    (M : Fin 4 → ℤ) (hM : M ≠ 0)
    (hann : ∀ j : Fin 3, (∑ i, M i*v j.castSucc i) = 0) :
    LinearMap.ker (realNormalForm4 M) =
      Submodule.span ℝ (Set.range (fun j : Fin 3 => fun i => (v j.castSucc i : ℝ))) := by
  let u : Fin 4 → Fin 4 → ℝ := fun j i => (v j i : ℝ)
  let b := basisOfPiSpaceOfLinearIndependent hv
  have hb (i : Fin 4) : b i = u i := congrFun (coe_basisOfPiSpaceOfLinearIndependent hv) i
  have hf (j : Fin 3) : realNormalForm4 M (u j.castSucc) = 0 := by
    rw [realNormalForm4_apply]
    change (∑ i, (M i : ℝ)*(v j.castSucc i : ℝ)) = 0
    exact_mod_cast hann j
  have hfn : realNormalForm4 M ≠ 0 := by
    intro hz
    apply hM
    funext i
    have he := congrArg (fun f : Module.Dual ℝ (Fin 4 → ℝ) => f (Pi.single i 1)) hz
    have hi : (M i : ℝ) = 0 := by simpa [realNormalForm4,Pi.single_apply] using he
    exact_mod_cast hi
  have hlast : realNormalForm4 M (u 3) ≠ 0 := by
    intro hz
    apply hfn
    apply b.ext
    intro j
    rw [hb]
    refine Fin.lastCases ?_ (fun i => ?_) j
    · exact hz
    · exact hf i
  have hvalue (x : Fin 4 → ℝ) :
      realNormalForm4 M x = b.repr x 3 * realNormalForm4 M (u 3) := by
    conv_lhs => rw [← b.sum_repr x]
    rw [map_sum,Fin.sum_univ_castSucc]
    simp only [map_smul,hb,hf,smul_zero,Finset.sum_const_zero,zero_add]
    rfl
  apply le_antisymm
  · intro x hx
    have hz : b.repr x 3 = 0 := (mul_eq_zero.mp ((hvalue x).symm.trans hx)).resolve_right hlast
    have he := b.sum_repr x
    rw [Fin.sum_univ_castSucc,show Fin.last 3 = (3 : Fin 4) from rfl,hz,zero_smul,add_zero] at he
    rw [← he]
    apply Submodule.sum_mem
    intro j _
    apply Submodule.smul_mem
    rw [hb]
    exact Submodule.subset_span ⟨j,rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨j,rfl⟩
    exact hf j

theorem hermite_sizes4 (eta : ℝ) (heta : 0 < eta) (r : ℕ) (hr : 0 < r) :
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

theorem additional_weight4 {m : ℕ} (r : Fin m → ℕ) (hr : ∀ h, 0 < r h)
    (eta : ℝ) (heta : 0 < eta) (K : Vars4 m →₀ ℕ)
    (hK : ∀ h, (∑ i : Fin 4, K (h,i)) ≤ Nat.floor ((r h : ℝ)*eta)) :
    rothSourceDerivativeWeight r K ≤ (m : ℝ)*eta := by
  unfold rothSourceDerivativeWeight
  calc
    _ ≤ ∑ h : Fin m, eta := by
      apply Finset.sum_le_sum
      intro h _
      apply (div_le_iff₀ (show (0 : ℝ) < r h by exact_mod_cast hr h)).mpr
      have hk : (∑ i : Fin 4, (K (h,i) : ℝ)) ≤ (Nat.floor ((r h : ℝ)*eta) : ℝ) := by
        exact_mod_cast hK h
      exact hk.trans (by simpa [mul_comm] using Nat.floor_le (le_of_lt (mul_pos (by exact_mod_cast hr h) heta)))
    _ = _ := by simp

theorem additional_cutoff4 {m : ℕ} (r : Fin m → ℕ) (hr : ∀ h, 0 < r h)
    (eta : ℝ) (heta : 0 < eta) (J K : Vars4 m →₀ ℕ)
    (hJ : rothSourceDerivativeWeight r J < (m : ℝ)*eta)
    (hK : ∀ h, (∑ i : Fin 4, K (h,i)) ≤ Nat.floor ((r h : ℝ)*eta)) :
    rothSourceDerivativeWeight r (K+J) < 2*eta*m := by
  rw [rothSource_weight_add]
  have hk := additional_weight4 r hr eta heta K hK
  nlinarith

theorem hasse_grid_composition4 {m : ℕ} (P : MvPolynomial (Vars4 m) ℤ)
    (J K : Vars4 m →₀ ℕ) (x : Fin m → Fin 4 → ℤ)
    (hz : integerValue (K+J) P x = 0) :
    integerValue K (derivative4 J P) x = 0 := by
  apply Int.cast_injective (α := ℚ)
  rw [Int.cast_zero,integerValue_cast,derivative4_map,source4_derivative_comp]
  rw [MvPolynomial.smul_eq_C_mul,map_mul,MvPolynomial.eval_C,← integerValue_cast, hz]
  simp


def normalPolynomial4 {m : ℕ} (M : Fin m → Fin 4 → ℤ) (h : Fin m) :
    MvPolynomial (Vars4 m) ℝ := ∑ i, MvPolynomial.C (M h i : ℝ)*MvPolynomial.X (h,i)

def sourceNormalIdeal4 {m : ℕ} (M : Fin m → Fin 4 → ℤ) (r : Fin m → ℕ) (c : ℝ) :
    Ideal (MvPolynomial (Vars4 m) ℝ) :=
  Ideal.span {F | ∃ i : Fin m → ℕ, c ≤ ∑ h, (i h : ℝ)/(r h : ℝ) ∧
    F = ∏ h, (normalPolynomial4 M h)^(i h)}

theorem homogeneous4_map {R : Type*} [CommRing R] (f : R →+* K) {m : ℕ}
    (r : Fin m → ℕ) (P : MvPolynomial (Vars4 m) R) (hP : homogeneous4 r P) :
    homogeneous4 r (P.map f) := by
  intro d hd h
  have hn : P.coeff d ≠ 0 := by
    intro hz
    have hn := MvPolynomial.mem_support_iff.mp hd
    apply hn
    rw [MvPolynomial.coeff_map,hz,map_zero]
  exact hP d (MvPolynomial.mem_support_iff.mpr hn) h

theorem integer_grid_rational_restriction4 {m : ℕ} (r : Fin m → ℕ) (hr : ∀ h, 0 < r h)
    (P : MvPolynomial (Vars4 m) ℤ) (hP : homogeneous4 r P) (J : Vars4 m →₀ ℕ)
    (w : Fin m → Fin 3 → Fin 4 → ℤ) (eta : ℝ) (heta : 0 < eta)
    (hgrid : ∀ a : Fin m → Fin 3 → ℕ, (∀ h j, 1 ≤ a h j ∧ a h j ≤ Nat.floor eta⁻¹+1) →
      ∀ B : Vars4 m →₀ ℕ, (∀ h, (∑ i : Fin 4, B (h,i)) ≤ Nat.floor ((r h : ℝ)*eta)) →
      integerValue B (derivative4 J P) (gridPoint w a) = 0) :
    ∀ y : Fin m → Fin 4 → ℚ,
      (∀ h, y h ∈ Submodule.span ℚ (Set.range (fun j i => (w h j i : ℚ)))) →
      MvPolynomial.eval (fun u => y u.1 u.2) (derivative4 J (P.map (Int.castRingHom ℚ))) = 0 := by
  classical
  let N := Nat.floor eta⁻¹+1
  let S : Fin m → Fin 3 → Finset ℚ := fun _ _ => (Finset.Icc 1 N).image (fun n : ℕ => (n : ℚ))
  have hcard : ∀ h j, (S h j).card = N := by
    intro h j
    dsimp [S]
    rw [Finset.card_image_of_injective _ (Nat.cast_injective)]
    simp
  have hdeg : ∀ d ∈ (derivative4 J (P.map (Int.castRingHom ℚ))).support, ∀ h,
      (∑ i : Fin 4, d (h,i)) ≤ r h :=
    derivative4_block_degree_bound r _ (fun d hd h => (homogeneous4_map _ r P hP d hd h).le) J
  have hsize : ∀ h, r h < N*(Nat.floor ((r h : ℝ)*eta)+1) := by
    intro h
    have he := (hermite_sizes4 eta heta (r h) (hr h)).2.2
    exact_mod_cast he
  apply multiblock_span_hermite4 _ (fun h j i => (w h j i : ℚ)) S (fun _ => N)
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
  change (integerValue B (derivative4 J P) (gridPoint w n) : ℚ) = 0 at hz
  rw [integerValue_cast,derivative4_map] at hz
  have he : blockFramePoint4 (fun h j i => (w h j i : ℚ)) a =
      (fun u : Vars4 m => (gridPoint w n u.1 u.2 : ℚ)) := by
    funext u
    rcases u with ⟨h,i⟩
    simp only [blockFramePoint4,gridPoint,Int.cast_sum,Int.cast_mul,Int.cast_natCast]
    apply Finset.sum_congr rfl
    intro j _
    rw [hna h j]
  rw [he]
  exact hz


theorem integer_grid_real_restriction4 {m : ℕ} (r : Fin m → ℕ) (hr : ∀ h, 0 < r h)
    (P : MvPolynomial (Vars4 m) ℤ) (hP : homogeneous4 r P) (J : Vars4 m →₀ ℕ)
    (w : Fin m → Fin 3 → Fin 4 → ℤ) (eta : ℝ) (heta : 0 < eta)
    (hgrid : ∀ a : Fin m → Fin 3 → ℕ, (∀ h j, 1 ≤ a h j ∧ a h j ≤ Nat.floor eta⁻¹+1) →
      ∀ B : Vars4 m →₀ ℕ, (∀ h, (∑ i : Fin 4, B (h,i)) ≤ Nat.floor ((r h : ℝ)*eta)) →
      integerValue B (derivative4 J P) (gridPoint w a) = 0) :
    ∀ y : Fin m → Fin 4 → ℝ,
      (∀ h, y h ∈ Submodule.span ℝ (Set.range (fun j i => (w h j i : ℝ)))) →
      MvPolynomial.eval (fun u => y u.1 u.2) (derivative4 J (P.map (Int.castRingHom ℝ))) = 0 := by
  classical
  let N := Nat.floor eta⁻¹+1
  let S : Fin m → Fin 3 → Finset ℝ := fun _ _ => (Finset.Icc 1 N).image (fun n : ℕ => (n : ℝ))
  have hcard : ∀ h j, (S h j).card = N := by
    intro h j
    dsimp [S]
    rw [Finset.card_image_of_injective _ (Nat.cast_injective)]
    simp
  have hdeg : ∀ d ∈ (derivative4 J (P.map (Int.castRingHom ℝ))).support, ∀ h,
      (∑ i : Fin 4, d (h,i)) ≤ r h :=
    derivative4_block_degree_bound r _ (fun d hd h => (homogeneous4_map _ r P hP d hd h).le) J
  have hsize : ∀ h, r h < N*(Nat.floor ((r h : ℝ)*eta)+1) := by
    intro h
    have he := (hermite_sizes4 eta heta (r h) (hr h)).2.2
    exact_mod_cast he
  apply multiblock_span_hermite4 _ (fun h j i => (w h j i : ℝ)) S (fun _ => N)
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
  change (integerValue B (derivative4 J P) (gridPoint w n) : ℝ) = ((0 : ℤ) : ℝ) at hz
  rw [hz0] at hz
  rw [integerValue_cast,derivative4_map] at hz
  have he : blockFramePoint4 (fun h j i => (w h j i : ℝ)) a =
      (fun u : Vars4 m => (gridPoint w n u.1 u.2 : ℝ)) := by
    funext u
    rcases u with ⟨h,i⟩
    simp only [blockFramePoint4,gridPoint,Int.cast_sum,Int.cast_mul,Int.cast_natCast]
    apply Finset.sum_congr rfl
    intro j _
    rw [hna h j]
  rw [he]
  exact hz


def normalForward4 {m : ℕ} (M : Fin m → Fin 4 → ℤ) (k : Fin m → Fin 4) :
    MvPolynomial (Vars4 m) ℝ →+* MvPolynomial (Vars4 m) ℝ :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    (fun u => if u.2 = k u.1 then normalPolynomial4 M u.1 else MvPolynomial.X u)

def normalInverse4 {m : ℕ} (M : Fin m → Fin 4 → ℤ) (k : Fin m → Fin 4) :
    MvPolynomial (Vars4 m) ℝ →+* MvPolynomial (Vars4 m) ℝ :=
  MvPolynomial.eval₂Hom MvPolynomial.C (fun u => if u.2 = k u.1 then
    MvPolynomial.C ((M u.1 (k u.1) : ℝ)⁻¹) *
      (MvPolynomial.X u - ∑ j ∈ Finset.univ.erase (k u.1),
        MvPolynomial.C (M u.1 j : ℝ) * MvPolynomial.X (u.1,j))
    else MvPolynomial.X u)

theorem normalForward6_inverse4 {m : ℕ} (M : Fin m → Fin 4 → ℤ)
    (k : Fin m → Fin 4) (hk : ∀ h, M h (k h) ≠ 0)
    (P : MvPolynomial (Vars4 m) ℝ) :
    normalForward4 M k (normalInverse4 M k P) = P := by
  classical
  have he : (normalForward4 M k).comp (normalInverse4 M k) = RingHom.id _ := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [normalForward4,normalInverse4]
    · intro u
      rcases u with ⟨h,i⟩
      by_cases hi : i = k h
      · subst i
        have hc : (MvPolynomial.C ((M h (k h) : ℝ)⁻¹) : MvPolynomial (Vars4 m) ℝ) *
            MvPolynomial.C (M h (k h) : ℝ) = 1 := by
          rw [← MvPolynomial.C_mul,inv_mul_cancel₀ (by exact_mod_cast hk h),map_one]
        have hs : normalPolynomial4 M h =
            (∑ j ∈ Finset.univ.erase (k h),
              MvPolynomial.C (M h j : ℝ) * MvPolynomial.X (h,j)) +
              MvPolynomial.C (M h (k h) : ℝ) * MvPolynomial.X (h,k h) := by
          exact (Finset.sum_erase_add _ _ (Finset.mem_univ (k h))).symm
        simp only [RingHom.comp_apply,normalInverse4,MvPolynomial.eval₂Hom_X',
          Prod.fst,Prod.snd,ite_true,map_mul,map_sub,map_sum,normalForward4,
          MvPolynomial.eval₂Hom_C,MvPolynomial.eval₂Hom_X',RingHom.id_apply]
        have hfree : (∑ j ∈ Finset.univ.erase (k h),
            MvPolynomial.C (M h j : ℝ) *
              (if j = k h then normalPolynomial4 M h else MvPolynomial.X (h,j))) =
            ∑ j ∈ Finset.univ.erase (k h),
              MvPolynomial.C (M h j : ℝ) * MvPolynomial.X (h,j) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [if_neg (Finset.mem_erase.mp hj).1]
        rw [hfree,hs,add_sub_cancel_left,← mul_assoc,hc,one_mul]
      · simp [normalForward4,normalInverse4,hi]
  exact congrArg (fun f => f P) he

theorem normalInverse6_forward4 {m : ℕ} (M : Fin m → Fin 4 → ℤ)
    (k : Fin m → Fin 4) (hk : ∀ h, M h (k h) ≠ 0)
    (P : MvPolynomial (Vars4 m) ℝ) :
    normalInverse4 M k (normalForward4 M k P) = P := by
  classical
  have he : (normalInverse4 M k).comp (normalForward4 M k) = RingHom.id _ := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [normalForward4,normalInverse4]
    · intro u
      rcases u with ⟨h,i⟩
      by_cases hi : i = k h
      · subst i
        have hc : (MvPolynomial.C (M h (k h) : ℝ) : MvPolynomial (Vars4 m) ℝ) *
            MvPolynomial.C ((M h (k h) : ℝ)⁻¹) = 1 := by
          rw [← MvPolynomial.C_mul,mul_inv_cancel₀ (by exact_mod_cast hk h),map_one]
        simp only [RingHom.comp_apply,normalForward4,MvPolynomial.eval₂Hom_X',
          Prod.fst,Prod.snd,ite_true,RingHom.id_apply]
        change normalInverse4 M k (normalPolynomial4 M h) = MvPolynomial.X (h,k h)
        rw [normalPolynomial4,← Finset.sum_erase_add _ _ (Finset.mem_univ (k h))]
        simp only [map_add,map_sum,map_mul,normalInverse4,MvPolynomial.eval₂Hom_C,
          MvPolynomial.eval₂Hom_X',Prod.fst,Prod.snd,ite_true]
        have hfree : (∑ j ∈ Finset.univ.erase (k h),
            MvPolynomial.C (M h j : ℝ) *
              (if j = k h then MvPolynomial.C ((M h (k h) : ℝ)⁻¹) *
                (MvPolynomial.X (h,j) - ∑ l ∈ Finset.univ.erase (k h),
                  MvPolynomial.C (M h l : ℝ) * MvPolynomial.X (h,l))
               else MvPolynomial.X (h,j))) =
            ∑ j ∈ Finset.univ.erase (k h),
              MvPolynomial.C (M h j : ℝ) * MvPolynomial.X (h,j) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [if_neg (Finset.mem_erase.mp hj).1]
        rw [hfree,← mul_assoc,hc,one_mul]
        ring
      · simp [normalForward4,normalInverse4,hi]
  exact congrArg (fun f => f P) he

noncomputable def zeroNormalCoordinates4 {m : ℕ} (k : Fin m → Fin 4) :
    MvPolynomial (Vars4 m) K →+* MvPolynomial (Vars4 m) K :=
  MvPolynomial.eval₂Hom MvPolynomial.C (fun u => if u.2 = k u.1 then 0 else MvPolynomial.X u)

theorem zeroNormalCoordinates4_monomial {m : ℕ} (k : Fin m → Fin 4)
    (b : Vars4 m →₀ ℕ) (c : K) :
    zeroNormalCoordinates4 k (MvPolynomial.monomial b c) =
      if (∀ h, b (h,k h) = 0) then MvPolynomial.monomial b c else 0 := by
  classical
  rw [zeroNormalCoordinates4, MvPolynomial.eval₂Hom_monomial]
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
    have hz : (∏ u : Vars4 m, (if u.2 = k u.1 then 0 else MvPolynomial.X u) ^ b u) =
        (0 : MvPolynomial (Vars4 m) K) := by
      apply Finset.prod_eq_zero (Finset.mem_univ (h,k h))
      simp [hh]
    rw [hz, mul_zero]

theorem zeroNormalCoordinates4_coeff {m : ℕ} (k : Fin m → Fin 4)
    (Q : MvPolynomial (Vars4 m) K) (b : Vars4 m →₀ ℕ) :
    (zeroNormalCoordinates4 k Q).coeff b = if (∀ h, b (h,k h) = 0) then Q.coeff b else 0 := by
  classical
  induction Q using MvPolynomial.induction_on' with
  | monomial a c =>
    rw [zeroNormalCoordinates4_monomial]
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


theorem normal_zero_restriction4 {m : ℕ} (M : Fin m → Fin 4 → ℤ)
    (k : Fin m → Fin 4) (hk : ∀ h, M h (k h) ≠ 0)
    (P : MvPolynomial (Vars4 m) ℝ)
    (hzero : ∀ y : Fin m → Fin 4 → ℝ,
      (∀ h, y h ∈ LinearMap.ker (realNormalForm4 (M h))) →
      MvPolynomial.eval (fun u => y u.1 u.2) P = 0) :
    zeroNormalCoordinates4 k (normalInverse4 M k P) = 0 := by
  classical
  apply MvPolynomial.funext
  intro z
  let H := (zeroNormalCoordinates4 (K := ℝ) k).comp (normalInverse4 M k)
  let y : Fin m → Fin 4 → ℝ := fun h i => MvPolynomial.eval z (H (MvPolynomial.X (h,i)))
  have he : (MvPolynomial.eval z).comp H = MvPolynomial.eval (fun u => y u.1 u.2) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [H,normalInverse4,zeroNormalCoordinates4]
    · intro u
      simp [y]
  have hker : ∀ h, y h ∈ LinearMap.ker (realNormalForm4 (M h)) := by
    intro h
    have hn := normalInverse6_forward4 M k hk (MvPolynomial.X (h,k h))
    simp only [normalForward4,MvPolynomial.eval₂Hom_X',Prod.fst,Prod.snd,ite_true] at hn
    have hz := congrArg (fun Q => MvPolynomial.eval z (zeroNormalCoordinates4 k Q)) hn
    simp only [zeroNormalCoordinates4,MvPolynomial.eval₂Hom_X',Prod.fst,Prod.snd,
      ite_true,map_zero] at hz
    have hp := congrArg (fun f : MvPolynomial (Vars4 m) ℝ →+* ℝ => f (normalPolynomial4 M h)) he
    change MvPolynomial.eval z (H (normalPolynomial4 M h)) = _ at hp
    change MvPolynomial.eval z (H (normalPolynomial4 M h)) = 0 at hz
    rw [hp] at hz
    simpa [LinearMap.mem_ker,realNormalForm4,normalPolynomial4,map_sum,map_mul,y] using hz
  have hp := congrArg (fun f : MvPolynomial (Vars4 m) ℝ →+* ℝ => f P) he
  change MvPolynomial.eval z (zeroNormalCoordinates4 k (normalInverse4 M k P)) =
    MvPolynomial.eval (fun u => y u.1 u.2) P at hp
  rw [hp,hzero y hker,map_zero]

theorem normalInverse4_pderiv_X {m : ℕ} (M : Fin m → Fin 4 → ℤ)
    (k : Fin m → Fin 4) (h : Fin m) (u : Vars4 m) :
    MvPolynomial.pderiv (h,k h) (normalInverse4 M k (MvPolynomial.X u)) =
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
      simp only [normalInverse4,MvPolynomial.eval₂Hom_X',Prod.fst,Prod.snd,ite_true,
        MvPolynomial.pderiv_C_mul,map_sub,hs,MvPolynomial.pderiv_X,Pi.single_eq_same]
      simp
    · simp [normalInverse4,hi,MvPolynomial.pderiv_X,Pi.single_apply,Prod.mk.injEq,Ne.symm hi]
  · by_cases hi : i = k g <;>
      simp [normalInverse4,hi,MvPolynomial.pderiv_C_mul,MvPolynomial.pderiv_X,map_sum,
        Pi.single_apply,Prod.mk.injEq,hg,Ne.symm hg]

theorem normalInverse4_chain {m : ℕ} (M : Fin m → Fin 4 → ℤ)
    (k : Fin m → Fin 4) (h : Fin m) (P : MvPolynomial (Vars4 m) ℝ) :
    MvPolynomial.pderiv (h,k h) (normalInverse4 M k P) =
      MvPolynomial.C ((M h (k h) : ℝ)⁻¹) * normalInverse4 M k (MvPolynomial.pderiv (h,k h) P) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C c => simp [normalInverse4]
  | add P Q hP hQ => simp only [map_add,hP,hQ,mul_add]
  | mul_X P u hP =>
    rw [map_mul,MvPolynomial.pderiv_mul,hP,normalInverse4_pderiv_X,
      MvPolynomial.pderiv_mul,map_add,map_mul,MvPolynomial.pderiv_X]
    simp only [Pi.single_apply,apply_ite,map_one,map_zero]
    by_cases hu : u = (h,k h)
    · subst u
      simp
      ring
    · simp [hu,Ne.symm hu]
      ring

def normalCoordinateWeight4 {m : ℕ} (r : Fin m → ℕ) (k : Fin m → Fin 4)
    (b : Vars4 m →₀ ℕ) : ℝ := ∑ h, (b (h,k h) : ℝ) / r h

theorem normalCoordinateWeight4_add {m : ℕ} (r : Fin m → ℕ) (k : Fin m → Fin 4)
    (b c : Vars4 m →₀ ℕ) :
    normalCoordinateWeight4 r k (b+c) = normalCoordinateWeight4 r k b + normalCoordinateWeight4 r k c := by
  simp [normalCoordinateWeight4,Finsupp.add_apply,Nat.cast_add,add_div,Finset.sum_add_distrib]

theorem normalCoordinateWeight4_single {m : ℕ} (r : Fin m → ℕ) (k : Fin m → Fin 4) (h : Fin m) :
    normalCoordinateWeight4 r k (Finsupp.single (h,k h) 1) = 1/(r h : ℝ) := by
  have he (g : Fin m) : (Finsupp.single (h,k h) 1 : Vars4 m →₀ ℕ) (g,k g) =
      if g = h then 1 else 0 := by
    by_cases hg : g = h
    · subst g; simp
    · simp [Finsupp.single_apply,Prod.mk.injEq,Ne.symm hg,hg]
  simp only [normalCoordinateWeight4]
  simp_rw [he]
  simp [ite_div,Finset.sum_ite_eq,Finset.sum_ite_eq']

theorem normalInverse4_coeff_zero {m : ℕ} (M : Fin m → Fin 4 → ℤ)
    (k : Fin m → Fin 4) (hk : ∀ h, M h (k h) ≠ 0)
    (r : Fin m → ℕ) (c : ℝ) (P : MvPolynomial (Vars4 m) ℝ)
    (hindex : ∀ J : Vars4 m →₀ ℕ, rothSourceDerivativeWeight r J < c →
      ∀ y : Fin m → Fin 4 → ℝ, (∀ h, y h ∈ LinearMap.ker (realNormalForm4 (M h))) →
        MvPolynomial.eval (fun u => y u.1 u.2) (derivative4 J P) = 0)
    (J b : Vars4 m →₀ ℕ)
    (hbad : rothSourceDerivativeWeight r J + normalCoordinateWeight4 r k b < c) :
    (normalInverse4 M k (derivative4 J P)).coeff b = 0 := by
  classical
  have go : ∀ n : ℕ, ∀ J b : Vars4 m →₀ ℕ,
      (∑ h : Fin m, b (h,k h)) = n →
      rothSourceDerivativeWeight r J + normalCoordinateWeight4 r k b < c →
      (normalInverse4 M k (derivative4 J P)).coeff b = 0 := by
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
        have hnonneg : 0 ≤ normalCoordinateWeight4 r k b := by
          unfold normalCoordinateWeight4
          positivity
        have hJ : rothSourceDerivativeWeight r J < c := by linarith
        have hz := normal_zero_restriction4 M k hk (derivative4 J P) (hindex J hJ)
        have he := congrArg (MvPolynomial.coeff b) hz
        rw [zeroNormalCoordinates4_coeff,if_pos hbzero,MvPolynomial.coeff_zero] at he
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
          have hs := congrArg (fun b : Vars4 m →₀ ℕ => ∑ g : Fin m, b (g,k g)) hdeq
          have he (g : Fin m) : (Finsupp.single (h,k h) 1 : Vars4 m →₀ ℕ) (g,k g) =
              if g = h then 1 else 0 := by
            by_cases hg : g = h
            · subst g; simp
            · simp [Finsupp.single_apply,Prod.mk.injEq,Ne.symm hg,hg]
          simp_rw [Finsupp.add_apply,he] at hs
          simpa [Finset.sum_add_distrib,Finset.sum_ite_eq,Finset.sum_ite_eq',hn] using hs
        have hcoord : normalCoordinateWeight4 r k d + 1/(r h : ℝ) = normalCoordinateWeight4 r k b := by
          rw [← normalCoordinateWeight4_single r k h,← normalCoordinateWeight4_add,hdeq]
        have hz : (normalInverse4 M k (derivative4 (J+Finsupp.single (h,k h) 1) P)).coeff d = 0 := by
          apply ih (∑ g : Fin m, d (g,k g)) (by omega) _ d rfl
          rw [rothSource_weight_add,rothSource_weight_single]
          linarith
        have hd : (MvPolynomial.pderiv (h,k h) (normalInverse4 M k (derivative4 J P))).coeff d = 0 := by
          rw [normalInverse4_chain,source4_pderiv_hasse,map_nsmul,
            MvPolynomial.coeff_C_mul,MvPolynomial.coeff_smul,hz,smul_zero,mul_zero]
        rw [SourceSupport4.pderiv_coeff,hdeq] at hd
        exact (mul_eq_zero.mp hd).resolve_left (Nat.cast_ne_zero.mpr (by omega))
  exact go _ J b rfl hbad

theorem normalForward4_monomial {m : ℕ} (M : Fin m → Fin 4 → ℤ)
    (k : Fin m → Fin 4) (b : Vars4 m →₀ ℕ) (a : ℝ) :
    normalForward4 M k (MvPolynomial.monomial b a) =
      MvPolynomial.C a * ((∏ h, (normalPolynomial4 M h) ^ b (h,k h)) *
        (∏ h, ∏ i ∈ Finset.univ.erase (k h), MvPolynomial.X (h,i) ^ b (h,i))) := by
  classical
  rw [normalForward4,MvPolynomial.eval₂Hom_monomial]
  rw [Finsupp.prod_fintype _ _ (fun _ => by simp),Fintype.prod_prod_type,
    ← Finset.prod_mul_distrib]
  congr 1
  apply Finset.prod_congr rfl
  intro h hh
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ (k h))]
  simp only [Prod.fst,Prod.snd,ite_true]
  have he : (∏ i ∈ Finset.univ.erase (k h),
      (if i = k h then normalPolynomial4 M h else MvPolynomial.X (h,i)) ^ b (h,i)) =
      ∏ i ∈ Finset.univ.erase (k h), MvPolynomial.X (h,i) ^ b (h,i) := by
    apply Finset.prod_congr rfl
    intro i hi
    rw [if_neg (Finset.mem_erase.mp hi).1]
  rw [he]
  ring

theorem normalForward4_monomial_mem {m : ℕ} (M : Fin m → Fin 4 → ℤ)
    (k : Fin m → Fin 4) (r : Fin m → ℕ) (c : ℝ)
    (b : Vars4 m →₀ ℕ) (a : ℝ) (hb : c ≤ normalCoordinateWeight4 r k b) :
    normalForward4 M k (MvPolynomial.monomial b a) ∈ sourceNormalIdeal4 M r c := by
  have hg : (∏ h, (normalPolynomial4 M h) ^ b (h,k h)) ∈ sourceNormalIdeal4 M r c :=
    Ideal.subset_span ⟨fun h => b (h,k h),hb,rfl⟩
  rw [normalForward4_monomial]
  have hm := Ideal.mul_mem_left (sourceNormalIdeal4 M r c)
    (MvPolynomial.C a * (∏ h, ∏ i ∈ Finset.univ.erase (k h), MvPolynomial.X (h,i) ^ b (h,i))) hg
  convert hm using 1
  ring

theorem sourceNormalIdeal4_of_derivative_restrictions {m : ℕ}
    (M : Fin m → Fin 4 → ℤ) (hM : ∀ h, M h ≠ 0)
    (r : Fin m → ℕ) (c : ℝ) (P : MvPolynomial (Vars4 m) ℝ)
    (hindex : ∀ J : Vars4 m →₀ ℕ, rothSourceDerivativeWeight r J < c →
      ∀ y : Fin m → Fin 4 → ℝ, (∀ h, y h ∈ LinearMap.ker (realNormalForm4 (M h))) →
        MvPolynomial.eval (fun u => y u.1 u.2) (derivative4 J P) = 0) :
    P ∈ sourceNormalIdeal4 M r c := by
  classical
  have hex (h : Fin m) : ∃ i : Fin 4, M h i ≠ 0 := by
    by_contra! hz
    exact hM h (funext hz)
  choose k hk using hex
  have hcoeff (b : Vars4 m →₀ ℕ) (hb : normalCoordinateWeight4 r k b < c) :
      (normalInverse4 M k P).coeff b = 0 := by
    have hz := normalInverse4_coeff_zero M k hk r c P hindex 0 b
      (by simpa [rothSourceDerivativeWeight] using hb)
    simpa only [derivative4_zero_index] using hz
  have hsupport (b) (hb : b ∈ (normalInverse4 M k P).support) :
      c ≤ normalCoordinateWeight4 r k b := by
    by_contra! hlt
    exact (MvPolynomial.mem_support_iff.mp hb) (hcoeff b hlt)
  have hsum := congrArg (normalForward4 M k) (normalInverse4 M k P).as_sum
  rw [normalForward6_inverse4 M k hk P,map_sum] at hsum
  rw [hsum]
  apply Ideal.sum_mem
  intro b hb
  exact normalForward4_monomial_mem M k r c b _ (hsupport b hb)

theorem integer_grid_high_normal_index4 {m : ℕ} (r : Fin m → ℕ) (hr : ∀ h, 0 < r h)
    (P : MvPolynomial (Vars4 m) ℤ) (hP : homogeneous4 r P)
    (w : Fin m → Fin 3 → Fin 4 → ℤ) (M : Fin m → Fin 4 → ℤ)
    (hM : ∀ h, M h ≠ 0)
    (hQ : ∀ h, LinearMap.ker (normalForm4 (M h)) =
      Submodule.span ℚ (Set.range (fun j i => (w h j i : ℚ))))
    (hR : ∀ h, LinearMap.ker (realNormalForm4 (M h)) =
      Submodule.span ℝ (Set.range (fun j i => (w h j i : ℝ))))
    (eta : ℝ) (heta : 0 < eta)
    (hgrid : ∀ a : Fin m → Fin 3 → ℕ, (∀ h j, 1 ≤ a h j ∧ a h j ≤ Nat.floor eta⁻¹+1) →
      ∀ J : Vars4 m →₀ ℕ, rothSourceDerivativeWeight r J < 2*eta*m →
        integerValue J P (gridPoint w a) = 0) :
    (∀ J : Vars4 m →₀ ℕ, rothSourceDerivativeWeight r J < (m : ℝ)*eta →
      (∀ y : Fin m → Fin 4 → ℚ, (∀ h, y h ∈ LinearMap.ker (normalForm4 (M h))) →
        MvPolynomial.eval (fun u => y u.1 u.2) (derivative4 J (P.map (Int.castRingHom ℚ))) = 0) ∧
      (∀ y : Fin m → Fin 4 → ℝ, (∀ h, y h ∈ LinearMap.ker (realNormalForm4 (M h))) →
        MvPolynomial.eval (fun u => y u.1 u.2) (derivative4 J (P.map (Int.castRingHom ℝ))) = 0)) ∧
    P.map (Int.castRingHom ℝ) ∈ sourceNormalIdeal4 M r ((m : ℝ)*eta) := by
  have hrestr : ∀ J : Vars4 m →₀ ℕ, rothSourceDerivativeWeight r J < (m : ℝ)*eta →
      (∀ y : Fin m → Fin 4 → ℚ, (∀ h, y h ∈ LinearMap.ker (normalForm4 (M h))) →
        MvPolynomial.eval (fun u => y u.1 u.2) (derivative4 J (P.map (Int.castRingHom ℚ))) = 0) ∧
      (∀ y : Fin m → Fin 4 → ℝ, (∀ h, y h ∈ LinearMap.ker (realNormalForm4 (M h))) →
        MvPolynomial.eval (fun u => y u.1 u.2) (derivative4 J (P.map (Int.castRingHom ℝ))) = 0) := by
    intro J hJ
    have hc : ∀ a : Fin m → Fin 3 → ℕ, (∀ h j, 1 ≤ a h j ∧ a h j ≤ Nat.floor eta⁻¹+1) →
        ∀ B : Vars4 m →₀ ℕ, (∀ h, (∑ i : Fin 4, B (h,i)) ≤ Nat.floor ((r h : ℝ)*eta)) →
          integerValue B (derivative4 J P) (gridPoint w a) = 0 := by
      intro a ha B hB
      exact hasse_grid_composition4 P J B _
        (hgrid a ha (B+J) (additional_cutoff4 r hr eta heta J B hJ hB))
    constructor
    · intro y hy
      apply integer_grid_rational_restriction4 r hr P hP J w eta heta hc y
      intro h
      rw [← hQ h]
      exact hy h
    · intro y hy
      exact integer_grid_real_restriction4 r hr P hP J w eta heta hc y
        (fun h => (hR h) ▸ hy h)

  exact ⟨hrestr,sourceNormalIdeal4_of_derivative_restrictions M hM r ((m : ℝ)*eta)
    (P.map (Int.castRingHom ℝ)) (fun J hJ => (hrestr J hJ).2)⟩



theorem primitive_cofactor_normal4 (v : Fin 4 → Fin 4 → ℤ)
    (hv : LinearIndependent ℝ (fun j => integerReal (v j))) :
    ∃ (g : ℤ) (M a : Fin 4 → ℤ), g ≠ 0 ∧ M ≠ 0 ∧
      (∀ i, integerLastDual4 v i = g*M i) ∧ (∑ i, a i*M i) = 1 ∧
      Ideal.span (Set.range M) = ⊤ ∧
      (∀ j : Fin 3, (∑ i, M i*v j.castSucc i) = 0) ∧
      LinearMap.ker (normalForm4 M) =
        Submodule.span ℚ (Set.range (fun j : Fin 3 => fun i => (v j.castSucc i : ℚ))) ∧
      LinearMap.ker (realNormalForm4 M) =
        Submodule.span ℝ (Set.range (fun j : Fin 3 => integerReal (v j.castSucc))) := by
  have hrat := integral_frame_rational_independent v hv
  obtain ⟨g,M,a,hg,hMn,hscale,ha,hspan⟩ :=
    primitive_integer4 (integerLastDual4 v) (integerLastDual4_nonzero v hrat)
  have hgQ : (g : ℚ) ≠ 0 := by exact_mod_cast hg
  have hscaleQ : normalForm4 (integerLastDual4 v) = (g : ℚ) • normalForm4 M := by
    apply LinearMap.ext
    intro x
    rw [normalForm4_apply,LinearMap.smul_apply,normalForm4_apply,smul_eq_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [hscale i]
    push_cast
    ring
  have hk : LinearMap.ker (normalForm4 M) = firstThreeSpan4 (fun j i => (v j i : ℚ)) := by
    calc
      _ = LinearMap.ker (normalForm4 (integerLastDual4 v)) := by rw [hscaleQ,LinearMap.ker_smul _ _ hgQ]
      _ = _ := by
        rw [integerLastDual4_form v hrat,LinearMap.ker_smul _ _
          (show ((Matrix.det v : ℤ) : ℚ) ≠ 0 by exact_mod_cast integerFrame4_det_ne_zero v hrat),
          lastDual4_kernel]
  have hann (j : Fin 3) : (∑ i, M i*v j.castSucc i) = 0 := by
    have hm : (fun i => (v j.castSucc i : ℚ)) ∈ LinearMap.ker (normalForm4 M) := by
      rw [hk]
      exact Submodule.subset_span (Set.mem_range_self j)
    have hmQ := (normalForm4_apply M (fun i => (v j.castSucc i : ℚ))).symm.trans hm
    exact_mod_cast hmQ
  exact ⟨g,M,a,hg,hMn,hscale,ha,hspan,hann,hk,real_normal_kernel4 v hv M hMn hann⟩

variable {A2 A3 : Matrix (Fin 4) (Fin 4) ℚ} {L : Matrix (Fin 4) (Fin 4) ℝ}
  {hL : IsUnit L} {c0 c2 c3 : Fin 4 → ℝ} {delta : ℝ}
  {U : Set ℝ} {hQU : ∀ q ∈ U, 1 < q}
  {u : (q : U) → Fin 4 → originalSourceGroup4 A2 A3 q.val c2 c3}

def sourceFrameHighIndex4
    (F : (q : U) → DeformedAttaining4 A2 A3 L hL q.val
      (hQU q.val q.property) c0 c2 c3 delta (u q)) : Prop :=

    ∃ eta : ℝ, 0 < eta ∧ eta < 1 ∧ ∃ m : ℕ, 0 < m ∧
      ∃ K : IntermediateField ℚ ℝ, FiniteDimensional ℚ K ∧
      (∀ tau i j, SourceForms4.forms4 A2 A3 L tau i j ∈ K) ∧
      ∃ D E : ℝ, 1 ≤ D ∧ 1 ≤ E ∧
      ∀ rho : ℝ, 0 < rho → ∃ t : Fin m → U,
        StrictMono (fun h => (t h).val) ∧
        ∃ r : Fin m → ℕ, (∀ h, 0 < r h) ∧
        (∀ (h : Fin m) (hh : h.val+1 < m), (r ⟨h.val+1,hh⟩ : ℝ) ≤ rho*(r h : ℝ)) ∧
        ∃ P : MvPolynomial (Vars4 m) ℤ, P ≠ 0 ∧ homogeneous4 r P ∧
          (height4 P : ℝ) ≤ D^(∑ h, r h) ∧
          matrixIndex4 L r eta P ∧ matrixIndex4 (SourceForms4.finiteMatrix4 2 A2) r eta P ∧
          matrixIndex4 (SourceForms4.finiteMatrix4 3 A3) r eta P ∧
          (∀ J b : Vars4 m →₀ ℕ,
            ‖(Auxiliary4.SourceExpansion4.expansion L J P).coeff b‖ ≤ E^(∑ h,r h) ∧
            ‖(Auxiliary4.SourceExpansion4.expansion (SourceForms4.finiteMatrix4 2 A2) J P).coeff b‖ ≤ E^(∑ h,r h) ∧
            ‖(Auxiliary4.SourceExpansion4.expansion (SourceForms4.finiteMatrix4 3 A3) J P).coeff b‖ ≤ E^(∑ h,r h)) ∧
          (∀ a : Fin m → Fin 3 → ℕ, (∀ h j, 1 ≤ a h j ∧ a h j ≤ Nat.floor eta⁻¹+1) →
          ∀ J : Vars4 m →₀ ℕ, rothSourceDerivativeWeight r J < 2*eta*m →
            integerValue J P (gridPoint (fun h j => ((F (t h)).w j.castSucc : Fin 4 → ℤ)) a) = 0) ∧
          ∃ (g : Fin m → ℤ) (M a : Fin m → Fin 4 → ℤ),
            (∀ h, g h ≠ 0 ∧ M h ≠ 0 ∧
              (∀ i, integerLastDual4 (fun j => ((F (t h)).w j : Fin 4 → ℤ)) i = g h*M h i) ∧
              (∑ i, a h i*M h i) = 1 ∧ Ideal.span (Set.range (M h)) = ⊤ ∧
              LinearMap.ker (normalForm4 (M h)) =
                Submodule.span ℚ (Set.range (fun j : Fin 3 => fun i => (((F (t h)).w j.castSucc : Fin 4 → ℤ) i : ℚ))) ∧
              LinearMap.ker (realNormalForm4 (M h)) =
                Submodule.span ℝ (Set.range (fun j : Fin 3 => integerReal ((F (t h)).w j.castSucc : Fin 4 → ℤ)))) ∧
            (∀ J : Vars4 m →₀ ℕ, rothSourceDerivativeWeight r J < (m : ℝ)*eta →
              (∀ y : Fin m → Fin 4 → ℚ, (∀ h, y h ∈ LinearMap.ker (normalForm4 (M h))) →
                MvPolynomial.eval (fun u => y u.1 u.2) (derivative4 J (P.map (Int.castRingHom ℚ))) = 0) ∧
              (∀ y : Fin m → Fin 4 → ℝ, (∀ h, y h ∈ LinearMap.ker (realNormalForm4 (M h))) →
                MvPolynomial.eval (fun u => y u.1 u.2) (derivative4 J (P.map (Int.castRingHom ℝ))) = 0)) ∧
            P.map (Int.castRingHom ℝ) ∈ sourceNormalIdeal4 M r ((m : ℝ)*eta)

theorem same_selected_frame_high_index4
    (h2 : A2.det = 1) (h3 : A3.det = 1) (hLdet : L.det = 1)
    (ha : ∀ i j, IsAlgebraic ℚ (L i j))
    (F : (q : U) → DeformedAttaining4 A2 A3 L hL q.val
      (hQU q.val q.property) c0 c2 c3 delta (u q))
    (hU : ¬ BddAbove U) (hd : 0 < delta)
    (hc2 : ∀ i, -1 ≤ c2 i ∧ c2 i ≤ 0) (hc3 : ∀ i, -1 ≤ c3 i ∧ c3 i ≤ 0) : sourceFrameHighIndex4 F := by
  obtain ⟨eta,he,he1,m,hm,K,hK,hmem,D,E,hD,hE,hblocks⟩ :=
    SourceBlocks4.same_selected_frame_grid4 h2 h3 hLdet ha F hU hd hc2 hc3
  refine ⟨eta,he,he1,m,hm,K,hK,hmem,D,E,hD,hE,?_⟩
  intro rho hp
  obtain ⟨t,ht,r,hr,hrsep,P,hP,hhom,hheight,hi0,hi2,hi3,hcfs,hgrid⟩ := hblocks rho hp
  have hex (h : Fin m) := primitive_cofactor_normal4
    (fun j => ((F (t h)).w j : Fin 4 → ℤ)) (F (t h)).real_independent
  choose g M a hg hM hscale ha hspan hann hQ hR using hex
  refine ⟨t,ht,r,hr,hrsep,P,hP,hhom,hheight,hi0,hi2,hi3,hcfs,hgrid,g,M,a,?_,?_⟩
  · intro h
    exact ⟨hg h,hM h,hscale h,ha h,hspan h,hQ h,hR h⟩
  · exact integer_grid_high_normal_index4 r hr P hhom
      (fun h j => ((F (t h)).w j.castSucc : Fin 4 → ℤ)) M hM hQ hR eta he hgrid


end CompoundFeasibility.SourceNormalIndex4
