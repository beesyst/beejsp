import SubspaceBridge.SourceBlocks6
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.Polynomial.Roots
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceNormalIndex
open Auxiliary6 Auxiliary6.SourceExpansion Auxiliary6.SourceEvaluation Auxiliary6.SourceGrid

def normalForm6 (M : Fin 6 → ℤ) : Module.Dual ℚ (Fin 6 → ℚ) :=
  ∑ i, (M i : ℚ) • LinearMap.proj i

theorem normalForm6_apply (M : Fin 6 → ℤ) (x : Fin 6 → ℚ) :
    normalForm6 M x = ∑ i, (M i : ℚ)*x i := by
  simp [normalForm6]

theorem functional_coordinates6 (f : Module.Dual ℚ (Fin 6 → ℚ)) (x : Fin 6 → ℚ) :
    f x = ∑ i, x i * f (Pi.single i 1) := by
  have hx : x = ∑ i : Fin 6, x i • Pi.single i (1 : ℚ) := by
    ext j
    simp [Pi.single_apply, mul_ite]
  conv_lhs => rw [hx]
  simp

theorem primitive_integer6 (z : Fin 6 → ℤ) (hz : z ≠ 0) :
    ∃ (g : ℤ) (M a : Fin 6 → ℤ), g ≠ 0 ∧ M ≠ 0 ∧
      (∀ i, z i = g*M i) ∧ (∑ i, a i*M i) = 1 ∧ Ideal.span (Set.range M) = ⊤ := by
  let I : Ideal ℤ := Ideal.span (Set.range z)
  let g := Submodule.IsPrincipal.generator I
  have hdiv (i : Fin 6) : g ∣ z i :=
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

theorem primitive_normal6 (v : Fin 6 → Fin 6 → ℤ)
    (hv : LinearIndependent ℚ (fun j i => (v j i : ℚ))) :
    ∃ M a : Fin 6 → ℤ, M ≠ 0 ∧ (∑ i, a i*M i) = 1 ∧
      Ideal.span (Set.range M) = ⊤ ∧
      (∀ j : Fin 5, (∑ i, M i*v j.castSucc i) = 0) ∧
      LinearMap.ker (normalForm6 M) =
        Submodule.span ℚ (Set.range (fun j : Fin 5 => fun i => (v j.castSucc i : ℚ))) := by
  let u : Fin 6 → Fin 6 → ℚ := fun j i => (v j i : ℚ)
  let f := rationalFrameDual42 u hv 5
  obtain ⟨D,hD⟩ := IsLocalization.exist_integer_multiples_of_finite
    (nonZeroDivisors ℤ) (fun i : Fin 6 => f (Pi.single i 1))
  have hDn : (D : ℤ) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp D.property
  have hDQ : ((D : ℤ) : ℚ) ≠ 0 := by exact_mod_cast hDn
  have hcoords : ∀ i : Fin 6, ∃ z : ℤ, (z : ℚ) = ((D : ℤ) : ℚ)*f (Pi.single i 1) := by
    intro i
    obtain ⟨z,hz⟩ := hD i
    exact ⟨z,by simpa only [Algebra.smul_def,map_intCast] using hz⟩
  choose z hz using hcoords
  have hzf : normalForm6 z = ((D : ℤ) : ℚ) • f := by
    apply LinearMap.ext
    intro x
    rw [normalForm6_apply,LinearMap.smul_apply,smul_eq_mul,functional_coordinates6 f x,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [hz i]
    ring
  have hzn : z ≠ 0 := by
    intro he
    have heq := congrArg (fun F : Module.Dual ℚ (Fin 6 → ℚ) => F (u 5)) hzf
    have hp : f (u 5) = 1 := by simpa using rationalFrameDual42_pairing u hv 5 5
    rw [he] at heq
    simp only [normalForm6_apply,Pi.zero_apply,Int.cast_zero,zero_mul,
      Finset.sum_const_zero,LinearMap.smul_apply,smul_eq_mul,hp,if_pos rfl,mul_one] at heq
    exact hDQ heq.symm
  obtain ⟨g,M,a,hg,hMn,hscale,ha,hprimitive⟩ := primitive_integer6 z hzn
  have hgQ : (g : ℚ) ≠ 0 := by exact_mod_cast hg
  have hzM : normalForm6 z = (g : ℚ) • normalForm6 M := by
    apply LinearMap.ext
    intro x
    rw [normalForm6_apply,LinearMap.smul_apply,normalForm6_apply,smul_eq_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [hscale i]
    push_cast
    ring
  have hker : LinearMap.ker (normalForm6 M) = LinearMap.ker f := by
    calc
      _ = LinearMap.ker (normalForm6 z) := by rw [hzM,LinearMap.ker_smul _ _ hgQ]
      _ = _ := by rw [hzf,LinearMap.ker_smul _ _ hDQ]
  have hk : LinearMap.ker (normalForm6 M) = firstFiveSpan42 u :=
    hker.trans (lastDual42_kernel u hv)
  refine ⟨M,a,hMn,ha,hprimitive,?_,hk⟩
  intro j
  have hm : u j.castSucc ∈ LinearMap.ker (normalForm6 M) := by
    rw [hk]
    exact Submodule.subset_span (Set.mem_range_self j)
  have hmQ : (∑ i, (M i : ℚ)*(v j.castSucc i : ℚ)) = 0 := by
    exact (normalForm6_apply M (u j.castSucc)).symm.trans hm
  exact_mod_cast hmQ


def realNormalForm6 (M : Fin 6 → ℤ) : Module.Dual ℝ (Fin 6 → ℝ) :=
  ∑ i, (M i : ℝ) • LinearMap.proj i

theorem realNormalForm6_apply (M : Fin 6 → ℤ) (x : Fin 6 → ℝ) :
    realNormalForm6 M x = ∑ i, (M i : ℝ)*x i := by
  simp [realNormalForm6]

theorem real_normal_kernel6 (v : Fin 6 → Fin 6 → ℤ)
    (hv : LinearIndependent ℝ (fun j i => (v j i : ℝ)))
    (M : Fin 6 → ℤ) (hM : M ≠ 0)
    (hann : ∀ j : Fin 5, (∑ i, M i*v j.castSucc i) = 0) :
    LinearMap.ker (realNormalForm6 M) =
      firstFiveSpan42 (fun j i => (v j i : ℝ)) := by
  let u : Fin 6 → Fin 6 → ℝ := fun j i => (v j i : ℝ)
  let b := basisOfPiSpaceOfLinearIndependent hv
  have hb (i : Fin 6) : b i = u i := congrFun (coe_basisOfPiSpaceOfLinearIndependent hv) i
  have hf (j : Fin 5) : realNormalForm6 M (u j.castSucc) = 0 := by
    rw [realNormalForm6_apply]
    change (∑ i, (M i : ℝ)*(v j.castSucc i : ℝ)) = 0
    exact_mod_cast hann j
  have hfn : realNormalForm6 M ≠ 0 := by
    intro hz
    apply hM
    funext i
    have he := congrArg (fun f : Module.Dual ℝ (Fin 6 → ℝ) => f (Pi.single i 1)) hz
    have hi : (M i : ℝ) = 0 := by simpa [realNormalForm6,Pi.single_apply] using he
    exact_mod_cast hi
  have hlast : realNormalForm6 M (u 5) ≠ 0 := by
    intro hz
    apply hfn
    apply b.ext
    intro j
    rw [hb]
    refine Fin.lastCases ?_ (fun i => ?_) j
    · exact hz
    · exact hf i
  have hvalue (x : Fin 6 → ℝ) :
      realNormalForm6 M x = b.repr x 5 * realNormalForm6 M (u 5) := by
    conv_lhs => rw [← b.sum_repr x]
    rw [map_sum,Fin.sum_univ_castSucc]
    simp only [map_smul,hb,hf,smul_zero,Finset.sum_const_zero,zero_add]
    rfl
  apply le_antisymm
  · intro x hx
    have hz : b.repr x 5 = 0 := (mul_eq_zero.mp ((hvalue x).symm.trans hx)).resolve_right hlast
    have he := b.sum_repr x
    rw [Fin.sum_univ_castSucc,show Fin.last 5 = (5 : Fin 6) from rfl,hz,zero_smul,add_zero] at he
    rw [← he]
    apply Submodule.sum_mem
    intro j _
    apply Submodule.smul_mem
    rw [hb]
    exact Submodule.subset_span ⟨j,rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨j,rfl⟩
    exact hf j

theorem actual_block_normals6 {V : Type*} (w : V → Fin 6 → Fin 6 → ℤ)
    (hw : ∀ q, LinearIndependent ℝ (fun j i => (w q j i : ℝ)))
    {m : ℕ} (t : Fin m → V) :
    ∃ M a : Fin m → Fin 6 → ℤ, ∀ h,
      M h ≠ 0 ∧ (∑ i, a h i*M h i) = 1 ∧ Ideal.span (Set.range (M h)) = ⊤ ∧
      (∀ j : Fin 5, (∑ i, M h i*w (t h) j.castSucc i) = 0) ∧
      LinearMap.ker (normalForm6 (M h)) = firstFiveSpan42 (fun j i => (w (t h) j i : ℚ)) ∧
      LinearMap.ker (realNormalForm6 (M h)) = firstFiveSpan42 (fun j i => (w (t h) j i : ℝ)) := by
  have hex (h : Fin m) := primitive_normal6 (w (t h))
    ((integer6_independent_iff42 _).mpr (hw (t h)))
  choose M a hM ha hspan hann hker using hex
  exact ⟨M,a,fun h => ⟨hM h,ha h,hspan h,hann h,hker h,
    real_normal_kernel6 _ (hw (t h)) _ (hM h) (hann h)⟩⟩


theorem hermite_univariate6 {K : Type*} [Field K] (P : Polynomial K)
    (S : Finset K) (t r : ℕ) (hdeg : P.natDegree ≤ r)
    (hsize : r < S.card*(t+1))
    (hzero : ∀ a ∈ S, ∀ j ≤ t, (Polynomial.hasseDeriv j P).eval a = 0) : P = 0 := by
  classical
  by_contra hP
  have hdiv (a : K) (ha : a ∈ S) :
      (Polynomial.X-Polynomial.C a)^(t+1) ∣ P := by
    rw [Polynomial.X_sub_C_pow_dvd_iff,Polynomial.X_pow_dvd_iff]
    intro j hj
    exact (Polynomial.taylor_coeff a P j).trans (hzero a ha j (by omega))
  have hprod : (∏ a ∈ S, (Polynomial.X-Polynomial.C a)^(t+1)) ∣ P := by
    apply Finset.prod_dvd_of_coprime
    · intro a ha b hb hab
      exact (Polynomial.pairwise_coprime_X_sub_C (Function.injective_id) hab).pow
    · exact hdiv
  have hmonic (a : K) (_ : a ∈ S) :
      ((Polynomial.X-Polynomial.C a)^(t+1)).Monic := (Polynomial.monic_X_sub_C a).pow _
  have hd := Polynomial.natDegree_le_of_dvd hprod hP
  rw [Polynomial.natDegree_prod_of_monic _ _ hmonic] at hd
  simp only [Polynomial.natDegree_pow,Polynomial.natDegree_X_sub_C,one_mul,mul_one,
    Finset.sum_const,smul_eq_mul] at hd
  omega


theorem hermite_sizes6 (eta : ℝ) (heta : 0 < eta) (r : ℕ) (hr : 0 < r) :
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

theorem additional_weight6 {m : ℕ} (r : Fin m → ℕ) (hr : ∀ h, 0 < r h)
    (eta : ℝ) (heta : 0 < eta) (K : Vars6 m →₀ ℕ)
    (hK : ∀ h, (∑ i : Fin 6, K (h,i)) ≤ Nat.floor ((r h : ℝ)*eta)) :
    rothSourceDerivativeWeight r K ≤ (m : ℝ)*eta := by
  unfold rothSourceDerivativeWeight
  calc
    _ ≤ ∑ h : Fin m, eta := by
      apply Finset.sum_le_sum
      intro h _
      apply (div_le_iff₀ (show (0 : ℝ) < r h by exact_mod_cast hr h)).mpr
      have hk : (∑ i : Fin 6, (K (h,i) : ℝ)) ≤ (Nat.floor ((r h : ℝ)*eta) : ℝ) := by
        exact_mod_cast hK h
      exact hk.trans (by simpa [mul_comm] using Nat.floor_le (le_of_lt (mul_pos (by exact_mod_cast hr h) heta)))
    _ = _ := by simp

theorem additional_cutoff6 {m : ℕ} (r : Fin m → ℕ) (hr : ∀ h, 0 < r h)
    (eta : ℝ) (heta : 0 < eta) (J K : Vars6 m →₀ ℕ)
    (hJ : rothSourceDerivativeWeight r J < (m : ℝ)*eta)
    (hK : ∀ h, (∑ i : Fin 6, K (h,i)) ≤ Nat.floor ((r h : ℝ)*eta)) :
    rothSourceDerivativeWeight r (K+J) < 2*eta*m := by
  rw [rothSource_weight_add]
  have hk := additional_weight6 r hr eta heta K hK
  nlinarith

theorem hasse_grid_composition6 {m : ℕ} (P : MvPolynomial (Vars6 m) ℤ)
    (J K : Vars6 m →₀ ℕ) (x : Fin m → Fin 6 → ℤ)
    (hz : integerValue (K+J) P x = 0) :
    integerValue K (derivative6 J P) x = 0 := by
  apply Int.cast_injective (α := ℚ)
  rw [Int.cast_zero,integerValue_cast,derivative6_map,rothSource_derivative_comp]
  rw [MvPolynomial.smul_eq_C_mul,map_mul,MvPolynomial.eval_C,← integerValue_cast, hz]
  simp


def normalPolynomial6 {m : ℕ} (M : Fin m → Fin 6 → ℤ) (h : Fin m) :
    MvPolynomial (Vars6 m) ℝ := ∑ i, MvPolynomial.C (M h i : ℝ)*MvPolynomial.X (h,i)

def sourceNormalIdeal6 {m : ℕ} (M : Fin m → Fin 6 → ℤ) (r : Fin m → ℕ) (c : ℝ) :
    Ideal (MvPolynomial (Vars6 m) ℝ) :=
  Ideal.span {F | ∃ i : Fin m → ℕ, c ≤ ∑ h, (i h : ℝ)/(r h : ℝ) ∧
    F = ∏ h, (normalPolynomial6 M h)^(i h)}

theorem source_actual_normal_grid6 (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L) (c0 c2 c3 : Fin 4 → ℝ)
    (V : Set ℝ) (hQV : ∀ q ∈ V, 1 < q)
    (hs : SourceBlocks.sourceBlockVanishing42 A2 A3 L hL c0 c2 c3 V hQV) :
    ∃ w : (q : V) → Fin 6 → directCompoundGroup42 A2 A3 q.val c2 c3,
    ∃ M a : V → Fin 6 → ℤ,
      (∀ q, M q ≠ 0 ∧ (∑ i, a q i*M q i) = 1 ∧
        Ideal.span (Set.range (M q)) = ⊤ ∧
        (∀ j : Fin 5, (∑ i, M q i*(w q j.castSucc : Fin 6 → ℤ) i) = 0) ∧
        LinearMap.ker (normalForm6 (M q)) =
          firstFiveSpan42 (fun j i => ((w q j : Fin 6 → ℤ) i : ℚ)) ∧
        LinearMap.ker (realNormalForm6 (M q)) =
          firstFiveSpan42 (fun j i => ((w q j : Fin 6 → ℤ) i : ℝ))) ∧
    ∃ eta : ℝ, 0 < eta ∧ eta < 1 ∧ ∃ m : ℕ, 0 < m ∧
    ∀ rho : ℝ, 0 < rho →
    ∃ t : Fin m → V, StrictMono (fun h => (t h).val) ∧
    ∃ r : Fin m → ℕ, (∀ h, 0 < r h) ∧
    ∃ P : MvPolynomial (Vars6 m) ℤ, P ≠ 0 ∧ homogeneous6 r P ∧
      (∀ a : Fin m → Fin 5 → ℕ, (∀ h j, 1 ≤ a h j ∧ a h j ≤ Nat.floor eta⁻¹+1) →
        ∀ J : Vars6 m →₀ ℕ, rothSourceDerivativeWeight r J < 2*eta*m →
        integerValue J P (gridPoint (fun h j => (w (t h) j.castSucc : Fin 6 → ℤ)) a) = 0) ∧
      (∀ a : Fin m → Fin 5 → ℕ, (∀ h j, 1 ≤ a h j ∧ a h j ≤ Nat.floor eta⁻¹+1) →
        ∀ J K : Vars6 m →₀ ℕ, rothSourceDerivativeWeight r J < (m : ℝ)*eta →
        (∀ h, (∑ i : Fin 6, K (h,i)) ≤ Nat.floor ((r h : ℝ)*eta)) →
        integerValue K (derivative6 J P)
          (gridPoint (fun h j => (w (t h) j.castSucc : Fin 6 → ℤ)) a) = 0) := by
  rcases hs with ⟨delta,hd,hd1,c,hc,hbal,hfin,sigma,hW,w,hw,K,hK,hmem,D,E,hD,hE,
    eta,heta,heta1,hetad,m,hm,hmb,hblocks⟩
  have hex (q : V) := primitive_normal6 (fun j => (w q j : Fin 6 → ℤ))
    ((integer6_independent_iff42 _).mpr (hw q).1)
  choose M a hM ha hspan hann hker using hex
  refine ⟨w,M,a,?_,eta,heta,heta1,m,hm,?_⟩
  · intro q
    exact ⟨hM q,ha q,hspan q,hann q,hker q,
      real_normal_kernel6 _ (hw q).1 _ (hM q) (hann q)⟩
  · intro rho hrho
    obtain ⟨t,ht,hfinite,hgrowth,hsep,h0,r,hr,hlog,hA,hdegree,hbalance,P,hP,hhom,
      hheight,hfield,hreal,hclaims,hcoeff,hgrid⟩ := hblocks rho hrho
    refine ⟨t,ht,r,hr,P,hP,hhom,hgrid,?_⟩
    intro a ha J K hJ hOrders
    exact hasse_grid_composition6 P J K _
      (hgrid a ha (K+J) (additional_cutoff6 r hr eta heta J K hJ hOrders))

end CompoundFeasibility.SourceNormalIndex
