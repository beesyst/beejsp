import SubspaceBridge.SourceSampleNormal10
import SubspaceBridge.SourceAuxiliaryPolynomial10
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceSampling10
open SourceMultiblock10 SourceNormalHighIndex10 SchmidtPolynomial10

structure OriginalSampleData10 (V : Set ℝ) (m : ℕ) where
  t : Fin m → V
  r : Fin m → ℕ
  w : Fin m → Fin 10 → Fin 10 → ℤ
  M : Fin m → Fin 10 → ℤ
  a : Fin m → Fin 10 → ℤ
  P : MvPolynomial (Vars10 m) ℤ

structure OriginalSampleConditions10
    (A2 A3 : Matrix (Fin 10) (Fin 10) ℚ) (L : Matrix (Fin 10) (Fin 10) ℝ)
    (c2 c3 : Fin 10 → ℝ) (V : Set ℝ) (v : V → Fin 10 → Fin 10 → ℤ)
    (c : Fin 3 → Fin 10 → ℝ) (epsilon eta D E B rho : ℝ) (m : ℕ) (hm : 0 < m) (S : OriginalSampleData10 V m) : Prop where
  increasing : StrictMono (fun h => (S.t h).val)
  large : ∀ h, B < (S.t h).val ∧ 1 < (S.t h).val ∧
    1 < (S.t h).val^5 ∧ 1060*E < ((S.t h).val^5)^eta ∧ 10*(eta⁻¹+1) < ((S.t h).val^5)^eta
  positive_degrees : ∀ h, 0 < S.r h
  degree_separation : ∀ (h : Fin m) (hh : h.val+1 < m),
    (S.r ⟨h.val+1,hh⟩ : ℝ) ≤ rho*(S.r h : ℝ)
  logarithmic_balance : ∀ h,
    (S.r ⟨0,hm⟩ : ℝ)*Real.log ((S.t ⟨0,hm⟩).val^5) ≤ (S.r h : ℝ)*Real.log ((S.t h).val^5) ∧
    (S.r h : ℝ)*Real.log ((S.t h).val^5) ≤ (1+eta)*((S.r ⟨0,hm⟩ : ℝ)*Real.log ((S.t ⟨0,hm⟩).val^5))
  member : ∀ h j, S.w h j ∈ originalSourceGroup10 A2 A3 (S.t h).val c2 c3
  independent : ∀ h, LinearIndependent ℝ (fun j => integerReal (S.w h j : Fin 10 → ℤ))
  original_flag : ∀ h, minimaFlag10 (fun j => integerReal (v (S.t h) j)) 9 =
    minimaFlag10 (fun j => integerReal (S.w h j : Fin 10 → ℤ)) 9
  real_bound : ∀ h (j : Fin 9) i,
    ‖(L *ᵥ integerReal (S.w h j.castSucc : Fin 10 → ℤ)) i‖ ≤ ((S.t h).val^5)^(c 0 i-epsilon)
  two_bound : ∀ h (j : Fin 9) i, ‖(SourceForms10.finiteMatrix10 2 A2 *ᵥ
    (fun k => ((S.w h j.castSucc : Fin 10 → ℤ) k : ℚ_[2]))) i‖ ≤ ((S.t h).val^5)^(c 1 i)
  three_bound : ∀ h (j : Fin 9) i, ‖(SourceForms10.finiteMatrix10 3 A3 *ᵥ
    (fun k => ((S.w h j.castSucc : Fin 10 → ℤ) k : ℚ_[3]))) i‖ ≤ ((S.t h).val^5)^(c 2 i)
  normal_nonzero : ∀ h, S.M h ≠ 0
  bezout : ∀ h, (∑ i, S.a h i*S.M h i) = 1
  primitive : ∀ h, Ideal.span (Set.range (S.M h)) = ⊤
  original_rational_kernel : ∀ h, LinearMap.ker (SchmidtNormal10.normalForm10 (S.M h)) =
    SchmidtNormal10.firstNineSpan10 (fun j i => (v (S.t h) j i : ℚ))
  original_real_kernel : ∀ h, LinearMap.ker (SchmidtNormal10.realNormalForm10 (S.M h)) =
    minimaFlag10 (fun j => integerReal (v (S.t h) j)) 9
  rational_kernel : ∀ h, LinearMap.ker (SchmidtNormal10.normalForm10 (S.M h)) =
    SchmidtNormal10.firstNineSpan10 (fun j i => ((S.w h j : Fin 10 → ℤ) i : ℚ))
  real_kernel : ∀ h, LinearMap.ker (SchmidtNormal10.realNormalForm10 (S.M h)) =
    minimaFlag10 (fun j => integerReal (S.w h j : Fin 10 → ℤ)) 9
  polynomial_nonzero : S.P ≠ 0
  homogeneous : homogeneous10 S.r S.P
  block_degrees : ∀ h, blockDegree10 S.P h = S.r h
  variable_degrees : ∀ u, S.P.degreeOf u ≤ S.r u.1
  height : (height10 S.P : ℝ) ≤ D^(∑ h, S.r h)
  grid : ∀ b : Fin m → Fin 9 → ℕ, (∀ h j, 1 ≤ b h j ∧ b h j ≤ Nat.floor eta⁻¹+1) →
    ∀ J : Vars10 m →₀ ℕ, rothSourceDerivativeWeight S.r J < 2*eta*m →
      integerValue J S.P (gridPoint (fun h j => (S.w h j.castSucc : Fin 10 → ℤ)) b) = 0
  rational_restrictions : ∀ J : Vars10 m →₀ ℕ, rothSourceDerivativeWeight S.r J < (m : ℝ)*eta →
    ∀ y : Fin m → Fin 10 → ℚ, (∀ h, y h ∈ LinearMap.ker (SchmidtNormal10.normalForm10 (S.M h))) →
      MvPolynomial.eval (fun u => y u.1 u.2) (derivative10 J (S.P.map (Int.castRingHom ℚ))) = 0
  real_restrictions : ∀ J : Vars10 m →₀ ℕ, rothSourceDerivativeWeight S.r J < (m : ℝ)*eta →
    ∀ y : Fin m → Fin 10 → ℝ, (∀ h, y h ∈ LinearMap.ker (SchmidtNormal10.realNormalForm10 (S.M h))) →
      MvPolynomial.eval (fun u => y u.1 u.2) (derivative10 J (S.P.map (Int.castRingHom ℝ))) = 0
  normal_ideal : S.P.map (Int.castRingHom ℝ) ∈ SchmidtNormal10.sourceNormalIdeal10 S.M S.r ((m : ℝ)*eta)

structure OriginalAuxiliarySample10
    (A2 A3 : Matrix (Fin 10) (Fin 10) ℚ) (L : Matrix (Fin 10) (Fin 10) ℝ)
    (c2 c3 : Fin 10 → ℝ) (V : Set ℝ) (v : V → Fin 10 → Fin 10 → ℤ)
    (c : Fin 3 → Fin 10 → ℝ) (epsilon eta D E B rho : ℝ) (m : ℕ) (hm : 0 < m) where
  data : OriginalSampleData10 V m
  conditions : OriginalSampleConditions10 A2 A3 L c2 c3 V v c epsilon eta D E B rho m hm data

end CompoundFeasibility.SourceSampling10
