import SubspaceBridge.SchmidtPolynomial10
import SubspaceBridge.SchmidtTaylorCorrespondence6
import SubspaceBridge.SchmidtHilfssatz12
open scoped BigOperators Classical Matrix
namespace CompoundFeasibility.SchmidtScalar10
open SchmidtNormal10 SchmidtPolynomial10 SourceNormalHighIndex10
open SchmidtRationalNormalization6 SchmidtTaylorCorrespondence6
noncomputable section

def binaryLift6 {m : ℕ} (M : Fin m → Fin 10 → ℤ) : Fin m → Fin 6 → ℤ :=
  fun h i => if i = 0 then M h 0 else if i = 1 then M h 1 else 0

theorem binaryLift6_zero {m : ℕ} (M : Fin m → Fin 10 → ℤ) (h : Fin m) :
    binaryLift6 M h 0 = M h 0 := by simp [binaryLift6]

theorem binaryLift6_one {m : ℕ} (M : Fin m → Fin 10 → ℤ) (h : Fin m) :
    binaryLift6 M h 1 = M h 1 := by simp [binaryLift6]

theorem scalarIdeal10_binary {m : ℕ} (M : Fin m → Fin 10 → ℤ) (r : Fin m → ℕ) (c : ℝ) :
    scalarIdeal10 M r c = SchmidtScalarDehomogenization6.scalarIdeal6 (binaryLift6 M) r c := by
  simp only [scalarIdeal10,SchmidtScalarDehomogenization6.scalarIdeal6,
    scalarNormal10,SchmidtScalarDehomogenization6.scalarNormal6,binaryLift6_zero,binaryLift6_one]

theorem scalarStrictIdeal10_binary {m : ℕ} (M : Fin m → Fin 10 → ℤ) (r : Fin m → ℕ) (c : ℝ) :
    scalarStrictIdeal10 M r c = SchmidtScalarDehomogenization6.scalarStrictIdeal6 (binaryLift6 M) r c := by
  simp only [scalarStrictIdeal10,SchmidtScalarDehomogenization6.scalarStrictIdeal6,
    scalarNormal10,SchmidtScalarDehomogenization6.scalarNormal6,binaryLift6_zero,binaryLift6_one]

theorem denominator_nat_bounds10 (a b : ℤ) (ha : a ≠ 0)
    (hb : Int.gcd a b^9 ≤ a.natAbs^8) :
    a.natAbs ≤ (rootDenominator6 a b).natAbs^9 ∧
      (rootDenominator6 a b).natAbs ≤ a.natAbs := by
  obtain ⟨hg,_,_,heq,_,_,_⟩ := integer_normalization6 a b ha
  have hA : a.natAbs = Int.gcd a b*(rootDenominator6 a b).natAbs := by
    simpa only [Int.natAbs_mul,Int.natAbs_natCast] using congrArg Int.natAbs heq
  have hmul : (Int.gcd a b)^8*Int.gcd a b ≤
      (Int.gcd a b)^8*(rootDenominator6 a b).natAbs^8 := by
    calc
      (Int.gcd a b)^8*Int.gcd a b = (Int.gcd a b)^9 := by ring
      _ ≤ a.natAbs^8 := hb
      _ = (Int.gcd a b*(rootDenominator6 a b).natAbs)^8 := congrArg (fun n : ℕ => n^8) hA
      _ = _ := by ring
  have hc : Int.gcd a b ≤ (rootDenominator6 a b).natAbs^8 :=
    Nat.le_of_mul_le_mul_left hmul (pow_pos hg 8)
  constructor
  · calc
      a.natAbs = Int.gcd a b*(rootDenominator6 a b).natAbs := hA
      _ ≤ (rootDenominator6 a b).natAbs^8*(rootDenominator6 a b).natAbs := Nat.mul_le_mul_right _ hc
      _ = (rootDenominator6 a b).natAbs^9 := by ring
  · calc
      (rootDenominator6 a b).natAbs = 1*(rootDenominator6 a b).natAbs := (one_mul _).symm
      _ ≤ Int.gcd a b*(rootDenominator6 a b).natAbs := Nat.mul_le_mul_right _ (by omega)
      _ = a.natAbs := hA.symm

theorem denominator_real_bounds10 (a b : ℤ) (ha : a ≠ 0)
    (hb : Int.gcd a b^9 ≤ a.natAbs^8) :
    |(a : ℝ)|^(1/9 : ℝ) ≤ |(rootDenominator6 a b : ℝ)| ∧
      |(rootDenominator6 a b : ℝ)| ≤ |(a : ℝ)| := by
  obtain ⟨hl,hu⟩ := denominator_nat_bounds10 a b ha hb
  have hlR : (a.natAbs : ℝ) ≤ ((rootDenominator6 a b).natAbs : ℝ)^9 := by exact_mod_cast hl
  have huR : ((rootDenominator6 a b).natAbs : ℝ) ≤ (a.natAbs : ℝ) := by exact_mod_cast hu
  have hp : |(a : ℝ)| ≤ |(rootDenominator6 a b : ℝ)|^9 := by
    simpa only [Int.cast_natAbs,Int.cast_abs] using hlR
  constructor
  · rw [one_div]
    apply (Real.rpow_inv_le_iff_of_pos (abs_nonneg _) (abs_nonneg _) (by norm_num : (0 : ℝ) < 9)).mpr
    exact hp.trans_eq (Real.rpow_natCast _ 9).symm
  · simpa only [Int.cast_natAbs,Int.cast_abs] using huR

theorem scalar_reduction10 {m : ℕ} (M : Fin m → Fin 10 → ℤ)
    (hM : ∀ h, M h 0 ≠ 0) (r : Fin m → ℕ)
    (P : MvPolynomial (SourceMultiblock10.Vars10 m) ℤ) (hP : homogeneous10 r P) (hn : P ≠ 0) :
    ∃ G : MvPolynomial (Fin m) ℤ, G ≠ 0 ∧ JSP000334.rothIntegerHeight G ≤ height10 P ∧
      (∀ h, G.degreeOf h ≤ r h) ∧
      (∀ c, P.map (Int.castRingHom ℝ) ∈ sourceNormalIdeal10 M r c →
        G.map (Int.castRingHom ℝ) ∈ monicIdeal6 (binaryLift6 M) r c) ∧
      (∀ c, P.map (Int.castRingHom ℝ) ∈ sourceStrictNormalIdeal10 M r c →
        G.map (Int.castRingHom ℝ) ∈ monicStrictIdeal6 (binaryLift6 M) r c) := by
  let F := reducedPolynomial10 P
  let G := scalar10 F
  have hFn : F ≠ 0 := reducedPolynomial10_nonzero P hn
  obtain ⟨hhom,hdeg⟩ := reducedPolynomial10_homogeneous P r hP hn
  have hbin : binarySupport10 F := reducedPolynomial10_support P
  have hG : G ≠ 0 := scalar10_nonzero _ F hhom hbin hFn
  have hH : JSP000334.rothIntegerHeight G ≤ height10 P :=
    (scalar10_height _ F hhom hbin).le.trans (reducedPolynomial10_height P)
  have hM6 (h) : binaryLift6 M h 0 ≠ 0 := by simpa only [binaryLift6_zero] using hM h
  refine ⟨G,hG,hH,?_,?_,?_⟩
  · intro h
    exact (scalar10_degree _ F hhom hbin h).trans (hdeg h)
  · intro c hPc
    rw [← scalarIdeal6_eq_monic (binaryLift6 M) hM6 r c,← scalarIdeal10_binary M r c]
    exact scalar10_closed M r c F (reducedPolynomial10_closed M hM r c P hn hPc)
  · intro c hPc
    rw [← scalarStrictIdeal6_eq_monic (binaryLift6 M) hM6 r c,← scalarStrictIdeal10_binary M r c]
    exact scalar10_strict M r c F (reducedPolynomial10_strict M hM r c P hn hPc)

end
end CompoundFeasibility.SchmidtScalar10
