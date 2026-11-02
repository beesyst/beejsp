import SubspaceBridge.SchmidtSatz11Conclusion6
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SchlickeweiDualVanishing6
open SourceNormalIndex SourceNormalHeight SourceProper6 SourceMixed6 SourceReadiness6
open Auxiliary6.SourceExpansion

def dualVector6 (v : Fin 6 → Fin 6 → ℤ)
    (hv : LinearIndependent ℚ (fun j i => (v j i : ℚ))) : Fin 6 → ℚ :=
  fun k => rationalFrameDual42 (fun j i => (v j i : ℚ)) hv 5 (Pi.single k 1)

theorem normal_dual6 (v : Fin 6 → Fin 6 → ℤ)
    (hv : LinearIndependent ℚ (fun j i => (v j i : ℚ))) (M : Fin 6 → ℤ)
    (hM : M ≠ 0) (hann : ∀ j : Fin 5, (∑ i, M i*v j.castSucc i) = 0) :
    ∃ a : ℚ, a ≠ 0 ∧
      normalForm6 M = a • rationalFrameDual42 (fun j i => (v j i : ℚ)) hv 5 ∧
      (∀ k, (M k : ℚ) = a*dualVector6 v hv k) ∧
      (∀ k, dualVector6 v hv k = a⁻¹*(M k : ℚ)) := by
  obtain ⟨a,ha,he⟩ := actual_normal_last_dual6 v hv M hM hann
  have hc (k) : (M k : ℚ) = a*dualVector6 v hv k := by
    have h := congrArg (fun f : Module.Dual ℚ (Fin 6 → ℚ) => f (Pi.single k 1)) he
    simpa [normalForm6,Pi.single_apply,dualVector6] using h
  refine ⟨a,ha,he,hc,?_⟩
  intro k
  rw [hc,← mul_assoc,inv_mul_cancel₀ ha,one_mul]

def rationalValue6 {K : Type*} [Field K] [Algebra ℚ K]
    (B : Matrix (Fin 6) (Fin 6) K) (D : Fin 6 → ℚ) (i : Fin 6) : K :=
  ∑ k, algebraMap ℚ K (D k)*cofactor6 B i k

theorem rationalValue6_scale {K : Type*} [Field K] [Algebra ℚ K]
    (B : Matrix (Fin 6) (Fin 6) K) (D : Fin 6 → ℚ) (a : ℚ) (i : Fin 6) :
    rationalValue6 B (fun k => a*D k) i = algebraMap ℚ K a*rationalValue6 B D i := by
  simp only [rationalValue6,map_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem local_zero6 {K : Type*} [Field K] [Algebra ℚ K]
    (B : Matrix (Fin 6) (Fin 6) K) (M : Fin 6 → ℤ) (D : Fin 6 → ℚ)
    (a : ℚ) (ha : a ≠ 0) (hscale : ∀ k, (M k : ℚ) = a*D k) (i : Fin 6) :
    cofactorValue6 B M i = 0 ↔ rationalValue6 B D i = 0 := by
  have hn : algebraMap ℚ K a ≠ 0 := (map_ne_zero (algebraMap ℚ K)).mpr ha
  have he : cofactorValue6 B M i = algebraMap ℚ K a*rationalValue6 B D i := by
    rw [← rationalValue6_scale]
    simp only [rationalValue6,cofactorValue6,← hscale,map_intCast]
  rw [he,mul_eq_zero,or_iff_right hn]

theorem real_zero6 (B : Matrix (Fin 6) (Fin 6) ℝ) (M : Fin 6 → ℤ) (D : Fin 6 → ℚ)
    (a : ℚ) (ha : a ≠ 0) (hscale : ∀ k, (M k : ℚ) = a*D k) (i : Fin 6) :
    ‖cofactorValue6 B M i‖ = 0 ↔ ‖rationalValue6 B D i‖ = 0 := by
  simpa only [norm_eq_zero] using local_zero6 B M D a ha hscale i

theorem padic_zero6 (p : ℕ) [Fact p.Prime] (B : Matrix (Fin 6) (Fin 6) ℚ_[p])
    (M : Fin 6 → ℤ) (D : Fin 6 → ℚ) (a : ℚ) (ha : a ≠ 0)
    (hscale : ∀ k, (M k : ℚ) = a*D k) (i : Fin 6) :
    ‖cofactorValue6 B M i‖ = 0 ↔ ‖rationalValue6 B D i‖ = 0 := by
  simpa only [norm_eq_zero] using local_zero6 B M D a ha hscale i

def dualNormProduct6 (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (D : Fin 6 → ℚ) (s : MixedIndex6) : ℝ :=
  ‖rationalValue6 (compound L) D (s 0)‖ *
  ‖rationalValue6 (finiteMatrix 2 A2) D (s 1)‖ *
  ‖rationalValue6 (finiteMatrix 3 A3) D (s 2)‖

theorem mixed_zero6 (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ)
    (M : Fin 6 → ℤ) (D : Fin 6 → ℚ) (a : ℚ) (ha : a ≠ 0)
    (hscale : ∀ k, (M k : ℚ) = a*D k) (s : MixedIndex6) :
    actualNormProduct6 A2 A3 L M s = 0 ↔ dualNormProduct6 A2 A3 L D s = 0 := by
  simp only [actualNormProduct6,dualNormProduct6,mul_eq_zero]
  rw [real_zero6 _ M D a ha hscale,padic_zero6 2 _ M D a ha hscale,padic_zero6 3 _ M D a ha hscale]

variable {A2 A3 : Matrix (Fin 4) (Fin 4) ℚ} {L : Matrix (Fin 4) (Fin 4) ℝ}
    {hL : IsUnit L} {c0 c2 c3 : Fin 4 → ℝ} {delta4 : ℝ} {V : Set ℝ}
    {hQV : ∀ q ∈ V, 1 < q}

def sourceFrameIndependent6 (R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV) (q : V) :
    LinearIndependent ℚ (fun j i => ((R.w q j : Fin 6 → ℤ) i : ℚ)) :=
  (integer6_independent_iff42 _).mpr (R.frames q).1

theorem source_normal_dual6 (R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV) (q : V) :
    ∃ a : ℚ, a ≠ 0 ∧
      normalForm6 (R.M q) = a • rationalFrameDual42
        (fun j i => ((R.w q j : Fin 6 → ℤ) i : ℚ)) (sourceFrameIndependent6 R q) 5 ∧
      (∀ k, (R.M q k : ℚ) = a*dualVector6 (fun j => (R.w q j : Fin 6 → ℤ)) (sourceFrameIndependent6 R q) k) ∧
      (∀ k, dualVector6 (fun j => (R.w q j : Fin 6 → ℤ)) (sourceFrameIndependent6 R q) k = a⁻¹*(R.M q k : ℚ)) := by
  exact normal_dual6 _ (sourceFrameIndependent6 R q) (R.M q)
    (R.normals q).1 (R.normals q).2.2.2.1

theorem source_dual_eventual_zero6 (R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV) :
    ∃ B : ℝ, (∀ q : V, B < q.val → ∀ s ∈ admissibleMixed6 R.c (R.delta/2),
      actualNormProduct6 A2 A3 L (R.M q) s = 0) ∧
      ∀ q : V, B < q.val →
        ∃ a : ℚ, a ≠ 0 ∧
          normalForm6 (R.M q) = a • rationalFrameDual42
            (fun j i => ((R.w q j : Fin 6 → ℤ) i : ℚ)) (sourceFrameIndependent6 R q) 5 ∧
          (∀ k, (R.M q k : ℚ) = a*dualVector6 (fun j => (R.w q j : Fin 6 → ℤ)) (sourceFrameIndependent6 R q) k) ∧
          (∀ k, dualVector6 (fun j => (R.w q j : Fin 6 → ℤ)) (sourceFrameIndependent6 R q) k = a⁻¹*(R.M q k : ℚ)) ∧
          ∀ s ∈ admissibleMixed6 R.c (R.delta/2),
            dualNormProduct6 A2 A3 L
              (dualVector6 (fun j => (R.w q j : Fin 6 → ℤ)) (sourceFrameIndependent6 R q)) s = 0 := by
  obtain ⟨B,hB⟩ := SchmidtSatz11Conclusion6.source_eventual_zero6 R
  refine ⟨B,hB,?_⟩
  intro q hq
  obtain ⟨a,ha,hform,hscale,hinverse⟩ := source_normal_dual6 R q
  refine ⟨a,ha,hform,hscale,hinverse,?_⟩
  intro s hs
  exact (mixed_zero6 A2 A3 L (R.M q) _ a ha hscale s).mp (hB q hq s hs)

def dualFormValue6 {K : Type*} [Field K] [Algebra ℚ K]
    (B : Matrix (Fin 6) (Fin 6) K) (D : Fin 6 → ℚ) (i : Fin 6) : K :=
  ∑ k, algebraMap ℚ K (D k)*B⁻¹.transpose i k

theorem cofactor_dualForm6 {K : Type*} [Field K] [Algebra ℚ K]
    (B : Matrix (Fin 6) (Fin 6) K) (hB : B.det = 1) (D : Fin 6 → ℚ) (i : Fin 6) :
    rationalValue6 B D i = dualFormValue6 B D i := by
  simp [rationalValue6,dualFormValue6,Matrix.inv_def,hB,cofactor6]


theorem dualFormValue6_det {K : Type*} [Field K] [Algebra ℚ K]
    (B : Matrix (Fin 6) (Fin 6) K) (D : Fin 6 → ℚ) (i : Fin 6) :
    dualFormValue6 B D i = B.det⁻¹ * rationalValue6 B D i := by
  simp only [dualFormValue6, rationalValue6, Matrix.inv_def, cofactor6,
    Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem dualFormValue6_zero {K : Type*} [Field K] [Algebra ℚ K]
    (B : Matrix (Fin 6) (Fin 6) K) (hB : B.det ≠ 0) (D : Fin 6 → ℚ) (i : Fin 6) :
    rationalValue6 B D i = 0 ↔ dualFormValue6 B D i = 0 := by
  rw [dualFormValue6_det, mul_eq_zero, or_iff_right (inv_ne_zero hB)]

theorem dualFormValue6_norm_zero {K : Type*} [NormedField K] [Algebra ℚ K]
    (B : Matrix (Fin 6) (Fin 6) K) (hB : B.det ≠ 0) (D : Fin 6 → ℚ) (i : Fin 6) :
    ‖rationalValue6 B D i‖ = 0 ↔ ‖dualFormValue6 B D i‖ = 0 := by
  simpa only [norm_eq_zero] using dualFormValue6_zero B hB D i

end CompoundFeasibility.SchlickeweiDualVanishing6
