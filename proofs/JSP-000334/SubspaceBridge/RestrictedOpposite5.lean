import SubspaceBridge.RestrictedRealBody5
import SubspaceBridge.RestrictedFiniteBound5
open scoped BigOperators Matrix
open MeasureTheory
namespace CompoundFeasibility.RestrictedOpposite5
open RestrictedGeometry5 RestrictedRelaxed5 RestrictedWeightOrder5 SelectedRestriction5
open RestrictedRealBody5 RestrictedFiniteBound5 RestrictedCovolumeOrder5
noncomputable section

theorem selectedLocalGroup5_rpow_spec {d : ℕ} (p : ℕ) [Fact p.Prime]
    (A : Matrix (Fin 5) (Fin 5) ℚ) (Q : ℝ) (hQ : 1 < Q) (c : Fin 5 → ℝ)
    (hc : ∀ i, c i ≤ 0) (s : Fin d → Fin 5) (z : Fin 5 → ℤ) :
    z ∈ selectedLocalGroup5 p A Q c s ↔
      ∀ k, (padicNorm p ((A *ᵥ (fun i => (z i : ℚ))) (s k)) : ℝ) ≤ Q^(c (s k)) := by
  simp only [selectedLocalGroup5,AddSubgroup.mem_iInf,AddSubgroup.mem_comap]
  exact forall_congr' (fun k => (padic_rpow_ceil42 p Q (c (s k)) hQ (hc _) _).symm)

def oppositePoint5 (P : Submodule ℚ (Fin 5 → ℚ)) (hP : Module.finrank ℚ P ≤ 4)
    (A₂ A₃ : Matrix (Fin 5) (Fin 5) ℚ) (L : Matrix (Fin 5) (Fin 5) ℝ)
    (h₂ : A₂.det = 1) (h₃ : A₃.det = 1) (hL : L.det = 1)
    (c₀ c₂ c₃ : Fin 5 → ℝ) (Q K : ℝ) : Prop :=
  let s₀ := realSelection5 P hP L hL c₀
  let s₂ := finiteSelection5 P A₂ h₂ c₂
  let s₃ := finiteSelection5 P A₃ h₃ c₃
  let G := relaxedLattice5 P A₂ A₃ Q c₂ c₃ s₂ s₃
  let C := relaxedBody5 P L Q c₀ s₀
  restrictedBody5 P L Q c₀ ⊆ C ∧
  restrictedLattice5 P A₂ A₃ Q c₂ c₃ ≤ G ∧
  IsCompact C ∧ Convex ℝ C ∧ (0 : rationalRealSpan5 P) ∈ interior C ∧
  0 < (restrictedMeasure5 P).real C ∧ (restrictedMeasure5 P) C < ⊤ ∧
  Module.finrank ℤ G = Module.finrank ℚ P ∧
  0 < ZLattice.covolume G (restrictedMeasure5 P) ∧
  ZLattice.covolume G (restrictedMeasure5 P) ≤
    ZLattice.covolume (restrictedLattice5 P A₂ A₃ Q c₂ c₃) (restrictedMeasure5 P) ∧
  (∀ z : Fin 5 → ℤ, z ∈ selectedSourceGroup5 A₂ A₃ Q c₂ c₃ s₂ s₃ ↔
    (∀ k, (padicNorm 2 ((A₂ *ᵥ (fun i => (z i : ℚ))) (s₂ k)) : ℝ) ≤ Q^(c₂ (s₂ k))) ∧
    (∀ k, (padicNorm 3 ((A₃ *ᵥ (fun i => (z i : ℚ))) (s₃ k)) : ℝ) ≤ Q^(c₃ (s₃ k)))) ∧
  (restrictedMeasure5 P).real (restrictedBody5 P L Q c₀) /
    ZLattice.covolume (restrictedLattice5 P A₂ A₃ Q c₂ c₃) (restrictedMeasure5 P) ≤
      (restrictedMeasure5 P).real C / ZLattice.covolume G (restrictedMeasure5 P) ∧
  (restrictedMeasure5 P).real C / ZLattice.covolume G (restrictedMeasure5 P) ≤
    K * Q^(sourceSelectedExponent5 P hP A₂ A₃ L h₂ h₃ hL c₀ c₂ c₃) ∧
  (restrictedMeasure5 P).real (restrictedBody5 P L Q c₀) /
    ZLattice.covolume (restrictedLattice5 P A₂ A₃ Q c₂ c₃) (restrictedMeasure5 P) ≤
      K * Q^(sourceSelectedExponent5 P hP A₂ A₃ L h₂ h₃ hL c₀ c₂ c₃)

theorem source_restricted_opposite_uniform5 (P : Submodule ℚ (Fin 5 → ℚ))
    (hP : Module.finrank ℚ P ≤ 4) (A₂ A₃ : Matrix (Fin 5) (Fin 5) ℚ)
    (L : Matrix (Fin 5) (Fin 5) ℝ) (h₂ : A₂.det = 1) (h₃ : A₃.det = 1) (hL : L.det = 1)
    (c₀ c₂ c₃ : Fin 5 → ℝ) (hc₂ : ∀ i, c₂ i ≤ 0) (hc₃ : ∀ i, c₃ i ≤ 0) :
    ∃ K : ℝ, 0 < K ∧ ∀ (Q : ℝ), 1 < Q → oppositePoint5 P hP A₂ A₃ L h₂ h₃ hL c₀ c₂ c₃ Q K := by
  obtain ⟨Kreal,hKreal,hreal⟩ := source_uniform_real_volume5 P hP L hL c₀
  obtain ⟨Kfinite,hKfinite,hfinite⟩ := source_finite_inverse_covolume5 P hP A₂ A₃ h₂ h₃ c₂ c₃
  refine ⟨Kreal*Kfinite,mul_pos hKreal hKfinite,?_⟩
  intro Q hQ
  let s₀ := realSelection5 P hP L hL c₀
  let s₂ := finiteSelection5 P A₂ h₂ c₂
  let s₃ := finiteSelection5 P A₃ h₃ c₃
  let G := relaxedLattice5 P A₂ A₃ Q c₂ c₃ s₂ s₃
  let C := relaxedBody5 P L Q c₀ s₀
  obtain ⟨hcompact,hconv,hinterior,hvol,hvolfinite⟩ := source_relaxed_body_geometry5 P hP L hL Q hQ c₀
  have hbody := restrictedBody5_subset_relaxed P L Q c₀ s₀
  have hlattice := restrictedLattice5_le_relaxed P A₂ A₃ Q c₂ c₃ s₂ s₃
  have hcov := relaxedLattice5_covolume_pos P A₂ A₃ Q c₂ c₃ s₂ s₃
  have hcovorder := covolume_antitone5 P _ _ hlattice
  have hvolorder := measureReal_mono (μ := restrictedMeasure5 P) hbody hvolfinite.ne
  have hratio : (restrictedMeasure5 P).real (restrictedBody5 P L Q c₀) /
      ZLattice.covolume (restrictedLattice5 P A₂ A₃ Q c₂ c₃) (restrictedMeasure5 P) ≤
      (restrictedMeasure5 P).real C / ZLattice.covolume G (restrictedMeasure5 P) := by
    calc
      _ ≤ (restrictedMeasure5 P).real C /
          ZLattice.covolume (restrictedLattice5 P A₂ A₃ Q c₂ c₃) (restrictedMeasure5 P) :=
        div_le_div_of_nonneg_right hvolorder (restrictedLattice5_covolume_pos P A₂ A₃ Q c₂ c₃).le
      _ ≤ _ := div_le_div_of_nonneg_left (measureReal_nonneg) hcov hcovorder
  have hQpos : 0 < Q := zero_lt_one.trans hQ
  have hupper : (restrictedMeasure5 P).real C / ZLattice.covolume G (restrictedMeasure5 P) ≤
      (Kreal*Kfinite) * Q^(sourceSelectedExponent5 P hP A₂ A₃ L h₂ h₃ hL c₀ c₂ c₃) := by
    calc
      _ = (restrictedMeasure5 P).real C * (1 / ZLattice.covolume G (restrictedMeasure5 P)) := by ring
      _ ≤ (restrictedMeasure5 P).real C *
          (Kfinite*Q^((∑ k, c₂ (s₂ k))+(∑ k, c₃ (s₃ k)))) :=
        mul_le_mul_of_nonneg_left (hfinite Q hQ) measureReal_nonneg
      _ = (Kreal*Q^(∑ k, c₀ (s₀ k))) *
          (Kfinite*Q^((∑ k, c₂ (s₂ k))+(∑ k, c₃ (s₃ k)))) := by rw [hreal Q hQ]
      _ = (Kreal*Kfinite) * (Q^(∑ k, c₀ (s₀ k)) * Q^((∑ k, c₂ (s₂ k))+(∑ k, c₃ (s₃ k)))) := by ring
      _ = _ := by
        rw [← Real.rpow_add hQpos]
        congr 2
        dsimp [sourceSelectedExponent5,s₀,s₂,s₃,realSelection5,finiteSelection5]
        ring
  refine ⟨hbody,hlattice,hcompact,hconv,hinterior,hvol,hvolfinite,
    relaxedLattice5_rank P hP A₂ A₃ Q c₂ c₃ s₂ s₃,hcov,hcovorder,?_,hratio,hupper,hratio.trans hupper⟩
  intro z
  change (z ∈ selectedLocalGroup5 2 A₂ Q c₂ s₂ ∧ z ∈ selectedLocalGroup5 3 A₃ Q c₃ s₃) ↔ _
  rw [selectedLocalGroup5_rpow_spec 2 A₂ Q hQ c₂ hc₂ s₂ z,
    selectedLocalGroup5_rpow_spec 3 A₃ Q hQ c₃ hc₃ s₃ z]

theorem source_finite_greedy_indices5 (P : Submodule ℚ (Fin 5 → ℚ))
    (A : Matrix (Fin 5) (Fin 5) ℚ) (hA : A.det = 1) (c : Fin 5 → ℝ) :
    let M := RestrictedRows5.rationalRowCoordinates5 P A
    let hf := RestrictedRows5.rationalRowCoordinates5_span P A hA
    let E := selectedIndex5 M c hf
    StrictMono E ∧ ∀ k : Fin (Module.finrank ℚ P),
      Module.finrank ℚ (Submodule.span ℚ (RestrictedGreedyRows5.rowPrefix5 (sortedRows5 M c) ((E k).val+1))) = k.val+1 ∧
      ∀ i : Fin 5, i < E k → Module.finrank ℚ (Submodule.span ℚ
        (RestrictedGreedyRows5.rowPrefix5 (sortedRows5 M c) (i.val+1))) ≤ k.val := by
  refine ⟨(selectedIndex5 _ c _).strictMono,?_⟩
  intro k
  exact RestrictedGreedyRanks5.greedyIndex5_first_rank_increase _
    (sortedRows5_span _ c (RestrictedRows5.rationalRowCoordinates5_span P A hA))
    (Module.finrank ℚ P) (by simp) k

theorem source_real_greedy_indices5 (P : Submodule ℚ (Fin 5 → ℚ)) (hP : Module.finrank ℚ P ≤ 4)
    (L : Matrix (Fin 5) (Fin 5) ℝ) (hL : L.det = 1) (c : Fin 5 → ℝ) :
    let M := realRestrictionCoordinates5 P hP L
    let hf := realRestrictionCoordinates5_span P hP L hL
    let E := selectedIndex5 M c hf
    StrictMono E ∧ ∀ k : Fin (Module.finrank ℚ P),
      Module.finrank ℝ (Submodule.span ℝ (RestrictedGreedyRows5.rowPrefix5 (sortedRows5 M c) ((E k).val+1))) = k.val+1 ∧
      ∀ i : Fin 5, i < E k → Module.finrank ℝ (Submodule.span ℝ
        (RestrictedGreedyRows5.rowPrefix5 (sortedRows5 M c) (i.val+1))) ≤ k.val := by
  refine ⟨(selectedIndex5 _ c _).strictMono,?_⟩
  intro k
  exact RestrictedGreedyRanks5.greedyIndex5_first_rank_increase _
    (sortedRows5_span _ c (realRestrictionCoordinates5_span P hP L hL))
    (Module.finrank ℚ P) (by simp) k

end
end CompoundFeasibility.RestrictedOpposite5
