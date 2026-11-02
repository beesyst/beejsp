import SubspaceBridge.RestrictedRealBody4
import SubspaceBridge.RestrictedFiniteBound4
open scoped BigOperators Matrix
open MeasureTheory
namespace CompoundFeasibility.RestrictedOpposite4
open RestrictedGeometry4 RestrictedRelaxed4 RestrictedWeightOrder4 SelectedRestriction4
open RestrictedRealBody4 RestrictedFiniteBound4 RestrictedCovolumeOrder4
noncomputable section

theorem selectedLocalGroup4_rpow_spec {d : ℕ} (p : ℕ) [Fact p.Prime]
    (A : Matrix (Fin 4) (Fin 4) ℚ) (Q : ℝ) (hQ : 1 < Q) (c : Fin 4 → ℝ)
    (hc : ∀ i, c i ≤ 0) (s : Fin d → Fin 4) (z : Fin 4 → ℤ) :
    z ∈ selectedLocalGroup4 p A Q c s ↔
      ∀ k, (padicNorm p ((A *ᵥ (fun i => (z i : ℚ))) (s k)) : ℝ) ≤ Q^(c (s k)) := by
  simp only [selectedLocalGroup4,AddSubgroup.mem_iInf,AddSubgroup.mem_comap]
  exact forall_congr' (fun k => (padic_rpow_ceil42 p Q (c (s k)) hQ (hc _) _).symm)

def oppositePoint4 (P : Submodule ℚ (Fin 4 → ℚ)) (hP : Module.finrank ℚ P ≤ 3)
    (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ)
    (h₂ : A₂.det = 1) (h₃ : A₃.det = 1) (hL : L.det = 1)
    (c₀ c₂ c₃ : Fin 4 → ℝ) (Q K : ℝ) : Prop :=
  let s₀ := realSelection4 P hP L hL c₀
  let s₂ := finiteSelection4 P A₂ h₂ c₂
  let s₃ := finiteSelection4 P A₃ h₃ c₃
  let G := relaxedLattice4 P A₂ A₃ Q c₂ c₃ s₂ s₃
  let C := relaxedBody4 P L Q c₀ s₀
  restrictedBody4 P L Q c₀ ⊆ C ∧
  restrictedLattice4 P A₂ A₃ Q c₂ c₃ ≤ G ∧
  IsCompact C ∧ Convex ℝ C ∧ (0 : rationalRealSpan4 P) ∈ interior C ∧
  0 < (restrictedMeasure4 P).real C ∧ (restrictedMeasure4 P) C < ⊤ ∧
  Module.finrank ℤ G = Module.finrank ℚ P ∧
  0 < ZLattice.covolume G (restrictedMeasure4 P) ∧
  ZLattice.covolume G (restrictedMeasure4 P) ≤
    ZLattice.covolume (restrictedLattice4 P A₂ A₃ Q c₂ c₃) (restrictedMeasure4 P) ∧
  (∀ z : Fin 4 → ℤ, z ∈ selectedSourceGroup4 A₂ A₃ Q c₂ c₃ s₂ s₃ ↔
    (∀ k, (padicNorm 2 ((A₂ *ᵥ (fun i => (z i : ℚ))) (s₂ k)) : ℝ) ≤ Q^(c₂ (s₂ k))) ∧
    (∀ k, (padicNorm 3 ((A₃ *ᵥ (fun i => (z i : ℚ))) (s₃ k)) : ℝ) ≤ Q^(c₃ (s₃ k)))) ∧
  (restrictedMeasure4 P).real (restrictedBody4 P L Q c₀) /
    ZLattice.covolume (restrictedLattice4 P A₂ A₃ Q c₂ c₃) (restrictedMeasure4 P) ≤
      (restrictedMeasure4 P).real C / ZLattice.covolume G (restrictedMeasure4 P) ∧
  (restrictedMeasure4 P).real C / ZLattice.covolume G (restrictedMeasure4 P) ≤
    K * Q^(sourceSelectedExponent4 P hP A₂ A₃ L h₂ h₃ hL c₀ c₂ c₃) ∧
  (restrictedMeasure4 P).real (restrictedBody4 P L Q c₀) /
    ZLattice.covolume (restrictedLattice4 P A₂ A₃ Q c₂ c₃) (restrictedMeasure4 P) ≤
      K * Q^(sourceSelectedExponent4 P hP A₂ A₃ L h₂ h₃ hL c₀ c₂ c₃)

theorem source_restricted_opposite_uniform4 (P : Submodule ℚ (Fin 4 → ℚ))
    (hP : Module.finrank ℚ P ≤ 3) (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (h₂ : A₂.det = 1) (h₃ : A₃.det = 1) (hL : L.det = 1)
    (c₀ c₂ c₃ : Fin 4 → ℝ) (hc₂ : ∀ i, c₂ i ≤ 0) (hc₃ : ∀ i, c₃ i ≤ 0) :
    ∃ K : ℝ, 0 < K ∧ ∀ (Q : ℝ), 1 < Q → oppositePoint4 P hP A₂ A₃ L h₂ h₃ hL c₀ c₂ c₃ Q K := by
  obtain ⟨Kreal,hKreal,hreal⟩ := source_uniform_real_volume4 P hP L hL c₀
  obtain ⟨Kfinite,hKfinite,hfinite⟩ := source_finite_inverse_covolume4 P hP A₂ A₃ h₂ h₃ c₂ c₃
  refine ⟨Kreal*Kfinite,mul_pos hKreal hKfinite,?_⟩
  intro Q hQ
  let s₀ := realSelection4 P hP L hL c₀
  let s₂ := finiteSelection4 P A₂ h₂ c₂
  let s₃ := finiteSelection4 P A₃ h₃ c₃
  let G := relaxedLattice4 P A₂ A₃ Q c₂ c₃ s₂ s₃
  let C := relaxedBody4 P L Q c₀ s₀
  obtain ⟨hcompact,hconv,hinterior,hvol,hvolfinite⟩ := source_relaxed_body_geometry4 P hP L hL Q hQ c₀
  have hbody := restrictedBody4_subset_relaxed P L Q c₀ s₀
  have hlattice := restrictedLattice4_le_relaxed P A₂ A₃ Q c₂ c₃ s₂ s₃
  have hcov := relaxedLattice4_covolume_pos P A₂ A₃ Q c₂ c₃ s₂ s₃
  have hcovorder := covolume_antitone4 P _ _ hlattice
  have hvolorder := measureReal_mono (μ := restrictedMeasure4 P) hbody hvolfinite.ne
  have hratio : (restrictedMeasure4 P).real (restrictedBody4 P L Q c₀) /
      ZLattice.covolume (restrictedLattice4 P A₂ A₃ Q c₂ c₃) (restrictedMeasure4 P) ≤
      (restrictedMeasure4 P).real C / ZLattice.covolume G (restrictedMeasure4 P) := by
    calc
      _ ≤ (restrictedMeasure4 P).real C /
          ZLattice.covolume (restrictedLattice4 P A₂ A₃ Q c₂ c₃) (restrictedMeasure4 P) :=
        div_le_div_of_nonneg_right hvolorder (restrictedLattice4_covolume_pos P A₂ A₃ Q c₂ c₃).le
      _ ≤ _ := div_le_div_of_nonneg_left (measureReal_nonneg) hcov hcovorder
  have hQpos : 0 < Q := zero_lt_one.trans hQ
  have hupper : (restrictedMeasure4 P).real C / ZLattice.covolume G (restrictedMeasure4 P) ≤
      (Kreal*Kfinite) * Q^(sourceSelectedExponent4 P hP A₂ A₃ L h₂ h₃ hL c₀ c₂ c₃) := by
    calc
      _ = (restrictedMeasure4 P).real C * (1 / ZLattice.covolume G (restrictedMeasure4 P)) := by ring
      _ ≤ (restrictedMeasure4 P).real C *
          (Kfinite*Q^((∑ k, c₂ (s₂ k))+(∑ k, c₃ (s₃ k)))) :=
        mul_le_mul_of_nonneg_left (hfinite Q hQ) measureReal_nonneg
      _ = (Kreal*Q^(∑ k, c₀ (s₀ k))) *
          (Kfinite*Q^((∑ k, c₂ (s₂ k))+(∑ k, c₃ (s₃ k)))) := by rw [hreal Q hQ]
      _ = (Kreal*Kfinite) * (Q^(∑ k, c₀ (s₀ k)) * Q^((∑ k, c₂ (s₂ k))+(∑ k, c₃ (s₃ k)))) := by ring
      _ = _ := by
        rw [← Real.rpow_add hQpos]
        congr 2
        dsimp [sourceSelectedExponent4,s₀,s₂,s₃,realSelection4,finiteSelection4]
        ring
  refine ⟨hbody,hlattice,hcompact,hconv,hinterior,hvol,hvolfinite,
    relaxedLattice4_rank P hP A₂ A₃ Q c₂ c₃ s₂ s₃,hcov,hcovorder,?_,hratio,hupper,hratio.trans hupper⟩
  intro z
  change (z ∈ selectedLocalGroup4 2 A₂ Q c₂ s₂ ∧ z ∈ selectedLocalGroup4 3 A₃ Q c₃ s₃) ↔ _
  rw [selectedLocalGroup4_rpow_spec 2 A₂ Q hQ c₂ hc₂ s₂ z,
    selectedLocalGroup4_rpow_spec 3 A₃ Q hQ c₃ hc₃ s₃ z]

theorem source_finite_greedy_indices4 (P : Submodule ℚ (Fin 4 → ℚ))
    (A : Matrix (Fin 4) (Fin 4) ℚ) (hA : A.det = 1) (c : Fin 4 → ℝ) :
    let M := RestrictedRows4.rationalRowCoordinates4 P A
    let hf := RestrictedRows4.rationalRowCoordinates4_span P A hA
    let E := selectedIndex4 M c hf
    StrictMono E ∧ ∀ k : Fin (Module.finrank ℚ P),
      Module.finrank ℚ (Submodule.span ℚ (RestrictedGreedyRows4.rowPrefix4 (sortedRows4 M c) ((E k).val+1))) = k.val+1 ∧
      ∀ i : Fin 4, i < E k → Module.finrank ℚ (Submodule.span ℚ
        (RestrictedGreedyRows4.rowPrefix4 (sortedRows4 M c) (i.val+1))) ≤ k.val := by
  refine ⟨(selectedIndex4 _ c _).strictMono,?_⟩
  intro k
  exact RestrictedGreedyRanks4.greedyIndex4_first_rank_increase _
    (sortedRows4_span _ c (RestrictedRows4.rationalRowCoordinates4_span P A hA))
    (Module.finrank ℚ P) (by simp) k

theorem source_real_greedy_indices4 (P : Submodule ℚ (Fin 4 → ℚ)) (hP : Module.finrank ℚ P ≤ 3)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : L.det = 1) (c : Fin 4 → ℝ) :
    let M := realRestrictionCoordinates4 P hP L
    let hf := realRestrictionCoordinates4_span P hP L hL
    let E := selectedIndex4 M c hf
    StrictMono E ∧ ∀ k : Fin (Module.finrank ℚ P),
      Module.finrank ℝ (Submodule.span ℝ (RestrictedGreedyRows4.rowPrefix4 (sortedRows4 M c) ((E k).val+1))) = k.val+1 ∧
      ∀ i : Fin 4, i < E k → Module.finrank ℝ (Submodule.span ℝ
        (RestrictedGreedyRows4.rowPrefix4 (sortedRows4 M c) (i.val+1))) ≤ k.val := by
  refine ⟨(selectedIndex4 _ c _).strictMono,?_⟩
  intro k
  exact RestrictedGreedyRanks4.greedyIndex4_first_rank_increase _
    (sortedRows4_span _ c (realRestrictionCoordinates4_span P hP L hL))
    (Module.finrank ℚ P) (by simp) k

end
end CompoundFeasibility.RestrictedOpposite4
