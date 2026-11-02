import SubspaceBridge.SourceShortLine226
import SubspaceBridge.SourceSecondRadius228
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceSecondMinimum229
open SourceDualGeometry219 SourceDualAnnihilation222 SourceSecondMinimum226 SourceSecondMinimum228

theorem real_short_pair229 (b : Basis (Fin 10) ℝ (Fin 10 → ℝ))
    (e : (Fin 10 → ℝ) ≃ₗ[ℝ] (Fin 10 → ℝ))
    (G : AddSubgroup (Fin 10 → ℤ)) (M : Fin 10 → ℤ)
    (hlat : (lattice10Span b : Set (Fin 10 → ℝ)) = ratReal222 '' scaledDual219 G)
    (hline : ∀ z ∈ scaledDual219 G, coordinateGauge10 e (ratReal222 z) ≤ 2 →
      z ∈ Submodule.span ℚ {fun i => (M i : ℚ)})
    (x y : Fin 10 → ℝ) (hx : x ∈ lattice10Span b) (hy : y ∈ lattice10Span b)
    (hgx : coordinateGauge10 e x ≤ 2) (hgy : coordinateGauge10 e y ≤ 2) :
    ¬ LinearIndependent ℝ (fun i : Fin 2 => if i = 0 then x else y) := by
  have hx' : x ∈ ratReal222 '' scaledDual219 G :=
    Eq.mp (congrArg (fun S : Set (Fin 10 → ℝ) => x ∈ S) hlat) hx
  have hy' : y ∈ ratReal222 '' scaledDual219 G :=
    Eq.mp (congrArg (fun S : Set (Fin 10 → ℝ) => y ∈ S) hlat) hy
  obtain ⟨z0, hz0, he0⟩ := hx'
  obtain ⟨z1, hz1, he1⟩ := hy'
  have hg0 : coordinateGauge10 e (ratReal222 z0) ≤ 2 := he0 ▸ hgx
  have hg1 : coordinateGauge10 e (ratReal222 z1) ≤ 2 := he1 ▸ hgy
  have hd := real_line_pair_dependent226 M z0 z1 (hline z0 hz0 hg0) (hline z1 hz1 hg1)
  have he : (fun i : Fin 2 => if i = 0 then ratReal222 z0 else ratReal222 z1) =
      (fun i : Fin 2 => if i = 0 then x else y) := by
    funext i
    rw [he0, he1]
  exact he ▸ hd

theorem second_radius_of_line229 (b : Basis (Fin 10) ℝ (Fin 10 → ℝ))
    (e : (Fin 10 → ℝ) ≃ₗ[ℝ] (Fin 10 → ℝ))
    (G : AddSubgroup (Fin 10 → ℤ)) (M : Fin 10 → ℤ)
    (hlat : (lattice10Span b : Set (Fin 10 → ℝ)) = ratReal222 '' scaledDual219 G)
    (hline : ∀ z ∈ scaledDual219 G, coordinateGauge10 e (ratReal222 z) ≤ 2 →
      z ∈ Submodule.span ℚ {fun i => (M i : ℚ)}) :
    2 ≤ successiveRadius10 b e (1 : Fin 10) := by
  exact second_radius_of_dependence228 b e (real_short_pair229 b e G M hlat hline)

end CompoundFeasibility.SourceSecondMinimum229
