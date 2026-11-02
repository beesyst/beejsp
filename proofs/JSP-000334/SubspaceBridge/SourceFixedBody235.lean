import SubspaceBridge.SourceFixedPowers235
import SubspaceBridge.SourceFixedCases235
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceFixedGeometry235
open SourceFixedArithmetic234 SourceSelectedUpper10 SourceGlobalSelected10
open SourceOriginalDual10 SourceSatz51Entry218 SourceLastDual231 SourceDualAnnihilation222

theorem integer_cast_real235 (v : Fin 10 → ℤ) :
    ratReal222 (fun i => (v i : ℚ)) = integerReal v := by
  funext i
  change ((v i : ℚ) : ℝ) = (v i : ℝ)
  simp only [Rat.cast_intCast]

theorem fixed_body235
    {A2 A3 : Matrix (Fin 10) (Fin 10) ℚ} {L : Matrix (Fin 10) (Fin 10) ℝ}
    {hL : IsUnit L} {q : ℝ} {hq : 1 < q} {c2 c3 A : Fin 10 → ℝ} {delta : ℝ}
    (h2d : A2.det = 1) (h3d : A3.det = 1) (h2 : IsUnit A2) (h3 : IsUnit A3)
    (hc2 : ∀ i, c2 i ≤ 0) (hc3 : ∀ i, c3 i ≤ 0)
    (D : SourceData218 A2 A3 L hL q hq c2 c3 A delta)
    (S : Finset (Fin 3 → Fin 10)) (hS : sourceSet218 q delta A c2 c3 = S)
    (v : Fin 10 → ℤ) (hv : v ≠ 0) (hz : ∀ s ∈ S, mixedProduct10 A2 A3 L v s = 0)
    (C : ℤ) (hC : 0 < C) (t : ℤ)
    (ht : t = C*2^((9-floorMin234 2 A2 h2 q c2 v hv).toNat)*
      3^((9-floorMin234 3 A3 h3 q c3 v hv).toNat))
    (hcut : ((C : ℝ)*2^10*3^10*(1+∑ j, |(L⁻¹.transpose *ᵥ integerReal v) j|))*
      q^(-delta/4) ≤ 1) :
    ratReal222 (fun i => ((t • v) i : ℚ)) ∈ dualBody222 L
      (ZLattice.covolume (integerRealImage (originalSourceGroup10 A2 A3 q c2 c3))) A := by
  rw [integer_cast_real235]
  intro i
  rw [real_coordinate_scale235,abs_mul,
    abs_of_pos (show (0 : ℝ) < t by exact_mod_cast (ht ▸ positive_scale235 C hC _ _))]
  by_cases hs : ∃ j2 ∈ dualSupport234 A2 v, ∃ j3 ∈ dualSupport234 A3 v, ![i,j2,j3] ∈ S
  · rw [selected_coordinate_zero235 A2 A3 h2 h3 L v S hz i hs,abs_zero,mul_zero]
    exact (div_pos (ZLattice.covolume_pos _ MeasureTheory.volume) (D.positive i)).le
  · obtain ⟨j2,hj2,j3,hj3,hbound⟩ := rescale_real_bound235 A2 A3 h2 h3 q hq c2 c3 hc2 hc3 v hv C hC t ht
    have hnot : ![i,j2,j3] ∉ S := fun he => hs ⟨j2,hj2,j3,hj3,he⟩
    have hsmall := (source_complement235 q delta hq A c2 c3 D.positive S hS i j2 j3 hnot).1
    have hb := complement_coordinate_bound235 q hq delta A c2 c3 D.positive D.balance
      (ZLattice.covolume (integerRealImage (originalSourceGroup10 A2 A3 q c2 c3)))
      (source_width_covolume231 h2d h3d D) ((C : ℝ)*2^10*3^10)
      ((L⁻¹.transpose *ᵥ integerReal v) i) (t : ℝ) (by positivity) i j2 j3 hbound hsmall
    have hcoeff := (coefficient_bound235 (fun j => (L⁻¹.transpose *ᵥ integerReal v) j)).2 i
    have hh := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hcoeff (show (0 : ℝ) ≤ (C : ℝ)*2^10*3^10 by positivity))
      (Real.rpow_pos_of_pos (zero_lt_one.trans hq) (-delta/4)).le
    have hfactor : (C : ℝ)*2^10*3^10*|(L⁻¹.transpose *ᵥ integerReal v) i| * q^(-delta/4) ≤ 1 :=
      hh.trans hcut
    have hw : 0 ≤ ZLattice.covolume
        (integerRealImage (originalSourceGroup10 A2 A3 q c2 c3))/A i :=
      (div_pos (ZLattice.covolume_pos _ MeasureTheory.volume) (D.positive i)).le
    calc
      _ ≤ _ := hb
      _ = ((C : ℝ)*2^10*3^10*|(L⁻¹.transpose *ᵥ integerReal v) i| * q^(-delta/4))*
          (ZLattice.covolume (integerRealImage (originalSourceGroup10 A2 A3 q c2 c3))/A i) := by ring
      _ ≤ _ := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hfactor hw

end CompoundFeasibility.SourceFixedGeometry235
