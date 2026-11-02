import SubspaceBridge.SourceSampleAbsolute10
import SubspaceBridge.OriginalDual10
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourcePrimitiveHeight10
open SchmidtNormal10 OriginalDual10

theorem primitive_original_cofactor_factor10 (v : Matrix (Fin 10) (Fin 10) ℤ)
    (hv : LinearIndependent ℚ (fun j i => (v j i : ℚ))) (M a : Fin 10 → ℤ)
    (hM : M ≠ 0) (ha : (∑ i, a i*M i) = 1)
    (hann : ∀ j : Fin 9, (∑ i, M i*v j.castSucc i) = 0) :
    let g : ℤ := ∑ i, a i*integerLastDual10 v i
    g ≠ 0 ∧ (∀ i, integerLastDual10 v i = g*M i) ∧
      ∀ d : ℤ, (∀ i, d ∣ integerLastDual10 v i) ↔ d ∣ g := by
  let u : Fin 10 → Fin 10 → ℚ := fun j i => (v j i : ℚ)
  let b := basisOfPiSpaceOfLinearIndependent hv
  have hb (j : Fin 10) : b j = u j := congrFun (coe_basisOfPiSpaceOfLinearIndependent hv) j
  let Z := integerLastDual10 v
  have hZ (j : Fin 10) : normalForm10 Z (u j) =
      if j = 9 then (v.det : ℚ) else 0 := by
    have hh := integerLastDual10_pairing_fin10 v j
    have hq : (∑ i, (v j i : ℚ)*(integerLastDual10 v i : ℚ)) =
        if j = Fin.last 9 then (v.det : ℚ) else 0 := by exact_mod_cast hh
    simpa only [normalForm10_apply,u,Z,mul_comm] using hq
  have hMj (j : Fin 9) : normalForm10 M (u j.castSucc) = 0 := by
    change (∑ i, (M i : ℚ)*(v j.castSucc i : ℚ)) = 0
    exact_mod_cast hann j
  have ht : normalForm10 M (u 9) ≠ 0 := by
    intro hz
    have hf : normalForm10 M = 0 := by
      apply b.ext
      intro j
      rw [hb]
      refine Fin.lastCases ?_ (fun i => ?_) j
      · exact hz
      · exact hMj i
    apply hM
    funext i
    have hh := congrArg (fun f : Module.Dual ℚ (Fin 10 → ℚ) => f (Pi.single i 1)) hf
    have hi : (M i : ℚ) = 0 := by simpa [normalForm10,Pi.single_apply] using hh
    exact_mod_cast hi
  let t : ℚ := (v.det : ℚ)/normalForm10 M (u 9)
  have hforms : normalForm10 Z = t • normalForm10 M := by
    apply b.ext
    intro j
    rw [hb,hZ]
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simp only [show Fin.last 9 = (9 : Fin 10) from rfl,ite_true,LinearMap.smul_apply,smul_eq_mul]
      exact (div_mul_cancel₀ _ ht).symm
    · have hi : i.castSucc ≠ (9 : Fin 10) := by intro h; have := congrArg Fin.val h; change i.val = 9 at this; omega
      rw [if_neg hi,LinearMap.smul_apply,hMj,smul_zero]
  have hcoord (i : Fin 10) : (Z i : ℚ) = t*(M i : ℚ) := by
    have hh := congrArg (fun f : Module.Dual ℚ (Fin 10 → ℚ) => f (Pi.single i 1)) hforms
    simpa [normalForm10,Pi.single_apply] using hh
  let g : ℤ := ∑ i, a i*Z i
  have hgQ : (g : ℚ) = t := by
    have haQ : (∑ i, (a i : ℚ)*(M i : ℚ)) = 1 := by exact_mod_cast ha
    calc
      (g : ℚ) = ∑ i, (a i : ℚ)*(Z i : ℚ) := by simp [g]
      _ = t*(∑ i, (a i : ℚ)*(M i : ℚ)) := by
        simp only [hcoord,Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = t := by rw [haQ,mul_one]
  have hscale (i : Fin 10) : Z i = g*M i := by
    have hh : (Z i : ℚ) = (g : ℚ)*(M i : ℚ) := by rw [hgQ]; exact hcoord i
    exact_mod_cast hh
  have hg : g ≠ 0 := by
    intro hz
    apply integerLastDual10_nonzero v hv
    funext i
    change Z i = 0
    rw [hscale,hz,zero_mul]
  refine ⟨hg,hscale,?_⟩
  intro d
  constructor
  · intro hd
    exact Finset.dvd_sum (fun i _ => dvd_mul_of_dvd_right (hd i) (a i))
  · intro hd i
    change d ∣ Z i
    rw [hscale]
    exact dvd_mul_of_dvd_left hd (M i)

end CompoundFeasibility.SourcePrimitiveHeight10
