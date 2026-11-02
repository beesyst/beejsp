import SubspaceBridge.SourcePairForm241
import SubspaceBridge.SourceFixedNormal241
import SubspaceBridge.SourceOriginalRationalDual10
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceFlag241
open Exterior52_237 Exterior52_238 SchmidtNormal10 SourceOriginalDual10

theorem original_rational_independent241 (u : Fin 5 → Fin 5 → ℤ)
    (hu : LinearIndependent ℝ (fun j => integerReal (u j))) :
    LinearIndependent ℚ (fun j i => (u j i : ℚ)) := by
  let f : (Fin 5 → ℚ) →ₗ[ℚ] (Fin 5 → ℝ) :=
    LinearMap.pi (fun i => (Algebra.linearMap ℚ ℝ).comp (LinearMap.proj i))
  apply LinearIndependent.of_comp f
  convert hu.restrict_scalars' ℚ using 1

theorem pairForm_integer_cast241 (b : Fin 10 → ℤ) (x y : Fin 5 → ℤ) :
    pairForm241 b (fun i => (x i : ℚ)) (fun i => (y i : ℚ)) =
      normalForm10 b (fun s => (wedge237 (R := ℤ) x y s : ℚ)) := by
  simp [pairForm_apply241,normalForm10_apply,wedge237]

theorem exceptional_pair_nonzero241 (u : Fin 5 → Fin 5 → ℤ)
    (hu : LinearIndependent ℝ (fun j => integerReal (u j))) (b : Fin 10 → ℤ) (hb : b ≠ 0)
    (hz : ∀ s : Fin 10, s ≠ 9 → normalForm10 b
      (fun i => (wedge237 (R := ℤ) (u (lo237 s)) (u (hi237 s)) i : ℚ)) = 0) :
    normalForm10 b (fun i => (wedge237 (R := ℤ) (u 3) (u 4) i : ℚ)) ≠ 0 := by
  intro h9
  let w : Fin 10 → Fin 10 → ℤ := fun s => wedge237 (R := ℤ) (u (lo237 s)) (u (hi237 s))
  have hw := integer_frame_rational_independent10 w (compoundFrame_independent238 u hu)
  have hf : normalForm10 b = 0 := by
    apply (rationalFrameBasis42 (fun j i => (w j i : ℚ)) hw).ext
    intro s
    rw [rationalFrameBasis42_apply]
    change normalForm10 b (fun i => (w s i : ℚ)) = 0
    by_cases hs : s = 9
    · subst s
      exact h9
    · exact hz s hs
  apply hb
  funext i
  have h := congrArg (fun f : Module.Dual ℚ (Fin 10 → ℚ) => f (Pi.single i 1)) hf
  have hi : (b i : ℚ) = 0 := by simpa [normalForm10_apply,Pi.single_apply] using h
  exact_mod_cast hi

end CompoundFeasibility.SourceFlag241
