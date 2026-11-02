import SubspaceBridge.SourceTripleForm244
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceFlag244
open Exterior53_242 SchmidtNormal10 SourceOriginalDual10

theorem exceptional_triple_nonzero244 (u : Fin 5 → Fin 5 → ℤ)
    (hu : LinearIndependent ℝ (fun j => integerReal (u j))) (b : Fin 10 → ℤ) (hb : b ≠ 0)
    (hz : ∀ s : Fin 10, s ≠ 9 → normalForm10 b
      (fun i => (wedge3242 (R := ℤ) (u (lo242 s)) (u (mid242 s)) (u (hi242 s)) i : ℚ)) = 0) :
    normalForm10 b (fun i => (wedge3242 (R := ℤ) (u 2) (u 3) (u 4) i : ℚ)) ≠ 0 := by
  intro h9
  let w : Fin 10 → Fin 10 → ℤ := fun s => wedge3242 (R := ℤ) (u (lo242 s)) (u (mid242 s)) (u (hi242 s))
  have hw := integer_frame_rational_independent10 w (compoundFrame_independent3242 u hu)
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

end CompoundFeasibility.SourceFlag244
