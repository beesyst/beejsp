import SubspaceBridge.SourceExterior54Bound246L
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.Exterior54_246

theorem local_wedge4246 (p : ℕ) [Fact p.Prime]
    (A : Matrix (Fin 5) (Fin 5) ℚ) (e : Fin 5 → ℕ)
    (x : Fin 4 → Fin 5 → ℤ) (hx : ∀ j, x j ∈ lattice5 p A e) :
    wedge4246 x ∈ lattice5 p (compound4246 A)
      (fun i => ∑ r : Fin 4, e (i.succAbove r)) := by
  have hy : ∀ j k, ‖((A.map (algebraMap ℚ ℚ_[p])) *ᵥ
      (fun t => (x j t : ℚ_[p]))) k‖ ≤ (p : ℝ)^(-(e k : ℤ)) := by
    intro j k
    rw [OriginalDual10.finite_form_norm10]
    have hr := (Rat.cast_le (K := ℝ)
      (p := padicNorm p ((A *ᵥ (fun t => (x j t : ℚ))) k))
      (q := (p : ℚ)^(-(e k : ℤ)))).mpr ((lattice5_spec p A e (x j)).mp (hx j) k)
    simpa only [Rat.cast_zpow, Rat.cast_natCast] using hr
  rw [lattice5_spec]
  intro i
  have hs := padic_wedge_bound4246 p
    (fun j => A.map (algebraMap ℚ ℚ_[p]) *ᵥ (fun t => (x j t : ℚ_[p])))
    (fun k => (p : ℝ)^(-(e k : ℤ))) (fun k => by positivity) hy i
  have ht := wedge_transform4246 (A.map (algebraMap ℚ ℚ_[p]))
    (fun j t => (x j t : ℚ_[p]))
  have hc : (fun k => ((wedge4246 x k : ℤ) : ℚ_[p])) =
      wedge4246 (fun j t => (x j t : ℚ_[p])) := wedge_map4246 (Int.castRingHom ℚ_[p]) x
  rw [← ht, ← hc, ← compound_map4246 (algebraMap ℚ ℚ_[p]) A,
    OriginalDual10.finite_form_norm10] at hs
  have hp : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hprod (s : Finset (Fin 4)) :
      (∏ k ∈ s, (p : ℝ)^(-(e (i.succAbove k) : ℤ))) =
        (p : ℝ)^(∑ k ∈ s, -(e (i.succAbove k) : ℤ)) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add₀ hp]
  rw [hprod] at hs
  have he : (∑ k : Fin 4, -(e (i.succAbove k) : ℤ)) =
      -((∑ k : Fin 4, e (i.succAbove k) : ℕ) : ℤ) := by simp
  rw [he] at hs
  apply (Rat.cast_le (K := ℝ)).mp
  simpa only [Rat.cast_zpow, Rat.cast_natCast] using hs

end CompoundFeasibility.Exterior54_246
