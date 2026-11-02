import SubspaceBridge.SourceBlockUnit245Q
import SubspaceBridge.SourceExterior53Normalize242
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.BlockReduction245Q
open BlockReduction245P Exterior53_242

theorem first_join245Q {R : Type*} (x y : Fin 5 → R) : first245Q (join245Q x y) = x := by
  ext i
  simp [first245Q,join245Q]

theorem second_join245Q {R : Type*} (x y : Fin 5 → R) : second245Q (join245Q x y) = y := by
  ext i
  simp [second245Q,join245Q]

theorem threshold245Q (p : ℕ) (Q c : ℝ) :
    JSP000334.qThreshold p (Q^3) (c/3) = JSP000334.qThreshold p Q c := by
  simpa only [add_zero] using powered_threshold3242 p Q c 0 0

theorem block_lattice245Q (p : ℕ) [Fact p.Prime]
    (A : Matrix (Fin 5) (Fin 5) ℚ) (Q : ℝ) (c : Fin 5 → ℝ) (z : Fin 10 → ℤ) :
    z ∈ lattice10 p (block245P A)
      (fun i => Nat.ceil (JSP000334.qThreshold p (Q^3) (weightp245P c i))) ↔
    first245Q z ∈ lattice5 p A (fun i => Nat.ceil (JSP000334.qThreshold p Q (c i))) := by
  rw [lattice10_spec,lattice5_spec]
  constructor
  · intro h i
    have hi := h (blockIndex245P (Sum.inl i))
    rw [block_mulVec_left245Q] at hi
    simpa only [weightp245P,Equiv.symm_apply_apply,Sum.elim_inl,threshold245Q] using hi
  · intro h i
    obtain ⟨s,rfl⟩ := blockIndex245P.surjective i
    cases s with
    | inl j =>
      rw [block_mulVec_left245Q]
      simpa only [weightp245P,Equiv.symm_apply_apply,Sum.elim_inl,threshold245Q] using h j
    | inr j =>
      rw [block_mulVec_right245Q]
      simpa [weightp245P,JSP000334.qThreshold,second245Q] using
        (padicNorm.of_int (p := p) (second245Q z j))

theorem block_source_group245Q (A2 A3 : Matrix (Fin 5) (Fin 5) ℚ)
    (Q : ℝ) (c2 c3 : Fin 5 → ℝ) (z : Fin 10 → ℤ) :
    z ∈ originalSourceGroup10 (block245P A2) (block245P A3) (Q^3)
      (weightp245P c2) (weightp245P c3) ↔
      first245Q z ∈ originalSourceGroup5 A2 A3 Q c2 c3 := by
  change (z ∈ lattice10 2 (block245P A2) _ ∧ z ∈ lattice10 3 (block245P A3) _) ↔
    (first245Q z ∈ lattice5 2 A2 _ ∧ first245Q z ∈ lattice5 3 A3 _)
  rw [block_lattice245Q,block_lattice245Q]

end CompoundFeasibility.BlockReduction245Q
