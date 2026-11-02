import SubspaceBridge.CompoundDualLine42
open scoped BigOperators
namespace DualLine42Literal
noncomputable section

def minors (x y : Fin 4 → ℚ) : Fin 6 → ℚ :=
  ![x 0*y 1-x 1*y 0,x 0*y 2-x 2*y 0,x 0*y 3-x 3*y 0,
    x 1*y 2-x 2*y 1,x 1*y 3-x 3*y 1,x 2*y 3-x 3*y 2]

def coefficients (f g : Module.Dual ℚ (Fin 4 → ℚ)) : Fin 6 → ℚ :=
  minors (fun i => f (Pi.single i 1)) (fun i => g (Pi.single i 1))

def exteriorFunctional (f g : Module.Dual ℚ (Fin 4 → ℚ)) : Module.Dual ℚ (Fin 6 → ℚ) :=
  ∑ s : Fin 6, coefficients f g s • LinearMap.proj s

theorem raw_minors (x y : Fin 4 → ℚ) : minors x y = CompoundFeasibility.wedge x y := by
  ext s
  fin_cases s <;> rfl

theorem raw_functional (f g : Module.Dual ℚ (Fin 4 → ℚ)) :
    exteriorFunctional f g = CompoundFeasibility.wedgeDual42 f g := by
  unfold exteriorFunctional CompoundFeasibility.wedgeDual42
  congr 1
  funext s
  rw [coefficients,raw_minors]
  rfl

theorem determinant_pairing (f g : Module.Dual ℚ (Fin 4 → ℚ)) (x y : Fin 4 → ℚ) :
    exteriorFunctional f g (minors x y) = f x * g y - f y * g x := by
  rw [raw_functional,raw_minors]
  exact CompoundFeasibility.wedgeDual42_pairing f g x y

theorem rational_duals {n : ℕ} (u : Fin n → Fin n → ℚ) (hu : LinearIndependent ℚ u) :
    ∃ D : Fin n → Module.Dual ℚ (Fin n → ℚ), ∀ i j,
      D i (u j) = if j = i then 1 else 0 :=
  ⟨CompoundFeasibility.rationalFrameDual42 u hu,
    CompoundFeasibility.rationalFrameDual42_pairing u hu⟩

theorem last_annihilator (v : Fin 6 → Fin 6 → ℚ) (hv : LinearIndependent ℚ v) :
    ∃ d : Module.Dual ℚ (Fin 6 → ℚ),
      d ≠ 0 ∧ (∀ j, d (v j) = if j = 5 then 1 else 0) ∧
      LinearMap.ker d = Submodule.span ℚ (Set.range (fun i : Fin 5 => v i.castSucc)) ∧
      ∀ f : Module.Dual ℚ (Fin 6 → ℚ), (∀ i : Fin 5, f (v i.castSucc) = 0) →
        f = f (v 5) • d :=
  ⟨CompoundFeasibility.rationalFrameDual42 v hv 5,
    CompoundFeasibility.lastDual42_nonzero v hv,
    CompoundFeasibility.rationalFrameDual42_pairing v hv 5,
    CompoundFeasibility.lastDual42_kernel v hv,
    CompoundFeasibility.functional_lastDual42 v hv⟩

end
end DualLine42Literal
#check DualLine42Literal.minors
#print axioms DualLine42Literal.minors
#check DualLine42Literal.coefficients
#print axioms DualLine42Literal.coefficients
#check DualLine42Literal.exteriorFunctional
#print axioms DualLine42Literal.exteriorFunctional
#check DualLine42Literal.raw_minors
#print axioms DualLine42Literal.raw_minors
#check DualLine42Literal.raw_functional
#print axioms DualLine42Literal.raw_functional
#check DualLine42Literal.determinant_pairing
#print axioms DualLine42Literal.determinant_pairing
#check DualLine42Literal.rational_duals
#print axioms DualLine42Literal.rational_duals
#check DualLine42Literal.last_annihilator
#print axioms DualLine42Literal.last_annihilator
