import SubspaceBridge.RestrictedRelaxed5
import SubspaceBridge.RestrictedCovolumeOrder5
import SubspaceBridge.RestrictedRationalMembership5
open scoped BigOperators Matrix
namespace CompoundFeasibility.RestrictedIntegerCoordinates5
open RestrictedGeometry5 RestrictedRelaxed5
noncomputable section

def baseLattice5 (P : Submodule ℚ (Fin 5 → ℚ)) : Submodule ℤ (rationalRealSpan5 P) :=
  restrictedLattice5 P 0 0 2 (fun _ => 0) (fun _ => 0)

theorem baseLattice5_mem (P : Submodule ℚ (Fin 5 → ℚ)) (x : rationalRealSpan5 P) :
    x ∈ baseLattice5 P ↔ ∃ z : Fin 5 → ℤ, integerReal z = (x : Fin 5 → ℝ) := by
  constructor
  · rintro ⟨z,hz,hx⟩
    exact ⟨z,hx⟩
  · rintro ⟨z,hz⟩
    refine ⟨z,?_,hz⟩
    change z ∈ lattice5 2 0 _ ∧ z ∈ lattice5 3 0 _
    constructor
    · apply (lattice5_spec 2 0 _ z).mpr
      intro i
      simp only [Matrix.zero_mulVec,Pi.zero_apply,padicNorm.zero]
      positivity
    · apply (lattice5_spec 3 0 _ z).mpr
      intro i
      simp only [Matrix.zero_mulVec,Pi.zero_apply,padicNorm.zero]
      positivity

theorem relaxedLattice5_le_base {d : ℕ} (P : Submodule ℚ (Fin 5 → ℚ))
    (A₂ A₃ : Matrix (Fin 5) (Fin 5) ℚ) (Q : ℝ) (c₂ c₃ : Fin 5 → ℝ) (s₂ s₃ : Fin d → Fin 5) :
    relaxedLattice5 P A₂ A₃ Q c₂ c₃ s₂ s₃ ≤ baseLattice5 P := by
  rintro x ⟨z,hz,hx⟩
  exact (baseLattice5_mem P x).mpr ⟨z,hx⟩

def baseIntegerBasis5 (P : Submodule ℚ (Fin 5 → ℚ)) (hP : Module.finrank ℚ P ≤ 4) :
    Basis (Fin (Module.finrank ℚ P)) ℤ (baseLattice5 P) := by
  letI : DiscreteTopology (baseLattice5 P) := by
    dsimp only [baseLattice5]
    infer_instance
  letI : IsZLattice ℝ (baseLattice5 P) := by
    dsimp only [baseLattice5]
    infer_instance
  letI : Module.Free ℤ (baseLattice5 P) := ZLattice.module_free ℝ (baseLattice5 P)
  letI : Module.Finite ℤ (baseLattice5 P) := ZLattice.module_finite ℝ (baseLattice5 P)
  exact (Module.finBasis ℤ (baseLattice5 P)).reindex
    (finCongr (restrictedLattice5_rank P hP 0 0 2 (fun _ => 0) (fun _ => 0)))

def integerCoordinateMap5 (P : Submodule ℚ (Fin 5 → ℚ)) (hP : Module.finrank ℚ P ≤ 4) :
    (Fin (Module.finrank ℚ P) → ℤ) →ₗ[ℤ] rationalRealSpan5 P :=
  (baseLattice5 P).subtype.comp (baseIntegerBasis5 P hP).equivFun.symm.toLinearMap

theorem integerCoordinateMap5_injective (P : Submodule ℚ (Fin 5 → ℚ)) (hP : Module.finrank ℚ P ≤ 4) :
    Function.Injective (integerCoordinateMap5 P hP) :=
  (baseLattice5 P).subtype_injective.comp (baseIntegerBasis5 P hP).equivFun.symm.injective

theorem integerCoordinateMap5_equivFun (P : Submodule ℚ (Fin 5 → ℚ))
    (hP : Module.finrank ℚ P ≤ 4) (x : baseLattice5 P) :
    integerCoordinateMap5 P hP ((baseIntegerBasis5 P hP).equivFun x) = (x : rationalRealSpan5 P) := by
  change (((baseIntegerBasis5 P hP).equivFun.symm ((baseIntegerBasis5 P hP).equivFun x) :
    baseLattice5 P) : rationalRealSpan5 P) = (x : rationalRealSpan5 P)
  rw [LinearEquiv.symm_apply_apply]

def relaxedIntegerGroup5 {d : ℕ} (P : Submodule ℚ (Fin 5 → ℚ)) (hP : Module.finrank ℚ P ≤ 4)
    (A₂ A₃ : Matrix (Fin 5) (Fin 5) ℚ) (Q : ℝ) (c₂ c₃ : Fin 5 → ℝ) (s₂ s₃ : Fin d → Fin 5) :
    AddSubgroup (Fin (Module.finrank ℚ P) → ℤ) :=
  (relaxedLattice5 P A₂ A₃ Q c₂ c₃ s₂ s₃).toAddSubgroup.comap
    (integerCoordinateMap5 P hP).toAddMonoidHom

def relaxedIntegerEquiv5 {d : ℕ} (P : Submodule ℚ (Fin 5 → ℚ)) (hP : Module.finrank ℚ P ≤ 4)
    (A₂ A₃ : Matrix (Fin 5) (Fin 5) ℚ) (Q : ℝ) (c₂ c₃ : Fin 5 → ℝ) (s₂ s₃ : Fin d → Fin 5) :
    relaxedIntegerGroup5 P hP A₂ A₃ Q c₂ c₃ s₂ s₃ ≃ₗ[ℤ] relaxedLattice5 P A₂ A₃ Q c₂ c₃ s₂ s₃ where
  toFun z := ⟨integerCoordinateMap5 P hP z,z.property⟩
  invFun x := ⟨(baseIntegerBasis5 P hP).equivFun
    ⟨x.val,relaxedLattice5_le_base P A₂ A₃ Q c₂ c₃ s₂ s₃ x.property⟩,by
      change integerCoordinateMap5 P hP _ ∈ relaxedLattice5 P A₂ A₃ Q c₂ c₃ s₂ s₃
      rw [integerCoordinateMap5_equivFun]
      exact x.property⟩
  left_inv z := by
    apply Subtype.ext
    apply integerCoordinateMap5_injective P hP
    rw [integerCoordinateMap5_equivFun]
  right_inv x := by
    apply Subtype.ext
    change integerCoordinateMap5 P hP ((baseIntegerBasis5 P hP).equivFun
      ⟨x.val,relaxedLattice5_le_base P A₂ A₃ Q c₂ c₃ s₂ s₃ x.property⟩) = x.val
    rw [integerCoordinateMap5_equivFun]
  map_add' x y := by
    apply Subtype.ext
    exact (integerCoordinateMap5 P hP).map_add x y
  map_smul' a x := by
    apply Subtype.ext
    exact (integerCoordinateMap5 P hP).map_smul a x

theorem relaxedIntegerGroup5_rank {d : ℕ} (P : Submodule ℚ (Fin 5 → ℚ)) (hP : Module.finrank ℚ P ≤ 4)
    (A₂ A₃ : Matrix (Fin 5) (Fin 5) ℚ) (Q : ℝ) (c₂ c₃ : Fin 5 → ℝ) (s₂ s₃ : Fin d → Fin 5) :
    Module.finrank ℤ (relaxedIntegerGroup5 P hP A₂ A₃ Q c₂ c₃ s₂ s₃) = Module.finrank ℚ P :=
  (relaxedIntegerEquiv5 P hP A₂ A₃ Q c₂ c₃ s₂ s₃).finrank_eq.trans
    (relaxedLattice5_rank P hP A₂ A₃ Q c₂ c₃ s₂ s₃)

def baseIntegerVector5 (P : Submodule ℚ (Fin 5 → ℚ)) (hP : Module.finrank ℚ P ≤ 4)
    (k : Fin (Module.finrank ℚ P)) : Fin 5 → ℤ :=
  Classical.choose ((baseLattice5_mem P (baseIntegerBasis5 P hP k)).mp (baseIntegerBasis5 P hP k).property)

theorem baseIntegerVector5_values (P : Submodule ℚ (Fin 5 → ℚ)) (hP : Module.finrank ℚ P ≤ 4)
    (k : Fin (Module.finrank ℚ P)) :
    integerReal (baseIntegerVector5 P hP k) = ((baseIntegerBasis5 P hP k : rationalRealSpan5 P) : Fin 5 → ℝ) :=
  Classical.choose_spec ((baseLattice5_mem P (baseIntegerBasis5 P hP k)).mp (baseIntegerBasis5 P hP k).property)

theorem baseIntegerVector5_rational_mem (P : Submodule ℚ (Fin 5 → ℚ)) (hP : Module.finrank ℚ P ≤ 4)
    (k : Fin (Module.finrank ℚ P)) : (fun i => (baseIntegerVector5 P hP k i : ℚ)) ∈ P := by
  apply (RestrictedRationalMembership5.rationalRealSpan5_mem_rational P _).mp
  have he : (fun i => ((baseIntegerVector5 P hP k i : ℚ) : ℝ)) =
      integerReal (baseIntegerVector5 P hP k) := by
    ext i
    simp [integerReal]
  rw [he,baseIntegerVector5_values]
  exact (baseIntegerBasis5 P hP k).val.property

def baseRationalVector5 (P : Submodule ℚ (Fin 5 → ℚ)) (hP : Module.finrank ℚ P ≤ 4)
    (k : Fin (Module.finrank ℚ P)) : P :=
  ⟨fun i => (baseIntegerVector5 P hP k i : ℚ),baseIntegerVector5_rational_mem P hP k⟩

theorem baseRationalVector5_independent (P : Submodule ℚ (Fin 5 → ℚ)) (hP : Module.finrank ℚ P ≤ 4) :
    LinearIndependent ℚ (baseRationalVector5 P hP) := by
  letI : DiscreteTopology (baseLattice5 P) := by dsimp only [baseLattice5];infer_instance
  letI : IsZLattice ℝ (baseLattice5 P) := by dsimp only [baseLattice5];infer_instance
  let b := (baseIntegerBasis5 P hP).ofZLatticeBasis ℝ (baseLattice5 P)
  have hli := b.linearIndependent.map' (rationalRealSpan5 P).subtype (rationalRealSpan5 P).ker_subtype
  have hreal : LinearIndependent ℝ (fun k => integerReal (baseIntegerVector5 P hP k)) := by
    convert hli using 1
    funext k
    rw [baseIntegerVector5_values]
    simp [b,Function.comp_def]
  let ratReal : (Fin 5 → ℚ) →ₗ[ℚ] (Fin 5 → ℝ) :=
    LinearMap.pi (fun i => (Algebra.linearMap ℚ ℝ).comp (LinearMap.proj i))
  have hcast : LinearIndependent ℚ (fun k => ratReal (baseRationalVector5 P hP k : Fin 5 → ℚ)) := by
    convert hreal.restrict_scalars' ℚ using 1
  have hambient := LinearIndependent.of_comp ratReal hcast
  exact LinearIndependent.of_comp P.subtype hambient

def baseRationalBasis5 (P : Submodule ℚ (Fin 5 → ℚ)) (hP : Module.finrank ℚ P ≤ 4) :
    Basis (Fin (Module.finrank ℚ P)) ℚ P :=
  Basis.mk (baseRationalVector5_independent P hP)
    ((baseRationalVector5_independent P hP).span_eq_top_of_card_eq_finrank' (by simp)).ge

end
end CompoundFeasibility.RestrictedIntegerCoordinates5
