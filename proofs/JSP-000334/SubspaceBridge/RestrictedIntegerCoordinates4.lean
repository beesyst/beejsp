import SubspaceBridge.RestrictedRelaxed4
import SubspaceBridge.RestrictedCovolumeOrder4
import SubspaceBridge.RestrictedRationalMembership4
open scoped BigOperators Matrix
namespace CompoundFeasibility.RestrictedIntegerCoordinates4
open RestrictedGeometry4 RestrictedRelaxed4
noncomputable section

def baseLattice4 (P : Submodule ℚ (Fin 4 → ℚ)) : Submodule ℤ (rationalRealSpan4 P) :=
  restrictedLattice4 P 0 0 2 (fun _ => 0) (fun _ => 0)

theorem baseLattice4_mem (P : Submodule ℚ (Fin 4 → ℚ)) (x : rationalRealSpan4 P) :
    x ∈ baseLattice4 P ↔ ∃ z : Fin 4 → ℤ, integerReal z = (x : Fin 4 → ℝ) := by
  constructor
  · rintro ⟨z,hz,hx⟩
    exact ⟨z,hx⟩
  · rintro ⟨z,hz⟩
    refine ⟨z,?_,hz⟩
    change z ∈ lattice4 2 0 _ ∧ z ∈ lattice4 3 0 _
    constructor
    · apply (lattice4_spec 2 0 _ z).mpr
      intro i
      simp only [Matrix.zero_mulVec,Pi.zero_apply,padicNorm.zero]
      positivity
    · apply (lattice4_spec 3 0 _ z).mpr
      intro i
      simp only [Matrix.zero_mulVec,Pi.zero_apply,padicNorm.zero]
      positivity

theorem relaxedLattice4_le_base {d : ℕ} (P : Submodule ℚ (Fin 4 → ℚ))
    (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) (Q : ℝ) (c₂ c₃ : Fin 4 → ℝ) (s₂ s₃ : Fin d → Fin 4) :
    relaxedLattice4 P A₂ A₃ Q c₂ c₃ s₂ s₃ ≤ baseLattice4 P := by
  rintro x ⟨z,hz,hx⟩
  exact (baseLattice4_mem P x).mpr ⟨z,hx⟩

def baseIntegerBasis4 (P : Submodule ℚ (Fin 4 → ℚ)) (hP : Module.finrank ℚ P ≤ 3) :
    Basis (Fin (Module.finrank ℚ P)) ℤ (baseLattice4 P) := by
  letI : DiscreteTopology (baseLattice4 P) := by
    dsimp only [baseLattice4]
    infer_instance
  letI : IsZLattice ℝ (baseLattice4 P) := by
    dsimp only [baseLattice4]
    infer_instance
  letI : Module.Free ℤ (baseLattice4 P) := ZLattice.module_free ℝ (baseLattice4 P)
  letI : Module.Finite ℤ (baseLattice4 P) := ZLattice.module_finite ℝ (baseLattice4 P)
  exact (Module.finBasis ℤ (baseLattice4 P)).reindex
    (finCongr (restrictedLattice4_rank P hP 0 0 2 (fun _ => 0) (fun _ => 0)))

def integerCoordinateMap4 (P : Submodule ℚ (Fin 4 → ℚ)) (hP : Module.finrank ℚ P ≤ 3) :
    (Fin (Module.finrank ℚ P) → ℤ) →ₗ[ℤ] rationalRealSpan4 P :=
  (baseLattice4 P).subtype.comp (baseIntegerBasis4 P hP).equivFun.symm.toLinearMap

theorem integerCoordinateMap4_injective (P : Submodule ℚ (Fin 4 → ℚ)) (hP : Module.finrank ℚ P ≤ 3) :
    Function.Injective (integerCoordinateMap4 P hP) :=
  (baseLattice4 P).subtype_injective.comp (baseIntegerBasis4 P hP).equivFun.symm.injective

theorem integerCoordinateMap4_equivFun (P : Submodule ℚ (Fin 4 → ℚ))
    (hP : Module.finrank ℚ P ≤ 3) (x : baseLattice4 P) :
    integerCoordinateMap4 P hP ((baseIntegerBasis4 P hP).equivFun x) = (x : rationalRealSpan4 P) := by
  change (((baseIntegerBasis4 P hP).equivFun.symm ((baseIntegerBasis4 P hP).equivFun x) :
    baseLattice4 P) : rationalRealSpan4 P) = (x : rationalRealSpan4 P)
  rw [LinearEquiv.symm_apply_apply]

def relaxedIntegerGroup4 {d : ℕ} (P : Submodule ℚ (Fin 4 → ℚ)) (hP : Module.finrank ℚ P ≤ 3)
    (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) (Q : ℝ) (c₂ c₃ : Fin 4 → ℝ) (s₂ s₃ : Fin d → Fin 4) :
    AddSubgroup (Fin (Module.finrank ℚ P) → ℤ) :=
  (relaxedLattice4 P A₂ A₃ Q c₂ c₃ s₂ s₃).toAddSubgroup.comap
    (integerCoordinateMap4 P hP).toAddMonoidHom

def relaxedIntegerEquiv4 {d : ℕ} (P : Submodule ℚ (Fin 4 → ℚ)) (hP : Module.finrank ℚ P ≤ 3)
    (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) (Q : ℝ) (c₂ c₃ : Fin 4 → ℝ) (s₂ s₃ : Fin d → Fin 4) :
    relaxedIntegerGroup4 P hP A₂ A₃ Q c₂ c₃ s₂ s₃ ≃ₗ[ℤ] relaxedLattice4 P A₂ A₃ Q c₂ c₃ s₂ s₃ where
  toFun z := ⟨integerCoordinateMap4 P hP z,z.property⟩
  invFun x := ⟨(baseIntegerBasis4 P hP).equivFun
    ⟨x.val,relaxedLattice4_le_base P A₂ A₃ Q c₂ c₃ s₂ s₃ x.property⟩,by
      change integerCoordinateMap4 P hP _ ∈ relaxedLattice4 P A₂ A₃ Q c₂ c₃ s₂ s₃
      rw [integerCoordinateMap4_equivFun]
      exact x.property⟩
  left_inv z := by
    apply Subtype.ext
    apply integerCoordinateMap4_injective P hP
    rw [integerCoordinateMap4_equivFun]
  right_inv x := by
    apply Subtype.ext
    change integerCoordinateMap4 P hP ((baseIntegerBasis4 P hP).equivFun
      ⟨x.val,relaxedLattice4_le_base P A₂ A₃ Q c₂ c₃ s₂ s₃ x.property⟩) = x.val
    rw [integerCoordinateMap4_equivFun]
  map_add' x y := by
    apply Subtype.ext
    exact (integerCoordinateMap4 P hP).map_add x y
  map_smul' a x := by
    apply Subtype.ext
    exact (integerCoordinateMap4 P hP).map_smul a x

theorem relaxedIntegerGroup4_rank {d : ℕ} (P : Submodule ℚ (Fin 4 → ℚ)) (hP : Module.finrank ℚ P ≤ 3)
    (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) (Q : ℝ) (c₂ c₃ : Fin 4 → ℝ) (s₂ s₃ : Fin d → Fin 4) :
    Module.finrank ℤ (relaxedIntegerGroup4 P hP A₂ A₃ Q c₂ c₃ s₂ s₃) = Module.finrank ℚ P :=
  (relaxedIntegerEquiv4 P hP A₂ A₃ Q c₂ c₃ s₂ s₃).finrank_eq.trans
    (relaxedLattice4_rank P hP A₂ A₃ Q c₂ c₃ s₂ s₃)

def baseIntegerVector4 (P : Submodule ℚ (Fin 4 → ℚ)) (hP : Module.finrank ℚ P ≤ 3)
    (k : Fin (Module.finrank ℚ P)) : Fin 4 → ℤ :=
  Classical.choose ((baseLattice4_mem P (baseIntegerBasis4 P hP k)).mp (baseIntegerBasis4 P hP k).property)

theorem baseIntegerVector4_values (P : Submodule ℚ (Fin 4 → ℚ)) (hP : Module.finrank ℚ P ≤ 3)
    (k : Fin (Module.finrank ℚ P)) :
    integerReal (baseIntegerVector4 P hP k) = ((baseIntegerBasis4 P hP k : rationalRealSpan4 P) : Fin 4 → ℝ) :=
  Classical.choose_spec ((baseLattice4_mem P (baseIntegerBasis4 P hP k)).mp (baseIntegerBasis4 P hP k).property)

theorem baseIntegerVector4_rational_mem (P : Submodule ℚ (Fin 4 → ℚ)) (hP : Module.finrank ℚ P ≤ 3)
    (k : Fin (Module.finrank ℚ P)) : (fun i => (baseIntegerVector4 P hP k i : ℚ)) ∈ P := by
  apply (RestrictedRationalMembership4.rationalRealSpan4_mem_rational P _).mp
  have he : (fun i => ((baseIntegerVector4 P hP k i : ℚ) : ℝ)) =
      integerReal (baseIntegerVector4 P hP k) := by
    ext i
    simp [integerReal]
  rw [he,baseIntegerVector4_values]
  exact (baseIntegerBasis4 P hP k).val.property

def baseRationalVector4 (P : Submodule ℚ (Fin 4 → ℚ)) (hP : Module.finrank ℚ P ≤ 3)
    (k : Fin (Module.finrank ℚ P)) : P :=
  ⟨fun i => (baseIntegerVector4 P hP k i : ℚ),baseIntegerVector4_rational_mem P hP k⟩

theorem baseRationalVector4_independent (P : Submodule ℚ (Fin 4 → ℚ)) (hP : Module.finrank ℚ P ≤ 3) :
    LinearIndependent ℚ (baseRationalVector4 P hP) := by
  letI : DiscreteTopology (baseLattice4 P) := by dsimp only [baseLattice4];infer_instance
  letI : IsZLattice ℝ (baseLattice4 P) := by dsimp only [baseLattice4];infer_instance
  let b := (baseIntegerBasis4 P hP).ofZLatticeBasis ℝ (baseLattice4 P)
  have hli := b.linearIndependent.map' (rationalRealSpan4 P).subtype (rationalRealSpan4 P).ker_subtype
  have hreal : LinearIndependent ℝ (fun k => integerReal (baseIntegerVector4 P hP k)) := by
    convert hli using 1
    funext k
    rw [baseIntegerVector4_values]
    simp [b,Function.comp_def]
  let ratReal : (Fin 4 → ℚ) →ₗ[ℚ] (Fin 4 → ℝ) :=
    LinearMap.pi (fun i => (Algebra.linearMap ℚ ℝ).comp (LinearMap.proj i))
  have hcast : LinearIndependent ℚ (fun k => ratReal (baseRationalVector4 P hP k : Fin 4 → ℚ)) := by
    convert hreal.restrict_scalars' ℚ using 1
  have hambient := LinearIndependent.of_comp ratReal hcast
  exact LinearIndependent.of_comp P.subtype hambient

def baseRationalBasis4 (P : Submodule ℚ (Fin 4 → ℚ)) (hP : Module.finrank ℚ P ≤ 3) :
    Basis (Fin (Module.finrank ℚ P)) ℚ P :=
  Basis.mk (baseRationalVector4_independent P hP)
    ((baseRationalVector4_independent P hP).span_eq_top_of_card_eq_finrank' (by simp)).ge

end
end CompoundFeasibility.RestrictedIntegerCoordinates4
