import SubspaceBridge.RestrictedAttainment4
noncomputable section
namespace CompoundFeasibility.RestrictedGeometry4
variable (P : Submodule ℚ (Fin 4 → ℚ))
variable (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) (Q : ℝ) (c₂ c₃ : Fin 4 → ℝ)

def restrictedLatticeFlag4 {n : ℕ} (v : Fin n → rationalRealSpan4 P) (k : Fin n) :
    Submodule ℤ (restrictedLattice4 P A₂ A₃ Q c₂ c₃) :=
  ((intrinsicPrefix4 v k).restrictScalars ℤ).comap
    (restrictedLattice4 P A₂ A₃ Q c₂ c₃).subtype

def restrictedFlagLattice4 {n : ℕ} (v : Fin n → rationalRealSpan4 P) (k : Fin n) :
    Submodule ℤ (intrinsicPrefix4 v k) :=
  (restrictedLattice4 P A₂ A₃ Q c₂ c₃).comap
    ((intrinsicPrefix4 v k).subtype.restrictScalars ℤ)

theorem restrictedLatticeFlag4_saturated {n : ℕ}
    (v : Fin n → rationalRealSpan4 P) (k : Fin n) (z : ℤ) (hz : z ≠ 0)
    (x : restrictedLattice4 P A₂ A₃ Q c₂ c₃)
    (hx : z • x ∈ restrictedLatticeFlag4 P A₂ A₃ Q c₂ c₃ v k) :
    x ∈ restrictedLatticeFlag4 P A₂ A₃ Q c₂ c₃ v k := by
  change z • (x : rationalRealSpan4 P) ∈ intrinsicPrefix4 v k at hx
  rw [← Int.cast_smul_eq_zsmul ℝ] at hx
  exact (Submodule.smul_mem_iff (intrinsicPrefix4 v k)
    (by exact_mod_cast hz : (z : ℝ) ≠ 0)).mp hx

def restrictedLatticeFlag4_equiv {n : ℕ} (v : Fin n → rationalRealSpan4 P) (k : Fin n) :
    restrictedLatticeFlag4 P A₂ A₃ Q c₂ c₃ v k ≃ₗ[ℤ]
      restrictedFlagLattice4 P A₂ A₃ Q c₂ c₃ v k where
  toFun x := ⟨⟨x.val.val,x.property⟩,x.val.property⟩
  invFun x := ⟨⟨x.val.val,x.property⟩,x.val.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

instance restrictedFlagLattice4_discrete {n : ℕ}
    (v : Fin n → rationalRealSpan4 P) (k : Fin n) :
    DiscreteTopology (restrictedFlagLattice4 P A₂ A₃ Q c₂ c₃ v k) := by
  let f : restrictedFlagLattice4 P A₂ A₃ Q c₂ c₃ v k →
      restrictedLattice4 P A₂ A₃ Q c₂ c₃ := fun x => ⟨x.val.val,x.property⟩
  apply DiscreteTopology.of_continuous_injective (f := f)
  · exact (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  · intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : restrictedLattice4 P A₂ A₃ Q c₂ c₃ => (z : rationalRealSpan4 P)) h

theorem restrictedFlagLattice4_isZLattice {n : ℕ}
    (v : Fin n → rationalRealSpan4 P) (hv : LinearIndependent ℝ v)
    (hvL : ∀ i, v i ∈ restrictedLattice4 P A₂ A₃ Q c₂ c₃) (k : Fin n) :
    IsZLattice ℝ (E := intrinsicPrefix4 v k) (restrictedFlagLattice4 P A₂ A₃ Q c₂ c₃ v k) where
  span_top := by
    let B : Basis (Fin k.val) ℝ (intrinsicPrefix4 v k) :=
      Basis.span (hv.comp (Fin.castLE (by omega)) (Fin.castLE_injective _))
    apply top_unique
    rw [← B.span_eq]
    apply Submodule.span_mono
    rintro _ ⟨i,rfl⟩
    change (B i : rationalRealSpan4 P) ∈ restrictedLattice4 P A₂ A₃ Q c₂ c₃
    have hB : (B i : rationalRealSpan4 P) = v (Fin.castLE (by omega) i) :=
      Basis.span_apply (hv.comp (Fin.castLE (by omega)) (Fin.castLE_injective _)) i
    rw [hB]
    exact hvL _


end CompoundFeasibility.RestrictedGeometry4
