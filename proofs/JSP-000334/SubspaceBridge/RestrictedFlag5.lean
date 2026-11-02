import SubspaceBridge.RestrictedAttainment5
noncomputable section
namespace CompoundFeasibility.RestrictedGeometry5
variable (P : Submodule ℚ (Fin 5 → ℚ))
variable (A₂ A₃ : Matrix (Fin 5) (Fin 5) ℚ) (Q : ℝ) (c₂ c₃ : Fin 5 → ℝ)

def restrictedLatticeFlag5 {n : ℕ} (v : Fin n → rationalRealSpan5 P) (k : Fin n) :
    Submodule ℤ (restrictedLattice5 P A₂ A₃ Q c₂ c₃) :=
  ((intrinsicPrefix5 v k).restrictScalars ℤ).comap
    (restrictedLattice5 P A₂ A₃ Q c₂ c₃).subtype

def restrictedFlagLattice5 {n : ℕ} (v : Fin n → rationalRealSpan5 P) (k : Fin n) :
    Submodule ℤ (intrinsicPrefix5 v k) :=
  (restrictedLattice5 P A₂ A₃ Q c₂ c₃).comap
    ((intrinsicPrefix5 v k).subtype.restrictScalars ℤ)

theorem restrictedLatticeFlag5_saturated {n : ℕ}
    (v : Fin n → rationalRealSpan5 P) (k : Fin n) (z : ℤ) (hz : z ≠ 0)
    (x : restrictedLattice5 P A₂ A₃ Q c₂ c₃)
    (hx : z • x ∈ restrictedLatticeFlag5 P A₂ A₃ Q c₂ c₃ v k) :
    x ∈ restrictedLatticeFlag5 P A₂ A₃ Q c₂ c₃ v k := by
  change z • (x : rationalRealSpan5 P) ∈ intrinsicPrefix5 v k at hx
  rw [← Int.cast_smul_eq_zsmul ℝ] at hx
  exact (Submodule.smul_mem_iff (intrinsicPrefix5 v k)
    (by exact_mod_cast hz : (z : ℝ) ≠ 0)).mp hx

def restrictedLatticeFlag5_equiv {n : ℕ} (v : Fin n → rationalRealSpan5 P) (k : Fin n) :
    restrictedLatticeFlag5 P A₂ A₃ Q c₂ c₃ v k ≃ₗ[ℤ]
      restrictedFlagLattice5 P A₂ A₃ Q c₂ c₃ v k where
  toFun x := ⟨⟨x.val.val,x.property⟩,x.val.property⟩
  invFun x := ⟨⟨x.val.val,x.property⟩,x.val.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

instance restrictedFlagLattice5_discrete {n : ℕ}
    (v : Fin n → rationalRealSpan5 P) (k : Fin n) :
    DiscreteTopology (restrictedFlagLattice5 P A₂ A₃ Q c₂ c₃ v k) := by
  let f : restrictedFlagLattice5 P A₂ A₃ Q c₂ c₃ v k →
      restrictedLattice5 P A₂ A₃ Q c₂ c₃ := fun x => ⟨x.val.val,x.property⟩
  apply DiscreteTopology.of_continuous_injective (f := f)
  · exact (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  · intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : restrictedLattice5 P A₂ A₃ Q c₂ c₃ => (z : rationalRealSpan5 P)) h

theorem restrictedFlagLattice5_isZLattice {n : ℕ}
    (v : Fin n → rationalRealSpan5 P) (hv : LinearIndependent ℝ v)
    (hvL : ∀ i, v i ∈ restrictedLattice5 P A₂ A₃ Q c₂ c₃) (k : Fin n) :
    IsZLattice ℝ (E := intrinsicPrefix5 v k) (restrictedFlagLattice5 P A₂ A₃ Q c₂ c₃ v k) where
  span_top := by
    let B : Basis (Fin k.val) ℝ (intrinsicPrefix5 v k) :=
      Basis.span (hv.comp (Fin.castLE (by omega)) (Fin.castLE_injective _))
    apply top_unique
    rw [← B.span_eq]
    apply Submodule.span_mono
    rintro _ ⟨i,rfl⟩
    change (B i : rationalRealSpan5 P) ∈ restrictedLattice5 P A₂ A₃ Q c₂ c₃
    have hB : (B i : rationalRealSpan5 P) = v (Fin.castLE (by omega) i) :=
      Basis.span_apply (hv.comp (Fin.castLE (by omega)) (Fin.castLE_injective _)) i
    rw [hB]
    exact hvL _


end CompoundFeasibility.RestrictedGeometry5
