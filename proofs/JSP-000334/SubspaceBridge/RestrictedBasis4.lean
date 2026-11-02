import SubspaceBridge.RestrictedFlag4
noncomputable section
namespace CompoundFeasibility.RestrictedGeometry4
variable (P : Submodule ℚ (Fin 4 → ℚ))
variable (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) (Q : ℝ) (c₂ c₃ : Fin 4 → ℝ)

local instance restrictedFlagLattice4_group {n : ℕ}
    (v : Fin n → rationalRealSpan4 P) (k : Fin n) :
    AddCommGroup (restrictedFlagLattice4 P A₂ A₃ Q c₂ c₃ v k) := by
  let S : Submodule ℝ (rationalRealSpan4 P) := intrinsicPrefix4 v k
  letI sGroup : AddCommGroup S := Submodule.addCommGroup S
  letI sModule : Module ℤ S := (S.restrictScalars ℤ).module
  let M : Submodule ℤ S := restrictedFlagLattice4 P A₂ A₃ Q c₂ c₃ v k
  exact Submodule.addCommGroup M

theorem restrictedLatticeFlag4_rank_equiv {n : ℕ}
    (v : Fin n → rationalRealSpan4 P) (k : Fin n) :
    Module.finrank ℤ (restrictedLatticeFlag4 P A₂ A₃ Q c₂ c₃ v k) =
      Module.finrank ℤ (restrictedFlagLattice4 P A₂ A₃ Q c₂ c₃ v k) := by
  let G : Submodule ℤ (rationalRealSpan4 P) := restrictedLattice4 P A₂ A₃ Q c₂ c₃
  let N : Submodule ℤ G := restrictedLatticeFlag4 P A₂ A₃ Q c₂ c₃ v k
  let S : Submodule ℝ (rationalRealSpan4 P) := intrinsicPrefix4 v k
  let M : Submodule ℤ S := restrictedFlagLattice4 P A₂ A₃ Q c₂ c₃ v k
  letI gGroup : AddCommGroup G := Submodule.addCommGroup G
  letI gModule : Module ℤ G := G.module
  letI nGroup : AddCommGroup N := Submodule.addCommGroup N
  letI nModule : Module ℤ N := N.module
  letI sGroup : AddCommGroup S := Submodule.addCommGroup S
  letI sModule : Module ℤ S := (S.restrictScalars ℤ).module
  letI mGroup : AddCommGroup M := Submodule.addCommGroup M
  letI mModule : Module ℤ M := M.module
  let e : N ≃ₗ[ℤ] M := restrictedLatticeFlag4_equiv P A₂ A₃ Q c₂ c₃ v k
  exact e.finrank_eq

theorem restrictedFlagLattice4_rank_real {n : ℕ}
    (v : Fin n → rationalRealSpan4 P) (hv : LinearIndependent ℝ v)
    (hvL : ∀ i, v i ∈ restrictedLattice4 P A₂ A₃ Q c₂ c₃) (k : Fin n) :
    Module.finrank ℤ (restrictedFlagLattice4 P A₂ A₃ Q c₂ c₃ v k) =
      Module.finrank ℝ (intrinsicPrefix4 v k) := by
  let S : Submodule ℝ (rationalRealSpan4 P) := intrinsicPrefix4 v k
  let M : Submodule ℤ S := restrictedFlagLattice4 P A₂ A₃ Q c₂ c₃ v k
  letI sGroup : AddCommGroup S := Submodule.addCommGroup S
  letI sModule : Module ℤ S := (S.restrictScalars ℤ).module
  letI mGroup : AddCommGroup M := Submodule.addCommGroup M
  letI mModule : Module ℤ M := M.module
  letI hM : IsZLattice ℝ (E := S) M :=
    restrictedFlagLattice4_isZLattice P A₂ A₃ Q c₂ c₃ v hv hvL k
  exact ZLattice.rank ℝ (E := S) M


theorem restrictedPrefix4_rank_real {P : Submodule ℚ (Fin 4 → ℚ)} {n : ℕ}
    (v : Fin n → rationalRealSpan4 P) (hv : LinearIndependent ℝ v) (k : Fin n) :
    Module.finrank ℝ (intrinsicPrefix4 v k) = k.val := by
  exact intrinsicPrefix4_finrank v hv k

theorem restrictedLatticeFlag4_finrank {n : ℕ}
    (v : Fin n → rationalRealSpan4 P) (hv : LinearIndependent ℝ v)
    (hvL : ∀ i, v i ∈ restrictedLattice4 P A₂ A₃ Q c₂ c₃) (k : Fin n) :
    Module.finrank ℤ (restrictedLatticeFlag4 P A₂ A₃ Q c₂ c₃ v k) = k.val := by
  exact (restrictedLatticeFlag4_rank_equiv P A₂ A₃ Q c₂ c₃ v k).trans
    ((restrictedFlagLattice4_rank_real P A₂ A₃ Q c₂ c₃ v hv hvL k).trans
      (restrictedPrefix4_rank_real v hv k))


theorem restrictedLatticeFlag4_basis_real_span {ι : Type*} {n : ℕ}
    (v : Fin n → rationalRealSpan4 P)
    (hvL : ∀ i, v i ∈ restrictedLattice4 P A₂ A₃ Q c₂ c₃) (k : Fin n)
    (a : @Basis ι ℤ (restrictedLatticeFlag4 P A₂ A₃ Q c₂ c₃ v k) _ _
      (restrictedLatticeFlag4 P A₂ A₃ Q c₂ c₃ v k).module) :
    Submodule.span ℝ (Set.range (fun i =>
      (((a i : restrictedLatticeFlag4 P A₂ A₃ Q c₂ c₃ v k) :
        restrictedLattice4 P A₂ A₃ Q c₂ c₃) : rationalRealSpan4 P))) = intrinsicPrefix4 v k := by
  let G := restrictedLattice4 P A₂ A₃ Q c₂ c₃
  let N := restrictedLatticeFlag4 P A₂ A₃ Q c₂ c₃ v k
  letI nModule : Module ℤ N := N.module
  let W := Submodule.span ℝ (Set.range (fun i => (((a i : N) : G) : rationalRealSpan4 P)))
  have hw : ∀ x : N, ((x : G) : rationalRealSpan4 P) ∈ W := by
    have h : Submodule.span ℤ (Set.range a) ≤
        ((W.restrictScalars ℤ).comap G.subtype).comap N.subtype := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i,rfl⟩
      exact Submodule.subset_span (Set.mem_range_self i)
    rw [a.span_eq] at h
    intro x
    exact h (Submodule.mem_top : x ∈ (⊤ : Submodule ℤ N))
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact (a i).property
  · apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    let x : N := ⟨⟨v (Fin.castLE (by omega) i),hvL _⟩,
      Submodule.subset_span (Set.mem_range_self i)⟩
    exact hw x

theorem intrinsicPrefix4_mono {n : ℕ} (v : Fin n → rationalRealSpan4 P)
    (i j : Fin n) (hij : i ≤ j) : intrinsicPrefix4 v i ≤ intrinsicPrefix4 v j := by
  apply Submodule.span_le.mpr
  rintro _ ⟨k,rfl⟩
  apply Submodule.subset_span
  refine ⟨Fin.castLE (show i.val ≤ j.val from hij) k,?_⟩
  congr 1



theorem restrictedLatticeFlag4_mono {n : ℕ} (v : Fin n → rationalRealSpan4 P)
    (i j : Fin n) (hij : i ≤ j) :
    restrictedLatticeFlag4 P A₂ A₃ Q c₂ c₃ v i ≤
      restrictedLatticeFlag4 P A₂ A₃ Q c₂ c₃ v j := by
  intro x hx
  exact intrinsicPrefix4_mono P v i j hij hx


theorem exists_restricted_adapted_integer_basis4
    (hP : Module.finrank ℚ P ≤ 3) (d : Fin 4) (hd : Module.finrank ℚ P = d.val)
    (v : Fin d.val → rationalRealSpan4 P) (hv : LinearIndependent ℝ v)
    (hvL : ∀ i, v i ∈ restrictedLattice4 P A₂ A₃ Q c₂ c₃) :
    ∃ c : Basis (Fin d.val) ℤ (restrictedLattice4 P A₂ A₃ Q c₂ c₃), ∀ k : Fin d.val,
      Submodule.span ℝ (Set.range (fun i : Fin k.val =>
        ((c (Fin.castLE (by omega) i) : restrictedLattice4 P A₂ A₃ Q c₂ c₃) :
          rationalRealSpan4 P))) = intrinsicPrefix4 v k := by
  classical
  let G : Submodule ℤ (rationalRealSpan4 P) := restrictedLattice4 P A₂ A₃ Q c₂ c₃
  letI gModule : Module ℤ G := G.module
  letI gFinite : Module.Finite ℤ G := ZLattice.module_finite ℝ G
  letI gNoZero : NoZeroSMulDivisors ℤ G := Submodule.noZeroSMulDivisors G
  letI gFree : Module.Free ℤ G := Module.free_of_finite_type_torsion_free'
  have hrG : Module.finrank ℤ G = d.val :=
    (restrictedLattice4_rank P hP A₂ A₃ Q c₂ c₃).trans hd
  fin_cases d
  · exact ⟨Module.finBasisOfFinrankEq ℤ G hrG,fun k => Fin.elim0 k⟩
  · refine ⟨Module.finBasisOfFinrankEq ℤ G hrG,?_⟩
    intro k
    fin_cases k
    simp [intrinsicPrefix4]
  · let N1 : Submodule ℤ G := restrictedLatticeFlag4 P A₂ A₃ Q c₂ c₃ v 1
    letI n1Module : Module ℤ N1 := N1.module
    letI n1Finite : Module.Finite ℤ N1 := Module.Finite.of_injective N1.subtype N1.subtype_injective
    letI n1NoZero : NoZeroSMulDivisors ℤ N1 := Submodule.noZeroSMulDivisors N1
    letI n1Free : Module.Free ℤ N1 := Module.free_of_finite_type_torsion_free'
    have hr1 : Module.finrank ℤ N1 = 1 :=
      restrictedLatticeFlag4_finrank P A₂ A₃ Q c₂ c₃ v hv hvL 1
    let a : @Basis (Fin 1) ℤ N1 _ _ n1Module := Module.finBasisOfFinrankEq ℤ N1 hr1
    obtain ⟨c,hc⟩ := JSP000334.saturated_integer_basis_extend N1 a hrG
      (restrictedLatticeFlag4_saturated P A₂ A₃ Q c₂ c₃ v 1)
    refine ⟨c,?_⟩
    intro k
    fin_cases k
    · simp [intrinsicPrefix4]
    · have heq : (fun i : Fin 1 => ((c (Fin.castLE (by omega) i) : G) : rationalRealSpan4 P)) =
          (fun i : Fin 1 => (((a i : N1) : G) : rationalRealSpan4 P)) := by
        funext i
        exact congrArg (fun x : G => (x : rationalRealSpan4 P)) (hc i)
      rw [heq]
      exact restrictedLatticeFlag4_basis_real_span P A₂ A₃ Q c₂ c₃ v hvL 1 a
  · let N1 : Submodule ℤ G := restrictedLatticeFlag4 P A₂ A₃ Q c₂ c₃ v 1
    let N2 : Submodule ℤ G := restrictedLatticeFlag4 P A₂ A₃ Q c₂ c₃ v 2
    letI n1Module : Module ℤ N1 := N1.module
    letI n1Finite : Module.Finite ℤ N1 := Module.Finite.of_injective N1.subtype N1.subtype_injective
    letI n1NoZero : NoZeroSMulDivisors ℤ N1 := Submodule.noZeroSMulDivisors N1
    letI n1Free : Module.Free ℤ N1 := Module.free_of_finite_type_torsion_free'
    letI n2Module : Module ℤ N2 := N2.module
    letI n2Finite : Module.Finite ℤ N2 := Module.Finite.of_injective N2.subtype N2.subtype_injective
    letI n2NoZero : NoZeroSMulDivisors ℤ N2 := Submodule.noZeroSMulDivisors N2
    letI n2Free : Module.Free ℤ N2 := Module.free_of_finite_type_torsion_free'
    have h12 : N1 ≤ N2 := restrictedLatticeFlag4_mono P A₂ A₃ Q c₂ c₃ v 1 2 (by decide)
    let S12 : Submodule ℤ N2 := N1.comap N2.subtype
    letI s12Module : Module ℤ S12 := S12.module
    let e12 : S12 ≃ₗ[ℤ] N1 := Submodule.comapSubtypeEquivOfLe h12
    have hr1 : Module.finrank ℤ N1 = 1 :=
      restrictedLatticeFlag4_finrank P A₂ A₃ Q c₂ c₃ v hv hvL 1
    have hr2 : Module.finrank ℤ N2 = 2 :=
      restrictedLatticeFlag4_finrank P A₂ A₃ Q c₂ c₃ v hv hvL 2
    let a : @Basis (Fin 1) ℤ N1 _ _ n1Module := Module.finBasisOfFinrankEq ℤ N1 hr1
    let aS12 : @Basis (Fin 1) ℤ S12 _ _ s12Module := a.map e12.symm
    obtain ⟨a2,ha2⟩ := JSP000334.saturated_integer_basis_extend S12 aS12 hr2
      (fun z hz x hx => restrictedLatticeFlag4_saturated P A₂ A₃ Q c₂ c₃ v 1 z hz (x : G) hx)
    obtain ⟨c,hc⟩ := JSP000334.saturated_integer_basis_extend N2 a2 hrG
      (restrictedLatticeFlag4_saturated P A₂ A₃ Q c₂ c₃ v 2)
    have h1 : ((a2 0 : N2) : G) = (a 0 : G) := by
      simpa only [aS12,Basis.map_apply,e12,Submodule.comapSubtypeEquivOfLe_symm_apply] using
        congrArg (fun x : N2 => (x : G)) (ha2 0)
    refine ⟨c,?_⟩
    intro k
    fin_cases k
    · simp [intrinsicPrefix4]
    · have heq : (fun i : Fin 1 => ((c (Fin.castLE (by omega) i) : G) : rationalRealSpan4 P)) =
          (fun i : Fin 1 => (((a i : N1) : G) : rationalRealSpan4 P)) := by
        funext i
        fin_cases i
        exact congrArg (fun x : G => (x : rationalRealSpan4 P)) ((hc 0).trans h1)
      rw [heq]
      exact restrictedLatticeFlag4_basis_real_span P A₂ A₃ Q c₂ c₃ v hvL 1 a
    · have heq : (fun i : Fin 2 => ((c (Fin.castLE (by omega) i) : G) : rationalRealSpan4 P)) =
          (fun i : Fin 2 => (((a2 i : N2) : G) : rationalRealSpan4 P)) := by
        funext i
        exact congrArg (fun x : G => (x : rationalRealSpan4 P)) (hc i)
      rw [heq]
      exact restrictedLatticeFlag4_basis_real_span P A₂ A₃ Q c₂ c₃ v hvL 2 a2


end CompoundFeasibility.RestrictedGeometry4
