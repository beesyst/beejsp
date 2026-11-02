import SubspaceBridge.Minima5
open scoped BigOperators Matrix
open MeasureTheory
namespace CompoundFeasibility
noncomputable section

def minimaFlag5 (v : Fin 5 → Fin 5 → ℝ) (k : Fin 5) : Submodule ℝ (Fin 5 → ℝ) := minimaPrefix5 v k

theorem minimaFlag5_finrank (v : Fin 5 → Fin 5 → ℝ) (hv : LinearIndependent ℝ v) (k : Fin 5) :
    Module.finrank ℝ (minimaFlag5 v k) = k.val := minimaPrefix5_finrank v hv k

theorem minimaFlag5_mono (v : Fin 5 → (Fin 5 → ℝ)) (k l : Fin 5) (hkl : k ≤ l) :
    minimaFlag5 v k ≤ minimaFlag5 v l := by
  apply Submodule.span_mono
  rintro _ ⟨i, rfl⟩
  refine ⟨Fin.castLE hkl i, ?_⟩
  rfl

def latticeFlag5 (b : Basis (Fin 5) ℝ (Fin 5 → ℝ)) (v : Fin 5 → (Fin 5 → ℝ))
    (k : Fin 5) : Submodule ℤ (lattice5Span b) :=
  ((minimaFlag5 v k).restrictScalars ℤ).comap (lattice5Span b).subtype

def flagLattice5 (b : Basis (Fin 5) ℝ (Fin 5 → ℝ)) (v : Fin 5 → (Fin 5 → ℝ))
    (k : Fin 5) : Submodule ℤ (minimaFlag5 v k) :=
  (lattice5Span b).comap ((minimaFlag5 v k).subtype.restrictScalars ℤ)

theorem latticeFlag5_saturated (b : Basis (Fin 5) ℝ (Fin 5 → ℝ))
    (v : Fin 5 → (Fin 5 → ℝ)) (k : Fin 5) (n : ℤ) (hn : n ≠ 0)
    (x : lattice5Span b) (hx : n • x ∈ latticeFlag5 b v k) :
    x ∈ latticeFlag5 b v k := by
  change n • (x : (Fin 5 → ℝ)) ∈ minimaFlag5 v k at hx
  rw [← Int.cast_smul_eq_zsmul ℝ] at hx
  change (x : (Fin 5 → ℝ)) ∈ minimaFlag5 v k
  exact (Submodule.smul_mem_iff (minimaFlag5 v k) (by exact_mod_cast hn : (n : ℝ) ≠ 0)).mp hx

noncomputable def latticeFlag5_equiv_flagLattice5 (b : Basis (Fin 5) ℝ (Fin 5 → ℝ))
    (v : Fin 5 → (Fin 5 → ℝ)) (k : Fin 5) :
    latticeFlag5 b v k ≃ₗ[ℤ] flagLattice5 b v k where
  toFun x := ⟨⟨x.val.val, x.property⟩, x.val.property⟩
  invFun x := ⟨⟨x.val.val, x.property⟩, x.val.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

instance flagLattice5_discrete (b : Basis (Fin 5) ℝ (Fin 5 → ℝ))
    (v : Fin 5 → (Fin 5 → ℝ)) (k : Fin 5) : DiscreteTopology (flagLattice5 b v k) := by
  let f : flagLattice5 b v k → lattice5Span b := fun x => ⟨x.val.val, x.property⟩
  apply DiscreteTopology.of_continuous_injective (f := f)
  · exact (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  · intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : lattice5Span b => (z : (Fin 5 → ℝ))) h

instance flagLattice5_isZLattice (b : Basis (Fin 5) ℝ (Fin 5 → ℝ))
    (v : Fin 5 → (Fin 5 → ℝ)) (hv : LinearIndependent ℝ v)
    (hvL : ∀ i, v i ∈ lattice5Span b) (k : Fin 5) :
    IsZLattice ℝ (flagLattice5 b v k) where
  span_top := by
    let u : Fin k.val → (Fin 5 → ℝ) := fun i => v (Fin.castLE (by omega) i)
    let B : Basis (Fin k.val) ℝ (minimaFlag5 v k) :=
      Basis.span (hv.comp (Fin.castLE (by omega)) (Fin.castLE_injective _))
    apply top_unique
    rw [← B.span_eq]
    apply Submodule.span_mono
    rintro _ ⟨i, rfl⟩
    change (B i : (Fin 5 → ℝ)) ∈ lattice5Span b
    have hB : (B i : (Fin 5 → ℝ)) = u i :=
      Basis.span_apply (hv.comp (Fin.castLE (by omega)) (Fin.castLE_injective _)) i
    rw [hB]
    exact hvL (Fin.castLE (by omega) i)

theorem latticeFlag5_finrank (b : Basis (Fin 5) ℝ (Fin 5 → ℝ))
    (v : Fin 5 → (Fin 5 → ℝ)) (hv : LinearIndependent ℝ v)
    (hvL : ∀ i, v i ∈ lattice5Span b) (k : Fin 5) :
    Module.finrank ℤ (latticeFlag5 b v k) = k.val := by
  letI := flagLattice5_isZLattice b v hv hvL k
  rw [(latticeFlag5_equiv_flagLattice5 b v k).finrank_eq,
    ZLattice.rank ℝ (flagLattice5 b v k), minimaFlag5_finrank v hv k]


theorem latticeFlag5_basis_real_span {ι : Type*}
    (b : Basis (Fin 5) ℝ (Fin 5 → ℝ)) (v : Fin 5 → (Fin 5 → ℝ))
    (hvL : ∀ i, v i ∈ lattice5Span b) (k : Fin 5)
    (a : @Basis ι ℤ (latticeFlag5 b v k) _ _ (latticeFlag5 b v k).module) :
    Submodule.span ℝ (Set.range (fun i =>
      (((a i : latticeFlag5 b v k) : lattice5Span b) : (Fin 5 → ℝ)))) = minimaFlag5 v k := by
  let N := latticeFlag5 b v k
  letI nModule : Module ℤ N := N.module
  let W := Submodule.span ℝ (Set.range (fun i =>
    (((a i : latticeFlag5 b v k) : lattice5Span b) : (Fin 5 → ℝ))))
  have hw : ∀ x : N, ((x : lattice5Span b) : (Fin 5 → ℝ)) ∈ W := by
    have h : Submodule.span ℤ (Set.range a) ≤
        ((W.restrictScalars ℤ).comap (lattice5Span b).subtype).comap N.subtype := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact Submodule.subset_span (Set.mem_range_self i)
    rw [a.span_eq] at h
    intro x
    exact h (Submodule.mem_top : x ∈ (⊤ : Submodule ℤ N))
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact (a i).property
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    let x : N := ⟨⟨v (Fin.castLE (by omega) i), hvL _⟩,
      Submodule.subset_span (Set.mem_range_self i)⟩
    exact hw x


theorem exists_adapted_integer_basis5
    (b : Basis (Fin 5) ℝ (Fin 5 → ℝ)) (v : Fin 5 → Fin 5 → ℝ)
    (hv : LinearIndependent ℝ v) (hvL : ∀ i, v i ∈ lattice5Span b) :
    ∃ c : Basis (Fin 5) ℤ (lattice5Span b), ∀ k : Fin 5,
      Submodule.span ℝ (Set.range (fun i : Fin k.val =>
        ((c (Fin.castLE (by omega) i) : lattice5Span b) : Fin 5 → ℝ))) = minimaFlag5 v k := by
  classical
  let L := lattice5Span b
  letI lModule : Module ℤ L := (lattice5Span b).module
  letI lFinite : Module.Finite ℤ L := Module.Finite.of_basis (b.restrictScalars ℤ)
  letI lFree : Module.Free ℤ L := Module.Free.of_basis (b.restrictScalars ℤ)
  letI lNoZero : NoZeroSMulDivisors ℤ L := Submodule.noZeroSMulDivisors L
  let N1 : Submodule ℤ L := latticeFlag5 b v 1
  letI n1Module : Module ℤ N1 := N1.module
  letI n1Finite : Module.Finite ℤ N1 := Module.Finite.of_injective N1.subtype N1.subtype_injective
  letI n1NoZero : NoZeroSMulDivisors ℤ N1 := Submodule.noZeroSMulDivisors N1
  letI n1Free : Module.Free ℤ N1 := Module.free_of_finite_type_torsion_free'
  have hr1 : Module.finrank ℤ N1 = 1 := latticeFlag5_finrank b v hv hvL 1
  let N2 : Submodule ℤ L := latticeFlag5 b v 2
  letI n2Module : Module ℤ N2 := N2.module
  letI n2Finite : Module.Finite ℤ N2 := Module.Finite.of_injective N2.subtype N2.subtype_injective
  letI n2NoZero : NoZeroSMulDivisors ℤ N2 := Submodule.noZeroSMulDivisors N2
  letI n2Free : Module.Free ℤ N2 := Module.free_of_finite_type_torsion_free'
  have hr2 : Module.finrank ℤ N2 = 2 := latticeFlag5_finrank b v hv hvL 2
  let N3 : Submodule ℤ L := latticeFlag5 b v 3
  letI n3Module : Module ℤ N3 := N3.module
  letI n3Finite : Module.Finite ℤ N3 := Module.Finite.of_injective N3.subtype N3.subtype_injective
  letI n3NoZero : NoZeroSMulDivisors ℤ N3 := Submodule.noZeroSMulDivisors N3
  letI n3Free : Module.Free ℤ N3 := Module.free_of_finite_type_torsion_free'
  have hr3 : Module.finrank ℤ N3 = 3 := latticeFlag5_finrank b v hv hvL 3
  let N4 : Submodule ℤ L := latticeFlag5 b v 4
  letI n4Module : Module ℤ N4 := N4.module
  letI n4Finite : Module.Finite ℤ N4 := Module.Finite.of_injective N4.subtype N4.subtype_injective
  letI n4NoZero : NoZeroSMulDivisors ℤ N4 := Submodule.noZeroSMulDivisors N4
  letI n4Free : Module.Free ℤ N4 := Module.free_of_finite_type_torsion_free'
  have hr4 : Module.finrank ℤ N4 = 4 := latticeFlag5_finrank b v hv hvL 4
  have h12 : N1 ≤ N2 := fun _ hx => minimaFlag5_mono v 1 2 (by decide) hx
  let S12 : Submodule ℤ N2 := N1.comap N2.subtype
  letI s12Module : Module ℤ S12 := S12.module
  let e12 : S12 ≃ₗ[ℤ] N1 := Submodule.comapSubtypeEquivOfLe h12
  have h23 : N2 ≤ N3 := fun _ hx => minimaFlag5_mono v 2 3 (by decide) hx
  let S23 : Submodule ℤ N3 := N2.comap N3.subtype
  letI s23Module : Module ℤ S23 := S23.module
  let e23 : S23 ≃ₗ[ℤ] N2 := Submodule.comapSubtypeEquivOfLe h23
  have h34 : N3 ≤ N4 := fun _ hx => minimaFlag5_mono v 3 4 (by decide) hx
  let S34 : Submodule ℤ N4 := N3.comap N4.subtype
  letI s34Module : Module ℤ S34 := S34.module
  let e34 : S34 ≃ₗ[ℤ] N3 := Submodule.comapSubtypeEquivOfLe h34
  have hrL : Module.finrank ℤ L = 5 := by
    simpa using Module.finrank_eq_card_basis (b.restrictScalars ℤ)
  let a1 : @Basis (Fin 1) ℤ N1 _ _ n1Module := Module.finBasisOfFinrankEq ℤ N1 hr1
  let aS12 : @Basis (Fin 1) ℤ S12 _ _ s12Module := a1.map e12.symm
  obtain ⟨a2,ha2⟩ := JSP000334.saturated_integer_basis_extend S12 aS12 hr2
    (fun z hz x hx => latticeFlag5_saturated b v 1 z hz (x : L) hx)
  have he1 (i : Fin 1) : ((a2 i.castSucc : N2) : L) = (a1 i : L) := by
    simpa only [aS12,Basis.map_apply,e12,Submodule.comapSubtypeEquivOfLe_symm_apply] using
      congrArg (fun x : N2 => (x : L)) (ha2 i)
  let aS23 : @Basis (Fin 2) ℤ S23 _ _ s23Module := a2.map e23.symm
  obtain ⟨a3,ha3⟩ := JSP000334.saturated_integer_basis_extend S23 aS23 hr3
    (fun z hz x hx => latticeFlag5_saturated b v 2 z hz (x : L) hx)
  have he2 (i : Fin 2) : ((a3 i.castSucc : N3) : L) = (a2 i : L) := by
    simpa only [aS23,Basis.map_apply,e23,Submodule.comapSubtypeEquivOfLe_symm_apply] using
      congrArg (fun x : N3 => (x : L)) (ha3 i)
  let aS34 : @Basis (Fin 3) ℤ S34 _ _ s34Module := a3.map e34.symm
  obtain ⟨a4,ha4⟩ := JSP000334.saturated_integer_basis_extend S34 aS34 hr4
    (fun z hz x hx => latticeFlag5_saturated b v 3 z hz (x : L) hx)
  have he3 (i : Fin 3) : ((a4 i.castSucc : N4) : L) = (a3 i : L) := by
    simpa only [aS34,Basis.map_apply,e34,Submodule.comapSubtypeEquivOfLe_symm_apply] using
      congrArg (fun x : N4 => (x : L)) (ha4 i)
  obtain ⟨c,hc⟩ := JSP000334.saturated_integer_basis_extend N4 a4 hrL (latticeFlag5_saturated b v 4)
  refine ⟨c,?_⟩
  intro k
  fin_cases k
  · simp [minimaFlag5,minimaPrefix5]
  · have heq : (fun i : Fin 1 => ((c (Fin.castLE (by omega) i) : L) : Fin 5 → ℝ)) =
        (fun i : Fin 1 => (((a1 i : N1) : L) : Fin 5 → ℝ)) := by
      funext i
      exact congrArg (fun x : L => (x : Fin 5 → ℝ)) ((((hc (((i).castSucc).castSucc).castSucc).trans (he3 ((i).castSucc).castSucc)).trans (he2 (i).castSucc)).trans (he1 i))
    rw [heq]
    exact latticeFlag5_basis_real_span b v hvL 1 a1
  · have heq : (fun i : Fin 2 => ((c (Fin.castLE (by omega) i) : L) : Fin 5 → ℝ)) =
        (fun i : Fin 2 => (((a2 i : N2) : L) : Fin 5 → ℝ)) := by
      funext i
      exact congrArg (fun x : L => (x : Fin 5 → ℝ)) (((hc ((i).castSucc).castSucc).trans (he3 (i).castSucc)).trans (he2 i))
    rw [heq]
    exact latticeFlag5_basis_real_span b v hvL 2 a2
  · have heq : (fun i : Fin 3 => ((c (Fin.castLE (by omega) i) : L) : Fin 5 → ℝ)) =
        (fun i : Fin 3 => (((a3 i : N3) : L) : Fin 5 → ℝ)) := by
      funext i
      exact congrArg (fun x : L => (x : Fin 5 → ℝ)) ((hc (i).castSucc).trans (he3 i))
    rw [heq]
    exact latticeFlag5_basis_real_span b v hvL 3 a3
  · have heq : (fun i : Fin 4 => ((c (Fin.castLE (by omega) i) : L) : Fin 5 → ℝ)) =
        (fun i : Fin 4 => (((a4 i : N4) : L) : Fin 5 → ℝ)) := by
      funext i
      exact congrArg (fun x : L => (x : Fin 5 → ℝ)) (hc i)
    rw [heq]
    exact latticeFlag5_basis_real_span b v hvL 4 a4

end
end CompoundFeasibility
