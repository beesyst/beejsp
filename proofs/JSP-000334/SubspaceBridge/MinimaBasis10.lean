import SubspaceBridge.Minima10
open scoped BigOperators Matrix
open MeasureTheory
namespace CompoundFeasibility
noncomputable section

def minimaFlag10 (v : Fin 10 → Fin 10 → ℝ) (k : Fin 10) : Submodule ℝ (Fin 10 → ℝ) := minimaPrefix10 v k

theorem minimaFlag10_finrank (v : Fin 10 → Fin 10 → ℝ) (hv : LinearIndependent ℝ v) (k : Fin 10) :
    Module.finrank ℝ (minimaFlag10 v k) = k.val := minimaPrefix10_finrank v hv k

theorem minimaFlag10_mono (v : Fin 10 → (Fin 10 → ℝ)) (k l : Fin 10) (hkl : k ≤ l) :
    minimaFlag10 v k ≤ minimaFlag10 v l := by
  apply Submodule.span_mono
  rintro _ ⟨i, rfl⟩
  refine ⟨Fin.castLE hkl i, ?_⟩
  rfl

def latticeFlag10 (b : Basis (Fin 10) ℝ (Fin 10 → ℝ)) (v : Fin 10 → (Fin 10 → ℝ))
    (k : Fin 10) : Submodule ℤ (lattice10Span b) :=
  ((minimaFlag10 v k).restrictScalars ℤ).comap (lattice10Span b).subtype

def flagLattice10 (b : Basis (Fin 10) ℝ (Fin 10 → ℝ)) (v : Fin 10 → (Fin 10 → ℝ))
    (k : Fin 10) : Submodule ℤ (minimaFlag10 v k) :=
  (lattice10Span b).comap ((minimaFlag10 v k).subtype.restrictScalars ℤ)

theorem latticeFlag10_saturated (b : Basis (Fin 10) ℝ (Fin 10 → ℝ))
    (v : Fin 10 → (Fin 10 → ℝ)) (k : Fin 10) (n : ℤ) (hn : n ≠ 0)
    (x : lattice10Span b) (hx : n • x ∈ latticeFlag10 b v k) :
    x ∈ latticeFlag10 b v k := by
  change n • (x : (Fin 10 → ℝ)) ∈ minimaFlag10 v k at hx
  rw [← Int.cast_smul_eq_zsmul ℝ] at hx
  change (x : (Fin 10 → ℝ)) ∈ minimaFlag10 v k
  exact (Submodule.smul_mem_iff (minimaFlag10 v k) (by exact_mod_cast hn : (n : ℝ) ≠ 0)).mp hx

noncomputable def latticeFlag10_equiv_flagLattice10 (b : Basis (Fin 10) ℝ (Fin 10 → ℝ))
    (v : Fin 10 → (Fin 10 → ℝ)) (k : Fin 10) :
    latticeFlag10 b v k ≃ₗ[ℤ] flagLattice10 b v k where
  toFun x := ⟨⟨x.val.val, x.property⟩, x.val.property⟩
  invFun x := ⟨⟨x.val.val, x.property⟩, x.val.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

instance flagLattice10_discrete (b : Basis (Fin 10) ℝ (Fin 10 → ℝ))
    (v : Fin 10 → (Fin 10 → ℝ)) (k : Fin 10) : DiscreteTopology (flagLattice10 b v k) := by
  let f : flagLattice10 b v k → lattice10Span b := fun x => ⟨x.val.val, x.property⟩
  apply DiscreteTopology.of_continuous_injective (f := f)
  · exact (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  · intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : lattice10Span b => (z : (Fin 10 → ℝ))) h

instance flagLattice10_isZLattice (b : Basis (Fin 10) ℝ (Fin 10 → ℝ))
    (v : Fin 10 → (Fin 10 → ℝ)) (hv : LinearIndependent ℝ v)
    (hvL : ∀ i, v i ∈ lattice10Span b) (k : Fin 10) :
    IsZLattice ℝ (flagLattice10 b v k) where
  span_top := by
    let u : Fin k.val → (Fin 10 → ℝ) := fun i => v (Fin.castLE (by omega) i)
    let B : Basis (Fin k.val) ℝ (minimaFlag10 v k) :=
      Basis.span (hv.comp (Fin.castLE (by omega)) (Fin.castLE_injective _))
    apply top_unique
    rw [← B.span_eq]
    apply Submodule.span_mono
    rintro _ ⟨i, rfl⟩
    change (B i : (Fin 10 → ℝ)) ∈ lattice10Span b
    have hB : (B i : (Fin 10 → ℝ)) = u i :=
      Basis.span_apply (hv.comp (Fin.castLE (by omega)) (Fin.castLE_injective _)) i
    rw [hB]
    exact hvL (Fin.castLE (by omega) i)

theorem latticeFlag10_finrank (b : Basis (Fin 10) ℝ (Fin 10 → ℝ))
    (v : Fin 10 → (Fin 10 → ℝ)) (hv : LinearIndependent ℝ v)
    (hvL : ∀ i, v i ∈ lattice10Span b) (k : Fin 10) :
    Module.finrank ℤ (latticeFlag10 b v k) = k.val := by
  letI := flagLattice10_isZLattice b v hv hvL k
  rw [(latticeFlag10_equiv_flagLattice10 b v k).finrank_eq,
    ZLattice.rank ℝ (flagLattice10 b v k), minimaFlag10_finrank v hv k]


theorem latticeFlag10_basis_real_span {ι : Type*}
    (b : Basis (Fin 10) ℝ (Fin 10 → ℝ)) (v : Fin 10 → (Fin 10 → ℝ))
    (hvL : ∀ i, v i ∈ lattice10Span b) (k : Fin 10)
    (a : @Basis ι ℤ (latticeFlag10 b v k) _ _ (latticeFlag10 b v k).module) :
    Submodule.span ℝ (Set.range (fun i =>
      (((a i : latticeFlag10 b v k) : lattice10Span b) : (Fin 10 → ℝ)))) = minimaFlag10 v k := by
  let N := latticeFlag10 b v k
  letI nModule : Module ℤ N := N.module
  let W := Submodule.span ℝ (Set.range (fun i =>
    (((a i : latticeFlag10 b v k) : lattice10Span b) : (Fin 10 → ℝ))))
  have hw : ∀ x : N, ((x : lattice10Span b) : (Fin 10 → ℝ)) ∈ W := by
    have h : Submodule.span ℤ (Set.range a) ≤
        ((W.restrictScalars ℤ).comap (lattice10Span b).subtype).comap N.subtype := by
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


theorem extend_lattice_flag10
    (b : Basis (Fin 10) ℝ (Fin 10 → ℝ)) (v : Fin 10 → Fin 10 → ℝ)
    (hv : LinearIndependent ℝ v) (hvL : ∀ i, v i ∈ lattice10Span b)
    (k : Fin 9) (a : Basis (Fin k.val) ℤ (latticeFlag10 b v k.castSucc)) :
    ∃ c : Basis (Fin (k.val+1)) ℤ (latticeFlag10 b v k.succ),
      ∀ i : Fin k.val,
        ((c i.castSucc : latticeFlag10 b v k.succ) : lattice10Span b) =
          ((a i : latticeFlag10 b v k.castSucc) : lattice10Span b) := by
  let L := lattice10Span b
  letI lModule : Module ℤ L := (lattice10Span b).module
  letI lFinite : Module.Finite ℤ L := Module.Finite.of_basis (b.restrictScalars ℤ)
  let Nk : Submodule ℤ L := latticeFlag10 b v k.castSucc
  let Nn : Submodule ℤ L := latticeFlag10 b v k.succ
  letI nnModule : Module ℤ Nn := Nn.module
  letI nnFinite : Module.Finite ℤ Nn := Module.Finite.of_injective Nn.subtype Nn.subtype_injective
  letI nnNoZero : NoZeroSMulDivisors ℤ Nn := Submodule.noZeroSMulDivisors Nn
  have hkn : Nk ≤ Nn := fun _ hx => minimaFlag10_mono v _ _ (by change k.val ≤ k.val+1; omega) hx
  let S : Submodule ℤ Nn := Nk.comap Nn.subtype
  letI sModule : Module ℤ S := S.module
  let e : S ≃ₗ[ℤ] Nk := Submodule.comapSubtypeEquivOfLe hkn
  let aS : @Basis (Fin k.val) ℤ S _ _ sModule := a.map e.symm
  obtain ⟨c,hc⟩ := JSP000334.saturated_integer_basis_extend S aS
    (latticeFlag10_finrank b v hv hvL k.succ)
    (fun z hz x hx => latticeFlag10_saturated b v k.castSucc z hz (x : L) hx)
  refine ⟨c,?_⟩
  intro i
  simpa only [aS,Basis.map_apply,e,Submodule.comapSubtypeEquivOfLe_symm_apply] using
    congrArg (fun x : Nn => (x : L)) (hc i)

theorem exists_adapted_integer_basis10
    (b : Basis (Fin 10) ℝ (Fin 10 → ℝ)) (v : Fin 10 → Fin 10 → ℝ)
    (hv : LinearIndependent ℝ v) (hvL : ∀ i, v i ∈ lattice10Span b) :
    ∃ c : Basis (Fin 10) ℤ (lattice10Span b), ∀ k : Fin 10,
      Submodule.span ℝ (Set.range (fun i : Fin k.val =>
        ((c (Fin.castLE (by omega) i) : lattice10Span b) : Fin 10 → ℝ))) = minimaFlag10 v k := by
  classical
  let L := lattice10Span b
  letI lModule : Module ℤ L := (lattice10Span b).module
  letI lFinite : Module.Finite ℤ L := Module.Finite.of_basis (b.restrictScalars ℤ)
  letI lFree : Module.Free ℤ L := Module.Free.of_basis (b.restrictScalars ℤ)
  letI lNoZero : NoZeroSMulDivisors ℤ L := Submodule.noZeroSMulDivisors L
  let N1 : Submodule ℤ L := latticeFlag10 b v 1
  let N2 : Submodule ℤ L := latticeFlag10 b v 2
  let N3 : Submodule ℤ L := latticeFlag10 b v 3
  let N4 : Submodule ℤ L := latticeFlag10 b v 4
  let N5 : Submodule ℤ L := latticeFlag10 b v 5
  let N6 : Submodule ℤ L := latticeFlag10 b v 6
  let N7 : Submodule ℤ L := latticeFlag10 b v 7
  let N8 : Submodule ℤ L := latticeFlag10 b v 8
  let N9 : Submodule ℤ L := latticeFlag10 b v 9
  letI n1Module : Module ℤ N1 := N1.module
  letI n1Finite : Module.Finite ℤ N1 := Module.Finite.of_injective N1.subtype N1.subtype_injective
  letI n1NoZero : NoZeroSMulDivisors ℤ N1 := Submodule.noZeroSMulDivisors N1
  letI n1Free : Module.Free ℤ N1 := Module.free_of_finite_type_torsion_free'
  have hr1 : Module.finrank ℤ N1 = 1 := latticeFlag10_finrank b v hv hvL 1
  have hrL : Module.finrank ℤ L = 10 := by
    simpa using Module.finrank_eq_card_basis (b.restrictScalars ℤ)
  let a1 : @Basis (Fin 1) ℤ N1 _ _ n1Module := Module.finBasisOfFinrankEq ℤ N1 hr1
  obtain ⟨a2,he1⟩ := extend_lattice_flag10 b v hv hvL 1 a1
  obtain ⟨a3,he2⟩ := extend_lattice_flag10 b v hv hvL 2 a2
  obtain ⟨a4,he3⟩ := extend_lattice_flag10 b v hv hvL 3 a3
  obtain ⟨a5,he4⟩ := extend_lattice_flag10 b v hv hvL 4 a4
  obtain ⟨a6,he5⟩ := extend_lattice_flag10 b v hv hvL 5 a5
  obtain ⟨a7,he6⟩ := extend_lattice_flag10 b v hv hvL 6 a6
  obtain ⟨a8,he7⟩ := extend_lattice_flag10 b v hv hvL 7 a7
  obtain ⟨a9,he8⟩ := extend_lattice_flag10 b v hv hvL 8 a8
  obtain ⟨c,hc⟩ := JSP000334.saturated_integer_basis_extend N9 a9 hrL (latticeFlag10_saturated b v 9)
  refine ⟨c,?_⟩
  intro k
  fin_cases k
  · simp [minimaFlag10,minimaPrefix10]
  · change Submodule.span ℝ (Set.range (fun i : Fin 1 =>
      ((c (Fin.castLE (by omega) i) : L) : Fin 10 → ℝ))) = minimaFlag10 v 1
    have heq : (fun i : Fin 1 => ((c (Fin.castLE (by omega) i) : L) : Fin 10 → ℝ)) =
        (fun i : Fin 1 => (((a1 i : N1) : L) : Fin 10 → ℝ)) := by
      funext i
      apply congrArg (fun x : L => (x : Fin 10 → ℝ))
      calc
        (c (Fin.castLE (by omega) i) : L) = (a9 i.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc : L) := hc i.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc
        _ = (a8 i.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc : L) := he8 i.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc
        _ = (a7 i.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc : L) := he7 i.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc
        _ = (a6 i.castSucc.castSucc.castSucc.castSucc.castSucc : L) := he6 i.castSucc.castSucc.castSucc.castSucc.castSucc
        _ = (a5 i.castSucc.castSucc.castSucc.castSucc : L) := he5 i.castSucc.castSucc.castSucc.castSucc
        _ = (a4 i.castSucc.castSucc.castSucc : L) := he4 i.castSucc.castSucc.castSucc
        _ = (a3 i.castSucc.castSucc : L) := he3 i.castSucc.castSucc
        _ = (a2 i.castSucc : L) := he2 i.castSucc
        _ = (a1 i : L) := he1 i
    rw [heq]
    exact latticeFlag10_basis_real_span b v hvL 1 a1
  · change Submodule.span ℝ (Set.range (fun i : Fin 2 =>
      ((c (Fin.castLE (by omega) i) : L) : Fin 10 → ℝ))) = minimaFlag10 v 2
    have heq : (fun i : Fin 2 => ((c (Fin.castLE (by omega) i) : L) : Fin 10 → ℝ)) =
        (fun i : Fin 2 => (((a2 i : N2) : L) : Fin 10 → ℝ)) := by
      funext i
      apply congrArg (fun x : L => (x : Fin 10 → ℝ))
      calc
        (c (Fin.castLE (by omega) i) : L) = (a9 i.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc : L) := hc i.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc
        _ = (a8 i.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc : L) := he8 i.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc
        _ = (a7 i.castSucc.castSucc.castSucc.castSucc.castSucc : L) := he7 i.castSucc.castSucc.castSucc.castSucc.castSucc
        _ = (a6 i.castSucc.castSucc.castSucc.castSucc : L) := he6 i.castSucc.castSucc.castSucc.castSucc
        _ = (a5 i.castSucc.castSucc.castSucc : L) := he5 i.castSucc.castSucc.castSucc
        _ = (a4 i.castSucc.castSucc : L) := he4 i.castSucc.castSucc
        _ = (a3 i.castSucc : L) := he3 i.castSucc
        _ = (a2 i : L) := he2 i
    rw [heq]
    exact latticeFlag10_basis_real_span b v hvL 2 a2
  · change Submodule.span ℝ (Set.range (fun i : Fin 3 =>
      ((c (Fin.castLE (by omega) i) : L) : Fin 10 → ℝ))) = minimaFlag10 v 3
    have heq : (fun i : Fin 3 => ((c (Fin.castLE (by omega) i) : L) : Fin 10 → ℝ)) =
        (fun i : Fin 3 => (((a3 i : N3) : L) : Fin 10 → ℝ)) := by
      funext i
      apply congrArg (fun x : L => (x : Fin 10 → ℝ))
      calc
        (c (Fin.castLE (by omega) i) : L) = (a9 i.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc : L) := hc i.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc
        _ = (a8 i.castSucc.castSucc.castSucc.castSucc.castSucc : L) := he8 i.castSucc.castSucc.castSucc.castSucc.castSucc
        _ = (a7 i.castSucc.castSucc.castSucc.castSucc : L) := he7 i.castSucc.castSucc.castSucc.castSucc
        _ = (a6 i.castSucc.castSucc.castSucc : L) := he6 i.castSucc.castSucc.castSucc
        _ = (a5 i.castSucc.castSucc : L) := he5 i.castSucc.castSucc
        _ = (a4 i.castSucc : L) := he4 i.castSucc
        _ = (a3 i : L) := he3 i
    rw [heq]
    exact latticeFlag10_basis_real_span b v hvL 3 a3
  · change Submodule.span ℝ (Set.range (fun i : Fin 4 =>
      ((c (Fin.castLE (by omega) i) : L) : Fin 10 → ℝ))) = minimaFlag10 v 4
    have heq : (fun i : Fin 4 => ((c (Fin.castLE (by omega) i) : L) : Fin 10 → ℝ)) =
        (fun i : Fin 4 => (((a4 i : N4) : L) : Fin 10 → ℝ)) := by
      funext i
      apply congrArg (fun x : L => (x : Fin 10 → ℝ))
      calc
        (c (Fin.castLE (by omega) i) : L) = (a9 i.castSucc.castSucc.castSucc.castSucc.castSucc : L) := hc i.castSucc.castSucc.castSucc.castSucc.castSucc
        _ = (a8 i.castSucc.castSucc.castSucc.castSucc : L) := he8 i.castSucc.castSucc.castSucc.castSucc
        _ = (a7 i.castSucc.castSucc.castSucc : L) := he7 i.castSucc.castSucc.castSucc
        _ = (a6 i.castSucc.castSucc : L) := he6 i.castSucc.castSucc
        _ = (a5 i.castSucc : L) := he5 i.castSucc
        _ = (a4 i : L) := he4 i
    rw [heq]
    exact latticeFlag10_basis_real_span b v hvL 4 a4
  · change Submodule.span ℝ (Set.range (fun i : Fin 5 =>
      ((c (Fin.castLE (by omega) i) : L) : Fin 10 → ℝ))) = minimaFlag10 v 5
    have heq : (fun i : Fin 5 => ((c (Fin.castLE (by omega) i) : L) : Fin 10 → ℝ)) =
        (fun i : Fin 5 => (((a5 i : N5) : L) : Fin 10 → ℝ)) := by
      funext i
      apply congrArg (fun x : L => (x : Fin 10 → ℝ))
      calc
        (c (Fin.castLE (by omega) i) : L) = (a9 i.castSucc.castSucc.castSucc.castSucc : L) := hc i.castSucc.castSucc.castSucc.castSucc
        _ = (a8 i.castSucc.castSucc.castSucc : L) := he8 i.castSucc.castSucc.castSucc
        _ = (a7 i.castSucc.castSucc : L) := he7 i.castSucc.castSucc
        _ = (a6 i.castSucc : L) := he6 i.castSucc
        _ = (a5 i : L) := he5 i
    rw [heq]
    exact latticeFlag10_basis_real_span b v hvL 5 a5
  · change Submodule.span ℝ (Set.range (fun i : Fin 6 =>
      ((c (Fin.castLE (by omega) i) : L) : Fin 10 → ℝ))) = minimaFlag10 v 6
    have heq : (fun i : Fin 6 => ((c (Fin.castLE (by omega) i) : L) : Fin 10 → ℝ)) =
        (fun i : Fin 6 => (((a6 i : N6) : L) : Fin 10 → ℝ)) := by
      funext i
      apply congrArg (fun x : L => (x : Fin 10 → ℝ))
      calc
        (c (Fin.castLE (by omega) i) : L) = (a9 i.castSucc.castSucc.castSucc : L) := hc i.castSucc.castSucc.castSucc
        _ = (a8 i.castSucc.castSucc : L) := he8 i.castSucc.castSucc
        _ = (a7 i.castSucc : L) := he7 i.castSucc
        _ = (a6 i : L) := he6 i
    rw [heq]
    exact latticeFlag10_basis_real_span b v hvL 6 a6
  · change Submodule.span ℝ (Set.range (fun i : Fin 7 =>
      ((c (Fin.castLE (by omega) i) : L) : Fin 10 → ℝ))) = minimaFlag10 v 7
    have heq : (fun i : Fin 7 => ((c (Fin.castLE (by omega) i) : L) : Fin 10 → ℝ)) =
        (fun i : Fin 7 => (((a7 i : N7) : L) : Fin 10 → ℝ)) := by
      funext i
      apply congrArg (fun x : L => (x : Fin 10 → ℝ))
      calc
        (c (Fin.castLE (by omega) i) : L) = (a9 i.castSucc.castSucc : L) := hc i.castSucc.castSucc
        _ = (a8 i.castSucc : L) := he8 i.castSucc
        _ = (a7 i : L) := he7 i
    rw [heq]
    exact latticeFlag10_basis_real_span b v hvL 7 a7
  · change Submodule.span ℝ (Set.range (fun i : Fin 8 =>
      ((c (Fin.castLE (by omega) i) : L) : Fin 10 → ℝ))) = minimaFlag10 v 8
    have heq : (fun i : Fin 8 => ((c (Fin.castLE (by omega) i) : L) : Fin 10 → ℝ)) =
        (fun i : Fin 8 => (((a8 i : N8) : L) : Fin 10 → ℝ)) := by
      funext i
      apply congrArg (fun x : L => (x : Fin 10 → ℝ))
      calc
        (c (Fin.castLE (by omega) i) : L) = (a9 i.castSucc : L) := hc i.castSucc
        _ = (a8 i : L) := he8 i
    rw [heq]
    exact latticeFlag10_basis_real_span b v hvL 8 a8
  · change Submodule.span ℝ (Set.range (fun i : Fin 9 =>
      ((c (Fin.castLE (by omega) i) : L) : Fin 10 → ℝ))) = minimaFlag10 v 9
    have heq : (fun i : Fin 9 => ((c (Fin.castLE (by omega) i) : L) : Fin 10 → ℝ)) =
        (fun i : Fin 9 => (((a9 i : N9) : L) : Fin 10 → ℝ)) := by
      funext i
      apply congrArg (fun x : L => (x : Fin 10 → ℝ))
      exact hc i
    rw [heq]
    exact latticeFlag10_basis_real_span b v hvL 9 a9

end
end CompoundFeasibility
