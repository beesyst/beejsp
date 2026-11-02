import SubspaceBridge.RestrictedFlag4
import SubspaceBridge.RestrictedMinkowski4
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
open scoped BigOperators
open MeasureTheory
noncomputable section
namespace CompoundFeasibility.RestrictedRecovery2Literal4
open RestrictedGeometry4


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




variable {P : Submodule ℚ (Fin 4 → ℚ)}
variable {A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ} {Q : ℝ} {c₂ c₃ : Fin 4 → ℝ} {d : ℕ}

def restrictedIntegerPoint4
    (c : Basis (Fin d) ℤ (restrictedLattice4 P A₂ A₃ Q c₂ c₃))
    (z : Fin d → ℤ) : rationalRealSpan4 P :=
  (c.equivFun.symm z : restrictedLattice4 P A₂ A₃ Q c₂ c₃)

theorem restrictedIntegerPoint4_mem
    (c : Basis (Fin d) ℤ (restrictedLattice4 P A₂ A₃ Q c₂ c₃)) (z : Fin d → ℤ) :
    restrictedIntegerPoint4 c z ∈ restrictedLattice4 P A₂ A₃ Q c₂ c₃ :=
  (c.equivFun.symm z).property

theorem restrictedIntegerPoint4_coord
    (c : Basis (Fin d) ℤ (restrictedLattice4 P A₂ A₃ Q c₂ c₃)) (z : Fin d → ℤ) (i : Fin d) :
    (c.ofZLatticeBasis ℝ _).repr (restrictedIntegerPoint4 c z) i = (z i : ℝ) := by
  rw [restrictedIntegerPoint4,Basis.ofZLatticeBasis_repr_apply]
  change ((c.equivFun (c.equivFun.symm z)) i : ℝ) = (z i : ℝ)
  rw [LinearEquiv.apply_symm_apply]

theorem restrictedIntegerPoint4_outside
    (c : Basis (Fin d) ℤ (restrictedLattice4 P A₂ A₃ Q c₂ c₃))
    (v : Fin d → rationalRealSpan4 P)
    (hadapt : ∀ k : Fin d, Submodule.span ℝ (Set.range (fun i : Fin k.val =>
      ((c (Fin.castLE (by omega) i) : restrictedLattice4 P A₂ A₃ Q c₂ c₃) :
        rationalRealSpan4 P))) = intrinsicPrefix4 v k)
    (z : Fin d → ℤ) (k : Fin d) (hk : z k ≠ 0) :
    restrictedIntegerPoint4 c z ∉ intrinsicPrefix4 v k := by
  let b := c.ofZLatticeBasis ℝ (restrictedLattice4 P A₂ A₃ Q c₂ c₃)
  have hle : intrinsicPrefix4 v k ≤ LinearMap.ker (b.coord k) := by
    rw [← hadapt k]
    apply Submodule.span_le.mpr
    rintro _ ⟨j,rfl⟩
    change b.repr ((c (Fin.castLE (by omega) j) : restrictedLattice4 P A₂ A₃ Q c₂ c₃) :
      rationalRealSpan4 P) k = 0
    have hne : (Fin.castLE (by omega) j : Fin d) ≠ k := by
      intro h
      have heq := congrArg Fin.val h
      change j.val = k.val at heq
      omega
    simp [b,Basis.ofZLatticeBasis_repr_apply,hne]
  intro h
  have hzero := hle h
  change b.repr (restrictedIntegerPoint4 c z) k = 0 at hzero
  rw [restrictedIntegerPoint4_coord] at hzero
  exact hk (by exact_mod_cast hzero)

theorem restrictedIntegerPoint4_short_bound
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L) (hQ : 1 < Q) (c₀ : Fin 4 → ℝ)
    (c : Basis (Fin d) ℤ (restrictedLattice4 P A₂ A₃ Q c₂ c₃))
    (v : Fin d → rationalRealSpan4 P)
    (hadapt : ∀ k : Fin d, Submodule.span ℝ (Set.range (fun i : Fin k.val =>
      ((c (Fin.castLE (by omega) i) : restrictedLattice4 P A₂ A₃ Q c₂ c₃) :
        rationalRealSpan4 P))) = intrinsicPrefix4 v k)
    (hshort : ∀ i, ∀ y ∈ restrictedLattice4 P A₂ A₃ Q c₂ c₃, y ∉ intrinsicPrefix4 v i →
      restrictedGauge4 P L hL Q hQ c₀ (v i) ≤ restrictedGauge4 P L hL Q hQ c₀ y)
    (z : Fin d → ℤ) (k : Fin d) (hk : z k ≠ 0) :
    restrictedGauge4 P L hL Q hQ c₀ (v k) ≤
      restrictedGauge4 P L hL Q hQ c₀ (restrictedIntegerPoint4 c z) := by
  exact hshort k _ (restrictedIntegerPoint4_mem c z)
    (restrictedIntegerPoint4_outside c v hadapt z k hk)


theorem exists_restricted_short_coordinates4 (P : Submodule ℚ (Fin 4 → ℚ))
    (hP : Module.finrank ℚ P ≤ 3)
    (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c₀ c₂ c₃ : Fin 4 → ℝ) :
    ∃ c : Basis (Fin (Module.finrank ℚ P)) ℤ (restrictedLattice4 P A₂ A₃ Q c₂ c₃),
      ∀ (z : Fin (Module.finrank ℚ P) → ℤ) (k : Fin (Module.finrank ℚ P)), z k ≠ 0 →
        restrictedMinima4 P A₂ A₃ L hL Q hQ c₀ c₂ c₃ k ≤
          restrictedGauge4 P L hL Q hQ c₀ (restrictedIntegerPoint4 c z) := by
  obtain ⟨v,hv,hvL,_,_,hatt,hshort⟩ :=
    exists_restrictedMinima4_attaining P hP A₂ A₃ L hL Q hQ c₀ c₂ c₃
  let dim : Fin 4 := ⟨Module.finrank ℚ P,by omega⟩
  obtain ⟨c,hc⟩ := exists_restricted_adapted_integer_basis4 P A₂ A₃ Q c₂ c₃ hP dim rfl v hv hvL
  refine ⟨c,?_⟩
  intro z k hk
  rw [← hatt k]
  exact restrictedIntegerPoint4_short_bound L hL hQ c₀ c v hc hshort z k hk



variable {P : Submodule ℚ (Fin 4 → ℚ)}
variable {A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ} {Q : ℝ} {c₂ c₃ : Fin 4 → ℝ} {d : ℕ}

theorem restrictedBasis4_map_addHaar
    (c : Basis (Fin d) ℤ (restrictedLattice4 P A₂ A₃ Q c₂ c₃)) :
    Measure.map (c.ofZLatticeBasis ℝ _).equivFun
      (c.ofZLatticeBasis ℝ _).addHaar = volume := by
  let b := c.ofZLatticeBasis ℝ (restrictedLattice4 P A₂ A₃ Q c₂ c₃)
  have heq : b.map b.equivFunL.toLinearEquiv = Pi.basisFun ℝ (Fin d) := by
    ext i j
    simp [Basis.map_apply,Basis.equivFun_apply,Pi.basisFun_apply,Finsupp.single_apply,Pi.single_apply,eq_comm]
  change Measure.map b.equivFunL b.addHaar = volume
  rw [Basis.map_addHaar b b.equivFunL,heq,Basis.addHaar_def,
    Basis.parallelepiped_basisFun,MeasureTheory.addHaarMeasure_eq_volume_pi]

theorem restrictedBasis4_measure_eq_covolume_smul
    (c : Basis (Fin d) ℤ (restrictedLattice4 P A₂ A₃ Q c₂ c₃)) :
    restrictedMeasure4 P =
      ENNReal.ofReal (ZLattice.covolume (restrictedLattice4 P A₂ A₃ Q c₂ c₃)
        (restrictedMeasure4 P)) • (c.ofZLatticeBasis ℝ _).addHaar := by
  let b := c.ofZLatticeBasis ℝ (restrictedLattice4 P A₂ A₃ Q c₂ c₃)
  let mu := restrictedMeasure4 P
  have hcv : ENNReal.ofReal (ZLattice.covolume (restrictedLattice4 P A₂ A₃ Q c₂ c₃) mu) =
      mu (_root_.parallelepiped b) := by
    rw [ZLattice.covolume_eq_measure_fundamentalDomain _ mu (ZLattice.isAddFundamentalDomain c mu)]
    change ENNReal.ofReal (mu (ZSpan.fundamentalDomain b)).toReal = _
    rw [ENNReal.ofReal_toReal (ZSpan.fundamentalDomain_isBounded b).measure_lt_top.ne,
      measure_congr (ZSpan.fundamentalDomain_ae_parallelepiped b mu)]
  have h := Measure.addHaarMeasure_unique mu b.parallelepiped
  rw [← Basis.addHaar_def] at h
  change mu = _
  rw [hcv]
  exact h

theorem restrictedBasis4_volume_ratio
    (c : Basis (Fin d) ℤ (restrictedLattice4 P A₂ A₃ Q c₂ c₃))
    (C : Set (rationalRealSpan4 P)) (hC : IsCompact C) :
    volume.real ((c.ofZLatticeBasis ℝ _).equivFun '' C) =
      (restrictedMeasure4 P).real C /
        ZLattice.covolume (restrictedLattice4 P A₂ A₃ Q c₂ c₃) (restrictedMeasure4 P) := by
  let b := c.ofZLatticeBasis ℝ (restrictedLattice4 P A₂ A₃ Q c₂ c₃)
  have himage : volume (b.equivFun '' C) = b.addHaar C := by
    rw [← restrictedBasis4_map_addHaar c]
    change (Measure.map b.equivFunL b.addHaar) (b.equivFunL '' C) = b.addHaar C
    rw [Measure.map_apply b.equivFunL.continuous.measurable (hC.image b.equivFunL.continuous).measurableSet,
      Set.preimage_image_eq _ b.equivFunL.injective]
  have hcv := restrictedLattice4_covolume_pos P A₂ A₃ Q c₂ c₃
  change (volume (b.equivFun '' C)).toReal = _
  rw [himage]
  apply (eq_div_iff hcv.ne').mpr
  have heq := congrArg (fun mu : Measure (rationalRealSpan4 P) => mu.real C)
    (restrictedBasis4_measure_eq_covolume_smul c)
  simpa [measureReal_def,Measure.smul_apply,ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hcv.le,mul_comm,b] using heq.symm





theorem source_restricted_minkowski_upper4 (P : Submodule ℚ (Fin 4 → ℚ))
    (hP : Module.finrank ℚ P ≤ 3)
    (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c₀ c₂ c₃ : Fin 4 → ℝ) :
    (∏ i, restrictedMinima4 P A₂ A₃ L hL Q hQ c₀ c₂ c₃ i) *
      (restrictedMeasure4 P).real (restrictedBody4 P L Q c₀) /
        ZLattice.covolume (restrictedLattice4 P A₂ A₃ Q c₂ c₃) (restrictedMeasure4 P) ≤
          (4 : ℝ)^(Module.finrank ℚ P) := by
  obtain ⟨c,hshort⟩ := exists_restricted_short_coordinates4 P hP A₂ A₃ L hL Q hQ c₀ c₂ c₃
  obtain ⟨_,_,_,hpos,hmono,_,_⟩ := exists_restrictedMinima4_attaining P hP A₂ A₃ L hL Q hQ c₀ c₂ c₃
  let dim : Fin 4 := ⟨Module.finrank ℚ P,by omega⟩
  let b := c.ofZLatticeBasis ℝ (restrictedLattice4 P A₂ A₃ Q c₂ c₃)
  let e := b.equivFun.symm
  let f : (Fin dim.val → ℝ) → ℝ := fun x => restrictedGauge4 P L hL Q hQ c₀ (e x)
  have hf : ∀ (r : ℝ) (x : Fin dim.val → ℝ), f (r • x) = |r| * f x := by
    intro r x
    simp [f,restrictedGauge4,coordinateGauge4,map_smul,norm_smul,Real.norm_eq_abs]
  have hp (z : Fin dim.val → ℤ) :
      e (fun i => (z i : ℝ)) = restrictedIntegerPoint4 c z := by
    apply b.equivFun.injective
    ext i
    change (b.equivFun (b.equivFun.symm (fun i => (z i : ℝ)))) i = _
    rw [LinearEquiv.apply_symm_apply]
    exact (restrictedIntegerPoint4_coord c z i).symm
  have hbody : {x | f x ≤ 1} = b.equivFun '' restrictedBody4 P L Q c₀ := by
    rw [LinearEquiv.image_eq_preimage]
    ext x
    change restrictedGauge4 P L hL Q hQ c₀ (e x) ≤ 1 ↔ e x ∈ restrictedBody4 P L Q c₀
    rw [restrictedBody4_gauge P L hL Q hQ c₀]
    rfl
  have hconv : Convex ℝ {x | f x ≤ 1} := by
    rw [hbody]
    exact (restrictedBody4_compact_convex P L hL Q hQ c₀).2.linear_image b.equivFun.toLinearMap
  have hsymm : ∀ x, f (-x) = f x := by
    intro x
    simp [f,restrictedGauge4,coordinateGauge4,map_neg]
  have hu := RestrictedMinkowski4.adapted_product_volume_upper dim f hf
    (restrictedMinima4 P A₂ A₃ L hL Q hQ c₀ c₂ c₃) hpos hmono
    (fun z k hk _ => by
      change _ ≤ restrictedGauge4 P L hL Q hQ c₀ (e (fun i => (z i : ℝ)))
      rw [hp]
      exact hshort z k hk) hsymm hconv
  have hvol := restrictedBasis4_volume_ratio c (restrictedBody4 P L Q c₀)
    (restrictedBody4_compact_convex P L hL Q hQ c₀).1
  rw [hbody,hvol] at hu
  simpa only [div_eq_mul_inv,mul_assoc] using hu




theorem crosspolytope_coordinate_volume4 (d : Fin 4) (hd : 0 < d.val) :
    volume {x : Fin d.val → ℝ | ∑ i, |x i| ≤ 1} =
      ENNReal.ofReal ((2 : ℝ)^d.val / (Nat.factorial d.val : ℝ)) := by
  letI : Nonempty (Fin d.val) := ⟨⟨0,hd⟩⟩
  have h := MeasureTheory.volume_sum_rpow_le (Fin d.val) (p := (1 : ℝ)) (by norm_num) 1
  simpa [Real.rpow_one,Real.Gamma_nat_eq_factorial,Real.Gamma_add_one (by norm_num : (1 : ℝ) ≠ 0),Real.Gamma_one] using h

theorem restrictedFrame4_det_lower {P : Submodule ℚ (Fin 4 → ℚ)}
    {A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ} {Q : ℝ} {c₂ c₃ : Fin 4 → ℝ} {d : ℕ}
    (c : Basis (Fin d) ℤ (restrictedLattice4 P A₂ A₃ Q c₂ c₃))
    (v : Fin d → rationalRealSpan4 P) (hv : LinearIndependent ℝ v)
    (hvL : ∀ i, v i ∈ restrictedLattice4 P A₂ A₃ Q c₂ c₃) :
    1 ≤ |(Matrix.of (fun i => (c.ofZLatticeBasis ℝ _).equivFun (v i))).det| := by
  classical
  let b := c.ofZLatticeBasis ℝ (restrictedLattice4 P A₂ A₃ Q c₂ c₃)
  let z : Matrix (Fin d) (Fin d) ℤ := fun i j => c.repr ⟨v i,hvL i⟩ j
  have hz : Matrix.of (fun i => b.equivFun (v i)) = z.map (Int.castRingHom ℝ) := by
    ext i j
    exact Basis.ofZLatticeBasis_repr_apply ℝ _ c ⟨v i,hvL i⟩ j
  have hind : LinearIndependent ℝ (fun i => b.equivFun (v i)) :=
    hv.map' b.equivFun.toLinearMap b.equivFun.ker
  let a := basisOfPiSpaceOfLinearIndependent hind
  have hne : (Matrix.of (fun i => b.equivFun (v i))).det ≠ 0 := by
    rw [← Pi.basisFun_det_apply]
    have ha : (fun i => b.equivFun (v i)) = (a : Fin d → Fin d → ℝ) :=
      (coe_basisOfPiSpaceOfLinearIndependent hind).symm
    rw [ha]
    exact isUnit_iff_ne_zero.mp ((Pi.basisFun ℝ (Fin d)).isUnit_det a)
  have hcast : (Matrix.of (fun i => b.equivFun (v i))).det = (z.det : ℝ) := by
    rw [hz]
    exact ((Int.castRingHom ℝ).map_det z).symm
  have hzne : z.det ≠ 0 := by
    intro h
    apply hne
    rw [hcast,h,Int.cast_zero]
  have hz1 : (1 : ℤ) ≤ |z.det| := by
    have hp : (0 : ℤ) < |z.det| := abs_pos.mpr hzne
    omega
  change 1 ≤ |(Matrix.of (fun i => b.equivFun (v i))).det|
  rw [hcast]
  exact_mod_cast hz1


variable {P : Submodule ℚ (Fin 4 → ℚ)}
variable {A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ} {Q : ℝ} {c₂ c₃ : Fin 4 → ℝ} {d : ℕ}

def restrictedCrosspolytopeMap4
    (c : Basis (Fin d) ℤ (restrictedLattice4 P A₂ A₃ Q c₂ c₃))
    (v : Fin d → rationalRealSpan4 P) (mu : Fin d → ℝ) :
    (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ) :=
  (Pi.basisFun ℝ (Fin d)).constr ℕ
    (fun i => (mu i)⁻¹ • (c.ofZLatticeBasis ℝ _).equivFun (v i))

theorem restrictedCrosspolytopeMap4_det
    (c : Basis (Fin d) ℤ (restrictedLattice4 P A₂ A₃ Q c₂ c₃))
    (v : Fin d → rationalRealSpan4 P) (mu : Fin d → ℝ) :
    LinearMap.det (restrictedCrosspolytopeMap4 c v mu) =
      (∏ i, (mu i)⁻¹) * (Matrix.of (fun i => (c.ofZLatticeBasis ℝ _).equivFun (v i))).det := by
  rw [restrictedCrosspolytopeMap4,← LinearMap.det_toMatrix (Pi.basisFun ℝ (Fin d)),
    ← Basis.toMatrix_eq_toMatrix_constr,← Basis.det_apply,Pi.basisFun_det_apply]
  exact Matrix.det_mul_column (fun i => (mu i)⁻¹) _

theorem restrictedCrosspolytopeMap4_pullback
    (c : Basis (Fin d) ℤ (restrictedLattice4 P A₂ A₃ Q c₂ c₃))
    (v : Fin d → rationalRealSpan4 P) (mu : Fin d → ℝ) (x : Fin d → ℝ) :
    (c.ofZLatticeBasis ℝ _).equivFun.symm (restrictedCrosspolytopeMap4 c v mu x) =
      ∑ i, (x i / mu i) • v i := by
  simp only [restrictedCrosspolytopeMap4,Basis.constr_apply_fintype,
    map_sum,map_smul,LinearEquiv.symm_apply_apply,smul_smul]
  rfl


theorem restrictedCrosspolytope4_subset
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L) (hQ : 1 < Q) (c₀ : Fin 4 → ℝ)
    (c : Basis (Fin d) ℤ (restrictedLattice4 P A₂ A₃ Q c₂ c₃))
    (v : Fin d → rationalRealSpan4 P) (mu : Fin d → ℝ) (hpos : ∀ i, 0 < mu i)
    (hatt : ∀ i, restrictedGauge4 P L hL Q hQ c₀ (v i) = mu i) :
    restrictedCrosspolytopeMap4 c v mu '' {x | ∑ i, |x i| ≤ 1} ⊆
      (c.ofZLatticeBasis ℝ _).equivFun '' restrictedBody4 P L Q c₀ := by
  rintro _ ⟨x,hx,rfl⟩
  rw [LinearEquiv.image_eq_preimage]
  change (c.ofZLatticeBasis ℝ _).equivFun.symm (restrictedCrosspolytopeMap4 c v mu x) ∈
    restrictedBody4 P L Q c₀
  rw [restrictedCrosspolytopeMap4_pullback,restrictedBody4_gauge P L hL Q hQ c₀]
  change ‖originalCoordinates4 L hL Q hQ c₀
    ((∑ i, (x i / mu i) • v i : rationalRealSpan4 P) : Fin 4 → ℝ)‖ ≤ 1
  simp only [Submodule.coe_sum,Submodule.coe_smul,map_sum,map_smul]
  calc
    _ ≤ ∑ i, ‖(x i / mu i) • originalCoordinates4 L hL Q hQ c₀ (v i : Fin 4 → ℝ)‖ :=
      norm_sum_le _ _
    _ = ∑ i, |x i| := by
      apply Finset.sum_congr rfl
      intro i _
      rw [norm_smul,Real.norm_eq_abs]
      change |x i / mu i| * restrictedGauge4 P L hL Q hQ c₀ (v i) = |x i|
      rw [hatt,abs_div,abs_of_pos (hpos i),div_mul_cancel₀ _ (hpos i).ne']
    _ ≤ 1 := hx


theorem restrictedCrosspolytope4_volume (dim : Fin 4) (hdim : 0 < dim.val)
    (c : Basis (Fin dim.val) ℤ (restrictedLattice4 P A₂ A₃ Q c₂ c₃))
    (v : Fin dim.val → rationalRealSpan4 P) (mu : Fin dim.val → ℝ) (hpos : ∀ i, 0 < mu i) :
    volume.real (restrictedCrosspolytopeMap4 c v mu '' {x | ∑ i, |x i| ≤ 1}) =
      ((2 : ℝ)^dim.val / (Nat.factorial dim.val : ℝ)) *
        |(Matrix.of (fun i => (c.ofZLatticeBasis ℝ _).equivFun (v i))).det| / (∏ i, mu i) := by
  rw [measureReal_def,Measure.addHaar_image_linearMap,
    crosspolytope_coordinate_volume4 dim hdim,ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (abs_nonneg _),ENNReal.toReal_ofReal (by positivity),
    restrictedCrosspolytopeMap4_det,abs_mul,Finset.prod_inv_distrib,
    abs_of_pos (inv_pos.mpr (Finset.prod_pos (fun i _ => hpos i)))]
  ring


theorem source_restricted_minkowski_lower4 (P : Submodule ℚ (Fin 4 → ℚ))
    (hPlo : 1 ≤ Module.finrank ℚ P) (hP : Module.finrank ℚ P ≤ 3)
    (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c₀ c₂ c₃ : Fin 4 → ℝ) :
    (2 : ℝ)^(Module.finrank ℚ P) / (Nat.factorial (Module.finrank ℚ P) : ℝ) ≤
      (∏ i, restrictedMinima4 P A₂ A₃ L hL Q hQ c₀ c₂ c₃ i) *
        (restrictedMeasure4 P).real (restrictedBody4 P L Q c₀) /
          ZLattice.covolume (restrictedLattice4 P A₂ A₃ Q c₂ c₃) (restrictedMeasure4 P) := by
  obtain ⟨v,hv,hvL,hpos,_,hatt,_⟩ := exists_restrictedMinima4_attaining P hP A₂ A₃ L hL Q hQ c₀ c₂ c₃
  let dim : Fin 4 := ⟨Module.finrank ℚ P,by omega⟩
  let G := restrictedLattice4 P A₂ A₃ Q c₂ c₃
  let c : Basis (Fin dim.val) ℤ G :=
    Module.finBasisOfFinrankEq ℤ G (restrictedLattice4_rank P hP A₂ A₃ Q c₂ c₃)
  let mu := restrictedMinima4 P A₂ A₃ L hL Q hQ c₀ c₂ c₃
  let b := c.ofZLatticeBasis ℝ G
  let T := restrictedCrosspolytopeMap4 c v mu
  have hinc := restrictedCrosspolytope4_subset L hL hQ c₀ c v mu hpos hatt
  have hcpt : IsCompact (b.equivFun '' restrictedBody4 P L Q c₀) :=
    (restrictedBody4_compact_convex P L hL Q hQ c₀).1.image b.equivFunL.continuous
  have hm : volume.real (T '' {x | ∑ i, |x i| ≤ 1}) ≤
      volume.real (b.equivFun '' restrictedBody4 P L Q c₀) :=
    ENNReal.toReal_mono hcpt.measure_lt_top.ne (measure_mono hinc)
  have hvol := restrictedCrosspolytope4_volume dim (by change 0 < Module.finrank ℚ P; omega)
    c v mu hpos
  have hbody := restrictedBasis4_volume_ratio c (restrictedBody4 P L Q c₀)
    (restrictedBody4_compact_convex P L hL Q hQ c₀).1
  change volume.real (restrictedCrosspolytopeMap4 c v mu '' {x | ∑ i, |x i| ≤ 1}) ≤ _ at hm
  rw [hvol,hbody] at hm
  have hprod : 0 < ∏ i, mu i := Finset.prod_pos (fun i _ => hpos i)
  have hdet := restrictedFrame4_det_lower c v hv hvL
  have hconst : 0 ≤ (2 : ℝ)^dim.val / (Nat.factorial dim.val : ℝ) := by positivity
  have hlow : (2 : ℝ)^dim.val / (Nat.factorial dim.val : ℝ) ≤
      ((2 : ℝ)^dim.val / (Nat.factorial dim.val : ℝ)) *
        |(Matrix.of (fun i => b.equivFun (v i))).det| := by
    exact le_mul_of_one_le_right hconst hdet
  have hcancel := (div_le_iff₀ hprod).mp hm
  calc
    _ ≤ ((2 : ℝ)^dim.val / (Nat.factorial dim.val : ℝ)) *
        |(Matrix.of (fun i => b.equivFun (v i))).det| := hlow
    _ ≤ ((restrictedMeasure4 P).real (restrictedBody4 P L Q c₀) /
        ZLattice.covolume G (restrictedMeasure4 P)) * (∏ i, mu i) := hcancel
    _ = _ := by ring





theorem source_restricted_minkowski4 (P : Submodule ℚ (Fin 4 → ℚ))
    (hPlo : 1 ≤ Module.finrank ℚ P) (hP : Module.finrank ℚ P ≤ 3)
    (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c₀ c₂ c₃ : Fin 4 → ℝ) :
    Module.finrank ℝ (rationalRealSpan4 P) = Module.finrank ℚ P ∧
    Module.finrank ℤ (restrictedLattice4 P A₂ A₃ Q c₂ c₃) = Module.finrank ℚ P ∧
    0 < (restrictedMeasure4 P).real (restrictedBody4 P L Q c₀) ∧
    (restrictedMeasure4 P) (restrictedBody4 P L Q c₀) < ⊤ ∧
    0 < ZLattice.covolume (restrictedLattice4 P A₂ A₃ Q c₂ c₃) (restrictedMeasure4 P) ∧
    ∃ v : Fin (Module.finrank ℚ P) → rationalRealSpan4 P,
      LinearIndependent ℝ v ∧ (∀ i, v i ∈ restrictedLattice4 P A₂ A₃ Q c₂ c₃) ∧
      (∀ i, 0 < restrictedMinima4 P A₂ A₃ L hL Q hQ c₀ c₂ c₃ i) ∧
      Monotone (restrictedMinima4 P A₂ A₃ L hL Q hQ c₀ c₂ c₃) ∧
      (∀ i, restrictedGauge4 P L hL Q hQ c₀ (v i) =
        restrictedMinima4 P A₂ A₃ L hL Q hQ c₀ c₂ c₃ i) ∧
      (∀ i, ∀ y ∈ restrictedLattice4 P A₂ A₃ Q c₂ c₃, y ∉ intrinsicPrefix4 v i →
        restrictedGauge4 P L hL Q hQ c₀ (v i) ≤ restrictedGauge4 P L hL Q hQ c₀ y) ∧
      (2 : ℝ)^(Module.finrank ℚ P) / (Nat.factorial (Module.finrank ℚ P) : ℝ) ≤
        (∏ i, restrictedMinima4 P A₂ A₃ L hL Q hQ c₀ c₂ c₃ i) *
          (restrictedMeasure4 P).real (restrictedBody4 P L Q c₀) /
            ZLattice.covolume (restrictedLattice4 P A₂ A₃ Q c₂ c₃) (restrictedMeasure4 P) ∧
      (∏ i, restrictedMinima4 P A₂ A₃ L hL Q hQ c₀ c₂ c₃ i) *
        (restrictedMeasure4 P).real (restrictedBody4 P L Q c₀) /
          ZLattice.covolume (restrictedLattice4 P A₂ A₃ Q c₂ c₃) (restrictedMeasure4 P) ≤
            (4 : ℝ)^(Module.finrank ℚ P) := by
  obtain ⟨v,hv,hvL,hpos,hmono,hatt,hshort⟩ :=
    exists_restrictedMinima4_attaining P hP A₂ A₃ L hL Q hQ c₀ c₂ c₃
  have hvol := restrictedBody4_volume_pos_finite P L hL Q hQ c₀
  exact ⟨rationalRealSpan4_finrank P hP,restrictedLattice4_rank P hP A₂ A₃ Q c₂ c₃,
    hvol.1,hvol.2,restrictedLattice4_covolume_pos P A₂ A₃ Q c₂ c₃,
    v,hv,hvL,hpos,hmono,hatt,hshort,
    source_restricted_minkowski_lower4 P hPlo hP A₂ A₃ L hL Q hQ c₀ c₂ c₃,
    source_restricted_minkowski_upper4 P hP A₂ A₃ L hL Q hQ c₀ c₂ c₃⟩



#print axioms restrictedFlagLattice4_group


#print axioms restrictedLatticeFlag4_rank_equiv


#print axioms restrictedFlagLattice4_rank_real


#print axioms restrictedPrefix4_rank_real


#print axioms restrictedLatticeFlag4_finrank


#print axioms restrictedLatticeFlag4_basis_real_span


#print axioms intrinsicPrefix4_mono


#print axioms restrictedLatticeFlag4_mono


#print axioms exists_restricted_adapted_integer_basis4


#print axioms restrictedIntegerPoint4


#print axioms restrictedIntegerPoint4_mem


#print axioms restrictedIntegerPoint4_coord


#print axioms restrictedIntegerPoint4_outside


#print axioms restrictedIntegerPoint4_short_bound


#print axioms exists_restricted_short_coordinates4


#print axioms restrictedBasis4_map_addHaar


#print axioms restrictedBasis4_measure_eq_covolume_smul


#print axioms restrictedBasis4_volume_ratio


#print axioms source_restricted_minkowski_upper4


#print axioms crosspolytope_coordinate_volume4


#print axioms restrictedFrame4_det_lower


#print axioms restrictedCrosspolytopeMap4


#print axioms restrictedCrosspolytopeMap4_det


#print axioms restrictedCrosspolytopeMap4_pullback


#print axioms restrictedCrosspolytope4_subset


#print axioms restrictedCrosspolytope4_volume


#print axioms source_restricted_minkowski_lower4


#print axioms source_restricted_minkowski4


end CompoundFeasibility.RestrictedRecovery2Literal4
