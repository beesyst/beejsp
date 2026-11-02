import SubspaceBridge.RestrictedGeometry4

noncomputable section
namespace CompoundFeasibility.RestrictedRecoveryLiteral4
open RestrictedGeometry4

def intrinsicPrefix4 {P : Submodule ℚ (Fin 4 → ℚ)} {n : ℕ}
    (v : Fin n → rationalRealSpan4 P) (i : Fin n) : Submodule ℝ (rationalRealSpan4 P) :=
  Submodule.span ℝ (Set.range (fun j : Fin i.val => v (Fin.castLE (by omega) j)))

theorem intrinsicPrefix4_snoc_castSucc {P : Submodule ℚ (Fin 4 → ℚ)} {n : ℕ}
    (v : Fin n → rationalRealSpan4 P) (x : rationalRealSpan4 P) (i : Fin n) :
    intrinsicPrefix4 (Fin.snoc v x) i.castSucc = intrinsicPrefix4 v i := by
  unfold intrinsicPrefix4
  apply congrArg (fun u : Fin i.val → rationalRealSpan4 P => Submodule.span ℝ (Set.range u))
  funext j
  have he : (Fin.castLE (by omega) j : Fin (n+1)) =
      (Fin.castLE (Nat.le_of_lt i.isLt) j).castSucc := by apply Fin.ext; rfl
  rw [he]
  simp only [Fin.snoc_castSucc]

theorem intrinsicPrefix4_snoc_last {P : Submodule ℚ (Fin 4 → ℚ)} {n : ℕ}
    (v : Fin n → rationalRealSpan4 P) (x : rationalRealSpan4 P) :
    intrinsicPrefix4 (Fin.snoc v x) (Fin.last n) = Submodule.span ℝ (Set.range v) := by
  unfold intrinsicPrefix4
  apply congrArg (fun u : Fin n → rationalRealSpan4 P => Submodule.span ℝ (Set.range u))
  funext j
  have he : (Fin.castLE (by omega) j : Fin (n+1)) = j.castSucc := by apply Fin.ext; rfl
  rw [he]
  simp only [Fin.snoc_castSucc]


theorem exists_restricted_greedy_prefix4 (P : Submodule ℚ (Fin 4 → ℚ))
    (hP : Module.finrank ℚ P ≤ 3)
    (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c₀ c₂ c₃ : Fin 4 → ℝ) :
    ∀ n ≤ Module.finrank ℚ P, ∃ v : Fin n → rationalRealSpan4 P,
      LinearIndependent ℝ v ∧ (∀ i, v i ∈ restrictedLattice4 P A₂ A₃ Q c₂ c₃) ∧
      ∀ i, ∀ y ∈ restrictedLattice4 P A₂ A₃ Q c₂ c₃, y ∉ intrinsicPrefix4 v i →
        restrictedGauge4 P L hL Q hQ c₀ (v i) ≤ restrictedGauge4 P L hL Q hQ c₀ y := by
  intro n
  induction n with
  | zero =>
    intro _
    exact ⟨Fin.elim0,linearIndependent_empty_type,(fun i => Fin.elim0 i),fun i => Fin.elim0 i⟩
  | succ n ih =>
    intro hn
    obtain ⟨v,hv,hvL,hmin⟩ := ih (by omega)
    let W := Submodule.span ℝ (Set.range v)
    have hW : W ≠ ⊤ := by
      intro h
      have hd := finrank_span_eq_card hv
      simp only [Fintype.card_fin] at hd
      change Module.finrank ℝ W = n at hd
      rw [h,finrank_top,rationalRealSpan4_finrank P hP] at hd
      omega
    obtain ⟨x,hxL,hxW,hxmin⟩ := exists_restricted_shortest_outside4 P hP A₂ A₃ L hL Q hQ c₀ c₂ c₃ W hW
    refine ⟨Fin.snoc v x,linearIndependent_fin_snoc.mpr ⟨hv,hxW⟩,?_,?_⟩
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa only [Fin.snoc_last] using hxL
      · simpa only [Fin.snoc_castSucc] using hvL j
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rw [intrinsicPrefix4_snoc_last]
        simpa only [Fin.snoc_last] using hxmin
      · rw [intrinsicPrefix4_snoc_castSucc]
        simpa only [Fin.snoc_castSucc] using hmin j



theorem intrinsicPrefix4_not_mem {P : Submodule ℚ (Fin 4 → ℚ)} {n : ℕ}
    (v : Fin n → rationalRealSpan4 P) (hv : LinearIndependent ℝ v) (i j : Fin n) (hij : i ≤ j) :
    v j ∉ intrinsicPrefix4 v i := by
  have hle : intrinsicPrefix4 v i ≤ Submodule.span ℝ (v '' {t | t < i}) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨a,rfl⟩
    exact Submodule.subset_span ⟨Fin.castLE (by omega) a,by change a.val < i.val; exact a.isLt,rfl⟩
  exact fun h => hv.not_mem_span_image (s := {t | t < i}) (x := j) (not_lt_of_ge hij) (hle h)

theorem intrinsicPrefix4_finrank {P : Submodule ℚ (Fin 4 → ℚ)} {n : ℕ}
    (v : Fin n → rationalRealSpan4 P) (hv : LinearIndependent ℝ v) (i : Fin n) :
    Module.finrank ℝ (intrinsicPrefix4 v i) = i.val := by
  exact (finrank_span_eq_card (hv.comp (Fin.castLE (by omega) : Fin i.val → Fin n)
    (Fin.castLE_injective _))).trans (Fintype.card_fin i.val)

theorem intrinsic_family_escapes4 {P : Submodule ℚ (Fin 4 → ℚ)} {n : ℕ}
    (a : Fin (n+1) → rationalRealSpan4 P) (ha : LinearIndependent ℝ a)
    (W : Submodule ℝ (rationalRealSpan4 P)) (hW : Module.finrank ℝ W = n) :
    ∃ i, a i ∉ W := by
  by_contra! h
  have hle : Submodule.span ℝ (Set.range a) ≤ W :=
    Submodule.span_le.mpr (by rintro _ ⟨i,rfl⟩; exact h i)
  have hd := Submodule.finrank_mono hle
  rw [finrank_span_eq_card ha,Fintype.card_fin,hW] at hd
  omega

theorem exists_restrictedMinima4_attaining (P : Submodule ℚ (Fin 4 → ℚ))
    (hP : Module.finrank ℚ P ≤ 3)
    (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c₀ c₂ c₃ : Fin 4 → ℝ) :
    ∃ v : Fin (Module.finrank ℚ P) → rationalRealSpan4 P,
      LinearIndependent ℝ v ∧ (∀ i, v i ∈ restrictedLattice4 P A₂ A₃ Q c₂ c₃) ∧
      (∀ i, 0 < restrictedMinima4 P A₂ A₃ L hL Q hQ c₀ c₂ c₃ i) ∧
      Monotone (restrictedMinima4 P A₂ A₃ L hL Q hQ c₀ c₂ c₃) ∧
      (∀ i, restrictedGauge4 P L hL Q hQ c₀ (v i) =
        restrictedMinima4 P A₂ A₃ L hL Q hQ c₀ c₂ c₃ i) ∧
      ∀ i, ∀ y ∈ restrictedLattice4 P A₂ A₃ Q c₂ c₃, y ∉ intrinsicPrefix4 v i →
        restrictedGauge4 P L hL Q hQ c₀ (v i) ≤ restrictedGauge4 P L hL Q hQ c₀ y := by
  obtain ⟨v,hv,hvL,hmin⟩ := exists_restricted_greedy_prefix4 P hP A₂ A₃ L hL Q hQ c₀ c₂ c₃
    (Module.finrank ℚ P) le_rfl
  let f := restrictedGauge4 P L hL Q hQ c₀
  have hmono : Monotone (fun i => f (v i)) := by
    intro i j hij
    exact hmin i (v j) (hvL j) (intrinsicPrefix4_not_mem v hv i j hij)
  have heq (k) : restrictedMinima4 P A₂ A₃ L hL Q hQ c₀ c₂ c₃ k = f (v k) := by
    apply le_antisymm
    · apply csInf_le (restrictedRadii4_bddBelow P A₂ A₃ L hL Q hQ c₀ c₂ c₃ k)
      let emb : Fin (k.val+1) → Fin (Module.finrank ℚ P) := Fin.castLE (by omega)
      refine ⟨fun i => v (emb i),hv.comp emb (Fin.castLE_injective _),fun i => hvL (emb i),?_⟩
      intro i
      exact hmono (show emb i ≤ k by change i.val ≤ k.val; omega)
    · apply le_csInf (restrictedRadii4_nonempty P hP A₂ A₃ L hL Q hQ c₀ c₂ c₃ k)
      rintro r ⟨a,ha,haL,har⟩
      obtain ⟨i,hi⟩ := intrinsic_family_escapes4 a ha (intrinsicPrefix4 v k) (intrinsicPrefix4_finrank v hv k)
      exact (hmin k (a i) (haL i) hi).trans (har i)
  refine ⟨v,hv,hvL,restrictedMinima4_pos P hP A₂ A₃ L hL Q hQ c₀ c₂ c₃,?_,?_,hmin⟩
  · intro i j hij
    rw [heq i,heq j]
    exact hmono hij
  · intro i
    exact (heq i).symm




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




#print axioms intrinsicPrefix4

#print axioms intrinsicPrefix4_snoc_castSucc

#print axioms intrinsicPrefix4_snoc_last

#print axioms exists_restricted_greedy_prefix4

#print axioms intrinsicPrefix4_not_mem

#print axioms intrinsicPrefix4_finrank

#print axioms intrinsic_family_escapes4

#print axioms exists_restrictedMinima4_attaining

#print axioms restrictedLatticeFlag4

#print axioms restrictedFlagLattice4

#print axioms restrictedLatticeFlag4_saturated

#print axioms restrictedLatticeFlag4_equiv

#print axioms restrictedFlagLattice4_discrete

#print axioms restrictedFlagLattice4_isZLattice

end CompoundFeasibility.RestrictedRecoveryLiteral4
