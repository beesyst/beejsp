import SubspaceBridge.RestrictedGeometry5

noncomputable section
namespace CompoundFeasibility.RestrictedGeometry5

def intrinsicPrefix5 {P : Submodule ℚ (Fin 5 → ℚ)} {n : ℕ}
    (v : Fin n → rationalRealSpan5 P) (i : Fin n) : Submodule ℝ (rationalRealSpan5 P) :=
  Submodule.span ℝ (Set.range (fun j : Fin i.val => v (Fin.castLE (by omega) j)))

theorem intrinsicPrefix5_snoc_castSucc {P : Submodule ℚ (Fin 5 → ℚ)} {n : ℕ}
    (v : Fin n → rationalRealSpan5 P) (x : rationalRealSpan5 P) (i : Fin n) :
    intrinsicPrefix5 (Fin.snoc v x) i.castSucc = intrinsicPrefix5 v i := by
  unfold intrinsicPrefix5
  apply congrArg (fun u : Fin i.val → rationalRealSpan5 P => Submodule.span ℝ (Set.range u))
  funext j
  have he : (Fin.castLE (by omega) j : Fin (n+1)) =
      (Fin.castLE (Nat.le_of_lt i.isLt) j).castSucc := by apply Fin.ext; rfl
  rw [he]
  simp only [Fin.snoc_castSucc]

theorem intrinsicPrefix5_snoc_last {P : Submodule ℚ (Fin 5 → ℚ)} {n : ℕ}
    (v : Fin n → rationalRealSpan5 P) (x : rationalRealSpan5 P) :
    intrinsicPrefix5 (Fin.snoc v x) (Fin.last n) = Submodule.span ℝ (Set.range v) := by
  unfold intrinsicPrefix5
  apply congrArg (fun u : Fin n → rationalRealSpan5 P => Submodule.span ℝ (Set.range u))
  funext j
  have he : (Fin.castLE (by omega) j : Fin (n+1)) = j.castSucc := by apply Fin.ext; rfl
  rw [he]
  simp only [Fin.snoc_castSucc]


theorem exists_restricted_greedy_prefix5 (P : Submodule ℚ (Fin 5 → ℚ))
    (hP : Module.finrank ℚ P ≤ 4)
    (A₂ A₃ : Matrix (Fin 5) (Fin 5) ℚ) (L : Matrix (Fin 5) (Fin 5) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c₀ c₂ c₃ : Fin 5 → ℝ) :
    ∀ n ≤ Module.finrank ℚ P, ∃ v : Fin n → rationalRealSpan5 P,
      LinearIndependent ℝ v ∧ (∀ i, v i ∈ restrictedLattice5 P A₂ A₃ Q c₂ c₃) ∧
      ∀ i, ∀ y ∈ restrictedLattice5 P A₂ A₃ Q c₂ c₃, y ∉ intrinsicPrefix5 v i →
        restrictedGauge5 P L hL Q hQ c₀ (v i) ≤ restrictedGauge5 P L hL Q hQ c₀ y := by
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
      rw [h,finrank_top,rationalRealSpan5_finrank P hP] at hd
      omega
    obtain ⟨x,hxL,hxW,hxmin⟩ := exists_restricted_shortest_outside5 P hP A₂ A₃ L hL Q hQ c₀ c₂ c₃ W hW
    refine ⟨Fin.snoc v x,linearIndependent_fin_snoc.mpr ⟨hv,hxW⟩,?_,?_⟩
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa only [Fin.snoc_last] using hxL
      · simpa only [Fin.snoc_castSucc] using hvL j
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rw [intrinsicPrefix5_snoc_last]
        simpa only [Fin.snoc_last] using hxmin
      · rw [intrinsicPrefix5_snoc_castSucc]
        simpa only [Fin.snoc_castSucc] using hmin j



theorem intrinsicPrefix5_not_mem {P : Submodule ℚ (Fin 5 → ℚ)} {n : ℕ}
    (v : Fin n → rationalRealSpan5 P) (hv : LinearIndependent ℝ v) (i j : Fin n) (hij : i ≤ j) :
    v j ∉ intrinsicPrefix5 v i := by
  have hle : intrinsicPrefix5 v i ≤ Submodule.span ℝ (v '' {t | t < i}) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨a,rfl⟩
    exact Submodule.subset_span ⟨Fin.castLE (by omega) a,by change a.val < i.val; exact a.isLt,rfl⟩
  exact fun h => hv.not_mem_span_image (s := {t | t < i}) (x := j) (not_lt_of_ge hij) (hle h)

theorem intrinsicPrefix5_finrank {P : Submodule ℚ (Fin 5 → ℚ)} {n : ℕ}
    (v : Fin n → rationalRealSpan5 P) (hv : LinearIndependent ℝ v) (i : Fin n) :
    Module.finrank ℝ (intrinsicPrefix5 v i) = i.val := by
  exact (finrank_span_eq_card (hv.comp (Fin.castLE (by omega) : Fin i.val → Fin n)
    (Fin.castLE_injective _))).trans (Fintype.card_fin i.val)

theorem intrinsic_family_escapes5 {P : Submodule ℚ (Fin 5 → ℚ)} {n : ℕ}
    (a : Fin (n+1) → rationalRealSpan5 P) (ha : LinearIndependent ℝ a)
    (W : Submodule ℝ (rationalRealSpan5 P)) (hW : Module.finrank ℝ W = n) :
    ∃ i, a i ∉ W := by
  by_contra! h
  have hle : Submodule.span ℝ (Set.range a) ≤ W :=
    Submodule.span_le.mpr (by rintro _ ⟨i,rfl⟩; exact h i)
  have hd := Submodule.finrank_mono hle
  rw [finrank_span_eq_card ha,Fintype.card_fin,hW] at hd
  omega

theorem exists_restrictedMinima5_attaining (P : Submodule ℚ (Fin 5 → ℚ))
    (hP : Module.finrank ℚ P ≤ 4)
    (A₂ A₃ : Matrix (Fin 5) (Fin 5) ℚ) (L : Matrix (Fin 5) (Fin 5) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c₀ c₂ c₃ : Fin 5 → ℝ) :
    ∃ v : Fin (Module.finrank ℚ P) → rationalRealSpan5 P,
      LinearIndependent ℝ v ∧ (∀ i, v i ∈ restrictedLattice5 P A₂ A₃ Q c₂ c₃) ∧
      (∀ i, 0 < restrictedMinima5 P A₂ A₃ L hL Q hQ c₀ c₂ c₃ i) ∧
      Monotone (restrictedMinima5 P A₂ A₃ L hL Q hQ c₀ c₂ c₃) ∧
      (∀ i, restrictedGauge5 P L hL Q hQ c₀ (v i) =
        restrictedMinima5 P A₂ A₃ L hL Q hQ c₀ c₂ c₃ i) ∧
      ∀ i, ∀ y ∈ restrictedLattice5 P A₂ A₃ Q c₂ c₃, y ∉ intrinsicPrefix5 v i →
        restrictedGauge5 P L hL Q hQ c₀ (v i) ≤ restrictedGauge5 P L hL Q hQ c₀ y := by
  obtain ⟨v,hv,hvL,hmin⟩ := exists_restricted_greedy_prefix5 P hP A₂ A₃ L hL Q hQ c₀ c₂ c₃
    (Module.finrank ℚ P) le_rfl
  let f := restrictedGauge5 P L hL Q hQ c₀
  have hmono : Monotone (fun i => f (v i)) := by
    intro i j hij
    exact hmin i (v j) (hvL j) (intrinsicPrefix5_not_mem v hv i j hij)
  have heq (k) : restrictedMinima5 P A₂ A₃ L hL Q hQ c₀ c₂ c₃ k = f (v k) := by
    apply le_antisymm
    · apply csInf_le (restrictedRadii5_bddBelow P A₂ A₃ L hL Q hQ c₀ c₂ c₃ k)
      let emb : Fin (k.val+1) → Fin (Module.finrank ℚ P) := Fin.castLE (by omega)
      refine ⟨fun i => v (emb i),hv.comp emb (Fin.castLE_injective _),fun i => hvL (emb i),?_⟩
      intro i
      exact hmono (show emb i ≤ k by change i.val ≤ k.val; omega)
    · apply le_csInf (restrictedRadii5_nonempty P hP A₂ A₃ L hL Q hQ c₀ c₂ c₃ k)
      rintro r ⟨a,ha,haL,har⟩
      obtain ⟨i,hi⟩ := intrinsic_family_escapes5 a ha (intrinsicPrefix5 v k) (intrinsicPrefix5_finrank v hv k)
      exact (hmin k (a i) (haL i) hi).trans (har i)
  refine ⟨v,hv,hvL,restrictedMinima5_pos P hP A₂ A₃ L hL Q hQ c₀ c₂ c₃,?_,?_,hmin⟩
  · intro i j hij
    rw [heq i,heq j]
    exact hmono hij
  · intro i
    exact (heq i).symm


end CompoundFeasibility.RestrictedGeometry5
