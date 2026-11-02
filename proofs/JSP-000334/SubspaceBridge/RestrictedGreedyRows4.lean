import SubspaceBridge.RestrictedRows4
open scoped BigOperators Classical
namespace CompoundFeasibility.RestrictedGreedyRows4
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def rowPrefix4 (rows : Fin 4 → V) (n : ℕ) : Set V :=
  rows '' {i : Fin 4 | i.val < n}

def greedyPivot4 (rows : Fin 4 → V) (i : Fin 4) : Prop :=
  rows i ∉ Submodule.span K (rowPrefix4 rows i.val)

def greedyPrefix4 (rows : Fin 4 → V) (n : ℕ) : Set (Fin 4) :=
  {i | i.val < n ∧ greedyPivot4 (K := K) rows i}

theorem rowPrefix4_succ (rows : Fin 4 → V) (n : ℕ) (hn : n < 4) :
    rowPrefix4 rows (n+1) = insert (rows ⟨n,hn⟩) (rowPrefix4 rows n) := by
  have hs : {i : Fin 4 | i.val < n+1} = insert ⟨n,hn⟩ {i : Fin 4 | i.val < n} := by
    ext i
    simp only [Set.mem_setOf_eq,Set.mem_insert_iff,Fin.ext_iff]
    omega
  unfold rowPrefix4
  rw [hs,Set.image_insert_eq]

theorem greedyPrefix4_succ (rows : Fin 4 → V) (n : ℕ) (hn : n < 4) :
    greedyPrefix4 (K := K) rows (n+1) =
      if greedyPivot4 (K := K) rows ⟨n,hn⟩ then
        insert ⟨n,hn⟩ (greedyPrefix4 (K := K) rows n)
      else greedyPrefix4 (K := K) rows n := by
  classical
  ext k
  by_cases hki : k = ⟨n,hn⟩
  · subst k
    by_cases hp : greedyPivot4 (K := K) rows ⟨n,hn⟩ <;> simp [greedyPrefix4,hp]
  · have hv : k.val < n+1 ↔ k.val < n := by
      have hne : k.val ≠ n := fun h => hki (Fin.ext h)
      omega
    by_cases hp : greedyPivot4 (K := K) rows ⟨n,hn⟩ <;> simp [greedyPrefix4,hp,hki,hv]

theorem greedyPrefix4_independent_span (rows : Fin 4 → V) :
    ∀ n : ℕ, n ≤ 4 →
      LinearIndepOn K rows (greedyPrefix4 (K := K) rows n) ∧
      Submodule.span K (rows '' greedyPrefix4 (K := K) rows n) =
        Submodule.span K (rowPrefix4 rows n) := by
  classical
  intro n
  induction n with
  | zero => simp [greedyPrefix4,rowPrefix4]
  | succ n ih =>
    intro hn
    have hnlt : n < 4 := by omega
    obtain ⟨hli,hspan⟩ := ih (by omega)
    rw [greedyPrefix4_succ rows n hnlt,rowPrefix4_succ rows n hnlt]
    have hnot : (⟨n,hnlt⟩ : Fin 4) ∉ greedyPrefix4 (K := K) rows n := by
      simp [greedyPrefix4]
    by_cases hp : greedyPivot4 (K := K) rows ⟨n,hnlt⟩
    · rw [if_pos hp,Set.image_insert_eq]
      have hout : rows ⟨n,hnlt⟩ ∉ Submodule.span K (rows '' greedyPrefix4 (K := K) rows n) := by
        rw [hspan]
        exact hp
      exact ⟨(linearIndepOn_insert hnot).mpr ⟨hli,hout⟩,by rw [Submodule.span_insert,hspan,Submodule.span_insert]⟩
    · rw [if_neg hp]
      have hmem : rows ⟨n,hnlt⟩ ∈ Submodule.span K (rowPrefix4 rows n) := not_not.mp hp
      exact ⟨hli,by rw [Submodule.span_insert_eq_span hmem];exact hspan⟩

def greedyFinset4 (rows : Fin 4 → V) : Finset (Fin 4) :=
  Finset.univ.filter (greedyPivot4 (K := K) rows)

theorem greedyFinset4_eq_prefix (rows : Fin 4 → V) :
    (greedyFinset4 (K := K) rows : Set (Fin 4)) = greedyPrefix4 (K := K) rows 4 := by
  ext i
  simp [greedyFinset4,greedyPrefix4,i.isLt]

theorem greedyFinset4_independent_span (rows : Fin 4 → V)
    (hfull : Submodule.span K (Set.range rows) = ⊤) :
    LinearIndepOn K rows (greedyFinset4 (K := K) rows : Set (Fin 4)) ∧
      Submodule.span K (rows '' (greedyFinset4 (K := K) rows : Set (Fin 4))) = ⊤ := by
  rw [greedyFinset4_eq_prefix]
  obtain ⟨hi,hs⟩ := greedyPrefix4_independent_span (K := K) rows 4 (by omega)
  have hall : rowPrefix4 rows 4 = Set.range rows := by
    simp [rowPrefix4,show {i : Fin 4 | i.val < 4} = Set.univ by ext i; simp [i.isLt]]
  exact ⟨hi,hs.trans (hall ▸ hfull)⟩

theorem greedyFinset4_card [FiniteDimensional K V] (rows : Fin 4 → V)
    (hfull : Submodule.span K (Set.range rows) = ⊤) :
    (greedyFinset4 (K := K) rows).card = Module.finrank K V := by
  obtain ⟨hli,hspan⟩ := greedyFinset4_independent_span (K := K) rows hfull
  have hrange : Set.range (fun i : greedyFinset4 (K := K) rows => rows i.val) =
      rows '' (greedyFinset4 (K := K) rows : Set (Fin 4)) := by
    ext x
    constructor
    · rintro ⟨i,rfl⟩
      exact ⟨i.val,i.property,rfl⟩
    · rintro ⟨i,hi,rfl⟩
      exact ⟨⟨i,hi⟩,rfl⟩
  have hi : LinearIndependent K (fun i : greedyFinset4 (K := K) rows => rows i.val) := hli
  let b : Basis (greedyFinset4 (K := K) rows) K V :=
    Basis.mk hi (by rw [hrange,hspan])
  simpa using (Module.finrank_eq_card_basis b).symm

def greedyIndex4 [FiniteDimensional K V] (rows : Fin 4 → V)
    (hfull : Submodule.span K (Set.range rows) = ⊤) (d : ℕ) (hdim : Module.finrank K V = d) :
    Fin d ↪o Fin 4 :=
  (greedyFinset4 (K := K) rows).orderEmbOfFin ((greedyFinset4_card (K := K) rows hfull).trans hdim)

theorem greedyIndex4_pivot [FiniteDimensional K V] (rows : Fin 4 → V)
    (hfull : Submodule.span K (Set.range rows) = ⊤) (d : ℕ) (hdim : Module.finrank K V = d)
    (k : Fin d) : greedyPivot4 (K := K) rows (greedyIndex4 rows hfull d hdim k) := by
  have h := (greedyFinset4 (K := K) rows).orderEmbOfFin_mem
    ((greedyFinset4_card (K := K) rows hfull).trans hdim) k
  exact (Finset.mem_filter.mp h).2

theorem greedyIndex4_independent [FiniteDimensional K V] (rows : Fin 4 → V)
    (hfull : Submodule.span K (Set.range rows) = ⊤) (d : ℕ) (hdim : Module.finrank K V = d) :
    LinearIndependent K (fun k => rows (greedyIndex4 rows hfull d hdim k)) := by
  have hli := (greedyFinset4_independent_span (K := K) rows hfull).1
  let f : Fin d → greedyFinset4 (K := K) rows := fun k =>
    ⟨greedyIndex4 rows hfull d hdim k,
      (greedyFinset4 (K := K) rows).orderEmbOfFin_mem ((greedyFinset4_card (K := K) rows hfull).trans hdim) k⟩
  have hf : Function.Injective f := fun k l h =>
    (greedyIndex4 rows hfull d hdim).injective (congrArg Subtype.val h)
  exact hli.comp f hf

end
end CompoundFeasibility.RestrictedGreedyRows4
