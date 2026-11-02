import SubspaceBridge.RestrictedRows5
open scoped BigOperators Classical
namespace CompoundFeasibility.RestrictedGreedyRows5
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def rowPrefix5 (rows : Fin 5 → V) (n : ℕ) : Set V :=
  rows '' {i : Fin 5 | i.val < n}

def greedyPivot5 (rows : Fin 5 → V) (i : Fin 5) : Prop :=
  rows i ∉ Submodule.span K (rowPrefix5 rows i.val)

def greedyPrefix5 (rows : Fin 5 → V) (n : ℕ) : Set (Fin 5) :=
  {i | i.val < n ∧ greedyPivot5 (K := K) rows i}

theorem rowPrefix5_succ (rows : Fin 5 → V) (n : ℕ) (hn : n < 5) :
    rowPrefix5 rows (n+1) = insert (rows ⟨n,hn⟩) (rowPrefix5 rows n) := by
  have hs : {i : Fin 5 | i.val < n+1} = insert ⟨n,hn⟩ {i : Fin 5 | i.val < n} := by
    ext i
    simp only [Set.mem_setOf_eq,Set.mem_insert_iff,Fin.ext_iff]
    omega
  unfold rowPrefix5
  rw [hs,Set.image_insert_eq]

theorem greedyPrefix5_succ (rows : Fin 5 → V) (n : ℕ) (hn : n < 5) :
    greedyPrefix5 (K := K) rows (n+1) =
      if greedyPivot5 (K := K) rows ⟨n,hn⟩ then
        insert ⟨n,hn⟩ (greedyPrefix5 (K := K) rows n)
      else greedyPrefix5 (K := K) rows n := by
  classical
  ext k
  by_cases hki : k = ⟨n,hn⟩
  · subst k
    by_cases hp : greedyPivot5 (K := K) rows ⟨n,hn⟩ <;> simp [greedyPrefix5,hp]
  · have hv : k.val < n+1 ↔ k.val < n := by
      have hne : k.val ≠ n := fun h => hki (Fin.ext h)
      omega
    by_cases hp : greedyPivot5 (K := K) rows ⟨n,hn⟩ <;> simp [greedyPrefix5,hp,hki,hv]

theorem greedyPrefix5_independent_span (rows : Fin 5 → V) :
    ∀ n : ℕ, n ≤ 5 →
      LinearIndepOn K rows (greedyPrefix5 (K := K) rows n) ∧
      Submodule.span K (rows '' greedyPrefix5 (K := K) rows n) =
        Submodule.span K (rowPrefix5 rows n) := by
  classical
  intro n
  induction n with
  | zero => simp [greedyPrefix5,rowPrefix5]
  | succ n ih =>
    intro hn
    have hnlt : n < 5 := by omega
    obtain ⟨hli,hspan⟩ := ih (by omega)
    rw [greedyPrefix5_succ rows n hnlt,rowPrefix5_succ rows n hnlt]
    have hnot : (⟨n,hnlt⟩ : Fin 5) ∉ greedyPrefix5 (K := K) rows n := by
      simp [greedyPrefix5]
    by_cases hp : greedyPivot5 (K := K) rows ⟨n,hnlt⟩
    · rw [if_pos hp,Set.image_insert_eq]
      have hout : rows ⟨n,hnlt⟩ ∉ Submodule.span K (rows '' greedyPrefix5 (K := K) rows n) := by
        rw [hspan]
        exact hp
      exact ⟨(linearIndepOn_insert hnot).mpr ⟨hli,hout⟩,by rw [Submodule.span_insert,hspan,Submodule.span_insert]⟩
    · rw [if_neg hp]
      have hmem : rows ⟨n,hnlt⟩ ∈ Submodule.span K (rowPrefix5 rows n) := not_not.mp hp
      exact ⟨hli,by rw [Submodule.span_insert_eq_span hmem];exact hspan⟩

def greedyFinset5 (rows : Fin 5 → V) : Finset (Fin 5) :=
  Finset.univ.filter (greedyPivot5 (K := K) rows)

theorem greedyFinset5_eq_prefix (rows : Fin 5 → V) :
    (greedyFinset5 (K := K) rows : Set (Fin 5)) = greedyPrefix5 (K := K) rows 5 := by
  ext i
  simp [greedyFinset5,greedyPrefix5,i.isLt]

theorem greedyFinset5_independent_span (rows : Fin 5 → V)
    (hfull : Submodule.span K (Set.range rows) = ⊤) :
    LinearIndepOn K rows (greedyFinset5 (K := K) rows : Set (Fin 5)) ∧
      Submodule.span K (rows '' (greedyFinset5 (K := K) rows : Set (Fin 5))) = ⊤ := by
  rw [greedyFinset5_eq_prefix]
  obtain ⟨hi,hs⟩ := greedyPrefix5_independent_span (K := K) rows 5 (by omega)
  have hall : rowPrefix5 rows 5 = Set.range rows := by
    simp [rowPrefix5,show {i : Fin 5 | i.val < 5} = Set.univ by ext i; simp [i.isLt]]
  exact ⟨hi,hs.trans (hall ▸ hfull)⟩

theorem greedyFinset5_card [FiniteDimensional K V] (rows : Fin 5 → V)
    (hfull : Submodule.span K (Set.range rows) = ⊤) :
    (greedyFinset5 (K := K) rows).card = Module.finrank K V := by
  obtain ⟨hli,hspan⟩ := greedyFinset5_independent_span (K := K) rows hfull
  have hrange : Set.range (fun i : greedyFinset5 (K := K) rows => rows i.val) =
      rows '' (greedyFinset5 (K := K) rows : Set (Fin 5)) := by
    ext x
    constructor
    · rintro ⟨i,rfl⟩
      exact ⟨i.val,i.property,rfl⟩
    · rintro ⟨i,hi,rfl⟩
      exact ⟨⟨i,hi⟩,rfl⟩
  have hi : LinearIndependent K (fun i : greedyFinset5 (K := K) rows => rows i.val) := hli
  let b : Basis (greedyFinset5 (K := K) rows) K V :=
    Basis.mk hi (by rw [hrange,hspan])
  simpa using (Module.finrank_eq_card_basis b).symm

def greedyIndex5 [FiniteDimensional K V] (rows : Fin 5 → V)
    (hfull : Submodule.span K (Set.range rows) = ⊤) (d : ℕ) (hdim : Module.finrank K V = d) :
    Fin d ↪o Fin 5 :=
  (greedyFinset5 (K := K) rows).orderEmbOfFin ((greedyFinset5_card (K := K) rows hfull).trans hdim)

theorem greedyIndex5_pivot [FiniteDimensional K V] (rows : Fin 5 → V)
    (hfull : Submodule.span K (Set.range rows) = ⊤) (d : ℕ) (hdim : Module.finrank K V = d)
    (k : Fin d) : greedyPivot5 (K := K) rows (greedyIndex5 rows hfull d hdim k) := by
  have h := (greedyFinset5 (K := K) rows).orderEmbOfFin_mem
    ((greedyFinset5_card (K := K) rows hfull).trans hdim) k
  exact (Finset.mem_filter.mp h).2

theorem greedyIndex5_independent [FiniteDimensional K V] (rows : Fin 5 → V)
    (hfull : Submodule.span K (Set.range rows) = ⊤) (d : ℕ) (hdim : Module.finrank K V = d) :
    LinearIndependent K (fun k => rows (greedyIndex5 rows hfull d hdim k)) := by
  have hli := (greedyFinset5_independent_span (K := K) rows hfull).1
  let f : Fin d → greedyFinset5 (K := K) rows := fun k =>
    ⟨greedyIndex5 rows hfull d hdim k,
      (greedyFinset5 (K := K) rows).orderEmbOfFin_mem ((greedyFinset5_card (K := K) rows hfull).trans hdim) k⟩
  have hf : Function.Injective f := fun k l h =>
    (greedyIndex5 rows hfull d hdim).injective (congrArg Subtype.val h)
  exact hli.comp f hf

end
end CompoundFeasibility.RestrictedGreedyRows5
