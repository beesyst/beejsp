import SubspaceBridge.NonrothVolumeGrowth4
import SubspaceBridge.RestrictedSource4
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Matrix.Rank

open scoped BigOperators Matrix
namespace CompoundFeasibility.M193LiteralRestrictedSelectedIndex4
noncomputable section

theorem selected_integer_two_index_bound
    (B : Matrix (Fin 2) (Fin 2) ℤ) (hB : B.det ≠ 0)
    (G : AddSubgroup (Fin 2 → ℤ)) (b : Basis (Fin 2) ℤ G)
    (e : Fin 2 → ℕ)
    (hlocal : ∀ (x : G) i, padicNorm 2 (((B.map (Int.castRingHom ℚ)) *ᵥ
      (fun k => ((x : Fin 2 → ℤ) k : ℚ))) i) ≤ (2 : ℚ)^(-(e i : ℤ))) :
    2^(∑ i, e i) ≤ B.det.natAbs * G.index := by
  let C : Matrix (Fin 2) (Fin 2) ℤ := fun i j => (b j : Fin 2 → ℤ) i
  have hC : C.det.natAbs = G.index := by
    rw [AddSubgroup.index_eq_natAbs_det (Pi.basisFun ℤ (Fin 2)) G b, Basis.det_apply]
    rfl
  have hli : LinearIndependent ℤ (fun j => (b j : Fin 2 → ℤ)) :=
    b.linearIndependent.map' G.toIntSubmodule.subtype (Submodule.ker_subtype _)
  have hCne : C.det ≠ 0 :=
    (SourceRelativeIndex6.integer_span_index_det (Pi.basisFun ℤ (Fin 2)) _ hli).2.2
  have hdiv : ∀ i j, (2 : ℤ)^(e i) ∣ (B*C) i j := by
    intro i j
    have hh : ((2^e i : ℕ) : ℤ) ∣ (B*C) i j := by
      apply padicNorm.dvd_iff_norm_le.mpr
      convert hlocal (b j) i using 1 <;> simp [Matrix.mul_apply,Matrix.mulVec,dotProduct,C]
    simpa using hh
  choose D hD using hdiv
  let E : Matrix (Fin 2) (Fin 2) ℤ := D
  have hmatrix : B*C = Matrix.diagonal (fun i => (2 : ℤ)^e i) * E := by
    ext i j
    simpa [Matrix.diagonal_mul] using hD i j
  have hdetdiv : (2 : ℤ)^(∑ i, e i) ∣ (B*C).det := by
    rw [hmatrix,Matrix.det_mul,Matrix.det_diagonal,Finset.prod_pow_eq_pow_sum]
    exact dvd_mul_right _ _
  have hnonzero : (B*C).det ≠ 0 := by rw [Matrix.det_mul];exact mul_ne_zero hB hCne
  have hle := Int.natAbs_le_of_dvd_ne_zero hdetdiv hnonzero
  simpa only [Matrix.det_mul,Int.natAbs_mul,Int.natAbs_pow,
    show (2 : ℤ).natAbs = 2 from rfl,hC] using hle

theorem selected_rational_index_lower4 (d : Fin 4)
    (B₂ B₃ : Matrix (Fin d.val) (Fin d.val) ℚ)
    (G : AddSubgroup (Fin d.val → ℤ)) (b : Basis (Fin d.val) ℤ G)
    (e₂ e₃ : Fin d.val → ℕ)
    (h₂ : ∀ (x : G) i, padicNorm 2 ((B₂ *ᵥ (fun k => ((x : Fin d.val → ℤ) k : ℚ))) i) ≤
      (2 : ℚ)^(-(e₂ i : ℤ)))
    (h₃ : ∀ (x : G) i, padicNorm 3 ((B₃ *ᵥ (fun k => ((x : Fin d.val → ℤ) k : ℚ))) i) ≤
      (3 : ℚ)^(-(e₃ i : ℤ))) :
    (padicNorm 2 B₂.det : ℝ) * (padicNorm 3 B₃.det : ℝ) *
      (2 : ℝ)^(∑ i, e₂ i) * (3 : ℝ)^(∑ i, e₃ i) ≤ (G.index : ℝ) := by
  let U : Matrix (Fin d.val) (Fin d.val) ℤ := fun k i => (b k : Fin d.val → ℤ) i
  have hli : LinearIndependent ℤ (fun k => (b k : Fin d.val → ℤ)) :=
    b.linearIndependent.map' G.toIntSubmodule.subtype (Submodule.ker_subtype _)
  have hUne : U.det ≠ 0 := by
    have h := (SourceRelativeIndex6.integer_span_index_det (Pi.basisFun ℤ (Fin d.val)) _ hli).2.2
    change U.transpose.det ≠ 0 at h
    simpa using h
  have hUR : (U.map (Int.castRingHom ℝ)).det ≠ 0 := by
    rw [← integer_matrix_det_cast]
    exact_mod_cast hUne
  have hreal := Matrix.linearIndependent_rows_of_det_ne_zero hUR
  have hindex : |(U.map (Int.castRingHom ℝ)).det| = (G.index : ℝ) := by
    have h := AddSubgroup.index_eq_natAbs_det (Pi.basisFun ℤ (Fin d.val)) G b
    rw [Basis.det_apply] at h
    have he : (Pi.basisFun ℤ (Fin d.val)).toMatrix (fun k => (b k : Fin d.val → ℤ)) = U.transpose := by rfl
    rw [he,Matrix.det_transpose] at h
    rw [← integer_matrix_det_cast,← Int.cast_abs,← Int.cast_natAbs,← h]
  have hbase := integer_matrix_three_place_lower U hreal
  rw [hindex] at hbase
  have htwo := padic_det_frame_bound 2 B₂ e₂ U (fun k i => h₂ (b k) i)
  have hthree := padic_det_frame_bound 3 B₃ e₃ U (fun k i => h₃ (b k) i)
  have htwoR : (padicNorm 2 B₂.det : ℝ) * (padicNorm 2 (U.map (Int.castRingHom ℚ)).det : ℝ) ≤
      ((2 : ℝ)^(∑ i, e₂ i))⁻¹ := by
    have hh := (Rat.cast_le (K := ℝ)).mpr htwo
    simpa only [Rat.cast_mul,Rat.cast_inv,Rat.cast_pow,Rat.cast_ofNat] using hh
  have hthreeR : (padicNorm 3 B₃.det : ℝ) * (padicNorm 3 (U.map (Int.castRingHom ℚ)).det : ℝ) ≤
      ((3 : ℝ)^(∑ i, e₃ i))⁻¹ := by
    have hh := (Rat.cast_le (K := ℝ)).mpr hthree
    simpa only [Rat.cast_mul,Rat.cast_inv,Rat.cast_pow,Rat.cast_ofNat] using hh
  have hp₂ : 0 ≤ (padicNorm 2 B₂.det : ℝ) := by exact_mod_cast padicNorm.nonneg B₂.det
  have hp₃ : 0 ≤ (padicNorm 3 B₃.det : ℝ) := by exact_mod_cast padicNorm.nonneg B₃.det
  have hu₂ : 0 ≤ (padicNorm 2 (U.map (Int.castRingHom ℚ)).det : ℝ) := by exact_mod_cast padicNorm.nonneg _
  have hu₃ : 0 ≤ (padicNorm 3 (U.map (Int.castRingHom ℚ)).det : ℝ) := by exact_mod_cast padicNorm.nonneg _
  have hm := mul_le_mul htwoR hthreeR (mul_nonneg hp₃ hu₃) (by positivity)
  have hstart := mul_le_mul_of_nonneg_right hbase (mul_nonneg hp₂ hp₃)
  have hstep : (padicNorm 2 B₂.det : ℝ) * (padicNorm 3 B₃.det : ℝ) ≤
      (G.index : ℝ) * (((2 : ℝ)^(∑ i, e₂ i))⁻¹ * ((3 : ℝ)^(∑ i, e₃ i))⁻¹) := by
    calc
      _ ≤ (G.index : ℝ) *
          (((padicNorm 2 B₂.det : ℝ) * (padicNorm 2 (U.map (Int.castRingHom ℚ)).det : ℝ)) *
           ((padicNorm 3 B₃.det : ℝ) * (padicNorm 3 (U.map (Int.castRingHom ℚ)).det : ℝ))) := by nlinarith [hstart]
      _ ≤ _ := mul_le_mul_of_nonneg_left hm (by positivity)
  have hlast := mul_le_mul_of_nonneg_right hstep
    (show 0 ≤ (2 : ℝ)^(∑ i, e₂ i) * (3 : ℝ)^(∑ i, e₃ i) by positivity)
  have hcancel : (G.index : ℝ) *
      (((2 : ℝ)^(∑ i, e₂ i))⁻¹ * ((3 : ℝ)^(∑ i, e₃ i))⁻¹) *
      ((2 : ℝ)^(∑ i, e₂ i) * (3 : ℝ)^(∑ i, e₃ i)) = (G.index : ℝ) := by
    calc
      _ = (G.index : ℝ) *
          ((((2 : ℝ)^(∑ i, e₂ i))⁻¹ * (2 : ℝ)^(∑ i, e₂ i)) *
           (((3 : ℝ)^(∑ i, e₃ i))⁻¹ * (3 : ℝ)^(∑ i, e₃ i))) := by ring
      _ = _ := by rw [inv_mul_cancel₀ (by positivity),inv_mul_cancel₀ (by positivity),mul_one,mul_one]
  rw [hcancel] at hlast
  simpa only [mul_assoc] using hlast

end
end CompoundFeasibility.M193LiteralRestrictedSelectedIndex4

open scoped BigOperators Matrix
namespace CompoundFeasibility.M193LiteralRestrictedWeightOrder4
open RestrictedGeometry4
noncomputable section

def weightOrder4 (c : Fin 4 → ℝ) : Equiv.Perm (Fin 4) := Tuple.sort c

def permutedRows4 {K : Type*} (A : Matrix (Fin 4) (Fin 4) K)
    (sigma : Equiv.Perm (Fin 4)) : Matrix (Fin 4) (Fin 4) K := fun i k => A (sigma i) k

theorem weightOrder4_bijective (c : Fin 4 → ℝ) : Function.Bijective (weightOrder4 c) :=
  (weightOrder4 c).bijective

theorem weightOrder4_monotone (c : Fin 4 → ℝ) :
    Monotone (fun i => c (weightOrder4 c i)) := Tuple.monotone_sort c

theorem weightOrder4_adjacent (c : Fin 4 → ℝ) (i : Fin 3) :
    c (weightOrder4 c i.castSucc) ≤ c (weightOrder4 c i.succ) :=
  weightOrder4_monotone c (by exact Fin.le_iff_val_le_val.mpr (by simp))

theorem weightOrder4_forall_pair {α : Type*} (f : Fin 4 → α) (c : Fin 4 → ℝ)
    (R : α → ℝ → Prop) :
    (∀ i, R (f (weightOrder4 c i)) (c (weightOrder4 c i))) ↔ ∀ i, R (f i) (c i) := by
  constructor
  · intro h i
    simpa using h ((weightOrder4 c).symm i)
  · intro h i
    exact h _

theorem weightOrder4_ties (c : Fin 4 → ℝ) (sigma : Equiv.Perm (Fin 4))
    (h : Monotone (fun i => c (sigma i))) :
    (fun i => c (sigma i)) = (fun i => c (weightOrder4 c i)) := by
  exact (Tuple.comp_sort_eq_comp_iff_monotone).mpr h

theorem permutedRows4_mulVec {K : Type*} [CommRing K]
    (A : Matrix (Fin 4) (Fin 4) K) (sigma : Equiv.Perm (Fin 4)) (x : Fin 4 → K) (i : Fin 4) :
    (permutedRows4 A sigma *ᵥ x) i = (A *ᵥ x) (sigma i) := rfl

theorem originalBody4_weightOrder (L : Matrix (Fin 4) (Fin 4) ℝ) (Q : ℝ) (c : Fin 4 → ℝ) :
    originalBody4 (permutedRows4 L (weightOrder4 c)) Q (fun i => c (weightOrder4 c i)) =
      originalBody4 L Q c := by
  ext x
  exact weightOrder4_forall_pair (fun i => (L *ᵥ x) i) c (fun y w => |y| ≤ Q^w)

theorem lattice4_weightOrder (p : ℕ) [Fact p.Prime]
    (A : Matrix (Fin 4) (Fin 4) ℚ) (Q : ℝ) (c : Fin 4 → ℝ) :
    lattice4 p (permutedRows4 A (weightOrder4 c))
      (fun i => Nat.ceil (JSP000334.qThreshold p Q (c (weightOrder4 c i)))) =
    lattice4 p A (fun i => Nat.ceil (JSP000334.qThreshold p Q (c i))) := by
  ext x
  rw [lattice4_spec,lattice4_spec]
  exact weightOrder4_forall_pair (fun i => (A *ᵥ (fun k => (x k : ℚ))) i) c
    (fun y w => padicNorm p y ≤ (p : ℚ)^(-(Nat.ceil (JSP000334.qThreshold p Q w) : ℤ)))

theorem originalSourceGroup4_weightOrder
    (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) (Q : ℝ) (c₂ c₃ : Fin 4 → ℝ) :
    originalSourceGroup4 (permutedRows4 A₂ (weightOrder4 c₂))
      (permutedRows4 A₃ (weightOrder4 c₃)) Q
      (fun i => c₂ (weightOrder4 c₂ i)) (fun i => c₃ (weightOrder4 c₃ i)) =
    originalSourceGroup4 A₂ A₃ Q c₂ c₃ := by
  unfold originalSourceGroup4 sourceLattice4
  rw [lattice4_weightOrder,lattice4_weightOrder]

theorem restrictedBody4_weightOrder (P : Submodule ℚ (Fin 4 → ℚ))
    (L : Matrix (Fin 4) (Fin 4) ℝ) (Q : ℝ) (c : Fin 4 → ℝ) :
    restrictedBody4 P (permutedRows4 L (weightOrder4 c)) Q (fun i => c (weightOrder4 c i)) =
      restrictedBody4 P L Q c := by
  unfold restrictedBody4
  rw [originalBody4_weightOrder]

theorem restrictedLattice4_weightOrder (P : Submodule ℚ (Fin 4 → ℚ))
    (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) (Q : ℝ) (c₂ c₃ : Fin 4 → ℝ) :
    restrictedLattice4 P (permutedRows4 A₂ (weightOrder4 c₂))
      (permutedRows4 A₃ (weightOrder4 c₃)) Q
      (fun i => c₂ (weightOrder4 c₂ i)) (fun i => c₃ (weightOrder4 c₃ i)) =
    restrictedLattice4 P A₂ A₃ Q c₂ c₃ := by
  unfold restrictedLattice4
  rw [originalSourceGroup4_weightOrder]

end
end CompoundFeasibility.M193LiteralRestrictedWeightOrder4

open scoped BigOperators Matrix
namespace CompoundFeasibility.M193LiteralRestrictedRows4
open RestrictedGeometry4
noncomputable section

def rowCoordinates4 {K : Type*} [Field K] {d : ℕ}
    (P : Submodule K (Fin 4 → K)) (b : Basis (Fin d) K P)
    (A : Matrix (Fin 4) (Fin 4) K) : Matrix (Fin 4) (Fin d) K :=
  fun i k => (A *ᵥ (b k : Fin 4 → K)) i

theorem rowCoordinates4_span {K : Type*} [Field K] {d : ℕ}
    (P : Submodule K (Fin 4 → K)) (b : Basis (Fin d) K P)
    (A : Matrix (Fin 4) (Fin 4) K) (hA : IsUnit A) :
    Submodule.span K (Set.range (rowCoordinates4 P b A).row) = ⊤ := by
  let e := LinearEquiv.ofBijective (Matrix.toLin' A)
    ⟨Matrix.mulVec_injective_iff_isUnit.mpr hA,Matrix.mulVec_surjective_iff_isUnit.mpr hA⟩
  have hli : LinearIndependent K (fun k => (A *ᵥ (b k : Fin 4 → K))) :=
    (b.linearIndependent.map' P.subtype P.ker_subtype).map' e.toLinearMap e.ker
  have hcol : LinearIndependent K (rowCoordinates4 P b A).transpose.row := hli
  have hrank : (rowCoordinates4 P b A).rank = d := by
    rw [← Matrix.rank_transpose]
    simpa only [Fintype.card_fin] using hcol.rank_matrix
  apply Submodule.eq_top_of_finrank_eq
  rw [← Matrix.rank_eq_finrank_span_row,hrank,Module.finrank_pi]
  simp

def rationalRowCoordinates4 (P : Submodule ℚ (Fin 4 → ℚ))
    (A : Matrix (Fin 4) (Fin 4) ℚ) : Matrix (Fin 4) (Fin (Module.finrank ℚ P)) ℚ :=
  rowCoordinates4 P (Module.finBasis ℚ P) A

def realRowCoordinates4 (P : Submodule ℚ (Fin 4 → ℚ))
    (L : Matrix (Fin 4) (Fin 4) ℝ) :
    Matrix (Fin 4) (Fin (Module.finrank ℝ (rationalRealSpan4 P))) ℝ :=
  rowCoordinates4 (rationalRealSpan4 P) (Module.finBasis ℝ (rationalRealSpan4 P)) L

theorem rationalRowCoordinates4_span (P : Submodule ℚ (Fin 4 → ℚ))
    (A : Matrix (Fin 4) (Fin 4) ℚ) (hA : A.det = 1) :
    Submodule.span ℚ (Set.range (rationalRowCoordinates4 P A).row) = ⊤ := by
  exact rowCoordinates4_span P _ A ((Matrix.isUnit_iff_isUnit_det A).mpr (hA ▸ isUnit_one))

theorem realRowCoordinates4_span (P : Submodule ℚ (Fin 4 → ℚ))
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : L.det = 1) :
    Submodule.span ℝ (Set.range (realRowCoordinates4 P L).row) = ⊤ := by
  exact rowCoordinates4_span _ _ L ((Matrix.isUnit_iff_isUnit_det L).mpr (hL ▸ isUnit_one))

end
end CompoundFeasibility.M193LiteralRestrictedRows4

open scoped BigOperators Classical
namespace CompoundFeasibility.M193LiteralRestrictedGreedyRows4
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
end CompoundFeasibility.M193LiteralRestrictedGreedyRows4

open scoped BigOperators Matrix
namespace CompoundFeasibility.M193LiteralSelectedRestriction4
open RestrictedGeometry4 M193LiteralRestrictedWeightOrder4 M193LiteralRestrictedRows4 M193LiteralRestrictedGreedyRows4
noncomputable section

def sortedRows4 {K : Type*} [Field K] {d : ℕ}
    (M : Matrix (Fin 4) (Fin d) K) (c : Fin 4 → ℝ) : Fin 4 → Fin d → K :=
  fun i => M (weightOrder4 c i)

theorem sortedRows4_span {K : Type*} [Field K] {d : ℕ}
    (M : Matrix (Fin 4) (Fin d) K) (c : Fin 4 → ℝ)
    (hfull : Submodule.span K (Set.range M.row) = ⊤) :
    Submodule.span K (Set.range (sortedRows4 M c)) = ⊤ := by
  have hrange : Set.range (sortedRows4 M c) = Set.range M.row := by
    ext x
    constructor
    · rintro ⟨i,rfl⟩
      exact ⟨weightOrder4 c i,rfl⟩
    · rintro ⟨i,rfl⟩
      exact ⟨(weightOrder4 c).symm i,by simp [sortedRows4,Matrix.row_def]⟩
  rw [hrange,hfull]

def selectedIndex4 {K : Type*} [Field K] {d : ℕ}
    (M : Matrix (Fin 4) (Fin d) K) (c : Fin 4 → ℝ)
    (hfull : Submodule.span K (Set.range M.row) = ⊤) : Fin d ↪o Fin 4 :=
  greedyIndex4 (sortedRows4 M c) (sortedRows4_span M c hfull) d (by simp)

def selectedMatrix4 {K : Type*} [Field K] {d : ℕ}
    (M : Matrix (Fin 4) (Fin d) K) (c : Fin 4 → ℝ)
    (hfull : Submodule.span K (Set.range M.row) = ⊤) : Matrix (Fin d) (Fin d) K :=
  fun k => M (weightOrder4 c (selectedIndex4 M c hfull k))

theorem selectedMatrix4_independent {K : Type*} [Field K] {d : ℕ}
    (M : Matrix (Fin 4) (Fin d) K) (c : Fin 4 → ℝ)
    (hfull : Submodule.span K (Set.range M.row) = ⊤) :
    LinearIndependent K (selectedMatrix4 M c hfull).row :=
  greedyIndex4_independent (sortedRows4 M c) (sortedRows4_span M c hfull) d (by simp)

theorem selectedMatrix4_det_ne_zero {K : Type*} [Field K] {d : ℕ}
    (M : Matrix (Fin 4) (Fin d) K) (c : Fin 4 → ℝ)
    (hfull : Submodule.span K (Set.range M.row) = ⊤) :
    (selectedMatrix4 M c hfull).det ≠ 0 := by
  exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp
    (Matrix.linearIndependent_rows_iff_isUnit.mp (selectedMatrix4_independent M c hfull)))

def realRestrictionBasis4 (P : Submodule ℚ (Fin 4 → ℚ)) (hP : Module.finrank ℚ P ≤ 3) :
    Basis (Fin (Module.finrank ℚ P)) ℝ (rationalRealSpan4 P) :=
  (Module.finBasis ℝ (rationalRealSpan4 P)).reindex (finCongr (rationalRealSpan4_finrank P hP))

def realRestrictionCoordinates4 (P : Submodule ℚ (Fin 4 → ℚ)) (hP : Module.finrank ℚ P ≤ 3)
    (L : Matrix (Fin 4) (Fin 4) ℝ) : Matrix (Fin 4) (Fin (Module.finrank ℚ P)) ℝ :=
  rowCoordinates4 (rationalRealSpan4 P) (realRestrictionBasis4 P hP) L

theorem realRestrictionCoordinates4_span (P : Submodule ℚ (Fin 4 → ℚ))
    (hP : Module.finrank ℚ P ≤ 3) (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : L.det = 1) :
    Submodule.span ℝ (Set.range (realRestrictionCoordinates4 P hP L).row) = ⊤ :=
  rowCoordinates4_span _ _ L ((Matrix.isUnit_iff_isUnit_det L).mpr (hL ▸ isUnit_one))

def sourceSelectedExponent4 (P : Submodule ℚ (Fin 4 → ℚ)) (hP : Module.finrank ℚ P ≤ 3)
    (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ)
    (h₂ : A₂.det = 1) (h₃ : A₃.det = 1) (hL : L.det = 1) (c₀ c₂ c₃ : Fin 4 → ℝ) : ℝ :=
    (∑ k : Fin (Module.finrank ℚ P), c₀ (weightOrder4 c₀
      (selectedIndex4 (realRestrictionCoordinates4 P hP L) c₀ (realRestrictionCoordinates4_span P hP L hL) k))) +
    (∑ k : Fin (Module.finrank ℚ P), c₂ (weightOrder4 c₂
      (selectedIndex4 (rationalRowCoordinates4 P A₂) c₂ (rationalRowCoordinates4_span P A₂ h₂) k))) +
    (∑ k : Fin (Module.finrank ℚ P), c₃ (weightOrder4 c₃
      (selectedIndex4 (rationalRowCoordinates4 P A₃) c₃ (rationalRowCoordinates4_span P A₃ h₃) k)))

end
end CompoundFeasibility.M193LiteralSelectedRestriction4

open scoped BigOperators Classical
namespace CompoundFeasibility.M193LiteralRestrictedGreedyRanks4
open M193LiteralRestrictedGreedyRows4
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem greedyIndex4_prefix_set (rows : Fin 4 → V)
    (hfull : Submodule.span K (Set.range rows) = ⊤) (d : ℕ) (hdim : Module.finrank K V = d)
    (k : Fin d) :
    greedyPrefix4 (K := K) rows (greedyIndex4 rows hfull d hdim k).val =
      Set.range (fun a : Fin k.val => greedyIndex4 rows hfull d hdim (Fin.castLE (by omega) a)) := by
  let E := greedyIndex4 rows hfull d hdim
  have hrange : Set.range E = (greedyFinset4 (K := K) rows : Set (Fin 4)) :=
    (greedyFinset4 (K := K) rows).range_orderEmbOfFin ((greedyFinset4_card (K := K) rows hfull).trans hdim)
  ext i
  constructor
  · intro hi
    have himem : i ∈ (greedyFinset4 (K := K) rows : Set (Fin 4)) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi.2⟩
    rw [← hrange] at himem
    obtain ⟨a,rfl⟩ := himem
    have ha : a < k := E.lt_iff_lt.mp hi.1
    refine ⟨⟨a.val,ha⟩,?_⟩
    congr 1
  · rintro ⟨a,rfl⟩
    exact ⟨E.strictMono (show Fin.castLE (by omega) a < k from a.isLt),
      greedyIndex4_pivot rows hfull d hdim _⟩

theorem greedyIndex4_prefix_rank (rows : Fin 4 → V)
    (hfull : Submodule.span K (Set.range rows) = ⊤) (d : ℕ) (hdim : Module.finrank K V = d)
    (k : Fin d) :
    Module.finrank K (Submodule.span K (rowPrefix4 rows (greedyIndex4 rows hfull d hdim k).val)) = k.val := by
  have hs := (greedyPrefix4_independent_span (K := K) rows
    (greedyIndex4 rows hfull d hdim k).val (by omega)).2
  rw [← hs,greedyIndex4_prefix_set rows hfull d hdim k,← Set.range_comp]
  have hli := (greedyIndex4_independent rows hfull d hdim).comp
    (fun a : Fin k.val => Fin.castLE (by omega) a) (Fin.castLE_injective (by omega))
  simpa only [Fintype.card_fin] using finrank_span_eq_card hli

theorem greedyIndex4_first_rank_increase (rows : Fin 4 → V)
    (hfull : Submodule.span K (Set.range rows) = ⊤) (d : ℕ) (hdim : Module.finrank K V = d)
    (k : Fin d) :
    Module.finrank K (Submodule.span K (rowPrefix4 rows
      ((greedyIndex4 rows hfull d hdim k).val+1))) = k.val+1 ∧
    ∀ i : Fin 4, i < greedyIndex4 rows hfull d hdim k →
      Module.finrank K (Submodule.span K (rowPrefix4 rows (i.val+1))) ≤ k.val := by
  let E := greedyIndex4 rows hfull d hdim
  have hp := greedyIndex4_pivot rows hfull d hdim k
  have hprev := greedyIndex4_prefix_rank rows hfull d hdim k
  have hnonzero : rows (E k) ≠ 0 := by
    intro hz
    apply hp
    rw [hz]
    exact Submodule.zero_mem _
  have hdisjoint := Submodule.disjoint_span_singleton_of_not_mem hp
  have hdimstep := Submodule.finrank_sup_add_finrank_inf_eq
    (Submodule.span K (rowPrefix4 rows (E k).val)) (K ∙ rows (E k))
  rw [hdisjoint.eq_bot,finrank_bot,add_zero,finrank_span_singleton hnonzero,hprev] at hdimstep
  constructor
  · rw [rowPrefix4_succ rows (E k).val (E k).isLt,Submodule.span_insert,sup_comm]
    exact hdimstep
  · intro i hi
    calc
      _ ≤ Module.finrank K (Submodule.span K (rowPrefix4 rows (E k).val)) := by
        apply Submodule.finrank_mono
        apply Submodule.span_mono
        rintro x ⟨a,ha,rfl⟩
        have hle : i.val+1 ≤ (E k).val := by
          change i.val < (E k).val at hi
          omega
        exact ⟨a,lt_of_lt_of_le ha hle,rfl⟩
      _ = _ := hprev

end
end CompoundFeasibility.M193LiteralRestrictedGreedyRanks4

open scoped BigOperators Matrix
namespace CompoundFeasibility.M193LiteralRestrictedRelaxed4
open RestrictedGeometry4
noncomputable section

def relaxedBody4 {d : ℕ} (P : Submodule ℚ (Fin 4 → ℚ))
    (L : Matrix (Fin 4) (Fin 4) ℝ) (Q : ℝ) (c : Fin 4 → ℝ) (s : Fin d → Fin 4) :
    Set (rationalRealSpan4 P) :=
  {x | ∀ k, |(L *ᵥ (x : Fin 4 → ℝ)) (s k)| ≤ Q^(c (s k))}

def selectedLocalGroup4 {d : ℕ} (p : ℕ) [Fact p.Prime]
    (A : Matrix (Fin 4) (Fin 4) ℚ) (Q : ℝ) (c : Fin 4 → ℝ) (s : Fin d → Fin 4) :
    AddSubgroup (Fin 4 → ℤ) :=
  ⨅ k, (normBall p (Nat.ceil (JSP000334.qThreshold p Q (c (s k))))).comap (row4 A (s k))

def selectedSourceGroup4 {d : ℕ} (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (Q : ℝ) (c₂ c₃ : Fin 4 → ℝ) (s₂ s₃ : Fin d → Fin 4) : AddSubgroup (Fin 4 → ℤ) :=
  selectedLocalGroup4 2 A₂ Q c₂ s₂ ⊓ selectedLocalGroup4 3 A₃ Q c₃ s₃

def relaxedLattice4 {d : ℕ} (P : Submodule ℚ (Fin 4 → ℚ))
    (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) (Q : ℝ) (c₂ c₃ : Fin 4 → ℝ)
    (s₂ s₃ : Fin d → Fin 4) : Submodule ℤ (rationalRealSpan4 P) :=
  (integerRealImage (selectedSourceGroup4 A₂ A₃ Q c₂ c₃ s₂ s₃)).comap
    ((rationalRealSpan4 P).subtype.restrictScalars ℤ)

theorem restrictedBody4_subset_relaxed {d : ℕ} (P : Submodule ℚ (Fin 4 → ℚ))
    (L : Matrix (Fin 4) (Fin 4) ℝ) (Q : ℝ) (c : Fin 4 → ℝ) (s : Fin d → Fin 4) :
    restrictedBody4 P L Q c ⊆ relaxedBody4 P L Q c s := by
  intro x hx k
  exact hx (s k)

theorem lattice4_le_selectedLocalGroup4 {d : ℕ} (p : ℕ) [Fact p.Prime]
    (A : Matrix (Fin 4) (Fin 4) ℚ) (Q : ℝ) (c : Fin 4 → ℝ) (s : Fin d → Fin 4) :
    lattice4 p A (fun i => Nat.ceil (JSP000334.qThreshold p Q (c i))) ≤
      selectedLocalGroup4 p A Q c s := by
  intro x hx
  simp only [selectedLocalGroup4,AddSubgroup.mem_iInf,AddSubgroup.mem_comap]
  intro k
  exact (show x ∈ (normBall p (Nat.ceil (JSP000334.qThreshold p Q (c (s k))))).comap
    (row4 A (s k)) from (AddSubgroup.mem_iInf.mp hx) (s k))

theorem originalSourceGroup4_le_selected {d : ℕ}
    (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) (Q : ℝ) (c₂ c₃ : Fin 4 → ℝ) (s₂ s₃ : Fin d → Fin 4) :
    originalSourceGroup4 A₂ A₃ Q c₂ c₃ ≤ selectedSourceGroup4 A₂ A₃ Q c₂ c₃ s₂ s₃ := by
  exact inf_le_inf (lattice4_le_selectedLocalGroup4 2 A₂ Q c₂ s₂)
    (lattice4_le_selectedLocalGroup4 3 A₃ Q c₃ s₃)

theorem restrictedLattice4_le_relaxed {d : ℕ} (P : Submodule ℚ (Fin 4 → ℚ))
    (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) (Q : ℝ) (c₂ c₃ : Fin 4 → ℝ) (s₂ s₃ : Fin d → Fin 4) :
    restrictedLattice4 P A₂ A₃ Q c₂ c₃ ≤ relaxedLattice4 P A₂ A₃ Q c₂ c₃ s₂ s₃ := by
  rintro x ⟨z,hz,hx⟩
  exact ⟨z,originalSourceGroup4_le_selected A₂ A₃ Q c₂ c₃ s₂ s₃ hz,hx⟩

instance relaxedLattice4_discrete {d : ℕ} (P : Submodule ℚ (Fin 4 → ℚ))
    (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) (Q : ℝ) (c₂ c₃ : Fin 4 → ℝ) (s₂ s₃ : Fin d → Fin 4) :
    DiscreteTopology (relaxedLattice4 P A₂ A₃ Q c₂ c₃ s₂ s₃) := by
  let G := integerRealImage (selectedSourceGroup4 A₂ A₃ Q c₂ c₃ s₂ s₃)
  let f : relaxedLattice4 P A₂ A₃ Q c₂ c₃ s₂ s₃ → G :=
    fun x => ⟨x.val.val,x.property⟩
  apply DiscreteTopology.of_continuous_injective (f := f)
  · exact (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  · intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : G => (z : Fin 4 → ℝ)) h

instance relaxedLattice4_isZLattice {d : ℕ} (P : Submodule ℚ (Fin 4 → ℚ))
    (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) (Q : ℝ) (c₂ c₃ : Fin 4 → ℝ) (s₂ s₃ : Fin d → Fin 4) :
    IsZLattice ℝ (relaxedLattice4 P A₂ A₃ Q c₂ c₃ s₂ s₃) where
  span_top := by
    apply top_unique
    calc
      ⊤ = Submodule.span ℝ (restrictedLattice4 P A₂ A₃ Q c₂ c₃ : Set (rationalRealSpan4 P)) :=
        (IsZLattice.span_top (K := ℝ) (L := restrictedLattice4 P A₂ A₃ Q c₂ c₃)).symm
      _ ≤ _ := Submodule.span_mono (restrictedLattice4_le_relaxed P A₂ A₃ Q c₂ c₃ s₂ s₃)

theorem relaxedLattice4_rank {d : ℕ} (P : Submodule ℚ (Fin 4 → ℚ))
    (hP : Module.finrank ℚ P ≤ 3) (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (Q : ℝ) (c₂ c₃ : Fin 4 → ℝ) (s₂ s₃ : Fin d → Fin 4) :
    Module.finrank ℤ (relaxedLattice4 P A₂ A₃ Q c₂ c₃ s₂ s₃) = Module.finrank ℚ P := by
  rw [ZLattice.rank ℝ,rationalRealSpan4_finrank P hP]

theorem relaxedLattice4_covolume_pos {d : ℕ} (P : Submodule ℚ (Fin 4 → ℚ))
    (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) (Q : ℝ) (c₂ c₃ : Fin 4 → ℝ) (s₂ s₃ : Fin d → Fin 4) :
    0 < ZLattice.covolume (relaxedLattice4 P A₂ A₃ Q c₂ c₃ s₂ s₃) (restrictedMeasure4 P) :=
  ZLattice.covolume_pos _ _

end
end CompoundFeasibility.M193LiteralRestrictedRelaxed4

open scoped BigOperators Matrix
namespace CompoundFeasibility.M193LiteralRestrictedCovolumeOrder4
open RestrictedGeometry4
noncomputable section

theorem covolume_antitone4 (P : Submodule ℚ (Fin 4 → ℚ))
    (L₁ L₂ : Submodule ℤ (rationalRealSpan4 P))
    [DiscreteTopology L₁] [DiscreteTopology L₂] [IsZLattice ℝ L₁] [IsZLattice ℝ L₂]
    (hle : L₁ ≤ L₂) :
    ZLattice.covolume L₂ (restrictedMeasure4 P) ≤ ZLattice.covolume L₁ (restrictedMeasure4 P) := by
  let n := Module.finrank ℝ (rationalRealSpan4 P)
  let b₁ : Basis (Fin n) ℤ L₁ := (Module.finBasis ℤ L₁).reindex (finCongr (ZLattice.rank ℝ L₁))
  let b₂ : Basis (Fin n) ℤ L₂ := (Module.finBasis ℤ L₂).reindex (finCongr (ZLattice.rank ℝ L₂))
  let u : Fin n → L₂ := fun k => Submodule.inclusion hle (b₁ k)
  let T : Matrix (Fin n) (Fin n) ℤ := b₂.toMatrix u
  have hli : LinearIndependent ℤ u :=
    b₁.linearIndependent.map' (Submodule.inclusion hle) (Submodule.ker_inclusion _ _ hle)
  have hT : T.det ≠ 0 := (SourceRelativeIndex6.integer_span_index_det b₂ u hli).2.2
  let bR := b₂.ofZLatticeBasis ℝ L₂
  have hcoord : bR.toMatrix (fun k => (b₁ k : rationalRealSpan4 P)) = T.map (Int.castRingHom ℝ) := by
    ext i k
    change bR.repr (u k : rationalRealSpan4 P) i = (b₂.repr (u k) i : ℝ)
    exact Basis.ofZLatticeBasis_repr_apply ℝ L₂ b₂ (u k) i
  have hfund : (restrictedMeasure4 P).real (ZSpan.fundamentalDomain bR) =
      ZLattice.covolume L₂ (restrictedMeasure4 P) :=
    (ZLattice.covolume_eq_measure_fundamentalDomain L₂ (restrictedMeasure4 P)
      (ZLattice.isAddFundamentalDomain b₂ (restrictedMeasure4 P))).symm
  have hcov : ZLattice.covolume L₁ (restrictedMeasure4 P) =
      |(T.map (Int.castRingHom ℝ)).det| * ZLattice.covolume L₂ (restrictedMeasure4 P) := by
    rw [ZLattice.covolume_eq_det_mul_measureReal L₁ (restrictedMeasure4 P) b₁ bR,Basis.det_apply]
    simp only [Function.comp_def]
    rw [hcoord,hfund]
  have hone : (1 : ℝ) ≤ |(T.map (Int.castRingHom ℝ)).det| := by
    rw [← integer_matrix_det_cast,← Int.cast_abs,← Int.cast_natAbs]
    exact_mod_cast (Int.natAbs_pos.mpr hT)
  rw [hcov]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hone
    (ZLattice.covolume_pos L₂ (restrictedMeasure4 P)).le

end
end CompoundFeasibility.M193LiteralRestrictedCovolumeOrder4

open scoped BigOperators Matrix
namespace CompoundFeasibility.M193LiteralRestrictedRationalMembership4
open RestrictedGeometry4
noncomputable section

theorem rationalRealSpan4_mem_rational (P : Submodule ℚ (Fin 4 → ℚ)) (x : Fin 4 → ℚ) :
    (fun i => (x i : ℝ)) ∈ rationalRealSpan4 P ↔ x ∈ P := by
  constructor
  · intro hx
    obtain ⟨g,hg⟩ := P.subtype.exists_leftInverse_of_injective P.ker_subtype
    let f : (Fin 4 → ℚ) →ₗ[ℚ] (Fin 4 → ℚ) := P.subtype.comp g
    let M : Matrix (Fin 4) (Fin 4) ℚ := LinearMap.toMatrix' f
    let fR := Matrix.toLin' (M.map (algebraMap ℚ ℝ))
    have hfixQ : ∀ y ∈ P, M *ᵥ y = y := by
      intro y hy
      have h := congrArg (fun z : P => (z : Fin 4 → ℚ)) (LinearMap.congr_fun hg ⟨y,hy⟩)
      change (Matrix.toLin' (LinearMap.toMatrix' f)) y = y
      rw [Matrix.toLin'_toMatrix']
      exact h
    have hle : rationalRealSpan4 P ≤ LinearMap.ker (fR-LinearMap.id) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨y,hy,rfl⟩
      change fR (fun i => (y i : ℝ)) - (fun i => (y i : ℝ)) = 0
      apply sub_eq_zero.mpr
      ext i
      have h := congrFun (hfixQ y hy) i
      change ∑ k, (M i k : ℝ)*(y k : ℝ) = (y i : ℝ)
      simp only [Matrix.mulVec,dotProduct] at h
      exact_mod_cast h
    have hfixR : fR (fun i => (x i : ℝ)) = (fun i => (x i : ℝ)) :=
      sub_eq_zero.mp (hle hx)
    have hfix : M *ᵥ x = x := by
      ext i
      have h := congrFun hfixR i
      change (∑ k, (M i k : ℝ)*(x k : ℝ)) = (x i : ℝ) at h
      simp only [Matrix.mulVec,dotProduct]
      exact_mod_cast h
    have hm : M *ᵥ x ∈ P := by
      change (Matrix.toLin' (LinearMap.toMatrix' f)) x ∈ P
      rw [Matrix.toLin'_toMatrix']
      exact (g x).property
    rwa [hfix] at hm
  · intro hx
    exact Submodule.subset_span ⟨x,hx,rfl⟩

end
end CompoundFeasibility.M193LiteralRestrictedRationalMembership4

open scoped BigOperators Matrix
namespace CompoundFeasibility.M193LiteralRestrictedIntegerCoordinates4
open RestrictedGeometry4 M193LiteralRestrictedRelaxed4
noncomputable section

def baseLattice4 (P : Submodule ℚ (Fin 4 → ℚ)) : Submodule ℤ (rationalRealSpan4 P) :=
  restrictedLattice4 P 0 0 2 (fun _ => 0) (fun _ => 0)

theorem baseLattice4_mem (P : Submodule ℚ (Fin 4 → ℚ)) (x : rationalRealSpan4 P) :
    x ∈ baseLattice4 P ↔ ∃ z : Fin 4 → ℤ, integerReal z = (x : Fin 4 → ℝ) := by
  constructor
  · rintro ⟨z,hz,hx⟩
    exact ⟨z,hx⟩
  · rintro ⟨z,hz⟩
    refine ⟨z,?_,hz⟩
    change z ∈ lattice4 2 0 _ ∧ z ∈ lattice4 3 0 _
    constructor
    · apply (lattice4_spec 2 0 _ z).mpr
      intro i
      simp only [Matrix.zero_mulVec,Pi.zero_apply,padicNorm.zero]
      positivity
    · apply (lattice4_spec 3 0 _ z).mpr
      intro i
      simp only [Matrix.zero_mulVec,Pi.zero_apply,padicNorm.zero]
      positivity

theorem relaxedLattice4_le_base {d : ℕ} (P : Submodule ℚ (Fin 4 → ℚ))
    (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) (Q : ℝ) (c₂ c₃ : Fin 4 → ℝ) (s₂ s₃ : Fin d → Fin 4) :
    relaxedLattice4 P A₂ A₃ Q c₂ c₃ s₂ s₃ ≤ baseLattice4 P := by
  rintro x ⟨z,hz,hx⟩
  exact (baseLattice4_mem P x).mpr ⟨z,hx⟩

def baseIntegerBasis4 (P : Submodule ℚ (Fin 4 → ℚ)) (hP : Module.finrank ℚ P ≤ 3) :
    Basis (Fin (Module.finrank ℚ P)) ℤ (baseLattice4 P) := by
  letI : DiscreteTopology (baseLattice4 P) := by
    dsimp only [baseLattice4]
    infer_instance
  letI : IsZLattice ℝ (baseLattice4 P) := by
    dsimp only [baseLattice4]
    infer_instance
  letI : Module.Free ℤ (baseLattice4 P) := ZLattice.module_free ℝ (baseLattice4 P)
  letI : Module.Finite ℤ (baseLattice4 P) := ZLattice.module_finite ℝ (baseLattice4 P)
  exact (Module.finBasis ℤ (baseLattice4 P)).reindex
    (finCongr (restrictedLattice4_rank P hP 0 0 2 (fun _ => 0) (fun _ => 0)))

def integerCoordinateMap4 (P : Submodule ℚ (Fin 4 → ℚ)) (hP : Module.finrank ℚ P ≤ 3) :
    (Fin (Module.finrank ℚ P) → ℤ) →ₗ[ℤ] rationalRealSpan4 P :=
  (baseLattice4 P).subtype.comp (baseIntegerBasis4 P hP).equivFun.symm.toLinearMap

theorem integerCoordinateMap4_injective (P : Submodule ℚ (Fin 4 → ℚ)) (hP : Module.finrank ℚ P ≤ 3) :
    Function.Injective (integerCoordinateMap4 P hP) :=
  (baseLattice4 P).subtype_injective.comp (baseIntegerBasis4 P hP).equivFun.symm.injective

theorem integerCoordinateMap4_equivFun (P : Submodule ℚ (Fin 4 → ℚ))
    (hP : Module.finrank ℚ P ≤ 3) (x : baseLattice4 P) :
    integerCoordinateMap4 P hP ((baseIntegerBasis4 P hP).equivFun x) = (x : rationalRealSpan4 P) := by
  change (((baseIntegerBasis4 P hP).equivFun.symm ((baseIntegerBasis4 P hP).equivFun x) :
    baseLattice4 P) : rationalRealSpan4 P) = (x : rationalRealSpan4 P)
  rw [LinearEquiv.symm_apply_apply]

def relaxedIntegerGroup4 {d : ℕ} (P : Submodule ℚ (Fin 4 → ℚ)) (hP : Module.finrank ℚ P ≤ 3)
    (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) (Q : ℝ) (c₂ c₃ : Fin 4 → ℝ) (s₂ s₃ : Fin d → Fin 4) :
    AddSubgroup (Fin (Module.finrank ℚ P) → ℤ) :=
  (relaxedLattice4 P A₂ A₃ Q c₂ c₃ s₂ s₃).toAddSubgroup.comap
    (integerCoordinateMap4 P hP).toAddMonoidHom

def relaxedIntegerEquiv4 {d : ℕ} (P : Submodule ℚ (Fin 4 → ℚ)) (hP : Module.finrank ℚ P ≤ 3)
    (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) (Q : ℝ) (c₂ c₃ : Fin 4 → ℝ) (s₂ s₃ : Fin d → Fin 4) :
    relaxedIntegerGroup4 P hP A₂ A₃ Q c₂ c₃ s₂ s₃ ≃ₗ[ℤ] relaxedLattice4 P A₂ A₃ Q c₂ c₃ s₂ s₃ where
  toFun z := ⟨integerCoordinateMap4 P hP z,z.property⟩
  invFun x := ⟨(baseIntegerBasis4 P hP).equivFun
    ⟨x.val,relaxedLattice4_le_base P A₂ A₃ Q c₂ c₃ s₂ s₃ x.property⟩,by
      change integerCoordinateMap4 P hP _ ∈ relaxedLattice4 P A₂ A₃ Q c₂ c₃ s₂ s₃
      rw [integerCoordinateMap4_equivFun]
      exact x.property⟩
  left_inv z := by
    apply Subtype.ext
    apply integerCoordinateMap4_injective P hP
    rw [integerCoordinateMap4_equivFun]
  right_inv x := by
    apply Subtype.ext
    change integerCoordinateMap4 P hP ((baseIntegerBasis4 P hP).equivFun
      ⟨x.val,relaxedLattice4_le_base P A₂ A₃ Q c₂ c₃ s₂ s₃ x.property⟩) = x.val
    rw [integerCoordinateMap4_equivFun]
  map_add' x y := by
    apply Subtype.ext
    exact (integerCoordinateMap4 P hP).map_add x y
  map_smul' a x := by
    apply Subtype.ext
    exact (integerCoordinateMap4 P hP).map_smul a x

theorem relaxedIntegerGroup4_rank {d : ℕ} (P : Submodule ℚ (Fin 4 → ℚ)) (hP : Module.finrank ℚ P ≤ 3)
    (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) (Q : ℝ) (c₂ c₃ : Fin 4 → ℝ) (s₂ s₃ : Fin d → Fin 4) :
    Module.finrank ℤ (relaxedIntegerGroup4 P hP A₂ A₃ Q c₂ c₃ s₂ s₃) = Module.finrank ℚ P :=
  (relaxedIntegerEquiv4 P hP A₂ A₃ Q c₂ c₃ s₂ s₃).finrank_eq.trans
    (relaxedLattice4_rank P hP A₂ A₃ Q c₂ c₃ s₂ s₃)

def baseIntegerVector4 (P : Submodule ℚ (Fin 4 → ℚ)) (hP : Module.finrank ℚ P ≤ 3)
    (k : Fin (Module.finrank ℚ P)) : Fin 4 → ℤ :=
  Classical.choose ((baseLattice4_mem P (baseIntegerBasis4 P hP k)).mp (baseIntegerBasis4 P hP k).property)

theorem baseIntegerVector4_values (P : Submodule ℚ (Fin 4 → ℚ)) (hP : Module.finrank ℚ P ≤ 3)
    (k : Fin (Module.finrank ℚ P)) :
    integerReal (baseIntegerVector4 P hP k) = ((baseIntegerBasis4 P hP k : rationalRealSpan4 P) : Fin 4 → ℝ) :=
  Classical.choose_spec ((baseLattice4_mem P (baseIntegerBasis4 P hP k)).mp (baseIntegerBasis4 P hP k).property)

theorem baseIntegerVector4_rational_mem (P : Submodule ℚ (Fin 4 → ℚ)) (hP : Module.finrank ℚ P ≤ 3)
    (k : Fin (Module.finrank ℚ P)) : (fun i => (baseIntegerVector4 P hP k i : ℚ)) ∈ P := by
  apply (M193LiteralRestrictedRationalMembership4.rationalRealSpan4_mem_rational P _).mp
  have he : (fun i => ((baseIntegerVector4 P hP k i : ℚ) : ℝ)) =
      integerReal (baseIntegerVector4 P hP k) := by
    ext i
    simp [integerReal]
  rw [he,baseIntegerVector4_values]
  exact (baseIntegerBasis4 P hP k).val.property

def baseRationalVector4 (P : Submodule ℚ (Fin 4 → ℚ)) (hP : Module.finrank ℚ P ≤ 3)
    (k : Fin (Module.finrank ℚ P)) : P :=
  ⟨fun i => (baseIntegerVector4 P hP k i : ℚ),baseIntegerVector4_rational_mem P hP k⟩

theorem baseRationalVector4_independent (P : Submodule ℚ (Fin 4 → ℚ)) (hP : Module.finrank ℚ P ≤ 3) :
    LinearIndependent ℚ (baseRationalVector4 P hP) := by
  letI : DiscreteTopology (baseLattice4 P) := by dsimp only [baseLattice4];infer_instance
  letI : IsZLattice ℝ (baseLattice4 P) := by dsimp only [baseLattice4];infer_instance
  let b := (baseIntegerBasis4 P hP).ofZLatticeBasis ℝ (baseLattice4 P)
  have hli := b.linearIndependent.map' (rationalRealSpan4 P).subtype (rationalRealSpan4 P).ker_subtype
  have hreal : LinearIndependent ℝ (fun k => integerReal (baseIntegerVector4 P hP k)) := by
    convert hli using 1
    funext k
    rw [baseIntegerVector4_values]
    simp [b,Function.comp_def]
  let ratReal : (Fin 4 → ℚ) →ₗ[ℚ] (Fin 4 → ℝ) :=
    LinearMap.pi (fun i => (Algebra.linearMap ℚ ℝ).comp (LinearMap.proj i))
  have hcast : LinearIndependent ℚ (fun k => ratReal (baseRationalVector4 P hP k : Fin 4 → ℚ)) := by
    convert hreal.restrict_scalars' ℚ using 1
  have hambient := LinearIndependent.of_comp ratReal hcast
  exact LinearIndependent.of_comp P.subtype hambient

def baseRationalBasis4 (P : Submodule ℚ (Fin 4 → ℚ)) (hP : Module.finrank ℚ P ≤ 3) :
    Basis (Fin (Module.finrank ℚ P)) ℚ P :=
  Basis.mk (baseRationalVector4_independent P hP)
    ((baseRationalVector4_independent P hP).span_eq_top_of_card_eq_finrank' (by simp)).ge

end
end CompoundFeasibility.M193LiteralRestrictedIntegerCoordinates4

open scoped BigOperators Matrix
namespace CompoundFeasibility.M193LiteralRestrictedSelectedBasis4
open M193LiteralRestrictedRows4 M193LiteralRestrictedWeightOrder4 M193LiteralSelectedRestriction4 M193LiteralRestrictedIntegerCoordinates4
noncomputable section

theorem rowCoordinates4_change_basis {K : Type*} [Field K] {d : ℕ}
    (P : Submodule K (Fin 4 → K)) (b b' : Basis (Fin d) K P)
    (A : Matrix (Fin 4) (Fin 4) K) :
    rowCoordinates4 P b' A = rowCoordinates4 P b A * b.toMatrix b' := by
  ext i k
  let f : P →ₗ[K] K := (LinearMap.proj i).comp ((Matrix.toLin' A).comp P.subtype)
  have h := congrArg f (b.sum_repr (b' k))
  change f (b' k) = ∑ a, f (b a) * b.repr (b' k) a
  simpa only [map_sum,map_smul,smul_eq_mul,mul_comm] using h.symm

theorem selected_basis_matrix_det4 {K : Type*} [Field K] {d : ℕ}
    (P : Submodule K (Fin 4 → K)) (b b' : Basis (Fin d) K P)
    (A : Matrix (Fin 4) (Fin 4) K) (c : Fin 4 → ℝ)
    (hfull : Submodule.span K (Set.range (rowCoordinates4 P b A).row) = ⊤) :
    (Matrix.of (fun k => rowCoordinates4 P b' A
      (weightOrder4 c (selectedIndex4 (rowCoordinates4 P b A) c hfull k)))).det ≠ 0 := by
  let T := b.toMatrix b'
  have hT : T.det ≠ 0 := by
    have h : T.det * (b'.toMatrix b).det = 1 := by
      rw [← Matrix.det_mul,Basis.toMatrix_mul_toMatrix_flip,Matrix.det_one]
    intro hz
    rw [hz,zero_mul] at h
    exact zero_ne_one h
  have he : Matrix.of (fun k => rowCoordinates4 P b' A
      (weightOrder4 c (selectedIndex4 (rowCoordinates4 P b A) c hfull k))) =
      selectedMatrix4 (rowCoordinates4 P b A) c hfull * T := by
    ext k a
    exact congrFun (congrFun (rowCoordinates4_change_basis P b b' A)
      (weightOrder4 c (selectedIndex4 (rowCoordinates4 P b A) c hfull k))) a
  rw [he,Matrix.det_mul]
  exact mul_ne_zero (selectedMatrix4_det_ne_zero _ c hfull) hT

def finiteSelectedMatrix4 (P : Submodule ℚ (Fin 4 → ℚ)) (hP : Module.finrank ℚ P ≤ 3)
    (A : Matrix (Fin 4) (Fin 4) ℚ) (hA : A.det = 1) (c : Fin 4 → ℝ) :
    Matrix (Fin (Module.finrank ℚ P)) (Fin (Module.finrank ℚ P)) ℚ :=
  fun k => rowCoordinates4 P (baseRationalBasis4 P hP) A
    (weightOrder4 c (selectedIndex4 (rationalRowCoordinates4 P A) c (rationalRowCoordinates4_span P A hA) k))

theorem finiteSelectedMatrix4_det_ne_zero (P : Submodule ℚ (Fin 4 → ℚ)) (hP : Module.finrank ℚ P ≤ 3)
    (A : Matrix (Fin 4) (Fin 4) ℚ) (hA : A.det = 1) (c : Fin 4 → ℝ) :
    (finiteSelectedMatrix4 P hP A hA c).det ≠ 0 :=
  selected_basis_matrix_det4 P (Module.finBasis ℚ P) (baseRationalBasis4 P hP) A c
    (rationalRowCoordinates4_span P A hA)

end
end CompoundFeasibility.M193LiteralRestrictedSelectedBasis4

open scoped BigOperators Matrix
namespace CompoundFeasibility.M193LiteralRestrictedFiniteCoordinates4
open RestrictedGeometry4 M193LiteralRestrictedRelaxed4 M193LiteralRestrictedIntegerCoordinates4 M193LiteralRestrictedRows4
noncomputable section

theorem integerCoordinateMap4_integerReal (P : Submodule ℚ (Fin 4 → ℚ)) (hP : Module.finrank ℚ P ≤ 3)
    (z : Fin (Module.finrank ℚ P) → ℤ) :
    ((integerCoordinateMap4 P hP z : rationalRealSpan4 P) : Fin 4 → ℝ) =
      integerReal (fun i => ∑ k, z k * baseIntegerVector4 P hP k i) := by
  change ((((baseIntegerBasis4 P hP).equivFun.symm z : baseLattice4 P) : rationalRealSpan4 P) : Fin 4 → ℝ) = _
  rw [Basis.equivFun_symm_apply]
  ext i
  simp only [Submodule.coe_sum,Submodule.coe_smul,Submodule.coe_smul_of_tower,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  simp_rw [← baseIntegerVector4_values P hP]
  simp [integerReal]

theorem selected_local_coordinates4 {d : ℕ} (P : Submodule ℚ (Fin 4 → ℚ)) (hP : Module.finrank ℚ P ≤ 3)
    (p : ℕ) [Fact p.Prime] (A : Matrix (Fin 4) (Fin 4) ℚ) (Q : ℝ) (c : Fin 4 → ℝ)
    (s : Fin d → Fin 4) (z : Fin (Module.finrank ℚ P) → ℤ)
    (hz : ((integerCoordinateMap4 P hP z : rationalRealSpan4 P) : Fin 4 → ℝ) ∈
      integerRealImage (selectedLocalGroup4 p A Q c s)) :
    ∀ k, padicNorm p (((fun a b => rowCoordinates4 P (baseRationalBasis4 P hP) A (s a) b) *ᵥ
      (fun i => (z i : ℚ))) k) ≤ (p : ℚ)^(-(Nat.ceil (JSP000334.qThreshold p Q (c (s k))) : ℤ)) := by
  obtain ⟨w,hw,hval⟩ := hz
  have hwval : w = fun i => ∑ k, z k * baseIntegerVector4 P hP k i :=
    integerReal_injective (hval.trans (integerCoordinateMap4_integerReal P hP z))
  subst w
  intro k
  have hk := (AddSubgroup.mem_iInf.mp hw) k
  change padicNorm p ((A *ᵥ (fun i => ((∑ a, z a * baseIntegerVector4 P hP a i : ℤ) : ℚ))) (s k)) ≤
    ((p : ℚ)^Nat.ceil (JSP000334.qThreshold p Q (c (s k))))⁻¹ at hk
  have heval : (((fun a b => rowCoordinates4 P (baseRationalBasis4 P hP) A (s a) b) *ᵥ
      (fun i => (z i : ℚ))) k) =
      (A *ᵥ (fun i => ((∑ a, z a * baseIntegerVector4 P hP a i : ℤ) : ℚ))) (s k) := by
    simp only [Matrix.mulVec,dotProduct,rowCoordinates4,baseRationalBasis4,Basis.mk_apply,
      baseRationalVector4,Int.cast_sum,Int.cast_mul]
    simp_rw [Finset.sum_mul,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro a ha
    ring
  rw [heval]
  simpa only [zpow_neg,zpow_natCast] using hk

end
end CompoundFeasibility.M193LiteralRestrictedFiniteCoordinates4

open scoped BigOperators Matrix
namespace CompoundFeasibility.M193LiteralRestrictedCoordinateCovolume4
open RestrictedGeometry4 M193LiteralRestrictedRelaxed4 M193LiteralRestrictedIntegerCoordinates4
noncomputable section

theorem relaxedLattice4_covolume_index {d : ℕ} (P : Submodule ℚ (Fin 4 → ℚ))
    (hP : Module.finrank ℚ P ≤ 3) (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (Q : ℝ) (c₂ c₃ : Fin 4 → ℝ) (s₂ s₃ : Fin d → Fin 4) :
    ZLattice.covolume (relaxedLattice4 P A₂ A₃ Q c₂ c₃ s₂ s₃) (restrictedMeasure4 P) =
      ((relaxedIntegerGroup4 P hP A₂ A₃ Q c₂ c₃ s₂ s₃).index : ℝ) *
        ZLattice.covolume (baseLattice4 P) (restrictedMeasure4 P) := by
  let H := relaxedIntegerGroup4 P hP A₂ A₃ Q c₂ c₃ s₂ s₃
  let L := relaxedLattice4 P A₂ A₃ Q c₂ c₃ s₂ s₃
  let e : H ≃ₗ[ℤ] L := relaxedIntegerEquiv4 P hP A₂ A₃ Q c₂ c₃ s₂ s₃
  letI : Module.Free ℤ H := Module.Free.of_equiv e.symm
  letI : Module.Finite ℤ H := Module.Finite.equiv e.symm
  let bH : Basis (Fin (Module.finrank ℚ P)) ℤ H :=
    Module.finBasisOfFinrankEq ℤ H (relaxedIntegerGroup4_rank P hP A₂ A₃ Q c₂ c₃ s₂ s₃)
  let bL : Basis (Fin (Module.finrank ℚ P)) ℤ L := bH.map e
  letI : DiscreteTopology (baseLattice4 P) := by dsimp only [baseLattice4];infer_instance
  letI : IsZLattice ℝ (baseLattice4 P) := by dsimp only [baseLattice4];infer_instance
  let b₀ := baseIntegerBasis4 P hP
  let bR := b₀.ofZLatticeBasis ℝ (baseLattice4 P)
  let U : Matrix (Fin (Module.finrank ℚ P)) (Fin (Module.finrank ℚ P)) ℤ :=
    fun i k => (bH k : Fin (Module.finrank ℚ P) → ℤ) i
  have hcoord : bR.toMatrix (fun k => (bL k : rationalRealSpan4 P)) = U.map (Int.castRingHom ℝ) := by
    ext i k
    change (bR.repr (integerCoordinateMap4 P hP (bH k)) i) = ((bH k : Fin (Module.finrank ℚ P) → ℤ) i : ℝ)
    change ((b₀.ofZLatticeBasis ℝ (baseLattice4 P)).repr
      ((b₀.equivFun.symm (bH k : Fin (Module.finrank ℚ P) → ℤ) : baseLattice4 P) : rationalRealSpan4 P)) i = _
    rw [Basis.ofZLatticeBasis_repr_apply]
    change (((b₀.equivFun (b₀.equivFun.symm (bH k : Fin (Module.finrank ℚ P) → ℤ))) i : ℤ) : ℝ) = _
    rw [LinearEquiv.apply_symm_apply]
  have hindex : |(U.map (Int.castRingHom ℝ)).det| = (H.index : ℝ) := by
    have h := AddSubgroup.index_eq_natAbs_det (Pi.basisFun ℤ (Fin (Module.finrank ℚ P))) H bH
    rw [Basis.det_apply] at h
    have he : (Pi.basisFun ℤ (Fin (Module.finrank ℚ P))).toMatrix
        (fun k => (bH k : Fin (Module.finrank ℚ P) → ℤ)) = U := by rfl
    rw [he] at h
    rw [← integer_matrix_det_cast,← Int.cast_abs,← Int.cast_natAbs,← h]
  have hfund : (restrictedMeasure4 P).real (ZSpan.fundamentalDomain bR) =
      ZLattice.covolume (baseLattice4 P) (restrictedMeasure4 P) :=
    (ZLattice.covolume_eq_measure_fundamentalDomain (baseLattice4 P) (restrictedMeasure4 P)
      (ZLattice.isAddFundamentalDomain b₀ (restrictedMeasure4 P))).symm
  change ZLattice.covolume L (restrictedMeasure4 P) = _
  rw [ZLattice.covolume_eq_det_mul_measureReal L (restrictedMeasure4 P) bL bR,Basis.det_apply]
  simp only [Function.comp_def]
  rw [hcoord,hindex,hfund]

end
end CompoundFeasibility.M193LiteralRestrictedCoordinateCovolume4

open scoped BigOperators Matrix
namespace CompoundFeasibility.M193LiteralRestrictedFiniteBound4
open RestrictedGeometry4 M193LiteralRestrictedRelaxed4 M193LiteralRestrictedIntegerCoordinates4 M193LiteralRestrictedRows4
open M193LiteralRestrictedWeightOrder4 M193LiteralSelectedRestriction4 M193LiteralRestrictedSelectedBasis4 M193LiteralRestrictedFiniteCoordinates4
open M193LiteralRestrictedCoordinateCovolume4 M193LiteralRestrictedSelectedIndex4
noncomputable section

def finiteSelection4 (P : Submodule ℚ (Fin 4 → ℚ)) (A : Matrix (Fin 4) (Fin 4) ℚ)
    (hA : A.det = 1) (c : Fin 4 → ℝ) : Fin (Module.finrank ℚ P) → Fin 4 :=
  fun k => weightOrder4 c (selectedIndex4 (rationalRowCoordinates4 P A) c (rationalRowCoordinates4_span P A hA) k)

theorem selected_prime_powers_lower4 {d : ℕ} (p : ℕ) (hp : 1 < p)
    (Q : ℝ) (hQ : 1 < Q) (c : Fin d → ℝ) :
    Q^(-(∑ k, c k)) ≤ (p : ℝ)^(∑ k, Nat.ceil (JSP000334.qThreshold p Q (c k))) := by
  have hQpos : 0 < Q := zero_lt_one.trans hQ
  calc
    _ = ∏ k, Q^(-c k) := by
      rw [← Real.rpow_sum_of_pos hQpos]
      simp
    _ ≤ ∏ k, (p : ℝ)^Nat.ceil (JSP000334.qThreshold p Q (c k)) := by
      apply Finset.prod_le_prod (fun _ _ => (Real.rpow_pos_of_pos hQpos _).le)
      intro k hk
      rw [← JSP000334.qThreshold_rpow p hp Q (c k) hQ,← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hp.le) (Nat.le_ceil _)
    _ = _ := Finset.prod_pow_eq_pow_sum _ _ _

theorem source_finite_inverse_covolume4 (P : Submodule ℚ (Fin 4 → ℚ))
    (hP : Module.finrank ℚ P ≤ 3) (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (h₂ : A₂.det = 1) (h₃ : A₃.det = 1) (c₂ c₃ : Fin 4 → ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (Q : ℝ), 1 < Q →
      1 / ZLattice.covolume
        (relaxedLattice4 P A₂ A₃ Q c₂ c₃ (finiteSelection4 P A₂ h₂ c₂) (finiteSelection4 P A₃ h₃ c₃))
        (restrictedMeasure4 P) ≤
      K * Q^((∑ k, c₂ (finiteSelection4 P A₂ h₂ c₂ k)) + (∑ k, c₃ (finiteSelection4 P A₃ h₃ c₃ k))) := by
  letI : DiscreteTopology (baseLattice4 P) := by dsimp only [baseLattice4];infer_instance
  letI : IsZLattice ℝ (baseLattice4 P) := by dsimp only [baseLattice4];infer_instance
  let s₂ := finiteSelection4 P A₂ h₂ c₂
  let s₃ := finiteSelection4 P A₃ h₃ c₃
  let B₂ := finiteSelectedMatrix4 P hP A₂ h₂ c₂
  let B₃ := finiteSelectedMatrix4 P hP A₃ h₃ c₃
  let D : ℝ := (padicNorm 2 B₂.det : ℝ) * (padicNorm 3 B₃.det : ℝ)
  let C₀ := ZLattice.covolume (baseLattice4 P) (restrictedMeasure4 P)
  have hD₂ : 0 < (padicNorm 2 B₂.det : ℝ) := by
    exact_mod_cast lt_of_le_of_ne (padicNorm.nonneg B₂.det)
      (Ne.symm (padicNorm.nonzero (finiteSelectedMatrix4_det_ne_zero P hP A₂ h₂ c₂)))
  have hD₃ : 0 < (padicNorm 3 B₃.det : ℝ) := by
    exact_mod_cast lt_of_le_of_ne (padicNorm.nonneg B₃.det)
      (Ne.symm (padicNorm.nonzero (finiteSelectedMatrix4_det_ne_zero P hP A₃ h₃ c₃)))
  have hD : 0 < D := mul_pos hD₂ hD₃
  have hC₀ : 0 < C₀ := ZLattice.covolume_pos _ _
  refine ⟨1/(D*C₀),div_pos zero_lt_one (mul_pos hD hC₀),?_⟩
  intro Q hQ
  let F := (∑ k, c₂ (s₂ k)) + ∑ k, c₃ (s₃ k)
  let e₂ := fun k => Nat.ceil (JSP000334.qThreshold 2 Q (c₂ (s₂ k)))
  let e₃ := fun k => Nat.ceil (JSP000334.qThreshold 3 Q (c₃ (s₃ k)))
  let H := relaxedIntegerGroup4 P hP A₂ A₃ Q c₂ c₃ s₂ s₃
  let E := relaxedIntegerEquiv4 P hP A₂ A₃ Q c₂ c₃ s₂ s₃
  letI : Module.Free ℤ H := Module.Free.of_equiv E.symm
  letI : Module.Finite ℤ H := Module.Finite.equiv E.symm
  let bH : Basis (Fin (Module.finrank ℚ P)) ℤ H :=
    Module.finBasisOfFinrankEq ℤ H (relaxedIntegerGroup4_rank P hP A₂ A₃ Q c₂ c₃ s₂ s₃)
  have hnorm₂ (z : H) : ∀ k, padicNorm 2 ((B₂ *ᵥ (fun i => ((z : Fin (Module.finrank ℚ P) → ℤ) i : ℚ))) k) ≤
      (2 : ℚ)^(-(e₂ k : ℤ)) := by
    apply selected_local_coordinates4 P hP 2 A₂ Q c₂ s₂ z
    obtain ⟨w,hw,hval⟩ := z.property
    exact ⟨w,hw.1,hval⟩
  have hnorm₃ (z : H) : ∀ k, padicNorm 3 ((B₃ *ᵥ (fun i => ((z : Fin (Module.finrank ℚ P) → ℤ) i : ℚ))) k) ≤
      (3 : ℚ)^(-(e₃ k : ℤ)) := by
    apply selected_local_coordinates4 P hP 3 A₃ Q c₃ s₃ z
    obtain ⟨w,hw,hval⟩ := z.property
    exact ⟨w,hw.2,hval⟩
  have hindex := selected_rational_index_lower4 ⟨Module.finrank ℚ P,by omega⟩
    B₂ B₃ H bH e₂ e₃ hnorm₂ hnorm₃
  have hlow₂ := selected_prime_powers_lower4 2 (by decide) Q hQ (fun k => c₂ (s₂ k))
  have hlow₃ := selected_prime_powers_lower4 3 (by decide) Q hQ (fun k => c₃ (s₃ k))
  have hQpos : 0 < Q := zero_lt_one.trans hQ
  have hQlow : Q^(-F) ≤ (2 : ℝ)^(∑ k, e₂ k) * (3 : ℝ)^(∑ k, e₃ k) := by
    calc
      _ = Q^(-(∑ k, c₂ (s₂ k))) * Q^(-(∑ k, c₃ (s₃ k))) := by
        rw [← Real.rpow_add hQpos]
        congr 1
        dsimp [F]
        ring
      _ ≤ _ := mul_le_mul hlow₂ hlow₃ (by positivity) (by positivity)
  have hidxlo : D*Q^(-F) ≤ (H.index : ℝ) := by
    calc
      _ ≤ D * ((2 : ℝ)^(∑ k, e₂ k) * (3 : ℝ)^(∑ k, e₃ k)) :=
        mul_le_mul_of_nonneg_left hQlow hD.le
      _ ≤ _ := by convert hindex using 1 <;> ring
  have hcvlo : D*C₀*Q^(-F) ≤
      ZLattice.covolume (relaxedLattice4 P A₂ A₃ Q c₂ c₃ s₂ s₃) (restrictedMeasure4 P) := by
    rw [relaxedLattice4_covolume_index P hP]
    convert mul_le_mul_of_nonneg_right hidxlo hC₀.le using 1 <;> ring
  have hcancel : Q^(-F)*Q^F = 1 := by rw [← Real.rpow_add hQpos];simp
  have hbound : D*C₀ ≤ ZLattice.covolume (relaxedLattice4 P A₂ A₃ Q c₂ c₃ s₂ s₃)
      (restrictedMeasure4 P) * Q^F := by
    calc
      _ = (D*C₀*Q^(-F))*Q^F := by
        calc
          D*C₀ = D*C₀*(Q^(-F)*Q^F) := by rw [hcancel,mul_one]
          _ = _ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hcvlo (Real.rpow_pos_of_pos hQpos _).le
  change 1 / ZLattice.covolume (relaxedLattice4 P A₂ A₃ Q c₂ c₃ s₂ s₃) (restrictedMeasure4 P) ≤
    (1/(D*C₀))*Q^F
  rw [div_mul_eq_mul_div,one_mul]
  apply (div_le_div_iff₀ (relaxedLattice4_covolume_pos P A₂ A₃ Q c₂ c₃ s₂ s₃) (mul_pos hD hC₀)).mpr
  simpa only [one_mul,mul_comm] using hbound

end
end CompoundFeasibility.M193LiteralRestrictedFiniteBound4

open scoped BigOperators
open MeasureTheory
namespace CompoundFeasibility.M193LiteralSelectedBoxVolume4
noncomputable section

def weightedBox4 {d : ℕ} (r : Fin d → ℝ) : Set (Fin d → ℝ) :=
  Set.pi Set.univ (fun i => Set.Icc (-r i) (r i))

theorem weightedBox4_compact_convex {d : ℕ} (r : Fin d → ℝ)
    (e : (Fin d → ℝ) ≃ₗ[ℝ] (Fin d → ℝ)) :
    IsCompact (e ⁻¹' weightedBox4 r) ∧ Convex ℝ (e ⁻¹' weightedBox4 r) := by
  have hc : IsCompact (weightedBox4 r) := isCompact_univ_pi (fun _ => isCompact_Icc)
  constructor
  · have hh : IsCompact (e.symm '' weightedBox4 r) :=
      hc.image e.symm.toContinuousLinearEquiv.continuous
    simpa only [LinearEquiv.image_eq_preimage,LinearEquiv.symm_symm] using hh
  · exact (convex_pi (fun _ _ => convex_Icc _ _)).linear_preimage e.toLinearMap

theorem weightedBox4_volume {d : ℕ} (r : Fin d → ℝ) (hr : ∀ i, 0 < r i)
    (e : (Fin d → ℝ) ≃ₗ[ℝ] (Fin d → ℝ)) :
    volume.real (e ⁻¹' weightedBox4 r) =
      (2 : ℝ)^d * (∏ i, r i) / |LinearMap.det e.toLinearMap| := by
  rw [measureReal_def,weightedBox4,Measure.addHaar_preimage_linearEquiv,volume_pi,Measure.pi_pi]
  simp only [Real.volume_Icc,sub_neg_eq_add,← two_mul,
    ENNReal.toReal_mul,ENNReal.toReal_prod,LinearEquiv.det_coe_symm,abs_inv,
    ENNReal.toReal_ofReal,abs_nonneg,div_eq_mul_inv]
  have hnonneg : ∀ i, 0 ≤ 2*r i := fun i => le_of_lt (mul_pos (by norm_num) (hr i))
  simp only [ENNReal.toReal_ofReal (hnonneg _),Finset.prod_mul_distrib,Finset.prod_const,
    Finset.card_univ,Fintype.card_fin]
  rw [ENNReal.toReal_ofReal (inv_nonneg.mpr (abs_nonneg _))]
  ring

end
end CompoundFeasibility.M193LiteralSelectedBoxVolume4

open scoped BigOperators Matrix
open MeasureTheory
namespace CompoundFeasibility.M193LiteralRestrictedRealBody4
open RestrictedGeometry4 M193LiteralRestrictedRelaxed4 M193LiteralRestrictedIntegerCoordinates4 M193LiteralRestrictedRows4
open M193LiteralRestrictedWeightOrder4 M193LiteralSelectedRestriction4 M193LiteralRestrictedSelectedBasis4 M193LiteralSelectedBoxVolume4
noncomputable section

def baseRealBasis4 (P : Submodule ℚ (Fin 4 → ℚ)) (hP : Module.finrank ℚ P ≤ 3) :
    Basis (Fin (Module.finrank ℚ P)) ℝ (rationalRealSpan4 P) := by
  letI : DiscreteTopology (baseLattice4 P) := by dsimp only [baseLattice4];infer_instance
  letI : IsZLattice ℝ (baseLattice4 P) := by dsimp only [baseLattice4];infer_instance
  exact (baseIntegerBasis4 P hP).ofZLatticeBasis ℝ (baseLattice4 P)

def realSelection4 (P : Submodule ℚ (Fin 4 → ℚ)) (hP : Module.finrank ℚ P ≤ 3)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : L.det = 1) (c : Fin 4 → ℝ) : Fin (Module.finrank ℚ P) → Fin 4 :=
  fun k => weightOrder4 c (selectedIndex4 (realRestrictionCoordinates4 P hP L) c
    (realRestrictionCoordinates4_span P hP L hL) k)

def realSelectedMatrix4 (P : Submodule ℚ (Fin 4 → ℚ)) (hP : Module.finrank ℚ P ≤ 3)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : L.det = 1) (c : Fin 4 → ℝ) :
    Matrix (Fin (Module.finrank ℚ P)) (Fin (Module.finrank ℚ P)) ℝ :=
  fun k => rowCoordinates4 (rationalRealSpan4 P) (baseRealBasis4 P hP) L (realSelection4 P hP L hL c k)

theorem realSelectedMatrix4_det_ne_zero (P : Submodule ℚ (Fin 4 → ℚ)) (hP : Module.finrank ℚ P ≤ 3)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : L.det = 1) (c : Fin 4 → ℝ) :
    (realSelectedMatrix4 P hP L hL c).det ≠ 0 :=
  selected_basis_matrix_det4 (rationalRealSpan4 P) (realRestrictionBasis4 P hP) (baseRealBasis4 P hP)
    L c (realRestrictionCoordinates4_span P hP L hL)

def selectedRealEquiv4 (P : Submodule ℚ (Fin 4 → ℚ)) (hP : Module.finrank ℚ P ≤ 3)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : L.det = 1) (c : Fin 4 → ℝ) :
    (Fin (Module.finrank ℚ P) → ℝ) ≃ₗ[ℝ] (Fin (Module.finrank ℚ P) → ℝ) :=
  LinearEquiv.ofBijective (Matrix.toLin' (realSelectedMatrix4 P hP L hL c)) (by
    have hu : IsUnit (realSelectedMatrix4 P hP L hL c) :=
      (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr (realSelectedMatrix4_det_ne_zero P hP L hL c))
    exact ⟨Matrix.mulVec_injective_iff_isUnit.mpr hu,Matrix.mulVec_surjective_iff_isUnit.mpr hu⟩)

theorem rowCoordinates4_mulVec_basis {K : Type*} [Field K] {d : ℕ}
    (P : Submodule K (Fin 4 → K)) (b : Basis (Fin d) K P)
    (A : Matrix (Fin 4) (Fin 4) K) (x : P) :
    rowCoordinates4 P b A *ᵥ b.equivFun x = A *ᵥ (x : Fin 4 → K) := by
  ext i
  let f : P →ₗ[K] K := (LinearMap.proj i).comp ((Matrix.toLin' A).comp P.subtype)
  have h := congrArg f (b.sum_repr x)
  change ∑ k, f (b k) * b.repr x k = f x
  simpa only [map_sum,map_smul,smul_eq_mul,mul_comm] using h

theorem relaxedBody4_coordinates (P : Submodule ℚ (Fin 4 → ℚ)) (hP : Module.finrank ℚ P ≤ 3)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : L.det = 1) (Q : ℝ) (c : Fin 4 → ℝ) :
    relaxedBody4 P L Q c (realSelection4 P hP L hL c) =
      (baseRealBasis4 P hP).equivFun ⁻¹' ((selectedRealEquiv4 P hP L hL c) ⁻¹'
        weightedBox4 (fun k => Q^(c (realSelection4 P hP L hL c k)))) := by
  have heval (x : rationalRealSpan4 P) (k : Fin (Module.finrank ℚ P)) :
      selectedRealEquiv4 P hP L hL c ((baseRealBasis4 P hP).equivFun x) k =
        (L *ᵥ (x : Fin 4 → ℝ)) (realSelection4 P hP L hL c k) :=
    congrFun (rowCoordinates4_mulVec_basis (rationalRealSpan4 P) (baseRealBasis4 P hP) L x)
      (realSelection4 P hP L hL c k)
  ext x
  simp only [relaxedBody4,Set.mem_setOf_eq,Set.mem_preimage,weightedBox4,Set.mem_pi,
    Set.mem_univ,forall_const,Set.mem_Icc,heval,abs_le]

theorem source_relaxed_body_geometry4 (P : Submodule ℚ (Fin 4 → ℚ)) (hP : Module.finrank ℚ P ≤ 3)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : L.det = 1) (Q : ℝ) (hQ : 1 < Q) (c : Fin 4 → ℝ) :
    IsCompact (relaxedBody4 P L Q c (realSelection4 P hP L hL c)) ∧
    Convex ℝ (relaxedBody4 P L Q c (realSelection4 P hP L hL c)) ∧
    (0 : rationalRealSpan4 P) ∈ interior (relaxedBody4 P L Q c (realSelection4 P hP L hL c)) ∧
    0 < (restrictedMeasure4 P).real (relaxedBody4 P L Q c (realSelection4 P hP L hL c)) ∧
    (restrictedMeasure4 P) (relaxedBody4 P L Q c (realSelection4 P hP L hL c)) < ⊤ := by
  let r := fun k => Q^(c (realSelection4 P hP L hL c k))
  let e := selectedRealEquiv4 P hP L hL c
  let b := baseRealBasis4 P hP
  obtain ⟨hbox,hconvex⟩ := weightedBox4_compact_convex r e
  have hcompact : IsCompact (relaxedBody4 P L Q c (realSelection4 P hP L hL c)) := by
    rw [relaxedBody4_coordinates]
    have hh : IsCompact (b.equivFun.symm '' (e ⁻¹' weightedBox4 r)) :=
      hbox.image b.equivFunL.symm.continuous
    simpa only [LinearEquiv.image_eq_preimage,LinearEquiv.symm_symm] using hh
  have hconv : Convex ℝ (relaxedBody4 P L Q c (realSelection4 P hP L hL c)) := by
    rw [relaxedBody4_coordinates]
    exact hconvex.linear_preimage b.equivFun.toLinearMap
  have hi : (0 : rationalRealSpan4 P) ∈ interior (relaxedBody4 P L Q c (realSelection4 P hP L hL c)) :=
    interior_mono (restrictedBody4_subset_relaxed P L Q c _) (restrictedBody4_zero_interior P L (sourceUnit42 L hL) Q hQ c)
  have hfinite := hcompact.measure_lt_top (μ := restrictedMeasure4 P)
  have hpos := Measure.measure_pos_of_nonempty_interior (restrictedMeasure4 P) ⟨0,hi⟩
  exact ⟨hcompact,hconv,hi,ENNReal.toReal_pos hpos.ne' hfinite.ne,hfinite⟩

theorem source_uniform_real_volume4 (P : Submodule ℚ (Fin 4 → ℚ)) (hP : Module.finrank ℚ P ≤ 3)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : L.det = 1) (c : Fin 4 → ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (Q : ℝ), 1 < Q →
      (restrictedMeasure4 P).real (relaxedBody4 P L Q c (realSelection4 P hP L hL c)) =
      K * Q^(∑ k, c (realSelection4 P hP L hL c k)) := by
  letI : DiscreteTopology (baseLattice4 P) := by dsimp only [baseLattice4];infer_instance
  letI : IsZLattice ℝ (baseLattice4 P) := by dsimp only [baseLattice4];infer_instance
  let b₀ := baseIntegerBasis4 P hP
  let b := baseRealBasis4 P hP
  let M := realSelectedMatrix4 P hP L hL c
  let e := selectedRealEquiv4 P hP L hL c
  let s := realSelection4 P hP L hL c
  let C₀ := ZLattice.covolume (baseLattice4 P) (restrictedMeasure4 P)
  let K := C₀ * (2 : ℝ)^(Module.finrank ℚ P) / |M.det|
  have hC₀ : 0 < C₀ := ZLattice.covolume_pos _ _
  have hM : 0 < |M.det| := abs_pos.mpr (realSelectedMatrix4_det_ne_zero P hP L hL c)
  have hK : 0 < K := div_pos (mul_pos hC₀ (by positivity)) hM
  refine ⟨K,hK,?_⟩
  intro Q hQ
  have hQpos : 0 < Q := zero_lt_one.trans hQ
  let r := fun k => Q^(c (s k))
  have hc := (source_relaxed_body_geometry4 P hP L hL Q hQ c).1
  have himage : b.equivFun '' relaxedBody4 P L Q c s = e ⁻¹' weightedBox4 r := by
    rw [relaxedBody4_coordinates,Set.image_preimage_eq _ b.equivFun.surjective]
  have hratio := restrictedBasis4_volume_ratio (P := P) (A₂ := 0) (A₃ := 0) (Q := 2)
    (c₂ := fun _ => 0) (c₃ := fun _ => 0) b₀ (relaxedBody4 P L Q c s) hc
  change volume.real (b.equivFun '' relaxedBody4 P L Q c s) =
    (restrictedMeasure4 P).real (relaxedBody4 P L Q c s) / C₀ at hratio
  have hdet : LinearMap.det e.toLinearMap = M.det := LinearMap.det_toLin' M
  rw [himage,weightedBox4_volume r (fun k => Real.rpow_pos_of_pos hQpos _) e,hdet] at hratio
  have hprod : (∏ k, r k) = Q^(∑ k, c (s k)) := by
    dsimp [r]
    rw [← Real.rpow_sum_of_pos hQpos _ Finset.univ]
  rw [hprod] at hratio
  calc
    _ = ((2 : ℝ)^(Module.finrank ℚ P) * Q^(∑ k, c (s k)) / |M.det|) * C₀ :=
      ((eq_div_iff hC₀.ne').mp hratio).symm
    _ = _ := by dsimp [K];ring

end
end CompoundFeasibility.M193LiteralRestrictedRealBody4

open scoped BigOperators Matrix
open MeasureTheory
namespace CompoundFeasibility.M193LiteralRestrictedOpposite4
open RestrictedGeometry4 M193LiteralRestrictedRelaxed4 M193LiteralRestrictedWeightOrder4 M193LiteralSelectedRestriction4
open M193LiteralRestrictedRealBody4 M193LiteralRestrictedFiniteBound4 M193LiteralRestrictedCovolumeOrder4
noncomputable section

theorem selectedLocalGroup4_rpow_spec {d : ℕ} (p : ℕ) [Fact p.Prime]
    (A : Matrix (Fin 4) (Fin 4) ℚ) (Q : ℝ) (hQ : 1 < Q) (c : Fin 4 → ℝ)
    (hc : ∀ i, c i ≤ 0) (s : Fin d → Fin 4) (z : Fin 4 → ℤ) :
    z ∈ selectedLocalGroup4 p A Q c s ↔
      ∀ k, (padicNorm p ((A *ᵥ (fun i => (z i : ℚ))) (s k)) : ℝ) ≤ Q^(c (s k)) := by
  simp only [selectedLocalGroup4,AddSubgroup.mem_iInf,AddSubgroup.mem_comap]
  exact forall_congr' (fun k => (padic_rpow_ceil42 p Q (c (s k)) hQ (hc _) _).symm)

def oppositePoint4 (P : Submodule ℚ (Fin 4 → ℚ)) (hP : Module.finrank ℚ P ≤ 3)
    (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ)
    (h₂ : A₂.det = 1) (h₃ : A₃.det = 1) (hL : L.det = 1)
    (c₀ c₂ c₃ : Fin 4 → ℝ) (Q K : ℝ) : Prop :=
  let s₀ := realSelection4 P hP L hL c₀
  let s₂ := finiteSelection4 P A₂ h₂ c₂
  let s₃ := finiteSelection4 P A₃ h₃ c₃
  let G := relaxedLattice4 P A₂ A₃ Q c₂ c₃ s₂ s₃
  let C := relaxedBody4 P L Q c₀ s₀
  restrictedBody4 P L Q c₀ ⊆ C ∧
  restrictedLattice4 P A₂ A₃ Q c₂ c₃ ≤ G ∧
  IsCompact C ∧ Convex ℝ C ∧ (0 : rationalRealSpan4 P) ∈ interior C ∧
  0 < (restrictedMeasure4 P).real C ∧ (restrictedMeasure4 P) C < ⊤ ∧
  Module.finrank ℤ G = Module.finrank ℚ P ∧
  0 < ZLattice.covolume G (restrictedMeasure4 P) ∧
  ZLattice.covolume G (restrictedMeasure4 P) ≤
    ZLattice.covolume (restrictedLattice4 P A₂ A₃ Q c₂ c₃) (restrictedMeasure4 P) ∧
  (∀ z : Fin 4 → ℤ, z ∈ selectedSourceGroup4 A₂ A₃ Q c₂ c₃ s₂ s₃ ↔
    (∀ k, (padicNorm 2 ((A₂ *ᵥ (fun i => (z i : ℚ))) (s₂ k)) : ℝ) ≤ Q^(c₂ (s₂ k))) ∧
    (∀ k, (padicNorm 3 ((A₃ *ᵥ (fun i => (z i : ℚ))) (s₃ k)) : ℝ) ≤ Q^(c₃ (s₃ k)))) ∧
  (restrictedMeasure4 P).real (restrictedBody4 P L Q c₀) /
    ZLattice.covolume (restrictedLattice4 P A₂ A₃ Q c₂ c₃) (restrictedMeasure4 P) ≤
      (restrictedMeasure4 P).real C / ZLattice.covolume G (restrictedMeasure4 P) ∧
  (restrictedMeasure4 P).real C / ZLattice.covolume G (restrictedMeasure4 P) ≤
    K * Q^(sourceSelectedExponent4 P hP A₂ A₃ L h₂ h₃ hL c₀ c₂ c₃) ∧
  (restrictedMeasure4 P).real (restrictedBody4 P L Q c₀) /
    ZLattice.covolume (restrictedLattice4 P A₂ A₃ Q c₂ c₃) (restrictedMeasure4 P) ≤
      K * Q^(sourceSelectedExponent4 P hP A₂ A₃ L h₂ h₃ hL c₀ c₂ c₃)

theorem source_restricted_opposite_uniform4 (P : Submodule ℚ (Fin 4 → ℚ))
    (hP : Module.finrank ℚ P ≤ 3) (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (h₂ : A₂.det = 1) (h₃ : A₃.det = 1) (hL : L.det = 1)
    (c₀ c₂ c₃ : Fin 4 → ℝ) (hc₂ : ∀ i, c₂ i ≤ 0) (hc₃ : ∀ i, c₃ i ≤ 0) :
    ∃ K : ℝ, 0 < K ∧ ∀ (Q : ℝ), 1 < Q → oppositePoint4 P hP A₂ A₃ L h₂ h₃ hL c₀ c₂ c₃ Q K := by
  obtain ⟨Kreal,hKreal,hreal⟩ := source_uniform_real_volume4 P hP L hL c₀
  obtain ⟨Kfinite,hKfinite,hfinite⟩ := source_finite_inverse_covolume4 P hP A₂ A₃ h₂ h₃ c₂ c₃
  refine ⟨Kreal*Kfinite,mul_pos hKreal hKfinite,?_⟩
  intro Q hQ
  let s₀ := realSelection4 P hP L hL c₀
  let s₂ := finiteSelection4 P A₂ h₂ c₂
  let s₃ := finiteSelection4 P A₃ h₃ c₃
  let G := relaxedLattice4 P A₂ A₃ Q c₂ c₃ s₂ s₃
  let C := relaxedBody4 P L Q c₀ s₀
  obtain ⟨hcompact,hconv,hinterior,hvol,hvolfinite⟩ := source_relaxed_body_geometry4 P hP L hL Q hQ c₀
  have hbody := restrictedBody4_subset_relaxed P L Q c₀ s₀
  have hlattice := restrictedLattice4_le_relaxed P A₂ A₃ Q c₂ c₃ s₂ s₃
  have hcov := relaxedLattice4_covolume_pos P A₂ A₃ Q c₂ c₃ s₂ s₃
  have hcovorder := covolume_antitone4 P _ _ hlattice
  have hvolorder := measureReal_mono (μ := restrictedMeasure4 P) hbody hvolfinite.ne
  have hratio : (restrictedMeasure4 P).real (restrictedBody4 P L Q c₀) /
      ZLattice.covolume (restrictedLattice4 P A₂ A₃ Q c₂ c₃) (restrictedMeasure4 P) ≤
      (restrictedMeasure4 P).real C / ZLattice.covolume G (restrictedMeasure4 P) := by
    calc
      _ ≤ (restrictedMeasure4 P).real C /
          ZLattice.covolume (restrictedLattice4 P A₂ A₃ Q c₂ c₃) (restrictedMeasure4 P) :=
        div_le_div_of_nonneg_right hvolorder (restrictedLattice4_covolume_pos P A₂ A₃ Q c₂ c₃).le
      _ ≤ _ := div_le_div_of_nonneg_left (measureReal_nonneg) hcov hcovorder
  have hQpos : 0 < Q := zero_lt_one.trans hQ
  have hupper : (restrictedMeasure4 P).real C / ZLattice.covolume G (restrictedMeasure4 P) ≤
      (Kreal*Kfinite) * Q^(sourceSelectedExponent4 P hP A₂ A₃ L h₂ h₃ hL c₀ c₂ c₃) := by
    calc
      _ = (restrictedMeasure4 P).real C * (1 / ZLattice.covolume G (restrictedMeasure4 P)) := by ring
      _ ≤ (restrictedMeasure4 P).real C *
          (Kfinite*Q^((∑ k, c₂ (s₂ k))+(∑ k, c₃ (s₃ k)))) :=
        mul_le_mul_of_nonneg_left (hfinite Q hQ) measureReal_nonneg
      _ = (Kreal*Q^(∑ k, c₀ (s₀ k))) *
          (Kfinite*Q^((∑ k, c₂ (s₂ k))+(∑ k, c₃ (s₃ k)))) := by rw [hreal Q hQ]
      _ = (Kreal*Kfinite) * (Q^(∑ k, c₀ (s₀ k)) * Q^((∑ k, c₂ (s₂ k))+(∑ k, c₃ (s₃ k)))) := by ring
      _ = _ := by
        rw [← Real.rpow_add hQpos]
        congr 2
        dsimp [sourceSelectedExponent4,s₀,s₂,s₃,realSelection4,finiteSelection4]
        ring
  refine ⟨hbody,hlattice,hcompact,hconv,hinterior,hvol,hvolfinite,
    relaxedLattice4_rank P hP A₂ A₃ Q c₂ c₃ s₂ s₃,hcov,hcovorder,?_,hratio,hupper,hratio.trans hupper⟩
  intro z
  change (z ∈ selectedLocalGroup4 2 A₂ Q c₂ s₂ ∧ z ∈ selectedLocalGroup4 3 A₃ Q c₃ s₃) ↔ _
  rw [selectedLocalGroup4_rpow_spec 2 A₂ Q hQ c₂ hc₂ s₂ z,
    selectedLocalGroup4_rpow_spec 3 A₃ Q hQ c₃ hc₃ s₃ z]

theorem source_finite_greedy_indices4 (P : Submodule ℚ (Fin 4 → ℚ))
    (A : Matrix (Fin 4) (Fin 4) ℚ) (hA : A.det = 1) (c : Fin 4 → ℝ) :
    let M := M193LiteralRestrictedRows4.rationalRowCoordinates4 P A
    let hf := M193LiteralRestrictedRows4.rationalRowCoordinates4_span P A hA
    let E := selectedIndex4 M c hf
    StrictMono E ∧ ∀ k : Fin (Module.finrank ℚ P),
      Module.finrank ℚ (Submodule.span ℚ (M193LiteralRestrictedGreedyRows4.rowPrefix4 (sortedRows4 M c) ((E k).val+1))) = k.val+1 ∧
      ∀ i : Fin 4, i < E k → Module.finrank ℚ (Submodule.span ℚ
        (M193LiteralRestrictedGreedyRows4.rowPrefix4 (sortedRows4 M c) (i.val+1))) ≤ k.val := by
  refine ⟨(selectedIndex4 _ c _).strictMono,?_⟩
  intro k
  exact M193LiteralRestrictedGreedyRanks4.greedyIndex4_first_rank_increase _
    (sortedRows4_span _ c (M193LiteralRestrictedRows4.rationalRowCoordinates4_span P A hA))
    (Module.finrank ℚ P) (by simp) k

theorem source_real_greedy_indices4 (P : Submodule ℚ (Fin 4 → ℚ)) (hP : Module.finrank ℚ P ≤ 3)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : L.det = 1) (c : Fin 4 → ℝ) :
    let M := realRestrictionCoordinates4 P hP L
    let hf := realRestrictionCoordinates4_span P hP L hL
    let E := selectedIndex4 M c hf
    StrictMono E ∧ ∀ k : Fin (Module.finrank ℚ P),
      Module.finrank ℝ (Submodule.span ℝ (M193LiteralRestrictedGreedyRows4.rowPrefix4 (sortedRows4 M c) ((E k).val+1))) = k.val+1 ∧
      ∀ i : Fin 4, i < E k → Module.finrank ℝ (Submodule.span ℝ
        (M193LiteralRestrictedGreedyRows4.rowPrefix4 (sortedRows4 M c) (i.val+1))) ≤ k.val := by
  refine ⟨(selectedIndex4 _ c _).strictMono,?_⟩
  intro k
  exact M193LiteralRestrictedGreedyRanks4.greedyIndex4_first_rank_increase _
    (sortedRows4_span _ c (realRestrictionCoordinates4_span P hP L hL))
    (Module.finrank ℚ P) (by simp) k

end
end CompoundFeasibility.M193LiteralRestrictedOpposite4

open scoped BigOperators Classical Matrix
namespace CompoundFeasibility.M193LiteralNonrothOppositeGrowth4
open Exterior3 OriginalLastDual4 OriginalFlagAssembly4 BoundedWeights4 OriginalAttainmentFlag4 OriginalAttainmentTransport4 NonrothAttainmentFlag4 MinimaPower4 RestrictedGrowth4 NonrothVolumeGrowth4 M193LiteralRestrictedOpposite4
noncomputable section

def selectedOppositeGrowth4 (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (h₂ : A₂.det = 1) (h₃ : A₃.det = 1) (hL : L.det = 1) (c₀ c₂ c₃ : Fin 4 → ℝ)
    (epsilon delta c4 C4 B : ℝ) (U V : Set ℝ) (j : Fin 3) (hQV : ∀ Q ∈ V, 1 < Q) : Prop :=
    ∃ (N : ℕ) (hN : 1 ≤ N),
      (∀ i, |c₀ i| ≤ (N : ℝ) ∧ (-(N : ℝ) ≤ c₂ i ∧ c₂ i ≤ 0) ∧ (-(N : ℝ) ≤ c₃ i ∧ c₃ i ≤ 0)) ∧
      (∀ i, |scaledWeights4 N c₀ i| ≤ 1) ∧
      (∀ i, -1 ≤ scaledWeights4 N c₂ i ∧ scaledWeights4 N c₂ i ≤ 0) ∧
      (∀ i, -1 ≤ scaledWeights4 N c₃ i ∧ scaledWeights4 N c₃ i ≤ 0) ∧
      (∑ i, (scaledWeights4 N c₀ i+scaledWeights4 N c₂ i+scaledWeights4 N c₃ i) = 0) ∧
      exactNormalization4 N hN A₂ A₃ L (sourceUnit42 L hL) c₀ c₂ c₃ ∧
      0 < delta/(N : ℝ) ∧
      (∀ Q ∈ V, Q^(-delta) = (Q^N)^(-(delta/(N : ℝ)))) ∧
      ¬ BddAbove (powerImage4 N V) ∧
      ∃ hWR : ∀ R ∈ powerImage4 N V, 1 < R,
        (∀ (R : ℝ) (hR : R ∈ powerImage4 N V),
          sourceMinima4 A₂ A₃ L (sourceUnit42 L hL) R (hWR R hR)
            (scaledWeights4 N c₀) (scaledWeights4 N c₂) (scaledWeights4 N c₃) j.castSucc <
          sourceMinima4 A₂ A₃ L (sourceUnit42 L hL) R (hWR R hR)
            (scaledWeights4 N c₀) (scaledWeights4 N c₂) (scaledWeights4 N c₃) j.succ*R^(-(delta/(N : ℝ)))) ∧
        ∃ (Wfixed : Set ℝ) (hWsub : Wfixed ⊆ powerImage4 N V), ¬ BddAbove Wfixed ∧
          ∃ P : Submodule ℚ (Fin 4 → ℚ), Module.finrank ℚ P = j.val+1 ∧
            ∃ hPbounds : 1 ≤ Module.finrank ℚ P ∧ Module.finrank ℚ P ≤ 3, P ≠ ⊤ ∧
            ∃ v : (r : Wfixed) → Fin 4 → originalSourceGroup4 A₂ A₃ r.val (scaledWeights4 N c₂) (scaledWeights4 N c₃),
              (∀ r : Wfixed, P = originalFirstFlag4 j.succ (fun i => (v r i : Fin 4 → ℤ))) ∧
              (∀ r : Wfixed, ambientFrame4 A₂ A₃ L (sourceUnit42 L hL) r.val (hWR r.val (hWsub r.property))
                (scaledWeights4 N c₀) (scaledWeights4 N c₂) (scaledWeights4 N c₃) (v r)) ∧
              originalPreimage4 N V Wfixed ⊆ V ∧ ¬ BddAbove (originalPreimage4 N V Wfixed) ∧
              ∃ u : (q : originalPreimage4 N V Wfixed) → Fin 4 → originalSourceGroup4 A₂ A₃ q.val c₂ c₃,
                (∀ q i, (u q i : Fin 4 → ℤ) = (v ⟨q.val^N,q.property.2⟩ i : Fin 4 → ℤ)) ∧
                (∀ q, P = originalFirstFlag4 j.succ (fun i => (u q i : Fin 4 → ℤ))) ∧
                (∀ q : originalPreimage4 N V Wfixed, ambientFrame4 A₂ A₃ L (sourceUnit42 L hL) q.val (hQV q.val q.property.1)
                  c₀ c₂ c₃ (u q)) ∧
                (∀ (q : originalPreimage4 N V Wfixed) (k : Fin (Module.finrank ℚ P)),
                  RestrictedGeometry4.restrictedMinima4 P A₂ A₃ L (sourceUnit42 L hL) q.val
                    (hQV q.val q.property.1) c₀ c₂ c₃ k =
                  sourceMinima4 A₂ A₃ L (sourceUnit42 L hL) q.val (hQV q.val q.property.1) c₀ c₂ c₃
                    (RestrictedGeometry4.ambientPrefixIndex4 P hPbounds.2 k)) ∧
                originalPreimage4 N V Wfixed ⊆ U ∧
                (∀ q : originalPreimage4 N V Wfixed,
                  1 < q.val ∧ B < q.val ∧
                  sourceMinima4 A₂ A₃ L (sourceUnit42 L hL) q.val (hQV q.val q.property.1) c₀ c₂ c₃ j.castSucc <
                    sourceMinima4 A₂ A₃ L (sourceUnit42 L hL) q.val (hQV q.val q.property.1) c₀ c₂ c₃ j.succ*q.val^(-delta) ∧
                  c4 ≤ (∏ i : Fin 4, sourceMinima4 A₂ A₃ L (sourceUnit42 L hL) q.val (hQV q.val q.property.1) c₀ c₂ c₃ i) ∧
                  (∏ i : Fin 4, sourceMinima4 A₂ A₃ L (sourceUnit42 L hL) q.val (hQV q.val q.property.1) c₀ c₂ c₃ i) ≤ C4) ∧
                (∀ Q ∈ originalPreimage4 N V Wfixed, ∃ hQ : 1 < Q, ∃ x : Fin 4 → ℤ,
                  OriginalVariableGap4.originalSourceSolution4 A₂ A₃ L c₀ c₂ c₃ Q epsilon x ∧
                  x ∈ originalSourceGroup4 A₂ A₃ Q c₂ c₃ ∧
                  coordinateGauge4 (originalCoordinates4 L (sourceUnit42 L hL) Q hQ c₀) (integerReal x) ≤ Q^(-epsilon) ∧
                  sourceMinima4 A₂ A₃ L (sourceUnit42 L hL) Q hQ c₀ c₂ c₃ 0 < Q^(-(epsilon/2))) ∧
                0 < decayExponent4 j delta ∧ 0 < growthConstant4 j C4 ∧
                (∀ q : originalPreimage4 N V Wfixed,
                  quantitativeOriginalPoint4 P hPbounds.2 j A₂ A₃ L (sourceUnit42 L hL)
                    q.val (hQV q.val q.property.1) c₀ c₂ c₃ delta C4) ∧
                ∃ cSelected K : ℝ,
                  cSelected = M193LiteralSelectedRestriction4.sourceSelectedExponent4 P hPbounds.2 A₂ A₃ L h₂ h₃ hL c₀ c₂ c₃ ∧
                  0 < K ∧ ∀ q : originalPreimage4 N V Wfixed,
                    oppositePoint4 P hPbounds.2 A₂ A₃ L h₂ h₃ hL c₀ c₂ c₃ q.val K ∧
                    growthConstant4 j C4 * q.val^(decayExponent4 j delta) ≤
                      (RestrictedGeometry4.restrictedMeasure4 P).real (RestrictedGeometry4.restrictedBody4 P L q.val c₀) /
                        ZLattice.covolume (RestrictedGeometry4.restrictedLattice4 P A₂ A₃ q.val c₂ c₃)
                          (RestrictedGeometry4.restrictedMeasure4 P) ∧
                    (RestrictedGeometry4.restrictedMeasure4 P).real (RestrictedGeometry4.restrictedBody4 P L q.val c₀) /
                      ZLattice.covolume (RestrictedGeometry4.restrictedLattice4 P A₂ A₃ q.val c₂ c₃)
                        (RestrictedGeometry4.restrictedMeasure4 P) ≤ K*q.val^cSelected

theorem source_restricted_opposite_growth4 (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (h₂ : A₂.det = 1) (h₃ : A₃.det = 1) (hL : L.det = 1)
    (hAlg : ∀ i j, IsAlgebraic ℚ (L i j))
    (c₀ c₂ c₃ : Fin 4 → ℝ) (hc₂ : ∀ i, c₂ i ≤ 0) (hc₃ : ∀ i, c₃ i ≤ 0)
    (hb : ∑ i, (c₀ i+c₂ i+c₃ i) = 0)
    (hn : ¬ OriginalVariableGap4.originalRothProperty4 A₂ A₃ L c₀ c₂ c₃) :
    ∃ epsilon deltaGap c4 C4 B : ℝ, ∃ U V : Set ℝ, ∃ j : Fin 3,
      0 < epsilon ∧ deltaGap = (epsilon/2)/4 ∧ 0 < deltaGap ∧
      0 < c4 ∧ 0 < C4 ∧ 1 < B ∧
      U = {Q : ℝ | ∃ x : Fin 4 → ℤ,
        OriginalVariableGap4.originalSourceSolution4 A₂ A₃ L c₀ c₂ c₃ Q epsilon x} ∧
      ¬ BddAbove U ∧
      (∀ Q ∈ U, ∃ hQ : 1 < Q, ∃ x : Fin 4 → ℤ,
        OriginalVariableGap4.originalSourceSolution4 A₂ A₃ L c₀ c₂ c₃ Q epsilon x ∧
        x ∈ originalSourceGroup4 A₂ A₃ Q c₂ c₃ ∧
        coordinateGauge4 (originalCoordinates4 L (sourceUnit42 L hL) Q hQ c₀) (integerReal x) ≤ Q^(-epsilon) ∧
        sourceMinima4 A₂ A₃ L (sourceUnit42 L hL) Q hQ c₀ c₂ c₃ 0 < Q^(-(epsilon/2))) ∧
      (∀ (Q : ℝ) (hQ : 1 < Q),
        c4 ≤ (∏ i : Fin 4, sourceMinima4 A₂ A₃ L (sourceUnit42 L hL) Q hQ c₀ c₂ c₃ i) ∧
        (∏ i : Fin 4, sourceMinima4 A₂ A₃ L (sourceUnit42 L hL) Q hQ c₀ c₂ c₃ i) ≤ C4) ∧
      V ⊆ U ∧ ¬ BddAbove V ∧
      ∃ hQV : ∀ Q ∈ V, 1 < Q,
        (∀ (Q : ℝ) (hq : Q ∈ V), B < Q ∧
          sourceMinima4 A₂ A₃ L (sourceUnit42 L hL) Q (hQV Q hq) c₀ c₂ c₃ j.castSucc <
          sourceMinima4 A₂ A₃ L (sourceUnit42 L hL) Q (hQV Q hq) c₀ c₂ c₃ j.succ*Q^(-deltaGap)) ∧
        selectedOppositeGrowth4 A₂ A₃ L h₂ h₃ hL c₀ c₂ c₃ epsilon deltaGap c4 C4 B U V j hQV := by
  obtain ⟨epsilon,deltaGap,c4,C4,B,U,V,j,he,hdelta,hd,hc4,hC4,hB,hUeq,hU,hsol,hprod,hVU,hV,hQV,hpoints,hselected⟩ :=
    NonrothVolumeGrowth4.source_restricted_volume_growth4 A₂ A₃ L h₂ h₃ hL hAlg c₀ c₂ c₃ hc₂ hc₃ hb hn
  obtain ⟨N,hN,hc,ha₀,ha₂,ha₃,hab,hcert,hdn,hpower,himage,hWR,hgapn,
    Wfixed,hWsub,hW,P,hPdim,hPbounds,hproper,v,hv,hvAtt,hFinalV,hFinal,
    u,hvalues,hflag,hAtt,hEq,hFinalU,hFinalpoints,hFinalsol,hEta,hLowerConst,hQuant⟩ := hselected
  obtain ⟨K,hK,hUpper⟩ := source_restricted_opposite_uniform4 P hPbounds.2 A₂ A₃ L h₂ h₃ hL c₀ c₂ c₃ hc₂ hc₃
  refine ⟨epsilon,deltaGap,c4,C4,B,U,V,j,he,hdelta,hd,hc4,hC4,hB,hUeq,hU,hsol,hprod,hVU,hV,hQV,hpoints,?_⟩
  refine ⟨N,hN,hc,ha₀,ha₂,ha₃,hab,hcert,hdn,hpower,himage,hWR,hgapn,?_⟩
  refine ⟨Wfixed,hWsub,hW,P,hPdim,hPbounds,hproper,v,hv,hvAtt,hFinalV,hFinal,?_⟩
  refine ⟨u,hvalues,hflag,hAtt,hEq,hFinalU,hFinalpoints,hFinalsol,hEta,hLowerConst,hQuant,
    M193LiteralSelectedRestriction4.sourceSelectedExponent4 P hPbounds.2 A₂ A₃ L h₂ h₃ hL c₀ c₂ c₃,K,rfl,hK,?_⟩
  intro q
  have hpoint := hUpper q.val (hQV q.val q.property.1)
  have hcopy := hpoint
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,hOriginalUpper⟩ := hcopy
  obtain ⟨_,_,_,_,_,_,_,_,_,_,hOriginalLower⟩ := hQuant q
  exact ⟨hpoint,hOriginalLower,hOriginalUpper⟩

theorem selectedOppositeGrowth4_forget
    (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ)
    (h₂ : A₂.det = 1) (h₃ : A₃.det = 1) (hL : L.det = 1) (c₀ c₂ c₃ : Fin 4 → ℝ)
    (epsilon delta c4 C4 B : ℝ) (U V : Set ℝ) (j : Fin 3) (hQV : ∀ Q ∈ V, 1 < Q)
    (h : selectedOppositeGrowth4 A₂ A₃ L h₂ h₃ hL c₀ c₂ c₃ epsilon delta c4 C4 B U V j hQV) :
    NonrothVolumeGrowth4.selectedRestrictedGrowth4 A₂ A₃ L hL c₀ c₂ c₃ epsilon delta c4 C4 B U V j hQV := by
  obtain ⟨N,hN,hc,ha₀,ha₂,ha₃,hab,hcert,hdn,hpower,himage,hWR,hgapn,
    Wfixed,hWsub,hW,P,hPdim,hPbounds,hproper,v,hv,hvAtt,hFinalV,hFinal,
    u,hvalues,hflag,hAtt,hEq,hFinalU,hFinalpoints,hFinalsol,hEta,hLowerConst,hQuant,cSelected,K,hcSelected,hK,hNew⟩ := h
  refine ⟨N,hN,hc,ha₀,ha₂,ha₃,hab,hcert,hdn,hpower,himage,hWR,hgapn,?_⟩
  refine ⟨Wfixed,hWsub,hW,P,hPdim,hPbounds,hproper,v,hv,hvAtt,hFinalV,hFinal,?_⟩
  exact ⟨u,hvalues,hflag,hAtt,hEq,hFinalU,hFinalpoints,hFinalsol,hEta,hLowerConst,hQuant⟩

end
end CompoundFeasibility.M193LiteralNonrothOppositeGrowth4

#check CompoundFeasibility.M193LiteralRestrictedSelectedIndex4.selected_integer_two_index_bound
#print axioms CompoundFeasibility.M193LiteralRestrictedSelectedIndex4.selected_integer_two_index_bound

#check CompoundFeasibility.M193LiteralRestrictedSelectedIndex4.selected_rational_index_lower4
#print axioms CompoundFeasibility.M193LiteralRestrictedSelectedIndex4.selected_rational_index_lower4

#check CompoundFeasibility.M193LiteralRestrictedWeightOrder4.weightOrder4
#print axioms CompoundFeasibility.M193LiteralRestrictedWeightOrder4.weightOrder4

#check CompoundFeasibility.M193LiteralRestrictedWeightOrder4.permutedRows4
#print axioms CompoundFeasibility.M193LiteralRestrictedWeightOrder4.permutedRows4

#check CompoundFeasibility.M193LiteralRestrictedWeightOrder4.weightOrder4_bijective
#print axioms CompoundFeasibility.M193LiteralRestrictedWeightOrder4.weightOrder4_bijective

#check CompoundFeasibility.M193LiteralRestrictedWeightOrder4.weightOrder4_monotone
#print axioms CompoundFeasibility.M193LiteralRestrictedWeightOrder4.weightOrder4_monotone

#check CompoundFeasibility.M193LiteralRestrictedWeightOrder4.weightOrder4_adjacent
#print axioms CompoundFeasibility.M193LiteralRestrictedWeightOrder4.weightOrder4_adjacent

#check CompoundFeasibility.M193LiteralRestrictedWeightOrder4.weightOrder4_forall_pair
#print axioms CompoundFeasibility.M193LiteralRestrictedWeightOrder4.weightOrder4_forall_pair

#check CompoundFeasibility.M193LiteralRestrictedWeightOrder4.weightOrder4_ties
#print axioms CompoundFeasibility.M193LiteralRestrictedWeightOrder4.weightOrder4_ties

#check CompoundFeasibility.M193LiteralRestrictedWeightOrder4.permutedRows4_mulVec
#print axioms CompoundFeasibility.M193LiteralRestrictedWeightOrder4.permutedRows4_mulVec

#check CompoundFeasibility.M193LiteralRestrictedWeightOrder4.originalBody4_weightOrder
#print axioms CompoundFeasibility.M193LiteralRestrictedWeightOrder4.originalBody4_weightOrder

#check CompoundFeasibility.M193LiteralRestrictedWeightOrder4.lattice4_weightOrder
#print axioms CompoundFeasibility.M193LiteralRestrictedWeightOrder4.lattice4_weightOrder

#check CompoundFeasibility.M193LiteralRestrictedWeightOrder4.originalSourceGroup4_weightOrder
#print axioms CompoundFeasibility.M193LiteralRestrictedWeightOrder4.originalSourceGroup4_weightOrder

#check CompoundFeasibility.M193LiteralRestrictedWeightOrder4.restrictedBody4_weightOrder
#print axioms CompoundFeasibility.M193LiteralRestrictedWeightOrder4.restrictedBody4_weightOrder

#check CompoundFeasibility.M193LiteralRestrictedWeightOrder4.restrictedLattice4_weightOrder
#print axioms CompoundFeasibility.M193LiteralRestrictedWeightOrder4.restrictedLattice4_weightOrder

#check CompoundFeasibility.M193LiteralRestrictedRows4.rowCoordinates4
#print axioms CompoundFeasibility.M193LiteralRestrictedRows4.rowCoordinates4

#check CompoundFeasibility.M193LiteralRestrictedRows4.rowCoordinates4_span
#print axioms CompoundFeasibility.M193LiteralRestrictedRows4.rowCoordinates4_span

#check CompoundFeasibility.M193LiteralRestrictedRows4.rationalRowCoordinates4
#print axioms CompoundFeasibility.M193LiteralRestrictedRows4.rationalRowCoordinates4

#check CompoundFeasibility.M193LiteralRestrictedRows4.realRowCoordinates4
#print axioms CompoundFeasibility.M193LiteralRestrictedRows4.realRowCoordinates4

#check CompoundFeasibility.M193LiteralRestrictedRows4.rationalRowCoordinates4_span
#print axioms CompoundFeasibility.M193LiteralRestrictedRows4.rationalRowCoordinates4_span

#check CompoundFeasibility.M193LiteralRestrictedRows4.realRowCoordinates4_span
#print axioms CompoundFeasibility.M193LiteralRestrictedRows4.realRowCoordinates4_span

#check CompoundFeasibility.M193LiteralRestrictedGreedyRows4.rowPrefix4
#print axioms CompoundFeasibility.M193LiteralRestrictedGreedyRows4.rowPrefix4

#check CompoundFeasibility.M193LiteralRestrictedGreedyRows4.greedyPivot4
#print axioms CompoundFeasibility.M193LiteralRestrictedGreedyRows4.greedyPivot4

#check CompoundFeasibility.M193LiteralRestrictedGreedyRows4.greedyPrefix4
#print axioms CompoundFeasibility.M193LiteralRestrictedGreedyRows4.greedyPrefix4

#check CompoundFeasibility.M193LiteralRestrictedGreedyRows4.rowPrefix4_succ
#print axioms CompoundFeasibility.M193LiteralRestrictedGreedyRows4.rowPrefix4_succ

#check CompoundFeasibility.M193LiteralRestrictedGreedyRows4.greedyPrefix4_succ
#print axioms CompoundFeasibility.M193LiteralRestrictedGreedyRows4.greedyPrefix4_succ

#check CompoundFeasibility.M193LiteralRestrictedGreedyRows4.greedyPrefix4_independent_span
#print axioms CompoundFeasibility.M193LiteralRestrictedGreedyRows4.greedyPrefix4_independent_span

#check CompoundFeasibility.M193LiteralRestrictedGreedyRows4.greedyFinset4
#print axioms CompoundFeasibility.M193LiteralRestrictedGreedyRows4.greedyFinset4

#check CompoundFeasibility.M193LiteralRestrictedGreedyRows4.greedyFinset4_eq_prefix
#print axioms CompoundFeasibility.M193LiteralRestrictedGreedyRows4.greedyFinset4_eq_prefix

#check CompoundFeasibility.M193LiteralRestrictedGreedyRows4.greedyFinset4_independent_span
#print axioms CompoundFeasibility.M193LiteralRestrictedGreedyRows4.greedyFinset4_independent_span

#check CompoundFeasibility.M193LiteralRestrictedGreedyRows4.greedyFinset4_card
#print axioms CompoundFeasibility.M193LiteralRestrictedGreedyRows4.greedyFinset4_card

#check CompoundFeasibility.M193LiteralRestrictedGreedyRows4.greedyIndex4
#print axioms CompoundFeasibility.M193LiteralRestrictedGreedyRows4.greedyIndex4

#check CompoundFeasibility.M193LiteralRestrictedGreedyRows4.greedyIndex4_pivot
#print axioms CompoundFeasibility.M193LiteralRestrictedGreedyRows4.greedyIndex4_pivot

#check CompoundFeasibility.M193LiteralRestrictedGreedyRows4.greedyIndex4_independent
#print axioms CompoundFeasibility.M193LiteralRestrictedGreedyRows4.greedyIndex4_independent

#check CompoundFeasibility.M193LiteralSelectedRestriction4.sortedRows4
#print axioms CompoundFeasibility.M193LiteralSelectedRestriction4.sortedRows4

#check CompoundFeasibility.M193LiteralSelectedRestriction4.sortedRows4_span
#print axioms CompoundFeasibility.M193LiteralSelectedRestriction4.sortedRows4_span

#check CompoundFeasibility.M193LiteralSelectedRestriction4.selectedIndex4
#print axioms CompoundFeasibility.M193LiteralSelectedRestriction4.selectedIndex4

#check CompoundFeasibility.M193LiteralSelectedRestriction4.selectedMatrix4
#print axioms CompoundFeasibility.M193LiteralSelectedRestriction4.selectedMatrix4

#check CompoundFeasibility.M193LiteralSelectedRestriction4.selectedMatrix4_independent
#print axioms CompoundFeasibility.M193LiteralSelectedRestriction4.selectedMatrix4_independent

#check CompoundFeasibility.M193LiteralSelectedRestriction4.selectedMatrix4_det_ne_zero
#print axioms CompoundFeasibility.M193LiteralSelectedRestriction4.selectedMatrix4_det_ne_zero

#check CompoundFeasibility.M193LiteralSelectedRestriction4.realRestrictionBasis4
#print axioms CompoundFeasibility.M193LiteralSelectedRestriction4.realRestrictionBasis4

#check CompoundFeasibility.M193LiteralSelectedRestriction4.realRestrictionCoordinates4
#print axioms CompoundFeasibility.M193LiteralSelectedRestriction4.realRestrictionCoordinates4

#check CompoundFeasibility.M193LiteralSelectedRestriction4.realRestrictionCoordinates4_span
#print axioms CompoundFeasibility.M193LiteralSelectedRestriction4.realRestrictionCoordinates4_span

#check CompoundFeasibility.M193LiteralSelectedRestriction4.sourceSelectedExponent4
#print axioms CompoundFeasibility.M193LiteralSelectedRestriction4.sourceSelectedExponent4

#check CompoundFeasibility.M193LiteralRestrictedGreedyRanks4.greedyIndex4_prefix_set
#print axioms CompoundFeasibility.M193LiteralRestrictedGreedyRanks4.greedyIndex4_prefix_set

#check CompoundFeasibility.M193LiteralRestrictedGreedyRanks4.greedyIndex4_prefix_rank
#print axioms CompoundFeasibility.M193LiteralRestrictedGreedyRanks4.greedyIndex4_prefix_rank

#check CompoundFeasibility.M193LiteralRestrictedGreedyRanks4.greedyIndex4_first_rank_increase
#print axioms CompoundFeasibility.M193LiteralRestrictedGreedyRanks4.greedyIndex4_first_rank_increase

#check CompoundFeasibility.M193LiteralRestrictedRelaxed4.relaxedBody4
#print axioms CompoundFeasibility.M193LiteralRestrictedRelaxed4.relaxedBody4

#check CompoundFeasibility.M193LiteralRestrictedRelaxed4.selectedLocalGroup4
#print axioms CompoundFeasibility.M193LiteralRestrictedRelaxed4.selectedLocalGroup4

#check CompoundFeasibility.M193LiteralRestrictedRelaxed4.selectedSourceGroup4
#print axioms CompoundFeasibility.M193LiteralRestrictedRelaxed4.selectedSourceGroup4

#check CompoundFeasibility.M193LiteralRestrictedRelaxed4.relaxedLattice4
#print axioms CompoundFeasibility.M193LiteralRestrictedRelaxed4.relaxedLattice4

#check CompoundFeasibility.M193LiteralRestrictedRelaxed4.restrictedBody4_subset_relaxed
#print axioms CompoundFeasibility.M193LiteralRestrictedRelaxed4.restrictedBody4_subset_relaxed

#check CompoundFeasibility.M193LiteralRestrictedRelaxed4.lattice4_le_selectedLocalGroup4
#print axioms CompoundFeasibility.M193LiteralRestrictedRelaxed4.lattice4_le_selectedLocalGroup4

#check CompoundFeasibility.M193LiteralRestrictedRelaxed4.originalSourceGroup4_le_selected
#print axioms CompoundFeasibility.M193LiteralRestrictedRelaxed4.originalSourceGroup4_le_selected

#check CompoundFeasibility.M193LiteralRestrictedRelaxed4.restrictedLattice4_le_relaxed
#print axioms CompoundFeasibility.M193LiteralRestrictedRelaxed4.restrictedLattice4_le_relaxed

#check CompoundFeasibility.M193LiteralRestrictedRelaxed4.relaxedLattice4_discrete
#print axioms CompoundFeasibility.M193LiteralRestrictedRelaxed4.relaxedLattice4_discrete

#check CompoundFeasibility.M193LiteralRestrictedRelaxed4.relaxedLattice4_isZLattice
#print axioms CompoundFeasibility.M193LiteralRestrictedRelaxed4.relaxedLattice4_isZLattice

#check CompoundFeasibility.M193LiteralRestrictedRelaxed4.relaxedLattice4_rank
#print axioms CompoundFeasibility.M193LiteralRestrictedRelaxed4.relaxedLattice4_rank

#check CompoundFeasibility.M193LiteralRestrictedRelaxed4.relaxedLattice4_covolume_pos
#print axioms CompoundFeasibility.M193LiteralRestrictedRelaxed4.relaxedLattice4_covolume_pos

#check CompoundFeasibility.M193LiteralRestrictedCovolumeOrder4.covolume_antitone4
#print axioms CompoundFeasibility.M193LiteralRestrictedCovolumeOrder4.covolume_antitone4

#check CompoundFeasibility.M193LiteralRestrictedRationalMembership4.rationalRealSpan4_mem_rational
#print axioms CompoundFeasibility.M193LiteralRestrictedRationalMembership4.rationalRealSpan4_mem_rational

#check CompoundFeasibility.M193LiteralRestrictedIntegerCoordinates4.baseLattice4
#print axioms CompoundFeasibility.M193LiteralRestrictedIntegerCoordinates4.baseLattice4

#check CompoundFeasibility.M193LiteralRestrictedIntegerCoordinates4.baseLattice4_mem
#print axioms CompoundFeasibility.M193LiteralRestrictedIntegerCoordinates4.baseLattice4_mem

#check CompoundFeasibility.M193LiteralRestrictedIntegerCoordinates4.relaxedLattice4_le_base
#print axioms CompoundFeasibility.M193LiteralRestrictedIntegerCoordinates4.relaxedLattice4_le_base

#check CompoundFeasibility.M193LiteralRestrictedIntegerCoordinates4.baseIntegerBasis4
#print axioms CompoundFeasibility.M193LiteralRestrictedIntegerCoordinates4.baseIntegerBasis4

#check CompoundFeasibility.M193LiteralRestrictedIntegerCoordinates4.integerCoordinateMap4
#print axioms CompoundFeasibility.M193LiteralRestrictedIntegerCoordinates4.integerCoordinateMap4

#check CompoundFeasibility.M193LiteralRestrictedIntegerCoordinates4.integerCoordinateMap4_injective
#print axioms CompoundFeasibility.M193LiteralRestrictedIntegerCoordinates4.integerCoordinateMap4_injective

#check CompoundFeasibility.M193LiteralRestrictedIntegerCoordinates4.integerCoordinateMap4_equivFun
#print axioms CompoundFeasibility.M193LiteralRestrictedIntegerCoordinates4.integerCoordinateMap4_equivFun

#check CompoundFeasibility.M193LiteralRestrictedIntegerCoordinates4.relaxedIntegerGroup4
#print axioms CompoundFeasibility.M193LiteralRestrictedIntegerCoordinates4.relaxedIntegerGroup4

#check CompoundFeasibility.M193LiteralRestrictedIntegerCoordinates4.relaxedIntegerEquiv4
#print axioms CompoundFeasibility.M193LiteralRestrictedIntegerCoordinates4.relaxedIntegerEquiv4

#check CompoundFeasibility.M193LiteralRestrictedIntegerCoordinates4.relaxedIntegerGroup4_rank
#print axioms CompoundFeasibility.M193LiteralRestrictedIntegerCoordinates4.relaxedIntegerGroup4_rank

#check CompoundFeasibility.M193LiteralRestrictedIntegerCoordinates4.baseIntegerVector4
#print axioms CompoundFeasibility.M193LiteralRestrictedIntegerCoordinates4.baseIntegerVector4

#check CompoundFeasibility.M193LiteralRestrictedIntegerCoordinates4.baseIntegerVector4_values
#print axioms CompoundFeasibility.M193LiteralRestrictedIntegerCoordinates4.baseIntegerVector4_values

#check CompoundFeasibility.M193LiteralRestrictedIntegerCoordinates4.baseIntegerVector4_rational_mem
#print axioms CompoundFeasibility.M193LiteralRestrictedIntegerCoordinates4.baseIntegerVector4_rational_mem

#check CompoundFeasibility.M193LiteralRestrictedIntegerCoordinates4.baseRationalVector4
#print axioms CompoundFeasibility.M193LiteralRestrictedIntegerCoordinates4.baseRationalVector4

#check CompoundFeasibility.M193LiteralRestrictedIntegerCoordinates4.baseRationalVector4_independent
#print axioms CompoundFeasibility.M193LiteralRestrictedIntegerCoordinates4.baseRationalVector4_independent

#check CompoundFeasibility.M193LiteralRestrictedIntegerCoordinates4.baseRationalBasis4
#print axioms CompoundFeasibility.M193LiteralRestrictedIntegerCoordinates4.baseRationalBasis4

#check CompoundFeasibility.M193LiteralRestrictedSelectedBasis4.rowCoordinates4_change_basis
#print axioms CompoundFeasibility.M193LiteralRestrictedSelectedBasis4.rowCoordinates4_change_basis

#check CompoundFeasibility.M193LiteralRestrictedSelectedBasis4.selected_basis_matrix_det4
#print axioms CompoundFeasibility.M193LiteralRestrictedSelectedBasis4.selected_basis_matrix_det4

#check CompoundFeasibility.M193LiteralRestrictedSelectedBasis4.finiteSelectedMatrix4
#print axioms CompoundFeasibility.M193LiteralRestrictedSelectedBasis4.finiteSelectedMatrix4

#check CompoundFeasibility.M193LiteralRestrictedSelectedBasis4.finiteSelectedMatrix4_det_ne_zero
#print axioms CompoundFeasibility.M193LiteralRestrictedSelectedBasis4.finiteSelectedMatrix4_det_ne_zero

#check CompoundFeasibility.M193LiteralRestrictedFiniteCoordinates4.integerCoordinateMap4_integerReal
#print axioms CompoundFeasibility.M193LiteralRestrictedFiniteCoordinates4.integerCoordinateMap4_integerReal

#check CompoundFeasibility.M193LiteralRestrictedFiniteCoordinates4.selected_local_coordinates4
#print axioms CompoundFeasibility.M193LiteralRestrictedFiniteCoordinates4.selected_local_coordinates4

#check CompoundFeasibility.M193LiteralRestrictedCoordinateCovolume4.relaxedLattice4_covolume_index
#print axioms CompoundFeasibility.M193LiteralRestrictedCoordinateCovolume4.relaxedLattice4_covolume_index

#check CompoundFeasibility.M193LiteralRestrictedFiniteBound4.finiteSelection4
#print axioms CompoundFeasibility.M193LiteralRestrictedFiniteBound4.finiteSelection4

#check CompoundFeasibility.M193LiteralRestrictedFiniteBound4.selected_prime_powers_lower4
#print axioms CompoundFeasibility.M193LiteralRestrictedFiniteBound4.selected_prime_powers_lower4

#check CompoundFeasibility.M193LiteralRestrictedFiniteBound4.source_finite_inverse_covolume4
#print axioms CompoundFeasibility.M193LiteralRestrictedFiniteBound4.source_finite_inverse_covolume4

#check CompoundFeasibility.M193LiteralSelectedBoxVolume4.weightedBox4
#print axioms CompoundFeasibility.M193LiteralSelectedBoxVolume4.weightedBox4

#check CompoundFeasibility.M193LiteralSelectedBoxVolume4.weightedBox4_compact_convex
#print axioms CompoundFeasibility.M193LiteralSelectedBoxVolume4.weightedBox4_compact_convex

#check CompoundFeasibility.M193LiteralSelectedBoxVolume4.weightedBox4_volume
#print axioms CompoundFeasibility.M193LiteralSelectedBoxVolume4.weightedBox4_volume

#check CompoundFeasibility.M193LiteralRestrictedRealBody4.baseRealBasis4
#print axioms CompoundFeasibility.M193LiteralRestrictedRealBody4.baseRealBasis4

#check CompoundFeasibility.M193LiteralRestrictedRealBody4.realSelection4
#print axioms CompoundFeasibility.M193LiteralRestrictedRealBody4.realSelection4

#check CompoundFeasibility.M193LiteralRestrictedRealBody4.realSelectedMatrix4
#print axioms CompoundFeasibility.M193LiteralRestrictedRealBody4.realSelectedMatrix4

#check CompoundFeasibility.M193LiteralRestrictedRealBody4.realSelectedMatrix4_det_ne_zero
#print axioms CompoundFeasibility.M193LiteralRestrictedRealBody4.realSelectedMatrix4_det_ne_zero

#check CompoundFeasibility.M193LiteralRestrictedRealBody4.selectedRealEquiv4
#print axioms CompoundFeasibility.M193LiteralRestrictedRealBody4.selectedRealEquiv4

#check CompoundFeasibility.M193LiteralRestrictedRealBody4.rowCoordinates4_mulVec_basis
#print axioms CompoundFeasibility.M193LiteralRestrictedRealBody4.rowCoordinates4_mulVec_basis

#check CompoundFeasibility.M193LiteralRestrictedRealBody4.relaxedBody4_coordinates
#print axioms CompoundFeasibility.M193LiteralRestrictedRealBody4.relaxedBody4_coordinates

#check CompoundFeasibility.M193LiteralRestrictedRealBody4.source_relaxed_body_geometry4
#print axioms CompoundFeasibility.M193LiteralRestrictedRealBody4.source_relaxed_body_geometry4

#check CompoundFeasibility.M193LiteralRestrictedRealBody4.source_uniform_real_volume4
#print axioms CompoundFeasibility.M193LiteralRestrictedRealBody4.source_uniform_real_volume4

#check CompoundFeasibility.M193LiteralRestrictedOpposite4.selectedLocalGroup4_rpow_spec
#print axioms CompoundFeasibility.M193LiteralRestrictedOpposite4.selectedLocalGroup4_rpow_spec

#check CompoundFeasibility.M193LiteralRestrictedOpposite4.oppositePoint4
#print axioms CompoundFeasibility.M193LiteralRestrictedOpposite4.oppositePoint4

#check CompoundFeasibility.M193LiteralRestrictedOpposite4.source_restricted_opposite_uniform4
#print axioms CompoundFeasibility.M193LiteralRestrictedOpposite4.source_restricted_opposite_uniform4

#check CompoundFeasibility.M193LiteralRestrictedOpposite4.source_finite_greedy_indices4
#print axioms CompoundFeasibility.M193LiteralRestrictedOpposite4.source_finite_greedy_indices4

#check CompoundFeasibility.M193LiteralRestrictedOpposite4.source_real_greedy_indices4
#print axioms CompoundFeasibility.M193LiteralRestrictedOpposite4.source_real_greedy_indices4

#check CompoundFeasibility.M193LiteralNonrothOppositeGrowth4.selectedOppositeGrowth4
#print axioms CompoundFeasibility.M193LiteralNonrothOppositeGrowth4.selectedOppositeGrowth4

#check CompoundFeasibility.M193LiteralNonrothOppositeGrowth4.source_restricted_opposite_growth4
#print axioms CompoundFeasibility.M193LiteralNonrothOppositeGrowth4.source_restricted_opposite_growth4

#check CompoundFeasibility.M193LiteralNonrothOppositeGrowth4.selectedOppositeGrowth4_forget
#print axioms CompoundFeasibility.M193LiteralNonrothOppositeGrowth4.selectedOppositeGrowth4_forget
