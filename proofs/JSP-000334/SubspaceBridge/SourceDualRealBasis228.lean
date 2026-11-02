import SubspaceBridge.SourceRealIndependence227
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceSecondMinimum228
open SourceDualGeometry219

theorem inverse_columns_independent228 (W : Matrix (Fin 10) (Fin 10) ℚ)
    (hW : IsUnit W) : LinearIndependent ℚ (fun j i => W⁻¹ i j) := by
  have hInv : IsUnit W⁻¹ := Matrix.isUnit_nonsing_inv_iff.mpr hW
  have hCols : LinearIndependent ℚ (fun j i => W⁻¹ i j) :=
    Matrix.linearIndependent_cols_iff_isUnit.mpr hInv
  exact hCols

theorem scaled_columns_family228 (W : Matrix (Fin 10) (Fin 10) ℚ) (t : ℚ) (ht : t ≠ 0) :
    ((fun _ : Fin 10 => Units.mk0 t ht) • (fun j : Fin 10 => fun i : Fin 10 => W⁻¹ i j)) =
      (fun j : Fin 10 => t • dualVector219 W j) := by
  funext j i
  simp only [Units.smul_def, Units.val_mk0, Pi.smul_apply', Pi.smul_apply, smul_eq_mul, dualVector219]

theorem rational_generators_independent228 (W : Matrix (Fin 10) (Fin 10) ℚ)
    (hW : IsUnit W) (t : ℚ) (ht : t ≠ 0) :
    LinearIndependent ℚ (fun j => t • dualVector219 W j) := by
  have h := (inverse_columns_independent228 W hW).units_smul (fun _ => Units.mk0 t ht)
  rw [scaled_columns_family228 W t ht] at h
  exact h

open SourceDualAnnihilation222 SourceSecondMinimum227

theorem cast_dual_family228 (W : Matrix (Fin 10) (Fin 10) ℚ) (t : ℚ) :
    (fun j i => ((t • dualVector219 W j) i : ℝ)) =
      (fun j => ratReal222 (t • dualVector219 W j)) := by
  funext j i
  simp only [ratReal222]

def rationalReal228 : (Fin 10 → ℚ) →ₗ[ℤ] (Fin 10 → ℝ) where
  toFun := ratReal222
  map_add' x y := by ext i; simp [ratReal222]
  map_smul' a x := by ext i; simp [ratReal222]

def dualRealGenerators228 (G : AddSubgroup (Fin 10 → ℤ)) (c : Basis (Fin 10) ℤ G)
    (j : Fin 10) : Fin 10 → ℝ :=
  ratReal222 ((G.index : ℚ) • dualVector219 (fun j i => ((c j : Fin 10 → ℤ) i : ℚ)) j)

theorem dualRealGenerators_independent228 (G : AddSubgroup (Fin 10 → ℤ))
    (c : Basis (Fin 10) ℤ G) (hD : G.index ≠ 0)
    (hc : LinearIndependent ℚ (fun j i => ((c j : Fin 10 → ℤ) i : ℚ))) :
    LinearIndependent ℝ (dualRealGenerators228 G c) := by
  let W : Matrix (Fin 10) (Fin 10) ℚ := fun j i => ((c j : Fin 10 → ℤ) i : ℚ)
  have hW : IsUnit W := Matrix.linearIndependent_rows_iff_isUnit.mp hc
  have ht : (G.index : ℚ) ≠ 0 := by exact_mod_cast hD
  have hq := rational_generators_independent228 W hW (G.index : ℚ) ht
  have hr := rational_real_independent227 _ hq
  rw [cast_dual_family228 W (G.index : ℚ)] at hr
  exact hr

def genuineDualRealBasis228 (G : AddSubgroup (Fin 10 → ℤ)) (c : Basis (Fin 10) ℤ G)
    (hD : G.index ≠ 0)
    (hc : LinearIndependent ℚ (fun j i => ((c j : Fin 10 → ℤ) i : ℚ))) :
    Basis (Fin 10) ℝ (Fin 10 → ℝ) :=
  basisOfPiSpaceOfLinearIndependent (dualRealGenerators_independent228 G c hD hc)

theorem genuineDualRealBasis_apply228 (G : AddSubgroup (Fin 10 → ℤ))
    (c : Basis (Fin 10) ℤ G) (hD : G.index ≠ 0)
    (hc : LinearIndependent ℚ (fun j i => ((c j : Fin 10 → ℤ) i : ℚ))) (j : Fin 10) :
    genuineDualRealBasis228 G c hD hc j = dualRealGenerators228 G c j :=
  congrFun (coe_basisOfPiSpaceOfLinearIndependent (dualRealGenerators_independent228 G c hD hc)) j

theorem genuineDualRealBasis_span228 (G : AddSubgroup (Fin 10 → ℤ))
    (c : Basis (Fin 10) ℤ G) (hD : G.index ≠ 0)
    (hc : LinearIndependent ℚ (fun j i => ((c j : Fin 10 → ℤ) i : ℚ))) :
    lattice10Span (genuineDualRealBasis228 G c hD hc) =
      (basisDualSpan219 G c).map rationalReal228 := by
  rw [basisDualSpan219, Submodule.map_span]
  change Submodule.span ℤ (Set.range (genuineDualRealBasis228 G c hD hc)) = _
  congr 1
  rw [← Set.range_comp']
  apply congrArg Set.range
  funext j
  exact genuineDualRealBasis_apply228 G c hD hc j

theorem genuineDualRealBasis_lattice228 (G : AddSubgroup (Fin 10 → ℤ))
    (c : Basis (Fin 10) ℤ G) (hD : G.index ≠ 0)
    (hc : LinearIndependent ℚ (fun j i => ((c j : Fin 10 → ℤ) i : ℚ))) :
    (lattice10Span (genuineDualRealBasis228 G c hD hc) : Set (Fin 10 → ℝ)) =
      ratReal222 '' scaledDual219 G := by
  rw [genuineDualRealBasis_span228, scaledDual_eq_basis219 G hD c hc]
  rfl

theorem original_dual_generators_independent228
    (A2 A3 : Matrix (Fin 10) (Fin 10) ℚ) (q : ℝ) (c2 c3 : Fin 10 → ℝ)
    (c : Basis (Fin 10) ℤ (originalSourceGroup10 A2 A3 q c2 c3)) :
    LinearIndependent ℝ (dualRealGenerators228 (originalSourceGroup10 A2 A3 q c2 c3) c) := by
  exact dualRealGenerators_independent228 _ c
    (Nat.ne_of_gt (sourceLattice10_index_pos A2 A3 _ _))
    (original_basis_independent220 A2 A3 q c2 c3 c)

def originalDualRealBasis228
    (A2 A3 : Matrix (Fin 10) (Fin 10) ℚ) (q : ℝ) (c2 c3 : Fin 10 → ℝ) :
    Basis (Fin 10) ℝ (Fin 10 → ℝ) :=
  let G := originalSourceGroup10 A2 A3 q c2 c3
  let c : Basis (Fin 10) ℤ G := (sourceLattice10_has_basis A2 A3
    (fun i => Nat.ceil (JSP000334.qThreshold 2 q (c2 i)))
    (fun i => Nat.ceil (JSP000334.qThreshold 3 q (c3 i)))).some
  genuineDualRealBasis228 G c (Nat.ne_of_gt (sourceLattice10_index_pos A2 A3 _ _))
    (original_basis_independent220 A2 A3 q c2 c3 c)

theorem originalDualRealBasis_lattice228
    (A2 A3 : Matrix (Fin 10) (Fin 10) ℚ) (q : ℝ) (c2 c3 : Fin 10 → ℝ) :
    (lattice10Span (originalDualRealBasis228 A2 A3 q c2 c3) : Set (Fin 10 → ℝ)) =
      ratReal222 '' scaledDual219 (originalSourceGroup10 A2 A3 q c2 c3) := by
  let G := originalSourceGroup10 A2 A3 q c2 c3
  let c : Basis (Fin 10) ℤ G := (sourceLattice10_has_basis A2 A3
    (fun i => Nat.ceil (JSP000334.qThreshold 2 q (c2 i)))
    (fun i => Nat.ceil (JSP000334.qThreshold 3 q (c3 i)))).some
  exact genuineDualRealBasis_lattice228 G c
    (Nat.ne_of_gt (sourceLattice10_index_pos A2 A3 _ _))
    (original_basis_independent220 A2 A3 q c2 c3 c)

end CompoundFeasibility.SourceSecondMinimum228
