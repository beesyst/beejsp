import SubspaceBridge.CofactorExteriorSquare3
open scoped BigOperators Matrix
namespace JSP000334
noncomputable section

theorem hodge_real_minor_bound3 (a b c d r s t u : ℝ)
    (hr : 0 ≤ r) (hs : 0 ≤ s) (ht : 0 ≤ t) (hu : 0 ≤ u)
    (ha : |a| ≤ r*t) (hb : |b| ≤ r*u) (hc : |c| ≤ s*t) (hd : |d| ≤ s*u) :
    |a*d-b*c| ≤ 2*r*s*t*u := by
  calc
    _ ≤ |a*d| + |b*c| := abs_sub _ _
    _ = |a| * |d| + |b| * |c| := by rw [abs_mul,abs_mul]
    _ ≤ (r*t)*(s*u)+(r*u)*(s*t) := add_le_add
      (mul_le_mul ha hd (abs_nonneg _) (mul_nonneg hr ht))
      (mul_le_mul hb hc (abs_nonneg _) (mul_nonneg hr hu))
    _ = _ := by ring

theorem hodgeWedge3_real_bound (x y t : Fin 3 → ℝ) (r s : ℝ)
    (hr : 0 ≤ r) (hs : 0 ≤ s) (ht : ∀ i, 0 ≤ t i)
    (hx : ∀ i, |x i| ≤ r*t i) (hy : ∀ i, |y i| ≤ s*t i) (i : Fin 3) :
    |hodgeWedge3 x y i| ≤ 2*r*s*t (i.succAbove 0)*t (i.succAbove 1) := by
  fin_cases i
  · simpa [hodgeWedge3,Fin.succAbove] using hodge_real_minor_bound3
      (x 1) (x 2) (y 1) (y 2) r s (t 1) (t 2) hr hs (ht 1) (ht 2)
        (hx 1) (hx 2) (hy 1) (hy 2)
  · change |hodgeWedge3 x y 1| ≤ 2*r*s*t 0*t 2
    have he : |hodgeWedge3 x y 1| = |x 0*y 2-x 2*y 0| := by
      simpa [hodgeWedge3] using abs_sub_comm (x 2*y 0) (x 0*y 2)
    rw [he]
    exact hodge_real_minor_bound3 (x 0) (x 2) (y 0) (y 2) r s (t 0) (t 2)
      hr hs (ht 0) (ht 2) (hx 0) (hx 2) (hy 0) (hy 2)
  · simpa [hodgeWedge3,Fin.succAbove] using hodge_real_minor_bound3
      (x 0) (x 1) (y 0) (y 1) r s (t 0) (t 1) hr hs (ht 0) (ht 1)
        (hx 0) (hx 1) (hy 0) (hy 1)

theorem cofactorRealMatrix3_adjugate (k : Fin 3) :
    (retainedRealMatrix3 k).adjugate.transpose = cofactorRealMatrix3 k := by
  unfold retainedRealMatrix3 cofactorRealMatrix3 cofactorIntegerMatrix3
  have h : ((retainedIntegerMatrix3 k).adjugate).map (Int.castRingHom ℝ) =
      ((retainedIntegerMatrix3 k).map (Int.castRingHom ℝ)).adjugate :=
    (Int.castRingHom ℝ).map_adjugate (retainedIntegerMatrix3 k)
  exact congrArg Matrix.transpose h.symm

theorem hodgeWedge3_source_gauge (k : Fin 3) (Q : ℝ) (hQ : 1 < Q)
    (c : Fin 3 → ℝ) (x y : IntegerTriple) :
    coordinateGauge3 (cofactorSourceCoordinates3 k (Q^2) (pairWeights3 c) (pairWeights3_Q_squared Q hQ))
      (integerTripleReal3 (hodgeWedge3 x y)) ≤
      2*coordinateGauge3 (qSourceCoordinates3 k Q c hQ) (integerTripleReal3 x)*
        coordinateGauge3 (qSourceCoordinates3 k Q c hQ) (integerTripleReal3 y) := by
  let r := coordinateGauge3 (qSourceCoordinates3 k Q c hQ) (integerTripleReal3 x)
  let s := coordinateGauge3 (qSourceCoordinates3 k Q c hQ) (integerTripleReal3 y)
  have hp : 0 < Q := lt_trans zero_lt_one hQ
  have hr : 0 ≤ r := norm_nonneg _
  have hs : 0 ≤ s := norm_nonneg _
  have hm := hodgeWedge3_matrix (retainedRealMatrix3 k) (integerTripleReal3 x) (integerTripleReal3 y)
  rw [cofactorRealMatrix3_adjugate] at hm
  have hw : hodgeWedge3 (integerTripleReal3 x) (integerTripleReal3 y) =
      integerTripleReal3 (hodgeWedge3 x y) := (hodgeWedge3_map (Int.castRingHom ℝ) x y).symm
  rw [hw] at hm
  apply (pi_norm_le_iff_of_nonempty _).mpr
  intro i
  change |(cofactorRealMatrix3 k *ᵥ integerTripleReal3 (hodgeWedge3 x y)) i /
    (Q^2) ^ pairWeights3 c i| ≤ 2*r*s
  rw [abs_div,abs_of_pos (Real.rpow_pos_of_pos (by positivity : 0 < Q^2) _),
    div_le_iff₀ (Real.rpow_pos_of_pos (by positivity : 0 < Q^2) _),
    pairWeights3_power Q hp,Real.rpow_add hp,← hm]
  have hh := hodgeWedge3_real_bound (retainedRealMatrix3 k *ᵥ integerTripleReal3 x)
    (retainedRealMatrix3 k *ᵥ integerTripleReal3 y) (fun i => Q^c i) r s hr hs
    (fun i => (Real.rpow_pos_of_pos hp _).le)
    (qSource_arch_bound k Q c hQ (integerTripleReal3 x))
    (qSource_arch_bound k Q c hQ (integerTripleReal3 y)) i
  simpa only [mul_assoc] using hh

theorem cofactor_pair_ceiling_bounds3 (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Nat.ceil (x+y) ≤ Nat.ceil x+Nat.ceil y ∧
      Nat.ceil x+Nat.ceil y ≤ Nat.ceil (x+y)+1 := by
  refine ⟨Nat.ceil_add_le x y,?_⟩
  have h1 := Nat.ceil_lt_add_one hx
  have h2 := Nat.ceil_lt_add_one hy
  have h3 := Nat.le_ceil (x+y)
  have h : (Nat.ceil x : ℝ)+(Nat.ceil y : ℝ) < (Nat.ceil (x+y) : ℝ)+2 := by linarith
  have hn : Nat.ceil x+Nat.ceil y < Nat.ceil (x+y)+2 := by exact_mod_cast h
  omega

theorem hodgeFrame3_original_first_line (u : Fin 3 → IntegerTriple)
    (hu : LinearIndependent ℝ (fun j => integerTripleReal3 (u j))) :
    Submodule.span ℚ {fun i => (u 0 i : ℚ)} =
      Submodule.span ℚ {dualFrameVector3 (hodgeFrame3 u) 2} := by
  have hwcast : (fun j => integerTripleReal3 (hodgeFrame3 u j)) =
      hodgeFrame3 (fun j => integerTripleReal3 (u j)) := hodgeFrame3_map (Int.castRingHom ℝ) u
  have hwr : LinearIndependent ℝ (fun j => integerTripleReal3 (hodgeFrame3 u j)) := by
    rw [hwcast]
    exact hodgeFrame3_independent _ hu
  have hwq := dualFrameMatrix3_rational_independent (hodgeFrame3 u) hwr
  have huq := dualFrameMatrix3_rational_independent u hu
  apply originalPlane_annihilator_line3 (hodgeFrame3 u) hwq (fun i => (u 0 i : ℚ)) (huq.ne_zero 0)
  · norm_num [originalPlanePairing3,hodgeFrame3,hodgeWedge3,Fin.sum_univ_three,
      Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]
    ring
  · norm_num [originalPlanePairing3,hodgeFrame3,hodgeWedge3,Fin.sum_univ_three,
      Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]
    ring

end
end JSP000334
