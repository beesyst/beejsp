import SubspaceBridge.OriginalPlaneTransport3
open scoped BigOperators
open JSP000334
namespace OriginalPlaneLiteral

noncomputable def lattice (k₂ k₃ : Fin 3) (Q : ℝ) (c₂ c₃ : Fin 3 → ℝ) : AddSubgroup IntegerTriple :=
  (primaryResidue3 (retainedIntegerMatrix3 k₂) 2 (fun i => Nat.ceil (-c₂ i * Real.log Q / Real.log 2))).ker ⊓
  (primaryResidue3 (retainedIntegerMatrix3 k₃) 3 (fun i => Nat.ceil (-c₃ i * Real.log Q / Real.log 3))).ker

noncomputable def minimum (G : AddSubgroup IntegerTriple) (e : RealTriple ≃ₗ[ℝ] RealTriple) (j : Fin 3) : ℝ :=
  sInf {r : ℝ | ∃ v : Fin (j.val + 1) → RealTriple, LinearIndependent ℝ v ∧
    (∀ i, v i ∈ G.toIntSubmodule.map integerTripleReal3) ∧ ∀ i, ‖e (v i)‖ ≤ r}

noncomputable def normal (w : Fin 3 → IntegerTriple) : Fin 3 → ℚ :=
  fun i => @Inv.inv (Matrix (Fin 3) (Fin 3) ℚ) Matrix.inv (fun j k => (w j k : ℚ)) i 2

theorem minimum_eq (G : AddSubgroup IntegerTriple) (B : Basis (Fin 3) ℝ RealTriple)
    (hB : lattice3 B = G.toIntSubmodule.map integerTripleReal3)
    (e : RealTriple ≃ₗ[ℝ] RealTriple) (j : Fin 3) : minimum G e j = successiveRadius3 B e j := by
  unfold minimum successiveRadius3
  rw [hB]
  rfl

theorem flag_eq (w : Fin 3 → RealTriple) : minimaFlag3 w 2 = Submodule.span ℝ {w 0,w 1} := by
  have hs : Set.range (fun i : Fin 2 => w (Fin.castLE (by decide) i)) = {w 0,w 1} := by
    ext x
    simp only [Set.mem_range,Set.mem_insert_iff,Set.mem_singleton_iff]
    constructor
    · rintro ⟨i,rfl⟩
      fin_cases i <;> simp
    · rintro (h | h)
      · exact ⟨0,h.symm⟩
      · exact ⟨1,h.symm⟩
  change Submodule.span ℝ (Set.range (fun i : Fin 2 => w (Fin.castLE (by decide) i))) = _
  rw [hs]

theorem separation_literal (l : Fin 3 → ℝ) (hl : ∀ i, 0 < l i)
    (Q delta : ℝ) (hQ : 0 < Q) (hp : (1 : ℝ) / 6 ≤ ∏ i, l i)
    (hg : l 1 < l 2 * Q ^ (-delta)) (hc : 3072 < Q ^ (2 * delta)) :
    let s := (l 0 * l 1 ^ 2)^((1:ℝ)/3) / l 1 * l 2
    s ^ (3 : ℕ) = (l 0 * l 1 * l 2) * (l 2 / l 1)^2 ∧
      Q ^ (2 * delta) / 6 < s ^ (3 : ℕ) ∧ 1 < s / 8 := by
  exact ⟨originalPlane_scaled_cube3 l hl,originalPlane_scaled_cube_gt3 l hl Q delta hQ hp hg,
    originalPlane_off_plane_margin3 l hl Q delta hQ hp hg hc⟩

theorem cutoff_literal (delta : ℝ) (hd : 0 < delta) :
    ∃ C : ℝ, ∀ Q : ℝ, C < Q → 3072 < Q ^ (2 * delta) := originalPlane_power_cutoff3 delta hd

theorem pairing_literal (w : Fin 3 → IntegerTriple)
    (hw : LinearIndependent ℝ (fun j => integerTripleReal3 (w j))) :
    normal w ≠ 0 ∧ ∀ j, (∑ k, (w j k : ℚ) * normal w k) = if j = 2 then 1 else 0 := by
  change dualFrameVector3 w 2 ≠ 0 ∧ _
  have hq := dualFrameMatrix3_rational_independent w hw
  exact ⟨originalPlane_last_dual_nonzero3 w hq,fun j => dualFrameVector3_pairing w hq j 2⟩

theorem dual_line_literal (a b : Fin 3 → IntegerTriple)
    (ha : LinearIndependent ℝ (fun j => integerTripleReal3 (a j)))
    (hb : LinearIndependent ℝ (fun j => integerTripleReal3 (b j)))
    (hp : Submodule.span ℝ {integerTripleReal3 (b 0),integerTripleReal3 (b 1)} =
      Submodule.span ℝ {integerTripleReal3 (a 0),integerTripleReal3 (a 1)}) :
    Submodule.span ℚ {normal b} = Submodule.span ℚ {normal a} := by
  exact originalPlane_real_to_rational_dual3 a b ha hb (by simpa only [flag_eq] using hp)

theorem deformed_transport_literal (k₀ k₂ k₃ : Fin 3) (Q delta : ℝ)
    (c₀ c₂ c₃ : Fin 3 → ℝ) (hQ : 1 < Q) (hd : 0 < delta)
    (hc₂ : ∀ i, c₂ i ≤ 0) (hc₃ : ∀ i, c₃ i ≤ 0)
    (hb : ∑ i, (c₀ i + c₂ i + c₃ i) = 0)
    (B : Basis (Fin 3) ℝ RealTriple) (u : Fin 3 → lattice k₂ k₃ Q c₂ c₃)
    (hB : lattice3 B = (lattice k₂ k₃ Q c₂ c₃).toIntSubmodule.map integerTripleReal3)
    (hu : LinearIndependent ℝ (fun j => integerTripleReal3 (u j : IntegerTriple)))
    (hatt : ∀ j, coordinateGauge3 (qSourceCoordinates3 k₀ Q c₀ hQ)
      (integerTripleReal3 (u j : IntegerTriple)) = minimum (lattice k₂ k₃ Q c₂ c₃) (qSourceCoordinates3 k₀ Q c₀ hQ) j)
    (hgap : minimum (lattice k₂ k₃ Q c₂ c₃) (qSourceCoordinates3 k₀ Q c₀ hQ) 1 <
      minimum (lattice k₂ k₃ Q c₂ c₃) (qSourceCoordinates3 k₀ Q c₀ hQ) 2 * Q ^ (-delta))
    (d : GapDeformedData3 k₀ k₂ k₃ Q delta c₀ c₂ c₃ hQ B u)
    (hcut : 3072 < Q ^ (2 * delta)) :
    integerTripleReal3 (d.frame 0 : IntegerTriple) ∈
      Submodule.span ℝ {integerTripleReal3 (u 0 : IntegerTriple),integerTripleReal3 (u 1 : IntegerTriple)} ∧
    integerTripleReal3 (d.frame 1 : IntegerTriple) ∈
      Submodule.span ℝ {integerTripleReal3 (u 0 : IntegerTriple),integerTripleReal3 (u 1 : IntegerTriple)} ∧
    Submodule.span ℝ {integerTripleReal3 (d.frame 0 : IntegerTriple),integerTripleReal3 (d.frame 1 : IntegerTriple)} =
      Submodule.span ℝ {integerTripleReal3 (u 0 : IntegerTriple),integerTripleReal3 (u 1 : IntegerTriple)} ∧
    Submodule.span ℚ {normal (fun j => (d.frame j : IntegerTriple))} =
      Submodule.span ℚ {normal (fun j => (u j : IntegerTriple))} := by
  have hm := minimum_eq _ B hB (qSourceCoordinates3 k₀ Q c₀ hQ)
  have ha : ∀ j, coordinateGauge3 (qSourceCoordinates3 k₀ Q c₀ hQ)
      (integerTripleReal3 (u j : IntegerTriple)) = successiveRadius3 B (qSourceCoordinates3 k₀ Q c₀ hQ) j := by
    simpa only [hm] using hatt
  have hg : successiveRadius3 B (qSourceCoordinates3 k₀ Q c₀ hQ) 1 <
      successiveRadius3 B (qSourceCoordinates3 k₀ Q c₀ hQ) 2 * Q ^ (-delta) := by simpa only [hm] using hgap
  have ht := originalPlane_deformed_transport3 k₀ k₂ k₃ Q delta c₀ c₂ c₃ hQ hd hc₂ hc₃ hb B u hB hu ha hg d hcut
  refine ⟨?_,?_,?_,ht.2.2⟩
  · simpa only [flag_eq] using ht.1 0
  · simpa only [flag_eq] using ht.1 1
  · simpa only [flag_eq] using ht.2.1

theorem satz52_literal (k₀ k₂ k₃ : Fin 3) (delta : ℝ) (hd : 0 < delta)
    (c₀ c₂ c₃ : Fin 3 → ℝ)
    (hc₀ : ∀ i, -1 ≤ c₀ i ∧ c₀ i ≤ 1)
    (hc₂ : ∀ i, -1 ≤ c₂ i ∧ c₂ i ≤ 0) (hc₃ : ∀ i, -1 ≤ c₃ i ∧ c₃ i ≤ 0)
    (hb : ∑ i, (c₀ i + c₂ i + c₃ i) = 0)
    (Omega : Set ℝ) (hOmega : ¬ BddAbove Omega) (hQ : ∀ Q ∈ Omega, 1 < Q)
    (B : Omega → Basis (Fin 3) ℝ RealTriple)
    (u : ∀ Q : Omega, Fin 3 → lattice k₂ k₃ Q.val c₂ c₃)
    (hB : ∀ Q : Omega, lattice3 (B Q) =
      (lattice k₂ k₃ Q.val c₂ c₃).toIntSubmodule.map integerTripleReal3)
    (hu : ∀ Q : Omega, LinearIndependent ℝ (fun j => integerTripleReal3 (u Q j : IntegerTriple)))
    (hatt : ∀ Q : Omega, ∀ j, coordinateGauge3 (qSourceCoordinates3 k₀ Q.val c₀ (hQ Q.val Q.property))
      (integerTripleReal3 (u Q j : IntegerTriple)) =
      minimum (lattice k₂ k₃ Q.val c₂ c₃) (qSourceCoordinates3 k₀ Q.val c₀ (hQ Q.val Q.property)) j)
    (hgap : ∀ Q : Omega, minimum (lattice k₂ k₃ Q.val c₂ c₃) (qSourceCoordinates3 k₀ Q.val c₀ (hQ Q.val Q.property)) 1 <
      minimum (lattice k₂ k₃ Q.val c₂ c₃) (qSourceCoordinates3 k₀ Q.val c₀ (hQ Q.val Q.property)) 2 * Q.val ^ (-delta)) :
    ∃ v : IntegerTriple, v ≠ 0 ∧ ∃ V : Set ℝ, V ⊆ Omega ∧ ¬ BddAbove V ∧
      ∀ Q : Omega, Q.val ∈ V →
        Submodule.span ℚ {normal (fun j => (u Q j : IntegerTriple))} =
          Submodule.span ℚ {fun i => (v i : ℚ)} := by
  have hm (Q : Omega) := minimum_eq _ (B Q) (hB Q)
    (qSourceCoordinates3 k₀ Q.val c₀ (hQ Q.val Q.property))
  have ha : ∀ Q : Omega, ∀ j, coordinateGauge3 (qSourceCoordinates3 k₀ Q.val c₀ (hQ Q.val Q.property))
      (integerTripleReal3 (u Q j : IntegerTriple)) =
      successiveRadius3 (B Q) (qSourceCoordinates3 k₀ Q.val c₀ (hQ Q.val Q.property)) j := by
    simpa only [hm] using hatt
  have hg : ∀ Q : Omega, successiveRadius3 (B Q) (qSourceCoordinates3 k₀ Q.val c₀ (hQ Q.val Q.property)) 1 <
      successiveRadius3 (B Q) (qSourceCoordinates3 k₀ Q.val c₀ (hQ Q.val Q.property)) 2 * Q.val ^ (-delta) := by
    simpa only [hm] using hgap
  exact source_fixed_last_dual_under_gap3 k₀ k₂ k₃ delta hd c₀ c₂ c₃ hc₀ hc₂ hc₃ hb Omega hOmega hQ B u hB hu ha hg

set_option pp.proofs false
#check lattice
#print lattice
#print axioms lattice
#check minimum
#print minimum
#print axioms minimum
#check normal
#print normal
#print axioms normal
#check minimum_eq
#print minimum_eq
#print axioms minimum_eq
#check flag_eq
#print flag_eq
#print axioms flag_eq
#check separation_literal
#print separation_literal
#print axioms separation_literal
#check cutoff_literal
#print cutoff_literal
#print axioms cutoff_literal
#check pairing_literal
#print pairing_literal
#print axioms pairing_literal
#check dual_line_literal
#print dual_line_literal
#print axioms dual_line_literal
#check deformed_transport_literal
#print deformed_transport_literal
#print axioms deformed_transport_literal
#check satz52_literal
#print satz52_literal
#print axioms satz52_literal
end OriginalPlaneLiteral
