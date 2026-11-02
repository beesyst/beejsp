import SubspaceBridge.Exterior3WedgeFlag4
import Mathlib.LinearAlgebra.Dual.Lemmas
open scoped BigOperators Classical Matrix
open CompoundFeasibility.Exterior3
namespace CompoundFeasibility.Exterior3OriginalLineLiteral186
open OriginalLastDual4 OriginalDeformation4 OriginalDeformedSource4 OriginalSelectedSystem4 SourceSelectedDual4
noncomputable section

theorem complement_action4 {R : Type*} [CommRing R] (x : Fin 4 → R) :
    complementMatrix4 *ᵥ x = ![-x 3,x 2,-x 1,x 0] := by
  ext i
  fin_cases i <;> simp [Matrix.mulVec,dotProduct,complementMatrix4,missing4,sign4,Fin.sum_univ_succ]

theorem complement_transpose_action4 {R : Type*} [CommRing R] (x : Fin 4 → R) :
    complementMatrix4.transpose *ᵥ x = ![x 3,-x 2,x 1,-x 0] := by
  ext i
  fin_cases i <;> simp [Matrix.mulVec,dotProduct,complementMatrix4,missing4,sign4,Fin.sum_univ_succ]

theorem complement_orthogonal_int4 :
    (complementMatrix4 : Matrix (Fin 4) (Fin 4) ℤ).transpose * complementMatrix4 = 1 ∧
    (complementMatrix4 : Matrix (Fin 4) (Fin 4) ℤ) * complementMatrix4.transpose = 1 :=
  complementMatrix4_orthogonal

theorem complement_orthogonal_rat4 :
    (complementMatrix4 : Matrix (Fin 4) (Fin 4) ℚ).transpose * complementMatrix4 = 1 ∧
    (complementMatrix4 : Matrix (Fin 4) (Fin 4) ℚ) * complementMatrix4.transpose = 1 :=
  complementMatrix4_orthogonal

theorem complement_inverse_action4 {R : Type*} [CommRing R] (x : Fin 4 → R) :
    complementMatrix4.transpose *ᵥ (complementMatrix4 *ᵥ x) = x := by
  rw [Matrix.mulVec_mulVec,(complementMatrix4_orthogonal (R := R)).1,Matrix.one_mulVec]

theorem complement_transpose_inverse_action4 {R : Type*} [CommRing R] (x : Fin 4 → R) :
    complementMatrix4 *ᵥ (complementMatrix4.transpose *ᵥ x) = x := by
  rw [Matrix.mulVec_mulVec,(complementMatrix4_orthogonal (R := R)).2,Matrix.one_mulVec]

theorem complement_int_cast4 (x : Fin 4 → ℤ) :
    (fun i => ((complementMatrix4 *ᵥ x) i : ℚ)) = complementMatrix4 *ᵥ (fun i => (x i : ℚ)) := by
  rw [complement_action4,complement_action4]
  ext i
  fin_cases i <;> simp

theorem complement_transpose_int_cast4 (x : Fin 4 → ℤ) :
    (fun i => ((complementMatrix4.transpose *ᵥ x) i : ℚ)) =
      complementMatrix4.transpose *ᵥ (fun i => (x i : ℚ)) := by
  rw [complement_transpose_action4,complement_transpose_action4]
  ext i
  fin_cases i <;> simp

def fixedOriginalNormal4 (b : Fin 4 → ℤ) : Fin 4 → ℤ := complementMatrix4.transpose *ᵥ b

theorem fixedOriginalNormal4_ne_zero (b : Fin 4 → ℤ) (hb : b ≠ 0) : fixedOriginalNormal4 b ≠ 0 := by
  intro hz
  have h := complement_transpose_inverse_action4 b
  change complementMatrix4 *ᵥ fixedOriginalNormal4 b = b at h
  rw [hz,Matrix.mulVec_zero] at h
  exact hb h.symm

theorem signed_pairing_orientation4 :
    (∑ s, (complementMatrix4 *ᵥ (![1,0,0,0] : Fin 4 → ℤ)) s *
      tripleWedge4 ![0,1,0,0] ![0,0,1,0] ![0,0,0,1] s) = 1 := by
  decide

theorem signed_complement_pairing4 {R : Type*} [CommRing R] (x y z w : Fin 4 → R) :
    (∑ s, (complementMatrix4 *ᵥ x) s * tripleWedge4 y z w s) =
      Matrix.det (fun i j : Fin 4 => (![x,y,z,w] j) i) := by
  rw [Matrix.det_succ_column_zero,complement_action4]
  simp [Fin.sum_univ_succ,Matrix.det_fin_three,Matrix.submatrix_apply,Fin.succAbove,
    tripleWedge4,tripleIndex4]
  <;> ring

theorem signed_pairing_repeat_left4 {R : Type*} [CommRing R] (x y z : Fin 4 → R) :
    (∑ s, (complementMatrix4 *ᵥ x) s * tripleWedge4 x y z s) = 0 := by
  rw [signed_complement_pairing4]
  exact Matrix.det_zero_of_column_eq (by decide : (0 : Fin 4) ≠ 1) (by intro i; rfl)

theorem tripleFrame4_first_three4 (u : Fin 4 → Fin 4 → ℤ) :
    tripleFrame4 u 0 = tripleWedge4 (u 0) (u 1) (u 2) ∧
    tripleFrame4 u 1 = tripleWedge4 (u 0) (u 1) (u 3) ∧
    tripleFrame4 u 2 = tripleWedge4 (u 0) (u 2) (u 3) := ⟨rfl,rfl,rfl⟩

theorem original_three_pairings_zero4 (u : Fin 4 → Fin 4 → ℤ) :
    ∀ j : Fin 3, normalForm4 (complementMatrix4 *ᵥ u 0)
      (fun i => (tripleFrame4 u j.castSucc i : ℚ)) = 0 := by
  intro j
  have h : (∑ i, (complementMatrix4 *ᵥ u 0) i * tripleFrame4 u j.castSucc i) = 0 := by
    fin_cases j
    · exact signed_pairing_repeat_left4 (u 0) (u 1) (u 2)
    · exact signed_pairing_repeat_left4 (u 0) (u 1) (u 3)
    · exact signed_pairing_repeat_left4 (u 0) (u 2) (u 3)
  rw [normalForm4_apply]
  exact_mod_cast h

theorem original_head_ne_zero4 (u : Fin 4 → Fin 4 → ℤ)
    (hu : LinearIndependent ℝ (fun j => integerReal (u j))) : u 0 ≠ 0 := by
  intro hz
  apply hu.ne_zero 0
  ext i
  simp [integerReal,hz]

theorem complement_ne_zero4 {R : Type*} [CommRing R] (x : Fin 4 → R) (hx : x ≠ 0) :
    complementMatrix4 *ᵥ x ≠ 0 := by
  intro hz
  have h := complement_inverse_action4 x
  rw [hz,Matrix.mulVec_zero] at h
  exact hx h.symm

theorem rank3_dual_annihilator_dimension4 (P : Submodule ℚ (Fin 4 → ℚ))
    (hP : Module.finrank ℚ P = 3) : Module.finrank ℚ P.dualAnnihilator = 1 := by
  have h := Subspace.finrank_add_finrank_dualAnnihilator_eq P
  rw [hP] at h
  have hdim : Module.finrank ℚ (Fin 4 → ℚ) = 4 := by simp
  rw [hdim] at h
  omega

theorem firstThree_normal_line4 (v : Fin 4 → Fin 4 → ℚ) (hv : LinearIndependent ℚ v)
    (n : Fin 4 → ℤ) (hn : n ≠ 0) (hz : ∀ j : Fin 3, normalForm4 n (v j.castSucc) = 0) :
    Submodule.span ℚ {fun i => (n i : ℚ)} = Submodule.span ℚ {lastDual4 v hv} := by
  let alpha := normalForm4 n (v 3)
  have he := functional_lastDual4 v hv (normalForm4 n) hz
  have ha : alpha ≠ 0 := by
    intro h0
    change normalForm4 n (v 3) = 0 at h0
    rw [h0,zero_smul] at he
    exact normalForm4_nonzero n hn he
  have hc : (fun i => (n i : ℚ)) = alpha • lastDual4 v hv := by
    ext i
    have h := congrArg (fun f : Module.Dual ℚ (Fin 4 → ℚ) => f (Pi.single i 1)) he
    simpa [normalForm4_apply,lastDual4,alpha,Pi.single_apply] using h
  rw [hc]
  exact Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr ha) _

theorem original_head_normal_line4 (u : Fin 4 → Fin 4 → ℤ)
    (hu : LinearIndependent ℝ (fun j => integerReal (u j))) (b : Fin 4 → ℤ) (hb : b ≠ 0)
    (P : Submodule ℚ (Fin 4 → ℚ)) (hP : P = LinearMap.ker (normalForm4 b))
    (hspan : P = firstThreeSpan4 (fun j i => (tripleFrame4 u j i : ℚ))) :
    Submodule.span ℚ {fun i => ((complementMatrix4 *ᵥ u 0) i : ℚ)} =
      Submodule.span ℚ {fun i => (b i : ℚ)} := by
  have hv := (tripleFrame4_independent u hu).1
  have hH := complement_ne_zero4 (u 0) (original_head_ne_zero4 u hu)
  have hn := firstThree_normal_line4 _ hv (complementMatrix4 *ᵥ u 0) hH (original_three_pairings_zero4 u)
  have hbzero (j : Fin 3) : normalForm4 b (fun i => (tripleFrame4 u j.castSucc i : ℚ)) = 0 := by
    have hm : (fun i => (tripleFrame4 u j.castSucc i : ℚ)) ∈ P := by
      rw [hspan]
      exact Submodule.subset_span ⟨j,rfl⟩
    rw [hP] at hm
    exact hm
  exact hn.trans (firstThree_normal_line4 _ hv b hb hbzero).symm

theorem original_head_annihilates_plane4 (u : Fin 4 → Fin 4 → ℤ)
    (P : Submodule ℚ (Fin 4 → ℚ))
    (hspan : P = firstThreeSpan4 (fun j i => (tripleFrame4 u j i : ℚ))) :
    normalForm4 (complementMatrix4 *ᵥ u 0) ∈ P.dualAnnihilator := by
  apply (Submodule.mem_dualAnnihilator _).mpr
  have hinc : P ≤ LinearMap.ker (normalForm4 (complementMatrix4 *ᵥ u 0)) := by
    rw [hspan]
    apply Submodule.span_le.mpr
    rintro _ ⟨j,rfl⟩
    exact original_three_pairings_zero4 u j
  intro x hx
  exact hinc hx

theorem original_head_fixed_line4 (u : Fin 4 → Fin 4 → ℤ)
    (hu : LinearIndependent ℝ (fun j => integerReal (u j))) (b : Fin 4 → ℤ) (hb : b ≠ 0)
    (P : Submodule ℚ (Fin 4 → ℚ)) (hP : P = LinearMap.ker (normalForm4 b))
    (hspan : P = firstThreeSpan4 (fun j i => (tripleFrame4 u j i : ℚ))) :
    Submodule.span ℚ {fun i => (u 0 i : ℚ)} =
      Submodule.span ℚ {fun i => (fixedOriginalNormal4 b i : ℚ)} := by
  have hn := original_head_normal_line4 u hu b hb P hP hspan
  have h := congrArg (fun S : Submodule ℚ (Fin 4 → ℚ) =>
    S.map (complementMatrix4.transpose : Matrix (Fin 4) (Fin 4) ℚ).mulVecLin) hn
  simpa only [Submodule.map_span,Set.image_singleton,Matrix.mulVecLin_apply,complement_int_cast4,
    complement_inverse_action4,← complement_transpose_int_cast4,fixedOriginalNormal4] using h

def originalFixedLine4 (b : Fin 4 → ℤ) : Submodule ℚ (Fin 4 → ℚ) :=
  Submodule.span ℚ {fun i => (fixedOriginalNormal4 b i : ℚ)}

theorem originalFixedLine4_finrank (b : Fin 4 → ℤ) (hb : b ≠ 0) :
    Module.finrank ℚ (originalFixedLine4 b) = 1 := by
  apply finrank_span_singleton
  intro hz
  apply fixedOriginalNormal4_ne_zero b hb
  ext i
  have hi := congrFun hz i
  change (fixedOriginalNormal4 b i : ℚ) = 0 at hi
  change fixedOriginalNormal4 b i = 0
  exact_mod_cast hi

theorem original_fixed_line_at4 (u : Fin 4 → Fin 4 → ℤ)
    (hu : LinearIndependent ℝ (fun j => integerReal (u j))) (b : Fin 4 → ℤ) (hb : b ≠ 0)
    (P : Submodule ℚ (Fin 4 → ℚ)) (hP : P = LinearMap.ker (normalForm4 b))
    (hPdim : Module.finrank ℚ P = 3)
    (hspan : P = firstThreeSpan4 (fun j i => (tripleFrame4 u j i : ℚ))) :
    u 0 ≠ 0 ∧ complementMatrix4 *ᵥ u 0 ≠ 0 ∧
    normalForm4 (complementMatrix4 *ᵥ u 0) ∈ P.dualAnnihilator ∧
    Module.finrank ℚ P.dualAnnihilator = 1 ∧
    Submodule.span ℚ {fun i => ((complementMatrix4 *ᵥ u 0) i : ℚ)} =
      Submodule.span ℚ {fun i => (b i : ℚ)} ∧
    Submodule.span ℚ {fun i => (u 0 i : ℚ)} = originalFixedLine4 b := by
  exact ⟨original_head_ne_zero4 u hu,complement_ne_zero4 _ (original_head_ne_zero4 u hu),
    original_head_annihilates_plane4 u P hspan,rank3_dual_annihilator_dimension4 P hPdim,
    original_head_normal_line4 u hu b hb P hP hspan,original_head_fixed_line4 u hu b hb P hP hspan⟩

def originalLineControl4 (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L) (Q : ℝ) (hQ : 1 < Q)
    (c₀ c₂ c₃ : Fin 4 → ℝ) (u : Fin 4 → originalSourceGroup4 A₂ A₃ Q c₂ c₃)
    (b : Fin 4 → ℤ) (P P1 : Submodule ℚ (Fin 4 → ℚ)) : Prop :=
  let uZ := fun j => (u j : Fin 4 → ℤ)
  coordinateGauge4 (originalCoordinates4 L hL Q hQ c₀) (integerReal (uZ 0)) =
    sourceMinima4 A₂ A₃ L hL Q hQ c₀ c₂ c₃ 0 ∧
  uZ 0 ≠ 0 ∧ complementMatrix4 *ᵥ uZ 0 ≠ 0 ∧
  normalForm4 (complementMatrix4 *ᵥ uZ 0) ∈ P.dualAnnihilator ∧
  Submodule.span ℚ {fun i => ((complementMatrix4 *ᵥ uZ 0) i : ℚ)} =
    Submodule.span ℚ {fun i => (b i : ℚ)} ∧
  Submodule.span ℚ {fun i => (uZ 0 i : ℚ)} = P1

def fixedLineFamily4 (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L) (c₀ c₂ c₃ : Fin 4 → ℝ)
    (Qfinal : Set ℝ) (hQ : ∀ Q ∈ Qfinal, 1 < Q)
    (u : (q : Qfinal) → Fin 4 → originalSourceGroup4 A₂ A₃ q.val c₂ c₃)
    (b : Fin 4 → ℤ) (P : Submodule ℚ (Fin 4 → ℚ)) : Prop :=
  ∃ a : Fin 4 → ℤ, a = fixedOriginalNormal4 b ∧ a ≠ 0 ∧
    ∃ P1 : Submodule ℚ (Fin 4 → ℚ),
      P1 = Submodule.span ℚ {fun i => (a i : ℚ)} ∧ Module.finrank ℚ P1 = 1 ∧
      Module.finrank ℚ P.dualAnnihilator = 1 ∧
      ∀ q : Qfinal, originalLineControl4 A₂ A₃ L hL q.val (hQ q.val q.property) c₀ c₂ c₃ (u q) b P P1

def fixedOriginalLineData4
    (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ)
    (hL : L.det = 1) (delta : ℝ) (c₀ c₂ c₃ : Fin 4 → ℝ)
    (U V : Set ℝ) (hQU : ∀ Q ∈ U, 1 < Q) (hVU : V ⊆ U)
    (u : (q : V) → Fin 4 → originalSourceGroup4 A₂ A₃ q.val c₂ c₃)
    (Vprime : Set ℝ) (hVpV : Vprime ⊆ V) (W : Set ℝ) (hWR : ∀ R ∈ W, 1 < R) : Prop :=
    let B₂ := compound3Matrix4 A₂
    let B₃ := compound3Matrix4 A₃
    let B₀ := compound3Matrix4 L
    let hBdet : B₀.det = 1 := by dsimp [B₀]; rw [compound3_det,hL,one_pow]
    ∃ Uc : Set ℝ, ∃ hUcW : Uc ⊆ W, ¬ BddAbove Uc ∧
      ∃ uc : (q : Uc) → Fin 4 → originalSourceGroup4 B₂ B₃ q.val (normalizedWeights3_4 c₂) (normalizedWeights3_4 c₃),
      ∃ Fc : (q : Uc) → DeformedAttaining4 B₂ B₃ B₀ (sourceUnit42 B₀ hBdet) q.val
        (hWR q.val (hUcW q.property)) (normalizedWeights3_4 c₀) (normalizedWeights3_4 c₂) (normalizedWeights3_4 c₃) (delta/12) (uc q),
      ∃ S : Finset OriginalSelectedSystem4.MixedIndex4, S.Nonempty ∧
      ∃ Wc : Set ℝ, ∃ hWcU : Wc ⊆ Uc, ¬ BddAbove Wc ∧
        ¬ BddAbove ((fun q : ℝ => q^(5 : ℕ)) '' Wc) ∧
        (∀ q : Uc, q.val ∈ Wc →
          OriginalSelectedSystem4.publishedIndexSet4 (q.val^(5 : ℕ)) ((delta/12)/24)
            (OriginalDeformation4.deformedWidths4 q.val (normalizedWeights3_4 c₀)
              (OriginalDeformation4.gapDeformation4
                (sourceMinima4 B₂ B₃ B₀ (sourceUnit42 B₀ hBdet) q.val
                  (hWR q.val (hUcW q.property)) (normalizedWeights3_4 c₀) (normalizedWeights3_4 c₂) (normalizedWeights3_4 c₃))) (Fc q).sigma) (fun i => (normalizedWeights3_4 c₂) i/5) (fun i => (normalizedWeights3_4 c₃) i/5) = S) ∧
        ∃ (q1 : Uc) (b : Fin 4 → ℤ) (B : ℝ), q1.val ∈ Wc ∧
          b = integerLastDual4 (fun j => ((Fc q1).w j : Fin 4 → ℤ)) ∧ b ≠ 0 ∧
          Submodule.span ℚ {fun i => (b i : ℚ)} =
            Submodule.span ℚ {lastDual4 (fun j i => (((Fc q1).w j : Fin 4 → ℤ) i : ℚ)) (Fc q1).rational_independent} ∧
          (∀ s ∈ S, mixedProduct4 B₂ B₃ B₀ b s = 0) ∧
          1 < B ∧ ¬ BddAbove {q : ℝ | q ∈ Wc ∧ B < q} ∧
          (∀ q : Uc, q.val ∈ Wc → B < q.val →
            Submodule.span ℚ {lastDual4 (fun j i => (((Fc q).w j : Fin 4 → ℤ) i : ℚ)) (Fc q).rational_independent} =
              Submodule.span ℚ {fun i => (b i : ℚ)}) ∧
          ∃ (Tspan : ℝ) (Wfixed : Set ℝ) (P : Submodule ℚ (Fin 4 → ℚ)),
            1 < Tspan ∧ Wfixed = {Q | Q ∈ Wc ∧ max B Tspan < Q} ∧
            ¬ BddAbove Wfixed ∧ P = LinearMap.ker (normalForm4 b) ∧
            Module.finrank ℚ P = 3 ∧
            (∀ q : Uc, q.val ∈ Wfixed →
              P = firstThreeSpan4 (fun j i => ((uc q j : Fin 4 → ℤ) i : ℚ)) ∧
              P = firstThreeSpan4 (fun j i => (((Fc q).w j : Fin 4 → ℤ) i : ℚ)) ∧
              minimaFlag4 (fun j => integerReal (uc q j : Fin 4 → ℤ)) 3 =
                minimaFlag4 (fun j => integerReal ((Fc q).w j : Fin 4 → ℤ)) 3 ∧
              Module.finrank ℝ (minimaFlag4 (fun j => integerReal (uc q j : Fin 4 → ℤ)) 3) = 3 ∧
              LinearIndependent ℚ (fun j : Fin 3 => fun i => ((uc q j.castSucc : Fin 4 → ℤ) i : ℚ))) ∧
            ∃ C₄ kappa : ℝ, 0 < C₄ ∧ 0 < kappa ∧ kappa = ((1 : ℝ)/24)/(216*C₄^3) ∧
              ∃ (Qfixed : Set ℝ) (hQfV : Qfixed ⊆ Vprime),
                Qfixed = cubePreimage3_4 Vprime Wfixed ∧ ¬ BddAbove Qfixed ∧
                (∀ Q ∈ Qfixed, Q^(3 : ℕ) ∈ Wfixed) ∧
                (∀ q : Qfixed,
                  let qV : V := ⟨q.val,hVpV (hQfV q.property)⟩
                  let hq := hQU q.val (hVU qV.property)
                  retainedOriginalWedges3_4 A₂ A₃ L hL q.val hq c₀ c₂ c₃ kappa delta (u qV)) ∧
              ∃ R₀ : ℝ, 1 < R₀ ∧
                (∀ R : ℝ, R₀ < R → max 16 (216/kappa) < R^(delta/12)) ∧
                ∃ (Qfinal : Set ℝ) (hQfinal : Qfinal ⊆ Qfixed),
                  Qfinal = cubeTail3_4 Qfixed R₀ ∧ ¬ BddAbove Qfinal ∧
                  (∀ q : Qfinal,
                    let qV : V := ⟨q.val,hVpV (hQfV (hQfinal q.property))⟩
                    let hq := hQU q.val (hVU qV.property)
                    ∃ r : Uc, r.val = q.val^(3 : ℕ) ∧
                      retainedOriginalWedges3_4 A₂ A₃ L hL q.val hq c₀ c₂ c₃ kappa delta (u qV) ∧
                      originalWedgeSpan3_4 (tripleFrame4 (fun j => (u qV j : Fin 4 → ℤ)))
                        (fun j => ((Fc r).w j : Fin 4 → ℤ)) P) ∧
                  fixedLineFamily4 A₂ A₃ L (sourceUnit42 L hL) c₀ c₂ c₃ Qfinal
                    (fun Q hQ => hQU Q (hVU (hVpV (hQfV (hQfinal hQ)))))
                    (fun q => u ⟨q.val,hVpV (hQfV (hQfinal q.property))⟩) b P


theorem fixed_original_line_data4_of_wedges
    (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ)
    (hL : L.det = 1) (delta : ℝ) (c₀ c₂ c₃ : Fin 4 → ℝ)
    (U V : Set ℝ) (hQU : ∀ Q ∈ U, 1 < Q) (hVU : V ⊆ U)
    (u : (q : V) → Fin 4 → originalSourceGroup4 A₂ A₃ q.val c₂ c₃)
    (Vprime : Set ℝ) (hVpV : Vprime ⊆ V) (W : Set ℝ) (hWR : ∀ R ∈ W, 1 < R)
    (hsource : fixedOriginalWedgeSpanData3_4 A₂ A₃ L hL delta c₀ c₂ c₃ U V hQU hVU u Vprime hVpV W hWR) :
    fixedOriginalLineData4 A₂ A₃ L hL delta c₀ c₂ c₃ U V hQU hVU u Vprime hVpV W hWR := by
  classical
  dsimp only [fixedOriginalLineData4]
  obtain ⟨Uc,hUcW,hUc,uc,Fc,S,hS,Wc,hWcU,hWc,hWcp,hselected,q1,b,B,hq1,hbint,hb,hline,hbz,hB,htail,hfixed,
    Tspan,Wfixed,P,hTspan,hF_eq,hF,hP,hPdim,hflags,C₄,kappa,hC₄,hk,hkeq,
    Qfixed,hQfV,hQfeq,hQf,hQcube,hret,R₀,hR₀,hcut,Qfinal,hQfinal,hQfinaleq,hQfinalU,hfinal⟩ := hsource
  refine ⟨Uc,hUcW,hUc,uc,Fc,S,hS,Wc,hWcU,hWc,hWcp,hselected,q1,b,B,hq1,hbint,hb,hline,hbz,hB,htail,hfixed,
    Tspan,Wfixed,P,hTspan,hF_eq,hF,hP,hPdim,hflags,C₄,kappa,hC₄,hk,hkeq,
    Qfixed,hQfV,hQfeq,hQf,hQcube,hret,R₀,hR₀,hcut,Qfinal,hQfinal,hQfinaleq,hQfinalU,hfinal,?_⟩
  refine ⟨fixedOriginalNormal4 b,rfl,fixedOriginalNormal4_ne_zero b hb,
    originalFixedLine4 b,rfl,originalFixedLine4_finrank b hb,rank3_dual_annihilator_dimension4 P hPdim,?_⟩
  intro q
  let qV : V := ⟨q.val,hVpV (hQfV (hQfinal q.property))⟩
  obtain ⟨r,hr,hretain,hspan⟩ := hfinal q
  obtain ⟨h0,hH,hann,_,hnorm,hline0⟩ := original_fixed_line_at4 (fun j => (u qV j : Fin 4 → ℤ))
    hretain.1.1 b hb P hP hPdim hspan.2.2.2
  exact ⟨hretain.1.2.1 0,h0,hH,hann,hnorm,hline0⟩

theorem source_original_fixed_rank1_4 (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (h₂ : A₂.det = 1) (h₃ : A₃.det = 1) (hL : L.det = 1)
    (hAlg : ∀ i j, IsAlgebraic ℚ (L i j)) (delta : ℝ) (hd : 0 < delta) :
    let B₂ := compound3Matrix4 A₂
    let B₃ := compound3Matrix4 A₃
    let B₀ := compound3Matrix4 L
    let hBdet : B₀.det = 1 := by dsimp [B₀]; rw [compound3_det,hL,one_pow]
    let hBunit := sourceUnit42 B₀ hBdet
    ∃ Told T : ℝ, 1 < Told ∧ 1 < T ∧ Told ≤ T ∧ 0 < delta/12 ∧
      (∀ Q : ℝ, T < Q → 36 < Q^(delta/4)) ∧
      B₂.det = 1 ∧ B₃.det = 1 ∧ B₀.det = 1 ∧ IsUnit B₂ ∧ IsUnit B₃ ∧ IsUnit B₀ ∧
      (∀ s t, IsAlgebraic ℚ (B₀ s t)) ∧
      ∀ (c₀ c₂ c₃ : Fin 4 → ℝ) (_hc₀ : ∀ i, |c₀ i| ≤ 1)
        (_hc₂ : ∀ i, -1 ≤ c₂ i ∧ c₂ i ≤ 0) (_hc₃ : ∀ i, -1 ≤ c₃ i ∧ c₃ i ≤ 0)
        (_hb : ∑ i, (c₀ i+c₂ i+c₃ i) = 0),
        (∀ s, |normalizedWeights3_4 c₀ s| ≤ 1) ∧
        (∀ s, -1 ≤ normalizedWeights3_4 c₂ s ∧ normalizedWeights3_4 c₂ s ≤ 0) ∧
        (∀ s, -1 ≤ normalizedWeights3_4 c₃ s ∧ normalizedWeights3_4 c₃ s ≤ 0) ∧
        (∑ s, (normalizedWeights3_4 c₀ s+normalizedWeights3_4 c₂ s+normalizedWeights3_4 c₃ s) = 0) ∧
        ∀ (U : Set ℝ) (_hU : ¬ BddAbove U) (hQU : ∀ Q ∈ U, 1 < Q),
          (∀ (Q : ℝ) (hq : Q ∈ U), sourceMinima4 A₂ A₃ L (sourceUnit42 L hL) Q (hQU Q hq) c₀ c₂ c₃ 0 <
            sourceMinima4 A₂ A₃ L (sourceUnit42 L hL) Q (hQU Q hq) c₀ c₂ c₃ 1*Q^(-delta)) →
          ∃ (V : Set ℝ) (hVU : V ⊆ U), V = {Q | Q ∈ U ∧ Told < Q} ∧ ¬ BddAbove V ∧
            ∃ u : (q : V) → Fin 4 → originalSourceGroup4 A₂ A₃ q.val c₂ c₃,
              (∀ q : V, originalFrameControl3_4 A₂ A₃ L (sourceUnit42 L hL) q.val
                (hQU q.val (hVU q.property)) c₀ c₂ c₃ (u q) ∧ Told < q.val ∧
                compoundMinima3_4 A₂ A₃ L (sourceUnit42 L hL) q.val (hQU q.val (hVU q.property)) c₀ c₂ c₃ 2 <
                  compoundMinima3_4 A₂ A₃ L (sourceUnit42 L hL) q.val (hQU q.val (hVU q.property)) c₀ c₂ c₃ 3*q.val^(-delta/2)) ∧
              ∃ (Vprime : Set ℝ) (hVpV : Vprime ⊆ V), Vprime = {Q | Q ∈ V ∧ T < Q} ∧ ¬ BddAbove Vprime ∧
                ∃ (W : Set ℝ) (hWR : ∀ R ∈ W, 1 < R), W = cubeImage3_4 Vprime ∧ ¬ BddAbove W ∧
                  (∀ q : Vprime,
                    normalizationTransport3_4 A₂ A₃ L (sourceUnit42 L hL) q.val
                      (hQU q.val (hVU (hVpV q.property))) c₀ c₂ c₃ ∧
                    (∀ s, tripleFrame4 (fun j => (u ⟨q.val,hVpV q.property⟩ j : Fin 4 → ℤ)) s ∈
                      normalizedGroup3_4 A₂ A₃ q.val c₂ c₃) ∧
                    normalizedMinima3_4 A₂ A₃ L (sourceUnit42 L hL) q.val
                      (hQU q.val (hVU (hVpV q.property))) c₀ c₂ c₃ 2 <
                      normalizedMinima3_4 A₂ A₃ L (sourceUnit42 L hL) q.val
                        (hQU q.val (hVU (hVpV q.property))) c₀ c₂ c₃ 3*(q.val^(3 : ℕ))^(-delta/12)) ∧
                  (∀ (R : ℝ) (hR : R ∈ W), ∃ q : Vprime, R = q.val^(3 : ℕ) ∧
                    sourceMinima4 B₂ B₃ B₀ hBunit R (hWR R hR)
                      (normalizedWeights3_4 c₀) (normalizedWeights3_4 c₂) (normalizedWeights3_4 c₃) 2 <
                    sourceMinima4 B₂ B₃ B₀ hBunit R (hWR R hR)
                      (normalizedWeights3_4 c₀) (normalizedWeights3_4 c₂) (normalizedWeights3_4 c₃) 3*R^(-delta/12)) ∧
fixedOriginalLineData4 A₂ A₃ L hL delta c₀ c₂ c₃ U V hQU hVU u Vprime hVpV W hWR := by
  classical
  dsimp only
  obtain ⟨Told,T,hTold,hT,hTT,hdNew,hcut,hB₂,hB₃,hB₀,hBu₂,hBu₃,hBu₀,hBalg,htails⟩ :=
    source_original_wedges_fixed_compound_rank3_4 A₂ A₃ L h₂ h₃ hL hAlg delta hd
  refine ⟨Told,T,hTold,hT,hTT,hdNew,hcut,hB₂,hB₃,hB₀,hBu₂,hBu₃,hBu₀,hBalg,?_⟩
  intro c₀ c₂ c₃ hc₀ hc₂ hc₃ hb
  obtain ⟨ha₀,ha₂,ha₃,hab,hfamilies⟩ := htails c₀ c₂ c₃ hc₀ hc₂ hc₃ hb
  refine ⟨ha₀,ha₂,ha₃,hab,?_⟩
  intro U hU hQU hgap
  obtain ⟨V,hVU,hVeq,hV,u,hu,Vprime,hVpV,hVpeq,hVp,W,hWR,hWeq,hW,hpoint,hpre,hsource⟩ :=
    hfamilies U hU hQU hgap
  exact ⟨V,hVU,hVeq,hV,u,hu,Vprime,hVpV,hVpeq,hVp,W,hWR,hWeq,hW,hpoint,hpre,
    fixed_original_line_data4_of_wedges A₂ A₃ L hL delta c₀ c₂ c₃ U V hQU hVU u Vprime hVpV W hWR hsource⟩

end
end CompoundFeasibility.Exterior3OriginalLineLiteral186
#check CompoundFeasibility.Exterior3OriginalLineLiteral186.complement_action4
#print CompoundFeasibility.Exterior3OriginalLineLiteral186.complement_action4
#print axioms CompoundFeasibility.Exterior3OriginalLineLiteral186.complement_action4
#check CompoundFeasibility.Exterior3OriginalLineLiteral186.complement_transpose_action4
#print CompoundFeasibility.Exterior3OriginalLineLiteral186.complement_transpose_action4
#print axioms CompoundFeasibility.Exterior3OriginalLineLiteral186.complement_transpose_action4
#check CompoundFeasibility.Exterior3OriginalLineLiteral186.complement_orthogonal_int4
#print CompoundFeasibility.Exterior3OriginalLineLiteral186.complement_orthogonal_int4
#print axioms CompoundFeasibility.Exterior3OriginalLineLiteral186.complement_orthogonal_int4
#check CompoundFeasibility.Exterior3OriginalLineLiteral186.complement_orthogonal_rat4
#print CompoundFeasibility.Exterior3OriginalLineLiteral186.complement_orthogonal_rat4
#print axioms CompoundFeasibility.Exterior3OriginalLineLiteral186.complement_orthogonal_rat4
#check CompoundFeasibility.Exterior3OriginalLineLiteral186.complement_inverse_action4
#print CompoundFeasibility.Exterior3OriginalLineLiteral186.complement_inverse_action4
#print axioms CompoundFeasibility.Exterior3OriginalLineLiteral186.complement_inverse_action4
#check CompoundFeasibility.Exterior3OriginalLineLiteral186.complement_transpose_inverse_action4
#print CompoundFeasibility.Exterior3OriginalLineLiteral186.complement_transpose_inverse_action4
#print axioms CompoundFeasibility.Exterior3OriginalLineLiteral186.complement_transpose_inverse_action4
#check CompoundFeasibility.Exterior3OriginalLineLiteral186.complement_int_cast4
#print CompoundFeasibility.Exterior3OriginalLineLiteral186.complement_int_cast4
#print axioms CompoundFeasibility.Exterior3OriginalLineLiteral186.complement_int_cast4
#check CompoundFeasibility.Exterior3OriginalLineLiteral186.complement_transpose_int_cast4
#print CompoundFeasibility.Exterior3OriginalLineLiteral186.complement_transpose_int_cast4
#print axioms CompoundFeasibility.Exterior3OriginalLineLiteral186.complement_transpose_int_cast4
#check CompoundFeasibility.Exterior3OriginalLineLiteral186.fixedOriginalNormal4
#print CompoundFeasibility.Exterior3OriginalLineLiteral186.fixedOriginalNormal4
#print axioms CompoundFeasibility.Exterior3OriginalLineLiteral186.fixedOriginalNormal4
#check CompoundFeasibility.Exterior3OriginalLineLiteral186.fixedOriginalNormal4_ne_zero
#print CompoundFeasibility.Exterior3OriginalLineLiteral186.fixedOriginalNormal4_ne_zero
#print axioms CompoundFeasibility.Exterior3OriginalLineLiteral186.fixedOriginalNormal4_ne_zero
#check CompoundFeasibility.Exterior3OriginalLineLiteral186.signed_pairing_orientation4
#print CompoundFeasibility.Exterior3OriginalLineLiteral186.signed_pairing_orientation4
#print axioms CompoundFeasibility.Exterior3OriginalLineLiteral186.signed_pairing_orientation4
#check CompoundFeasibility.Exterior3OriginalLineLiteral186.signed_complement_pairing4
#print CompoundFeasibility.Exterior3OriginalLineLiteral186.signed_complement_pairing4
#print axioms CompoundFeasibility.Exterior3OriginalLineLiteral186.signed_complement_pairing4
#check CompoundFeasibility.Exterior3OriginalLineLiteral186.signed_pairing_repeat_left4
#print CompoundFeasibility.Exterior3OriginalLineLiteral186.signed_pairing_repeat_left4
#print axioms CompoundFeasibility.Exterior3OriginalLineLiteral186.signed_pairing_repeat_left4
#check CompoundFeasibility.Exterior3OriginalLineLiteral186.tripleFrame4_first_three4
#print CompoundFeasibility.Exterior3OriginalLineLiteral186.tripleFrame4_first_three4
#print axioms CompoundFeasibility.Exterior3OriginalLineLiteral186.tripleFrame4_first_three4
#check CompoundFeasibility.Exterior3OriginalLineLiteral186.original_three_pairings_zero4
#print CompoundFeasibility.Exterior3OriginalLineLiteral186.original_three_pairings_zero4
#print axioms CompoundFeasibility.Exterior3OriginalLineLiteral186.original_three_pairings_zero4
#check CompoundFeasibility.Exterior3OriginalLineLiteral186.original_head_ne_zero4
#print CompoundFeasibility.Exterior3OriginalLineLiteral186.original_head_ne_zero4
#print axioms CompoundFeasibility.Exterior3OriginalLineLiteral186.original_head_ne_zero4
#check CompoundFeasibility.Exterior3OriginalLineLiteral186.complement_ne_zero4
#print CompoundFeasibility.Exterior3OriginalLineLiteral186.complement_ne_zero4
#print axioms CompoundFeasibility.Exterior3OriginalLineLiteral186.complement_ne_zero4
#check CompoundFeasibility.Exterior3OriginalLineLiteral186.rank3_dual_annihilator_dimension4
#print CompoundFeasibility.Exterior3OriginalLineLiteral186.rank3_dual_annihilator_dimension4
#print axioms CompoundFeasibility.Exterior3OriginalLineLiteral186.rank3_dual_annihilator_dimension4
#check CompoundFeasibility.Exterior3OriginalLineLiteral186.firstThree_normal_line4
#print CompoundFeasibility.Exterior3OriginalLineLiteral186.firstThree_normal_line4
#print axioms CompoundFeasibility.Exterior3OriginalLineLiteral186.firstThree_normal_line4
#check CompoundFeasibility.Exterior3OriginalLineLiteral186.original_head_normal_line4
#print CompoundFeasibility.Exterior3OriginalLineLiteral186.original_head_normal_line4
#print axioms CompoundFeasibility.Exterior3OriginalLineLiteral186.original_head_normal_line4
#check CompoundFeasibility.Exterior3OriginalLineLiteral186.original_head_annihilates_plane4
#print CompoundFeasibility.Exterior3OriginalLineLiteral186.original_head_annihilates_plane4
#print axioms CompoundFeasibility.Exterior3OriginalLineLiteral186.original_head_annihilates_plane4
#check CompoundFeasibility.Exterior3OriginalLineLiteral186.original_head_fixed_line4
#print CompoundFeasibility.Exterior3OriginalLineLiteral186.original_head_fixed_line4
#print axioms CompoundFeasibility.Exterior3OriginalLineLiteral186.original_head_fixed_line4
#check CompoundFeasibility.Exterior3OriginalLineLiteral186.originalFixedLine4
#print CompoundFeasibility.Exterior3OriginalLineLiteral186.originalFixedLine4
#print axioms CompoundFeasibility.Exterior3OriginalLineLiteral186.originalFixedLine4
#check CompoundFeasibility.Exterior3OriginalLineLiteral186.originalFixedLine4_finrank
#print CompoundFeasibility.Exterior3OriginalLineLiteral186.originalFixedLine4_finrank
#print axioms CompoundFeasibility.Exterior3OriginalLineLiteral186.originalFixedLine4_finrank
#check CompoundFeasibility.Exterior3OriginalLineLiteral186.original_fixed_line_at4
#print CompoundFeasibility.Exterior3OriginalLineLiteral186.original_fixed_line_at4
#print axioms CompoundFeasibility.Exterior3OriginalLineLiteral186.original_fixed_line_at4
#check CompoundFeasibility.Exterior3OriginalLineLiteral186.originalLineControl4
#print CompoundFeasibility.Exterior3OriginalLineLiteral186.originalLineControl4
#print axioms CompoundFeasibility.Exterior3OriginalLineLiteral186.originalLineControl4
#check CompoundFeasibility.Exterior3OriginalLineLiteral186.fixedLineFamily4
#print CompoundFeasibility.Exterior3OriginalLineLiteral186.fixedLineFamily4
#print axioms CompoundFeasibility.Exterior3OriginalLineLiteral186.fixedLineFamily4
#check CompoundFeasibility.Exterior3OriginalLineLiteral186.fixedOriginalLineData4
#print CompoundFeasibility.Exterior3OriginalLineLiteral186.fixedOriginalLineData4
#print axioms CompoundFeasibility.Exterior3OriginalLineLiteral186.fixedOriginalLineData4
#check CompoundFeasibility.Exterior3OriginalLineLiteral186.fixed_original_line_data4_of_wedges
#print CompoundFeasibility.Exterior3OriginalLineLiteral186.fixed_original_line_data4_of_wedges
#print axioms CompoundFeasibility.Exterior3OriginalLineLiteral186.fixed_original_line_data4_of_wedges
#check CompoundFeasibility.Exterior3OriginalLineLiteral186.source_original_fixed_rank1_4
#print CompoundFeasibility.Exterior3OriginalLineLiteral186.source_original_fixed_rank1_4
#print axioms CompoundFeasibility.Exterior3OriginalLineLiteral186.source_original_fixed_rank1_4
