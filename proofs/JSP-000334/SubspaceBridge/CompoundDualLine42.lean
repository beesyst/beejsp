import SubspaceBridge.CompoundHyperplane42
import Mathlib.LinearAlgebra.Dual.Basis
open scoped BigOperators Matrix
namespace CompoundFeasibility
noncomputable section

def wedgeDual42 (f g : Module.Dual ℚ (Fin 4 → ℚ)) : Module.Dual ℚ (Fin 6 → ℚ) :=
  ∑ s : Fin 6, (f (Pi.single (lo s) 1) * g (Pi.single (hi s) 1) -
    f (Pi.single (hi s) 1) * g (Pi.single (lo s) 1)) • LinearMap.proj s

theorem functional_coordinates42 (f : Module.Dual ℚ (Fin 4 → ℚ)) (x : Fin 4 → ℚ) :
    f x = ∑ i, x i * f (Pi.single i 1) := by
  classical
  have hx : x = ∑ i : Fin 4, x i • Pi.single i (1 : ℚ) := by
    ext j
    simp [Pi.single_apply, mul_ite]
  conv_lhs => rw [hx]
  simp

theorem wedgeDual42_pairing (f g : Module.Dual ℚ (Fin 4 → ℚ)) (x y : Fin 4 → ℚ) :
    wedgeDual42 f g (wedge x y) = f x * g y - f y * g x := by
  rw [functional_coordinates42 f x,functional_coordinates42 g y,
    functional_coordinates42 f y,functional_coordinates42 g x]
  simp [wedgeDual42,LinearMap.sum_apply,LinearMap.smul_apply,wedge,lo,hi,Fin.sum_univ_succ]
  ring

def rationalFrameBasis42 {n : ℕ} (u : Fin n → Fin n → ℚ) (hu : LinearIndependent ℚ u) :
    Basis (Fin n) ℚ (Fin n → ℚ) := by
  classical
  exact basisOfPiSpaceOfLinearIndependent hu

theorem rationalFrameBasis42_apply {n : ℕ} (u : Fin n → Fin n → ℚ)
    (hu : LinearIndependent ℚ u) (i : Fin n) : rationalFrameBasis42 u hu i = u i := by
  exact congrFun (coe_basisOfPiSpaceOfLinearIndependent hu) i

def rationalFrameDual42 {n : ℕ} (u : Fin n → Fin n → ℚ) (hu : LinearIndependent ℚ u)
    (i : Fin n) : Module.Dual ℚ (Fin n → ℚ) := (rationalFrameBasis42 u hu).dualBasis i

theorem rationalFrameDual42_pairing {n : ℕ} (u : Fin n → Fin n → ℚ)
    (hu : LinearIndependent ℚ u) (i j : Fin n) :
    rationalFrameDual42 u hu i (u j) = if j = i then 1 else 0 := by
  rw [← rationalFrameBasis42_apply u hu j]
  exact (rationalFrameBasis42 u hu).dualBasis_apply_self i j

theorem lastDual42_nonzero (v : Fin 6 → Fin 6 → ℚ) (hv : LinearIndependent ℚ v) :
    rationalFrameDual42 v hv 5 ≠ 0 := by
  intro hz
  have h := rationalFrameDual42_pairing v hv 5 5
  rw [hz] at h
  norm_num at h

theorem lastDual42_kernel (v : Fin 6 → Fin 6 → ℚ) (hv : LinearIndependent ℚ v) :
    LinearMap.ker (rationalFrameDual42 v hv 5) = firstFiveSpan42 v := by
  apply le_antisymm
  · intro x hx
    have hz : (rationalFrameBasis42 v hv).repr x 5 = 0 := by
      rw [← Basis.dualBasis_apply]
      exact (show rationalFrameDual42 v hv 5 x = 0 from hx)
    have he := (rationalFrameBasis42 v hv).sum_repr x
    rw [Fin.sum_univ_castSucc,show Fin.last 5 = (5 : Fin 6) from rfl,hz,zero_smul,add_zero] at he
    rw [← he]
    apply Submodule.sum_mem
    intro i _
    apply Submodule.smul_mem
    rw [rationalFrameBasis42_apply]
    exact Submodule.subset_span ⟨i,rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    change rationalFrameDual42 v hv 5 (v i.castSucc) = 0
    rw [rationalFrameDual42_pairing,if_neg]
    exact fun h => by have := congrArg Fin.val h; simp at this; omega

theorem functional_lastDual42 (v : Fin 6 → Fin 6 → ℚ) (hv : LinearIndependent ℚ v)
    (f : Module.Dual ℚ (Fin 6 → ℚ)) (hf : ∀ i : Fin 5, f (v i.castSucc) = 0) :
    f = f (v 5) • rationalFrameDual42 v hv 5 := by
  apply (rationalFrameBasis42 v hv).ext
  intro j
  rw [rationalFrameBasis42_apply,LinearMap.smul_apply,rationalFrameDual42_pairing]
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp
  · rw [hf]
    simp [show i.castSucc ≠ (5 : Fin 6) by intro h; have := congrArg Fin.val h; simp at this; omega]

theorem compoundDual42_pairing (u : Fin 4 → Fin 4 → ℤ)
    (hu : LinearIndependent ℚ (fun j i => (u j i : ℚ))) (s : Fin 6) :
    wedgeDual42 (rationalFrameDual42 (fun j i => (u j i : ℚ)) hu 2)
      (rationalFrameDual42 (fun j i => (u j i : ℚ)) hu 3)
      (fun i => (compoundFrame u s i : ℚ)) = if s = 5 then 1 else 0 := by
  change wedgeDual42 _ _ (fun i => (wedge (R := ℤ) (u (lo s)) (u (hi s)) i : ℚ)) = _
  rw [wedge_integer_cast,wedgeDual42_pairing]
  simp only [rationalFrameDual42_pairing]
  simp only [Fin.ext_iff]
  fin_cases s
  · change ((if (0 : ℕ) = 2 then (1 : ℚ) else 0) *
        (if (1 : ℕ) = 3 then 1 else 0) -
      (if (1 : ℕ) = 2 then 1 else 0) *
        (if (0 : ℕ) = 3 then 1 else 0)) =
      (if (0 : ℕ) = 5 then 1 else 0)
    norm_num
  · change ((if (0 : ℕ) = 2 then (1 : ℚ) else 0) *
        (if (2 : ℕ) = 3 then 1 else 0) -
      (if (2 : ℕ) = 2 then 1 else 0) *
        (if (0 : ℕ) = 3 then 1 else 0)) =
      (if (1 : ℕ) = 5 then 1 else 0)
    norm_num
  · change ((if (0 : ℕ) = 2 then (1 : ℚ) else 0) *
        (if (3 : ℕ) = 3 then 1 else 0) -
      (if (3 : ℕ) = 2 then 1 else 0) *
        (if (0 : ℕ) = 3 then 1 else 0)) =
      (if (2 : ℕ) = 5 then 1 else 0)
    norm_num
  · change ((if (1 : ℕ) = 2 then (1 : ℚ) else 0) *
        (if (2 : ℕ) = 3 then 1 else 0) -
      (if (2 : ℕ) = 2 then 1 else 0) *
        (if (1 : ℕ) = 3 then 1 else 0)) =
      (if (3 : ℕ) = 5 then 1 else 0)
    norm_num
  · change ((if (1 : ℕ) = 2 then (1 : ℚ) else 0) *
        (if (3 : ℕ) = 3 then 1 else 0) -
      (if (3 : ℕ) = 2 then 1 else 0) *
        (if (1 : ℕ) = 3 then 1 else 0)) =
      (if (4 : ℕ) = 5 then 1 else 0)
    norm_num
  · change ((if (2 : ℕ) = 2 then (1 : ℚ) else 0) *
        (if (3 : ℕ) = 3 then 1 else 0) -
      (if (3 : ℕ) = 2 then 1 else 0) *
        (if (2 : ℕ) = 3 then 1 else 0)) =
      (if (5 : ℕ) = 5 then 1 else 0)
    norm_num

theorem orderedCompoundDual42_pairing (u : Fin 4 → Fin 4 → ℤ)
    (hu : LinearIndependent ℚ (fun j i => (u j i : ℚ))) (a : Fin 4 → ℝ) (j : Fin 6) :
    wedgeDual42 (rationalFrameDual42 (fun j i => (u j i : ℚ)) hu 2)
      (rationalFrameDual42 (fun j i => (u j i : ℚ)) hu 3)
      (fun i => (orderedWedges42 u a j i : ℚ)) = if j = 5 then 1 else 0 := by
  rw [show (fun i => (orderedWedges42 u a j i : ℚ)) =
    (fun i => (compoundFrame u (pairProductOrder42 a j) i : ℚ)) from rfl,
    compoundDual42_pairing]
  have he : pairProductOrder42 a j = 5 ↔ j = 5 := by
    constructor
    · intro h
      apply (pairProductOrder42 a).injective
      simpa only [pairProductOrder42_last] using h
    · rintro rfl
      exact pairProductOrder42_last a
  simp only [he]

def rationalDualLine42 (u : Fin 4 → Fin 4 → ℤ) (v : Fin 6 → Fin 6 → ℤ) (a : Fin 4 → ℝ) : Prop :=
  ∃ (U : Fin 4 → Module.Dual ℚ (Fin 4 → ℚ)) (V : Fin 6 → Module.Dual ℚ (Fin 6 → ℚ)),
    (∀ i j, U i (fun t => (u j t : ℚ)) = if j = i then 1 else 0) ∧
    (∀ i j, V i (fun t => (v j t : ℚ)) = if j = i then 1 else 0) ∧
    let f := wedgeDual42 (U 2) (U 3)
    (∀ j, f (fun t => (orderedWedges42 u a j t : ℚ)) = if j = 5 then 1 else 0) ∧
    f ≠ 0 ∧ V 5 ≠ 0 ∧
    LinearMap.ker f = firstFiveSpan42 (fun j t => (v j t : ℚ)) ∧
    LinearMap.ker (V 5) = firstFiveSpan42 (fun j t => (v j t : ℚ)) ∧
    f (fun t => (v 5 t : ℚ)) ≠ 0 ∧
    f = f (fun t => (v 5 t : ℚ)) • V 5 ∧
    Submodule.span ℚ {V 5} = Submodule.span ℚ {f} ∧
    Module.finrank ℚ (Submodule.span ℚ {V 5}) = 1

theorem same_frame_dual_line42 (u : Fin 4 → Fin 4 → ℤ) (v : Fin 6 → Fin 6 → ℤ)
    (hu : LinearIndependent ℝ (fun j i => (u j i : ℝ)))
    (hv : LinearIndependent ℝ (fun j i => (v j i : ℝ))) (a : Fin 4 → ℝ)
    (he : firstFiveSpan42 (fun j i => (orderedWedges42 u a j i : ℚ)) =
      firstFiveSpan42 (fun j i => (v j i : ℚ))) : rationalDualLine42 u v a := by
  classical
  have huq := integral_frame_rational_independent u hu
  have hvq := (integer6_independent_iff42 v).mpr hv
  let U := rationalFrameDual42 (fun j i => (u j i : ℚ)) huq
  let V := rationalFrameDual42 (fun j i => (v j i : ℚ)) hvq
  let f := wedgeDual42 (U 2) (U 3)
  have hpair := orderedCompoundDual42_pairing u huq a
  have hfn : f ≠ 0 := by
    intro hz
    have h := hpair 5
    change f _ = _ at h
    rw [hz] at h
    norm_num at h
  have hvan : firstFiveSpan42 (fun j i => (v j i : ℚ)) ≤ LinearMap.ker f := by
    rw [← he]
    apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    change f (fun t => (orderedWedges42 u a i.castSucc t : ℚ)) = 0
    rw [hpair,if_neg]
    intro h
    have := congrArg Fin.val h
    simp at this
    omega
  have hrel : f = f (fun t => (v 5 t : ℚ)) • V 5 :=
    functional_lastDual42 _ hvq f (fun i => hvan (Submodule.subset_span ⟨i,rfl⟩))
  have hc : f (fun t => (v 5 t : ℚ)) ≠ 0 := by
    intro hz
    apply hfn
    rw [hrel,hz,zero_smul]
  have hk : LinearMap.ker f = LinearMap.ker (V 5) := by
    ext x
    change f x = 0 ↔ V 5 x = 0
    rw [hrel,LinearMap.smul_apply,smul_eq_mul,mul_eq_zero]
    simp only [hc,false_or]
  have hl : Submodule.span ℚ {V 5} = Submodule.span ℚ {f} := by
    conv_rhs => rw [hrel]
    exact (Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr hc) (V 5)).symm
  refine ⟨U,V,rationalFrameDual42_pairing _ huq,rationalFrameDual42_pairing _ hvq,
    hpair,hfn,lastDual42_nonzero _ hvq,?_,lastDual42_kernel _ hvq,hc,hrel,hl,?_⟩
  · exact hk.trans (lastDual42_kernel _ hvq)
  · exact finrank_span_singleton (lastDual42_nonzero _ hvq)


theorem source_hyperplane_dual_line42 (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L) (Q : ℝ) (hQ : 1 < Q)
    (c₀ c₂ c₃ : Fin 4 → ℝ) (κ : ℝ)
    (u : Fin 4 → originalSourceGroup4 A₂ A₃ Q c₂ c₃)
    (v : Fin 6 → directCompoundGroup42 A₂ A₃ Q c₂ c₃)
    (hs : sourceHyperplane42 A₂ A₃ L hL Q hQ c₀ c₂ c₃ κ u v) :
    rationalDualLine42 (fun i => (u i : Fin 4 → ℤ)) (fun j => (v j : Fin 6 → ℤ))
      (sourceMinima4 A₂ A₃ L hL Q hQ c₀ c₂ c₃) := by
  rcases hs with ⟨hu,_,hv,_,_,_,_,_,_,_,_,_,_,_,_,he,_⟩
  exact same_frame_dual_line42 _ _ hu hv _ he

theorem source_uniform_dual_line42 (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (h₂ : IsUnit A₂) (h₃ : IsUnit A₃) (hL : IsUnit L)
    (delta : ℝ) (hd : 0 < delta) :
    ∃ κ T : ℝ, 0 < κ ∧ 1 < T ∧ (∀ Q : ℝ, T < Q → 12 / κ < Q ^ (delta / 2)) ∧
      ∀ (Q : ℝ) (hQ : 1 < Q) (c₀ c₂ c₃ : Fin 4 → ℝ),
        (∀ i, c₂ i ≤ 0) → (∀ i, c₃ i ≤ 0) → (∑ i, (c₀ i + c₂ i + c₃ i) = 0) → T < Q →
        sourceMinima4 A₂ A₃ L hL Q hQ c₀ c₂ c₃ 1 < sourceMinima4 A₂ A₃ L hL Q hQ c₀ c₂ c₃ 2 * Q ^ (-delta) →
        ∃ (u : Fin 4 → originalSourceGroup4 A₂ A₃ Q c₂ c₃)
          (v : Fin 6 → directCompoundGroup42 A₂ A₃ Q c₂ c₃),
          sourceHyperplane42 A₂ A₃ L hL Q hQ c₀ c₂ c₃ κ u v ∧
          rationalDualLine42 (fun i => (u i : Fin 4 → ℤ)) (fun j => (v j : Fin 6 → ℤ))
            (sourceMinima4 A₂ A₃ L hL Q hQ c₀ c₂ c₃) := by
  obtain ⟨κ,T,hk,hT,hcut,h⟩ := source_uniform_hyperplane42 A₂ A₃ L h₂ h₃ hL delta hd
  refine ⟨κ,T,hk,hT,hcut,?_⟩
  intro Q hQ c₀ c₂ c₃ hc₂ hc₃ hbal hTQ hg
  obtain ⟨u,v,hs⟩ := h Q hQ c₀ c₂ c₃ hc₂ hc₃ hbal hTQ hg
  exact ⟨u,v,hs,source_hyperplane_dual_line42 A₂ A₃ L hL Q hQ c₀ c₂ c₃ κ u v hs⟩

end
end CompoundFeasibility
