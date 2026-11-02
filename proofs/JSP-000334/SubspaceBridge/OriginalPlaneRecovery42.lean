import SubspaceBridge.OriginalPlaneCoupling42
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.OriginalPlaneRecovery42
open SourceWeights SourceReadiness6 SourceNormalIndex SchlickeweiDualVanishing6
open SchlickeweiReference6 SchlickeweiRealCompletion6

theorem functional_ext6 (f g : Module.Dual ℚ (Fin 6 → ℚ))
    (h : ∀ i, f (Pi.single i 1) = g (Pi.single i 1)) : f = g := by
  apply LinearMap.ext
  intro x
  rw [functional_coordinates6 f x,functional_coordinates6 g x]
  apply Finset.sum_congr rfl
  intro i _
  rw [h i]

theorem normalForm_nonzero6 (b : Fin 6 → ℤ) (hb : b ≠ 0) : normalForm6 b ≠ 0 := by
  intro hz
  apply hb
  funext i
  have hi := congrArg (fun f : Module.Dual ℚ (Fin 6 → ℚ) => f (Pi.single i 1)) hz
  simp [normalForm6,Pi.single_apply] at hi
  exact_mod_cast hi

theorem normalForm_of_dual_line6 (v : Fin 6 → Fin 6 → ℤ)
    (hv : LinearIndependent ℚ (fun j i => (v j i : ℚ)))
    (b : Fin 6 → ℤ) (hb : b ≠ 0)
    (hline : Submodule.span ℚ {dualVector6 v hv} =
      Submodule.span ℚ {fun i => (b i : ℚ)}) :
    ∃ a : ℚ, a ≠ 0 ∧ normalForm6 b =
      a • rationalFrameDual42 (fun j i => (v j i : ℚ)) hv 5 := by
  have hmem : (fun i => (b i : ℚ)) ∈ Submodule.span ℚ {dualVector6 v hv} := by
    rw [hline]
    exact Submodule.subset_span (Set.mem_singleton _)
  obtain ⟨a,ha⟩ := Submodule.mem_span_singleton.mp hmem
  have he : normalForm6 b = a • rationalFrameDual42 (fun j i => (v j i : ℚ)) hv 5 := by
    apply functional_ext6
    intro i
    have hi := congrFun ha i
    simpa [normalForm6,dualVector6,Pi.single_apply] using hi.symm
  have hn : a ≠ 0 := by
    intro hz
    apply normalForm_nonzero6 b hb
    rw [he,hz,zero_smul]
  exact ⟨a,hn,he⟩

theorem normalForm_dual_kernel6 (v : Fin 6 → Fin 6 → ℤ)
    (hv : LinearIndependent ℚ (fun j i => (v j i : ℚ)))
    (b : Fin 6 → ℤ) (hb : b ≠ 0)
    (hline : Submodule.span ℚ {dualVector6 v hv} =
      Submodule.span ℚ {fun i => (b i : ℚ)}) :
    LinearMap.ker (normalForm6 b) = firstFiveSpan42 (fun j i => (v j i : ℚ)) := by
  obtain ⟨a,ha,he⟩ := normalForm_of_dual_line6 v hv b hb hline
  rw [he,LinearMap.ker_smul _ _ ha,lastDual42_kernel]

theorem nonzero_functionals_same_kernel {K E : Type*} [Field K] [AddCommGroup E]
    [Module K E] (f g : Module.Dual K E) (hf : f ≠ 0) (hg : g ≠ 0)
    (hker : LinearMap.ker f = LinearMap.ker g) :
    ∃ a : K, a ≠ 0 ∧ f = a • g := by
  obtain ⟨y,hy⟩ : ∃ y, g y ≠ 0 := by
    by_contra hn
    push_neg at hn
    exact hg (LinearMap.ext hn)
  let z := (g y)⁻¹ • y
  have hgz : g z = 1 := by simp [z,hy]
  have hvan (x : E) : f (x - g x • z) = 0 := by
    have hmem : x - g x • z ∈ LinearMap.ker g := by
      simp only [LinearMap.mem_ker,map_sub,map_smul,smul_eq_mul,hgz,mul_one,sub_self]
    exact (show x - g x • z ∈ LinearMap.ker f from hker.symm ▸ hmem)
  have he : f = f z • g := by
    ext x
    have h := hvan x
    simp only [map_sub,map_smul,smul_eq_mul,sub_eq_zero] at h
    simpa only [LinearMap.smul_apply,smul_eq_mul,mul_comm] using h
  have hn : f z ≠ 0 := by
    intro hz
    exact hf (by rw [he,hz,zero_smul])
  exact ⟨f z,hn,he⟩

theorem dual_pairing_unique42 (u : Fin 4 → Fin 4 → ℚ) (hu : LinearIndependent ℚ u)
    (U : Fin 4 → Module.Dual ℚ (Fin 4 → ℚ))
    (hU : ∀ i j, U i (u j) = if j = i then 1 else 0) :
    U = (fun i => rationalFrameDual42 u hu i) := by
  funext i
  apply (rationalFrameBasis42 u hu).ext
  intro j
  rw [rationalFrameBasis42_apply,hU,rationalFrameDual42_pairing]

theorem canonical_wedge_kernel42 (u : Fin 4 → Fin 4 → ℤ) (v : Fin 6 → Fin 6 → ℤ)
    (a : Fin 4 → ℝ) (hu : LinearIndependent ℚ (fun j i => (u j i : ℚ)))
    (hdual : rationalDualLine42 u v a) :
    let g := wedgeDual42 (rationalFrameDual42 (fun j i => (u j i : ℚ)) hu 2)
      (rationalFrameDual42 (fun j i => (u j i : ℚ)) hu 3)
    g ≠ 0 ∧ LinearMap.ker g = firstFiveSpan42 (fun j i => (v j i : ℚ)) := by
  obtain ⟨U,W,hU,_,_,hgn,_,hk,_,_,_,_,_⟩ := hdual
  have he := dual_pairing_unique42 (fun j i => (u j i : ℚ)) hu U hU
  rw [he] at hgn hk
  exact ⟨hgn,hk⟩

theorem source_original_decomposable42
    {A2 A3 : Matrix (Fin 4) (Fin 4) ℚ} {L : Matrix (Fin 4) (Fin 4) ℝ}
    {hL : IsUnit L} {c0 c2 c3 : Fin 4 → ℝ} {delta4 : ℝ} {V : Set ℝ}
    {hQV : ∀ q ∈ V, 1 < q}
    (R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV)
    (q : V) (b : Fin 6 → ℤ) (hb : b ≠ 0)
    (hline : Submodule.span ℚ {dualVector6 (fun j => (R.w q j : Fin 6 → ℤ))
      (sourceFrameIndependent6 R q)} = Submodule.span ℚ {fun i => (b i : ℚ)})
    (u : Fin 4 → originalSourceGroup4 A2 A3 q.val c2 c3)
    (v : Fin 6 → directCompoundGroup42 A2 A3 q.val c2 c3) (kappa : ℝ)
    (hs : sourceHyperplane42 A2 A3 L hL q.val (hQV q.val q.property) c0 c2 c3 kappa u v)
    (hdual : rationalDualLine42 (fun i => (u i : Fin 4 → ℤ)) (fun j => (v j : Fin 6 → ℤ))
      (sourceMinima4 A2 A3 L hL q.val (hQV q.val q.property) c0 c2 c3))
    (hspan : firstFiveSpan42 (fun j i => ((R.w q j : Fin 6 → ℤ) i : ℚ)) =
      firstFiveSpan42 (fun j i => (orderedWedges42 (fun k => (u k : Fin 4 → ℤ))
        (sourceMinima4 A2 A3 L hL q.val (hQV q.val q.property) c0 c2 c3) j i : ℚ))) :
    let hu := integral_frame_rational_independent (fun i => (u i : Fin 4 → ℤ)) hs.1
    let g := wedgeDual42 (rationalFrameDual42 (fun j i => ((u j : Fin 4 → ℤ) i : ℚ)) hu 2)
      (rationalFrameDual42 (fun j i => ((u j : Fin 4 → ℤ) i : ℚ)) hu 3)
    g ≠ 0 ∧
    LinearMap.ker (normalForm6 b) = firstFiveSpan42 (fun j i => ((R.w q j : Fin 6 → ℤ) i : ℚ)) ∧
    LinearMap.ker g = LinearMap.ker (normalForm6 b) ∧
    ∃ a : ℚ, a ≠ 0 ∧ normalForm6 b = a • g := by
  let hu := integral_frame_rational_independent (fun i => (u i : Fin 4 → ℤ)) hs.1
  let g := wedgeDual42 (rationalFrameDual42 (fun j i => ((u j : Fin 4 → ℤ) i : ℚ)) hu 2)
    (rationalFrameDual42 (fun j i => ((u j : Fin 4 → ℤ) i : ℚ)) hu 3)
  obtain ⟨hgn,hgker⟩ := canonical_wedge_kernel42 (fun i => (u i : Fin 4 → ℤ))
    (fun j => (v j : Fin 6 → ℤ)) _ hu hdual
  have hfker := normalForm_dual_kernel6 (fun j => (R.w q j : Fin 6 → ℤ))
    (sourceFrameIndependent6 R q) b hb hline
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,he,_⟩ := hs
  have hk : LinearMap.ker g = LinearMap.ker (normalForm6 b) :=
    hgker.trans (he.symm.trans (hspan.symm.trans hfker.symm))
  obtain ⟨a,ha,heq⟩ := nonzero_functionals_same_kernel (normalForm6 b) g
    (normalForm_nonzero6 b hb) hgn hk.symm
  exact ⟨hgn,hfker,hk,a,ha,heq⟩

def omega42 (f : Module.Dual ℚ (Fin 6 → ℚ)) (x y : Fin 4 → ℚ) : ℚ := f (wedge x y)

theorem omega42_add_left (f : Module.Dual ℚ (Fin 6 → ℚ)) (x z y : Fin 4 → ℚ) :
    omega42 f (x+z) y = omega42 f x y + omega42 f z y := by
  unfold omega42
  rw [← map_add]
  apply congrArg f
  ext i
  simp only [wedge,Pi.add_apply]
  ring

theorem omega42_add_right (f : Module.Dual ℚ (Fin 6 → ℚ)) (x y z : Fin 4 → ℚ) :
    omega42 f x (y+z) = omega42 f x y + omega42 f x z := by
  unfold omega42
  rw [← map_add]
  apply congrArg f
  ext i
  simp only [wedge,Pi.add_apply]
  ring

theorem omega42_smul_left (f : Module.Dual ℚ (Fin 6 → ℚ)) (a : ℚ) (x y : Fin 4 → ℚ) :
    omega42 f (a • x) y = a • omega42 f x y := by
  unfold omega42
  rw [← map_smul]
  apply congrArg f
  ext i
  simp only [wedge,Pi.smul_apply,smul_eq_mul]
  ring

theorem omega42_smul_right (f : Module.Dual ℚ (Fin 6 → ℚ)) (a : ℚ) (x y : Fin 4 → ℚ) :
    omega42 f x (a • y) = a • omega42 f x y := by
  unfold omega42
  rw [← map_smul]
  apply congrArg f
  ext i
  simp only [wedge,Pi.smul_apply,smul_eq_mul]
  ring

theorem omega42_alternating (f : Module.Dual ℚ (Fin 6 → ℚ)) (x : Fin 4 → ℚ) :
    omega42 f x x = 0 := by
  have he : wedge x x = 0 := by ext i; dsimp [wedge]; ring
  exact (congrArg f he).trans f.map_zero

def radical42 (f : Module.Dual ℚ (Fin 6 → ℚ)) : Submodule ℚ (Fin 4 → ℚ) where
  carrier := {x | ∀ y, omega42 f x y = 0}
  zero_mem' := by
    intro y
    have hz : wedge (0 : Fin 4 → ℚ) y = 0 := by ext i; simp [wedge]
    exact (congrArg f hz).trans f.map_zero
  add_mem' := by
    intro x z hx hz y
    rw [omega42_add_left,hx y,hz y,add_zero]
  smul_mem' := by
    intro a x hx y
    rw [omega42_smul_left,hx y,smul_zero]

theorem radical_dual_mem42 (u : Fin 4 → Fin 4 → ℚ) (hu : LinearIndependent ℚ u)
    (a : ℚ) (ha : a ≠ 0) (x : Fin 4 → ℚ) :
    x ∈ radical42 (a • wedgeDual42 (rationalFrameDual42 u hu 2) (rationalFrameDual42 u hu 3)) ↔
      rationalFrameDual42 u hu 2 x = 0 ∧ rationalFrameDual42 u hu 3 x = 0 := by
  have hp (y : Fin 4 → ℚ) :
      omega42 (a • wedgeDual42 (rationalFrameDual42 u hu 2) (rationalFrameDual42 u hu 3)) x y =
        a * (rationalFrameDual42 u hu 2 x * rationalFrameDual42 u hu 3 y -
          rationalFrameDual42 u hu 2 y * rationalFrameDual42 u hu 3 x) := by
    simp only [omega42,LinearMap.smul_apply,smul_eq_mul,wedgeDual42_pairing]
  constructor
  · intro hx
    have h2 := hx (u 2)
    have h3 := hx (u 3)
    rw [hp] at h2 h3
    simp only [rationalFrameDual42_pairing,Fin.reduceEq,ite_true,ite_false,
      mul_zero,mul_one,zero_mul,one_mul,zero_sub,sub_zero] at h2 h3
    exact ⟨(mul_eq_zero.mp h3).resolve_left ha,
      neg_eq_zero.mp ((mul_eq_zero.mp h2).resolve_left ha)⟩
  · rintro ⟨h2,h3⟩ y
    rw [hp,h2,h3]
    ring

theorem radical_dual_eq_firstTwo42 (u : Fin 4 → Fin 4 → ℚ) (hu : LinearIndependent ℚ u)
    (a : ℚ) (ha : a ≠ 0) :
    radical42 (a • wedgeDual42 (rationalFrameDual42 u hu 2) (rationalFrameDual42 u hu 3)) =
      Submodule.span ℚ {u 0,u 1} := by
  apply le_antisymm
  · intro x hx
    obtain ⟨h2,h3⟩ := (radical_dual_mem42 u hu a ha x).mp hx
    have hc2 : (rationalFrameBasis42 u hu).repr x 2 = 0 := by
      rw [← Basis.dualBasis_apply]
      exact h2
    have hc3 : (rationalFrameBasis42 u hu).repr x 3 = 0 := by
      rw [← Basis.dualBasis_apply]
      exact h3
    have he : (rationalFrameBasis42 u hu).repr x 0 • u 0 +
        (rationalFrameBasis42 u hu).repr x 1 • u 1 = x := by
      simpa [Fin.sum_univ_succ,hc2,hc3,rationalFrameBasis42_apply] using
        (rationalFrameBasis42 u hu).sum_repr x
    rw [← he]
    exact Submodule.add_mem _
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  · apply Submodule.span_le.mpr
    intro x hx
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl <;>
      apply (radical_dual_mem42 u hu a ha _).mpr <;> simp [rationalFrameDual42_pairing]

theorem firstTwo_finrank42 (u : Fin 4 → Fin 4 → ℚ) (hu : LinearIndependent ℚ u) :
    Module.finrank ℚ (Submodule.span ℚ {u 0,u 1}) = 2 := by
  let j : Fin 2 → Fin 4 := Fin.castLE (by decide : 2 ≤ 4)
  have hj : Function.Injective j := Fin.castLE_injective _
  have he : Set.range (fun i : Fin 2 => u (j i)) = {u 0,u 1} := by
    ext x
    constructor
    · rintro ⟨i,rfl⟩
      fin_cases i <;> simp [j]
    · intro hx
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact ⟨0,rfl⟩
      · exact ⟨1,rfl⟩
  rw [← he]
  simpa only [Fintype.card_fin] using finrank_span_eq_card (hu.comp j hj)

theorem radical_dual_finrank42 (u : Fin 4 → Fin 4 → ℚ) (hu : LinearIndependent ℚ u)
    (a : ℚ) (ha : a ≠ 0) :
    Module.finrank ℚ (radical42 (a • wedgeDual42 (rationalFrameDual42 u hu 2)
      (rationalFrameDual42 u hu 3))) = 2 := by
  rw [radical_dual_eq_firstTwo42 u hu a ha]
  exact firstTwo_finrank42 u hu

theorem radical_normal_mem42 (b : Fin 6 → ℤ) (x : Fin 4 → ℚ) :
    x ∈ radical42 (normalForm6 b) ↔ ∀ y : Fin 4 → ℚ,
      (∑ i : Fin 6, (b i : ℚ) * (x (lo i)*y (hi i)-x (hi i)*y (lo i))) = 0 := by
  change (∀ y : Fin 4 → ℚ, normalForm6 b (wedge x y) = 0) ↔ _
  simp only [normalForm6_apply,wedge]

theorem source_original_fixed_plane42 (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (h2 : A2.det = 1) (h3 : A3.det = 1)
    (hL : L.det = 1) (hAlg : ∀ i j, IsAlgebraic ℚ (L i j))
    (delta4 : ℝ) (hd : 0 < delta4) (c0 c2 c3 : Fin 4 → ℝ)
    (hc0 : ∀ i, |c0 i| ≤ 1) (hc2 : ∀ i, -1 ≤ c2 i ∧ c2 i ≤ 0)
    (hc3 : ∀ i, -1 ≤ c3 i ∧ c3 i ≤ 0) (hbalance : (∑ i, (c0 i+c2 i+c3 i)) = 0)
    (U : Set ℝ) (hU : ¬ BddAbove U) (hQU : ∀ q ∈ U, 1 < q)
    (hgap : ∀ (q : ℝ) (hq : q ∈ U),
      sourceMinima4 A2 A3 L (sourceUnit42 L hL) q (hQU q hq) c0 c2 c3 1 <
      sourceMinima4 A2 A3 L (sourceUnit42 L hL) q (hQU q hq) c0 c2 c3 2 * q^(-delta4)) :
    ∃ (V : Set ℝ) (hVU : V ⊆ U)
      (R : SourceReadiness42 A2 A3 L (sourceUnit42 L hL) c0 c2 c3 delta4 V
        (fun q hq => hQU q (hVU hq)))
      (u : (q : V) → Fin 4 → originalSourceGroup4 A2 A3 q.val c2 c3)
      (v : (q : V) → Fin 6 → directCompoundGroup42 A2 A3 q.val c2 c3)
      (sigma : V → Equiv.Perm (Fin 6))
      (w : (q : V) → Fin 6 → directCompoundGroup42 A2 A3 q.val c2 c3)
      (kappa B : ℝ) (q1 : V) (b : Fin 6 → ℤ) (P : Submodule ℚ (Fin 4 → ℚ)),
      (¬ BddAbove V ∧
      fixedSourceWeights42 A2 A3 L (sourceUnit42 L hL) c0 c2 c3 delta4 V
        (fun q hq => hQU q (hVU hq)) ∧
      R.w = w ∧ R.sigma = sigma ∧
      (∃ q0 : V, R.c = fixedWeights
        (fun i => logWeight (q0.val^(11 : ℕ)) (actualWidths A2 A3 L (sourceUnit42 L hL)
          q0.val (hQU q0.val (hVU q0.property)) c0 c2 c3 (sigma q0) i))
        (finiteWeight c2) (finiteWeight c3)) ∧
      ∀ q : V,
        sourceHyperplane42 A2 A3 L (sourceUnit42 L hL) q.val (hQU q.val (hVU q.property))
          c0 c2 c3 kappa (u q) (v q) ∧
        rationalDualLine42 (fun i => (u q i : Fin 4 → ℤ)) (fun j => (v q j : Fin 6 → ℤ))
          (sourceMinima4 A2 A3 L (sourceUnit42 L hL) q.val (hQU q.val (hVU q.property)) c0 c2 c3) ∧
        (firstFiveSpan42 (fun j i => ((R.w q j : Fin 6 → ℤ) i : ℚ)) =
          firstFiveSpan42 (fun j i => (orderedWedges42 (fun k => (u q k : Fin 4 → ℤ))
            (sourceMinima4 A2 A3 L (sourceUnit42 L hL) q.val (hQU q.val (hVU q.property)) c0 c2 c3) j i : ℚ))) ∧
        (firstFiveSpan42 (fun j i => ((w q j : Fin 6 → ℤ) i : ℚ)) =
          firstFiveSpan42 (fun j i => ((v q j : Fin 6 → ℤ) i : ℚ))) ∧
        orderedWedges42 (fun k => (u q k : Fin 4 → ℤ))
          (sourceMinima4 A2 A3 L (sourceUnit42 L hL) q.val (hQU q.val (hVU q.property)) c0 c2 c3) 5 =
            wedge (u q 2 : Fin 4 → ℤ) (u q 3 : Fin 4 → ℤ)) ∧
      b = sourceReference6 R q1 ∧ b ≠ 0 ∧ normalForm6 b ≠ 0 ∧
      P = radical42 (normalForm6 b) ∧ Module.finrank ℚ P = 2 ∧
      1 < B ∧ ¬ BddAbove {q : ℝ | q ∈ V ∧ B < q} ∧
      ∀ q : V, B < q.val →
        LinearMap.ker (normalForm6 b) = firstFiveSpan42 (fun j i => ((R.w q j : Fin 6 → ℤ) i : ℚ)) ∧
        ∃ hu : LinearIndependent ℚ (fun j i => ((u q j : Fin 4 → ℤ) i : ℚ)),
          let g := wedgeDual42 (rationalFrameDual42 (fun j i => ((u q j : Fin 4 → ℤ) i : ℚ)) hu 2)
            (rationalFrameDual42 (fun j i => ((u q j : Fin 4 → ℤ) i : ℚ)) hu 3)
          g ≠ 0 ∧ LinearMap.ker g = LinearMap.ker (normalForm6 b) ∧
          ∃ a : ℚ, a ≠ 0 ∧ normalForm6 b = a • g ∧
            P = Submodule.span ℚ {fun i => ((u q 0 : Fin 4 → ℤ) i : ℚ),
              fun i => ((u q 1 : Fin 4 → ℤ) i : ℚ)} := by
  obtain ⟨V,hVU,R,u,v,sigma,w,kappa,hprops⟩ := source_original_coupled_readiness42
    A2 A3 L h2 h3 hL hAlg delta4 hd c0 c2 c3 hc0 hc2 hc3 hbalance U hU hQU hgap
  obtain ⟨B,q1,hB,htail,hb,hline⟩ := source_satz51_selected6 R h2 h3 hL hc2 hc3
  let b := sourceReference6 R q1
  let P := radical42 (normalForm6 b)
  have hfn : normalForm6 b ≠ 0 := normalForm_nonzero6 b hb
  have hpoints (q : V) (hq : B < q.val) :
        LinearMap.ker (normalForm6 b) = firstFiveSpan42 (fun j i => ((R.w q j : Fin 6 → ℤ) i : ℚ)) ∧
        ∃ hu : LinearIndependent ℚ (fun j i => ((u q j : Fin 4 → ℤ) i : ℚ)),
          let g := wedgeDual42 (rationalFrameDual42 (fun j i => ((u q j : Fin 4 → ℤ) i : ℚ)) hu 2)
            (rationalFrameDual42 (fun j i => ((u q j : Fin 4 → ℤ) i : ℚ)) hu 3)
          g ≠ 0 ∧ LinearMap.ker g = LinearMap.ker (normalForm6 b) ∧
          ∃ a : ℚ, a ≠ 0 ∧ normalForm6 b = a • g ∧
            P = Submodule.span ℚ {fun i => ((u q 0 : Fin 4 → ℤ) i : ℚ),
              fun i => ((u q 1 : Fin 4 → ℤ) i : ℚ)} := by
    obtain ⟨hs,hdual,hspan,_,_⟩ := hprops.2.2.2.2.2 q
    let hu := integral_frame_rational_independent (fun j => (u q j : Fin 4 → ℤ)) hs.1
    obtain ⟨hgn,hfker,hgker,a,ha,hrel⟩ := source_original_decomposable42 R q b hb
      ((hline q hq).2.2.2.2) (u q) (v q) kappa hs hdual hspan
    have hP : P = Submodule.span ℚ {fun i => ((u q 0 : Fin 4 → ℤ) i : ℚ),
        fun i => ((u q 1 : Fin 4 → ℤ) i : ℚ)} := by
      change radical42 (normalForm6 b) = _
      rw [hrel]
      exact radical_dual_eq_firstTwo42
        (fun (j : Fin 4) (i : Fin 4) => ((u q j : Fin 4 → ℤ) i : ℚ)) hu a ha
    exact ⟨hfker,hu,hgn,hgker,a,ha,hrel,hP⟩
  have hdim : Module.finrank ℚ P = 2 := by
    obtain ⟨q,hq,_⟩ := not_bddAbove_iff.mp htail B
    obtain ⟨_,hu,_,_,a,ha,_,hP⟩ := hpoints ⟨q,hq.1⟩ hq.2
    rw [hP]
    exact firstTwo_finrank42
      (fun (j : Fin 4) (i : Fin 4) => ((u (⟨q,hq.1⟩ : V) j : Fin 4 → ℤ) i : ℚ)) hu
  exact ⟨V,hVU,R,u,v,sigma,w,kappa,B,q1,b,P,hprops,rfl,hb,hfn,rfl,hdim,hB,htail,hpoints⟩

end CompoundFeasibility.OriginalPlaneRecovery42
