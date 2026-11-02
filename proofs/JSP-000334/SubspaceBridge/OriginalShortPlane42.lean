import SubspaceBridge.OriginalPlaneRecovery42
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.OriginalShortPlane42
open OriginalPlaneRecovery42 SourceWeights SourceReadiness6 SourceNormalIndex SchlickeweiDualVanishing6
open SchlickeweiReference6 SchlickeweiRealCompletion6

def rationalFunctionalReal42 (f : Module.Dual ℚ (Fin 4 → ℚ)) : Module.Dual ℝ (Fin 4 → ℝ) :=
  ∑ i : Fin 4, (f (Pi.single i 1) : ℝ) • LinearMap.proj i

theorem rationalFunctionalReal42_cast (f : Module.Dual ℚ (Fin 4 → ℚ)) (x : Fin 4 → ℚ) :
    rationalFunctionalReal42 f (fun i => (x i : ℝ)) = (f x : ℝ) := by
  rw [functional_coordinates42 f x]
  simp only [rationalFunctionalReal42,LinearMap.sum_apply,LinearMap.smul_apply,
    LinearMap.proj_apply,smul_eq_mul,Rat.cast_sum,Rat.cast_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem integer_firstTwo_real_to_rat42 (u : Fin 4 → Fin 4 → ℤ)
    (hu : LinearIndependent ℝ (fun j => integerReal (u j))) (x : Fin 4 → ℤ)
    (hx : integerReal x ∈ Submodule.span ℝ {integerReal (u 0),integerReal (u 1)}) :
    (fun i => (x i : ℚ)) ∈ Submodule.span ℚ
      {fun i => (u 0 i : ℚ),fun i => (u 1 i : ℚ)} := by
  let uq : Fin 4 → Fin 4 → ℚ := fun j i => (u j i : ℚ)
  have huq : LinearIndependent ℚ uq := integral_frame_rational_independent u hu
  have hz (j : Fin 4) (hj : j = 2 ∨ j = 3) :
      rationalFrameDual42 uq huq j (fun i => (x i : ℚ)) = 0 := by
    let f := rationalFrameDual42 uq huq j
    have hker : Submodule.span ℝ {integerReal (u 0),integerReal (u 1)} ≤
        LinearMap.ker (rationalFunctionalReal42 f) := by
      apply Submodule.span_le.mpr
      intro z hz
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl <;> change rationalFunctionalReal42 f _ = 0
      · have he := rationalFunctionalReal42_cast f (uq 0)
        change rationalFunctionalReal42 f (integerReal (u 0)) = _ at he
        rw [he]
        rcases hj with rfl | rfl <;> simp [f,rationalFrameDual42_pairing]
      · have he := rationalFunctionalReal42_cast f (uq 1)
        change rationalFunctionalReal42 f (integerReal (u 1)) = _ at he
        rw [he]
        rcases hj with rfl | rfl <;> simp [f,rationalFrameDual42_pairing]
    have he := hker hx
    change rationalFunctionalReal42 f (integerReal x) = 0 at he
    have hc := rationalFunctionalReal42_cast f (fun i => (x i : ℚ))
    change rationalFunctionalReal42 f (integerReal x) = _ at hc
    rw [hc] at he
    exact_mod_cast he
  have hc2 : (rationalFrameBasis42 uq huq).repr (fun i => (x i : ℚ)) 2 = 0 := by
    rw [← Basis.dualBasis_apply]
    exact hz 2 (Or.inl rfl)
  have hc3 : (rationalFrameBasis42 uq huq).repr (fun i => (x i : ℚ)) 3 = 0 := by
    rw [← Basis.dualBasis_apply]
    exact hz 3 (Or.inr rfl)
  have he : (rationalFrameBasis42 uq huq).repr (fun i => (x i : ℚ)) 0 • uq 0 +
      (rationalFrameBasis42 uq huq).repr (fun i => (x i : ℚ)) 1 • uq 1 =
        (fun i => (x i : ℚ)) := by
    simpa [Fin.sum_univ_succ,hc2,hc3,rationalFrameBasis42_apply] using
      (rationalFrameBasis42 uq huq).sum_repr (fun i => (x i : ℚ))
  rw [← he]
  exact Submodule.add_mem _
    (Submodule.smul_mem _ _ (Submodule.subset_span (by simp [uq])))
    (Submodule.smul_mem _ _ (Submodule.subset_span (by simp [uq])))

theorem integer_firstTwo_real_iff_rat42 (u : Fin 4 → Fin 4 → ℤ)
    (hu : LinearIndependent ℝ (fun j => integerReal (u j))) (x : Fin 4 → ℤ) :
    integerReal x ∈ Submodule.span ℝ {integerReal (u 0),integerReal (u 1)} ↔
      (fun i => (x i : ℚ)) ∈ Submodule.span ℚ
        {fun i => (u 0 i : ℚ),fun i => (u 1 i : ℚ)} := by
  constructor
  · exact integer_firstTwo_real_to_rat42 u hu x
  · intro hx
    obtain ⟨a,b,he⟩ := Submodule.mem_span_pair.mp hx
    apply Submodule.mem_span_pair.mpr
    refine ⟨(a : ℝ),(b : ℝ),?_⟩
    ext i
    have hi := congrFun he i
    change a * (u 0 i : ℚ) + b * (u 1 i : ℚ) = (x i : ℚ) at hi
    change (a : ℝ) * (u 0 i : ℝ) + (b : ℝ) * (u 1 i : ℝ) = (x i : ℝ)
    exact_mod_cast hi


theorem sourceMinima4_strict_third42 (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L) (q : ℝ) (hq : 1 < q)
    (c0 c2 c3 : Fin 4 → ℝ) (delta4 : ℝ) (hd : 0 < delta4)
    (hgap : sourceMinima4 A2 A3 L hL q hq c0 c2 c3 1 <
      sourceMinima4 A2 A3 L hL q hq c0 c2 c3 2 * q^(-delta4)) :
    ∀ i : Fin 4, i < 2 → sourceMinima4 A2 A3 L hL q hq c0 c2 c3 i <
      sourceMinima4 A2 A3 L hL q hq c0 c2 c3 2 := by
  obtain ⟨hp,hm⟩ := sourceMinima4_pos_mono A2 A3 L hL q hq c0 c2 c3
  have hr : q^(-delta4) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hq (neg_neg_of_pos hd)
  have h12 : sourceMinima4 A2 A3 L hL q hq c0 c2 c3 1 <
      sourceMinima4 A2 A3 L hL q hq c0 c2 c3 2 :=
    hgap.trans (by simpa only [mul_one] using mul_lt_mul_of_pos_left hr (hp 2))
  intro i hi
  exact (hm (show i ≤ 1 by omega)).trans_lt h12

theorem minimaFlag4_two_eq_span (u : Fin 4 → Fin 4 → ℝ) :
    minimaFlag4 u 2 = Submodule.span ℝ {u 0,u 1} := by
  change Submodule.span ℝ (Set.range (fun i : Fin 2 => u (Fin.castLE (by decide) i))) = _
  congr 1
  ext x
  constructor
  · rintro ⟨i,rfl⟩
    fin_cases i <;> simp
  · intro hx
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact ⟨0,rfl⟩
    · exact ⟨1,rfl⟩

theorem source_short_real_firstTwo42 (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L) (q : ℝ) (hq : 1 < q)
    (c0 c2 c3 : Fin 4 → ℝ) (delta4 : ℝ) (hd : 0 < delta4)
    (hgap : sourceMinima4 A2 A3 L hL q hq c0 c2 c3 1 <
      sourceMinima4 A2 A3 L hL q hq c0 c2 c3 2 * q^(-delta4))
    (u : Fin 4 → originalSourceGroup4 A2 A3 q c2 c3)
    (hu : LinearIndependent ℝ (fun j => integerReal (u j : Fin 4 → ℤ)))
    (hatt : ∀ j, coordinateGauge4 (originalCoordinates4 L hL q hq c0)
      (integerReal (u j : Fin 4 → ℤ)) = sourceMinima4 A2 A3 L hL q hq c0 c2 c3 j)
    (x : originalSourceGroup4 A2 A3 q c2 c3)
    (hx : coordinateGauge4 (originalCoordinates4 L hL q hq c0)
      (integerReal (x : Fin 4 → ℤ)) < sourceMinima4 A2 A3 L hL q hq c0 c2 c3 2) :
    integerReal (x : Fin 4 → ℤ) ∈ Submodule.span ℝ
      {integerReal (u 0 : Fin 4 → ℤ),integerReal (u 1 : Fin 4 → ℤ)} := by
  let b := sourceRealBasis4 A2 A3
    (fun i => Nat.ceil (JSP000334.qThreshold 2 q (c2 i)))
    (fun i => Nat.ceil (JSP000334.qThreshold 3 q (c3 i)))
  let e := originalCoordinates4 L hL q hq c0
  have hr (j : Fin 4) : sourceMinima4 A2 A3 L hL q hq c0 c2 c3 j =
      successiveRadius4 b e j := sourceMinima4_eq_radius A2 A3 L hL q hq c0 c2 c3 j
  have hmem (y : originalSourceGroup4 A2 A3 q c2 c3) :
      integerReal (y : Fin 4 → ℤ) ∈ lattice4Span b := by
    rw [sourceRealBasis4_span]
    exact ⟨(y : Fin 4 → ℤ),y.property,rfl⟩
  have hflag := lattice4Span_short_mem_minimaFlag b e
    (fun j => integerReal (u j : Fin 4 → ℤ)) hu (fun j => hmem (u j))
    (fun j => (hatt j).trans (hr j)) 2
    (fun i hi => by rw [← hr i,← hr 2]; exact
      sourceMinima4_strict_third42 A2 A3 L hL q hq c0 c2 c3 delta4 hd hgap i hi)
    (integerReal (x : Fin 4 → ℤ)) (hmem x) (by rw [← hr 2]; exact hx)
  rw [minimaFlag4_two_eq_span] at hflag
  exact hflag

theorem source_short_rational_firstTwo42 (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L) (q : ℝ) (hq : 1 < q)
    (c0 c2 c3 : Fin 4 → ℝ) (delta4 : ℝ) (hd : 0 < delta4)
    (hgap : sourceMinima4 A2 A3 L hL q hq c0 c2 c3 1 <
      sourceMinima4 A2 A3 L hL q hq c0 c2 c3 2 * q^(-delta4))
    (u : Fin 4 → originalSourceGroup4 A2 A3 q c2 c3)
    (hu : LinearIndependent ℝ (fun j => integerReal (u j : Fin 4 → ℤ)))
    (hatt : ∀ j, coordinateGauge4 (originalCoordinates4 L hL q hq c0)
      (integerReal (u j : Fin 4 → ℤ)) = sourceMinima4 A2 A3 L hL q hq c0 c2 c3 j)
    (x : originalSourceGroup4 A2 A3 q c2 c3)
    (hx : coordinateGauge4 (originalCoordinates4 L hL q hq c0)
      (integerReal (x : Fin 4 → ℤ)) < sourceMinima4 A2 A3 L hL q hq c0 c2 c3 2) :
    (fun i => ((x : Fin 4 → ℤ) i : ℚ)) ∈ Submodule.span ℚ
      {fun i => ((u 0 : Fin 4 → ℤ) i : ℚ),fun i => ((u 1 : Fin 4 → ℤ) i : ℚ)} := by
  exact integer_firstTwo_real_to_rat42 (fun j => (u j : Fin 4 → ℤ)) hu
    (x : Fin 4 → ℤ)
    (source_short_real_firstTwo42 A2 A3 L hL q hq c0 c2 c3 delta4 hd hgap u hu hatt x hx)


theorem source_original_short_in_fixed_plane42 (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ)
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
      ((¬ BddAbove V ∧
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
              fun i => ((u q 1 : Fin 4 → ℤ) i : ℚ)}) ∧
      ∀ q : V, B < q.val → ∀ x : originalSourceGroup4 A2 A3 q.val c2 c3,
        coordinateGauge4 (originalCoordinates4 L (sourceUnit42 L hL)
          q.val (hQU q.val (hVU q.property)) c0) (integerReal (x : Fin 4 → ℤ)) <
          sourceMinima4 A2 A3 L (sourceUnit42 L hL)
            q.val (hQU q.val (hVU q.property)) c0 c2 c3 2 →
        (fun i => ((x : Fin 4 → ℤ) i : ℚ)) ∈ P := by
  obtain ⟨V,hVU,R,u,v,sigma,w,kappa,B,q1,b,P,hrest⟩ := source_original_fixed_plane42
    A2 A3 L h2 h3 hL hAlg delta4 hd c0 c2 c3 hc0 hc2 hc3 hbalance U hU hQU hgap
  refine ⟨V,hVU,R,u,v,sigma,w,kappa,B,q1,b,P,hrest,?_⟩
  intro q hq x hx
  obtain ⟨hprops,_,_,_,_,_,_,_,hpoints⟩ := hrest
  have hs := (hprops.2.2.2.2.2 q).1
  obtain ⟨_,hu,_,_,a,ha,_,hplane⟩ := hpoints q hq
  rw [hplane]
  exact source_short_rational_firstTwo42 A2 A3 L (sourceUnit42 L hL)
    q.val (hQU q.val (hVU q.property)) c0 c2 c3 delta4 hd
    (hgap q.val (hVU q.property)) (u q) hs.1 hs.2.1 x hx

end CompoundFeasibility.OriginalShortPlane42
