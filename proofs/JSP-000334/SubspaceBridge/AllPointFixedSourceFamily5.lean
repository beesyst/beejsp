import SubspaceBridge.AllPointSourceExtraction5
open scoped BigOperators Classical Matrix
noncomputable section
namespace JSP000334
open CompoundFeasibility CompoundFeasibility.OriginalFlagAssembly5

theorem allpoint_minima_bounds5
    (A2 A3 : Matrix (Fin 5) (Fin 5) ℚ) (L : Matrix (Fin 5) (Fin 5) ℝ)
    (h2 : A2.det=1) (h3 : A3.det=1) (hLd : L.det=1)
    (c0 c2 c3 : Fin 5 → ℝ) (hc2 : ∀ i,c2 i≤0) (hc3 : ∀ i,c3 i≤0)
    (hb : ∑ i,(c0 i+c2 i+c3 i)=0) :
    ∃ hL : IsUnit L, ∃ C D : ℝ,0<C ∧ 0<D ∧
      ∀ (Q : ℝ) (hQ : 1<Q),
        C≤(∏ i,sourceMinima5 A2 A3 L hL Q hQ c0 c2 c3 i) ∧
        (∏ i,sourceMinima5 A2 A3 L hL Q hQ c0 c2 c3 i)≤D := by
  have h2u : IsUnit A2 := (Matrix.isUnit_iff_isUnit_det A2).mpr (by rw [h2]; exact isUnit_one)
  have h3u : IsUnit A3 := (Matrix.isUnit_iff_isUnit_det A3).mpr (by rw [h3]; exact isUnit_one)
  have hL : IsUnit L := (Matrix.isUnit_iff_isUnit_det L).mpr (by rw [hLd]; exact isUnit_one)
  obtain ⟨C,D,hC,hD,hbounds⟩ := source_original_uniform_minima_two_sided5 A2 A3 L h2u h3u hL
  exact ⟨hL,C,D,hC,hD,fun Q hQ => hbounds Q hQ c0 c2 c3 hc2 hc3 hb⟩

theorem allpoint_fixed_source_family5
    (A2 A3 : Matrix (Fin 5) (Fin 5) ℚ) (L : Matrix (Fin 5) (Fin 5) ℝ)
    (h2 : A2.det=1) (h3 : A3.det=1) (hL : L.det=1)
    (hAlg : ∀ i j,IsAlgebraic ℚ (L i j))
    (c0 c2 c3 : Fin 5 → ℝ) (hc0 : ∀ i,|c0 i|≤1)
    (hc2 : ∀ i,-1≤c2 i ∧ c2 i≤0) (hc3 : ∀ i,-1≤c3 i ∧ c3 i≤0)
    (hb : ∑ i,(c0 i+c2 i+c3 i)=0) (epsilon : ℝ) (he : 0<epsilon)
    (Omega : Set ℝ) (hO : ¬BddAbove Omega) (hQ : ∀ Q∈Omega,1<Q)
    (z : Omega → Fin 5 → ℤ)
    (hz : ∀ Q : Omega,OriginalVariableGap5.originalSourceSolution5 A2 A3 L c0 c2 c3 Q.val epsilon (z Q)) :
    ∃ P : Submodule ℚ (Fin 5 → ℚ),P≠⊤ ∧ ∃ W : Set ℝ,W⊆Omega ∧ ¬BddAbove W ∧
      ∀ Q : Omega,Q.val∈W → (fun i => (z Q i : ℚ))∈P := by
  classical
  obtain ⟨hLu,C,D,hC,hD,hbounds⟩ := allpoint_minima_bounds5 A2 A3 L h2 h3 hL c0 c2 c3
    (fun i => (hc2 i).2) (fun i => (hc3 i).2) hb
  obtain ⟨B,hB,hcut⟩ := OriginalVariableGap5.first_minimum_cutoff5 C (35*epsilon/8) hC (by positivity)
  let T : Set ℝ := {Q | Q∈Omega ∧ B<Q}
  have hT : ¬BddAbove T := sourceDual_unbounded_tail3 Omega hO B
  let emb (Q : T) : Omega := ⟨Q.val,Q.property.1⟩
  let lam (Q : T) := sourceMinima5 A2 A3 L hLu Q.val
    (hQ _ Q.property.1) c0 c2 c3
  let g (Q : T) := coordinateGauge5 (originalCoordinates5 L hLu Q.val
    (hQ _ Q.property.1) c0) (integerReal (z (emb Q)))
  have hdata (Q : T) : ∃ j : Fin 4,lam Q j.castSucc<lam Q j.succ*Q.val^(-(epsilon/32)) ∧ g Q<lam Q j.succ := by
    have hq0 : 0<Q.val := (zero_lt_one.trans (hQ _ Q.property.1))
    have hp := sourceMinima5_pos_mono A2 A3 L hLu Q.val (hQ _ Q.property.1) c0 c2 c3
    have hmem := OriginalVariableGap5.source_solution_lattice5 A2 A3 L c0 c2 c3
      (fun i => (hc2 i).2) (fun i => (hc3 i).2) Q.val epsilon (z (emb Q)) (hz (emb Q))
    have hfirst := OriginalVariableGap5.source_first_minimum_le_gauge5 A2 A3 L hLu
      c0 c2 c3 Q.val (hQ _ Q.property.1) (z (emb Q)) (hz (emb Q)).1 hmem
    have hs := OriginalVariableGap5.source_solution_gauge5 A2 A3 L hLu
      c0 c2 c3 Q.val epsilon (hQ _ Q.property.1) (z (emb Q)) (hz (emb Q))
    have hprod : C≤lam Q 0*lam Q 1*lam Q 2*lam Q 3*lam Q 4 := by
      simpa [Fin.prod_univ_succ,mul_assoc,lam] using
        (hbounds Q.val (hQ _ Q.property.1)).1
    have htail : (Q.val^(-epsilon))^5*(Q.val^(epsilon/32))^20<C := by
      have hid : (Q.val^(-epsilon))^5*(Q.val^(epsilon/32))^20=Q.val^(-(35*epsilon/8)) := by
        rw [← Real.rpow_mul_natCast hq0.le,← Real.rpow_mul_natCast hq0.le,← Real.rpow_add hq0]
        congr 1
        ring
      rw [hid]
      exact hcut Q.val Q.property.2
    have hq : 1≤Q.val^(epsilon/32) := Real.one_le_rpow (hQ _ Q.property.1).le (by positivity)
    have hconvert (a b : ℝ) (h : a*Q.val^(epsilon/32)<b) : a<b*Q.val^(-(epsilon/32)) := by
      rw [Real.rpow_neg hq0.le]
      exact (lt_div_iff₀ (Real.rpow_pos_of_pos hq0 _)).mpr h
    obtain h|h|h|h := allpoint_rank_scalar5 (lam Q 0) (lam Q 1) (lam Q 2) (lam Q 3) (lam Q 4) (g Q)
      (Q.val^(-epsilon)) (Q.val^(epsilon/32)) C (hp.1 0) (hp.1 1) (hp.1 2) (hp.1 3) (hp.1 4)
      (Real.rpow_pos_of_pos hq0 _) hq (hp.2 (by decide)) (hp.2 (by decide)) (hp.2 (by decide)) (hp.2 (by decide))
      hfirst hs hprod htail
    · exact ⟨3,hconvert _ _ h.1,h.2⟩
    · exact ⟨2,hconvert _ _ h.1,h.2⟩
    · exact ⟨1,hconvert _ _ h.1,h.2⟩
    · exact ⟨0,hconvert _ _ h.1,h.2⟩
  choose j hj hs using hdata
  let f (Q : ℝ) : Fin 4 := if h : Q∈T then j ⟨Q,h⟩ else 0
  obtain ⟨r,_,hU⟩ := allpoint_finite_parameter_fiber3 (Set.univ : Set (Fin 4)) Set.finite_univ T hT f (by intros; trivial)
  let U : Set ℝ := {Q | Q∈T ∧ f Q=r}
  let orig (Q : U) : T := ⟨Q.val,Q.property.1⟩
  have hr (Q : U) : j (orig Q)=r := by simpa only [f,dif_pos Q.property.1,orig] using Q.property.2
  have hQU : ∀ Q∈U,1<Q := fun Q h => hQ Q h.1.1
  have hgap (Q : U) : sourceMinima5 A2 A3 L hLu Q.val (hQU _ Q.property) c0 c2 c3 r.castSucc<
      sourceMinima5 A2 A3 L hLu Q.val (hQU _ Q.property) c0 c2 c3 r.succ*Q.val^(-(epsilon/32)) := by
    have hh := hj (orig Q)
    rw [hr Q] at hh
    exact hh
  obtain ⟨P,hPdim,W,hWU,hW,hframes⟩ := source_selected_gap_fixed_flag5
    A2 A3 L h2 h3 hL hLu hAlg c0 c2 c3 hc0 hc2 hc3 hb
    (epsilon/32) (by positivity) U hU hQU r (fun Q h => hgap ⟨Q,h⟩)
  have hP : P≠⊤ := by
    intro htop
    have hfive : Module.finrank ℚ P=5 := by rw [htop,finrank_top]; simp
    have hri := r.isLt
    change Module.finrank ℚ P=r.val+1 at hPdim
    omega
  refine ⟨P,hP,W,(fun Q h => (hWU h).1.1),hW,?_⟩
  intro Q hQW
  let q : W := ⟨Q.val,hQW⟩
  let o : U := ⟨Q.val,hWU hQW⟩
  have hthreshold : g (orig o)<lam (orig o) r.succ := by
    have hh := hs (orig o)
    rw [hr o] at hh
    exact hh
  obtain ⟨u,hu,ha,hflag⟩ := hframes Q.val hQW
  rw [hflag]
  have hmemQ := OriginalVariableGap5.source_solution_lattice5 A2 A3 L c0 c2 c3
    (fun i => (hc2 i).2) (fun i => (hc3 i).2) Q.val epsilon (z Q) (hz Q)
  refine allpoint_source_short_rational5 A2 A3 L hLu Q.val
    (hQU _ (hWU hQW)) c0 c2 c3 r u ⟨hu,ha⟩ ?_ ⟨z Q,hmemQ⟩ ?_
  · intro i hi
    have hpos := sourceMinima5_pos_mono A2 A3 L hLu Q.val (hQU _ (hWU hQW)) c0 c2 c3
    have hfac : Q.val^(-(epsilon/32))<1 := Real.rpow_lt_one_of_one_lt_of_neg (hQ _ Q.property) (by linarith)
    have hg := hgap o
    have hg' : lam (orig o) r.castSucc<lam (orig o) r.succ :=
      hg.trans (mul_lt_of_lt_one_right (hpos.1 r.succ) hfac)
    exact (hpos.2 (show i≤r.castSucc by
      change i.val≤r.val
      change i.val<r.val+1 at hi
      omega)).trans_lt hg'
  · exact hthreshold


end JSP000334
