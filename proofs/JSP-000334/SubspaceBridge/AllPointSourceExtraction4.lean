import SubspaceBridge.NonrothAttainmentFlag4
import SubspaceBridge.AllPointFixedFamily3
open scoped BigOperators Classical Matrix
namespace JSP000334
open CompoundFeasibility CompoundFeasibility.OriginalFlagAssembly4
open CompoundFeasibility.OriginalShortPlane42

theorem allpoint_rank_scalar4 (a b c d g t q C : ℝ)
    (ha : 0<a) (hb : 0<b) (hc : 0<c) (hd : 0<d) (ht : 0<t) (hq : 1≤q)
    (hab : a≤b) (hbc : b≤c) (hcd : c≤d) (hag : a≤g) (hgt : g≤t)
    (hp : C≤a*b*c*d) (hcut : t^4*q^12<C) :
    (c*q<d ∧ g<d) ∨ (b*q<c ∧ g<c) ∨ (a*q<b ∧ g<b) := by
  have hq0 : 0<q := lt_of_lt_of_le zero_lt_one hq
  have hbig : t*q^3<d := by
    by_contra hh
    have hdle : d≤t*q^3 := le_of_not_gt hh
    have hp1 : a*b*c*d≤d^4 := by
      have h1 := mul_le_mul (hab.trans (hbc.trans hcd)) (hbc.trans hcd) hb.le hd.le
      have h2 := mul_le_mul hcd le_rfl hd.le hd.le
      have h3 := mul_le_mul h1 h2 (mul_pos hc hd).le (mul_nonneg hd.le hd.le)
      nlinarith only [h3]
    have hpow := pow_le_pow_left₀ hd.le hdle 4
    have he : (t*q^3)^4=t^4*q^12 := by ring
    rw [he] at hpow
    exact (not_lt_of_ge (hp.trans (hp1.trans hpow))) hcut
  have hq2 : 1≤q^2 := by nlinarith
  have hq3 : 1≤q^3 := by nlinarith [mul_le_mul_of_nonneg_right hq2 hq0.le]
  have htd : t<d := (by nlinarith : t≤t*q^3).trans_lt hbig
  by_cases h3 : c*q<d
  · exact Or.inl ⟨h3,hgt.trans_lt htd⟩
  have hdq : d≤c*q := le_of_not_gt h3
  have htc : t*q^2<c := by
    have hh := hbig.trans_le hdq
    have he : t*q^3=(t*q^2)*q := by ring
    rw [he] at hh
    exact (mul_lt_mul_right hq0).mp hh
  have hgc : g<c := hgt.trans_lt ((by nlinarith : t≤t*q^2).trans_lt htc)
  by_cases h2 : b*q<c
  · exact Or.inr (Or.inl ⟨h2,hgc⟩)
  have hcq : c≤b*q := le_of_not_gt h2
  have htb : t*q<b := by
    have hh := htc.trans_le hcq
    have he : t*q^2=(t*q)*q := by ring
    rw [he] at hh
    exact (mul_lt_mul_right hq0).mp hh
  have hgb : g<b := hgt.trans_lt ((by nlinarith : t≤t*q).trans_lt htb)
  have haq : a*q<b := (mul_le_mul_of_nonneg_right (hag.trans hgt) hq0.le).trans_lt htb
  exact Or.inr (Or.inr ⟨haq,hgb⟩)

open CompoundFeasibility CompoundFeasibility.OriginalFlagAssembly4
open CompoundFeasibility.OriginalShortPlane42

theorem allpoint_rational_flag4 (w : Fin 4 → Fin 4 → ℤ)
    (hw : LinearIndependent ℝ (fun j => integerReal (w j))) (k : Fin 4) (z : Fin 4 → ℤ)
    (hz : integerReal z ∈ minimaFlag4 (fun j => integerReal (w j)) k) :
    (fun i => (z i : ℚ)) ∈ originalFirstFlag4 k w := by
  classical
  let v : Fin 4 → Fin 4 → ℚ := fun j i => (w j i : ℚ)
  have hQ : LinearIndependent ℚ v := integral_frame_rational_independent w hw
  let b := rationalFrameBasis42 v hQ
  have hb (i : Fin 4) : b i=v i := rationalFrameBasis42_apply v hQ i
  have hzero (j : Fin 4) (hj : k≤j) : b.repr (fun i => (z i : ℚ)) j=0 := by
    let f := rationalFrameDual42 v hQ j
    have hk : minimaFlag4 (fun i => integerReal (w i)) k ≤
        LinearMap.ker (rationalFunctionalReal42 f) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i,rfl⟩
      have hij : (Fin.castLE (by omega) i : Fin 4)≠j := by
        intro he
        have hh := congrArg Fin.val he
        change i.val=j.val at hh
        have hi := i.isLt
        change k.val≤j.val at hj
        omega
      change rationalFunctionalReal42 f (integerReal (w (Fin.castLE (by omega) i)))=0
      have he := rationalFunctionalReal42_cast f (v (Fin.castLE (by omega) i))
      change rationalFunctionalReal42 f (integerReal (w (Fin.castLE (by omega) i)))=_ at he
      rw [he]
      simp [f,rationalFrameDual42_pairing,hij]
    have hh := hk hz
    change rationalFunctionalReal42 f (integerReal z)=0 at hh
    have he := rationalFunctionalReal42_cast f (fun i => (z i : ℚ))
    change rationalFunctionalReal42 f (integerReal z)=_ at he
    rw [he] at hh
    have hf : f (fun i => (z i : ℚ))=0 := by exact_mod_cast hh
    rw [← Basis.dualBasis_apply]
    exact hf
  rw [← b.sum_repr (fun i => (z i : ℚ))]
  apply Submodule.sum_mem
  intro i _
  by_cases hi : i.val<k.val
  · apply Submodule.smul_mem
    rw [hb]
    apply Submodule.subset_span
    exact ⟨⟨i.val,hi⟩,rfl⟩
  · rw [hzero i (by omega),zero_smul]
    exact Submodule.zero_mem _

theorem allpoint_source_short_rational4 (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L) (Q : ℝ) (hQ : 1<Q)
    (c0 c2 c3 : Fin 4 → ℝ) (k : Fin 4)
    (u : Fin 4 → originalSourceGroup4 A2 A3 Q c2 c3)
    (hu : OriginalAttainmentFlag4.ambientFrame4 A2 A3 L hL Q hQ c0 c2 c3 u)
    (hgap : ∀ i : Fin 4,i<k → sourceMinima4 A2 A3 L hL Q hQ c0 c2 c3 i<
      sourceMinima4 A2 A3 L hL Q hQ c0 c2 c3 k)
    (z : originalSourceGroup4 A2 A3 Q c2 c3)
    (hz : coordinateGauge4 (originalCoordinates4 L hL Q hQ c0) (integerReal (z : Fin 4 → ℤ))<
      sourceMinima4 A2 A3 L hL Q hQ c0 c2 c3 k) :
    (fun i => ((z : Fin 4 → ℤ) i : ℚ)) ∈ originalFirstFlag4 k (fun j => (u j : Fin 4 → ℤ)) := by
  let b := sourceRealBasis4 A2 A3
    (fun i => Nat.ceil (qThreshold 2 Q (c2 i))) (fun i => Nat.ceil (qThreshold 3 Q (c3 i)))
  let e := originalCoordinates4 L hL Q hQ c0
  have hr (j : Fin 4) : sourceMinima4 A2 A3 L hL Q hQ c0 c2 c3 j=successiveRadius4 b e j :=
    sourceMinima4_eq_radius A2 A3 L hL Q hQ c0 c2 c3 j
  have hmem (x : originalSourceGroup4 A2 A3 Q c2 c3) : integerReal (x : Fin 4 → ℤ)∈lattice4Span b := by
    rw [sourceRealBasis4_span]
    exact ⟨(x : Fin 4 → ℤ),x.property,rfl⟩
  apply allpoint_rational_flag4 _ hu.1 k _
  apply lattice4Span_short_mem_minimaFlag b e _ hu.1 (fun i => hmem (u i))
    (fun i => (hu.2 i).trans (hr i)) k
  · intro i hi
    rw [← hr i,← hr k]
    exact hgap i hi
  · exact hmem z
  · rw [← hr k]
    exact hz

theorem allpoint_fixed_source_family4
    (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ)
    (h2 : A2.det=1) (h3 : A3.det=1) (hL : L.det=1)
    (hAlg : ∀ i j,IsAlgebraic ℚ (L i j))
    (c0 c2 c3 : Fin 4 → ℝ) (hc0 : ∀ i,|c0 i|≤1)
    (hc2 : ∀ i,-1≤c2 i ∧ c2 i≤0) (hc3 : ∀ i,-1≤c3 i ∧ c3 i≤0)
    (hb : ∑ i,(c0 i+c2 i+c3 i)=0) (epsilon : ℝ) (he : 0<epsilon)
    (Omega : Set ℝ) (hO : ¬BddAbove Omega) (hQ : ∀ Q∈Omega,1<Q)
    (z : Omega → Fin 4 → ℤ)
    (hz : ∀ Q : Omega,OriginalVariableGap4.originalSourceSolution4 A2 A3 L c0 c2 c3 Q.val epsilon (z Q)) :
    ∃ P : Submodule ℚ (Fin 4 → ℚ),P≠⊤ ∧ ∃ W : Set ℝ,W⊆Omega ∧ ¬BddAbove W ∧
      ∀ Q : Omega,Q.val∈W → (fun i => (z Q i : ℚ))∈P := by
  classical
  obtain ⟨C,D,hC,hD,hbounds⟩ := OriginalMinimaProduct4.source_original_uniform_minima_two_sided4
    A2 A3 L (sourceUnit42 A2 h2) (sourceUnit42 A3 h3) (sourceUnit42 L hL)
  obtain ⟨B,hB,hcut⟩ := OriginalVariableGap4.first_minimum_cutoff4 C (13*epsilon/4) hC (by positivity)
  let T : Set ℝ := {Q | Q∈Omega ∧ B<Q}
  have hT : ¬BddAbove T := sourceDual_unbounded_tail3 Omega hO B
  let emb (Q : T) : Omega := ⟨Q.val,Q.property.1⟩
  let lam (Q : T) := sourceMinima4 A2 A3 L (sourceUnit42 L hL) Q.val
    (hQ _ Q.property.1) c0 c2 c3
  let g (Q : T) := coordinateGauge4 (originalCoordinates4 L (sourceUnit42 L hL) Q.val
    (hQ _ Q.property.1) c0) (integerReal (z (emb Q)))
  have hdata (Q : T) : ∃ j : Fin 3,lam Q j.castSucc<lam Q j.succ*Q.val^(-(epsilon/16)) ∧ g Q<lam Q j.succ := by
    have hq0 : 0<Q.val := (zero_lt_one.trans (hQ _ Q.property.1))
    have hp := sourceMinima4_pos_mono A2 A3 L (sourceUnit42 L hL) Q.val (hQ _ Q.property.1) c0 c2 c3
    have hmem := OriginalVariableGap4.source_solution_lattice4 A2 A3 L c0 c2 c3
      (fun i => (hc2 i).2) (fun i => (hc3 i).2) Q.val epsilon (z (emb Q)) (hz (emb Q))
    have hfirst := OriginalVariableGap4.source_first_minimum_le_gauge4 A2 A3 L (sourceUnit42 L hL)
      c0 c2 c3 Q.val (hQ _ Q.property.1) (z (emb Q)) (hz (emb Q)).1 hmem
    have hs := OriginalVariableGap4.source_solution_gauge4 A2 A3 L (sourceUnit42 L hL)
      c0 c2 c3 Q.val epsilon (hQ _ Q.property.1) (z (emb Q)) (hz (emb Q))
    have hprod : C≤lam Q 0*lam Q 1*lam Q 2*lam Q 3 := by
      simpa [Fin.prod_univ_succ,mul_assoc,lam] using
        (hbounds Q.val (hQ _ Q.property.1) c0 c2 c3 (fun i => (hc2 i).2) (fun i => (hc3 i).2) hb).1
    have htail : (Q.val^(-epsilon))^4*(Q.val^(epsilon/16))^12<C := by
      have hid : (Q.val^(-epsilon))^4*(Q.val^(epsilon/16))^12=Q.val^(-(13*epsilon/4)) := by
        rw [← Real.rpow_mul_natCast hq0.le,← Real.rpow_mul_natCast hq0.le,← Real.rpow_add hq0]
        congr 1
        ring
      rw [hid]
      exact hcut Q.val Q.property.2
    have hq : 1≤Q.val^(epsilon/16) := Real.one_le_rpow (hQ _ Q.property.1).le (by positivity)
    have hconvert (a b : ℝ) (h : a*Q.val^(epsilon/16)<b) : a<b*Q.val^(-(epsilon/16)) := by
      rw [Real.rpow_neg hq0.le]
      exact (lt_div_iff₀ (Real.rpow_pos_of_pos hq0 _)).mpr h
    obtain h|h|h := allpoint_rank_scalar4 (lam Q 0) (lam Q 1) (lam Q 2) (lam Q 3) (g Q)
      (Q.val^(-epsilon)) (Q.val^(epsilon/16)) C (hp.1 0) (hp.1 1) (hp.1 2) (hp.1 3)
      (Real.rpow_pos_of_pos hq0 _) hq (hp.2 (by decide)) (hp.2 (by decide)) (hp.2 (by decide))
      hfirst hs hprod htail
    · exact ⟨2,hconvert _ _ h.1,h.2⟩
    · exact ⟨1,hconvert _ _ h.1,h.2⟩
    · exact ⟨0,hconvert _ _ h.1,h.2⟩
  choose j hj hs using hdata
  let f (Q : ℝ) : Fin 3 := if h : Q∈T then j ⟨Q,h⟩ else 0
  obtain ⟨r,_,hU⟩ := allpoint_finite_parameter_fiber3 (Set.univ : Set (Fin 3)) Set.finite_univ T hT f (by intros; trivial)
  let U : Set ℝ := {Q | Q∈T ∧ f Q=r}
  let orig (Q : U) : T := ⟨Q.val,Q.property.1⟩
  have hr (Q : U) : j (orig Q)=r := by simpa only [f,dif_pos Q.property.1,orig] using Q.property.2
  have hQU : ∀ Q∈U,1<Q := fun Q h => hQ Q h.1.1
  have hgap (Q : U) : sourceMinima4 A2 A3 L (sourceUnit42 L hL) Q.val (hQU _ Q.property) c0 c2 c3 r.castSucc<
      sourceMinima4 A2 A3 L (sourceUnit42 L hL) Q.val (hQU _ Q.property) c0 c2 c3 r.succ*Q.val^(-(epsilon/16)) := by
    have hh := hj (orig Q)
    rw [hr Q] at hh
    exact hh
  obtain ⟨W,hWU,hW,P,hPdim,u,hu⟩ := OriginalAttainmentFlag4.source_selected_gap_attaining_flag4
    A2 A3 L h2 h3 hL hAlg (epsilon/16) (by positivity) c0 c2 c3 hc0 hc2 hc3 hb U hU hQU r
    (fun Q h => hgap ⟨Q,h⟩)
  have hP : P≠⊤ := by
    intro htop
    have hfour : Module.finrank ℚ P=4 := by rw [htop,finrank_top]; simp
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
  rw [(hu q).1]
  have hmemQ := OriginalVariableGap4.source_solution_lattice4 A2 A3 L c0 c2 c3
    (fun i => (hc2 i).2) (fun i => (hc3 i).2) Q.val epsilon (z Q) (hz Q)
  refine allpoint_source_short_rational4 A2 A3 L (sourceUnit42 L hL) Q.val
    (hQU _ (hWU hQW)) c0 c2 c3 r.succ (u q) (hu q).2 ?_ ⟨z Q,hmemQ⟩ ?_
  · intro i hi
    have hpos := sourceMinima4_pos_mono A2 A3 L (sourceUnit42 L hL) Q.val (hQU _ (hWU hQW)) c0 c2 c3
    have hfac : Q.val^(-(epsilon/16))<1 := Real.rpow_lt_one_of_one_lt_of_neg (hQ _ Q.property) (by linarith)
    have hg := hgap o
    have hg' : lam (orig o) r.castSucc<lam (orig o) r.succ :=
      hg.trans (mul_lt_of_lt_one_right (hpos.1 r.succ) hfac)
    exact (hpos.2 (show i≤r.castSucc by
      change i.val≤r.val
      change i.val<r.val+1 at hi
      omega)).trans_lt hg'
  · exact hthreshold

end JSP000334
