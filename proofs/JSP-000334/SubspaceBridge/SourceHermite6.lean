import SubspaceBridge.SourceNormalIndex6
import Mathlib.Algebra.MvPolynomial.Equiv
open scoped BigOperators Classical
noncomputable section
namespace CompoundFeasibility.SourceHermite
open SourceNormalIndex
variable {K : Type*} [Field K]

def gridJet6 {n : ℕ} (P : MvPolynomial (Fin n) K) (J : Fin n → ℕ) (x : Fin n → K) : K :=
  P.sum fun d c => c * ∏ i, (Nat.choose (d i) (J i) : K)*x i^(d i-J i)

theorem gridJet6_add {n : ℕ} (P Q : MvPolynomial (Fin n) K)
    (J : Fin n → ℕ) (x : Fin n → K) :
    gridJet6 (P+Q) J x = gridJet6 P J x + gridJet6 Q J x := by
  unfold gridJet6
  exact Finsupp.sum_add_index (by intros; simp) (by intros; ring)

theorem gridJet6_monomial {n : ℕ} (d : Fin n →₀ ℕ) (c : K)
    (J : Fin n → ℕ) (x : Fin n → K) :
    gridJet6 (MvPolynomial.monomial d c) J x =
      c * ∏ i, (Nat.choose (d i) (J i) : K)*x i^(d i-J i) := by
  simp [gridJet6,MvPolynomial.sum_monomial_eq]

def coordinateJetPolynomial6 {n : ℕ} (P : Polynomial (MvPolynomial (Fin n) K))
    (J : Fin n → ℕ) (x : Fin n → K) : Polynomial K :=
  P.sum fun k c => Polynomial.monomial k (gridJet6 c J x)

theorem coordinateJetPolynomial6_coeff {n : ℕ}
    (P : Polynomial (MvPolynomial (Fin n) K)) (J : Fin n → ℕ) (x : Fin n → K) (k : ℕ) :
    (coordinateJetPolynomial6 P J x).coeff k = gridJet6 (P.coeff k) J x := by
  classical
  unfold coordinateJetPolynomial6
  rw [Polynomial.sum_def,Polynomial.finset_sum_coeff]
  simp only [Polynomial.coeff_monomial]
  rw [Finset.sum_eq_single k]
  · simp
  · intro b hb hbk
    simp [hbk]
  · intro hk
    rw [Polynomial.not_mem_support_iff.mp hk]
    simp [gridJet6]

theorem finSucc_monomial_coeff6 {n : ℕ} (d : Fin (n+1) →₀ ℕ) (c : K)
    (k : ℕ) (e : Fin n →₀ ℕ) :
    MvPolynomial.coeff e ((MvPolynomial.finSuccEquiv K n (MvPolynomial.monomial d c)).coeff k) =
      MvPolynomial.coeff e ((Polynomial.monomial (d 0) (MvPolynomial.monomial d.tail c)).coeff k) := by
  rw [MvPolynomial.finSuccEquiv_coeff_coeff]
  have hd : d = e.cons k ↔ k = d 0 ∧ e = d.tail := by
    constructor
    · intro h; subst d; simp
    · rintro ⟨rfl,rfl⟩; exact (Finsupp.cons_tail d).symm
  by_cases hk : k = d 0
  · by_cases he : e = d.tail
    · have hde : d = e.cons k := hd.mpr ⟨hk,he⟩
      simp only [MvPolynomial.coeff_monomial,Polynomial.coeff_monomial,
        if_pos hde,if_pos hk.symm,if_pos he.symm]
    · have hne : d ≠ e.cons k := fun h => he (hd.mp h).2
      simp only [MvPolynomial.coeff_monomial,Polynomial.coeff_monomial,
        if_neg hne,if_pos hk.symm,if_neg (Ne.symm he)]
  · have hne : d ≠ e.cons k := fun h => hk (hd.mp h).1
    by_cases he : e = d.tail
    · simp only [MvPolynomial.coeff_monomial,Polynomial.coeff_monomial,
        if_neg hne,if_neg (Ne.symm hk),MvPolynomial.coeff_zero]
    · simp only [MvPolynomial.coeff_monomial,Polynomial.coeff_monomial,
        if_neg hne,if_neg (Ne.symm hk),MvPolynomial.coeff_zero]


theorem gridJet6_coordinate_split {n : ℕ} (P : MvPolynomial (Fin (n+1)) K)
    (j : ℕ) (J : Fin n → ℕ) (a : K) (x : Fin n → K) :
    gridJet6 P (Fin.cons j J) (Fin.cons a x) =
      (Polynomial.hasseDeriv j
        (coordinateJetPolynomial6 (MvPolynomial.finSuccEquiv K n P) J x)).eval a := by
  classical
  have hadd (P Q : Polynomial (MvPolynomial (Fin n) K)) :
      coordinateJetPolynomial6 (P+Q) J x =
        coordinateJetPolynomial6 P J x + coordinateJetPolynomial6 Q J x := by
    ext k
    simp only [coordinateJetPolynomial6_coeff,Polynomial.coeff_add,gridJet6_add]
  have hmono (k : ℕ) (c : MvPolynomial (Fin n) K) :
      coordinateJetPolynomial6 (Polynomial.monomial k c) J x =
        Polynomial.monomial k (gridJet6 c J x) := by
    ext l
    rw [coordinateJetPolynomial6_coeff]
    by_cases h : k = l
    · subst l; simp
    · simp [Polynomial.coeff_monomial,h,gridJet6]
  induction P using MvPolynomial.induction_on' with
  | add P Q hP hQ =>
    rw [gridJet6_add,map_add,hadd,map_add,Polynomial.eval_add,hP,hQ]
  | monomial d c =>
    have he : MvPolynomial.finSuccEquiv K n (MvPolynomial.monomial d c) =
        Polynomial.monomial (d 0) (MvPolynomial.monomial d.tail c) := by
      ext k e
      exact finSucc_monomial_coeff6 d c k e
    rw [gridJet6_monomial,he,hmono,gridJet6_monomial,Polynomial.hasseDeriv_monomial]
    simp only [Polynomial.eval_monomial,Fin.prod_univ_succ,Fin.cons_zero,Fin.cons_succ,Finsupp.tail_apply]
    ring


theorem gridJet6_zero {n : ℕ} (P : MvPolynomial (Fin n) K) (x : Fin n → K) :
    gridJet6 P (fun _ => 0) x = MvPolynomial.eval x P := by
  classical
  induction P using MvPolynomial.induction_on' with
  | add P Q hP hQ => rw [gridJet6_add,map_add,hP,hQ]
  | monomial d c =>
    simp [gridJet6_monomial,MvPolynomial.eval_monomial,Finsupp.prod_fintype]

theorem coordinateJetPolynomial6_degree {n : ℕ}
    (P : Polynomial (MvPolynomial (Fin n) K)) (J : Fin n → ℕ) (x : Fin n → K) :
    (coordinateJetPolynomial6 P J x).natDegree ≤ P.natDegree := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  rw [coordinateJetPolynomial6_coeff,Polynomial.coeff_eq_zero_of_natDegree_lt hk]
  simp [gridJet6]

theorem hermite_degree_budget6 (s k r t : ℕ) (hs : 0 < s) (hk : k ≤ r)
    (hsize : r < s*(t+1)) : k/s ≤ t ∧ r-k < s*(t-k/s+1) := by
  have hqt : k/s < t+1 := (Nat.div_lt_iff_lt_mul hs).mpr (by nlinarith)
  have hqt' : k/s ≤ t := by omega
  have hdiv : s*(k/s) ≤ k := by simpa [mul_comm] using Nat.div_mul_le_self k s
  have he : s*(t-k/s+1)+s*(k/s) = s*(t+1) := by
    calc
      _ = s*((t-k/s)+k/s+1) := by ring
      _ = _ := by rw [Nat.sub_add_cancel hqt']
  have hr : r-k+k = r := Nat.sub_add_cancel hk
  exact ⟨hqt',by omega⟩

theorem hermite_multivariate6 {n : ℕ} (P : MvPolynomial (Fin n) K)
    (S : Fin n → Finset K) (s t r : ℕ) (hcard : ∀ i, (S i).card = s)
    (hdeg : P.totalDegree ≤ r) (hsize : r < s*(t+1))
    (hzero : ∀ x : Fin n → K, (∀ i, x i ∈ S i) →
      ∀ J : Fin n → ℕ, (∑ i, J i) ≤ t → gridJet6 P J x = 0) : P = 0 := by
  classical
  induction n generalizing s t r with
  | zero =>
    have hz := hzero (fun i => Fin.elim0 i) (fun i => Fin.elim0 i) (fun _ => 0) (by simp)
    rw [gridJet6_zero,P.eq_C_of_isEmpty,MvPolynomial.eval_C] at hz
    rw [P.eq_C_of_isEmpty,hz,map_zero]
  | succ n ih =>
    by_cases hP : P = 0
    · exact hP
    let F := MvPolynomial.finSuccEquiv K n P
    let k := F.natDegree
    have hF : F ≠ 0 := by
      intro hz
      apply hP
      exact (MvPolynomial.finSuccEquiv K n).injective (by simpa [F] using hz)
    have hlead : F.coeff k ≠ 0 := by
      rw [show k = F.natDegree from rfl,Polynomial.coeff_natDegree]
      exact Polynomial.leadingCoeff_ne_zero.mpr hF
    have hb : (F.coeff k).totalDegree+k ≤ r :=
      (MvPolynomial.totalDegree_coeff_finSuccEquiv_add_le P k hlead).trans hdeg
    have hk : k ≤ r := by omega
    have hs : 0 < s := by
      by_contra hz
      have hz' : s = 0 := by omega
      simp [hz'] at hsize
    obtain ⟨hqt,hbudget⟩ := hermite_degree_budget6 s k r t hs hk hsize
    have hzlead : F.coeff k = 0 := by
      apply ih (F.coeff k) (fun i => S i.succ) s (t-k/s) (r-k)
        (fun i => hcard i.succ) (by omega) hbudget
      intro x hx J hJ
      let Q := coordinateJetPolynomial6 F J x
      have hQdeg : Q.natDegree ≤ k := coordinateJetPolynomial6_degree F J x
      have hQzero : Q = 0 := by
        apply hermite_univariate6 Q (S 0) (k/s) k hQdeg
        · rw [hcard]
          exact Nat.lt_mul_div_succ k hs
        · intro a ha j hj
          have horder : j+(∑ i, J i) ≤ t := by omega
          have hg := hzero (Fin.cons a x) (by
            intro i
            refine Fin.cases ?_ (fun i => ?_) i
            · exact ha
            · exact hx i) (Fin.cons j J) (by simpa [Fin.sum_univ_succ] using horder)
          rw [gridJet6_coordinate_split] at hg
          exact hg
      have hc := congrArg (fun Q : Polynomial K => Q.coeff k) hQzero
      simpa [Q,coordinateJetPolynomial6_coeff] using hc
    exact (hlead hzlead).elim


def frameChart6 (w : Fin 5 → Fin 6 → K) (i : Fin 6) : MvPolynomial (Fin 5) K :=
  ∑ j, MvPolynomial.C (w j i)*MvPolynomial.X j

def frameSubstitution6 (w : Fin 5 → Fin 6 → K) :
    MvPolynomial (Fin 6) K →+* MvPolynomial (Fin 5) K :=
  MvPolynomial.eval₂Hom MvPolynomial.C (frameChart6 w)

theorem frameChart6_eval (w : Fin 5 → Fin 6 → K) (x : Fin 5 → K) (i : Fin 6) :
    MvPolynomial.eval x (frameChart6 w i) = ∑ j, x j*w j i := by
  simp only [frameChart6,map_sum,map_mul,MvPolynomial.eval_C,MvPolynomial.eval_X]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem frameSubstitution6_eval (w : Fin 5 → Fin 6 → K)
    (P : MvPolynomial (Fin 6) K) (x : Fin 5 → K) :
    MvPolynomial.eval x (frameSubstitution6 w P) =
      MvPolynomial.eval (fun i => ∑ j, x j*w j i) P := by
  have he : (MvPolynomial.eval x).comp (frameSubstitution6 w) =
      MvPolynomial.eval (fun i => ∑ j, x j*w j i) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [frameSubstitution6]
    · intro i
      simp only [RingHom.comp_apply,frameSubstitution6,MvPolynomial.eval₂Hom_X']
      simpa only [MvPolynomial.eval_X] using frameChart6_eval w x i
  exact congrArg (fun f : MvPolynomial (Fin 6) K →+* K => f P) he

theorem frameChart6_pderiv (w : Fin 5 → Fin 6 → K) (j : Fin 5) (i : Fin 6) :
    MvPolynomial.pderiv j (frameChart6 w i) = MvPolynomial.C (w j i) := by
  simp [frameChart6,map_sum,MvPolynomial.pderiv_C_mul,MvPolynomial.pderiv_X,Pi.single_apply]

theorem frameSubstitution6_chain (w : Fin 5 → Fin 6 → K)
    (P : MvPolynomial (Fin 6) K) (j : Fin 5) :
    MvPolynomial.pderiv j (frameSubstitution6 w P) =
      ∑ i : Fin 6, MvPolynomial.C (w j i)*frameSubstitution6 w (MvPolynomial.pderiv i P) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C c => simp [frameSubstitution6,MvPolynomial.pderiv_C]
  | add P Q hP hQ =>
    simp only [map_add,hP,hQ,mul_add,Finset.sum_add_distrib]
  | mul_X P i hP =>
    have hX : frameSubstitution6 w (MvPolynomial.X i) = frameChart6 w i := by
      simp [frameSubstitution6]
    have hdelta : (∑ k : Fin 6, (MvPolynomial.C (w j k)*frameSubstitution6 w P)*
        (if k = i then 1 else 0)) = frameSubstitution6 w P*MvPolynomial.C (w j i) := by
      simp [mul_ite,Finset.sum_ite_eq',Finset.sum_ite_eq,mul_comm]
    have hD (k : Fin 6) :
        frameSubstitution6 w (MvPolynomial.pderiv k (P*MvPolynomial.X i)) =
          frameSubstitution6 w (MvPolynomial.pderiv k P)*frameChart6 w i +
          frameSubstitution6 w P*(if k = i then 1 else 0) := by
      by_cases he : k = i <;>
        simp [MvPolynomial.pderiv_mul,hX,MvPolynomial.pderiv_X,Pi.single_apply,he,eq_comm] <;> ring
    rw [map_mul,MvPolynomial.pderiv_mul,hP,hX,frameChart6_pderiv]
    simp_rw [hD,mul_add,← mul_assoc]
    rw [Finset.sum_add_distrib,← Finset.sum_mul,hdelta]


def frameCoordinates6 (w : Fin 5 → Fin 6 → K) (hw : LinearIndependent K w) :
    (Submodule.span K (Set.range w)) ≃ₗ[K] (Fin 5 → K) :=
  (Basis.span hw).repr.trans (Finsupp.linearEquivFunOnFinite K K (Fin 5))

theorem frame_coordinates_exist6 (w : Fin 5 → Fin 6 → K) (y : Fin 6 → K)
    (hy : y ∈ Submodule.span K (Set.range w)) :
    ∃ x : Fin 5 → K, ∀ i, y i = ∑ j, x j*w j i := by
  obtain ⟨x,hx⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hy
  refine ⟨x,?_⟩
  intro i
  have he := congrFun hx i
  simpa only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul] using he.symm

theorem gridJet6_pderiv {n : ℕ} (P : MvPolynomial (Fin n) K)
    (J : Fin n → ℕ) (x : Fin n → K) (i : Fin n) :
    gridJet6 (MvPolynomial.pderiv i P) J x =
      ((J i+1 : ℕ) : K)*gridJet6 P (Function.update J i (J i+1)) x := by
  classical
  induction P using MvPolynomial.induction_on' with
  | add P Q hP hQ => simp only [map_add,gridJet6_add,hP,hQ,mul_add]
  | monomial d c =>
    rw [MvPolynomial.pderiv_monomial,gridJet6_monomial,gridJet6_monomial]
    have hprod (f : Fin n → K) : (∏ j, f j) = f i*∏ j ∈ Finset.univ.erase i, f j := by
      exact (Finset.mul_prod_erase _ _ (Finset.mem_univ i)).symm
    rw [hprod,hprod]
    have hrest : (∏ j ∈ Finset.univ.erase i,
        (Nat.choose ((d-Finsupp.single i 1 : Fin n →₀ ℕ) j) (J j) : K)*x j^((d-Finsupp.single i 1 : Fin n →₀ ℕ) j-J j)) =
        ∏ j ∈ Finset.univ.erase i,
        (Nat.choose (d j) (Function.update J i (J i+1) j) : K)*
          x j^(d j-Function.update J i (J i+1) j) := by
      apply Finset.prod_congr rfl
      intro j hj
      have hji := (Finset.mem_erase.mp hj).1
      simp [Finsupp.tsub_apply,Finsupp.single_apply,Function.update_of_ne hji,Ne.symm hji]
    rw [hrest]
    simp only [Finsupp.tsub_apply,Finsupp.single_eq_same,Function.update_self]
    by_cases hd : d i = 0
    · simp [hd,Nat.choose_eq_zero_of_lt (Nat.zero_lt_succ _)]
    · by_cases hJ : J i < d i
      · have hexp : d i-1-J i = d i-(J i+1) := by omega
        have hch : ((d i : K)*(Nat.choose (d i-1) (J i) : K)) =
            ((J i+1 : ℕ) : K)*(Nat.choose (d i) (J i+1) : K) := by
          have h := Nat.succ_mul_choose_eq (d i-1) (J i)
          have he : d i-1+1 = d i := by omega
          rw [Nat.succ_eq_add_one,he,Nat.succ_eq_add_one] at h
          have hh := congrArg (fun u : ℕ => (u : K)) (h.trans (Nat.mul_comm _ _))
          simpa only [Nat.cast_mul] using hh
        rw [hexp]
        calc
          _ = c*((d i : K)*(Nat.choose (d i-1) (J i) : K))*
              x i^(d i-(J i+1))*
              (∏ j ∈ Finset.univ.erase i, (Nat.choose (d j) (Function.update J i (J i+1) j) : K)*
                x j^(d j-Function.update J i (J i+1) j)) := by ring
          _ = _ := by rw [hch]; ring
      · have hlt : d i-1 < J i := by omega
        have hlt' : d i < J i+1 := by omega
        simp [Nat.choose_eq_zero_of_lt hlt,Nat.choose_eq_zero_of_lt hlt']


theorem gridJet6_C_mul {n : ℕ} (a : K) (P : MvPolynomial (Fin n) K)
    (J : Fin n → ℕ) (x : Fin n → K) :
    gridJet6 (MvPolynomial.C a*P) J x = a*gridJet6 P J x := by
  classical
  induction P using MvPolynomial.induction_on' with
  | add P Q hP hQ => simp only [mul_add,gridJet6_add,hP,hQ]
  | monomial d c => rw [MvPolynomial.C_mul_monomial,gridJet6_monomial,gridJet6_monomial]; ring

theorem gridJet6_sum {n : ℕ} {ι : Type*} (s : Finset ι)
    (P : ι → MvPolynomial (Fin n) K) (J : Fin n → ℕ) (x : Fin n → K) :
    gridJet6 (∑ i ∈ s, P i) J x = ∑ i ∈ s, gridJet6 (P i) J x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [gridJet6]
  | @insert a s ha ih => simp [Finset.sum_insert,ha,gridJet6_add,ih]

theorem jet_order_update6 {n : ℕ} (J : Fin n → ℕ) (i : Fin n) (k : ℕ) :
    (∑ j, Function.update J i k j)+J i = (∑ j, J j)+k := by
  classical
  rw [Finset.sum_update_of_mem (Finset.mem_univ i)]
  have hbase := Finset.add_sum_erase Finset.univ J (Finset.mem_univ i)
  simp only [Finset.sdiff_singleton_eq_erase] at *
  omega

theorem frame_hasse_zero_transport6 [CharZero K] (w : Fin 5 → Fin 6 → K)
    (P : MvPolynomial (Fin 6) K) (x : Fin 5 → K) (T : ℕ) (A : Fin 5 → ℕ)
    (hA : (∑ j, A j) ≤ T)
    (hz : ∀ J : Fin 6 → ℕ, (∑ i, J i) ≤ T →
      gridJet6 P J (fun i => ∑ j, x j*w j i) = 0) :
    gridJet6 (frameSubstitution6 w P) A x = 0 := by
  classical
  induction T generalizing P A with
  | zero =>
    have hAz : A = 0 := by
      funext j
      have hj := Finset.single_le_sum (fun i _ => Nat.zero_le (A i)) (Finset.mem_univ j)
      have ha : A j = 0 := by omega
      exact ha
    rw [hAz]
    change gridJet6 (frameSubstitution6 w P) (fun _ => 0) x = 0
    rw [gridJet6_zero,frameSubstitution6_eval]
    simpa only [gridJet6_zero] using hz (fun _ => 0) (by simp)
  | succ T ih =>
    by_cases hAz : A = 0
    · rw [hAz]
      change gridJet6 (frameSubstitution6 w P) (fun _ => 0) x = 0
      rw [gridJet6_zero,frameSubstitution6_eval]
      simpa only [gridJet6_zero] using hz (fun _ => 0) (by simp)
    · obtain ⟨j,hjn⟩ := Function.ne_iff.mp hAz
      have hj : 0 < A j := Nat.pos_of_ne_zero hjn
      let B := Function.update A j (A j-1)
      have hBsum : (∑ k, B k)+1 = ∑ k, A k := by
        have he := jet_order_update6 A j (A j-1)
        dsimp [B]
        omega
      have hB : (∑ k, B k) ≤ T := by omega
      have hBA : Function.update B j (B j+1) = A := by
        funext k
        by_cases hk : k = j
        · subst k; simp [B,show A j-1+1 = A j by omega]
        · simp [B,hk]
      have hzD : gridJet6 (MvPolynomial.pderiv j (frameSubstitution6 w P)) B x = 0 := by
        rw [frameSubstitution6_chain,gridJet6_sum]
        apply Finset.sum_eq_zero
        intro i _
        rw [gridJet6_C_mul]
        have hi : gridJet6 (frameSubstitution6 w (MvPolynomial.pderiv i P)) B x = 0 := by
          apply ih _ B hB
          intro J hJ
          rw [gridJet6_pderiv]
          have he := jet_order_update6 J i (J i+1)
          have hinc : (∑ k, Function.update J i (J i+1) k) ≤ T+1 := by omega
          rw [hz _ hinc,mul_zero]
        rw [hi,mul_zero]
      rw [gridJet6_pderiv,hBA] at hzD
      exact (mul_eq_zero.mp hzD).resolve_left (by exact_mod_cast Nat.succ_ne_zero (B j))


theorem frameChart6_degree (w : Fin 5 → Fin 6 → K) (i : Fin 6) :
    (frameChart6 w i).totalDegree ≤ 1 := by
  apply MvPolynomial.totalDegree_finsetSum_le
  intro j _
  have h := MvPolynomial.totalDegree_mul (MvPolynomial.C (w j i)) (MvPolynomial.X j)
  simpa using h

theorem frameSubstitution6_degree (w : Fin 5 → Fin 6 → K)
    (P : MvPolynomial (Fin 6) K) :
    (frameSubstitution6 w P).totalDegree ≤ P.totalDegree := by
  classical
  conv_lhs => rw [P.as_sum]
  rw [map_sum]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro d hd
  rw [frameSubstitution6,MvPolynomial.eval₂Hom_monomial]
  have hp : (d.prod fun i e => frameChart6 w i^e).totalDegree ≤ d.sum (fun _ e => e) := by
    unfold Finsupp.prod Finsupp.sum
    apply (MvPolynomial.totalDegree_finset_prod _ _).trans
    apply Finset.sum_le_sum
    intro i _
    exact (MvPolynomial.totalDegree_pow _ _).trans (by
      have h := frameChart6_degree w i
      nlinarith)
  calc
    _ ≤ (d.prod fun i e => frameChart6 w i^e).totalDegree := by
      simpa only [MvPolynomial.smul_eq_C_mul] using
        MvPolynomial.totalDegree_smul_le (P.coeff d) (d.prod fun i e => frameChart6 w i^e)
    _ ≤ d.sum (fun _ e => e) := hp
    _ ≤ P.totalDegree := MvPolynomial.le_totalDegree hd

theorem frame_hermite6 [CharZero K] (w : Fin 5 → Fin 6 → K)
    (P : MvPolynomial (Fin 6) K) (S : Fin 5 → Finset K) (s t r : ℕ)
    (hcard : ∀ j, (S j).card = s) (hdeg : P.totalDegree ≤ r)
    (hsize : r < s*(t+1))
    (hz : ∀ a : Fin 5 → K, (∀ j, a j ∈ S j) →
      ∀ J : Fin 6 → ℕ, (∑ i, J i) ≤ t →
      gridJet6 P J (fun i => ∑ j, a j*w j i) = 0) :
    ∀ y : Fin 6 → K, y ∈ Submodule.span K (Set.range w) → MvPolynomial.eval y P = 0 := by
  have hQ : frameSubstitution6 w P = 0 := by
    apply hermite_multivariate6 _ S s t r hcard ((frameSubstitution6_degree w P).trans hdeg) hsize
    intro a ha J hJ
    exact frame_hasse_zero_transport6 w P a t J hJ (hz a ha)
  intro y hy
  obtain ⟨a,ha⟩ := frame_coordinates_exist6 w y hy
  have hey : y = fun i => ∑ j, a j*w j i := funext ha
  rw [hey,← frameSubstitution6_eval,hQ,map_zero]

end CompoundFeasibility.SourceHermite
