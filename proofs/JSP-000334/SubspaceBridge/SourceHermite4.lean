import SubspaceBridge.SourceHermite6
open scoped BigOperators Classical
noncomputable section
namespace CompoundFeasibility.SourceHermite4
open SourceHermite
variable {K : Type*} [Field K]

def frameChart4 (w : Fin 3 → Fin 4 → K) (i : Fin 4) : MvPolynomial (Fin 3) K :=
  ∑ j, MvPolynomial.C (w j i)*MvPolynomial.X j

def frameSubstitution4 (w : Fin 3 → Fin 4 → K) :
    MvPolynomial (Fin 4) K →+* MvPolynomial (Fin 3) K :=
  MvPolynomial.eval₂Hom MvPolynomial.C (frameChart4 w)

theorem frameChart4_eval (w : Fin 3 → Fin 4 → K) (x : Fin 3 → K) (i : Fin 4) :
    MvPolynomial.eval x (frameChart4 w i) = ∑ j, x j*w j i := by
  simp only [frameChart4,map_sum,map_mul,MvPolynomial.eval_C,MvPolynomial.eval_X]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem frameSubstitution4_eval (w : Fin 3 → Fin 4 → K)
    (P : MvPolynomial (Fin 4) K) (x : Fin 3 → K) :
    MvPolynomial.eval x (frameSubstitution4 w P) =
      MvPolynomial.eval (fun i => ∑ j, x j*w j i) P := by
  have he : (MvPolynomial.eval x).comp (frameSubstitution4 w) =
      MvPolynomial.eval (fun i => ∑ j, x j*w j i) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [frameSubstitution4]
    · intro i
      simp only [RingHom.comp_apply,frameSubstitution4,MvPolynomial.eval₂Hom_X']
      simpa only [MvPolynomial.eval_X] using frameChart4_eval w x i
  exact congrArg (fun f : MvPolynomial (Fin 4) K →+* K => f P) he

theorem frameChart4_pderiv (w : Fin 3 → Fin 4 → K) (j : Fin 3) (i : Fin 4) :
    MvPolynomial.pderiv j (frameChart4 w i) = MvPolynomial.C (w j i) := by
  simp [frameChart4,map_sum,MvPolynomial.pderiv_C_mul,MvPolynomial.pderiv_X,Pi.single_apply]

theorem frameSubstitution4_chain (w : Fin 3 → Fin 4 → K)
    (P : MvPolynomial (Fin 4) K) (j : Fin 3) :
    MvPolynomial.pderiv j (frameSubstitution4 w P) =
      ∑ i : Fin 4, MvPolynomial.C (w j i)*frameSubstitution4 w (MvPolynomial.pderiv i P) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C c => simp [frameSubstitution4,MvPolynomial.pderiv_C]
  | add P Q hP hQ =>
    simp only [map_add,hP,hQ,mul_add,Finset.sum_add_distrib]
  | mul_X P i hP =>
    have hX : frameSubstitution4 w (MvPolynomial.X i) = frameChart4 w i := by
      simp [frameSubstitution4]
    have hdelta : (∑ k : Fin 4, (MvPolynomial.C (w j k)*frameSubstitution4 w P)*
        (if k = i then 1 else 0)) = frameSubstitution4 w P*MvPolynomial.C (w j i) := by
      simp [mul_ite,Finset.sum_ite_eq',Finset.sum_ite_eq,mul_comm]
    have hD (k : Fin 4) :
        frameSubstitution4 w (MvPolynomial.pderiv k (P*MvPolynomial.X i)) =
          frameSubstitution4 w (MvPolynomial.pderiv k P)*frameChart4 w i +
          frameSubstitution4 w P*(if k = i then 1 else 0) := by
      by_cases he : k = i <;>
        simp [MvPolynomial.pderiv_mul,hX,MvPolynomial.pderiv_X,Pi.single_apply,he,eq_comm] <;> ring
    rw [map_mul,MvPolynomial.pderiv_mul,hP,hX,frameChart4_pderiv]
    simp_rw [hD,mul_add,← mul_assoc]
    rw [Finset.sum_add_distrib,← Finset.sum_mul,hdelta]



theorem frame_coordinates_exist4 (w : Fin 3 → Fin 4 → K) (y : Fin 4 → K)
    (hy : y ∈ Submodule.span K (Set.range w)) :
    ∃ x : Fin 3 → K, ∀ i, y i = ∑ j, x j*w j i := by
  obtain ⟨x,hx⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hy
  refine ⟨x,?_⟩
  intro i
  have he := congrFun hx i
  simpa only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul] using he.symm


theorem frame_hasse_zero_transport4 [CharZero K] (w : Fin 3 → Fin 4 → K)
    (P : MvPolynomial (Fin 4) K) (x : Fin 3 → K) (T : ℕ) (A : Fin 3 → ℕ)
    (hA : (∑ j, A j) ≤ T)
    (hz : ∀ J : Fin 4 → ℕ, (∑ i, J i) ≤ T →
      gridJet6 P J (fun i => ∑ j, x j*w j i) = 0) :
    gridJet6 (frameSubstitution4 w P) A x = 0 := by
  classical
  induction T generalizing P A with
  | zero =>
    have hAz : A = 0 := by
      funext j
      have hj := Finset.single_le_sum (fun i _ => Nat.zero_le (A i)) (Finset.mem_univ j)
      have ha : A j = 0 := by omega
      exact ha
    rw [hAz]
    change gridJet6 (frameSubstitution4 w P) (fun _ => 0) x = 0
    rw [gridJet6_zero,frameSubstitution4_eval]
    simpa only [gridJet6_zero] using hz (fun _ => 0) (by simp)
  | succ T ih =>
    by_cases hAz : A = 0
    · rw [hAz]
      change gridJet6 (frameSubstitution4 w P) (fun _ => 0) x = 0
      rw [gridJet6_zero,frameSubstitution4_eval]
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
      have hzD : gridJet6 (MvPolynomial.pderiv j (frameSubstitution4 w P)) B x = 0 := by
        rw [frameSubstitution4_chain,gridJet6_sum]
        apply Finset.sum_eq_zero
        intro i _
        rw [gridJet6_C_mul]
        have hi : gridJet6 (frameSubstitution4 w (MvPolynomial.pderiv i P)) B x = 0 := by
          apply ih _ B hB
          intro J hJ
          rw [gridJet6_pderiv]
          have he := jet_order_update6 J i (J i+1)
          have hinc : (∑ k, Function.update J i (J i+1) k) ≤ T+1 := by omega
          rw [hz _ hinc,mul_zero]
        rw [hi,mul_zero]
      rw [gridJet6_pderiv,hBA] at hzD
      exact (mul_eq_zero.mp hzD).resolve_left (by exact_mod_cast Nat.succ_ne_zero (B j))


theorem frameChart4_degree (w : Fin 3 → Fin 4 → K) (i : Fin 4) :
    (frameChart4 w i).totalDegree ≤ 1 := by
  apply MvPolynomial.totalDegree_finsetSum_le
  intro j _
  have h := MvPolynomial.totalDegree_mul (MvPolynomial.C (w j i)) (MvPolynomial.X j)
  simpa using h

theorem frameSubstitution4_degree (w : Fin 3 → Fin 4 → K)
    (P : MvPolynomial (Fin 4) K) :
    (frameSubstitution4 w P).totalDegree ≤ P.totalDegree := by
  classical
  conv_lhs => rw [P.as_sum]
  rw [map_sum]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro d hd
  rw [frameSubstitution4,MvPolynomial.eval₂Hom_monomial]
  have hp : (d.prod fun i e => frameChart4 w i^e).totalDegree ≤ d.sum (fun _ e => e) := by
    unfold Finsupp.prod Finsupp.sum
    apply (MvPolynomial.totalDegree_finset_prod _ _).trans
    apply Finset.sum_le_sum
    intro i _
    exact (MvPolynomial.totalDegree_pow _ _).trans (by
      have h := frameChart4_degree w i
      nlinarith)
  calc
    _ ≤ (d.prod fun i e => frameChart4 w i^e).totalDegree := by
      simpa only [MvPolynomial.smul_eq_C_mul] using
        MvPolynomial.totalDegree_smul_le (P.coeff d) (d.prod fun i e => frameChart4 w i^e)
    _ ≤ d.sum (fun _ e => e) := hp
    _ ≤ P.totalDegree := MvPolynomial.le_totalDegree hd

theorem frame_hermite4 [CharZero K] (w : Fin 3 → Fin 4 → K)
    (P : MvPolynomial (Fin 4) K) (S : Fin 3 → Finset K) (s t r : ℕ)
    (hcard : ∀ j, (S j).card = s) (hdeg : P.totalDegree ≤ r)
    (hsize : r < s*(t+1))
    (hz : ∀ a : Fin 3 → K, (∀ j, a j ∈ S j) →
      ∀ J : Fin 4 → ℕ, (∑ i, J i) ≤ t →
      gridJet6 P J (fun i => ∑ j, a j*w j i) = 0) :
    ∀ y : Fin 4 → K, y ∈ Submodule.span K (Set.range w) → MvPolynomial.eval y P = 0 := by
  have hQ : frameSubstitution4 w P = 0 := by
    apply hermite_multivariate6 _ S s t r hcard ((frameSubstitution4_degree w P).trans hdeg) hsize
    intro a ha J hJ
    exact frame_hasse_zero_transport4 w P a t J hJ (hz a ha)
  intro y hy
  obtain ⟨a,ha⟩ := frame_coordinates_exist4 w y hy
  have hey : y = fun i => ∑ j, a j*w j i := funext ha
  rw [hey,← frameSubstitution4_eval,hQ,map_zero]


end CompoundFeasibility.SourceHermite4
