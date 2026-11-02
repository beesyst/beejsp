import SubspaceBridge.AlgebraicLiouville4
import SubspaceBridge.OriginalAuxiliaryGeometry4
import SubspaceBridge.OriginalDeformedSource4
import SubspaceBridge.SourceHermite6
import SubspaceBridge.SourceBalance6
import Mathlib.Algebra.MvPolynomial.Funext

open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.OriginalSelectedSystem4Literal175

abbrev MixedIndex4 := Fin 3 → Fin 4

def publishedIndexSet4 (Q delta : ℝ) (A c2 c3 : Fin 4 → ℝ) : Finset MixedIndex4 :=
  Finset.univ.filter (fun s => 1 ≤ A (s 0)*Q^(c2 (s 1))*Q^(c3 (s 2))*Q^(delta/2))

def logarithmicWeights4 (Q : ℝ) (A c2 c3 : Fin 4 → ℝ) : Fin 3 → Fin 4 → ℝ :=
  ![fun i => Real.log (A i)/Real.log Q,c2,c3]

theorem logarithmic_width4 (Q : ℝ) (hQ : 1 < Q) (A : Fin 4 → ℝ)
    (hA : ∀ i, 0 < A i) (i : Fin 4) :
    Q^(Real.log (A i)/Real.log Q) = A i := by
  rw [Real.rpow_def_of_pos (zero_lt_one.trans hQ)]
  have hlog : Real.log Q ≠ 0 := (Real.log_pos hQ).ne'
  have he : Real.log Q*(Real.log (A i)/Real.log Q) = Real.log (A i) := by
    field_simp [hlog]
  rw [he,Real.exp_log (hA i)]

theorem logarithmic_balance4 (Q : ℝ) (hQ : 1 < Q) (A c2 c3 : Fin 4 → ℝ)
    (hA : ∀ i, 0 < A i)
    (hb : (∏ i, A i)*(∏ i, Q^(c2 i+c3 i)) = 1) :
    (∑ tau, ∑ i, logarithmicWeights4 Q A c2 c3 tau i) = 0 := by
  have hlog := congrArg Real.log hb
  rw [Real.log_mul (Finset.prod_pos (fun i _ => hA i)).ne'
    (Finset.prod_pos (fun i _ => Real.rpow_pos_of_pos (zero_lt_one.trans hQ) _)).ne',
    Real.log_prod Finset.univ A (fun i _ => (hA i).ne'),Real.log_prod Finset.univ (fun i => Q^(c2 i+c3 i)) (fun i _ => (Real.rpow_pos_of_pos (zero_lt_one.trans hQ) _).ne'),Real.log_one] at hlog
  simp_rw [Real.log_rpow (zero_lt_one.trans hQ)] at hlog
  simp [logarithmicWeights4,Fin.sum_univ_three,Finset.sum_div,Finset.sum_add_distrib,Finset.sum_mul] at hlog ⊢
  have hdiv := congrArg (fun x : ℝ => x/Real.log Q) hlog
  simpa only [Finset.sum_mul,Finset.sum_div,Finset.sum_add_distrib,add_div,
    mul_div_cancel_right₀ _ (Real.log_pos hQ).ne',zero_div,add_assoc] using hdiv

theorem balanced_mixed_nonnegative4 (c : Fin 3 → Fin 4 → ℝ)
    (hb : (∑ tau, ∑ i, c tau i) = 0) :
    ∃ s : MixedIndex4, 0 ≤ ∑ tau, c tau (s tau) := by
  have hm (tau : Fin 3) : ∃ i : Fin 4, ∀ j : Fin 4, c tau j ≤ c tau i := by
    obtain ⟨i,_,hi⟩ := Finset.exists_max_image Finset.univ (c tau) Finset.univ_nonempty
    exact ⟨i,fun j => hi j (Finset.mem_univ j)⟩
  choose s hs using hm
  refine ⟨s,?_⟩
  have hrow (tau : Fin 3) : (∑ i, c tau i) ≤ 4*c tau (s tau) := by
    calc
      _ ≤ ∑ _i : Fin 4, c tau (s tau) := Finset.sum_le_sum (fun j _ => hs tau j)
      _ = _ := by simp
  have h := Finset.sum_le_sum (fun tau (_ : tau ∈ Finset.univ) => hrow tau)
  rw [hb,← Finset.mul_sum] at h
  linarith

theorem published_index_logarithmic4 (Q delta : ℝ) (hQ : 1 < Q)
    (A c2 c3 : Fin 4 → ℝ) (hA : ∀ i, 0 < A i) (s : MixedIndex4) :
    s ∈ publishedIndexSet4 Q delta A c2 c3 ↔
      -delta/2 ≤ ∑ tau, logarithmicWeights4 Q A c2 c3 tau (s tau) := by
  simp only [publishedIndexSet4,Finset.mem_filter,Finset.mem_univ,true_and]
  rw [← logarithmic_width4 Q hQ A hA (s 0)]
  simp_rw [← Real.rpow_add (zero_lt_one.trans hQ)]
  rw [← Real.rpow_zero Q,Real.rpow_le_rpow_left_iff hQ]
  simp [logarithmicWeights4,Fin.sum_univ_three]
  constructor <;> intro h <;> linarith

theorem published_index_nonempty4 (Q delta : ℝ) (hQ : 1 < Q) (hd : 0 < delta)
    (A c2 c3 : Fin 4 → ℝ) (hA : ∀ i, 0 < A i)
    (hb : (∏ i, A i)*(∏ i, Q^(c2 i+c3 i)) = 1) :
    (publishedIndexSet4 Q delta A c2 c3).Nonempty := by
  obtain ⟨s,hs⟩ := balanced_mixed_nonnegative4 _ (logarithmic_balance4 Q hQ A c2 c3 hA hb)
  refine ⟨s,(published_index_logarithmic4 Q delta hQ A c2 c3 hA s).mpr ?_⟩
  linarith

theorem published_index_unbounded_fiber4 (V : Set ℝ) (hV : ¬ BddAbove V)
    (S : V → Finset MixedIndex4) (hS : ∀ q, (S q).Nonempty) :
    ∃ s : Finset MixedIndex4, s.Nonempty ∧
      ¬ BddAbove {q : ℝ | ∃ hq : q ∈ V, S ⟨q,hq⟩ = s} := by
  by_contra! h
  have hb (s : Finset MixedIndex4) :
      BddAbove {q : ℝ | ∃ hq : q ∈ V, S ⟨q,hq⟩ = s} := by
    by_cases hs : s.Nonempty
    · exact h s hs
    · have he : {q : ℝ | ∃ hq : q ∈ V, S ⟨q,hq⟩ = s} = ∅ := by
        ext q
        simp only [Set.mem_setOf_eq,Set.mem_empty_iff_false,iff_false,not_exists]
        intro hq he
        exact hs (he ▸ hS ⟨q,hq⟩)
      rw [he]
      exact bddAbove_empty
  choose b hb using hb
  obtain ⟨B,hB⟩ := (Set.finite_range b).bddAbove
  apply hV
  refine ⟨B,?_⟩
  intro q hq
  exact (hb (S ⟨q,hq⟩) ⟨hq,rfl⟩).trans (hB (Set.mem_range_self _))


theorem deformed_fixed_selected_system4
    (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ)
    (hL : IsUnit L) (c0 c2 c3 : Fin 4 → ℝ) (delta : ℝ) (hd : 0 < delta)
    (V : Set ℝ) (hV : ¬ BddAbove V) (hQV : ∀ q ∈ V, 1 < q)
    (u : (q : V) → Fin 4 → originalSourceGroup4 A2 A3 q.val c2 c3)
    (hready : ∀ q : V, OriginalDeformation4.deformationReady4 A2 A3 L hL q.val
      (hQV q.val q.property) c0 c2 c3 delta (u q)) :
    ∃ F : (q : V) → OriginalDeformedSource4.DeformedAttaining4 A2 A3 L hL q.val
        (hQV q.val q.property) c0 c2 c3 delta (u q),
      ∃ S : Finset MixedIndex4, S.Nonempty ∧ ∃ W : Set ℝ,
      W ⊆ V ∧ ¬ BddAbove W ∧
      ¬ BddAbove ((fun q : ℝ => q^(5 : ℕ)) '' W) ∧
      ∀ q : V, q.val ∈ W →
        publishedIndexSet4 (q.val^(5 : ℕ)) (delta/24)
          (OriginalDeformation4.deformedWidths4 q.val c0
            (OriginalDeformation4.gapDeformation4 (sourceMinima4 A2 A3 L hL q.val
              (hQV q.val q.property) c0 c2 c3)) (F q).sigma)
          (fun i => c2 i/5) (fun i => c3 i/5) = S := by
  let F := fun q : V => Classical.choice
    (OriginalDeformedSource4.attaining_of_ready4 A2 A3 L hL q.val (hQV q.val q.property)
      c0 c2 c3 delta (u q) (hready q))
  let A := fun (q : V) => OriginalDeformation4.deformedWidths4 q.val c0
    (OriginalDeformation4.gapDeformation4 (sourceMinima4 A2 A3 L hL q.val
      (hQV q.val q.property) c0 c2 c3)) (F q).sigma
  let index := fun (q : V) => publishedIndexSet4 (q.val^(5 : ℕ)) (delta/24)
    (A q) (fun i => c2 i/5) (fun i => c3 i/5)
  have hnonempty (q : V) : (index q).Nonempty := by
    apply published_index_nonempty4 _ _ (one_lt_pow₀ (hQV q.val q.property) (by decide))
      (by positivity) _ _ _ (F q).widths_pos
    have hb := (F q).balance
    have he (i : Fin 4) : (q.val^(5 : ℕ))^(c2 i/5+c3 i/5) = q.val^(c2 i+c3 i) := by
      rw [show c2 i/5+c3 i/5 = (c2 i+c3 i)/5 by ring]
      exact OriginalDeformation4.rescaled_power4 q.val (c2 i+c3 i) (zero_lt_one.trans (hQV q.val q.property))
    simpa only [he] using hb
  obtain ⟨S,hS,hW⟩ := published_index_unbounded_fiber4 V hV index hnonempty
  let W := {q : ℝ | ∃ hq : q ∈ V, index ⟨q,hq⟩ = S}
  have hWV : W ⊆ V := by rintro q ⟨hq,_⟩; exact hq
  refine ⟨F,S,hS,W,hWV,hW,OriginalDeformation4.fifth_image_unbounded4 W hW
    (fun q hq => hQV q (hWV hq)),?_⟩
  intro q hq
  obtain ⟨hq,he⟩ := hq
  exact he

end CompoundFeasibility.OriginalSelectedSystem4Literal175

open scoped BigOperators Classical
noncomputable section
namespace CompoundFeasibility.SourceHermite4Literal175
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


end CompoundFeasibility.SourceHermite4Literal175

open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceMultiblock4Literal175
open SourceHermite SourceHermite4Literal175
variable {K : Type*} [Field K]
abbrev Vars4 (m : ℕ) := Fin m × Fin 4

noncomputable def derivative4 {m : ℕ} {R : Type*} [CommRing R]
    (J : Vars4 m →₀ ℕ) (P : MvPolynomial (Vars4 m) R) :
    MvPolynomial (Vars4 m) R :=
  P.sum fun b c => MvPolynomial.monomial (b - J)
    (c * ∏ u : Vars4 m, (Nat.choose (b u) (J u) : R))

theorem derivative4_coeff {m : ℕ} {R : Type*} [CommRing R]
    (a gamma : Vars4 m →₀ ℕ) (P : MvPolynomial (Vars4 m) R) :
    (derivative4 a P).coeff gamma =
      P.coeff (gamma + a) *
        ∏ k : Vars4 m, (Nat.choose ((gamma + a) k) (a k) : R) := by
  classical
  rw [derivative4, MvPolynomial.sum_def, MvPolynomial.coeff_sum]
  calc
    _ = (MvPolynomial.monomial ((gamma + a) - a)
        (P.coeff (gamma + a) * ∏ k : Vars4 m,
          (Nat.choose ((gamma + a) k) (a k) : R))).coeff gamma := by
      apply Finset.sum_eq_single (gamma + a)
      · intro b hb hne
        by_cases hab : a ≤ b
        · have hd : b - a ≠ gamma := by
            intro hz
            apply hne
            calc
              b = (b - a) + a := (tsub_add_cancel_of_le hab).symm
              _ = gamma + a := by rw [hz]
          simp [MvPolynomial.coeff_monomial, hd]
        · change ¬ ∀ k, a k ≤ b k at hab
          push_neg at hab
          obtain ⟨k, hk⟩ := hab
          have hz : (∏ k : Vars4 m, (Nat.choose (b k) (a k) : R)) = 0 := by
            apply Finset.prod_eq_zero (Finset.mem_univ k)
            simp [Nat.choose_eq_zero_of_lt hk]
          simp [hz]
      · intro hn
        have hz : P.coeff (gamma + a) = 0 := MvPolynomial.not_mem_support_iff.mp hn
        simp [hz]
    _ = _ := by simp



variable {R : Type*} [CommRing R]

theorem derivative4_monomial {m : ℕ} (J b : Vars4 m →₀ ℕ) (c : R) :
    derivative4 J (MvPolynomial.monomial b c) = MvPolynomial.monomial (b-J)
      (c * ∏ u : Vars4 m, (Nat.choose (b u) (J u) : R)) := by
  unfold derivative4
  exact MvPolynomial.sum_monomial_eq (by simp)


variable {𝕂 : Type*} [Field 𝕂] [CharZero 𝕂]

theorem derivative4_add {m : ℕ} (J : Vars4 m →₀ ℕ)
    (P Q : MvPolynomial (Vars4 m) 𝕂) :
    derivative4 J (P + Q) = derivative4 J P + derivative4 J Q := by
  apply MvPolynomial.ext
  intro d
  simp only [derivative4_coeff, MvPolynomial.coeff_add, add_mul]

theorem source4_pderiv_eq_single {m : ℕ} (u : Vars4 m)
    (P : MvPolynomial (Vars4 m) 𝕂) :
    MvPolynomial.pderiv u P = derivative4 (Finsupp.single u 1) P := by
  classical
  induction P using MvPolynomial.induction_on' with
  | add P Q hP hQ => simp only [map_add, derivative4_add, hP, hQ]
  | monomial b c =>
    rw [MvPolynomial.pderiv_monomial, derivative4_monomial]
    congr 1
    congr 1
    rw [Finset.prod_eq_single u]
    · simp [Finsupp.single_apply, add_comm]
    · intro x hx hxu
      simp [Finsupp.single_apply, Ne.symm hxu]
    · simp

theorem source4_derivative_comp {m : ℕ} (a b : Vars4 m →₀ ℕ)
    (P : MvPolynomial (Vars4 m) 𝕂) :
    derivative4 a (derivative4 b P) =
      (∏ k : Vars4 m, (Nat.choose ((a + b) k) (a k) : 𝕂)) •
        derivative4 (a + b) P := by
  classical
  apply MvPolynomial.ext
  intro c
  simp only [derivative4_coeff, MvPolynomial.coeff_smul, smul_eq_mul]
  have hch (k : Vars4 m) :
      Nat.choose ((c + a + b) k) (b k) * Nat.choose ((c + a) k) (a k) =
        Nat.choose ((a + b) k) (a k) * Nat.choose ((c + a + b) k) ((a + b) k) := by
    simp only [Finsupp.add_apply]
    have h := Nat.choose_mul (n := c k + a k + b k) (k := a k + b k) (s := b k)
      (by omega) (by omega)
    have hn : c k + a k + b k - b k = c k + a k := by omega
    have ha : a k + b k - b k = a k := by omega
    rw [hn, ha] at h
    have hs : Nat.choose (a k + b k) (b k) = Nat.choose (a k + b k) (a k) :=
      Nat.choose_symm_add.symm
    rw [hs] at h
    nlinarith
  calc
    _ = P.coeff (c + (a + b)) *
        ∏ k : Vars4 m, ((Nat.choose ((c + a + b) k) (b k) : 𝕂) *
          (Nat.choose ((c + a) k) (a k) : 𝕂)) := by
      rw [Finset.prod_mul_distrib]
      simp only [add_assoc]
      ring
    _ = P.coeff (c + (a + b)) *
        ∏ k : Vars4 m, ((Nat.choose ((a + b) k) (a k) : 𝕂) *
          (Nat.choose ((c + a + b) k) ((a + b) k) : 𝕂)) := by
      congr 1
      apply Finset.prod_congr rfl
      intro k _
      exact_mod_cast hch k
    _ = _ := by rw [Finset.prod_mul_distrib]; simp only [add_assoc]; ring

theorem source4_pderiv_hasse {m : ℕ} (u : Vars4 m)
    (J : Vars4 m →₀ ℕ) (P : MvPolynomial (Vars4 m) 𝕂) :
    MvPolynomial.pderiv u (derivative4 J P) =
      (J u + 1) • derivative4 (J + Finsupp.single u 1) P := by
  rw [source4_pderiv_eq_single, source4_derivative_comp, add_comm J]
  have he : (∏ v : Vars4 m, (Nat.choose (((Finsupp.single u 1 : Vars4 m →₀ ℕ) + J) v)
      ((Finsupp.single u 1) v) : 𝕂)) = ((J u + 1 : ℕ) : 𝕂) := by
    rw [Finset.prod_eq_single u]
    · simp [Finsupp.single_apply, add_comm]
    · intro x hx hxu
      simp [Finsupp.single_apply, Ne.symm hxu]
    · simp
  rw [he]
  simp [nsmul_eq_mul, MvPolynomial.smul_eq_C_mul]


def blockPartialEval4 {m : ℕ} (h : Fin m) (x : Vars4 m → K) :
    MvPolynomial (Vars4 m) K →+* MvPolynomial (Fin 4) K :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    (fun u => if u.1 = h then MvPolynomial.X u.2 else MvPolynomial.C (x u))

def blockExponent4 {m : ℕ} (h : Fin m) (d : Vars4 m →₀ ℕ) : Fin 4 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => d (h,i))

theorem blockPartialEval4_eval {m : ℕ} (h : Fin m) (x : Vars4 m → K)
    (P : MvPolynomial (Vars4 m) K) (y : Fin 4 → K) :
    MvPolynomial.eval y (blockPartialEval4 h x P) =
      MvPolynomial.eval (fun u => if u.1 = h then y u.2 else x u) P := by
  have he : (MvPolynomial.eval y).comp (blockPartialEval4 h x) =
      MvPolynomial.eval (fun u => if u.1 = h then y u.2 else x u) := by
    apply MvPolynomial.ringHom_ext
    · intro c; simp [blockPartialEval4]
    · intro u
      by_cases hu : u.1 = h <;> simp [blockPartialEval4,hu]
  exact congrArg (fun f : MvPolynomial (Vars4 m) K →+* K => f P) he

theorem blockPartialEval4_monomial {m : ℕ} (h : Fin m) (x : Vars4 m → K)
    (d : Vars4 m →₀ ℕ) (c : K) :
    blockPartialEval4 h x (MvPolynomial.monomial d c) =
      MvPolynomial.monomial (blockExponent4 h d)
        (c*∏ g ∈ Finset.univ.erase h, ∏ i : Fin 4, x (g,i)^d (g,i)) := by
  classical
  rw [blockPartialEval4,MvPolynomial.eval₂Hom_monomial]
  simp only [Finsupp.prod_fintype _ _ (fun _ => pow_zero _),Fintype.prod_prod_type]
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ h)]
  simp only [Prod.fst,Prod.snd,if_pos rfl]
  have hout : (∏ g ∈ Finset.univ.erase h, ∏ i : Fin 4,
      (if g = h then MvPolynomial.X i else MvPolynomial.C (x (g,i)))^d (g,i)) =
      MvPolynomial.C (∏ g ∈ Finset.univ.erase h, ∏ i : Fin 4, x (g,i)^d (g,i)) := by
    simp only [map_prod,map_pow]
    apply Finset.prod_congr rfl
    intro g hg
    have hgh := (Finset.mem_erase.mp hg).1
    simp only [if_neg hgh]
  rw [hout]
  have hrow (i : Fin 4) : blockExponent4 h d i = d (h,i) := rfl
  simp only [MvPolynomial.monomial_eq,Finsupp.prod_fintype _ _ (fun _ => pow_zero _),hrow,
    MvPolynomial.C_mul]
  simp only [ite_true]
  ring


def blockJetIndex4 {m : ℕ} (h : Fin m) (A : Fin 4 → ℕ) : Vars4 m →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun u => if u.1 = h then A u.2 else 0)

theorem blockJetIndex4_apply {m : ℕ} (h : Fin m) (A : Fin 4 → ℕ) (u : Vars4 m) :
    blockJetIndex4 h A u = if u.1 = h then A u.2 else 0 := rfl

theorem blockJetIndex4_zero {m : ℕ} (h : Fin m) : blockJetIndex4 h (fun _ => 0) = 0 := by
  ext u
  simp [blockJetIndex4_apply]

theorem blockJetIndex4_update {m : ℕ} (h : Fin m) (A : Fin 4 → ℕ) (i : Fin 4) :
    blockJetIndex4 h (Function.update A i (A i+1)) =
      blockJetIndex4 h A+Finsupp.single (h,i) 1 := by
  classical
  ext ⟨g,k⟩
  by_cases hg : g = h
  · subst g
    by_cases hk : k = i
    · subst k; simp [blockJetIndex4_apply,Finsupp.add_apply,Finsupp.single_apply,Prod.mk.injEq]
    · simp [blockJetIndex4_apply,Finsupp.add_apply,Finsupp.single_apply,Function.update,
        Prod.mk.injEq,hk,Ne.symm hk]
  · simp [blockJetIndex4_apply,Finsupp.add_apply,Finsupp.single_apply,Prod.mk.injEq,hg,Ne.symm hg]

theorem derivative4_zero_index {m : ℕ} (P : MvPolynomial (Vars4 m) K) :
    derivative4 0 P = P := by
  ext d
  simp [derivative4_coeff]

theorem derivative4_commute [CharZero K] {m : ℕ} (A B : Vars4 m →₀ ℕ)
    (P : MvPolynomial (Vars4 m) K) :
    derivative4 A (derivative4 B P) = derivative4 B (derivative4 A P) := by
  rw [source4_derivative_comp,source4_derivative_comp,add_comm B A]
  congr 1
  apply Finset.prod_congr rfl
  intro u _
  simp only [Finsupp.add_apply]
  exact congrArg (fun n : ℕ => (n : K)) Nat.choose_symm_add

theorem blockPartialEval4_pderiv {m : ℕ} (h : Fin m) (x : Vars4 m → K)
    (P : MvPolynomial (Vars4 m) K) (i : Fin 4) :
    MvPolynomial.pderiv i (blockPartialEval4 h x P) =
      blockPartialEval4 h x (MvPolynomial.pderiv (h,i) P) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C c => simp [blockPartialEval4,MvPolynomial.pderiv_C]
  | add P Q hP hQ => simp only [map_add,hP,hQ]
  | mul_X P u hP =>
    have hX : blockPartialEval4 h x (MvPolynomial.X u) =
        if u.1 = h then MvPolynomial.X u.2 else MvPolynomial.C (x u) := by
      simp [blockPartialEval4]
    have hD : MvPolynomial.pderiv i
        (if u.1 = h then MvPolynomial.X u.2 else MvPolynomial.C (x u)) =
        blockPartialEval4 h x (MvPolynomial.pderiv (h,i) (MvPolynomial.X u)) := by
      rcases u with ⟨g,k⟩
      by_cases hg : g = h
      · subst g
        simp [MvPolynomial.pderiv_X,Pi.single_apply,Prod.mk.injEq,eq_comm]
      · simp [hg,MvPolynomial.pderiv_C,MvPolynomial.pderiv_X,Pi.single_apply,
          Prod.mk.injEq,Ne.symm hg]
    simp only [map_mul,MvPolynomial.pderiv_mul,map_add,hP,hX,hD]


theorem blockPartialEval4_jet [CharZero K] {m : ℕ} (h : Fin m) (x : Vars4 m → K)
    (P : MvPolynomial (Vars4 m) K) (A : Fin 4 → ℕ) (y : Fin 4 → K) :
    gridJet6 (blockPartialEval4 h x P) A y =
      MvPolynomial.eval (fun u => if u.1 = h then y u.2 else x u)
        (derivative4 (blockJetIndex4 h A) P) := by
  classical
  have hall : ∀ T : ℕ, ∀ (P : MvPolynomial (Vars4 m) K) (A : Fin 4 → ℕ),
      (∑ i, A i) ≤ T →
      gridJet6 (blockPartialEval4 h x P) A y =
        MvPolynomial.eval (fun u => if u.1 = h then y u.2 else x u)
          (derivative4 (blockJetIndex4 h A) P) := by
    intro T
    induction T with
    | zero =>
      intro P A hA
      have hAz : A = 0 := by
        funext i
        have hi := Finset.single_le_sum (fun j _ => Nat.zero_le (A j)) (Finset.mem_univ i)
        have hz : A i = 0 := by omega
        exact hz
      rw [hAz]
      change gridJet6 (blockPartialEval4 h x P) (fun _ => 0) y =
        MvPolynomial.eval _ (derivative4 (blockJetIndex4 h (fun _ => 0)) P)
      rw [gridJet6_zero,blockJetIndex4_zero,derivative4_zero_index,blockPartialEval4_eval]
    | succ T ih =>
      intro P A hA
      by_cases hAz : A = 0
      · rw [hAz]
        change gridJet6 (blockPartialEval4 h x P) (fun _ => 0) y =
          MvPolynomial.eval _ (derivative4 (blockJetIndex4 h (fun _ => 0)) P)
        rw [gridJet6_zero,blockJetIndex4_zero,derivative4_zero_index,blockPartialEval4_eval]
      · obtain ⟨i,hin⟩ := Function.ne_iff.mp hAz
        have hi : 0 < A i := Nat.pos_of_ne_zero hin
        let B := Function.update A i (A i-1)
        have hB : (∑ j, B j) ≤ T := by
          have he := jet_order_update6 A i (A i-1)
          dsimp [B]
          omega
        have hBA : Function.update B i (B i+1) = A := by
          funext j
          by_cases hj : j = i
          · subst j; simp [B,show A i-1+1 = A i by omega]
          · simp [B,hj]
        have hidx : blockJetIndex4 h B+Finsupp.single (h,i) 1 = blockJetIndex4 h A := by
          rw [← blockJetIndex4_update,hBA]
        have hright : MvPolynomial.eval (fun u => if u.1 = h then y u.2 else x u)
            (derivative4 (blockJetIndex4 h B) (MvPolynomial.pderiv (h,i) P)) =
            ((B i+1 : ℕ) : K)*MvPolynomial.eval (fun u => if u.1 = h then y u.2 else x u)
              (derivative4 (blockJetIndex4 h A) P) := by
          rw [source4_pderiv_eq_single,derivative4_commute,← source4_pderiv_eq_single,
            source4_pderiv_hasse,hidx]
          simp only [blockJetIndex4_apply,Prod.fst,Prod.snd,if_pos rfl,ite_true,map_nsmul,nsmul_eq_mul,map_mul,map_natCast]
        apply mul_left_cancel₀ (show ((B i+1 : ℕ) : K) ≠ 0 by exact_mod_cast Nat.succ_ne_zero (B i))
        calc
          _ = gridJet6 (MvPolynomial.pderiv i (blockPartialEval4 h x P)) B y := by
            rw [gridJet6_pderiv,hBA]
          _ = gridJet6 (blockPartialEval4 h x (MvPolynomial.pderiv (h,i) P)) B y := by
            rw [blockPartialEval4_pderiv]
          _ = _ := (ih _ B hB).trans hright
  exact hall (∑ i, A i) P A le_rfl



theorem blockPartialEval4_degree {m : ℕ} (h : Fin m) (x : Vars4 m → K)
    (P : MvPolynomial (Vars4 m) K) (r : ℕ)
    (hdeg : ∀ d ∈ P.support, (∑ i : Fin 4, d (h,i)) ≤ r) :
    (blockPartialEval4 h x P).totalDegree ≤ r := by
  classical
  conv_lhs => rw [P.as_sum]
  rw [map_sum]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro d hd
  rw [blockPartialEval4_monomial]
  apply (MvPolynomial.totalDegree_monomial_le _ _).trans
  have he : (blockExponent4 h d).sum (fun _ e => e) = ∑ i : Fin 4, d (h,i) := by
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
    rfl
  exact he.le.trans (hdeg d hd)


def blockFramePoint4 {m : ℕ} (w : Fin m → Fin 3 → Fin 4 → K)
    (a : Fin m → Fin 3 → K) (u : Vars4 m) : K := ∑ j, a u.1 j*w u.1 j u.2

theorem derivative4_block_degree_bound {m : ℕ} (r : Fin m → ℕ)
    (P : MvPolynomial (Vars4 m) K)
    (hP : ∀ d ∈ P.support, ∀ h, (∑ i : Fin 4, d (h,i)) ≤ r h) (J : Vars4 m →₀ ℕ) :
    ∀ d ∈ (derivative4 J P).support, ∀ h, (∑ i : Fin 4, d (h,i)) ≤ r h := by
  intro d hd h
  have hn := MvPolynomial.mem_support_iff.mp hd
  rw [derivative4_coeff] at hn
  have he := hP (d+J) (MvPolynomial.mem_support_iff.mpr (mul_ne_zero_iff.mp hn).1) h
  simp only [Finsupp.add_apply,Finset.sum_add_distrib] at he
  omega

theorem multiblock_frame_hermite4 [CharZero K] {m : ℕ} (P : MvPolynomial (Vars4 m) K)
    (w : Fin m → Fin 3 → Fin 4 → K) (S : Fin m → Fin 3 → Finset K)
    (s t r : Fin m → ℕ) (hcard : ∀ h j, (S h j).card = s h)
    (hdeg : ∀ d ∈ P.support, ∀ h, (∑ i : Fin 4, d (h,i)) ≤ r h)
    (hsize : ∀ h, r h < s h*(t h+1))
    (hgrid : ∀ a : Fin m → Fin 3 → K, (∀ h j, a h j ∈ S h j) →
      ∀ J : Vars4 m →₀ ℕ, (∀ h, (∑ i : Fin 4, J (h,i)) ≤ t h) →
      MvPolynomial.eval (blockFramePoint4 w a) (derivative4 J P) = 0) :
    ∀ a : Fin m → Fin 3 → K, MvPolynomial.eval (blockFramePoint4 w a) P = 0 := by
  classical
  let Stage (F : Finset (Fin m)) : Prop :=
    ∀ a : Fin m → Fin 3 → K, (∀ g, g ∉ F → ∀ j, a g j ∈ S g j) →
    ∀ J : Vars4 m →₀ ℕ, (∀ g, g ∈ F → ∀ i, J (g,i) = 0) →
      (∀ g, g ∉ F → (∑ i : Fin 4, J (g,i)) ≤ t g) →
      MvPolynomial.eval (blockFramePoint4 w a) (derivative4 J P) = 0
  have hstage : ∀ F, Stage F := by
    intro F
    induction F using Finset.induction_on with
    | empty =>
      intro a ha J hzero horder
      exact hgrid a (fun g j => ha g (Finset.not_mem_empty g) j) J
        (fun g => horder g (Finset.not_mem_empty g))
    | @insert h F hh ih =>
      intro a ha J hzero horder
      let x := blockFramePoint4 w a
      have hD : (blockPartialEval4 h x (derivative4 J P)).totalDegree ≤ r h :=
        blockPartialEval4_degree h x _ _ (fun d hd => derivative4_block_degree_bound r P hdeg J d hd h)
      have hH := frame_hermite4 (w h) (blockPartialEval4 h x (derivative4 J P))
        (S h) (s h) (t h) (r h) (hcard h) hD (hsize h)
      have hzeros : ∀ b : Fin 3 → K, (∀ j, b j ∈ S h j) →
          ∀ B : Fin 4 → ℕ, (∑ i, B i) ≤ t h →
          gridJet6 (blockPartialEval4 h x (derivative4 J P)) B
            (fun i => ∑ j, b j*w h j i) = 0 := by
        intro b hb B hB
        let a' := Function.update a h b
        let C := blockJetIndex4 h B+J
        have ha' : ∀ g, g ∉ F → ∀ j, a' g j ∈ S g j := by
          intro g hg j
          by_cases hgh : g = h
          · subst g; simpa [a'] using hb j
          · simpa [a',hgh] using ha g (by simp [hgh,hg]) j
        have hCzero : ∀ g, g ∈ F → ∀ i, C (g,i) = 0 := by
          intro g hg i
          have hgh : g ≠ h := by intro he; subst g; exact hh hg
          simp [C,Finsupp.add_apply,blockJetIndex4_apply,hgh,hzero g (Finset.mem_insert_of_mem hg) i]
        have hCorder : ∀ g, g ∉ F → (∑ i : Fin 4, C (g,i)) ≤ t g := by
          intro g hg
          by_cases hgh : g = h
          · subst g
            simpa [C,Finsupp.add_apply,blockJetIndex4_apply,hzero h (Finset.mem_insert_self h F)] using hB
          · simpa [C,Finsupp.add_apply,blockJetIndex4_apply,hgh] using
              horder g (by simp [hgh,hg])
        have hz := ih a' ha' C hCzero hCorder
        rw [blockPartialEval4_jet,source4_derivative_comp,MvPolynomial.smul_eval]
        have he : (fun u : Vars4 m => if u.1 = h then ∑ j, b j*w h j u.2 else x u) =
            blockFramePoint4 w a' := by
          funext u
          rcases u with ⟨g,i⟩
          by_cases hg : g = h <;> simp [blockFramePoint4,a',x,hg]
        rw [he]
        change _ * MvPolynomial.eval (blockFramePoint4 w a') (derivative4 C P) = 0
        rw [hz,mul_zero]
      have hspan : (fun i => ∑ j, a h j*w h j i) ∈ Submodule.span K (Set.range (w h)) := by
        have he : (fun i => ∑ j, a h j*w h j i) = ∑ j, a h j • w h j := by
          ext i
          simp [Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
        rw [he]
        apply Submodule.sum_mem
        intro j _
        exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self j))
      have hz := hH hzeros (fun i => ∑ j, a h j*w h j i) hspan
      rw [blockPartialEval4_eval] at hz
      have he : (fun u : Vars4 m => if u.1 = h then ∑ j, a h j*w h j u.2 else x u) = x := by
        funext u
        rcases u with ⟨g,i⟩
        by_cases hg : g = h <;> simp [x,blockFramePoint4,hg]
      rw [he] at hz
      exact hz
  intro a
  have hz := hstage Finset.univ a (by intro g hg; simp at hg) 0
    (by intros; rfl) (by intro g hg; simp at hg)
  simpa only [derivative4_zero_index] using hz


theorem multiblock_span_hermite4 [CharZero K] {m : ℕ} (P : MvPolynomial (Vars4 m) K)
    (w : Fin m → Fin 3 → Fin 4 → K) (S : Fin m → Fin 3 → Finset K)
    (s t r : Fin m → ℕ) (hcard : ∀ h j, (S h j).card = s h)
    (hdeg : ∀ d ∈ P.support, ∀ h, (∑ i : Fin 4, d (h,i)) ≤ r h)
    (hsize : ∀ h, r h < s h*(t h+1))
    (hgrid : ∀ a : Fin m → Fin 3 → K, (∀ h j, a h j ∈ S h j) →
      ∀ J : Vars4 m →₀ ℕ, (∀ h, (∑ i : Fin 4, J (h,i)) ≤ t h) →
      MvPolynomial.eval (blockFramePoint4 w a) (derivative4 J P) = 0) :
    ∀ y : Fin m → Fin 4 → K, (∀ h, y h ∈ Submodule.span K (Set.range (w h))) →
      MvPolynomial.eval (fun u => y u.1 u.2) P = 0 := by
  intro y hy
  have hex (h : Fin m) := frame_coordinates_exist4 (w h) (y h) (hy h)
  choose a ha using hex
  have he : (fun u : Vars4 m => y u.1 u.2) = blockFramePoint4 w a := by
    funext u
    exact ha u.1 u.2
  rw [he]
  exact multiblock_frame_hermite4 P w S s t r hcard hdeg hsize hgrid a


end CompoundFeasibility.SourceMultiblock4Literal175

open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.OriginalSelectedInputs4Literal175
open OriginalDeformation4 OriginalDeformedSource4 OriginalLastDual4 OriginalAuxiliaryDual4

theorem inverse_coefficients_algebraic4 (L : Matrix (Fin 4) (Fin 4) ℝ)
    (hL : L.det = 1) (hAlg : ∀ i j, IsAlgebraic ℚ (L i j)) :
    ∀ i j, IsAlgebraic ℚ (L⁻¹.transpose i j) := by
  obtain ⟨K,hK,hmem⟩ := liouville4_common_field L hAlg
  letI : FiniteDimensional ℚ K := hK
  letI : Algebra.IsAlgebraic ℚ K := Algebra.IsAlgebraic.of_finite ℚ K
  let B : Matrix (Fin 4) (Fin 4) K := fun i j => ⟨L i j,hmem i j⟩
  have hmap : B.map K.val.toRingHom = L := rfl
  have hdet : B.det ≠ 0 := by
    intro hz
    have he := K.val.toRingHom.map_det B
    change (B.det : ℝ) = (B.map K.val.toRingHom).det at he
    rw [hz,hmap,hL] at he
    exact zero_ne_one he
  have hinv := (Auxiliary6.SourceBalance.mapped_inverse K.val.toRingHom B hdet).1
  change B⁻¹.map K.val.toRingHom * L = 1 at hinv
  have he : L⁻¹ = B⁻¹.map K.val.toRingHom := Matrix.inv_eq_left_inv hinv
  intro i j
  rw [Matrix.transpose_apply,he]
  exact IntermediateField.isAlgebraic_iff.mp (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) (B⁻¹ j i))

theorem fixed_dual_liouville4 (L : Matrix (Fin 4) (Fin 4) ℝ)
    (hL : L.det = 1) (hAlg : ∀ i j, IsAlgebraic ℚ (L i j)) :
    ∃ C : ℝ, 0 < C ∧ ∃ D : ℕ, ∀ i (z : Fin 4 → ℤ),
      (L⁻¹.transpose *ᵥ integerReal z) i ≠ 0 →
      C ≤ |(L⁻¹.transpose *ᵥ integerReal z) i| *(max 1 ‖integerReal z‖)^D := by
  simpa only [Matrix.mulVec,dotProduct,integerReal] using
    algebraic_fin4_liouville_lower L⁻¹.transpose (inverse_coefficients_algebraic4 L hL hAlg)

theorem source_frame_real_dual_input4
    {A2 A3 : Matrix (Fin 4) (Fin 4) ℚ} {L : Matrix (Fin 4) (Fin 4) ℝ}
    {hL : IsUnit L} {Q : ℝ} {hQ : 1 < Q} {c0 c2 c3 : Fin 4 → ℝ} {delta : ℝ}
    {u : Fin 4 → originalSourceGroup4 A2 A3 Q c2 c3}
    (h2 : A2.det = 1) (h3 : A3.det = 1) (hLdet : L.det = 1)
    (F : DeformedAttaining4 A2 A3 L hL Q hQ c0 c2 c3 delta u) (i : Fin 4) :
    ‖(L⁻¹.transpose *ᵥ
      (fun k => (integerLastDual4 (fun j => (F.w j : Fin 4 → ℤ)) k : ℝ))) i‖ <
      6*(ZLattice.covolume (integerRealImage (originalSourceGroup4 A2 A3 Q c2 c3))/
        deformedWidths4 Q c0 (gapDeformation4 (sourceMinima4 A2 A3 L hL Q hQ c0 c2 c3)) F.sigma i)*
        (Q^(5 : ℕ))^(-3*(delta/24)) := by
  have hreal := OriginalDeformedFrame4.deformed_cofactor_decay4 A2 A3 L hL hLdet Q hQ
    c0 c2 c3 _ F.sigma F.deformation_pos F.w F.attaining (delta/24) F.small i
  have hcov := OriginalAuxiliaryGeometry4.balanced_width_product_covolume4 A2 A3 h2 h3 Q hQ
    _ c2 c3 F.balance
  apply hreal.trans_le
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
    ((div_le_div_iff_of_pos_right (F.widths_pos i)).mpr hcov) (by norm_num)) (by positivity)


def realCofactorForm4 (w : Fin 4 → Fin 4 → ℤ) : Module.Dual ℝ (Fin 4 → ℝ) :=
  ∑ i, (integerLastDual4 w i : ℝ) • LinearMap.proj i

theorem real_cofactor_kernel4 (w : Fin 4 → Fin 4 → ℤ)
    (hw : LinearIndependent ℝ (fun j => integerReal (w j))) :
    LinearMap.ker (realCofactorForm4 w) =
      Submodule.span ℝ (Set.range (fun j : Fin 3 => integerReal (w j.castSucc))) := by
  let b : Basis (Fin 4) ℝ (Fin 4 → ℝ) := basisOfPiSpaceOfLinearIndependent hw
  have hb (j : Fin 4) : b j = integerReal (w j) := congrFun (coe_basisOfPiSpaceOfLinearIndependent hw) j
  have hpair (j : Fin 4) : realCofactorForm4 w (integerReal (w j)) =
      if j = 3 then ((Matrix.det (w : Matrix (Fin 4) (Fin 4) ℤ) : ℤ) : ℝ) else 0 := by
    have hp := integerLastDual4_pairing w j
    have hr : (∑ i, (w j i : ℝ)*(integerLastDual4 w i : ℝ)) =
        if j = 3 then ((Matrix.det (w : Matrix (Fin 4) (Fin 4) ℤ) : ℤ) : ℝ) else 0 := by exact_mod_cast hp
    simpa [realCofactorForm4,integerReal,mul_comm] using hr
  have hd : ((Matrix.det (w : Matrix (Fin 4) (Fin 4) ℤ) : ℤ) : ℝ) ≠ 0 := by
    exact_mod_cast integerFrame4_det_ne_zero w (integral_frame_rational_independent w hw)
  have hvalue (x : Fin 4 → ℝ) : realCofactorForm4 w x = b.repr x 3*((Matrix.det (w : Matrix (Fin 4) (Fin 4) ℤ) : ℤ) : ℝ) := by
    conv_lhs => rw [← b.sum_repr x]
    simp only [map_sum,LinearMap.map_smul,hb,hpair,smul_eq_mul,mul_ite,mul_zero]
    simp
  apply le_antisymm
  · intro x hx
    have hz : b.repr x 3 = 0 := (mul_eq_zero.mp ((hvalue x).symm.trans hx)).resolve_right hd
    have he := b.sum_repr x
    rw [Fin.sum_univ_castSucc,show Fin.last 3 = (3 : Fin 4) from rfl,hz,zero_smul,add_zero] at he
    rw [← he]
    apply Submodule.sum_mem
    intro j _
    rw [hb]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self j))
  · apply Submodule.span_le.mpr
    rintro _ ⟨j,rfl⟩
    change realCofactorForm4 w (integerReal (w j.castSucc)) = 0
    rw [hpair,if_neg]
    intro hj
    have := congrArg Fin.val hj
    change j.val = 3 at this
    omega

theorem source_multiblock_kernel_restriction4 {m : ℕ}
    (P : MvPolynomial (SourceMultiblock4Literal175.Vars4 m) ℝ)
    (w : Fin m → Fin 4 → Fin 4 → ℤ)
    (hw : ∀ h, LinearIndependent ℝ (fun j => integerReal (w h j)))
    (S : Fin m → Fin 3 → Finset ℝ) (s t r : Fin m → ℕ)
    (hcard : ∀ h j, (S h j).card = s h)
    (hdeg : ∀ d ∈ P.support, ∀ h, (∑ i : Fin 4, d (h,i)) ≤ r h)
    (hsize : ∀ h, r h < s h*(t h+1))
    (hgrid : ∀ a : Fin m → Fin 3 → ℝ, (∀ h j, a h j ∈ S h j) →
      ∀ J : SourceMultiblock4Literal175.Vars4 m →₀ ℕ, (∀ h, (∑ i : Fin 4, J (h,i)) ≤ t h) →
      MvPolynomial.eval (SourceMultiblock4Literal175.blockFramePoint4
        (fun h j => integerReal (w h j.castSucc)) a) (SourceMultiblock4Literal175.derivative4 J P) = 0) :
    ∀ y : Fin m → Fin 4 → ℝ, (∀ h, y h ∈ LinearMap.ker (realCofactorForm4 (w h))) →
      MvPolynomial.eval (fun u => y u.1 u.2) P = 0 := by
  intro y hy
  apply SourceMultiblock4Literal175.multiblock_span_hermite4 P
    (fun h j => integerReal (w h j.castSucc)) S s t r hcard hdeg hsize hgrid y
  intro h
  rw [← real_cofactor_kernel4 (w h) (hw h)]
  exact hy h

end CompoundFeasibility.OriginalSelectedInputs4Literal175

#check CompoundFeasibility.OriginalSelectedSystem4Literal175.MixedIndex4
#print CompoundFeasibility.OriginalSelectedSystem4Literal175.MixedIndex4
#print axioms CompoundFeasibility.OriginalSelectedSystem4Literal175.MixedIndex4
#check CompoundFeasibility.OriginalSelectedSystem4Literal175.publishedIndexSet4
#print CompoundFeasibility.OriginalSelectedSystem4Literal175.publishedIndexSet4
#print axioms CompoundFeasibility.OriginalSelectedSystem4Literal175.publishedIndexSet4
#check CompoundFeasibility.OriginalSelectedSystem4Literal175.logarithmicWeights4
#print CompoundFeasibility.OriginalSelectedSystem4Literal175.logarithmicWeights4
#print axioms CompoundFeasibility.OriginalSelectedSystem4Literal175.logarithmicWeights4
#check CompoundFeasibility.OriginalSelectedSystem4Literal175.logarithmic_width4
#print CompoundFeasibility.OriginalSelectedSystem4Literal175.logarithmic_width4
#print axioms CompoundFeasibility.OriginalSelectedSystem4Literal175.logarithmic_width4
#check CompoundFeasibility.OriginalSelectedSystem4Literal175.logarithmic_balance4
#print CompoundFeasibility.OriginalSelectedSystem4Literal175.logarithmic_balance4
#print axioms CompoundFeasibility.OriginalSelectedSystem4Literal175.logarithmic_balance4
#check CompoundFeasibility.OriginalSelectedSystem4Literal175.balanced_mixed_nonnegative4
#print CompoundFeasibility.OriginalSelectedSystem4Literal175.balanced_mixed_nonnegative4
#print axioms CompoundFeasibility.OriginalSelectedSystem4Literal175.balanced_mixed_nonnegative4
#check CompoundFeasibility.OriginalSelectedSystem4Literal175.published_index_logarithmic4
#print CompoundFeasibility.OriginalSelectedSystem4Literal175.published_index_logarithmic4
#print axioms CompoundFeasibility.OriginalSelectedSystem4Literal175.published_index_logarithmic4
#check CompoundFeasibility.OriginalSelectedSystem4Literal175.published_index_nonempty4
#print CompoundFeasibility.OriginalSelectedSystem4Literal175.published_index_nonempty4
#print axioms CompoundFeasibility.OriginalSelectedSystem4Literal175.published_index_nonempty4
#check CompoundFeasibility.OriginalSelectedSystem4Literal175.published_index_unbounded_fiber4
#print CompoundFeasibility.OriginalSelectedSystem4Literal175.published_index_unbounded_fiber4
#print axioms CompoundFeasibility.OriginalSelectedSystem4Literal175.published_index_unbounded_fiber4
#check CompoundFeasibility.OriginalSelectedSystem4Literal175.deformed_fixed_selected_system4
#print CompoundFeasibility.OriginalSelectedSystem4Literal175.deformed_fixed_selected_system4
#print axioms CompoundFeasibility.OriginalSelectedSystem4Literal175.deformed_fixed_selected_system4
#check CompoundFeasibility.SourceHermite4Literal175.frameChart4
#print CompoundFeasibility.SourceHermite4Literal175.frameChart4
#print axioms CompoundFeasibility.SourceHermite4Literal175.frameChart4
#check CompoundFeasibility.SourceHermite4Literal175.frameSubstitution4
#print CompoundFeasibility.SourceHermite4Literal175.frameSubstitution4
#print axioms CompoundFeasibility.SourceHermite4Literal175.frameSubstitution4
#check CompoundFeasibility.SourceHermite4Literal175.frameChart4_eval
#print CompoundFeasibility.SourceHermite4Literal175.frameChart4_eval
#print axioms CompoundFeasibility.SourceHermite4Literal175.frameChart4_eval
#check CompoundFeasibility.SourceHermite4Literal175.frameSubstitution4_eval
#print CompoundFeasibility.SourceHermite4Literal175.frameSubstitution4_eval
#print axioms CompoundFeasibility.SourceHermite4Literal175.frameSubstitution4_eval
#check CompoundFeasibility.SourceHermite4Literal175.frameChart4_pderiv
#print CompoundFeasibility.SourceHermite4Literal175.frameChart4_pderiv
#print axioms CompoundFeasibility.SourceHermite4Literal175.frameChart4_pderiv
#check CompoundFeasibility.SourceHermite4Literal175.frameSubstitution4_chain
#print CompoundFeasibility.SourceHermite4Literal175.frameSubstitution4_chain
#print axioms CompoundFeasibility.SourceHermite4Literal175.frameSubstitution4_chain
#check CompoundFeasibility.SourceHermite4Literal175.frame_coordinates_exist4
#print CompoundFeasibility.SourceHermite4Literal175.frame_coordinates_exist4
#print axioms CompoundFeasibility.SourceHermite4Literal175.frame_coordinates_exist4
#check CompoundFeasibility.SourceHermite4Literal175.frame_hasse_zero_transport4
#print CompoundFeasibility.SourceHermite4Literal175.frame_hasse_zero_transport4
#print axioms CompoundFeasibility.SourceHermite4Literal175.frame_hasse_zero_transport4
#check CompoundFeasibility.SourceHermite4Literal175.frameChart4_degree
#print CompoundFeasibility.SourceHermite4Literal175.frameChart4_degree
#print axioms CompoundFeasibility.SourceHermite4Literal175.frameChart4_degree
#check CompoundFeasibility.SourceHermite4Literal175.frameSubstitution4_degree
#print CompoundFeasibility.SourceHermite4Literal175.frameSubstitution4_degree
#print axioms CompoundFeasibility.SourceHermite4Literal175.frameSubstitution4_degree
#check CompoundFeasibility.SourceHermite4Literal175.frame_hermite4
#print CompoundFeasibility.SourceHermite4Literal175.frame_hermite4
#print axioms CompoundFeasibility.SourceHermite4Literal175.frame_hermite4
#check CompoundFeasibility.SourceMultiblock4Literal175.Vars4
#print CompoundFeasibility.SourceMultiblock4Literal175.Vars4
#print axioms CompoundFeasibility.SourceMultiblock4Literal175.Vars4
#check CompoundFeasibility.SourceMultiblock4Literal175.derivative4
#print CompoundFeasibility.SourceMultiblock4Literal175.derivative4
#print axioms CompoundFeasibility.SourceMultiblock4Literal175.derivative4
#check CompoundFeasibility.SourceMultiblock4Literal175.derivative4_coeff
#print CompoundFeasibility.SourceMultiblock4Literal175.derivative4_coeff
#print axioms CompoundFeasibility.SourceMultiblock4Literal175.derivative4_coeff
#check CompoundFeasibility.SourceMultiblock4Literal175.derivative4_monomial
#print CompoundFeasibility.SourceMultiblock4Literal175.derivative4_monomial
#print axioms CompoundFeasibility.SourceMultiblock4Literal175.derivative4_monomial
#check CompoundFeasibility.SourceMultiblock4Literal175.derivative4_add
#print CompoundFeasibility.SourceMultiblock4Literal175.derivative4_add
#print axioms CompoundFeasibility.SourceMultiblock4Literal175.derivative4_add
#check CompoundFeasibility.SourceMultiblock4Literal175.source4_pderiv_eq_single
#print CompoundFeasibility.SourceMultiblock4Literal175.source4_pderiv_eq_single
#print axioms CompoundFeasibility.SourceMultiblock4Literal175.source4_pderiv_eq_single
#check CompoundFeasibility.SourceMultiblock4Literal175.source4_derivative_comp
#print CompoundFeasibility.SourceMultiblock4Literal175.source4_derivative_comp
#print axioms CompoundFeasibility.SourceMultiblock4Literal175.source4_derivative_comp
#check CompoundFeasibility.SourceMultiblock4Literal175.source4_pderiv_hasse
#print CompoundFeasibility.SourceMultiblock4Literal175.source4_pderiv_hasse
#print axioms CompoundFeasibility.SourceMultiblock4Literal175.source4_pderiv_hasse
#check CompoundFeasibility.SourceMultiblock4Literal175.blockPartialEval4
#print CompoundFeasibility.SourceMultiblock4Literal175.blockPartialEval4
#print axioms CompoundFeasibility.SourceMultiblock4Literal175.blockPartialEval4
#check CompoundFeasibility.SourceMultiblock4Literal175.blockExponent4
#print CompoundFeasibility.SourceMultiblock4Literal175.blockExponent4
#print axioms CompoundFeasibility.SourceMultiblock4Literal175.blockExponent4
#check CompoundFeasibility.SourceMultiblock4Literal175.blockPartialEval4_eval
#print CompoundFeasibility.SourceMultiblock4Literal175.blockPartialEval4_eval
#print axioms CompoundFeasibility.SourceMultiblock4Literal175.blockPartialEval4_eval
#check CompoundFeasibility.SourceMultiblock4Literal175.blockPartialEval4_monomial
#print CompoundFeasibility.SourceMultiblock4Literal175.blockPartialEval4_monomial
#print axioms CompoundFeasibility.SourceMultiblock4Literal175.blockPartialEval4_monomial
#check CompoundFeasibility.SourceMultiblock4Literal175.blockJetIndex4
#print CompoundFeasibility.SourceMultiblock4Literal175.blockJetIndex4
#print axioms CompoundFeasibility.SourceMultiblock4Literal175.blockJetIndex4
#check CompoundFeasibility.SourceMultiblock4Literal175.blockJetIndex4_apply
#print CompoundFeasibility.SourceMultiblock4Literal175.blockJetIndex4_apply
#print axioms CompoundFeasibility.SourceMultiblock4Literal175.blockJetIndex4_apply
#check CompoundFeasibility.SourceMultiblock4Literal175.blockJetIndex4_zero
#print CompoundFeasibility.SourceMultiblock4Literal175.blockJetIndex4_zero
#print axioms CompoundFeasibility.SourceMultiblock4Literal175.blockJetIndex4_zero
#check CompoundFeasibility.SourceMultiblock4Literal175.blockJetIndex4_update
#print CompoundFeasibility.SourceMultiblock4Literal175.blockJetIndex4_update
#print axioms CompoundFeasibility.SourceMultiblock4Literal175.blockJetIndex4_update
#check CompoundFeasibility.SourceMultiblock4Literal175.derivative4_zero_index
#print CompoundFeasibility.SourceMultiblock4Literal175.derivative4_zero_index
#print axioms CompoundFeasibility.SourceMultiblock4Literal175.derivative4_zero_index
#check CompoundFeasibility.SourceMultiblock4Literal175.derivative4_commute
#print CompoundFeasibility.SourceMultiblock4Literal175.derivative4_commute
#print axioms CompoundFeasibility.SourceMultiblock4Literal175.derivative4_commute
#check CompoundFeasibility.SourceMultiblock4Literal175.blockPartialEval4_pderiv
#print CompoundFeasibility.SourceMultiblock4Literal175.blockPartialEval4_pderiv
#print axioms CompoundFeasibility.SourceMultiblock4Literal175.blockPartialEval4_pderiv
#check CompoundFeasibility.SourceMultiblock4Literal175.blockPartialEval4_jet
#print CompoundFeasibility.SourceMultiblock4Literal175.blockPartialEval4_jet
#print axioms CompoundFeasibility.SourceMultiblock4Literal175.blockPartialEval4_jet
#check CompoundFeasibility.SourceMultiblock4Literal175.blockPartialEval4_degree
#print CompoundFeasibility.SourceMultiblock4Literal175.blockPartialEval4_degree
#print axioms CompoundFeasibility.SourceMultiblock4Literal175.blockPartialEval4_degree
#check CompoundFeasibility.SourceMultiblock4Literal175.blockFramePoint4
#print CompoundFeasibility.SourceMultiblock4Literal175.blockFramePoint4
#print axioms CompoundFeasibility.SourceMultiblock4Literal175.blockFramePoint4
#check CompoundFeasibility.SourceMultiblock4Literal175.derivative4_block_degree_bound
#print CompoundFeasibility.SourceMultiblock4Literal175.derivative4_block_degree_bound
#print axioms CompoundFeasibility.SourceMultiblock4Literal175.derivative4_block_degree_bound
#check CompoundFeasibility.SourceMultiblock4Literal175.multiblock_frame_hermite4
#print CompoundFeasibility.SourceMultiblock4Literal175.multiblock_frame_hermite4
#print axioms CompoundFeasibility.SourceMultiblock4Literal175.multiblock_frame_hermite4
#check CompoundFeasibility.SourceMultiblock4Literal175.multiblock_span_hermite4
#print CompoundFeasibility.SourceMultiblock4Literal175.multiblock_span_hermite4
#print axioms CompoundFeasibility.SourceMultiblock4Literal175.multiblock_span_hermite4
#check CompoundFeasibility.OriginalSelectedInputs4Literal175.inverse_coefficients_algebraic4
#print CompoundFeasibility.OriginalSelectedInputs4Literal175.inverse_coefficients_algebraic4
#print axioms CompoundFeasibility.OriginalSelectedInputs4Literal175.inverse_coefficients_algebraic4
#check CompoundFeasibility.OriginalSelectedInputs4Literal175.fixed_dual_liouville4
#print CompoundFeasibility.OriginalSelectedInputs4Literal175.fixed_dual_liouville4
#print axioms CompoundFeasibility.OriginalSelectedInputs4Literal175.fixed_dual_liouville4
#check CompoundFeasibility.OriginalSelectedInputs4Literal175.source_frame_real_dual_input4
#print CompoundFeasibility.OriginalSelectedInputs4Literal175.source_frame_real_dual_input4
#print axioms CompoundFeasibility.OriginalSelectedInputs4Literal175.source_frame_real_dual_input4
#check CompoundFeasibility.OriginalSelectedInputs4Literal175.realCofactorForm4
#print CompoundFeasibility.OriginalSelectedInputs4Literal175.realCofactorForm4
#print axioms CompoundFeasibility.OriginalSelectedInputs4Literal175.realCofactorForm4
#check CompoundFeasibility.OriginalSelectedInputs4Literal175.real_cofactor_kernel4
#print CompoundFeasibility.OriginalSelectedInputs4Literal175.real_cofactor_kernel4
#print axioms CompoundFeasibility.OriginalSelectedInputs4Literal175.real_cofactor_kernel4
#check CompoundFeasibility.OriginalSelectedInputs4Literal175.source_multiblock_kernel_restriction4
#print CompoundFeasibility.OriginalSelectedInputs4Literal175.source_multiblock_kernel_restriction4
#print axioms CompoundFeasibility.OriginalSelectedInputs4Literal175.source_multiblock_kernel_restriction4
