import SubspaceBridge.SourceHermite4
import Mathlib.Algebra.MvPolynomial.Funext
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceMultiblock4
open SourceHermite SourceHermite4
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


end CompoundFeasibility.SourceMultiblock4
