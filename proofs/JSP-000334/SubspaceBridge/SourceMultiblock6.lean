import SubspaceBridge.SourceHermite6
import Mathlib.Algebra.MvPolynomial.Funext
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceMultiblock
open Auxiliary6 Auxiliary6.SourceEvaluation Auxiliary6.SourceGrid SourceHermite SourceNormalIndex
variable {K : Type*} [Field K]

def blockPartialEval6 {m : ℕ} (h : Fin m) (x : Vars6 m → K) :
    MvPolynomial (Vars6 m) K →+* MvPolynomial (Fin 6) K :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    (fun u => if u.1 = h then MvPolynomial.X u.2 else MvPolynomial.C (x u))

def blockExponent6 {m : ℕ} (h : Fin m) (d : Vars6 m →₀ ℕ) : Fin 6 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => d (h,i))

theorem blockPartialEval6_eval {m : ℕ} (h : Fin m) (x : Vars6 m → K)
    (P : MvPolynomial (Vars6 m) K) (y : Fin 6 → K) :
    MvPolynomial.eval y (blockPartialEval6 h x P) =
      MvPolynomial.eval (fun u => if u.1 = h then y u.2 else x u) P := by
  have he : (MvPolynomial.eval y).comp (blockPartialEval6 h x) =
      MvPolynomial.eval (fun u => if u.1 = h then y u.2 else x u) := by
    apply MvPolynomial.ringHom_ext
    · intro c; simp [blockPartialEval6]
    · intro u
      by_cases hu : u.1 = h <;> simp [blockPartialEval6,hu]
  exact congrArg (fun f : MvPolynomial (Vars6 m) K →+* K => f P) he

theorem blockPartialEval6_monomial {m : ℕ} (h : Fin m) (x : Vars6 m → K)
    (d : Vars6 m →₀ ℕ) (c : K) :
    blockPartialEval6 h x (MvPolynomial.monomial d c) =
      MvPolynomial.monomial (blockExponent6 h d)
        (c*∏ g ∈ Finset.univ.erase h, ∏ i : Fin 6, x (g,i)^d (g,i)) := by
  classical
  rw [blockPartialEval6,MvPolynomial.eval₂Hom_monomial]
  simp only [Finsupp.prod_fintype _ _ (fun _ => pow_zero _),Fintype.prod_prod_type]
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ h)]
  simp only [Prod.fst,Prod.snd,if_pos rfl]
  have hout : (∏ g ∈ Finset.univ.erase h, ∏ i : Fin 6,
      (if g = h then MvPolynomial.X i else MvPolynomial.C (x (g,i)))^d (g,i)) =
      MvPolynomial.C (∏ g ∈ Finset.univ.erase h, ∏ i : Fin 6, x (g,i)^d (g,i)) := by
    simp only [map_prod,map_pow]
    apply Finset.prod_congr rfl
    intro g hg
    have hgh := (Finset.mem_erase.mp hg).1
    simp only [if_neg hgh]
  rw [hout]
  have hrow (i : Fin 6) : blockExponent6 h d i = d (h,i) := rfl
  simp only [MvPolynomial.monomial_eq,Finsupp.prod_fintype _ _ (fun _ => pow_zero _),hrow,
    MvPolynomial.C_mul]
  simp only [ite_true]
  ring


def blockJetIndex6 {m : ℕ} (h : Fin m) (A : Fin 6 → ℕ) : Vars6 m →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun u => if u.1 = h then A u.2 else 0)

theorem blockJetIndex6_apply {m : ℕ} (h : Fin m) (A : Fin 6 → ℕ) (u : Vars6 m) :
    blockJetIndex6 h A u = if u.1 = h then A u.2 else 0 := rfl

theorem blockJetIndex6_zero {m : ℕ} (h : Fin m) : blockJetIndex6 h (fun _ => 0) = 0 := by
  ext u
  simp [blockJetIndex6_apply]

theorem blockJetIndex6_update {m : ℕ} (h : Fin m) (A : Fin 6 → ℕ) (i : Fin 6) :
    blockJetIndex6 h (Function.update A i (A i+1)) =
      blockJetIndex6 h A+Finsupp.single (h,i) 1 := by
  classical
  ext ⟨g,k⟩
  by_cases hg : g = h
  · subst g
    by_cases hk : k = i
    · subst k; simp [blockJetIndex6_apply,Finsupp.add_apply,Finsupp.single_apply,Prod.mk.injEq]
    · simp [blockJetIndex6_apply,Finsupp.add_apply,Finsupp.single_apply,Function.update,
        Prod.mk.injEq,hk,Ne.symm hk]
  · simp [blockJetIndex6_apply,Finsupp.add_apply,Finsupp.single_apply,Prod.mk.injEq,hg,Ne.symm hg]

theorem derivative6_zero_index {m : ℕ} (P : MvPolynomial (Vars6 m) K) :
    derivative6 0 P = P := by
  ext d
  simp [derivative6_coeff]

theorem derivative6_commute [CharZero K] {m : ℕ} (A B : Vars6 m →₀ ℕ)
    (P : MvPolynomial (Vars6 m) K) :
    derivative6 A (derivative6 B P) = derivative6 B (derivative6 A P) := by
  rw [rothSource_derivative_comp,rothSource_derivative_comp,add_comm B A]
  congr 1
  apply Finset.prod_congr rfl
  intro u _
  simp only [Finsupp.add_apply]
  exact congrArg (fun n : ℕ => (n : K)) Nat.choose_symm_add

theorem blockPartialEval6_pderiv {m : ℕ} (h : Fin m) (x : Vars6 m → K)
    (P : MvPolynomial (Vars6 m) K) (i : Fin 6) :
    MvPolynomial.pderiv i (blockPartialEval6 h x P) =
      blockPartialEval6 h x (MvPolynomial.pderiv (h,i) P) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C c => simp [blockPartialEval6,MvPolynomial.pderiv_C]
  | add P Q hP hQ => simp only [map_add,hP,hQ]
  | mul_X P u hP =>
    have hX : blockPartialEval6 h x (MvPolynomial.X u) =
        if u.1 = h then MvPolynomial.X u.2 else MvPolynomial.C (x u) := by
      simp [blockPartialEval6]
    have hD : MvPolynomial.pderiv i
        (if u.1 = h then MvPolynomial.X u.2 else MvPolynomial.C (x u)) =
        blockPartialEval6 h x (MvPolynomial.pderiv (h,i) (MvPolynomial.X u)) := by
      rcases u with ⟨g,k⟩
      by_cases hg : g = h
      · subst g
        simp [MvPolynomial.pderiv_X,Pi.single_apply,Prod.mk.injEq,eq_comm]
      · simp [hg,MvPolynomial.pderiv_C,MvPolynomial.pderiv_X,Pi.single_apply,
          Prod.mk.injEq,Ne.symm hg]
    simp only [map_mul,MvPolynomial.pderiv_mul,map_add,hP,hX,hD]


theorem blockPartialEval6_jet [CharZero K] {m : ℕ} (h : Fin m) (x : Vars6 m → K)
    (P : MvPolynomial (Vars6 m) K) (A : Fin 6 → ℕ) (y : Fin 6 → K) :
    gridJet6 (blockPartialEval6 h x P) A y =
      MvPolynomial.eval (fun u => if u.1 = h then y u.2 else x u)
        (derivative6 (blockJetIndex6 h A) P) := by
  classical
  have hall : ∀ T : ℕ, ∀ (P : MvPolynomial (Vars6 m) K) (A : Fin 6 → ℕ),
      (∑ i, A i) ≤ T →
      gridJet6 (blockPartialEval6 h x P) A y =
        MvPolynomial.eval (fun u => if u.1 = h then y u.2 else x u)
          (derivative6 (blockJetIndex6 h A) P) := by
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
      change gridJet6 (blockPartialEval6 h x P) (fun _ => 0) y =
        MvPolynomial.eval _ (derivative6 (blockJetIndex6 h (fun _ => 0)) P)
      rw [gridJet6_zero,blockJetIndex6_zero,derivative6_zero_index,blockPartialEval6_eval]
    | succ T ih =>
      intro P A hA
      by_cases hAz : A = 0
      · rw [hAz]
        change gridJet6 (blockPartialEval6 h x P) (fun _ => 0) y =
          MvPolynomial.eval _ (derivative6 (blockJetIndex6 h (fun _ => 0)) P)
        rw [gridJet6_zero,blockJetIndex6_zero,derivative6_zero_index,blockPartialEval6_eval]
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
        have hidx : blockJetIndex6 h B+Finsupp.single (h,i) 1 = blockJetIndex6 h A := by
          rw [← blockJetIndex6_update,hBA]
        have hright : MvPolynomial.eval (fun u => if u.1 = h then y u.2 else x u)
            (derivative6 (blockJetIndex6 h B) (MvPolynomial.pderiv (h,i) P)) =
            ((B i+1 : ℕ) : K)*MvPolynomial.eval (fun u => if u.1 = h then y u.2 else x u)
              (derivative6 (blockJetIndex6 h A) P) := by
          rw [rothSource_pderiv_eq_single,derivative6_commute,← rothSource_pderiv_eq_single,
            rothSource_pderiv_hasse,hidx]
          simp only [blockJetIndex6_apply,Prod.fst,Prod.snd,if_pos rfl,ite_true,map_nsmul,nsmul_eq_mul,map_mul,map_natCast]
        apply mul_left_cancel₀ (show ((B i+1 : ℕ) : K) ≠ 0 by exact_mod_cast Nat.succ_ne_zero (B i))
        calc
          _ = gridJet6 (MvPolynomial.pderiv i (blockPartialEval6 h x P)) B y := by
            rw [gridJet6_pderiv,hBA]
          _ = gridJet6 (blockPartialEval6 h x (MvPolynomial.pderiv (h,i) P)) B y := by
            rw [blockPartialEval6_pderiv]
          _ = _ := (ih _ B hB).trans hright
  exact hall (∑ i, A i) P A le_rfl


theorem blockPartialEval6_integerValue [CharZero K] {m : ℕ} (h : Fin m)
    (P : MvPolynomial (Vars6 m) ℤ) (v : Fin m → Fin 6 → ℤ) (A : Fin 6 → ℕ) :
    gridJet6 (blockPartialEval6 h (fun u => (v u.1 u.2 : K)) (P.map (Int.castRingHom K)))
      A (fun i => (v h i : K)) = (integerValue (blockJetIndex6 h A) P v : K) := by
  rw [blockPartialEval6_jet,integerValue_cast]
  have he : (fun u : Vars6 m => if u.1 = h then (v h u.2 : K) else (v u.1 u.2 : K)) =
      (fun u : Vars6 m => (v u.1 u.2 : K)) := by
    funext u
    rcases u with ⟨g,i⟩
    by_cases hg : g = h <;> simp [hg]
  rw [he]

theorem blockPartialEval6_degree {m : ℕ} (h : Fin m) (x : Vars6 m → K)
    (P : MvPolynomial (Vars6 m) K) (r : ℕ)
    (hdeg : ∀ d ∈ P.support, (∑ i : Fin 6, d (h,i)) ≤ r) :
    (blockPartialEval6 h x P).totalDegree ≤ r := by
  classical
  conv_lhs => rw [P.as_sum]
  rw [map_sum]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro d hd
  rw [blockPartialEval6_monomial]
  apply (MvPolynomial.totalDegree_monomial_le _ _).trans
  have he : (blockExponent6 h d).sum (fun _ e => e) = ∑ i : Fin 6, d (h,i) := by
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
    rfl
  exact he.le.trans (hdeg d hd)

theorem derivative6_block_degree {m : ℕ} (r : Fin m → ℕ)
    (P : MvPolynomial (Vars6 m) K) (hP : homogeneous6 r P) (J : Vars6 m →₀ ℕ) :
    ∀ d ∈ (derivative6 J P).support, ∀ h, (∑ i : Fin 6, d (h,i)) ≤ r h := by
  intro d hd h
  have hn : P.coeff (d+J) ≠ 0 := by
    have hn := MvPolynomial.mem_support_iff.mp hd
    rw [derivative6_coeff] at hn
    exact (mul_ne_zero_iff.mp hn).1
  have he := hP (d+J) (MvPolynomial.mem_support_iff.mpr hn) h
  simp only [Finsupp.add_apply,Finset.sum_add_distrib] at he
  omega

theorem blockPartialEval6_map {L : Type*} [Field L] (f : K →+* L) {m : ℕ}
    (h : Fin m) (x : Vars6 m → K) (P : MvPolynomial (Vars6 m) K) :
    (blockPartialEval6 h x P).map f =
      blockPartialEval6 h (fun u => f (x u)) (P.map f) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C c => simp [blockPartialEval6]
  | add P Q hP hQ => simp only [map_add,hP,hQ]
  | mul_X P u hP =>
    simp only [map_mul,hP,MvPolynomial.map_X]
    by_cases hu : u.1 = h <;> simp [blockPartialEval6,hu]


def blockFramePoint6 {m : ℕ} (w : Fin m → Fin 5 → Fin 6 → K)
    (a : Fin m → Fin 5 → K) (u : Vars6 m) : K := ∑ j, a u.1 j*w u.1 j u.2

theorem derivative6_block_degree_bound {m : ℕ} (r : Fin m → ℕ)
    (P : MvPolynomial (Vars6 m) K)
    (hP : ∀ d ∈ P.support, ∀ h, (∑ i : Fin 6, d (h,i)) ≤ r h) (J : Vars6 m →₀ ℕ) :
    ∀ d ∈ (derivative6 J P).support, ∀ h, (∑ i : Fin 6, d (h,i)) ≤ r h := by
  intro d hd h
  have hn := MvPolynomial.mem_support_iff.mp hd
  rw [derivative6_coeff] at hn
  have he := hP (d+J) (MvPolynomial.mem_support_iff.mpr (mul_ne_zero_iff.mp hn).1) h
  simp only [Finsupp.add_apply,Finset.sum_add_distrib] at he
  omega

theorem multiblock_frame_hermite6 [CharZero K] {m : ℕ} (P : MvPolynomial (Vars6 m) K)
    (w : Fin m → Fin 5 → Fin 6 → K) (S : Fin m → Fin 5 → Finset K)
    (s t r : Fin m → ℕ) (hcard : ∀ h j, (S h j).card = s h)
    (hdeg : ∀ d ∈ P.support, ∀ h, (∑ i : Fin 6, d (h,i)) ≤ r h)
    (hsize : ∀ h, r h < s h*(t h+1))
    (hgrid : ∀ a : Fin m → Fin 5 → K, (∀ h j, a h j ∈ S h j) →
      ∀ J : Vars6 m →₀ ℕ, (∀ h, (∑ i : Fin 6, J (h,i)) ≤ t h) →
      MvPolynomial.eval (blockFramePoint6 w a) (derivative6 J P) = 0) :
    ∀ a : Fin m → Fin 5 → K, MvPolynomial.eval (blockFramePoint6 w a) P = 0 := by
  classical
  let Stage (F : Finset (Fin m)) : Prop :=
    ∀ a : Fin m → Fin 5 → K, (∀ g, g ∉ F → ∀ j, a g j ∈ S g j) →
    ∀ J : Vars6 m →₀ ℕ, (∀ g, g ∈ F → ∀ i, J (g,i) = 0) →
      (∀ g, g ∉ F → (∑ i : Fin 6, J (g,i)) ≤ t g) →
      MvPolynomial.eval (blockFramePoint6 w a) (derivative6 J P) = 0
  have hstage : ∀ F, Stage F := by
    intro F
    induction F using Finset.induction_on with
    | empty =>
      intro a ha J hzero horder
      exact hgrid a (fun g j => ha g (Finset.not_mem_empty g) j) J
        (fun g => horder g (Finset.not_mem_empty g))
    | @insert h F hh ih =>
      intro a ha J hzero horder
      let x := blockFramePoint6 w a
      have hD : (blockPartialEval6 h x (derivative6 J P)).totalDegree ≤ r h :=
        blockPartialEval6_degree h x _ _ (fun d hd => derivative6_block_degree_bound r P hdeg J d hd h)
      have hH := frame_hermite6 (w h) (blockPartialEval6 h x (derivative6 J P))
        (S h) (s h) (t h) (r h) (hcard h) hD (hsize h)
      have hzeros : ∀ b : Fin 5 → K, (∀ j, b j ∈ S h j) →
          ∀ B : Fin 6 → ℕ, (∑ i, B i) ≤ t h →
          gridJet6 (blockPartialEval6 h x (derivative6 J P)) B
            (fun i => ∑ j, b j*w h j i) = 0 := by
        intro b hb B hB
        let a' := Function.update a h b
        let C := blockJetIndex6 h B+J
        have ha' : ∀ g, g ∉ F → ∀ j, a' g j ∈ S g j := by
          intro g hg j
          by_cases hgh : g = h
          · subst g; simpa [a'] using hb j
          · simpa [a',hgh] using ha g (by simp [hgh,hg]) j
        have hCzero : ∀ g, g ∈ F → ∀ i, C (g,i) = 0 := by
          intro g hg i
          have hgh : g ≠ h := by intro he; subst g; exact hh hg
          simp [C,Finsupp.add_apply,blockJetIndex6_apply,hgh,hzero g (Finset.mem_insert_of_mem hg) i]
        have hCorder : ∀ g, g ∉ F → (∑ i : Fin 6, C (g,i)) ≤ t g := by
          intro g hg
          by_cases hgh : g = h
          · subst g
            simpa [C,Finsupp.add_apply,blockJetIndex6_apply,hzero h (Finset.mem_insert_self h F)] using hB
          · simpa [C,Finsupp.add_apply,blockJetIndex6_apply,hgh] using
              horder g (by simp [hgh,hg])
        have hz := ih a' ha' C hCzero hCorder
        rw [blockPartialEval6_jet,rothSource_derivative_comp,MvPolynomial.smul_eval]
        have he : (fun u : Vars6 m => if u.1 = h then ∑ j, b j*w h j u.2 else x u) =
            blockFramePoint6 w a' := by
          funext u
          rcases u with ⟨g,i⟩
          by_cases hg : g = h <;> simp [blockFramePoint6,a',x,hg]
        rw [he]
        change _ * MvPolynomial.eval (blockFramePoint6 w a') (derivative6 C P) = 0
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
      rw [blockPartialEval6_eval] at hz
      have he : (fun u : Vars6 m => if u.1 = h then ∑ j, a h j*w h j u.2 else x u) = x := by
        funext u
        rcases u with ⟨g,i⟩
        by_cases hg : g = h <;> simp [x,blockFramePoint6,hg]
      rw [he] at hz
      exact hz
  intro a
  have hz := hstage Finset.univ a (by intro g hg; simp at hg) 0
    (by intros; rfl) (by intro g hg; simp at hg)
  simpa only [derivative6_zero_index] using hz


theorem multiblock_span_hermite6 [CharZero K] {m : ℕ} (P : MvPolynomial (Vars6 m) K)
    (w : Fin m → Fin 5 → Fin 6 → K) (S : Fin m → Fin 5 → Finset K)
    (s t r : Fin m → ℕ) (hcard : ∀ h j, (S h j).card = s h)
    (hdeg : ∀ d ∈ P.support, ∀ h, (∑ i : Fin 6, d (h,i)) ≤ r h)
    (hsize : ∀ h, r h < s h*(t h+1))
    (hgrid : ∀ a : Fin m → Fin 5 → K, (∀ h j, a h j ∈ S h j) →
      ∀ J : Vars6 m →₀ ℕ, (∀ h, (∑ i : Fin 6, J (h,i)) ≤ t h) →
      MvPolynomial.eval (blockFramePoint6 w a) (derivative6 J P) = 0) :
    ∀ y : Fin m → Fin 6 → K, (∀ h, y h ∈ Submodule.span K (Set.range (w h))) →
      MvPolynomial.eval (fun u => y u.1 u.2) P = 0 := by
  intro y hy
  have hex (h : Fin m) := frame_coordinates_exist6 (w h) (y h) (hy h)
  choose a ha using hex
  have he : (fun u : Vars6 m => y u.1 u.2) = blockFramePoint6 w a := by
    funext u
    exact ha u.1 u.2
  rw [he]
  exact multiblock_frame_hermite6 P w S s t r hcard hdeg hsize hgrid a

theorem homogeneous6_map {R : Type*} [CommRing R] (f : R →+* K) {m : ℕ}
    (r : Fin m → ℕ) (P : MvPolynomial (Vars6 m) R) (hP : homogeneous6 r P) :
    homogeneous6 r (P.map f) := by
  intro d hd h
  have hn : P.coeff d ≠ 0 := by
    intro hz
    have hn := MvPolynomial.mem_support_iff.mp hd
    apply hn
    rw [MvPolynomial.coeff_map,hz,map_zero]
  exact hP d (MvPolynomial.mem_support_iff.mpr hn) h

theorem integer_grid_rational_restriction6 {m : ℕ} (r : Fin m → ℕ) (hr : ∀ h, 0 < r h)
    (P : MvPolynomial (Vars6 m) ℤ) (hP : homogeneous6 r P) (J : Vars6 m →₀ ℕ)
    (w : Fin m → Fin 5 → Fin 6 → ℤ) (eta : ℝ) (heta : 0 < eta)
    (hgrid : ∀ a : Fin m → Fin 5 → ℕ, (∀ h j, 1 ≤ a h j ∧ a h j ≤ Nat.floor eta⁻¹+1) →
      ∀ B : Vars6 m →₀ ℕ, (∀ h, (∑ i : Fin 6, B (h,i)) ≤ Nat.floor ((r h : ℝ)*eta)) →
      integerValue B (derivative6 J P) (gridPoint w a) = 0) :
    ∀ y : Fin m → Fin 6 → ℚ,
      (∀ h, y h ∈ Submodule.span ℚ (Set.range (fun j i => (w h j i : ℚ)))) →
      MvPolynomial.eval (fun u => y u.1 u.2) (derivative6 J (P.map (Int.castRingHom ℚ))) = 0 := by
  classical
  let N := Nat.floor eta⁻¹+1
  let S : Fin m → Fin 5 → Finset ℚ := fun _ _ => (Finset.Icc 1 N).image (fun n : ℕ => (n : ℚ))
  have hcard : ∀ h j, (S h j).card = N := by
    intro h j
    dsimp [S]
    rw [Finset.card_image_of_injective _ (Nat.cast_injective)]
    simp
  have hdeg : ∀ d ∈ (derivative6 J (P.map (Int.castRingHom ℚ))).support, ∀ h,
      (∑ i : Fin 6, d (h,i)) ≤ r h :=
    derivative6_block_degree r _ (homogeneous6_map _ r P hP) J
  have hsize : ∀ h, r h < N*(Nat.floor ((r h : ℝ)*eta)+1) := by
    intro h
    have he := (hermite_sizes6 eta heta (r h) (hr h)).2.2
    exact_mod_cast he
  apply multiblock_span_hermite6 _ (fun h j i => (w h j i : ℚ)) S (fun _ => N)
    (fun h => Nat.floor ((r h : ℝ)*eta)) r hcard hdeg hsize
  intro a ha B hB
  have hex : ∀ h j, ∃ n : ℕ, n ∈ Finset.Icc 1 N ∧ (n : ℚ) = a h j := by
    intro h j
    exact Finset.mem_image.mp (ha h j)
  choose n hn hna using hex
  have hn' : ∀ h j, 1 ≤ n h j ∧ n h j ≤ Nat.floor eta⁻¹+1 := by
    intro h j
    exact Finset.mem_Icc.mp (hn h j)
  have hz := congrArg (fun z : ℤ => (z : ℚ)) (hgrid n hn' B hB)
  change (integerValue B (derivative6 J P) (gridPoint w n) : ℚ) = 0 at hz
  rw [integerValue_cast,derivative6_map] at hz
  have he : blockFramePoint6 (fun h j i => (w h j i : ℚ)) a =
      (fun u : Vars6 m => (gridPoint w n u.1 u.2 : ℚ)) := by
    funext u
    rcases u with ⟨h,i⟩
    simp only [blockFramePoint6,gridPoint,Int.cast_sum,Int.cast_mul,Int.cast_natCast]
    apply Finset.sum_congr rfl
    intro j _
    rw [hna h j]
  rw [he]
  exact hz


def multiblockFrameSubstitution6 {m : ℕ} (w : Fin m → Fin 5 → Fin 6 → K) :
    MvPolynomial (Vars6 m) K →+* MvPolynomial (Fin m × Fin 5) K :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    (fun u => ∑ j, MvPolynomial.C (w u.1 j u.2)*MvPolynomial.X (u.1,j))

theorem multiblockFrameSubstitution6_eval {m : ℕ} (w : Fin m → Fin 5 → Fin 6 → K)
    (P : MvPolynomial (Vars6 m) K) (a : Fin m → Fin 5 → K) :
    MvPolynomial.eval (fun u => a u.1 u.2) (multiblockFrameSubstitution6 w P) =
      MvPolynomial.eval (blockFramePoint6 w a) P := by
  have he : (MvPolynomial.eval (fun u => a u.1 u.2)).comp (multiblockFrameSubstitution6 w) =
      MvPolynomial.eval (blockFramePoint6 w a) := by
    apply MvPolynomial.ringHom_ext
    · intro c; simp [multiblockFrameSubstitution6]
    · intro u
      simp only [RingHom.comp_apply,multiblockFrameSubstitution6,MvPolynomial.eval₂Hom_X',
        map_sum,map_mul,MvPolynomial.eval_C,MvPolynomial.eval_X,blockFramePoint6]
      apply Finset.sum_congr rfl
      intro j _
      ring
  exact congrArg (fun f : MvPolynomial (Vars6 m) K →+* K => f P) he

theorem multiblockFrameSubstitution6_map {L : Type*} [Field L] (f : K →+* L) {m : ℕ}
    (w : Fin m → Fin 5 → Fin 6 → K) (P : MvPolynomial (Vars6 m) K) :
    (multiblockFrameSubstitution6 w P).map f =
      multiblockFrameSubstitution6 (fun h j i => f (w h j i)) (P.map f) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C c => simp [multiblockFrameSubstitution6]
  | add P Q hP hQ => simp only [map_add,hP,hQ]
  | mul_X P u hP =>
    simp only [map_mul,hP,MvPolynomial.map_X]
    simp [multiblockFrameSubstitution6,map_sum,map_mul]

theorem rational_real_span_restriction6 {m : ℕ} (w : Fin m → Fin 5 → Fin 6 → ℤ)
    (P : MvPolynomial (Vars6 m) ℚ)
    (hQ : ∀ y : Fin m → Fin 6 → ℚ,
      (∀ h, y h ∈ Submodule.span ℚ (Set.range (fun j i => (w h j i : ℚ)))) →
      MvPolynomial.eval (fun u => y u.1 u.2) P = 0) :
    ∀ y : Fin m → Fin 6 → ℝ,
      (∀ h, y h ∈ Submodule.span ℝ (Set.range (fun j i => (w h j i : ℝ)))) →
      MvPolynomial.eval (fun u => y u.1 u.2) (P.map (algebraMap ℚ ℝ)) = 0 := by
  classical
  let wQ := fun h j i => (w h j i : ℚ)
  let wR := fun h j i => (w h j i : ℝ)
  have hzQ : multiblockFrameSubstitution6 wQ P = 0 := by
    apply MvPolynomial.funext
    intro a
    rw [map_zero]
    have he := multiblockFrameSubstitution6_eval wQ P (fun h j => a (h,j))
    rw [he]
    apply hQ (fun h i => blockFramePoint6 wQ (fun h j => a (h,j)) (h,i))
    intro h
    have hspan : (fun i => blockFramePoint6 wQ (fun h j => a (h,j)) (h,i)) =
        ∑ j, a (h,j) • wQ h j := by
      ext i
      simp [blockFramePoint6,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
    rw [hspan]
    apply Submodule.sum_mem
    intro j _
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self j))
  have hzR : multiblockFrameSubstitution6 wR (P.map (algebraMap ℚ ℝ)) = 0 := by
    have he := congrArg (fun Q : MvPolynomial (Fin m × Fin 5) ℚ => Q.map (algebraMap ℚ ℝ)) hzQ
    change (multiblockFrameSubstitution6 wQ P).map (algebraMap ℚ ℝ) =
      (0 : MvPolynomial (Fin m × Fin 5) ℚ).map (algebraMap ℚ ℝ) at he
    rw [multiblockFrameSubstitution6_map,map_zero] at he
    have hw : (fun h j i => algebraMap ℚ ℝ (wQ h j i)) = wR := by
      funext h j i
      simp [wQ,wR]
    rw [hw] at he
    exact he
  intro y hy
  have hex (h : Fin m) := frame_coordinates_exist6 (wR h) (y h) (hy h)
  choose a ha using hex
  have he : (fun u : Vars6 m => y u.1 u.2) = blockFramePoint6 wR a := by
    funext u
    exact ha u.1 u.2
  rw [he,← multiblockFrameSubstitution6_eval,hzR,map_zero]

theorem derivative6_integer_rational_real6 {m : ℕ} (J : Vars6 m →₀ ℕ)
    (P : MvPolynomial (Vars6 m) ℤ) :
    (derivative6 J (P.map (Int.castRingHom ℚ))).map (algebraMap ℚ ℝ) =
      derivative6 J (P.map (Int.castRingHom ℝ)) := by
  rw [derivative6_map,MvPolynomial.map_map]
  have he : (algebraMap ℚ ℝ).comp (Int.castRingHom ℚ) = Int.castRingHom ℝ := by
    ext n
    simp
  rw [he]

theorem integer_grid_real_restriction6 {m : ℕ} (r : Fin m → ℕ) (hr : ∀ h, 0 < r h)
    (P : MvPolynomial (Vars6 m) ℤ) (hP : homogeneous6 r P) (J : Vars6 m →₀ ℕ)
    (w : Fin m → Fin 5 → Fin 6 → ℤ) (eta : ℝ) (heta : 0 < eta)
    (hgrid : ∀ a : Fin m → Fin 5 → ℕ, (∀ h j, 1 ≤ a h j ∧ a h j ≤ Nat.floor eta⁻¹+1) →
      ∀ B : Vars6 m →₀ ℕ, (∀ h, (∑ i : Fin 6, B (h,i)) ≤ Nat.floor ((r h : ℝ)*eta)) →
      integerValue B (derivative6 J P) (gridPoint w a) = 0) :
    ∀ y : Fin m → Fin 6 → ℝ,
      (∀ h, y h ∈ Submodule.span ℝ (Set.range (fun j i => (w h j i : ℝ)))) →
      MvPolynomial.eval (fun u => y u.1 u.2) (derivative6 J (P.map (Int.castRingHom ℝ))) = 0 := by
  have hQ := integer_grid_rational_restriction6 r hr P hP J w eta heta hgrid
  have hR := rational_real_span_restriction6 w (derivative6 J (P.map (Int.castRingHom ℚ))) hQ
  intro y hy
  have hz := hR y hy
  rwa [derivative6_integer_rational_real6] at hz

theorem source_actual_normal_restrictions6 (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L) (c0 c2 c3 : Fin 4 → ℝ)
    (V : Set ℝ) (hQV : ∀ q ∈ V, 1 < q)
    (hs : SourceBlocks.sourceBlockVanishing42 A2 A3 L hL c0 c2 c3 V hQV) :
    ∃ w : (q : V) → Fin 6 → directCompoundGroup42 A2 A3 q.val c2 c3,
    ∃ M a : V → Fin 6 → ℤ,
      (∀ q, M q ≠ 0 ∧ (∑ i, a q i*M q i) = 1 ∧
        Ideal.span (Set.range (M q)) = ⊤ ∧
        (∀ j : Fin 5, (∑ i, M q i*(w q j.castSucc : Fin 6 → ℤ) i) = 0) ∧
        LinearMap.ker (normalForm6 (M q)) =
          firstFiveSpan42 (fun j i => ((w q j : Fin 6 → ℤ) i : ℚ)) ∧
        LinearMap.ker (realNormalForm6 (M q)) =
          firstFiveSpan42 (fun j i => ((w q j : Fin 6 → ℤ) i : ℝ))) ∧
    ∃ eta : ℝ, 0 < eta ∧ eta < 1 ∧ ∃ m : ℕ, 0 < m ∧
    ∀ rho : ℝ, 0 < rho →
    ∃ t : Fin m → V, StrictMono (fun h => (t h).val) ∧
    ∃ r : Fin m → ℕ, (∀ h, 0 < r h) ∧
    ∃ P : MvPolynomial (Vars6 m) ℤ, P ≠ 0 ∧ homogeneous6 r P ∧
      (∀ a : Fin m → Fin 5 → ℕ, (∀ h j, 1 ≤ a h j ∧ a h j ≤ Nat.floor eta⁻¹+1) →
        ∀ J : Vars6 m →₀ ℕ, rothSourceDerivativeWeight r J < 2*eta*m →
        integerValue J P (gridPoint (fun h j => (w (t h) j.castSucc : Fin 6 → ℤ)) a) = 0) ∧
      (∀ a : Fin m → Fin 5 → ℕ, (∀ h j, 1 ≤ a h j ∧ a h j ≤ Nat.floor eta⁻¹+1) →
        ∀ J K : Vars6 m →₀ ℕ, rothSourceDerivativeWeight r J < (m : ℝ)*eta →
        (∀ h, (∑ i : Fin 6, K (h,i)) ≤ Nat.floor ((r h : ℝ)*eta)) →
        integerValue K (derivative6 J P)
          (gridPoint (fun h j => (w (t h) j.castSucc : Fin 6 → ℤ)) a) = 0) ∧
      (∀ J : Vars6 m →₀ ℕ, rothSourceDerivativeWeight r J < (m : ℝ)*eta →
        (∀ y : Fin m → Fin 6 → ℚ, (∀ h, y h ∈ LinearMap.ker (normalForm6 (M (t h)))) →
          MvPolynomial.eval (fun u => y u.1 u.2) (derivative6 J (P.map (Int.castRingHom ℚ))) = 0) ∧
        (∀ y : Fin m → Fin 6 → ℝ, (∀ h, y h ∈ LinearMap.ker (realNormalForm6 (M (t h)))) →
          MvPolynomial.eval (fun u => y u.1 u.2) (derivative6 J (P.map (Int.castRingHom ℝ))) = 0)) := by
  rcases source_actual_normal_grid6 A2 A3 L hL c0 c2 c3 V hQV hs with
    ⟨w,M,a,hM,eta,heta,heta1,m,hm,hblocks⟩
  refine ⟨w,M,a,hM,eta,heta,heta1,m,hm,?_⟩
  intro rho hrho
  rcases hblocks rho hrho with ⟨t,ht,r,hr,P,hP,hhom,hgrid,hcomp⟩
  refine ⟨t,ht,r,hr,P,hP,hhom,hgrid,hcomp,?_⟩
  intro J hJ
  constructor
  · intro y hy
    apply integer_grid_rational_restriction6 r hr P hhom J
      (fun h j => (w (t h) j.castSucc : Fin 6 → ℤ)) eta heta
      (fun n hn B hB => hcomp n hn J B hJ hB) y
    intro h
    change y h ∈ firstFiveSpan42 (fun j i => ((w (t h) j : Fin 6 → ℤ) i : ℚ))
    rw [← (hM (t h)).2.2.2.2.1]
    exact hy h
  · intro y hy
    apply integer_grid_real_restriction6 r hr P hhom J
      (fun h j => (w (t h) j.castSucc : Fin 6 → ℤ)) eta heta
      (fun n hn B hB => hcomp n hn J B hJ hB) y
    intro h
    change y h ∈ firstFiveSpan42 (fun j i => ((w (t h) j : Fin 6 → ℤ) i : ℝ))
    rw [← (hM (t h)).2.2.2.2.2]
    exact hy h

def normalForward6 {m : ℕ} (M : Fin m → Fin 6 → ℤ) (k : Fin m → Fin 6) :
    MvPolynomial (Vars6 m) ℝ →+* MvPolynomial (Vars6 m) ℝ :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    (fun u => if u.2 = k u.1 then normalPolynomial6 M u.1 else MvPolynomial.X u)

def normalInverse6 {m : ℕ} (M : Fin m → Fin 6 → ℤ) (k : Fin m → Fin 6) :
    MvPolynomial (Vars6 m) ℝ →+* MvPolynomial (Vars6 m) ℝ :=
  MvPolynomial.eval₂Hom MvPolynomial.C (fun u => if u.2 = k u.1 then
    MvPolynomial.C ((M u.1 (k u.1) : ℝ)⁻¹) *
      (MvPolynomial.X u - ∑ j ∈ Finset.univ.erase (k u.1),
        MvPolynomial.C (M u.1 j : ℝ) * MvPolynomial.X (u.1,j))
    else MvPolynomial.X u)

theorem normalForward6_inverse6 {m : ℕ} (M : Fin m → Fin 6 → ℤ)
    (k : Fin m → Fin 6) (hk : ∀ h, M h (k h) ≠ 0)
    (P : MvPolynomial (Vars6 m) ℝ) :
    normalForward6 M k (normalInverse6 M k P) = P := by
  classical
  have he : (normalForward6 M k).comp (normalInverse6 M k) = RingHom.id _ := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [normalForward6,normalInverse6]
    · intro u
      rcases u with ⟨h,i⟩
      by_cases hi : i = k h
      · subst i
        have hc : (MvPolynomial.C ((M h (k h) : ℝ)⁻¹) : MvPolynomial (Vars6 m) ℝ) *
            MvPolynomial.C (M h (k h) : ℝ) = 1 := by
          rw [← MvPolynomial.C_mul,inv_mul_cancel₀ (by exact_mod_cast hk h),map_one]
        have hs : normalPolynomial6 M h =
            (∑ j ∈ Finset.univ.erase (k h),
              MvPolynomial.C (M h j : ℝ) * MvPolynomial.X (h,j)) +
              MvPolynomial.C (M h (k h) : ℝ) * MvPolynomial.X (h,k h) := by
          exact (Finset.sum_erase_add _ _ (Finset.mem_univ (k h))).symm
        simp only [RingHom.comp_apply,normalInverse6,MvPolynomial.eval₂Hom_X',
          Prod.fst,Prod.snd,ite_true,map_mul,map_sub,map_sum,normalForward6,
          MvPolynomial.eval₂Hom_C,MvPolynomial.eval₂Hom_X',RingHom.id_apply]
        have hfree : (∑ j ∈ Finset.univ.erase (k h),
            MvPolynomial.C (M h j : ℝ) *
              (if j = k h then normalPolynomial6 M h else MvPolynomial.X (h,j))) =
            ∑ j ∈ Finset.univ.erase (k h),
              MvPolynomial.C (M h j : ℝ) * MvPolynomial.X (h,j) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [if_neg (Finset.mem_erase.mp hj).1]
        rw [hfree,hs,add_sub_cancel_left,← mul_assoc,hc,one_mul]
      · simp [normalForward6,normalInverse6,hi]
  exact congrArg (fun f => f P) he

theorem normalInverse6_forward6 {m : ℕ} (M : Fin m → Fin 6 → ℤ)
    (k : Fin m → Fin 6) (hk : ∀ h, M h (k h) ≠ 0)
    (P : MvPolynomial (Vars6 m) ℝ) :
    normalInverse6 M k (normalForward6 M k P) = P := by
  classical
  have he : (normalInverse6 M k).comp (normalForward6 M k) = RingHom.id _ := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [normalForward6,normalInverse6]
    · intro u
      rcases u with ⟨h,i⟩
      by_cases hi : i = k h
      · subst i
        have hc : (MvPolynomial.C (M h (k h) : ℝ) : MvPolynomial (Vars6 m) ℝ) *
            MvPolynomial.C ((M h (k h) : ℝ)⁻¹) = 1 := by
          rw [← MvPolynomial.C_mul,mul_inv_cancel₀ (by exact_mod_cast hk h),map_one]
        simp only [RingHom.comp_apply,normalForward6,MvPolynomial.eval₂Hom_X',
          Prod.fst,Prod.snd,ite_true,RingHom.id_apply]
        change normalInverse6 M k (normalPolynomial6 M h) = MvPolynomial.X (h,k h)
        rw [normalPolynomial6,← Finset.sum_erase_add _ _ (Finset.mem_univ (k h))]
        simp only [map_add,map_sum,map_mul,normalInverse6,MvPolynomial.eval₂Hom_C,
          MvPolynomial.eval₂Hom_X',Prod.fst,Prod.snd,ite_true]
        have hfree : (∑ j ∈ Finset.univ.erase (k h),
            MvPolynomial.C (M h j : ℝ) *
              (if j = k h then MvPolynomial.C ((M h (k h) : ℝ)⁻¹) *
                (MvPolynomial.X (h,j) - ∑ l ∈ Finset.univ.erase (k h),
                  MvPolynomial.C (M h l : ℝ) * MvPolynomial.X (h,l))
               else MvPolynomial.X (h,j))) =
            ∑ j ∈ Finset.univ.erase (k h),
              MvPolynomial.C (M h j : ℝ) * MvPolynomial.X (h,j) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [if_neg (Finset.mem_erase.mp hj).1]
        rw [hfree,← mul_assoc,hc,one_mul]
        ring
      · simp [normalForward6,normalInverse6,hi]
  exact congrArg (fun f => f P) he

noncomputable def zeroNormalCoordinates6 {m : ℕ} (k : Fin m → Fin 6) :
    MvPolynomial (Vars6 m) K →+* MvPolynomial (Vars6 m) K :=
  MvPolynomial.eval₂Hom MvPolynomial.C (fun u => if u.2 = k u.1 then 0 else MvPolynomial.X u)

theorem zeroNormalCoordinates6_monomial {m : ℕ} (k : Fin m → Fin 6)
    (b : Vars6 m →₀ ℕ) (c : K) :
    zeroNormalCoordinates6 k (MvPolynomial.monomial b c) =
      if (∀ h, b (h,k h) = 0) then MvPolynomial.monomial b c else 0 := by
  classical
  rw [zeroNormalCoordinates6, MvPolynomial.eval₂Hom_monomial]
  rw [Finsupp.prod_fintype _ _ (fun _ => by simp)]
  by_cases hb : ∀ h, b (h,k h) = 0
  · rw [if_pos hb, MvPolynomial.monomial_eq]
    congr 1
    rw [Finsupp.prod_fintype _ _ (fun _ => by simp)]
    apply Finset.prod_congr rfl
    intro u _
    by_cases hu : u.2 = k u.1
    · have he : u = (u.1,k u.1) := Prod.ext rfl hu
      have hz : b u = 0 := (congrArg b he).trans (hb u.1)
      simp [hu, hz]
    · simp [hu]
  · rw [if_neg hb]
    push_neg at hb
    obtain ⟨h, hh⟩ := hb
    have hz : (∏ u : Vars6 m, (if u.2 = k u.1 then 0 else MvPolynomial.X u) ^ b u) =
        (0 : MvPolynomial (Vars6 m) K) := by
      apply Finset.prod_eq_zero (Finset.mem_univ (h,k h))
      simp [hh]
    rw [hz, mul_zero]

theorem zeroNormalCoordinates6_coeff {m : ℕ} (k : Fin m → Fin 6)
    (Q : MvPolynomial (Vars6 m) K) (b : Vars6 m →₀ ℕ) :
    (zeroNormalCoordinates6 k Q).coeff b = if (∀ h, b (h,k h) = 0) then Q.coeff b else 0 := by
  classical
  induction Q using MvPolynomial.induction_on' with
  | monomial a c =>
    rw [zeroNormalCoordinates6_monomial]
    by_cases ha : ∀ h, a (h,k h) = 0
    · rw [if_pos ha]
      by_cases hb : ∀ h, b (h,k h) = 0
      · simp [hb]
      · have hab : a ≠ b := by intro he; subst a; exact hb ha
        simp [hb, hab]
    · rw [if_neg ha]
      by_cases hb : ∀ h, b (h,k h) = 0
      · have hab : a ≠ b := by intro he; subst a; exact ha hb
        simp [hb, hab]
      · simp [hb]
  | add P Q hP hQ =>
    rw [map_add, MvPolynomial.coeff_add, hP, hQ, MvPolynomial.coeff_add]
    split_ifs <;> simp


theorem normal_zero_restriction6 {m : ℕ} (M : Fin m → Fin 6 → ℤ)
    (k : Fin m → Fin 6) (hk : ∀ h, M h (k h) ≠ 0)
    (P : MvPolynomial (Vars6 m) ℝ)
    (hzero : ∀ y : Fin m → Fin 6 → ℝ,
      (∀ h, y h ∈ LinearMap.ker (realNormalForm6 (M h))) →
      MvPolynomial.eval (fun u => y u.1 u.2) P = 0) :
    zeroNormalCoordinates6 k (normalInverse6 M k P) = 0 := by
  classical
  apply MvPolynomial.funext
  intro z
  let H := (zeroNormalCoordinates6 (K := ℝ) k).comp (normalInverse6 M k)
  let y : Fin m → Fin 6 → ℝ := fun h i => MvPolynomial.eval z (H (MvPolynomial.X (h,i)))
  have he : (MvPolynomial.eval z).comp H = MvPolynomial.eval (fun u => y u.1 u.2) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [H,normalInverse6,zeroNormalCoordinates6]
    · intro u
      simp [y]
  have hker : ∀ h, y h ∈ LinearMap.ker (realNormalForm6 (M h)) := by
    intro h
    have hn := normalInverse6_forward6 M k hk (MvPolynomial.X (h,k h))
    simp only [normalForward6,MvPolynomial.eval₂Hom_X',Prod.fst,Prod.snd,ite_true] at hn
    have hz := congrArg (fun Q => MvPolynomial.eval z (zeroNormalCoordinates6 k Q)) hn
    simp only [zeroNormalCoordinates6,MvPolynomial.eval₂Hom_X',Prod.fst,Prod.snd,
      ite_true,map_zero] at hz
    have hp := congrArg (fun f : MvPolynomial (Vars6 m) ℝ →+* ℝ => f (normalPolynomial6 M h)) he
    change MvPolynomial.eval z (H (normalPolynomial6 M h)) = _ at hp
    change MvPolynomial.eval z (H (normalPolynomial6 M h)) = 0 at hz
    rw [hp] at hz
    simpa [LinearMap.mem_ker,realNormalForm6,normalPolynomial6,map_sum,map_mul,y] using hz
  have hp := congrArg (fun f : MvPolynomial (Vars6 m) ℝ →+* ℝ => f P) he
  change MvPolynomial.eval z (zeroNormalCoordinates6 k (normalInverse6 M k P)) =
    MvPolynomial.eval (fun u => y u.1 u.2) P at hp
  rw [hp,hzero y hker,map_zero]

theorem normalInverse6_pderiv_X {m : ℕ} (M : Fin m → Fin 6 → ℤ)
    (k : Fin m → Fin 6) (h : Fin m) (u : Vars6 m) :
    MvPolynomial.pderiv (h,k h) (normalInverse6 M k (MvPolynomial.X u)) =
      MvPolynomial.C ((M h (k h) : ℝ)⁻¹) * (if (h,k h) = u then 1 else 0) := by
  classical
  rcases u with ⟨g,i⟩
  by_cases hg : g = h
  · subst g
    by_cases hi : i = k h
    · subst i
      have hs : MvPolynomial.pderiv (h,k h)
          (∑ j ∈ Finset.univ.erase (k h),
            MvPolynomial.C (M h j : ℝ) * MvPolynomial.X (h,j)) = 0 := by
        rw [map_sum]
        apply Finset.sum_eq_zero
        intro j hj
        simp [MvPolynomial.pderiv_C_mul,MvPolynomial.pderiv_X,Pi.single_apply,
          Prod.mk.injEq,Ne.symm (Finset.mem_erase.mp hj).1]
      simp only [normalInverse6,MvPolynomial.eval₂Hom_X',Prod.fst,Prod.snd,ite_true,
        MvPolynomial.pderiv_C_mul,map_sub,hs,MvPolynomial.pderiv_X,Pi.single_eq_same]
      simp
    · simp [normalInverse6,hi,MvPolynomial.pderiv_X,Pi.single_apply,Prod.mk.injEq,Ne.symm hi]
  · by_cases hi : i = k g <;>
      simp [normalInverse6,hi,MvPolynomial.pderiv_C_mul,MvPolynomial.pderiv_X,map_sum,
        Pi.single_apply,Prod.mk.injEq,hg,Ne.symm hg]

theorem normalInverse6_chain {m : ℕ} (M : Fin m → Fin 6 → ℤ)
    (k : Fin m → Fin 6) (h : Fin m) (P : MvPolynomial (Vars6 m) ℝ) :
    MvPolynomial.pderiv (h,k h) (normalInverse6 M k P) =
      MvPolynomial.C ((M h (k h) : ℝ)⁻¹) * normalInverse6 M k (MvPolynomial.pderiv (h,k h) P) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C c => simp [normalInverse6]
  | add P Q hP hQ => simp only [map_add,hP,hQ,mul_add]
  | mul_X P u hP =>
    rw [map_mul,MvPolynomial.pderiv_mul,hP,normalInverse6_pderiv_X,
      MvPolynomial.pderiv_mul,map_add,map_mul,MvPolynomial.pderiv_X]
    simp only [Pi.single_apply,apply_ite,map_one,map_zero]
    by_cases hu : u = (h,k h)
    · subst u
      simp
      ring
    · simp [hu,Ne.symm hu]
      ring

def normalCoordinateWeight6 {m : ℕ} (r : Fin m → ℕ) (k : Fin m → Fin 6)
    (b : Vars6 m →₀ ℕ) : ℝ := ∑ h, (b (h,k h) : ℝ) / r h

theorem normalCoordinateWeight6_add {m : ℕ} (r : Fin m → ℕ) (k : Fin m → Fin 6)
    (b c : Vars6 m →₀ ℕ) :
    normalCoordinateWeight6 r k (b+c) = normalCoordinateWeight6 r k b + normalCoordinateWeight6 r k c := by
  simp [normalCoordinateWeight6,Finsupp.add_apply,Nat.cast_add,add_div,Finset.sum_add_distrib]

theorem normalCoordinateWeight6_single {m : ℕ} (r : Fin m → ℕ) (k : Fin m → Fin 6) (h : Fin m) :
    normalCoordinateWeight6 r k (Finsupp.single (h,k h) 1) = 1/(r h : ℝ) := by
  have he (g : Fin m) : (Finsupp.single (h,k h) 1 : Vars6 m →₀ ℕ) (g,k g) =
      if g = h then 1 else 0 := by
    by_cases hg : g = h
    · subst g; simp
    · simp [Finsupp.single_apply,Prod.mk.injEq,Ne.symm hg,hg]
  simp only [normalCoordinateWeight6]
  simp_rw [he]
  simp [ite_div,Finset.sum_ite_eq,Finset.sum_ite_eq']

theorem normalInverse6_coeff_zero {m : ℕ} (M : Fin m → Fin 6 → ℤ)
    (k : Fin m → Fin 6) (hk : ∀ h, M h (k h) ≠ 0)
    (r : Fin m → ℕ) (c : ℝ) (P : MvPolynomial (Vars6 m) ℝ)
    (hindex : ∀ J : Vars6 m →₀ ℕ, rothSourceDerivativeWeight r J < c →
      ∀ y : Fin m → Fin 6 → ℝ, (∀ h, y h ∈ LinearMap.ker (realNormalForm6 (M h))) →
        MvPolynomial.eval (fun u => y u.1 u.2) (derivative6 J P) = 0)
    (J b : Vars6 m →₀ ℕ)
    (hbad : rothSourceDerivativeWeight r J + normalCoordinateWeight6 r k b < c) :
    (normalInverse6 M k (derivative6 J P)).coeff b = 0 := by
  classical
  have go : ∀ n : ℕ, ∀ J b : Vars6 m →₀ ℕ,
      (∑ h : Fin m, b (h,k h)) = n →
      rothSourceDerivativeWeight r J + normalCoordinateWeight6 r k b < c →
      (normalInverse6 M k (derivative6 J P)).coeff b = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro J b hn hw
      by_cases hnzero : n = 0
      · have hbzero : ∀ h, b (h,k h) = 0 := by
          intro h
          have hle : b (h,k h) ≤ ∑ g : Fin m, b (g,k g) :=
            Finset.single_le_sum (f := fun g : Fin m => b (g,k g)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ h)
          omega
        have hnonneg : 0 ≤ normalCoordinateWeight6 r k b := by
          unfold normalCoordinateWeight6
          positivity
        have hJ : rothSourceDerivativeWeight r J < c := by linarith
        have hz := normal_zero_restriction6 M k hk (derivative6 J P) (hindex J hJ)
        have he := congrArg (MvPolynomial.coeff b) hz
        rw [zeroNormalCoordinates6_coeff,if_pos hbzero,MvPolynomial.coeff_zero] at he
        exact he
      · have hex : ∃ h : Fin m, b (h,k h) ≠ 0 := by
          by_contra! hzero
          have hs : (∑ h : Fin m, b (h,k h)) = 0 := Finset.sum_eq_zero (fun h _ => hzero h)
          omega
        obtain ⟨h,hh⟩ := hex
        let d := b - Finsupp.single (h,k h) 1
        have hle : Finsupp.single (h,k h) 1 ≤ b := by rw [Finsupp.single_le_iff]; omega
        have hdeq : d + Finsupp.single (h,k h) 1 = b := tsub_add_cancel_of_le hle
        have hcount : (∑ g : Fin m, d (g,k g)) + 1 = n := by
          have hs := congrArg (fun b : Vars6 m →₀ ℕ => ∑ g : Fin m, b (g,k g)) hdeq
          have he (g : Fin m) : (Finsupp.single (h,k h) 1 : Vars6 m →₀ ℕ) (g,k g) =
              if g = h then 1 else 0 := by
            by_cases hg : g = h
            · subst g; simp
            · simp [Finsupp.single_apply,Prod.mk.injEq,Ne.symm hg,hg]
          simp_rw [Finsupp.add_apply,he] at hs
          simpa [Finset.sum_add_distrib,Finset.sum_ite_eq,Finset.sum_ite_eq',hn] using hs
        have hcoord : normalCoordinateWeight6 r k d + 1/(r h : ℝ) = normalCoordinateWeight6 r k b := by
          rw [← normalCoordinateWeight6_single r k h,← normalCoordinateWeight6_add,hdeq]
        have hz : (normalInverse6 M k (derivative6 (J+Finsupp.single (h,k h) 1) P)).coeff d = 0 := by
          apply ih (∑ g : Fin m, d (g,k g)) (by omega) _ d rfl
          rw [rothSource_weight_add,rothSource_weight_single]
          linarith
        have hd : (MvPolynomial.pderiv (h,k h) (normalInverse6 M k (derivative6 J P))).coeff d = 0 := by
          rw [normalInverse6_chain,rothSource_pderiv_hasse,map_nsmul,
            MvPolynomial.coeff_C_mul,MvPolynomial.coeff_smul,hz,smul_zero,mul_zero]
        rw [SourceSupport.pderiv_coeff,hdeq] at hd
        exact (mul_eq_zero.mp hd).resolve_left (Nat.cast_ne_zero.mpr (by omega))
  exact go _ J b rfl hbad

theorem normalForward6_monomial {m : ℕ} (M : Fin m → Fin 6 → ℤ)
    (k : Fin m → Fin 6) (b : Vars6 m →₀ ℕ) (a : ℝ) :
    normalForward6 M k (MvPolynomial.monomial b a) =
      MvPolynomial.C a * ((∏ h, (normalPolynomial6 M h) ^ b (h,k h)) *
        (∏ h, ∏ i ∈ Finset.univ.erase (k h), MvPolynomial.X (h,i) ^ b (h,i))) := by
  classical
  rw [normalForward6,MvPolynomial.eval₂Hom_monomial]
  rw [Finsupp.prod_fintype _ _ (fun _ => by simp),Fintype.prod_prod_type,
    ← Finset.prod_mul_distrib]
  congr 1
  apply Finset.prod_congr rfl
  intro h hh
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ (k h))]
  simp only [Prod.fst,Prod.snd,ite_true]
  have he : (∏ i ∈ Finset.univ.erase (k h),
      (if i = k h then normalPolynomial6 M h else MvPolynomial.X (h,i)) ^ b (h,i)) =
      ∏ i ∈ Finset.univ.erase (k h), MvPolynomial.X (h,i) ^ b (h,i) := by
    apply Finset.prod_congr rfl
    intro i hi
    rw [if_neg (Finset.mem_erase.mp hi).1]
  rw [he]
  ring

theorem normalForward6_monomial_mem {m : ℕ} (M : Fin m → Fin 6 → ℤ)
    (k : Fin m → Fin 6) (r : Fin m → ℕ) (c : ℝ)
    (b : Vars6 m →₀ ℕ) (a : ℝ) (hb : c ≤ normalCoordinateWeight6 r k b) :
    normalForward6 M k (MvPolynomial.monomial b a) ∈ sourceNormalIdeal6 M r c := by
  have hg : (∏ h, (normalPolynomial6 M h) ^ b (h,k h)) ∈ sourceNormalIdeal6 M r c :=
    Ideal.subset_span ⟨fun h => b (h,k h),hb,rfl⟩
  rw [normalForward6_monomial]
  have hm := Ideal.mul_mem_left (sourceNormalIdeal6 M r c)
    (MvPolynomial.C a * (∏ h, ∏ i ∈ Finset.univ.erase (k h), MvPolynomial.X (h,i) ^ b (h,i))) hg
  convert hm using 1
  ring

theorem sourceNormalIdeal6_of_derivative_restrictions {m : ℕ}
    (M : Fin m → Fin 6 → ℤ) (hM : ∀ h, M h ≠ 0)
    (r : Fin m → ℕ) (c : ℝ) (P : MvPolynomial (Vars6 m) ℝ)
    (hindex : ∀ J : Vars6 m →₀ ℕ, rothSourceDerivativeWeight r J < c →
      ∀ y : Fin m → Fin 6 → ℝ, (∀ h, y h ∈ LinearMap.ker (realNormalForm6 (M h))) →
        MvPolynomial.eval (fun u => y u.1 u.2) (derivative6 J P) = 0) :
    P ∈ sourceNormalIdeal6 M r c := by
  classical
  have hex (h : Fin m) : ∃ i : Fin 6, M h i ≠ 0 := by
    by_contra! hz
    exact hM h (funext hz)
  choose k hk using hex
  have hcoeff (b : Vars6 m →₀ ℕ) (hb : normalCoordinateWeight6 r k b < c) :
      (normalInverse6 M k P).coeff b = 0 := by
    have hz := normalInverse6_coeff_zero M k hk r c P hindex 0 b
      (by simpa [rothSourceDerivativeWeight] using hb)
    simpa only [derivative6_zero_index] using hz
  have hsupport (b) (hb : b ∈ (normalInverse6 M k P).support) :
      c ≤ normalCoordinateWeight6 r k b := by
    by_contra! hlt
    exact (MvPolynomial.mem_support_iff.mp hb) (hcoeff b hlt)
  have hsum := congrArg (normalForward6 M k) (normalInverse6 M k P).as_sum
  rw [normalForward6_inverse6 M k hk P,map_sum] at hsum
  rw [hsum]
  apply Ideal.sum_mem
  intro b hb
  exact normalForward6_monomial_mem M k r c b _ (hsupport b hb)

theorem integer_grid_high_normal_index6 {m : ℕ} (r : Fin m → ℕ) (hr : ∀ h, 0 < r h)
    (P : MvPolynomial (Vars6 m) ℤ) (hP : homogeneous6 r P)
    (w : Fin m → Fin 5 → Fin 6 → ℤ) (M : Fin m → Fin 6 → ℤ)
    (hM : ∀ h, M h ≠ 0)
    (hQ : ∀ h, LinearMap.ker (normalForm6 (M h)) =
      Submodule.span ℚ (Set.range (fun j i => (w h j i : ℚ))))
    (hR : ∀ h, LinearMap.ker (realNormalForm6 (M h)) =
      Submodule.span ℝ (Set.range (fun j i => (w h j i : ℝ))))
    (eta : ℝ) (heta : 0 < eta)
    (hgrid : ∀ a : Fin m → Fin 5 → ℕ, (∀ h j, 1 ≤ a h j ∧ a h j ≤ Nat.floor eta⁻¹+1) →
      ∀ J : Vars6 m →₀ ℕ, rothSourceDerivativeWeight r J < 2*eta*m →
        integerValue J P (gridPoint w a) = 0) :
    (∀ J : Vars6 m →₀ ℕ, rothSourceDerivativeWeight r J < (m : ℝ)*eta →
      (∀ y : Fin m → Fin 6 → ℚ, (∀ h, y h ∈ LinearMap.ker (normalForm6 (M h))) →
        MvPolynomial.eval (fun u => y u.1 u.2) (derivative6 J (P.map (Int.castRingHom ℚ))) = 0) ∧
      (∀ y : Fin m → Fin 6 → ℝ, (∀ h, y h ∈ LinearMap.ker (realNormalForm6 (M h))) →
        MvPolynomial.eval (fun u => y u.1 u.2) (derivative6 J (P.map (Int.castRingHom ℝ))) = 0)) ∧
    P.map (Int.castRingHom ℝ) ∈ sourceNormalIdeal6 M r ((m : ℝ)*eta) := by
  have hrestr : ∀ J : Vars6 m →₀ ℕ, rothSourceDerivativeWeight r J < (m : ℝ)*eta →
      (∀ y : Fin m → Fin 6 → ℚ, (∀ h, y h ∈ LinearMap.ker (normalForm6 (M h))) →
        MvPolynomial.eval (fun u => y u.1 u.2) (derivative6 J (P.map (Int.castRingHom ℚ))) = 0) ∧
      (∀ y : Fin m → Fin 6 → ℝ, (∀ h, y h ∈ LinearMap.ker (realNormalForm6 (M h))) →
        MvPolynomial.eval (fun u => y u.1 u.2) (derivative6 J (P.map (Int.castRingHom ℝ))) = 0) := by
    intro J hJ
    have hc : ∀ a : Fin m → Fin 5 → ℕ, (∀ h j, 1 ≤ a h j ∧ a h j ≤ Nat.floor eta⁻¹+1) →
        ∀ B : Vars6 m →₀ ℕ, (∀ h, (∑ i : Fin 6, B (h,i)) ≤ Nat.floor ((r h : ℝ)*eta)) →
          integerValue B (derivative6 J P) (gridPoint w a) = 0 := by
      intro a ha B hB
      exact hasse_grid_composition6 P J B _
        (hgrid a ha (B+J) (additional_cutoff6 r hr eta heta J B hJ hB))
    constructor
    · intro y hy
      apply integer_grid_rational_restriction6 r hr P hP J w eta heta hc y
      intro h
      rw [← hQ h]
      exact hy h
    · intro y hy
      apply integer_grid_real_restriction6 r hr P hP J w eta heta hc y
      intro h
      rw [← hR h]
      exact hy h
  exact ⟨hrestr,sourceNormalIdeal6_of_derivative_restrictions M hM r ((m : ℝ)*eta)
    (P.map (Int.castRingHom ℝ)) (fun J hJ => (hrestr J hJ).2)⟩

open SourceWeights Auxiliary6.SourceExpansion Auxiliary6.SourceBalance Auxiliary6.SourceVanishing

def sourceHighNormalIndex42 (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L) (c0 c2 c3 : Fin 4 → ℝ)
    (V : Set ℝ) (hQV : ∀ q ∈ V, 1 < q) : Prop :=
  ∃ delta6 : ℝ, 0 < delta6 ∧ delta6 < 1 ∧
  ∃ c : Fin 3 → Fin 6 → ℝ, (∀ tau i, |c tau i| ≤ 1) ∧
    (∑ tau, ∑ i, c tau i) = 0 ∧
    (∀ i, c 1 i = finiteWeight c2 i ∧ c 2 i = finiteWeight c3 i) ∧
  ∃ sigma : V → Equiv.Perm (Fin 6),
  ∃ hW : ∀ (q : V) i, 0 < actualWidths A2 A3 L hL q.val
    (hQV q.val q.property) c0 c2 c3 (sigma q) i,
  ∃ w : (q : V) → Fin 6 → directCompoundGroup42 A2 A3 q.val c2 c3,
  ∃ M a : V → Fin 6 → ℤ,
    (∀ q, M q ≠ 0 ∧ (∑ i, a q i*M q i) = 1 ∧
      Ideal.span (Set.range (M q)) = ⊤ ∧
      (∀ j : Fin 5, (∑ i, M q i*(w q j.castSucc : Fin 6 → ℤ) i) = 0) ∧
      LinearMap.ker (normalForm6 (M q)) =
        firstFiveSpan42 (fun j i => ((w q j : Fin 6 → ℤ) i : ℚ)) ∧
      LinearMap.ker (realNormalForm6 (M q)) =
        firstFiveSpan42 (fun j i => ((w q j : Fin 6 → ℤ) i : ℝ))) ∧
    (∀ q : V,
      let W := actualWidths A2 A3 L hL q.val (hQV q.val q.property) c0 c2 c3 (sigma q)
      let b := directRealBasis42 A2 A3 (q.val^(11 : ℕ)) (fun i => c2 i/11) (fun i => c3 i/11)
      let e := weightedCoordinates6 (compoundFormEquiv42 L hL) W (hW q)
      LinearIndependent ℝ (fun j => integerReal (w q j : Fin 6 → ℤ)) ∧
      LinearIndependent ℚ (fun j : Fin 5 => fun i => ((w q j.castSucc : Fin 6 → ℤ) i : ℚ)) ∧
      directCompoundGroup42 A2 A3 (q.val^(11 : ℕ)) (fun i => c2 i/11) (fun i => c3 i/11) =
        directCompoundGroup42 A2 A3 q.val c2 c3 ∧
      (∀ j, coordinateGauge6 e (integerReal (w q j : Fin 6 → ℤ)) = successiveRadius6 b e j) ∧
      (∀ j : Fin 5, ∀ i, ‖(compound L *ᵥ integerReal (w q j.castSucc : Fin 6 → ℤ)) i‖ ≤
        (q.val^(11 : ℕ))^(c 0 i-delta6)) ∧
      (∀ j : Fin 5, ∀ i, ‖(finiteMatrix 2 A2 *ᵥ
        (fun k => ((w q j.castSucc : Fin 6 → ℤ) k : ℚ_[2]))) i‖ ≤ (q.val^(11 : ℕ))^(c 1 i)) ∧
      (∀ j : Fin 5, ∀ i, ‖(finiteMatrix 3 A3 *ᵥ
        (fun k => ((w q j.castSucc : Fin 6 → ℤ) k : ℚ_[3]))) i‖ ≤ (q.val^(11 : ℕ))^(c 2 i))) ∧
  ∃ K : IntermediateField ℚ ℝ, FiniteDimensional ℚ K ∧
  ∃ hmem : ∀ tau s j, forms A2 A3 L tau s j ∈ K,
  ∃ D E : ℝ, 1 ≤ D ∧ 1 ≤ E ∧
  ∃ eta : ℝ, 0 < eta ∧ eta < 1 ∧ 1728*eta < delta6 ∧
  ∃ m : ℕ, 0 < m ∧ 4*(eta^2)⁻¹*Real.log (36*(Module.finrank ℚ K : ℝ)) ≤ (m : ℝ) ∧
  ∀ rho : ℝ, 0 < rho →
  ∃ t : Fin m → V, StrictMono (fun h => (t h).val) ∧ Set.Finite (Set.range t) ∧
    let Q : Fin m → ℝ := fun h => (t h).val^(11 : ℕ)
    (∀ h, 1 < Q h ∧ 64*E < (Q h)^eta ∧ 6*(eta⁻¹+1) < (Q h)^eta) ∧
    (∀ (h : Fin m) (hh : h.val+1 < m),
      (1+eta)*Real.log (Q h) ≤ rho*Real.log (Q ⟨h.val+1,hh⟩)) ∧
  ∃ (h0 : Fin m) (r : Fin m → ℕ), (∀ h, 0 < r h) ∧
    (∀ h, 0 < Real.log (Q h)) ∧ 0 < (r h0 : ℝ)*Real.log (Q h0) ∧
    (∀ (h : Fin m) (hh : h.val+1 < m), (r ⟨h.val+1,hh⟩ : ℝ) ≤ rho*(r h : ℝ)) ∧
    (∀ h, (r h0 : ℝ)*Real.log (Q h0) ≤ (r h : ℝ)*Real.log (Q h) ∧
      (r h : ℝ)*Real.log (Q h) ≤ (1+eta)*((r h0 : ℝ)*Real.log (Q h0))) ∧
  ∃ P : MvPolynomial (Vars6 m) ℤ, P ≠ 0 ∧ homogeneous6 r P ∧
    (height6 P : ℝ) ≤ D^(∑ h, r h) ∧ FieldIndex A2 A3 L K hmem r eta P ∧
    RealIndex A2 A3 L r eta P ∧
    (Claims r eta (compound L) P ∧ Claims r eta (finiteMatrix 2 A2) P ∧
      Claims r eta (finiteMatrix 3 A3) P) ∧
    (∀ J b : Vars6 m →₀ ℕ,
      ‖(expansion (compound L) J P).coeff b‖ ≤ E^(∑ h, r h) ∧
      ‖(expansion (finiteMatrix 2 A2) J P).coeff b‖ ≤ E^(∑ h, r h) ∧
      ‖(expansion (finiteMatrix 3 A3) J P).coeff b‖ ≤ E^(∑ h, r h)) ∧
    (∀ a : Fin m → Fin 5 → ℕ, (∀ h j, 1 ≤ a h j ∧ a h j ≤ Nat.floor eta⁻¹+1) →
    ∀ J : Vars6 m →₀ ℕ, rothSourceDerivativeWeight r J < 2*eta*m →
      integerValue J P (gridPoint (fun h j => (w (t h) j.castSucc : Fin 6 → ℤ)) a) = 0) ∧
    (∀ J : Vars6 m →₀ ℕ, rothSourceDerivativeWeight r J < (m : ℝ)*eta →
      (∀ y : Fin m → Fin 6 → ℚ, (∀ h, y h ∈ LinearMap.ker (normalForm6 (M (t h)))) →
        MvPolynomial.eval (fun u => y u.1 u.2) (derivative6 J (P.map (Int.castRingHom ℚ))) = 0) ∧
      (∀ y : Fin m → Fin 6 → ℝ, (∀ h, y h ∈ LinearMap.ker (realNormalForm6 (M (t h)))) →
        MvPolynomial.eval (fun u => y u.1 u.2) (derivative6 J (P.map (Int.castRingHom ℝ))) = 0)) ∧
    P.map (Int.castRingHom ℝ) ∈ sourceNormalIdeal6 (fun h => M (t h)) r ((m : ℝ)*eta)

theorem source_actual_high_normal_index6 (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L) (c0 c2 c3 : Fin 4 → ℝ)
    (V : Set ℝ) (hQV : ∀ q ∈ V, 1 < q)
    (hs : SourceBlocks.sourceBlockVanishing42 A2 A3 L hL c0 c2 c3 V hQV) :
    sourceHighNormalIndex42 A2 A3 L hL c0 c2 c3 V hQV := by
  rcases hs with ⟨delta,hd,hd1,c,hc,hbal,hfin,sigma,hW,w,hw,K,hK,hmem,D,E,hD,hE,
    eta,heta,heta1,hetad,m,hm,hmb,hblocks⟩
  have hex (q : V) := primitive_normal6 (fun j => (w q j : Fin 6 → ℤ))
    ((integer6_independent_iff42 _).mpr (hw q).1)
  choose M a hM ha hspan hann hker using hex
  have hnorm (q : V) := real_normal_kernel6 _ (hw q).1 _ (hM q) (hann q)
  refine ⟨delta,hd,hd1,c,hc,hbal,hfin,sigma,hW,w,M,a,?_,hw,K,hK,hmem,D,E,hD,hE,
    eta,heta,heta1,hetad,m,hm,hmb,?_⟩
  · intro q
    exact ⟨hM q,ha q,hspan q,hann q,hker q,hnorm q⟩
  · intro rho hrho
    obtain ⟨t,ht,hfinite,hgrowth,hsep,h0,r,hr,hlog,hA,hdegree,hbalance,P,hP,hhom,
      hheight,hfield,hreal,hclaims,hcoeff,hgrid⟩ := hblocks rho hrho
    refine ⟨t,ht,hfinite,hgrowth,hsep,h0,r,hr,hlog,hA,hdegree,hbalance,
      P,hP,hhom,hheight,hfield,hreal,hclaims,hcoeff,hgrid,?_⟩
    exact integer_grid_high_normal_index6 r hr P hhom
      (fun h j => (w (t h) j.castSucc : Fin 6 → ℤ)) (fun h => M (t h))
      (fun h => hM (t h)) (fun h => hker (t h)) (fun h => hnorm (t h)) eta heta hgrid

theorem source_compound_unbounded_high_normal_index42 (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (h2 : A2.det = 1) (h3 : A3.det = 1)
    (hL : L.det = 1) (hAlg : ∀ i j, IsAlgebraic ℚ (L i j))
    (delta4 : ℝ) (hd : 0 < delta4) (c0 c2 c3 : Fin 4 → ℝ)
    (hc0 : ∀ i, |c0 i| ≤ 1) (hc2 : ∀ i, -1 ≤ c2 i ∧ c2 i ≤ 0)
    (hc3 : ∀ i, -1 ≤ c3 i ∧ c3 i ≤ 0) (hbalance : (∑ i, (c0 i+c2 i+c3 i)) = 0)
    (U : Set ℝ) (hU : ¬ BddAbove U) (hQU : ∀ q ∈ U, 1 < q)
    (hgap : ∀ (q : ℝ) (hq : q ∈ U),
      sourceMinima4 A2 A3 L (sourceUnit42 L hL) q (hQU q hq) c0 c2 c3 1 <
      sourceMinima4 A2 A3 L (sourceUnit42 L hL) q (hQU q hq) c0 c2 c3 2 * q^(-delta4)) :
    ∃ (V : Set ℝ) (hVU : V ⊆ U), ¬ BddAbove V ∧
      fixedSourceWeights42 A2 A3 L (sourceUnit42 L hL) c0 c2 c3 delta4 V
        (fun q hq => hQU q (hVU hq)) ∧
      sourceHighNormalIndex42 A2 A3 L (sourceUnit42 L hL) c0 c2 c3 V
        (fun q hq => hQU q (hVU hq)) := by
  obtain ⟨V,hVU,hV,hfixed,hblocks⟩ := SourceBlocks.source_compound_unbounded_roth_blocks42
    A2 A3 L h2 h3 hL hAlg delta4 hd c0 c2 c3 hc0 hc2 hc3 hbalance U hU hQU hgap
  exact ⟨V,hVU,hV,hfixed,source_actual_high_normal_index6 A2 A3 L (sourceUnit42 L hL)
    c0 c2 c3 V (fun q hq => hQU q (hVU hq)) hblocks⟩

theorem sourceHighNormalIndex42_grid (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L) (c0 c2 c3 : Fin 4 → ℝ)
    (V : Set ℝ) (hQV : ∀ q ∈ V, 1 < q)
    (hs : sourceHighNormalIndex42 A2 A3 L hL c0 c2 c3 V hQV) :
    SourceBlocks.sourceBlockVanishing42 A2 A3 L hL c0 c2 c3 V hQV := by
  rcases hs with ⟨delta,hd,hd1,c,hc,hbal,hfin,sigma,hW,w,M,a,hM,hw,K,hK,hmem,D,E,hD,hE,
    eta,heta,heta1,hetad,m,hm,hmb,hblocks⟩
  refine ⟨delta,hd,hd1,c,hc,hbal,hfin,sigma,hW,w,hw,K,hK,hmem,D,E,hD,hE,
    eta,heta,heta1,hetad,m,hm,hmb,?_⟩
  intro rho hrho
  obtain ⟨t,ht,hfinite,hgrowth,hsep,h0,r,hr,hlog,hA,hdegree,hbalance,P,hP,hhom,
    hheight,hfield,hreal,hclaims,hcoeff,hgrid,hrestr,hindex⟩ := hblocks rho hrho
  exact ⟨t,ht,hfinite,hgrowth,hsep,h0,r,hr,hlog,hA,hdegree,hbalance,P,hP,hhom,
    hheight,hfield,hreal,hclaims,hcoeff,hgrid⟩

end CompoundFeasibility.SourceMultiblock
