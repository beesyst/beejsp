import SubspaceBridge.OriginalMinima4
import SubspaceBridge.OriginalMinimaProduct4
import SubspaceBridge.OriginalVariableGap4
import SubspaceBridge.OriginalLastDual4
open scoped BigOperators Matrix
namespace CompoundFeasibility.DavenportLiteral173
noncomputable section

theorem davenport_original_off_flag4 (b : Basis (Fin 4) ℝ (Fin 4 → ℝ))
    (e : (Fin 4 → ℝ) ≃ₗ[ℝ] (Fin 4 → ℝ)) (v : Fin 4 → (Fin 4 → ℝ))
    (hv : LinearIndependent ℝ v) (hvL : ∀ i, v i ∈ lattice4Span b)
    (hvr : ∀ i, coordinateGauge4 e (v i) = successiveRadius4 b e i)
    (j : Fin 4) (x : Fin 4 → ℝ) (hx : x ∈ lattice4Span b)
    (houtside : x ∉ minimaFlag4 v j) : successiveRadius4 b e j ≤ coordinateGauge4 e x := by
  classical
  obtain ⟨_, _, _, _, hm, _⟩ := exists_successive_minima4 b e
  let s := Finset.univ.filter (fun i => successiveRadius4 b e i = successiveRadius4 b e j)
  have hjs : j ∈ s := by simp [s]
  obtain ⟨r, hrs, hmin⟩ := Finset.exists_min_image s Fin.val ⟨j, hjs⟩
  have hr : successiveRadius4 b e r = successiveRadius4 b e j := (Finset.mem_filter.mp hrs).2
  have hrj : r ≤ j := hmin j hjs
  have hgap : ∀ i : Fin 4, i < r → successiveRadius4 b e i < successiveRadius4 b e r := by
    intro i hir
    have hle := hm (le_of_lt hir)
    apply lt_of_le_of_ne hle
    intro heq
    have his : i ∈ s := by simp [s, heq, hr]
    exact (not_le_of_gt hir) (hmin i his)
  by_contra h
  have hshort : coordinateGauge4 e x < successiveRadius4 b e r := by
    rw [hr]
    exact lt_of_not_ge h
  exact houtside (minimaFlag4_mono v _ _ hrj
    (lattice4Span_short_mem_minimaFlag b e v hv hvL hvr r hgap x hx hshort))

theorem davenport_pivot_step4 (k : ℕ) (W V : Submodule ℝ (Fin 4 → ℝ))
    (hW : Module.finrank ℝ W = k) (hV : Module.finrank ℝ V = k+1) (hWV : W ≤ V)
    (p : Fin k → Fin 4) (C : ℝ)
    (hbound : ∀ x ∈ W, ∀ M : ℝ, 0 ≤ M → (∀ i, |x (p i)| ≤ M) → ‖x‖ ≤ C*M) :
    ∃ a : Fin 4, a ∉ Set.range p ∧
      ∀ x ∈ V, ∀ M : ℝ, 0 ≤ M → (∀ i, |x (p i)| ≤ M) → |x a| ≤ M →
        ‖x‖ ≤ (2*C+1)*M := by
  classical
  let f : V →ₗ[ℝ] (Fin k → ℝ) :=
    { toFun := fun x i => x.val (p i)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hdim : Module.finrank ℝ (Fin k → ℝ) < Module.finrank ℝ V := by
    rw [hV]
    simp
  obtain ⟨z, hz, hzne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (LinearMap.ker_ne_bot_of_finrank_lt (f := f) hdim)
  let y : Fin 4 → ℝ := z.val
  have hyV : y ∈ V := z.property
  have hyne : y ≠ 0 := by
    intro h
    apply hzne
    exact Subtype.ext h
  have hyp (i : Fin k) : y (p i) = 0 := congrFun hz i
  have hyW : y ∉ W := by
    intro h
    have hzbound : ∀ i, |y (p i)| ≤ (0 : ℝ) := by
      intro i
      exact le_of_eq ((congrArg abs (hyp i)).trans (abs_zero))
    have hb : ‖y‖ ≤ C * 0 := hbound y h 0 (le_refl 0) hzbound
    have hn : ‖y‖ = 0 := le_antisymm (by simpa using hb) (norm_nonneg _)
    exact hyne (norm_eq_zero.mp hn)
  obtain ⟨a, _, ha⟩ := Finset.exists_max_image Finset.univ (fun i => |y i|) Finset.univ_nonempty
  have hnorm : ‖y‖ = |y a| := by
    apply le_antisymm
    · apply (pi_norm_le_iff_of_nonempty y).mpr
      intro i
      simpa only [Real.norm_eq_abs] using ha i (Finset.mem_univ i)
    · simpa only [Real.norm_eq_abs] using norm_le_pi_norm y a
  have haout : a ∉ Set.range p := by
    rintro ⟨i, hi⟩
    have hay : y a = 0 := hi ▸ hyp i
    exact hyne (norm_eq_zero.mp (by rw [hnorm, hay, abs_zero]))
  have hsupV : W ⊔ Submodule.span ℝ {y} ≤ V :=
    sup_le hWV (Submodule.span_le.mpr (by simpa only [Set.singleton_subset_iff] using hyV))
  have hstrict : W < W ⊔ Submodule.span ℝ {y} := by
    apply lt_of_le_of_ne le_sup_left
    intro heq
    apply hyW
    rw [heq]
    exact (show Submodule.span ℝ {y} ≤ W ⊔ Submodule.span ℝ {y} from le_sup_right)
      (Submodule.subset_span (Set.mem_singleton y))
  have hsup : W ⊔ Submodule.span ℝ {y} = V := by
    apply Submodule.eq_of_le_of_finrank_eq hsupV
    have hl := Submodule.finrank_lt_finrank_of_lt hstrict
    have hu := Submodule.finrank_mono hsupV
    omega
  refine ⟨a, haout, ?_⟩
  intro x hx M hM hp hxa
  have hxu : x ∈ W ⊔ Submodule.span ℝ {y} := hsup.symm ▸ hx
  obtain ⟨w, hw, t, ht, he⟩ := Submodule.mem_sup.mp hxu
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp ht
  have hwp (i : Fin k) : w (p i) = x (p i) := by
    have hh := congrFun he (p i)
    simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hyp i, mul_zero, add_zero] using hh
  have hwb : ‖w‖ ≤ C*M := hbound w hw M hM (by intro i; rw [hwp]; exact hp i)
  have hrel : c*y a = x a - w a := by
    have hh := congrFun he a
    change w a + c*y a = x a at hh
    linarith
  have hca : |c| * ‖y‖ ≤ M+‖w‖ := by
    calc
      |c| * ‖y‖ = |c*y a| := by rw [hnorm, abs_mul]
      _ = |x a-w a| := by rw [hrel]
      _ ≤ |x a|+|w a| := abs_sub _ _
      _ ≤ M+‖w‖ := add_le_add hxa (by simpa using norm_le_pi_norm w a)
  have hn : ‖x‖ ≤ ‖w‖+|c| * ‖y‖ := by
    rw [← he]
    simpa only [norm_smul, Real.norm_eq_abs] using norm_add_le w (c • y)
  nlinarith

def prefixSpan4 (v : Fin 4 → (Fin 4 → ℝ)) (k : ℕ) (hk : k ≤ 4) :
    Submodule ℝ (Fin 4 → ℝ) :=
  Submodule.span ℝ (Set.range (fun i : Fin k => v (Fin.castLE hk i)))

theorem prefixSpan4_finrank (v : Fin 4 → (Fin 4 → ℝ)) (hv : LinearIndependent ℝ v)
    (k : ℕ) (hk : k ≤ 4) : Module.finrank ℝ (prefixSpan4 v k hk) = k := by
  simpa only [prefixSpan4, Fintype.card_fin] using
    finrank_span_eq_card (hv.comp (Fin.castLE hk) (Fin.castLE_injective _))

theorem prefixSpan4_mono (v : Fin 4 → (Fin 4 → ℝ)) {i j : ℕ}
    (hi : i ≤ 4) (hj : j ≤ 4) (hij : i ≤ j) : prefixSpan4 v i hi ≤ prefixSpan4 v j hj := by
  apply Submodule.span_mono
  rintro _ ⟨k, rfl⟩
  exact ⟨Fin.castLE hij k, rfl⟩

theorem davenport_pivot_prefix4 (v : Fin 4 → (Fin 4 → ℝ)) (hv : LinearIndependent ℝ v)
    (k : ℕ) (hk : k ≤ 4) :
    ∃ p : Fin k → Fin 4, Function.Injective p ∧
      ∀ (j : ℕ) (hj : j ≤ k), ∀ x ∈ prefixSpan4 v j (hj.trans hk), ∀ M : ℝ, 0 ≤ M →
        (∀ i : Fin j, |x (p (Fin.castLE hj i))| ≤ M) → ‖x‖ ≤ ((2 : ℝ)^j-1)*M := by
  induction k with
  | zero =>
    refine ⟨Fin.elim0, ?_, ?_⟩
    · intro i
      exact Fin.elim0 i
    · intro j hj x hx M hM hcoords
      have hj0 : j = 0 := by omega
      subst j
      have hx0 : x = 0 := by simpa [prefixSpan4] using hx
      simp [hx0]
  | succ k ih =>
    have hk0 : k ≤ 4 := by omega
    obtain ⟨p, hp, hb⟩ := ih hk0
    have hbound : ∀ x ∈ prefixSpan4 v k hk0, ∀ M : ℝ, 0 ≤ M →
        (∀ i, |x (p i)| ≤ M) → ‖x‖ ≤ ((2 : ℝ)^k-1)*M := by
      intro x hx M hM hc
      exact hb k le_rfl x hx M hM hc
    obtain ⟨a, ha, hab⟩ := davenport_pivot_step4 k
      (prefixSpan4 v k hk0) (prefixSpan4 v (k+1) hk)
      (prefixSpan4_finrank v hv k hk0) (prefixSpan4_finrank v hv (k+1) hk)
      (prefixSpan4_mono v hk0 hk (Nat.le_succ k)) p ((2 : ℝ)^k-1) hbound
    let q : Fin (k+1) → Fin 4 := Fin.snoc p a
    have hq : Function.Injective q := by
      intro i j
      refine Fin.lastCases ?_ (fun i' => ?_) i
      · refine Fin.lastCases ?_ (fun j' => ?_) j
        · intro _
          rfl
        · intro h
          exact False.elim (ha ⟨j', (by simpa [q] using h.symm)⟩)
      · refine Fin.lastCases ?_ (fun j' => ?_) j
        · intro h
          exact False.elim (ha ⟨i', (by simpa [q] using h)⟩)
        · intro h
          exact congrArg Fin.castSucc (hp (by simpa [q] using h))
    refine ⟨q, hq, ?_⟩
    intro j hj x hx M hM hc
    by_cases hjk : j ≤ k
    · apply hb j hjk x hx M hM
      intro i
      have he : q (Fin.castLE hj i) = p (Fin.castLE hjk i) := by
        have heq : (Fin.castLE hj i : Fin (k+1)) = (Fin.castLE hjk i).castSucc := rfl
        rw [heq]
        simp only [q, Fin.snoc_castSucc]
      rw [← he]
      exact hc i
    · have hj' : j = k+1 := by omega
      subst j
      have hold (i : Fin k) : |x (p i)| ≤ M := by
        simpa only [Fin.castLE_rfl, id_eq, q, Fin.snoc_castSucc] using hc i.castSucc
      have hnew : |x a| ≤ M := by
        simpa only [Fin.castLE_rfl, id_eq, q, Fin.snoc_last] using hc (Fin.last k)
      have hn := hab x hx M hM hold hnew
      have hC : (2 * ((2 : ℝ)^k-1)+1)*M = ((2 : ℝ)^(k+1)-1)*M := by
        rw [pow_succ]
        ring
      rwa [hC] at hn

theorem prefixSpan4_map (e : (Fin 4 → ℝ) ≃ₗ[ℝ] (Fin 4 → ℝ))
    (v : Fin 4 → (Fin 4 → ℝ)) (k : ℕ) (hk : k ≤ 4) (x : Fin 4 → ℝ)
    (hx : x ∈ prefixSpan4 v k hk) : e x ∈ prefixSpan4 (e ∘ v) k hk := by
  have hs : (prefixSpan4 v k hk).map e.toLinearMap = prefixSpan4 (e ∘ v) k hk := by
    simp only [prefixSpan4, Submodule.map_span, ← Set.range_comp, Function.comp_def]
    rfl
  rw [← hs]
  exact Submodule.mem_map.mpr ⟨x, hx, rfl⟩

theorem davenport_flag_pivot4 (v : Fin 4 → (Fin 4 → ℝ)) (hv : LinearIndependent ℝ v) :
    ∃ p : Equiv.Perm (Fin 4), ∀ j : Fin 4,
      ∀ x ∈ prefixSpan4 v (j.val+1) (by omega), ∀ M : ℝ, 0 ≤ M →
        (∀ i : Fin (j.val+1), |x (p (Fin.castLE (by omega) i))| ≤ M) → ‖x‖ ≤ 16*M := by
  obtain ⟨p, hp, hb⟩ := davenport_pivot_prefix4 v hv 4 le_rfl
  let q : Equiv.Perm (Fin 4) := Equiv.ofBijective p (Finite.injective_iff_bijective.mp hp)
  refine ⟨q, ?_⟩
  intro j x hx M hM hc
  have hn := hb (j.val+1) (by omega) x hx M hM hc
  have hC : (2 : ℝ)^(j.val+1)-1 ≤ 16 := by fin_cases j <;> norm_num
  exact hn.trans (mul_le_mul_of_nonneg_right hC hM)

noncomputable def davenportCoordinates4 (e : (Fin 4 → ℝ) ≃ₗ[ℝ] (Fin 4 → ℝ))
    (deform : Fin 4 → ℝ) (sigma : Equiv.Perm (Fin 4)) (hd : ∀ i, 0 < deform i) :
    (Fin 4 → ℝ) ≃ₗ[ℝ] (Fin 4 → ℝ) :=
  weightedCoordinates4 e (fun i => (deform (sigma i))⁻¹) (fun i => inv_pos.mpr (hd _))

theorem davenportCoordinates4_apply (e : (Fin 4 → ℝ) ≃ₗ[ℝ] (Fin 4 → ℝ))
    (deform : Fin 4 → ℝ) (sigma : Equiv.Perm (Fin 4)) (hd : ∀ i, 0 < deform i)
    (x : Fin 4 → ℝ) (i : Fin 4) :
    davenportCoordinates4 e deform sigma hd x i = deform (sigma i) * e x i := by
  change e x i / (deform (sigma i))⁻¹ = _
  rw [div_inv_eq_mul, mul_comm]

theorem davenport_off_flag4_of_pivot (b : Basis (Fin 4) ℝ (Fin 4 → ℝ))
    (e : (Fin 4 → ℝ) ≃ₗ[ℝ] (Fin 4 → ℝ)) (v : Fin 4 → (Fin 4 → ℝ))
    (hv : LinearIndependent ℝ v) (hvL : ∀ i, v i ∈ lattice4Span b)
    (hvr : ∀ i, coordinateGauge4 e (v i) = successiveRadius4 b e i)
    (deform : Fin 4 → ℝ) (hd : ∀ i, 0 < deform i) (hanti : Antitone deform)
    (hscaled : Monotone (fun i => deform i * successiveRadius4 b e i))
    (p : Equiv.Perm (Fin 4))
    (hp : ∀ j : Fin 4, ∀ x ∈ prefixSpan4 (e ∘ v) (j.val+1) (by omega), ∀ M : ℝ, 0 ≤ M →
      (∀ i : Fin (j.val+1), |x (p (Fin.castLE (by omega) i))| ≤ M) → ‖x‖ ≤ 16*M) :
    ∀ j : Fin 4, ∀ x ∈ lattice4Span b, x ∉ minimaFlag4 v j →
      deform j * successiveRadius4 b e j / 16 ≤
        coordinateGauge4 (davenportCoordinates4 e deform p.symm hd) x := by
  classical
  intro j x hx hout
  let g := coordinateGauge4 (davenportCoordinates4 e deform p.symm hd) x
  have hg : 0 ≤ g := norm_nonneg _
  have hc (i : Fin 4) : deform i * |e x (p i)| ≤ g := by
    have hn := norm_le_pi_norm (davenportCoordinates4 e deform p.symm hd x) (p i)
    simpa only [Real.norm_eq_abs, davenportCoordinates4_apply, p.symm_apply_apply,
      abs_mul, abs_of_pos (hd i)] using hn
  let S := Finset.univ.filter (fun k : Fin 4 => x ∉ minimaFlag4 v k)
  have hjs : j ∈ S := by simp [S, hout]
  obtain ⟨k, hkS, hmax⟩ := Finset.exists_max_image S Fin.val ⟨j, hjs⟩
  have hkout : x ∉ minimaFlag4 v k := (Finset.mem_filter.mp hkS).2
  have hjk : j ≤ k := hmax j hjs
  have hxpre : x ∈ prefixSpan4 v (k.val+1) (by omega) := by
    by_cases hk : k.val+1 < 4
    · by_contra hnot
      let l : Fin 4 := ⟨k.val+1, hk⟩
      have hlS : l ∈ S := by
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        exact hnot
      have hle := hmax l hlS
      change k.val+1 ≤ k.val at hle
      omega
    · have htop : prefixSpan4 v (k.val+1) (by omega) = ⊤ := by
        apply Submodule.eq_top_of_finrank_eq
        rw [prefixSpan4_finrank v hv]
        simp only [Module.finrank_pi, Module.finrank_self, Fintype.card_fin, mul_one]
        omega
      rw [htop]
      exact Submodule.mem_top
  have hk4 : k.val+1 ≤ 4 := by omega
  let f : Fin (k.val+1) → Fin 4 := Fin.castLE hk4
  have hcoord (i : Fin (k.val+1)) : |e x (p (f i))| ≤ g / deform k := by
    apply (le_div_iff₀ (hd k)).mpr
    let l : Fin 4 := f i
    have hl : l ≤ k := by change i.val ≤ k.val; omega
    have hweight := mul_le_mul_of_nonneg_right (hanti hl) (abs_nonneg (e x (p l)))
    simpa only [mul_comm] using hweight.trans (hc l)
  have hnorm := hp k (e x) (prefixSpan4_map e v _ _ x hxpre) (g / deform k)
    (div_nonneg hg (hd k).le) hcoord
  have hlower := davenport_original_off_flag4 b e v hv hvL hvr k x hx hkout
  have hmul := mul_le_mul_of_nonneg_left (hlower.trans hnorm) (hd k).le
  have hcancel : deform k * (16 * (g / deform k)) = 16*g := by
    field_simp [(hd k).ne']
  rw [hcancel] at hmul
  have hmono := hscaled hjk
  change deform j * successiveRadius4 b e j / 16 ≤ g
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 16)).mpr
  exact hmono.trans (hmul.trans_eq (mul_comm 16 g))

theorem davenportCoordinates4_det (e : (Fin 4 → ℝ) ≃ₗ[ℝ] (Fin 4 → ℝ))
    (deform : Fin 4 → ℝ) (sigma : Equiv.Perm (Fin 4)) (hd : ∀ i, 0 < deform i)
    (hprod : (∏ i, deform i) = 1) :
    LinearMap.det (davenportCoordinates4 e deform sigma hd).toLinearMap = LinearMap.det e.toLinearMap := by
  rw [davenportCoordinates4, weightedCoordinates4_det, Finset.prod_inv_distrib,
    Equiv.prod_comp, hprod, inv_one, div_one]

theorem davenportBody4_volume (e : (Fin 4 → ℝ) ≃ₗ[ℝ] (Fin 4 → ℝ))
    (deform : Fin 4 → ℝ) (sigma : Equiv.Perm (Fin 4)) (hd : ∀ i, 0 < deform i)
    (hprod : (∏ i, deform i) = 1) :
    MeasureTheory.volume.real (parallelepipedBody4 (davenportCoordinates4 e deform sigma hd)) =
      MeasureTheory.volume.real (parallelepipedBody4 e) := by
  rw [parallelepipedBody4_volume, parallelepipedBody4_volume, davenportCoordinates4_det e deform sigma hd hprod]

theorem davenport_minima_lower4 (b : Basis (Fin 4) ℝ (Fin 4 → ℝ))
    (e' : (Fin 4 → ℝ) ≃ₗ[ℝ] (Fin 4 → ℝ)) (v : Fin 4 → (Fin 4 → ℝ))
    (hv : LinearIndependent ℝ v) (s : Fin 4 → ℝ)
    (hsep : ∀ j, ∀ x ∈ lattice4Span b, x ∉ minimaFlag4 v j → s j ≤ coordinateGauge4 e' x)
    (j : Fin 4) : s j ≤ successiveRadius4 b e' j := by
  obtain ⟨u, hu, huL, _, hm, hur⟩ := exists_successive_minima4 b e'
  let f : Fin (j.val+1) → Fin 4 := Fin.castLE (by omega)
  have hf : Function.Injective f := Fin.castLE_injective _
  obtain ⟨i, hi⟩ := independent_family_escapes_subspace4 (u ∘ f) (hu.comp f hf)
    (minimaFlag4 v j) (by rw [minimaFlag4_finrank v hv j]; omega)
  have hh := hsep j (u (f i)) (huL (f i)) hi
  rw [hur] at hh
  exact hh.trans (hm (show f i ≤ j from (by change i.val ≤ j.val; omega)))

theorem davenport_adapted_rows4 (v : Fin 4 → (Fin 4 → ℝ)) (hv : LinearIndependent ℝ v) :
    ∃ p : Equiv.Perm (Fin 4), ∃ y : Fin 4 → (Fin 4 → ℝ),
      (∀ j, v j - y j ∈ minimaFlag4 v j) ∧
      (∀ j i : Fin 4, i < j → y j (p i) = 0) ∧
      (∀ j : Fin 4, ‖y j‖ ≤ (2 : ℝ)^j.val * ‖v j‖) ∧
      ∀ j : Fin 4, ∀ x ∈ prefixSpan4 v (j.val+1) (by omega), ∀ M : ℝ, 0 ≤ M →
        (∀ i : Fin (j.val+1), |x (p (Fin.castLE (by omega) i))| ≤ M) → ‖x‖ ≤ 16*M := by
  classical
  obtain ⟨p, hp, hb⟩ := davenport_pivot_prefix4 v hv 4 le_rfl
  let q : Equiv.Perm (Fin 4) := Equiv.ofBijective p (Finite.injective_iff_bijective.mp hp)
  have hex (j : Fin 4) : ∃ w : minimaFlag4 v j,
      (∀ i : Fin j.val, w.val (q (Fin.castLE (by omega) i)) = v j (q (Fin.castLE (by omega) i))) ∧
      ‖w.val‖ ≤ ((2 : ℝ)^j.val-1)*‖v j‖ := by
    have hj4 : j.val ≤ 4 := Nat.le_of_lt j.isLt
    let f : minimaFlag4 v j →ₗ[ℝ] (Fin j.val → ℝ) :=
      { toFun := fun x i => x.val (q (Fin.castLE hj4 i))
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    have hf : Function.Injective f := by
      intro x1 x2 he
      apply Subtype.ext
      apply sub_eq_zero.mp
      apply norm_eq_zero.mp
      apply le_antisymm ?_ (norm_nonneg _)
      have hxW : x1.val-x2.val ∈ prefixSpan4 v j.val hj4 :=
        (minimaFlag4 v j).sub_mem x1.property x2.property
      have hzero (i : Fin j.val) : |(x1.val-x2.val) (p (Fin.castLE hj4 i))| ≤ (0 : ℝ) := by
        have hi := congrFun he i
        change x1.val (p (Fin.castLE hj4 i)) = x2.val (p (Fin.castLE hj4 i)) at hi
        change |x1.val (p (Fin.castLE hj4 i))-x2.val (p (Fin.castLE hj4 i))| ≤ (0 : ℝ)
        exact le_of_eq ((congrArg abs (sub_eq_zero.mpr hi)).trans abs_zero)
      have hn := hb j.val hj4 (x1.val-x2.val) hxW 0 le_rfl hzero
      simpa using hn
    have hdim : Module.finrank ℝ (minimaFlag4 v j) = Module.finrank ℝ (Fin j.val → ℝ) := by
      rw [minimaFlag4_finrank v hv j]
      simp
    have hsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim (f := f)).mp hf
    obtain ⟨w, hw⟩ := hsurj (fun i => v j (q (Fin.castLE hj4 i)))
    have hcoords (i : Fin j.val) : w.val (q (Fin.castLE hj4 i)) = v j (q (Fin.castLE hj4 i)) :=
      congrFun hw i
    refine ⟨w, hcoords, ?_⟩
    apply hb j.val hj4 w.val w.property ‖v j‖ (norm_nonneg _)
    intro i
    rw [show p (Fin.castLE hj4 i) = q (Fin.castLE hj4 i) from rfl, hcoords]
    simpa only [Real.norm_eq_abs] using norm_le_pi_norm (v j) (q (Fin.castLE hj4 i))
  choose w hw hnorm using hex
  refine ⟨q, fun j => v j-(w j).val, ?_, ?_, ?_, ?_⟩
  · intro j
    have he : v j-(v j-(w j).val) = (w j).val := by abel
    rw [he]
    exact (w j).property
  · intro j i hij
    let t : Fin j.val := ⟨i.val, hij⟩
    have hi : (Fin.castLE (by omega) t : Fin 4) = i := Fin.ext rfl
    have hh := hw j t
    rw [hi] at hh
    change v j (q i)-(w j).val (q i) = 0
    exact sub_eq_zero.mpr hh.symm
  · intro j
    have hn := norm_sub_le (v j) (w j).val
    have hb := hnorm j
    nlinarith
  · intro j x hx M hM hc
    have hn := hb (j.val+1) (by omega) x hx M hM hc
    have hC : (2 : ℝ)^(j.val+1)-1 ≤ 16 := by fin_cases j <;> norm_num
    exact hn.trans (mul_le_mul_of_nonneg_right hC hM)

theorem independent_prefix_adjustment4 (v w : Fin 4 → (Fin 4 → ℝ))
    (hv : LinearIndependent ℝ v) (hw : ∀ j, w j-v j ∈ minimaFlag4 v j) :
    LinearIndependent ℝ w := by
  classical
  let b := basisOfLinearIndependentOfCardEqFinrank hv (by simp)
  have hb (i : Fin 4) : b i = v i :=
    congrFun (coe_basisOfLinearIndependentOfCardEqFinrank hv _) i
  let f := b.equivFun
  have hbase (j i : Fin 4) : f (v j) i = if j = i then 1 else 0 := by
    rw [← hb j]
    exact b.equivFun_self j i
  have hzero (j i : Fin 4) (hji : j ≤ i) (x : Fin 4 → ℝ) (hx : x ∈ minimaFlag4 v j) :
      f x i = 0 := by
    let g : (Fin 4 → ℝ) →ₗ[ℝ] ℝ := (LinearMap.proj i).comp f.toLinearMap
    have hs : minimaFlag4 v j ≤ LinearMap.ker g := by
      apply Submodule.span_le.mpr
      rintro _ ⟨k, rfl⟩
      change f (v (Fin.castLE (by omega) k)) i = 0
      rw [hbase]
      have hne : (Fin.castLE (by omega) k : Fin 4) ≠ i := by
        intro heq
        have he := congrArg Fin.val heq
        change k.val = i.val at he
        omega
      simp only [hne, if_false]
    exact hs hx
  have hcoeff (j i : Fin 4) (hji : j ≤ i) : f (w j) i = f (v j) i := by
    have hz := hzero j i hji (w j-v j) (hw j)
    have he : f (w j-v j) i = f (w j) i-f (v j) i := by
      rw [map_sub]
      rfl
    rw [he] at hz
    exact sub_eq_zero.mp hz
  let T : Matrix (Fin 4) (Fin 4) ℝ := fun j i => f (w j) i
  have hdiag (i : Fin 4) : T i i = 1 := by
    change f (w i) i = 1
    rw [hcoeff i i le_rfl, hbase]
    simp
  have htri : T.transpose.BlockTriangular id := by
    intro i j hji
    change f (w j) i = 0
    rw [hcoeff j i (le_of_lt hji), hbase]
    exact if_neg (show j ≠ i from ne_of_lt hji)
  have hdet : T.det = 1 := by
    rw [← Matrix.det_transpose, Matrix.det_of_upperTriangular htri]
    simp only [Matrix.transpose_apply, hdiag, Finset.prod_const_one]
  have hunit : IsUnit T := (Matrix.isUnit_iff_isUnit_det T).mpr (by rw [hdet]; exact isUnit_one)
  have hrows : LinearIndependent ℝ (Matrix.row T) := Matrix.linearIndependent_rows_iff_isUnit.mpr hunit
  exact hrows.of_comp f.toLinearMap

theorem davenport_integral_reduce4 (Lambda : Submodule ℤ (Fin 4 → ℝ))
    (v : Fin 4 → (Fin 4 → ℝ)) (hvL : ∀ i, v i ∈ Lambda)
    (F : (Fin 4 → ℝ) ≃ₗ[ℝ] (Fin 4 → ℝ))
    (htri : ∀ i j : Fin 4, j < i → F (v j) i = 0)
    (hdiag : ∀ i : Fin 4, F (v i) i = 1)
    (k : ℕ) (hk : k ≤ 4) (x : Fin 4 → ℝ) (hx : x ∈ Lambda) :
    ∃ z ∈ Lambda, z-x ∈ prefixSpan4 v k hk ∧
      (∀ i : Fin 4, i.val < k → 0 ≤ F z i ∧ F z i < 1) ∧
      (∀ i : Fin 4, k ≤ i.val → F z i = F x i) := by
  classical
  induction k generalizing x with
  | zero =>
    refine ⟨x, hx, ?_, ?_, ?_⟩
    · simp only [sub_self]
      exact Submodule.zero_mem _
    · intro i hi
      omega
    · intro i hi
      rfl
  | succ k ih =>
    have hk0 : k ≤ 4 := by omega
    let a : Fin 4 := ⟨k, by omega⟩
    let n : ℤ := Int.floor (F x a)
    let x' : Fin 4 → ℝ := x-(n : ℝ) • v a
    have hx'L : x' ∈ Lambda := by
      apply Lambda.sub_mem hx
      simpa only [Int.cast_smul_eq_zsmul] using Lambda.smul_mem n (hvL a)
    obtain ⟨z, hzL, hzspan, hzlo, hzhi⟩ := ih hk0 x' hx'L
    have hdelta : x'-x ∈ prefixSpan4 v (k+1) hk := by
      have hva : v a ∈ prefixSpan4 v (k+1) hk :=
        Submodule.subset_span ⟨⟨k, Nat.lt_succ_self k⟩, rfl⟩
      have he : x'-x = -((n : ℝ) • v a) := by dsimp [x']; abel
      rw [he]
      exact (prefixSpan4 v (k+1) hk).neg_mem ((prefixSpan4 v (k+1) hk).smul_mem (n : ℝ) hva)
    have hfrac : F x' a = Int.fract (F x a) := by
      simp only [x', map_sub, map_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
        hdiag a, mul_one, n, Int.self_sub_floor]
    refine ⟨z, hzL, ?_, ?_, ?_⟩
    · have he : z-x = (z-x')+(x'-x) := by abel
      rw [he]
      exact (prefixSpan4 v (k+1) hk).add_mem
        (prefixSpan4_mono v hk0 hk (Nat.le_succ k) hzspan) hdelta
    · intro i hi
      by_cases hik : i.val < k
      · exact hzlo i hik
      · have hia : i = a := Fin.ext (by dsimp [a]; omega)
        subst i
        rw [hzhi a (by exact le_rfl), hfrac]
        exact ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
    · intro i hi
      rw [hzhi i (by omega)]
      have hai : a < i := by change k < i.val; omega
      simp only [x', map_sub, map_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
        htri i a hai, mul_zero, sub_zero]

theorem basis_prefix_coordinate_zero4 (b : Basis (Fin 4) ℝ (Fin 4 → ℝ))
    (j i : Fin 4) (hji : j ≤ i) (x : Fin 4 → ℝ) (hx : x ∈ minimaFlag4 b j) :
    b.equivFun x i = 0 := by
  let g : (Fin 4 → ℝ) →ₗ[ℝ] ℝ := (LinearMap.proj i).comp b.equivFun.toLinearMap
  have hs : minimaFlag4 b j ≤ LinearMap.ker g := by
    apply Submodule.span_le.mpr
    rintro _ ⟨k, rfl⟩
    change b.equivFun (b (Fin.castLE (by omega) k)) i = 0
    rw [b.equivFun_self]
    have hne : (Fin.castLE (by omega) k : Fin 4) ≠ i := by
      intro heq
      have he := congrArg Fin.val heq
      change k.val = i.val at he
      omega
    exact if_neg hne
  exact hs hx

theorem davenport_adapted_basis4 (v y : Fin 4 → (Fin 4 → ℝ)) (hv : LinearIndependent ℝ v)
    (hadapt : ∀ j, v j-y j ∈ minimaFlag4 v j) :
    ∃ b : Basis (Fin 4) ℝ (Fin 4 → ℝ), (∀ i, b i = y i) ∧
      ∀ j i : Fin 4, j ≤ i → b.equivFun (v j) i = if j = i then 1 else 0 := by
  classical
  have hy : LinearIndependent ℝ y := independent_prefix_adjustment4 v y hv (by
    intro j
    simpa only [neg_sub] using (minimaFlag4 v j).neg_mem (hadapt j))
  let b := basisOfLinearIndependentOfCardEqFinrank hy (by simp)
  have hb (i : Fin 4) : b i = y i :=
    congrFun (coe_basisOfLinearIndependentOfCardEqFinrank hy _) i
  have hbfun : (b : Fin 4 → (Fin 4 → ℝ)) = y := funext hb
  have hflags (j : Fin 4) : minimaFlag4 b j = minimaFlag4 v j := by
    apply Submodule.eq_of_le_of_finrank_eq
    · apply Submodule.span_le.mpr
      rintro _ ⟨k, rfl⟩
      let i : Fin 4 := Fin.castLE (by omega) k
      change b i ∈ minimaFlag4 v j
      rw [hb i]
      have hij : i ≤ j := by change k.val ≤ j.val; omega
      have hvj : v i ∈ minimaFlag4 v j := Submodule.subset_span ⟨k, rfl⟩
      have hwj : v i-y i ∈ minimaFlag4 v j := minimaFlag4_mono v _ _ hij (hadapt i)
      have he : v i-(v i-y i) = y i := by abel
      rw [← he]
      exact (minimaFlag4 v j).sub_mem hvj hwj
    · rw [minimaFlag4_finrank _ b.linearIndependent, minimaFlag4_finrank v hv]
  refine ⟨b, hb, ?_⟩
  intro j i hji
  have hx : v j-y j ∈ minimaFlag4 b j := (hflags j).symm ▸ hadapt j
  have hz := basis_prefix_coordinate_zero4 b j i hji (v j-y j) hx
  have he : b.equivFun (v j-y j) i = b.equivFun (v j) i-b.equivFun (y j) i := by
    rw [map_sub]
    rfl
  rw [he] at hz
  have hycoord : b.equivFun (y j) i = if j = i then 1 else 0 := by
    rw [← hb j]
    exact b.equivFun_self j i
  rw [← hycoord]
  exact sub_eq_zero.mp hz

theorem davenportCoordinates4_comp (e : (Fin 4 → ℝ) ≃ₗ[ℝ] (Fin 4 → ℝ))
    (deform : Fin 4 → ℝ) (sigma : Equiv.Perm (Fin 4)) (hd : ∀ i, 0 < deform i)
    (x : Fin 4 → ℝ) :
    davenportCoordinates4 e deform sigma hd x =
      davenportCoordinates4 (LinearEquiv.refl ℝ (Fin 4 → ℝ)) deform sigma hd (e x) := by
  ext i
  rw [davenportCoordinates4_apply, davenportCoordinates4_apply]
  rfl

theorem davenport_row_gauge_bound4 (y : Fin 4 → ℝ) (p : Equiv.Perm (Fin 4))
    (deform : Fin 4 → ℝ) (hd : ∀ i, 0 < deform i) (hanti : Antitone deform)
    (j : Fin 4) (hzero : ∀ i : Fin 4, i < j → y (p i) = 0) :
    coordinateGauge4 (davenportCoordinates4 (LinearEquiv.refl ℝ (Fin 4 → ℝ)) deform p.symm hd) y ≤
      deform j * ‖y‖ := by
  change ‖davenportCoordinates4 (LinearEquiv.refl ℝ (Fin 4 → ℝ)) deform p.symm hd y‖ ≤ _
  apply (pi_norm_le_iff_of_nonempty _).mpr
  intro a
  rw [Real.norm_eq_abs, davenportCoordinates4_apply]
  change |deform (p.symm a) * y a| ≤ _
  rw [abs_mul, abs_of_pos (hd _)]
  by_cases h : p.symm a < j
  · have hz : y a = 0 := by simpa only [p.apply_symm_apply] using hzero (p.symm a) h
    rw [hz, abs_zero, mul_zero]
    exact mul_nonneg (hd j).le (norm_nonneg _)
  · have hj : j ≤ p.symm a := le_of_not_gt h
    have hnorm : |y a| ≤ ‖y‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm y a
    exact (mul_le_mul_of_nonneg_right (hanti hj) (abs_nonneg _)).trans
      (mul_le_mul_of_nonneg_left hnorm (hd j).le)

theorem davenport_reduced_frame4 (b : Basis (Fin 4) ℝ (Fin 4 → ℝ))
    (e : (Fin 4 → ℝ) ≃ₗ[ℝ] (Fin 4 → ℝ)) (v : Fin 4 → (Fin 4 → ℝ))
    (hv : LinearIndependent ℝ v) (hvL : ∀ i, v i ∈ lattice4Span b)
    (hvr : ∀ i, coordinateGauge4 e (v i) = successiveRadius4 b e i)
    (deform : Fin 4 → ℝ) (hd : ∀ i, 0 < deform i) (hanti : Antitone deform)
    (hscaled : Monotone (fun i => deform i * successiveRadius4 b e i)) :
    ∃ p : Equiv.Perm (Fin 4), ∃ z : Fin 4 → (Fin 4 → ℝ), LinearIndependent ℝ z ∧
      (∀ i, z i ∈ lattice4Span b) ∧
      (∀ j, coordinateGauge4 (davenportCoordinates4 e deform p.symm hd) (z j) ≤
        16 * (deform j * successiveRadius4 b e j)) ∧
      ∀ j : Fin 4, ∀ x ∈ prefixSpan4 (e ∘ v) (j.val+1) (by omega), ∀ M : ℝ, 0 ≤ M →
        (∀ i : Fin (j.val+1), |x (p (Fin.castLE (by omega) i))| ≤ M) → ‖x‖ ≤ 16*M := by
  classical
  have he : LinearIndependent ℝ (e ∘ v) :=
    hv.map' e.toLinearMap (LinearMap.ker_eq_bot.mpr e.injective)
  obtain ⟨p, y, hyspan, hyzero, hynorm, hp⟩ := davenport_adapted_rows4 (e ∘ v) he
  obtain ⟨B, hB, hcoeff⟩ := davenport_adapted_basis4 (e ∘ v) y he hyspan
  let F : (Fin 4 → ℝ) ≃ₗ[ℝ] (Fin 4 → ℝ) := e.trans B.equivFun
  have htri (i j : Fin 4) (hji : j < i) : F (v j) i = 0 := by
    have h := hcoeff j i hji.le
    change B.equivFun (e (v j)) i = 0
    simpa only [Function.comp_apply, ne_of_lt hji, if_false] using h
  have hdiag (i : Fin 4) : F (v i) i = 1 := by
    simpa only [Function.comp_apply, if_pos rfl] using hcoeff i i le_rfl
  have hex (j : Fin 4) : ∃ z ∈ lattice4Span b, z-v j ∈ minimaFlag4 v j ∧
      (∀ i : Fin 4, i < j → 0 ≤ F z i ∧ F z i < 1) ∧
      (∀ i : Fin 4, j ≤ i → F z i = if j = i then 1 else 0) := by
    obtain ⟨z, hzL, hzspan, hzlo, hzhi⟩ :=
      davenport_integral_reduce4 (lattice4Span b) v hvL F htri hdiag j.val (by omega) (v j) (hvL j)
    refine ⟨z, hzL, hzspan, hzlo, ?_⟩
    intro i hji
    rw [hzhi i hji]
    exact hcoeff j i hji
  choose z hzL hzspan hzlo hzhi using hex
  have hz : LinearIndependent ℝ z := independent_prefix_adjustment4 v z hv hzspan
  let D := davenportCoordinates4 (LinearEquiv.refl ℝ (Fin 4 → ℝ)) deform p.symm hd
  have hybound (i : Fin 4) : coordinateGauge4 D (y i) ≤
      (2 : ℝ)^i.val * (deform i * successiveRadius4 b e i) := by
    have h0 := davenport_row_gauge_bound4 (y i) p deform hd hanti i (hyzero i)
    have h1 := mul_le_mul_of_nonneg_left (hynorm i) (hd i).le
    have h2 : deform i * ((2 : ℝ)^i.val * ‖(e ∘ v) i‖) =
        (2 : ℝ)^i.val * (deform i * successiveRadius4 b e i) := by
      change deform i * ((2 : ℝ)^i.val * coordinateGauge4 e (v i)) = _
      rw [hvr i]
      ring
    exact h0.trans (h1.trans_eq h2)
  refine ⟨p, z, hz, hzL, ?_, hp⟩
  intro j
  have haj : 0 ≤ deform j * successiveRadius4 b e j := by
    apply mul_nonneg (hd j).le
    rw [← hvr j]
    exact norm_nonneg _
  have hrepr : e (z j) = ∑ i : Fin 4, F (z j) i • y i := by
    have hh := B.sum_equivFun (e (z j))
    simpa only [hB] using hh.symm
  have hnorm : coordinateGauge4 (davenportCoordinates4 e deform p.symm hd) (z j) ≤
      ∑ i : Fin 4, (2 : ℝ)^i.val * (deform j * successiveRadius4 b e j) := by
    change ‖davenportCoordinates4 e deform p.symm hd (z j)‖ ≤ _
    rw [davenportCoordinates4_comp, hrepr, map_sum]
    simp only [map_smul]
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro i hi
    rw [norm_smul, Real.norm_eq_abs]
    by_cases hij : i ≤ j
    · have hcoef : |F (z j) i| ≤ 1 := by
        by_cases hlt : i < j
        · rw [abs_of_nonneg (hzlo j i hlt).1]
          exact (hzlo j i hlt).2.le
        · have heq : i = j := le_antisymm hij (le_of_not_gt hlt)
          subst i
          rw [hzhi j j le_rfl]
          norm_num
      have hm0 := mul_le_mul_of_nonneg_right hcoef (norm_nonneg (D (y i)))
      have hm1 := hybound i
      change ‖D (y i)‖ ≤ _ at hm1
      have hm2 := mul_le_mul_of_nonneg_left (hscaled hij) (by positivity : 0 ≤ (2 : ℝ)^i.val)
      rw [one_mul] at hm0
      exact hm0.trans (hm1.trans hm2)
    · have hji : j < i := lt_of_not_ge hij
      rw [hzhi j i hji.le, if_neg (ne_of_lt hji), abs_zero, zero_mul]
      exact mul_nonneg (by positivity) haj
  have hsum : (∑ i : Fin 4, (2 : ℝ)^i.val * (deform j * successiveRadius4 b e j)) =
      15 * (deform j * successiveRadius4 b e j) := by
    have hpow : (∑ i : Fin 4, (2 : ℝ)^i.val) = 15 := by
      rw [Fin.sum_univ_four]
      change (2 : ℝ)^0+2^1+2^2+2^3 = 15
      norm_num
    rw [← Finset.sum_mul, hpow]
  rw [hsum] at hnorm
  exact hnorm.trans (mul_le_mul_of_nonneg_right (by norm_num : (15 : ℝ) ≤ 16) haj)

theorem davenport_lemma4 (b : Basis (Fin 4) ℝ (Fin 4 → ℝ))
    (e : (Fin 4 → ℝ) ≃ₗ[ℝ] (Fin 4 → ℝ)) (v : Fin 4 → (Fin 4 → ℝ))
    (hv : LinearIndependent ℝ v) (hvL : ∀ i, v i ∈ lattice4Span b)
    (hvr : ∀ i, coordinateGauge4 e (v i) = successiveRadius4 b e i)
    (deform : Fin 4 → ℝ) (hd : ∀ i, 0 < deform i) (hprod : (∏ i, deform i) = 1)
    (hanti : Antitone deform) (hscaled : Monotone (fun i => deform i * successiveRadius4 b e i)) :
    ∃ sigma : Equiv.Perm (Fin 4),
      (∀ j, deform j * successiveRadius4 b e j / 16 ≤
          successiveRadius4 b (davenportCoordinates4 e deform sigma hd) j ∧
        successiveRadius4 b (davenportCoordinates4 e deform sigma hd) j ≤
          16 * (deform j * successiveRadius4 b e j)) ∧
      MeasureTheory.volume.real (parallelepipedBody4 (davenportCoordinates4 e deform sigma hd)) =
        MeasureTheory.volume.real (parallelepipedBody4 e) ∧
      ∀ j : Fin 4, ∀ x ∈ lattice4Span b, x ∉ minimaFlag4 v j →
        deform j * successiveRadius4 b e j / 16 ≤
          coordinateGauge4 (davenportCoordinates4 e deform sigma hd) x := by
  obtain ⟨p, z, hz, hzL, hzbound, hp⟩ := davenport_reduced_frame4 b e v hv hvL hvr deform hd hanti hscaled
  have hsep := davenport_off_flag4_of_pivot b e v hv hvL hvr deform hd hanti hscaled p hp
  refine ⟨p.symm, ?_, davenportBody4_volume e deform p.symm hd hprod, hsep⟩
  intro j
  refine ⟨davenport_minima_lower4 b _ v hv _ hsep j, ?_⟩
  let f : Fin (j.val+1) → Fin 4 := Fin.castLE (by omega)
  apply successiveRadius4_le_family b _ j (z ∘ f) (hz.comp f (Fin.castLE_injective _))
    (fun i => hzL (f i))
  intro i
  have hi : f i ≤ j := by change i.val ≤ j.val; omega
  exact (hzbound (f i)).trans (mul_le_mul_of_nonneg_left (hscaled hi) (by norm_num : (0 : ℝ) ≤ 16))

end
end CompoundFeasibility.DavenportLiteral173

open scoped BigOperators Matrix
namespace CompoundFeasibility.OriginalDeformationLiteral173
noncomputable section
open CompoundFeasibility.DavenportLiteral173


def literalGroup4 (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ) (Q : ℝ) (c2 c3 : Fin 4 → ℝ) :
    AddSubgroup (Fin 4 → ℤ) := sourceLattice4 A2 A3
      (fun i => Nat.ceil (JSP000334.qThreshold 2 Q (c2 i)))
      (fun i => Nat.ceil (JSP000334.qThreshold 3 Q (c3 i)))

def literalMinima4 (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L) (Q : ℝ) (hQ : 1 < Q)
    (c0 c2 c3 : Fin 4 → ℝ) (j : Fin 4) : ℝ :=
  sInf {r : ℝ | ∃ v : Fin (j.val+1) → (Fin 4 → ℝ), LinearIndependent ℝ v ∧
    (∀ i, ∃ x : Fin 4 → ℤ,
      x ∈ sourceLattice4 A2 A3
        (fun k => Nat.ceil (JSP000334.qThreshold 2 Q (c2 k)))
        (fun k => Nat.ceil (JSP000334.qThreshold 3 Q (c3 k))) ∧ integerReal x = v i) ∧
    ∀ i, ‖originalCoordinates4 L hL Q hQ c0 (v i)‖ ≤ r}

def literalRadius4 (b : Basis (Fin 4) ℝ (Fin 4 → ℝ))
    (e : (Fin 4 → ℝ) ≃ₗ[ℝ] (Fin 4 → ℝ)) (j : Fin 4) : ℝ :=
  sInf {r : ℝ | ∃ v : Fin (j.val+1) → (Fin 4 → ℝ), LinearIndependent ℝ v ∧
    (∀ i, v i ∈ lattice4Span b) ∧ ∀ i, ‖e (v i)‖ ≤ r}

def gapRadius4 (lam : Fin 4 → ℝ) : ℝ :=
  (lam 0 * lam 1 * lam 2 ^ 2) ^ ((1 : ℝ) / 4)

def gapDeformation4 (lam : Fin 4 → ℝ) (i : Fin 4) : ℝ :=
  gapRadius4 lam / lam (min i 2)

theorem gapRadius4_pos (lam : Fin 4 → ℝ) (hp : ∀ i, 0 < lam i) : 0 < gapRadius4 lam :=
  Real.rpow_pos_of_pos (mul_pos (mul_pos (hp 0) (hp 1)) (pow_pos (hp 2) 2)) _

theorem gapRadius4_power (lam : Fin 4 → ℝ) (hp : ∀ i, 0 < lam i) :
    gapRadius4 lam ^ (4 : ℕ) = lam 0 * lam 1 * lam 2 ^ 2 := by
  unfold gapRadius4
  have hpos : 0 < lam 0 * lam 1 * lam 2 ^ 2 :=
    mul_pos (mul_pos (hp 0) (hp 1)) (pow_pos (hp 2) 2)
  rw [← Real.rpow_natCast,← Real.rpow_mul hpos.le]
  norm_num

theorem gapRadius4_source_formula (lam : Fin 4 → ℝ) (hp : ∀ i, 0 < lam i) :
    gapRadius4 lam ^ (4 : ℕ) = (∏ i, lam i) * lam 2 / lam 3 := by
  rw [gapRadius4_power lam hp]
  rw [Fin.prod_univ_four]
  field_simp [(hp 3).ne']
  ring

theorem gapDeformation4_pos (lam : Fin 4 → ℝ) (hp : ∀ i, 0 < lam i) :
    ∀ i, 0 < gapDeformation4 lam i := fun i => div_pos (gapRadius4_pos lam hp) (hp _)

theorem gapDeformation4_product (lam : Fin 4 → ℝ) (hp : ∀ i, 0 < lam i) :
    (∏ i, gapDeformation4 lam i) = 1 := by
  change (∏ i, gapRadius4 lam / lam (min i 2)) = 1
  rw [Finset.prod_div_distrib]
  have hn : (∏ _i : Fin 4, gapRadius4 lam) = gapRadius4 lam ^ (4 : ℕ) := by simp
  have hden : (∏ i : Fin 4, lam (min i 2)) = lam 0 * lam 1 * lam 2 ^ 2 := by
    simp only [Fin.prod_univ_succ]
    change lam 0 * (lam 1 * (lam 2 * (lam 2 * 1))) = _
    ring
  rw [hn,hden,gapRadius4_power lam hp]
  exact div_self (ne_of_gt (mul_pos (mul_pos (hp 0) (hp 1)) (pow_pos (hp 2) 2)))

theorem gapDeformation4_antitone (lam : Fin 4 → ℝ) (hp : ∀ i, 0 < lam i)
    (hm : Monotone lam) : Antitone (gapDeformation4 lam) := by
  intro i j hij
  exact div_le_div_of_nonneg_left (gapRadius4_pos lam hp).le (hp _)
    (hm (min_le_min hij le_rfl))

theorem gapDeformation4_first (lam : Fin 4 → ℝ) (hp : ∀ i, 0 < lam i)
    (i : Fin 4) (hi : i ≤ 2) : gapDeformation4 lam i * lam i = gapRadius4 lam := by
  unfold gapDeformation4
  rw [min_eq_left hi]
  exact div_mul_cancel₀ _ (hp i).ne'

theorem gapDeformation4_last (lam : Fin 4 → ℝ) :
    gapDeformation4 lam 3 * lam 3 = gapRadius4 lam * lam 3 / lam 2 := by
  change (gapRadius4 lam / lam 2) * lam 3 = _
  ring

theorem gapDeformation4_scaled (lam : Fin 4 → ℝ) (hp : ∀ i, 0 < lam i)
    (hm : Monotone lam) : Monotone (fun i => gapDeformation4 lam i * lam i) := by
  have hlast : gapRadius4 lam ≤ gapDeformation4 lam 3 * lam 3 := by
    calc
      _ = (gapRadius4 lam / lam 2) * lam 2 := (div_mul_cancel₀ _ (hp 2).ne').symm
      _ ≤ (gapRadius4 lam / lam 2) * lam 3 :=
        mul_le_mul_of_nonneg_left (hm (by decide : (2 : Fin 4) ≤ 3))
          (div_pos (gapRadius4_pos lam hp) (hp 2)).le
      _ = _ := rfl
  intro i j hij
  change gapDeformation4 lam i * lam i ≤ gapDeformation4 lam j * lam j
  by_cases hj : j ≤ 2
  · rw [gapDeformation4_first lam hp i (hij.trans hj),gapDeformation4_first lam hp j hj]
  · have hj3 : j = 3 := by omega
    subst j
    by_cases hi : i ≤ 2
    · rw [gapDeformation4_first lam hp i hi]
      exact hlast
    · have hi3 : i = 3 := by omega
      subst i
      exact le_rfl

theorem gapRadius4_quantitative (lam : Fin 4 → ℝ) (hp : ∀ i, 0 < lam i)
    (C Q delta : ℝ) (hQ : 1 < Q) (hprod : (∏ i, lam i) ≤ C)
    (hgap : lam 2 < lam 3 * Q^(-delta)) :
    gapRadius4 lam ^ (4 : ℕ) < C*Q^(-delta) := by
  rw [gapRadius4_source_formula lam hp,mul_div_assoc]
  have hratio : lam 2 / lam 3 < Q^(-delta) := (div_lt_iff₀ (hp 3)).mpr (by simpa only [mul_comm] using hgap)
  exact (mul_lt_mul_of_pos_left hratio (Finset.prod_pos (fun i _ => hp i))).trans_le
    (mul_le_mul_of_nonneg_right hprod (Real.rpow_pos_of_pos (zero_lt_one.trans hQ) _).le)

theorem fourthRoot4_power (C : ℝ) (hC : 0 < C) :
    (C^((1 : ℝ)/4))^(4 : ℕ) = C := by
  rw [← Real.rpow_natCast,← Real.rpow_mul hC.le]
  norm_num

theorem gapRadius4_root_bound (lam : Fin 4 → ℝ) (hp : ∀ i, 0 < lam i)
    (C Q delta : ℝ) (hC : 0 < C) (hQ : 1 < Q)
    (hroot : gapRadius4 lam^(4 : ℕ) < C*Q^(-delta)) :
    gapRadius4 lam < C^((1 : ℝ)/4)*Q^(-delta/4) := by
  have hq : 0 < Q := zero_lt_one.trans hQ
  have hpow : (Q^(-delta/4))^(4 : ℕ) = Q^(-delta) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hq.le]
    congr 1
    ring
  apply lt_of_pow_lt_pow_left₀ 4
    (mul_pos (Real.rpow_pos_of_pos hC _) (Real.rpow_pos_of_pos hq _)).le
  rw [mul_pow,fourthRoot4_power C hC,hpow]
  exact hroot

theorem deformation_decay_absorb4 (r C Q delta : ℝ) (hQ : 1 < Q)
    (hroot : r^(4 : ℕ) < C*Q^(-delta))
    (hcut : (16 : ℝ)^4*C < Q^(delta/6)) :
    16*r < Q^(-5*delta/24) := by
  have hq : 0 < Q := zero_lt_one.trans hQ
  have he : (Q^(-5*delta/24))^(4 : ℕ) = Q^(-5*delta/6) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hq.le]
    congr 1
    ring
  have hmul : Q^(delta/6)*Q^(-delta) = Q^(-5*delta/6) := by
    rw [← Real.rpow_add hq]
    congr 1
    ring
  have hh : (16*r)^(4 : ℕ) < (Q^(-5*delta/24))^(4 : ℕ) := by
    rw [mul_pow,he]
    calc
      _ < (16 : ℝ)^4*(C*Q^(-delta)) := mul_lt_mul_of_pos_left hroot (by norm_num)
      _ = ((16 : ℝ)^4*C)*Q^(-delta) := by ring
      _ < Q^(delta/6)*Q^(-delta) :=
        mul_lt_mul_of_pos_right hcut (Real.rpow_pos_of_pos hq _)
      _ = _ := hmul
  exact lt_of_pow_lt_pow_left₀ 4 (Real.rpow_pos_of_pos hq _).le hh

theorem rescaled_small4 (Q delta x : ℝ) (hQ : 0 < Q)
    (hx : x < Q^(-5*delta/24)) : x < (Q^(5 : ℕ))^(-(delta/24)) := by
  have he : (Q^(5 : ℕ))^(-(delta/24)) = Q^(-5*delta/24) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hQ.le]
    congr 1
    ring
  rw [he]
  exact hx

theorem source_uniform_radius4
    (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ)
    (h2 : IsUnit A2) (h3 : IsUnit A3) (hL : IsUnit L)
    (delta : ℝ) (hd : 0 < delta) :
    ∃ C K T : ℝ, 0 < C ∧ 0 < K ∧ K = C^((1 : ℝ)/4) ∧ 1 < T ∧
      ∀ (Q : ℝ) (hQ : 1 < Q) (c0 c2 c3 : Fin 4 → ℝ),
      (∀ i, c2 i ≤ 0) → (∀ i, c3 i ≤ 0) → (∑ i, (c0 i+c2 i+c3 i) = 0) → T < Q →
      literalMinima4 A2 A3 L hL Q hQ c0 c2 c3 2 <
        literalMinima4 A2 A3 L hL Q hQ c0 c2 c3 3*Q^(-delta) →
      let lam := literalMinima4 A2 A3 L hL Q hQ c0 c2 c3
      gapRadius4 lam^(4 : ℕ) < C*Q^(-delta) ∧
      gapRadius4 lam < K*Q^(-delta/4) ∧ 16*gapRadius4 lam < Q^(-5*delta/24) := by
  obtain ⟨_,C,_,hC,hbounds⟩ :=
    OriginalMinimaProduct4.source_original_uniform_minima_two_sided4 A2 A3 L h2 h3 hL
  obtain ⟨T,hT,hcut⟩ := compound_gap_cutoff42 ((16 : ℝ)^4*C) (delta/3) (by positivity)
  refine ⟨C,C^((1 : ℝ)/4),T,hC,Real.rpow_pos_of_pos hC _,rfl,hT,?_⟩
  intro Q hQ c0 c2 c3 hc2 hc3 hb hTQ hgap
  have hp := (sourceMinima4_pos_mono A2 A3 L hL Q hQ c0 c2 c3).1
  have hroot := gapRadius4_quantitative _ hp C Q delta hQ (hbounds Q hQ c0 c2 c3 hc2 hc3 hb).2 hgap
  have hcut' : (16 : ℝ)^4*C < Q^(delta/6) := by
    convert hcut Q hTQ using 1 <;> congr 1 <;> ring
  exact ⟨hroot,gapRadius4_root_bound _ hp C Q delta hC hQ hroot,
    deformation_decay_absorb4 _ C Q delta hQ hroot hcut'⟩

def deformedWidths4 (Q : ℝ) (c0 : Fin 4 → ℝ) (d : Fin 4 → ℝ)
    (sigma : Equiv.Perm (Fin 4)) : Fin 4 → ℝ := fun i => Q^(c0 i)/d (sigma i)

def originalDeformedCoordinates4 (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c0 : Fin 4 → ℝ) (d : Fin 4 → ℝ)
    (sigma : Equiv.Perm (Fin 4)) (hd : ∀ i, 0 < d i) :
    (Fin 4 → ℝ) ≃ₗ[ℝ] (Fin 4 → ℝ) :=
  davenportCoordinates4 (originalCoordinates4 L hL Q hQ c0) d sigma hd

theorem originalDeformedCoordinates4_apply (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c0 : Fin 4 → ℝ) (d : Fin 4 → ℝ)
    (sigma : Equiv.Perm (Fin 4)) (hd : ∀ i, 0 < d i) (x : Fin 4 → ℝ) (i : Fin 4) :
    originalDeformedCoordinates4 L hL Q hQ c0 d sigma hd x i =
      d (sigma i)*(L *ᵥ x) i/Q^(c0 i) := by
  rw [originalDeformedCoordinates4,davenportCoordinates4_apply]
  change d (sigma i)*((L *ᵥ x) i/Q^(c0 i)) = _
  ring

theorem deformedWidths4_pos (Q : ℝ) (hQ : 0 < Q) (c0 : Fin 4 → ℝ)
    (d : Fin 4 → ℝ) (hd : ∀ i, 0 < d i) (sigma : Equiv.Perm (Fin 4)) :
    ∀ i, 0 < deformedWidths4 Q c0 d sigma i := fun i =>
  div_pos (Real.rpow_pos_of_pos hQ _) (hd _)

theorem deformedWidths4_balance (Q : ℝ) (hQ : 0 < Q) (c0 c2 c3 : Fin 4 → ℝ)
    (d : Fin 4 → ℝ) (hp : (∏ i, d i) = 1) (sigma : Equiv.Perm (Fin 4))
    (hb : (∑ i, (c0 i+c2 i+c3 i)) = 0) :
    (∏ i, deformedWidths4 Q c0 d sigma i)*(∏ i, Q^(c2 i+c3 i)) = 1 := by
  simp only [deformedWidths4,Finset.prod_div_distrib,Equiv.prod_comp,hp,div_one]
  rw [← Real.rpow_sum_of_pos hQ,← Real.rpow_sum_of_pos hQ,← Real.rpow_add hQ]
  have he : (∑ i, c0 i)+(∑ i, (c2 i+c3 i)) = 0 := by
    simpa only [Finset.sum_add_distrib,add_assoc] using hb
  rw [he,Real.rpow_zero]

def originalDeformedMinima4 (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L) (Q : ℝ) (hQ : 1 < Q)
    (c0 c2 c3 : Fin 4 → ℝ) (d : Fin 4 → ℝ) (sigma : Equiv.Perm (Fin 4))
    (hd : ∀ i, 0 < d i) (j : Fin 4) : ℝ :=
  literalRadius4 (sourceRealBasis4 A2 A3
    (fun i => Nat.ceil (JSP000334.qThreshold 2 Q (c2 i)))
    (fun i => Nat.ceil (JSP000334.qThreshold 3 Q (c3 i))))
    (originalDeformedCoordinates4 L hL Q hQ c0 d sigma hd) j

theorem source_original_davenport4 (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L) (Q : ℝ) (hQ : 1 < Q)
    (c0 c2 c3 : Fin 4 → ℝ) (u : Fin 4 → literalGroup4 A2 A3 Q c2 c3)
    (hu : LinearIndependent ℝ (fun i => integerReal (u i : Fin 4 → ℤ)))
    (hatt : ∀ i, coordinateGauge4 (originalCoordinates4 L hL Q hQ c0)
      (integerReal (u i : Fin 4 → ℤ)) = literalMinima4 A2 A3 L hL Q hQ c0 c2 c3 i) :
    let lam := literalMinima4 A2 A3 L hL Q hQ c0 c2 c3
    let d := gapDeformation4 lam
    ∃ hd : ∀ i, 0 < d i, (∏ i, d i) = 1 ∧ Antitone d ∧ Monotone (fun i => d i*lam i) ∧
      ∃ sigma : Equiv.Perm (Fin 4),
      (∀ j, d j*lam j/16 ≤ originalDeformedMinima4 A2 A3 L hL Q hQ c0 c2 c3 d sigma hd j ∧
        originalDeformedMinima4 A2 A3 L hL Q hQ c0 c2 c3 d sigma hd j ≤ 16*(d j*lam j)) ∧
      MeasureTheory.volume.real (parallelepipedBody4
        (originalDeformedCoordinates4 L hL Q hQ c0 d sigma hd)) =
          MeasureTheory.volume.real (parallelepipedBody4 (originalCoordinates4 L hL Q hQ c0)) ∧
      ∀ j : Fin 4, ∀ z : literalGroup4 A2 A3 Q c2 c3,
        integerReal (z : Fin 4 → ℤ) ∉ minimaFlag4 (fun i => integerReal (u i : Fin 4 → ℤ)) j →
        d j*lam j/16 ≤ coordinateGauge4 (originalDeformedCoordinates4 L hL Q hQ c0 d sigma hd)
          (integerReal (z : Fin 4 → ℤ)) := by
  dsimp only
  let b := sourceRealBasis4 A2 A3
    (fun i => Nat.ceil (JSP000334.qThreshold 2 Q (c2 i)))
    (fun i => Nat.ceil (JSP000334.qThreshold 3 Q (c3 i)))
  let e := originalCoordinates4 L hL Q hQ c0
  let lam := literalMinima4 A2 A3 L hL Q hQ c0 c2 c3
  let d := gapDeformation4 lam
  obtain ⟨hp,hm⟩ := sourceMinima4_pos_mono A2 A3 L hL Q hQ c0 c2 c3
  have hd : ∀ i, 0 < d i := gapDeformation4_pos lam hp
  have hprod : (∏ i, d i) = 1 := gapDeformation4_product lam hp
  have hanti : Antitone d := gapDeformation4_antitone lam hp hm
  have hscaled : Monotone (fun i => d i*lam i) := gapDeformation4_scaled lam hp hm
  have hrad (i : Fin 4) : lam i = successiveRadius4 b e i :=
    sourceMinima4_eq_radius A2 A3 L hL Q hQ c0 c2 c3 i
  have hmem (z : literalGroup4 A2 A3 Q c2 c3) : integerReal (z : Fin 4 → ℤ) ∈ lattice4Span b := by
    rw [sourceRealBasis4_span]
    exact ⟨(z : Fin 4 → ℤ),z.property,rfl⟩
  have hatt' (i : Fin 4) : coordinateGauge4 e (integerReal (u i : Fin 4 → ℤ)) =
      successiveRadius4 b e i := (hatt i).trans (hrad i)
  have hscaled' : Monotone (fun i => d i*successiveRadius4 b e i) := by
    simpa only [← hrad] using hscaled
  obtain ⟨sigma,hbounds,hvol,hsep⟩ := davenport_lemma4 b e
    (fun i => integerReal (u i : Fin 4 → ℤ)) hu (fun i => hmem (u i)) hatt' d hd hprod hanti hscaled'
  refine ⟨hd,hprod,hanti,hscaled,sigma,?_,hvol,?_⟩
  · intro j
    change d j*lam j/16 ≤ successiveRadius4 b (davenportCoordinates4 e d sigma hd) j ∧
      successiveRadius4 b (davenportCoordinates4 e d sigma hd) j ≤ 16*(d j*lam j)
    rw [hrad]
    exact hbounds j
  · intro j z hout
    change d j*lam j/16 ≤ coordinateGauge4 (davenportCoordinates4 e d sigma hd) (integerReal (z : Fin 4 → ℤ))
    rw [hrad]
    exact hsep j _ (hmem z) hout

theorem integerReal_norm_lower4 (z : Fin 4 → ℤ) (hz : z ≠ 0) : 1 ≤ ‖integerReal z‖ := by
  obtain ⟨i,hi⟩ := Function.ne_iff.mp hz
  have hi' : z i ≠ 0 := by simpa only [Pi.zero_apply] using hi
  have ha : (1 : ℝ) ≤ |(z i : ℝ)| := by exact_mod_cast Int.one_le_abs hi'
  exact ha.trans (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm (integerReal z) i)

theorem original_unweighted_bound4 (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c0 : Fin 4 → ℝ) (hc : ∀ i, |c0 i| ≤ 1) (x : Fin 4 → ℝ) :
    ‖originalFormEquiv4 L hL x‖ ≤ coordinateGauge4 (originalCoordinates4 L hL Q hQ c0) x * Q := by
  apply (pi_norm_le_iff_of_nonempty _).mpr
  intro i
  have hh := (originalCoordinates4_bounds L hL Q hQ c0 x _).mp le_rfl i
  have he : Q^(c0 i) ≤ Q := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hQ.le (abs_le.mp (hc i)).2
  exact hh.trans (mul_le_mul_of_nonneg_left he (norm_nonneg _))

theorem source_first_lower4 (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L) :
    ∃ D : ℝ, 0 < D ∧ ∀ (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ)
      (Q : ℝ) (hQ : 1 < Q) (c0 c2 c3 : Fin 4 → ℝ), (∀ i, |c0 i| ≤ 1) →
      1/(D*Q) ≤ literalMinima4 A2 A3 L hL Q hQ c0 c2 c3 0 := by
  let E := (originalFormEquiv4 L hL).toContinuousLinearEquiv
  let D := max 1 ‖E.symm.toContinuousLinearMap‖
  have hD : 0 < D := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨D,hD,?_⟩
  intro A2 A3 Q hQ c0 c2 c3 hc
  obtain ⟨u,hu,_,_,hatt,_⟩ := exists_sourceMinima4_attaining A2 A3 L hL Q hQ c0 c2 c3
  have hz : (u 0 : Fin 4 → ℤ) ≠ 0 := by
    intro hz
    apply hu.ne_zero 0
    rw [hz,map_zero]
  have hnorm := integerReal_norm_lower4 (u 0) hz
  have hinv : ‖integerReal (u 0 : Fin 4 → ℤ)‖ ≤ D*‖originalFormEquiv4 L hL
      (integerReal (u 0 : Fin 4 → ℤ))‖ := by
    have hi := E.symm.toContinuousLinearMap.le_opNorm (E (integerReal (u 0 : Fin 4 → ℤ)))
    simp only [ContinuousLinearEquiv.coe_coe,ContinuousLinearEquiv.symm_apply_apply] at hi
    exact hi.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))
  have hg := original_unweighted_bound4 L hL Q hQ c0 hc (integerReal (u 0 : Fin 4 → ℤ))
  rw [hatt] at hg
  change ‖originalFormEquiv4 L hL (integerReal (u 0 : Fin 4 → ℤ))‖ ≤
    literalMinima4 A2 A3 L hL Q hQ c0 c2 c3 0*Q at hg
  apply (div_le_iff₀ (mul_pos hD (zero_lt_one.trans hQ))).mpr
  nlinarith [mul_le_mul_of_nonneg_left hg hD.le,hnorm.trans hinv]

theorem last_upper_from_first4 (lam : Fin 4 → ℝ) (hp : ∀ i, 0 < lam i)
    (hm : Monotone lam) (C D Q : ℝ) (hD : 0 < D) (hQ : 0 < Q)
    (hprod : (∏ i, lam i) ≤ C) (hfirst : 1/(D*Q) ≤ lam 0) :
    lam 3 ≤ (C*D^3)*Q^3 := by
  have hlo : (lam 0)^3*lam 3 ≤ ∏ i, lam i := by
    have hi : (∏ i : Fin 4, if i = 3 then lam 3 else lam 0) ≤ ∏ i, lam i :=
      Finset.prod_le_prod (fun i _ => by split_ifs; exact (hp 3).le; exact (hp 0).le)
        (fun i _ => by split_ifs with h; subst i; exact le_rfl; exact hm (Fin.zero_le i))
    have he : (∏ i : Fin 4, if i = 3 then lam 3 else lam 0) = (lam 0)^3*lam 3 := by
      rw [Fin.prod_univ_four]
      change lam 0*lam 0*lam 0*lam 3 = (lam 0)^3*lam 3
      ring
    rw [he] at hi
    exact hi
  have hf : 1 ≤ D*Q*lam 0 := by
    simpa only [mul_comm] using (div_le_iff₀ (mul_pos hD hQ)).mp hfirst
  have hf3 : 1 ≤ (D*Q*lam 0)^3 := one_le_pow₀ hf
  calc
    lam 3 ≤ (D*Q*lam 0)^3*lam 3 := le_mul_of_one_le_left (hp 3).le hf3
    _ = (D*Q)^3*((lam 0)^3*lam 3) := by ring
    _ ≤ (D*Q)^3*C := mul_le_mul_of_nonneg_left (hlo.trans hprod) (by positivity)
    _ = _ := by ring

theorem source_uniform_basic_bounds4
    (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ)
    (h2 : IsUnit A2) (h3 : IsUnit A3) (hL : IsUnit L) :
    ∃ c C D K : ℝ, 0 < c ∧ 0 < C ∧ 0 < D ∧ 0 < K ∧ K = C*D^3 ∧
      ∀ (Q : ℝ) (hQ : 1 < Q) (c0 c2 c3 : Fin 4 → ℝ),
      (∀ i, |c0 i| ≤ 1) → (∀ i, c2 i ≤ 0) → (∀ i, c3 i ≤ 0) →
      (∑ i, (c0 i+c2 i+c3 i)) = 0 →
      let lam := literalMinima4 A2 A3 L hL Q hQ c0 c2 c3
      c ≤ (∏ i, lam i) ∧ (∏ i, lam i) ≤ C ∧ 1/(D*Q) ≤ lam 0 ∧ lam 3 ≤ K*Q^3 := by
  obtain ⟨c,C,hc,hC,hbounds⟩ :=
    OriginalMinimaProduct4.source_original_uniform_minima_two_sided4 A2 A3 L h2 h3 hL
  obtain ⟨D,hD,hfirst⟩ := source_first_lower4 L hL
  refine ⟨c,C,D,C*D^3,hc,hC,hD,by positivity,rfl,?_⟩
  intro Q hQ c0 c2 c3 hc0 hc2 hc3 hb
  obtain ⟨hp,hm⟩ := sourceMinima4_pos_mono A2 A3 L hL Q hQ c0 c2 c3
  have hf := hfirst A2 A3 Q hQ c0 c2 c3 hc0
  have hbd := hbounds Q hQ c0 c2 c3 hc2 hc3 hb
  exact ⟨hbd.1,hbd.2,hf,last_upper_from_first4 _ hp hm C D Q hD (zero_lt_one.trans hQ) hbd.2 hf⟩

theorem gapRadius4_le_root (lam : Fin 4 → ℝ) (hp : ∀ i, 0 < lam i) (hm : Monotone lam)
    (C : ℝ) (hC : 0 < C) (hprod : (∏ i, lam i) ≤ C) : gapRadius4 lam ≤ C^((1 : ℝ)/4) := by
  have hb : gapRadius4 lam^(4 : ℕ) ≤ C := by
    rw [gapRadius4_source_formula lam hp,mul_div_assoc]
    have hr : lam 2/lam 3 ≤ 1 := (div_le_one (hp 3)).mpr (hm (by decide))
    exact (mul_le_mul_of_nonneg_left hr (Finset.prod_pos (fun i _ => hp i)).le).trans
      (by simpa only [mul_one] using hprod)
  apply le_of_pow_le_pow_left₀ (by decide : (4 : ℕ) ≠ 0) (Real.rpow_pos_of_pos hC _).le
  rw [fourthRoot4_power C hC]
  exact hb

theorem gapRadius4_lower_scaled (lam : Fin 4 → ℝ) (hp : ∀ i, 0 < lam i) (hm : Monotone lam)
    (c : ℝ) (hc : 0 < c) (hprod : c ≤ ∏ i, lam i) :
    c^((1 : ℝ)/4)*lam 2 ≤ gapRadius4 lam*lam 3 := by
  have hmul : c*(lam 2)^4 ≤ (∏ i, lam i)*lam 2*(lam 3)^3 := by
    calc
      _ ≤ (∏ i, lam i)*(lam 2)^4 := mul_le_mul_of_nonneg_right hprod (by positivity)
      _ = ((∏ i, lam i)*lam 2)*(lam 2)^3 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (hp 2).le (hm (by decide : (2 : Fin 4) ≤ 3)) 3)
        (mul_pos (Finset.prod_pos (fun j _ => hp j)) (hp 2)).le
  have he : (gapRadius4 lam*lam 3)^(4 : ℕ) = (∏ i, lam i)*lam 2*(lam 3)^3 := by
    rw [mul_pow,gapRadius4_source_formula lam hp]
    field_simp [(hp 3).ne']
    ring
  apply le_of_pow_le_pow_left₀ (by decide : (4 : ℕ) ≠ 0)
    (mul_pos (gapRadius4_pos lam hp) (hp 3)).le
  rw [mul_pow,fourthRoot4_power c hc,he]
  exact hmul

theorem gapDeformation4_polynomial_bounds (lam : Fin 4 → ℝ) (hp : ∀ i, 0 < lam i)
    (hm : Monotone lam) (c C D K Q : ℝ) (hc : 0 < c) (hC : 0 < C)
    (hD : 0 < D) (hQ : 0 < Q) (hprodlo : c ≤ ∏ i, lam i) (hprodhi : (∏ i, lam i) ≤ C)
    (hfirst : 1/(D*Q) ≤ lam 0) (hlast : lam 3 ≤ K*Q^3) :
    ∀ i, gapDeformation4 lam i ≤ (D*C^((1 : ℝ)/4))*Q ∧
      (gapDeformation4 lam i)⁻¹ ≤ (K/c^((1 : ℝ)/4))*Q^3 := by
  have hr := gapRadius4_le_root lam hp hm C hC hprodhi
  have hlo := gapRadius4_lower_scaled lam hp hm c hc hprodlo
  have hcp : 0 < c^((1 : ℝ)/4) := Real.rpow_pos_of_pos hc _
  have hfirst' : 1 ≤ D*Q*lam 0 := by
    simpa only [mul_comm] using (div_le_iff₀ (mul_pos hD hQ)).mp hfirst
  intro i
  constructor
  · apply (div_le_iff₀ (hp (min i 2))).mpr
    have hfi : 1 ≤ D*Q*lam (min i 2) :=
      hfirst'.trans (mul_le_mul_of_nonneg_left (hm (Fin.zero_le _)) (mul_pos hD hQ).le)
    have hmul := mul_le_mul_of_nonneg_left hfi (Real.rpow_pos_of_pos hC ((1 : ℝ)/4)).le
    nlinarith
  · change (gapRadius4 lam/lam (min i 2))⁻¹ ≤ _
    rw [inv_div]
    have hmini : lam (min i 2) ≤ lam 2 := hm (min_le_right _ _)
    have hdiv : lam 2/gapRadius4 lam ≤ lam 3/c^((1 : ℝ)/4) :=
      (div_le_div_iff₀ (gapRadius4_pos lam hp) hcp).mpr (by nlinarith [hlo])
    calc
      _ ≤ lam 2/gapRadius4 lam := div_le_div_of_nonneg_right hmini (gapRadius4_pos lam hp).le
      _ ≤ lam 3/c^((1 : ℝ)/4) := hdiv
      _ ≤ (K*Q^3)/c^((1 : ℝ)/4) := div_le_div_of_nonneg_right hlast hcp.le
      _ = _ := by ring

theorem deformedWidths4_polynomial_bounds (lam : Fin 4 → ℝ) (hp : ∀ i, 0 < lam i)
    (hm : Monotone lam) (c C D K Q : ℝ) (hc : 0 < c) (hC : 0 < C)
    (hD : 0 < D) (hK : 0 < K) (hQ : 1 < Q) (c0 : Fin 4 → ℝ) (hc0 : ∀ i, |c0 i| ≤ 1)
    (hprodlo : c ≤ ∏ i, lam i) (hprodhi : (∏ i, lam i) ≤ C)
    (hfirst : 1/(D*Q) ≤ lam 0) (hlast : lam 3 ≤ K*Q^3)
    (sigma : Equiv.Perm (Fin 4)) :
    ∀ i, deformedWidths4 Q c0 (gapDeformation4 lam) sigma i ≤
        max (D*C^((1 : ℝ)/4)) (K/c^((1 : ℝ)/4))*Q^4 ∧
      (deformedWidths4 Q c0 (gapDeformation4 lam) sigma i)⁻¹ ≤
        max (D*C^((1 : ℝ)/4)) (K/c^((1 : ℝ)/4))*Q^4 := by
  have hq : 0 < Q := zero_lt_one.trans hQ
  have hb := gapDeformation4_polynomial_bounds lam hp hm c C D K Q hc hC hD hq
    hprodlo hprodhi hfirst hlast
  have hd := gapDeformation4_pos lam hp
  let B := max (D*C^((1 : ℝ)/4)) (K/c^((1 : ℝ)/4))
  have hB : 0 < B := (mul_pos hD (Real.rpow_pos_of_pos hC _)).trans_le (le_max_left _ _)
  intro i
  have hw : 0 < Q^(c0 i) := Real.rpow_pos_of_pos hq _
  have ha : Q^(c0 i) ≤ Q := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hQ.le (abs_le.mp (hc0 i)).2
  have hai : (Q^(c0 i))⁻¹ ≤ Q := by
    rw [← Real.rpow_neg hq.le]
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hQ.le
      (show -c0 i ≤ 1 by linarith [(abs_le.mp (hc0 i)).1])
  have hdi : (gapDeformation4 lam (sigma i))⁻¹ ≤ B*Q^3 :=
    (hb (sigma i)).2.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
  have hdhi : gapDeformation4 lam (sigma i) ≤ B*Q^3 := by
    have hq3 : Q ≤ Q^3 := le_self_pow₀ hQ.le (by decide)
    exact ((hb (sigma i)).1.trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hq.le)).trans
        (mul_le_mul_of_nonneg_left hq3 hB.le)
  constructor
  · change Q^(c0 i)/gapDeformation4 lam (sigma i) ≤ _
    rw [div_eq_mul_inv]
    have h := mul_le_mul ha hdi (inv_nonneg.mpr (hd _).le) hq.le
    convert h using 1 <;> ring
  · change (Q^(c0 i)/gapDeformation4 lam (sigma i))⁻¹ ≤ _
    rw [inv_div,div_eq_mul_inv]
    have h := mul_le_mul hdhi hai (inv_nonneg.mpr hw.le) (mul_pos hB (pow_pos hq 3)).le
    convert h using 1 <;> ring

theorem originalDeformedBody4_mem (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c0 : Fin 4 → ℝ) (d : Fin 4 → ℝ)
    (sigma : Equiv.Perm (Fin 4)) (hd : ∀ i, 0 < d i) (x : Fin 4 → ℝ) :
    x ∈ parallelepipedBody4 (originalDeformedCoordinates4 L hL Q hQ c0 d sigma hd) ↔
      ∀ i, |(L *ᵥ x) i| ≤ deformedWidths4 Q c0 d sigma i := by
  rw [mem_parallelepipedBody4_iff]
  change ‖originalDeformedCoordinates4 L hL Q hQ c0 d sigma hd x‖ ≤ 1 ↔ _
  rw [pi_norm_le_iff_of_nonempty]
  apply forall_congr'
  intro i
  rw [Real.norm_eq_abs,originalDeformedCoordinates4_apply,abs_div,abs_mul,
    abs_of_pos (hd _),abs_of_pos (Real.rpow_pos_of_pos (zero_lt_one.trans hQ) _)]
  change d (sigma i)*|(L *ᵥ x) i|/Q^(c0 i) ≤ 1 ↔ |(L *ᵥ x) i| ≤ Q^(c0 i)/d (sigma i)
  rw [div_le_iff₀ (Real.rpow_pos_of_pos (zero_lt_one.trans hQ) _),
    le_div_iff₀ (hd _),one_mul]
  constructor <;> intro h <;> simpa only [mul_comm] using h

theorem originalBody_gauge4 (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c0 : Fin 4 → ℝ) :
    parallelepipedBody4 (originalCoordinates4 L hL Q hQ c0) = originalBody4 L Q c0 := by
  ext x
  rw [mem_parallelepipedBody4_iff,originalBody4_mem_iff L hL Q hQ c0 x]
  rfl

theorem rescaled_power4 (Q c : ℝ) (hQ : 0 < Q) : (Q^(5 : ℕ))^(c/5) = Q^c := by
  rw [← Real.rpow_natCast,← Real.rpow_mul hQ.le]
  congr 1
  ring

theorem rescaled_threshold4 (p : ℕ) (Q c : ℝ) :
    JSP000334.qThreshold p (Q^(5 : ℕ)) (c/5) = JSP000334.qThreshold p Q c := by
  unfold JSP000334.qThreshold
  rw [Real.log_pow]
  ring

theorem source_finite_cutoff4 (Q : ℝ) (hQ : 1 < Q) (c : Fin 4 → ℝ)
    (hc : ∀ i, -1 ≤ c i ∧ c i ≤ 0) : ∀ i, Q^(-c i) < Q^(5 : ℕ) := by
  intro i
  have hb : Q^(-c i) ≤ Q := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hQ.le
      (show -c i ≤ 1 by linarith [(hc i).1])
  exact hb.trans_lt (by simpa only [pow_one] using pow_lt_pow_right₀ hQ (by decide : (1 : ℕ) < 5))

def deformationReady4 (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L) (Q : ℝ) (hQ : 1 < Q)
    (c0 c2 c3 : Fin 4 → ℝ) (delta : ℝ)
    (u : Fin 4 → literalGroup4 A2 A3 Q c2 c3) : Prop :=
  let lam := literalMinima4 A2 A3 L hL Q hQ c0 c2 c3
  let d := gapDeformation4 lam
  0 < gapRadius4 lam ∧ gapRadius4 lam^4 = (∏ i, lam i)*lam 2/lam 3 ∧
  ∃ hd : ∀ i, 0 < d i, (∏ i, d i) = 1 ∧ Antitone d ∧ Monotone (fun i => d i*lam i) ∧
  ∃ sigma : Equiv.Perm (Fin 4),
    (∀ i, 0 < deformedWidths4 Q c0 d sigma i) ∧
    (∏ i, deformedWidths4 Q c0 d sigma i)*(∏ i, Q^(c2 i+c3 i)) = 1 ∧
    (∀ j, d j*lam j/16 ≤ originalDeformedMinima4 A2 A3 L hL Q hQ c0 c2 c3 d sigma hd j ∧
      originalDeformedMinima4 A2 A3 L hL Q hQ c0 c2 c3 d sigma hd j ≤ 16*(d j*lam j)) ∧
    MeasureTheory.volume.real (parallelepipedBody4 (originalDeformedCoordinates4 L hL Q hQ c0 d sigma hd)) =
      MeasureTheory.volume.real (originalBody4 L Q c0) ∧
    (∀ j : Fin 4, ∀ z : literalGroup4 A2 A3 Q c2 c3,
      integerReal (z : Fin 4 → ℤ) ∉ minimaFlag4 (fun i => integerReal (u i : Fin 4 → ℤ)) j →
      d j*lam j/16 ≤ coordinateGauge4 (originalDeformedCoordinates4 L hL Q hQ c0 d sigma hd)
        (integerReal (z : Fin 4 → ℤ))) ∧
    originalDeformedMinima4 A2 A3 L hL Q hQ c0 c2 c3 d sigma hd 2 ≤ 16*gapRadius4 lam ∧
    originalDeformedMinima4 A2 A3 L hL Q hQ c0 c2 c3 d sigma hd 2 < Q^(-5*delta/24) ∧
    originalDeformedMinima4 A2 A3 L hL Q hQ c0 c2 c3 d sigma hd 2 < (Q^(5 : ℕ))^(-(delta/24)) ∧
    (∀ i, deformedWidths4 Q c0 d sigma i < Q^(5 : ℕ) ∧
      (deformedWidths4 Q c0 d sigma i)⁻¹ < Q^(5 : ℕ) ∧
      Q^(-c2 i) < Q^(5 : ℕ) ∧ Q^(-c3 i) < Q^(5 : ℕ)) ∧
    (∀ x, x ∈ parallelepipedBody4 (originalDeformedCoordinates4 L hL Q hQ c0 d sigma hd) ↔
      ∀ i, |(L *ᵥ x) i| ≤ deformedWidths4 Q c0 d sigma i) ∧
    (∀ i, (Q^(5 : ℕ))^(c2 i/5) = Q^(c2 i) ∧ (Q^(5 : ℕ))^(c3 i/5) = Q^(c3 i)) ∧
    (∀ (p : ℕ) i, JSP000334.qThreshold p (Q^(5 : ℕ)) (c2 i/5) = JSP000334.qThreshold p Q (c2 i) ∧
      JSP000334.qThreshold p (Q^(5 : ℕ)) (c3 i/5) = JSP000334.qThreshold p Q (c3 i))

theorem source_uniform_deformation4 (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (h2 : IsUnit A2) (h3 : IsUnit A3) (hL : IsUnit L)
    (delta : ℝ) (hd : 0 < delta) :
    ∃ T : ℝ, 1 < T ∧ ∀ (Q : ℝ) (hQ : 1 < Q) (c0 c2 c3 : Fin 4 → ℝ),
      (∀ i, |c0 i| ≤ 1) → (∀ i, -1 ≤ c2 i ∧ c2 i ≤ 0) → (∀ i, -1 ≤ c3 i ∧ c3 i ≤ 0) →
      (∑ i, (c0 i+c2 i+c3 i)) = 0 → T < Q →
      ∀ u : Fin 4 → literalGroup4 A2 A3 Q c2 c3,
      LinearIndependent ℝ (fun i => integerReal (u i : Fin 4 → ℤ)) →
      (∀ i, coordinateGauge4 (originalCoordinates4 L hL Q hQ c0)
        (integerReal (u i : Fin 4 → ℤ)) = literalMinima4 A2 A3 L hL Q hQ c0 c2 c3 i) →
      literalMinima4 A2 A3 L hL Q hQ c0 c2 c3 2 <
        literalMinima4 A2 A3 L hL Q hQ c0 c2 c3 3*Q^(-delta) →
      deformationReady4 A2 A3 L hL Q hQ c0 c2 c3 delta u := by
  obtain ⟨c,C,D,K,hc,hC,hD,hK,_,hbasic⟩ := source_uniform_basic_bounds4 A2 A3 L h2 h3 hL
  let B := max (D*C^((1 : ℝ)/4)) (K/c^((1 : ℝ)/4))
  obtain ⟨T0,hT0,hcut⟩ := compound_gap_cutoff42 ((16 : ℝ)^4*C) (delta/3) (by positivity)
  let T := max T0 (B+1)
  refine ⟨T,hT0.trans_le (le_max_left _ _),?_⟩
  intro Q hQ c0 c2 c3 hc0 hc2 hc3 hb hTQ u hu hatt hgap
  let lam := literalMinima4 A2 A3 L hL Q hQ c0 c2 c3
  obtain ⟨hp,hm⟩ := sourceMinima4_pos_mono A2 A3 L hL Q hQ c0 c2 c3
  obtain ⟨hlo,hhi,hfirst,hlast⟩ := hbasic Q hQ c0 c2 c3 hc0 (fun i => (hc2 i).2) (fun i => (hc3 i).2) hb
  have hroot := gapRadius4_quantitative lam hp C Q delta hQ hhi hgap
  have hcuteq : (16 : ℝ)^4*C < Q^(delta/6) := by
    convert hcut Q ((le_max_left _ _).trans_lt hTQ) using 1 <;> congr 1 <;> ring
  have hrsmall := deformation_decay_absorb4 _ C Q delta hQ hroot hcuteq
  obtain ⟨hdp,hprod,hanti,hscaled,sigma,hbounds,hvol,hsep⟩ :=
    source_original_davenport4 A2 A3 L hL Q hQ c0 c2 c3 u hu hatt
  have hu2 : originalDeformedMinima4 A2 A3 L hL Q hQ c0 c2 c3
      (gapDeformation4 lam) sigma hdp 2 ≤ 16*gapRadius4 lam := by
    have h := (hbounds 2).2
    rw [gapDeformation4_first lam hp 2 le_rfl] at h
    exact h
  have hsmall := hu2.trans_lt hrsmall
  have hwidth := deformedWidths4_polynomial_bounds lam hp hm c C D K Q hc hC hD hK hQ
    c0 hc0 hlo hhi hfirst hlast sigma
  have hBQ : B < Q := by
    have hBT : B+1 ≤ T := le_max_right _ _
    linarith
  have hlarge : B*Q^4 < Q^(5 : ℕ) := by
    calc
      _ < Q*Q^4 := mul_lt_mul_of_pos_right hBQ (pow_pos (zero_lt_one.trans hQ) 4)
      _ = _ := by ring
  refine ⟨gapRadius4_pos lam hp,gapRadius4_source_formula lam hp,hdp,hprod,hanti,hscaled,sigma,
    deformedWidths4_pos Q (zero_lt_one.trans hQ) c0 _ hdp sigma,
    deformedWidths4_balance Q (zero_lt_one.trans hQ) c0 c2 c3 _ hprod sigma hb,
    hbounds,hvol.trans (congrArg (fun S => MeasureTheory.volume.real S) (originalBody_gauge4 L hL Q hQ c0)),hsep,hu2,hsmall,rescaled_small4 Q delta _ (zero_lt_one.trans hQ) hsmall,?_,
    originalDeformedBody4_mem L hL Q hQ c0 _ sigma hdp,?_,?_⟩
  · intro i
    exact ⟨(hwidth i).1.trans_lt hlarge,(hwidth i).2.trans_lt hlarge,
      source_finite_cutoff4 Q hQ c2 hc2 i,source_finite_cutoff4 Q hQ c3 hc3 i⟩
  · intro i
    exact ⟨rescaled_power4 Q (c2 i) (zero_lt_one.trans hQ),rescaled_power4 Q (c3 i) (zero_lt_one.trans hQ)⟩
  · intro p i
    exact ⟨rescaled_threshold4 p Q (c2 i),rescaled_threshold4 p Q (c3 i)⟩

theorem rescaled_group4 (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ) (Q : ℝ) (c2 c3 : Fin 4 → ℝ) :
    literalGroup4 A2 A3 Q c2 c3 = literalGroup4 A2 A3 (Q^(5 : ℕ))
      (fun i => c2 i/5) (fun i => c3 i/5) := by
  simp only [literalGroup4,rescaled_threshold4]

theorem rescaled_finite_weights4 (c : Fin 4 → ℝ) (hc : ∀ i, -1 ≤ c i ∧ c i ≤ 0) :
    ∀ i, -1 ≤ c i/5 ∧ c i/5 ≤ 0 := by
  intro i
  constructor <;> linarith [(hc i).1,(hc i).2]

theorem fifth_image_unbounded4 (V : Set ℝ) (hV : ¬ BddAbove V) (hQV : ∀ q ∈ V, 1 < q) :
    ¬ BddAbove ((fun q : ℝ => q^(5 : ℕ)) '' V) := by
  rintro ⟨B,hB⟩
  obtain ⟨q,hq,hBq⟩ := not_bddAbove_iff.mp hV B
  have hpow : q ≤ q^(5 : ℕ) := le_self_pow₀ (hQV q hq).le (by decide)
  exact (not_lt_of_ge (hpow.trans (hB ⟨q,hq,rfl⟩))) hBq

theorem source_normalized_unbounded_deformation4
    (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ)
    (h2 : A2.det = 1) (h3 : A3.det = 1) (hL : L.det = 1)
    (_hAlg : ∀ i j, IsAlgebraic ℚ (L i j)) (delta : ℝ) (hd : 0 < delta)
    (c0 c2 c3 : Fin 4 → ℝ) (hc0 : ∀ i, |c0 i| ≤ 1)
    (hc2 : ∀ i, -1 ≤ c2 i ∧ c2 i ≤ 0) (hc3 : ∀ i, -1 ≤ c3 i ∧ c3 i ≤ 0)
    (hb : (∑ i, (c0 i+c2 i+c3 i)) = 0)
    (V : Set ℝ) (hV : ¬ BddAbove V) (hQV : ∀ q ∈ V, 1 < q)
    (hgap : ∀ (q : ℝ) (hq : q ∈ V),
      literalMinima4 A2 A3 L (sourceUnit42 L hL) q (hQV q hq) c0 c2 c3 2 <
        literalMinima4 A2 A3 L (sourceUnit42 L hL) q (hQV q hq) c0 c2 c3 3*q^(-delta)) :
    ∃ T : ℝ, 1 < T ∧
      ∃ u : (q : V) → Fin 4 → literalGroup4 A2 A3 q.val c2 c3,
      ¬ BddAbove V ∧ ¬ BddAbove {q : ℝ | q ∈ V ∧ T < q} ∧
      ¬ BddAbove ((fun q : ℝ => q^(5 : ℕ)) '' {q : ℝ | q ∈ V ∧ T < q}) ∧
      (∀ q : V, LinearIndependent ℝ (fun i => integerReal (u q i : Fin 4 → ℤ)) ∧
        ∀ i, coordinateGauge4 (originalCoordinates4 L (sourceUnit42 L hL) q.val
          (hQV q.val q.property) c0) (integerReal (u q i : Fin 4 → ℤ)) =
          literalMinima4 A2 A3 L (sourceUnit42 L hL) q.val (hQV q.val q.property) c0 c2 c3 i) ∧
      ∀ q : V, T < q.val →
        (1 < q.val^(5 : ℕ) ∧ 0 < delta/24) ∧
        literalGroup4 A2 A3 q.val c2 c3 =
          literalGroup4 A2 A3 (q.val^(5 : ℕ)) (fun i => c2 i/5) (fun i => c3 i/5) ∧
        deformationReady4 A2 A3 L (sourceUnit42 L hL) q.val (hQV q.val q.property) c0 c2 c3 delta (u q) := by
  obtain ⟨T,hT,hready⟩ := source_uniform_deformation4 A2 A3 L
    (sourceUnit42 A2 h2) (sourceUnit42 A3 h3) (sourceUnit42 L hL) delta hd
  obtain ⟨u,hVsame,hframes⟩ := OriginalLastDual4.source_original_last_dual_frame4
    A2 A3 L (sourceUnit42 L hL) c0 c2 c3 delta V hV hQV hgap
  refine ⟨T,hT,u,hVsame,JSP000334.sourceDual_unbounded_tail3 V hV T,
    fifth_image_unbounded4 _ (JSP000334.sourceDual_unbounded_tail3 V hV T) (fun q hq => hQV q hq.1),?_,?_⟩
  · intro q
    obtain ⟨hu,_,hatt,_,_,_,_,_,_⟩ := hframes q
    exact ⟨hu,hatt⟩
  · intro q hTQ
    obtain ⟨hu,_,hatt,_,_,_,_,_,_⟩ := hframes q
    exact ⟨⟨one_lt_pow₀ (hQV q.val q.property) (by decide),by positivity⟩,
      rescaled_group4 A2 A3 q.val c2 c3,
      hready q.val (hQV q.val q.property) c0 c2 c3 hc0 hc2 hc3 hb hTQ (u q) hu hatt
        (hgap q.val q.property)⟩

end
end CompoundFeasibility.OriginalDeformationLiteral173

#print axioms CompoundFeasibility.DavenportLiteral173.davenport_original_off_flag4
#print axioms CompoundFeasibility.DavenportLiteral173.davenport_pivot_step4
#print axioms CompoundFeasibility.DavenportLiteral173.prefixSpan4
#print axioms CompoundFeasibility.DavenportLiteral173.prefixSpan4_finrank
#print axioms CompoundFeasibility.DavenportLiteral173.prefixSpan4_mono
#print axioms CompoundFeasibility.DavenportLiteral173.davenport_pivot_prefix4
#print axioms CompoundFeasibility.DavenportLiteral173.prefixSpan4_map
#print axioms CompoundFeasibility.DavenportLiteral173.davenport_flag_pivot4
#print axioms CompoundFeasibility.DavenportLiteral173.davenportCoordinates4
#print axioms CompoundFeasibility.DavenportLiteral173.davenportCoordinates4_apply
#print axioms CompoundFeasibility.DavenportLiteral173.davenport_off_flag4_of_pivot
#print axioms CompoundFeasibility.DavenportLiteral173.davenportCoordinates4_det
#print axioms CompoundFeasibility.DavenportLiteral173.davenportBody4_volume
#print axioms CompoundFeasibility.DavenportLiteral173.davenport_minima_lower4
#print axioms CompoundFeasibility.DavenportLiteral173.davenport_adapted_rows4
#print axioms CompoundFeasibility.DavenportLiteral173.independent_prefix_adjustment4
#print axioms CompoundFeasibility.DavenportLiteral173.davenport_integral_reduce4
#print axioms CompoundFeasibility.DavenportLiteral173.basis_prefix_coordinate_zero4
#print axioms CompoundFeasibility.DavenportLiteral173.davenport_adapted_basis4
#print axioms CompoundFeasibility.DavenportLiteral173.davenportCoordinates4_comp
#print axioms CompoundFeasibility.DavenportLiteral173.davenport_row_gauge_bound4
#print axioms CompoundFeasibility.DavenportLiteral173.davenport_reduced_frame4
#print axioms CompoundFeasibility.DavenportLiteral173.davenport_lemma4
#print axioms CompoundFeasibility.OriginalDeformationLiteral173.gapRadius4
#print axioms CompoundFeasibility.OriginalDeformationLiteral173.gapDeformation4
#print axioms CompoundFeasibility.OriginalDeformationLiteral173.gapRadius4_pos
#print axioms CompoundFeasibility.OriginalDeformationLiteral173.gapRadius4_power
#print axioms CompoundFeasibility.OriginalDeformationLiteral173.gapRadius4_source_formula
#print axioms CompoundFeasibility.OriginalDeformationLiteral173.gapDeformation4_pos
#print axioms CompoundFeasibility.OriginalDeformationLiteral173.gapDeformation4_product
#print axioms CompoundFeasibility.OriginalDeformationLiteral173.gapDeformation4_antitone
#print axioms CompoundFeasibility.OriginalDeformationLiteral173.gapDeformation4_first
#print axioms CompoundFeasibility.OriginalDeformationLiteral173.gapDeformation4_last
#print axioms CompoundFeasibility.OriginalDeformationLiteral173.gapDeformation4_scaled
#print axioms CompoundFeasibility.OriginalDeformationLiteral173.gapRadius4_quantitative
#print axioms CompoundFeasibility.OriginalDeformationLiteral173.fourthRoot4_power
#print axioms CompoundFeasibility.OriginalDeformationLiteral173.gapRadius4_root_bound
#print axioms CompoundFeasibility.OriginalDeformationLiteral173.deformation_decay_absorb4
#print axioms CompoundFeasibility.OriginalDeformationLiteral173.rescaled_small4
#print axioms CompoundFeasibility.OriginalDeformationLiteral173.source_uniform_radius4
#print axioms CompoundFeasibility.OriginalDeformationLiteral173.deformedWidths4
#print axioms CompoundFeasibility.OriginalDeformationLiteral173.originalDeformedCoordinates4
#print axioms CompoundFeasibility.OriginalDeformationLiteral173.originalDeformedCoordinates4_apply
#print axioms CompoundFeasibility.OriginalDeformationLiteral173.deformedWidths4_pos
#print axioms CompoundFeasibility.OriginalDeformationLiteral173.deformedWidths4_balance
#print axioms CompoundFeasibility.OriginalDeformationLiteral173.originalDeformedMinima4
#print axioms CompoundFeasibility.OriginalDeformationLiteral173.source_original_davenport4
#print axioms CompoundFeasibility.OriginalDeformationLiteral173.integerReal_norm_lower4
#print axioms CompoundFeasibility.OriginalDeformationLiteral173.original_unweighted_bound4
#print axioms CompoundFeasibility.OriginalDeformationLiteral173.source_first_lower4
#print axioms CompoundFeasibility.OriginalDeformationLiteral173.last_upper_from_first4
#print axioms CompoundFeasibility.OriginalDeformationLiteral173.source_uniform_basic_bounds4
#print axioms CompoundFeasibility.OriginalDeformationLiteral173.gapRadius4_le_root
#print axioms CompoundFeasibility.OriginalDeformationLiteral173.gapRadius4_lower_scaled
#print axioms CompoundFeasibility.OriginalDeformationLiteral173.gapDeformation4_polynomial_bounds
#print axioms CompoundFeasibility.OriginalDeformationLiteral173.deformedWidths4_polynomial_bounds
#print axioms CompoundFeasibility.OriginalDeformationLiteral173.originalDeformedBody4_mem
#print axioms CompoundFeasibility.OriginalDeformationLiteral173.originalBody_gauge4
#print axioms CompoundFeasibility.OriginalDeformationLiteral173.rescaled_power4
#print axioms CompoundFeasibility.OriginalDeformationLiteral173.rescaled_threshold4
#print axioms CompoundFeasibility.OriginalDeformationLiteral173.source_finite_cutoff4
#print axioms CompoundFeasibility.OriginalDeformationLiteral173.deformationReady4
#print axioms CompoundFeasibility.OriginalDeformationLiteral173.source_uniform_deformation4
#print axioms CompoundFeasibility.OriginalDeformationLiteral173.rescaled_group4
#print axioms CompoundFeasibility.OriginalDeformationLiteral173.rescaled_finite_weights4
#print axioms CompoundFeasibility.OriginalDeformationLiteral173.source_normalized_unbounded_deformation4
#print axioms CompoundFeasibility.OriginalDeformationLiteral173.literalGroup4
#print axioms CompoundFeasibility.OriginalDeformationLiteral173.literalMinima4
#print axioms CompoundFeasibility.OriginalDeformationLiteral173.literalRadius4
#print CompoundFeasibility.OriginalDeformationLiteral173.source_normalized_unbounded_deformation4

#print axioms CompoundFeasibility.OriginalDeformationLiteral173.fifth_image_unbounded4
