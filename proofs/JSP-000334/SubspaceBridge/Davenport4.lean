import SubspaceBridge.OriginalMinima4
open scoped BigOperators Matrix
namespace CompoundFeasibility
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
end CompoundFeasibility
