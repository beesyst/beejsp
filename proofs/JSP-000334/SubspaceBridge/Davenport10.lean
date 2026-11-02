import SubspaceBridge.MinimaProduct10
open scoped BigOperators Matrix
namespace CompoundFeasibility
noncomputable section

def parallelepipedBody10 (e : (Fin 10 → ℝ) ≃ₗ[ℝ] (Fin 10 → ℝ)) : Set (Fin 10 → ℝ) :=
  e ⁻¹' Set.pi Set.univ (fun _ : Fin 10 => Set.Icc (-1 : ℝ) 1)

theorem mem_parallelepipedBody10_iff (e : (Fin 10 → ℝ) ≃ₗ[ℝ] (Fin 10 → ℝ)) (x : (Fin 10 → ℝ)) :
    x ∈ parallelepipedBody10 e ↔ coordinateGauge10 e x ≤ 1 := by
  simp [parallelepipedBody10, coordinateGauge10, pi_norm_le_iff_of_nonempty,
    Real.norm_eq_abs, abs_le, Pi.le_def, forall_and]

open scoped Pointwise in
theorem mem_dilate_parallelepipedBody10_iff (e : (Fin 10 → ℝ) ≃ₗ[ℝ] (Fin 10 → ℝ))
    (x : (Fin 10 → ℝ)) (r : ℝ) (hr : 0 < r) :
    x ∈ r • parallelepipedBody10 e ↔ coordinateGauge10 e x ≤ r := by
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ hr.ne', mem_parallelepipedBody10_iff]
  simp only [coordinateGauge10, map_smul, norm_smul, Real.norm_eq_abs, abs_inv,
    abs_of_pos hr]
  simpa using (inv_mul_le_iff₀ hr : r⁻¹ * ‖e x‖ ≤ 1 ↔ ‖e x‖ ≤ r * 1)

theorem parallelepipedBody10_volume (e : (Fin 10 → ℝ) ≃ₗ[ℝ] (Fin 10 → ℝ)) :
    MeasureTheory.volume.real (parallelepipedBody10 e) =
      1024 / |LinearMap.det e.toLinearMap| := by
  rw [MeasureTheory.measureReal_def, parallelepipedBody10,
    MeasureTheory.Measure.addHaar_preimage_linearEquiv,
    MeasureTheory.volume_pi, MeasureTheory.Measure.pi_pi]
  simp only [Real.volume_Icc, LinearEquiv.det_coe_symm, abs_inv,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal, abs_nonneg, div_eq_mul_inv]
  norm_num
  ring

theorem successiveRadius10_le_family (b : Basis (Fin 10) ℝ (Fin 10 → ℝ))
    (e : (Fin 10 → ℝ) ≃ₗ[ℝ] (Fin 10 → ℝ)) (k : Fin 10)
    (u : Fin (k.val + 1) → (Fin 10 → ℝ)) (hu : LinearIndependent ℝ u)
    (huL : ∀ i, u i ∈ lattice10Span b) (r : ℝ)
    (hr : ∀ i, coordinateGauge10 e (u i) ≤ r) :
    successiveRadius10 b e k ≤ r := by
  unfold successiveRadius10
  apply csInf_le (s := {s : ℝ | ∃ w : Fin (k.val + 1) → (Fin 10 → ℝ),
    LinearIndependent ℝ w ∧ (∀ i, w i ∈ lattice10Span b) ∧
      ∀ i, coordinateGauge10 e (w i) ≤ s}) _ ⟨u, hu, huL, hr⟩
  refine ⟨0, ?_⟩
  rintro s ⟨w, _, _, hw⟩
  exact (norm_nonneg (e (w 0))).trans (hw 0)

theorem lattice10Span_short_mem_minimaFlag (b : Basis (Fin 10) ℝ (Fin 10 → ℝ))
    (e : (Fin 10 → ℝ) ≃ₗ[ℝ] (Fin 10 → ℝ)) (v : Fin 10 → (Fin 10 → ℝ))
    (hv : LinearIndependent ℝ v) (hvL : ∀ i, v i ∈ lattice10Span b)
    (hvr : ∀ i, coordinateGauge10 e (v i) = successiveRadius10 b e i)
    (k : Fin 10) (hgap : ∀ i : Fin 10, i < k →
      successiveRadius10 b e i < successiveRadius10 b e k)
    (x : (Fin 10 → ℝ)) (hx : x ∈ lattice10Span b)
    (hxr : coordinateGauge10 e x < successiveRadius10 b e k) :
    x ∈ minimaFlag10 v k := by
  classical
  by_contra hxW
  let u : Fin k.val → (Fin 10 → ℝ) := fun i => v (Fin.castLE (by omega) i)
  have hu : LinearIndependent ℝ u := hv.comp _ (Fin.castLE_injective _)
  let w : Fin (k.val + 1) → (Fin 10 → ℝ) := Fin.snoc u x
  have hux : LinearIndependent ℝ w :=
    linearIndependent_fin_snoc.mpr ⟨hu, hxW⟩
  have hL : ∀ i : Fin (k.val + 1), w i ∈ lattice10Span b := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa [w] using hx
    · simpa [w, u] using hvL (Fin.castLE (by omega) j)
  have hlt : ∀ i : Fin (k.val + 1), coordinateGauge10 e (w i) < successiveRadius10 b e k := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa [w] using hxr
    · simpa [w, u, hvr] using hgap (Fin.castLE (by omega) j) (by exact j.isLt)
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ
    (fun i => coordinateGauge10 e (w i)) (Finset.univ_nonempty)
  have hle := successiveRadius10_le_family b e k w hux hL _
    (fun j => hi j (Finset.mem_univ j))
  exact (not_lt_of_ge hle) (hlt i)

theorem davenport_original_off_flag10 (b : Basis (Fin 10) ℝ (Fin 10 → ℝ))
    (e : (Fin 10 → ℝ) ≃ₗ[ℝ] (Fin 10 → ℝ)) (v : Fin 10 → (Fin 10 → ℝ))
    (hv : LinearIndependent ℝ v) (hvL : ∀ i, v i ∈ lattice10Span b)
    (hvr : ∀ i, coordinateGauge10 e (v i) = successiveRadius10 b e i)
    (j : Fin 10) (x : Fin 10 → ℝ) (hx : x ∈ lattice10Span b)
    (houtside : x ∉ minimaFlag10 v j) : successiveRadius10 b e j ≤ coordinateGauge10 e x := by
  classical
  obtain ⟨_, _, _, _, hm, _⟩ := exists_successive_minima10 b e
  let s := Finset.univ.filter (fun i => successiveRadius10 b e i = successiveRadius10 b e j)
  have hjs : j ∈ s := by simp [s]
  obtain ⟨r, hrs, hmin⟩ := Finset.exists_min_image s Fin.val ⟨j, hjs⟩
  have hr : successiveRadius10 b e r = successiveRadius10 b e j := (Finset.mem_filter.mp hrs).2
  have hrj : r ≤ j := hmin j hjs
  have hgap : ∀ i : Fin 10, i < r → successiveRadius10 b e i < successiveRadius10 b e r := by
    intro i hir
    have hle := hm (le_of_lt hir)
    apply lt_of_le_of_ne hle
    intro heq
    have his : i ∈ s := by simp [s, heq, hr]
    exact (not_le_of_gt hir) (hmin i his)
  by_contra h
  have hshort : coordinateGauge10 e x < successiveRadius10 b e r := by
    rw [hr]
    exact lt_of_not_ge h
  exact houtside (minimaFlag10_mono v _ _ hrj
    (lattice10Span_short_mem_minimaFlag b e v hv hvL hvr r hgap x hx hshort))

theorem davenport_pivot_step10 (k : ℕ) (W V : Submodule ℝ (Fin 10 → ℝ))
    (hW : Module.finrank ℝ W = k) (hV : Module.finrank ℝ V = k+1) (hWV : W ≤ V)
    (p : Fin k → Fin 10) (C : ℝ)
    (hbound : ∀ x ∈ W, ∀ M : ℝ, 0 ≤ M → (∀ i, |x (p i)| ≤ M) → ‖x‖ ≤ C*M) :
    ∃ a : Fin 10, a ∉ Set.range p ∧
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
  let y : Fin 10 → ℝ := z.val
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

def prefixSpan10 (v : Fin 10 → (Fin 10 → ℝ)) (k : ℕ) (hk : k ≤ 10) :
    Submodule ℝ (Fin 10 → ℝ) :=
  Submodule.span ℝ (Set.range (fun i : Fin k => v (Fin.castLE hk i)))

theorem prefixSpan10_finrank (v : Fin 10 → (Fin 10 → ℝ)) (hv : LinearIndependent ℝ v)
    (k : ℕ) (hk : k ≤ 10) : Module.finrank ℝ (prefixSpan10 v k hk) = k := by
  simpa only [prefixSpan10, Fintype.card_fin] using
    finrank_span_eq_card (hv.comp (Fin.castLE hk) (Fin.castLE_injective _))

theorem prefixSpan10_mono (v : Fin 10 → (Fin 10 → ℝ)) {i j : ℕ}
    (hi : i ≤ 10) (hj : j ≤ 10) (hij : i ≤ j) : prefixSpan10 v i hi ≤ prefixSpan10 v j hj := by
  apply Submodule.span_mono
  rintro _ ⟨k, rfl⟩
  exact ⟨Fin.castLE hij k, rfl⟩

theorem davenport_pivot_prefix10 (v : Fin 10 → (Fin 10 → ℝ)) (hv : LinearIndependent ℝ v)
    (k : ℕ) (hk : k ≤ 10) :
    ∃ p : Fin k → Fin 10, Function.Injective p ∧
      ∀ (j : ℕ) (hj : j ≤ k), ∀ x ∈ prefixSpan10 v j (hj.trans hk), ∀ M : ℝ, 0 ≤ M →
        (∀ i : Fin j, |x (p (Fin.castLE hj i))| ≤ M) → ‖x‖ ≤ ((2 : ℝ)^j-1)*M := by
  induction k with
  | zero =>
    refine ⟨Fin.elim0, ?_, ?_⟩
    · intro i
      exact Fin.elim0 i
    · intro j hj x hx M hM hcoords
      have hj0 : j = 0 := by omega
      subst j
      have hx0 : x = 0 := by simpa [prefixSpan10] using hx
      simp [hx0]
  | succ k ih =>
    have hk0 : k ≤ 10 := by omega
    obtain ⟨p, hp, hb⟩ := ih hk0
    have hbound : ∀ x ∈ prefixSpan10 v k hk0, ∀ M : ℝ, 0 ≤ M →
        (∀ i, |x (p i)| ≤ M) → ‖x‖ ≤ ((2 : ℝ)^k-1)*M := by
      intro x hx M hM hc
      exact hb k le_rfl x hx M hM hc
    obtain ⟨a, ha, hab⟩ := davenport_pivot_step10 k
      (prefixSpan10 v k hk0) (prefixSpan10 v (k+1) hk)
      (prefixSpan10_finrank v hv k hk0) (prefixSpan10_finrank v hv (k+1) hk)
      (prefixSpan10_mono v hk0 hk (Nat.le_succ k)) p ((2 : ℝ)^k-1) hbound
    let q : Fin (k+1) → Fin 10 := Fin.snoc p a
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

theorem prefixSpan10_map (e : (Fin 10 → ℝ) ≃ₗ[ℝ] (Fin 10 → ℝ))
    (v : Fin 10 → (Fin 10 → ℝ)) (k : ℕ) (hk : k ≤ 10) (x : Fin 10 → ℝ)
    (hx : x ∈ prefixSpan10 v k hk) : e x ∈ prefixSpan10 (e ∘ v) k hk := by
  have hs : (prefixSpan10 v k hk).map e.toLinearMap = prefixSpan10 (e ∘ v) k hk := by
    simp only [prefixSpan10, Submodule.map_span, ← Set.range_comp, Function.comp_def]
    rfl
  rw [← hs]
  exact Submodule.mem_map.mpr ⟨x, hx, rfl⟩

theorem davenport_flag_pivot10 (v : Fin 10 → (Fin 10 → ℝ)) (hv : LinearIndependent ℝ v) :
    ∃ p : Equiv.Perm (Fin 10), ∀ j : Fin 10,
      ∀ x ∈ prefixSpan10 v (j.val+1) (by omega), ∀ M : ℝ, 0 ≤ M →
        (∀ i : Fin (j.val+1), |x (p (Fin.castLE (by omega) i))| ≤ M) → ‖x‖ ≤ 1024*M := by
  obtain ⟨p, hp, hb⟩ := davenport_pivot_prefix10 v hv 10 le_rfl
  let q : Equiv.Perm (Fin 10) := Equiv.ofBijective p (Finite.injective_iff_bijective.mp hp)
  refine ⟨q, ?_⟩
  intro j x hx M hM hc
  have hn := hb (j.val+1) (by omega) x hx M hM hc
  have hC : (2 : ℝ)^(j.val+1)-1 ≤ 1024 := by fin_cases j <;> norm_num
  exact hn.trans (mul_le_mul_of_nonneg_right hC hM)

noncomputable def davenportCoordinates10 (e : (Fin 10 → ℝ) ≃ₗ[ℝ] (Fin 10 → ℝ))
    (deform : Fin 10 → ℝ) (sigma : Equiv.Perm (Fin 10)) (hd : ∀ i, 0 < deform i) :
    (Fin 10 → ℝ) ≃ₗ[ℝ] (Fin 10 → ℝ) :=
  weightedCoordinates10 e (fun i => (deform (sigma i))⁻¹) (fun i => inv_pos.mpr (hd _))

theorem davenportCoordinates10_apply (e : (Fin 10 → ℝ) ≃ₗ[ℝ] (Fin 10 → ℝ))
    (deform : Fin 10 → ℝ) (sigma : Equiv.Perm (Fin 10)) (hd : ∀ i, 0 < deform i)
    (x : Fin 10 → ℝ) (i : Fin 10) :
    davenportCoordinates10 e deform sigma hd x i = deform (sigma i) * e x i := by
  change e x i / (deform (sigma i))⁻¹ = _
  rw [div_inv_eq_mul, mul_comm]

theorem davenport_off_flag10_of_pivot (b : Basis (Fin 10) ℝ (Fin 10 → ℝ))
    (e : (Fin 10 → ℝ) ≃ₗ[ℝ] (Fin 10 → ℝ)) (v : Fin 10 → (Fin 10 → ℝ))
    (hv : LinearIndependent ℝ v) (hvL : ∀ i, v i ∈ lattice10Span b)
    (hvr : ∀ i, coordinateGauge10 e (v i) = successiveRadius10 b e i)
    (deform : Fin 10 → ℝ) (hd : ∀ i, 0 < deform i) (hanti : Antitone deform)
    (hscaled : Monotone (fun i => deform i * successiveRadius10 b e i))
    (p : Equiv.Perm (Fin 10))
    (hp : ∀ j : Fin 10, ∀ x ∈ prefixSpan10 (e ∘ v) (j.val+1) (by omega), ∀ M : ℝ, 0 ≤ M →
      (∀ i : Fin (j.val+1), |x (p (Fin.castLE (by omega) i))| ≤ M) → ‖x‖ ≤ 1024*M) :
    ∀ j : Fin 10, ∀ x ∈ lattice10Span b, x ∉ minimaFlag10 v j →
      deform j * successiveRadius10 b e j / 1024 ≤
        coordinateGauge10 (davenportCoordinates10 e deform p.symm hd) x := by
  classical
  intro j x hx hout
  let g := coordinateGauge10 (davenportCoordinates10 e deform p.symm hd) x
  have hg : 0 ≤ g := norm_nonneg _
  have hc (i : Fin 10) : deform i * |e x (p i)| ≤ g := by
    have hn := norm_le_pi_norm (davenportCoordinates10 e deform p.symm hd x) (p i)
    simpa only [Real.norm_eq_abs, davenportCoordinates10_apply, p.symm_apply_apply,
      abs_mul, abs_of_pos (hd i)] using hn
  let S := Finset.univ.filter (fun k : Fin 10 => x ∉ minimaFlag10 v k)
  have hjs : j ∈ S := by simp [S, hout]
  obtain ⟨k, hkS, hmax⟩ := Finset.exists_max_image S Fin.val ⟨j, hjs⟩
  have hkout : x ∉ minimaFlag10 v k := (Finset.mem_filter.mp hkS).2
  have hjk : j ≤ k := hmax j hjs
  have hxpre : x ∈ prefixSpan10 v (k.val+1) (by omega) := by
    by_cases hk : k.val+1 < 10
    · by_contra hnot
      let l : Fin 10 := ⟨k.val+1, hk⟩
      have hlS : l ∈ S := by
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        exact hnot
      have hle := hmax l hlS
      change k.val+1 ≤ k.val at hle
      omega
    · have htop : prefixSpan10 v (k.val+1) (by omega) = ⊤ := by
        apply Submodule.eq_top_of_finrank_eq
        rw [prefixSpan10_finrank v hv]
        simp only [Module.finrank_pi, Module.finrank_self, Fintype.card_fin, mul_one]
        omega
      rw [htop]
      exact Submodule.mem_top
  have hk10 : k.val+1 ≤ 10 := by omega
  let f : Fin (k.val+1) → Fin 10 := Fin.castLE hk10
  have hcoord (i : Fin (k.val+1)) : |e x (p (f i))| ≤ g / deform k := by
    apply (le_div_iff₀ (hd k)).mpr
    let l : Fin 10 := f i
    have hl : l ≤ k := by change i.val ≤ k.val; omega
    have hweight := mul_le_mul_of_nonneg_right (hanti hl) (abs_nonneg (e x (p l)))
    simpa only [mul_comm] using hweight.trans (hc l)
  have hnorm := hp k (e x) (prefixSpan10_map e v _ _ x hxpre) (g / deform k)
    (div_nonneg hg (hd k).le) hcoord
  have hlower := davenport_original_off_flag10 b e v hv hvL hvr k x hx hkout
  have hmul := mul_le_mul_of_nonneg_left (hlower.trans hnorm) (hd k).le
  have hcancel : deform k * (1024 * (g / deform k)) = 1024*g := by
    field_simp [(hd k).ne']
  rw [hcancel] at hmul
  have hmono := hscaled hjk
  change deform j * successiveRadius10 b e j / 1024 ≤ g
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 1024)).mpr
  exact hmono.trans (hmul.trans_eq (mul_comm 1024 g))

theorem davenportCoordinates10_det (e : (Fin 10 → ℝ) ≃ₗ[ℝ] (Fin 10 → ℝ))
    (deform : Fin 10 → ℝ) (sigma : Equiv.Perm (Fin 10)) (hd : ∀ i, 0 < deform i)
    (hprod : (∏ i, deform i) = 1) :
    LinearMap.det (davenportCoordinates10 e deform sigma hd).toLinearMap = LinearMap.det e.toLinearMap := by
  rw [davenportCoordinates10, weightedCoordinates10_det, Finset.prod_inv_distrib,
    Equiv.prod_comp, hprod, inv_one, div_one]

theorem davenportBody10_volume (e : (Fin 10 → ℝ) ≃ₗ[ℝ] (Fin 10 → ℝ))
    (deform : Fin 10 → ℝ) (sigma : Equiv.Perm (Fin 10)) (hd : ∀ i, 0 < deform i)
    (hprod : (∏ i, deform i) = 1) :
    MeasureTheory.volume.real (parallelepipedBody10 (davenportCoordinates10 e deform sigma hd)) =
      MeasureTheory.volume.real (parallelepipedBody10 e) := by
  rw [parallelepipedBody10_volume, parallelepipedBody10_volume, davenportCoordinates10_det e deform sigma hd hprod]

theorem davenport_minima_lower10 (b : Basis (Fin 10) ℝ (Fin 10 → ℝ))
    (e' : (Fin 10 → ℝ) ≃ₗ[ℝ] (Fin 10 → ℝ)) (v : Fin 10 → (Fin 10 → ℝ))
    (hv : LinearIndependent ℝ v) (s : Fin 10 → ℝ)
    (hsep : ∀ j, ∀ x ∈ lattice10Span b, x ∉ minimaFlag10 v j → s j ≤ coordinateGauge10 e' x)
    (j : Fin 10) : s j ≤ successiveRadius10 b e' j := by
  obtain ⟨u, hu, huL, _, hm, hur, _⟩ := exists_successive_minima10 b e'
  let f : Fin (j.val+1) → Fin 10 := Fin.castLE (by omega)
  have hf : Function.Injective f := Fin.castLE_injective _
  obtain ⟨i, hi⟩ := independent_family_escapes_subspace10 (u ∘ f) (hu.comp f hf)
    (minimaFlag10 v j) (by rw [minimaFlag10_finrank v hv j]; omega)
  have hh := hsep j (u (f i)) (huL (f i)) hi
  rw [hur] at hh
  exact hh.trans (hm (show f i ≤ j from (by change i.val ≤ j.val; omega)))

theorem davenport_adapted_rows10 (v : Fin 10 → (Fin 10 → ℝ)) (hv : LinearIndependent ℝ v) :
    ∃ p : Equiv.Perm (Fin 10), ∃ y : Fin 10 → (Fin 10 → ℝ),
      (∀ j, v j - y j ∈ minimaFlag10 v j) ∧
      (∀ j i : Fin 10, i < j → y j (p i) = 0) ∧
      (∀ j : Fin 10, ‖y j‖ ≤ (2 : ℝ)^j.val * ‖v j‖) ∧
      ∀ j : Fin 10, ∀ x ∈ prefixSpan10 v (j.val+1) (by omega), ∀ M : ℝ, 0 ≤ M →
        (∀ i : Fin (j.val+1), |x (p (Fin.castLE (by omega) i))| ≤ M) → ‖x‖ ≤ 1024*M := by
  classical
  obtain ⟨p, hp, hb⟩ := davenport_pivot_prefix10 v hv 10 le_rfl
  let q : Equiv.Perm (Fin 10) := Equiv.ofBijective p (Finite.injective_iff_bijective.mp hp)
  have hex (j : Fin 10) : ∃ w : minimaFlag10 v j,
      (∀ i : Fin j.val, w.val (q (Fin.castLE (by omega) i)) = v j (q (Fin.castLE (by omega) i))) ∧
      ‖w.val‖ ≤ ((2 : ℝ)^j.val-1)*‖v j‖ := by
    have hj10 : j.val ≤ 10 := Nat.le_of_lt j.isLt
    let f : minimaFlag10 v j →ₗ[ℝ] (Fin j.val → ℝ) :=
      { toFun := fun x i => x.val (q (Fin.castLE hj10 i))
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    have hf : Function.Injective f := by
      intro x1 x2 he
      apply Subtype.ext
      apply sub_eq_zero.mp
      apply norm_eq_zero.mp
      apply le_antisymm ?_ (norm_nonneg _)
      have hxW : x1.val-x2.val ∈ prefixSpan10 v j.val hj10 :=
        (minimaFlag10 v j).sub_mem x1.property x2.property
      have hzero (i : Fin j.val) : |(x1.val-x2.val) (p (Fin.castLE hj10 i))| ≤ (0 : ℝ) := by
        have hi := congrFun he i
        change x1.val (p (Fin.castLE hj10 i)) = x2.val (p (Fin.castLE hj10 i)) at hi
        change |x1.val (p (Fin.castLE hj10 i))-x2.val (p (Fin.castLE hj10 i))| ≤ (0 : ℝ)
        exact le_of_eq ((congrArg abs (sub_eq_zero.mpr hi)).trans abs_zero)
      have hn := hb j.val hj10 (x1.val-x2.val) hxW 0 le_rfl hzero
      simpa using hn
    have hdim : Module.finrank ℝ (minimaFlag10 v j) = Module.finrank ℝ (Fin j.val → ℝ) := by
      rw [minimaFlag10_finrank v hv j]
      simp
    have hsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim (f := f)).mp hf
    obtain ⟨w, hw⟩ := hsurj (fun i => v j (q (Fin.castLE hj10 i)))
    have hcoords (i : Fin j.val) : w.val (q (Fin.castLE hj10 i)) = v j (q (Fin.castLE hj10 i)) :=
      congrFun hw i
    refine ⟨w, hcoords, ?_⟩
    apply hb j.val hj10 w.val w.property ‖v j‖ (norm_nonneg _)
    intro i
    rw [show p (Fin.castLE hj10 i) = q (Fin.castLE hj10 i) from rfl, hcoords]
    simpa only [Real.norm_eq_abs] using norm_le_pi_norm (v j) (q (Fin.castLE hj10 i))
  choose w hw hnorm using hex
  refine ⟨q, fun j => v j-(w j).val, ?_, ?_, ?_, ?_⟩
  · intro j
    have he : v j-(v j-(w j).val) = (w j).val := by abel
    rw [he]
    exact (w j).property
  · intro j i hij
    let t : Fin j.val := ⟨i.val, hij⟩
    have hi : (Fin.castLE (by omega) t : Fin 10) = i := Fin.ext rfl
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
    have hC : (2 : ℝ)^(j.val+1)-1 ≤ 1024 := by fin_cases j <;> norm_num
    exact hn.trans (mul_le_mul_of_nonneg_right hC hM)

theorem independent_prefix_adjustment10 (v w : Fin 10 → (Fin 10 → ℝ))
    (hv : LinearIndependent ℝ v) (hw : ∀ j, w j-v j ∈ minimaFlag10 v j) :
    LinearIndependent ℝ w := by
  classical
  let b := basisOfLinearIndependentOfCardEqFinrank hv (by simp)
  have hb (i : Fin 10) : b i = v i :=
    congrFun (coe_basisOfLinearIndependentOfCardEqFinrank hv _) i
  let f := b.equivFun
  have hbase (j i : Fin 10) : f (v j) i = if j = i then 1 else 0 := by
    rw [← hb j]
    exact b.equivFun_self j i
  have hzero (j i : Fin 10) (hji : j ≤ i) (x : Fin 10 → ℝ) (hx : x ∈ minimaFlag10 v j) :
      f x i = 0 := by
    let g : (Fin 10 → ℝ) →ₗ[ℝ] ℝ := (LinearMap.proj i).comp f.toLinearMap
    have hs : minimaFlag10 v j ≤ LinearMap.ker g := by
      apply Submodule.span_le.mpr
      rintro _ ⟨k, rfl⟩
      change f (v (Fin.castLE (by omega) k)) i = 0
      rw [hbase]
      have hne : (Fin.castLE (by omega) k : Fin 10) ≠ i := by
        intro heq
        have he := congrArg Fin.val heq
        change k.val = i.val at he
        omega
      simp only [hne, if_false]
    exact hs hx
  have hcoeff (j i : Fin 10) (hji : j ≤ i) : f (w j) i = f (v j) i := by
    have hz := hzero j i hji (w j-v j) (hw j)
    have he : f (w j-v j) i = f (w j) i-f (v j) i := by
      rw [map_sub]
      rfl
    rw [he] at hz
    exact sub_eq_zero.mp hz
  let T : Matrix (Fin 10) (Fin 10) ℝ := fun j i => f (w j) i
  have hdiag (i : Fin 10) : T i i = 1 := by
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

theorem davenport_integral_reduce10 (Lambda : Submodule ℤ (Fin 10 → ℝ))
    (v : Fin 10 → (Fin 10 → ℝ)) (hvL : ∀ i, v i ∈ Lambda)
    (F : (Fin 10 → ℝ) ≃ₗ[ℝ] (Fin 10 → ℝ))
    (htri : ∀ i j : Fin 10, j < i → F (v j) i = 0)
    (hdiag : ∀ i : Fin 10, F (v i) i = 1)
    (k : ℕ) (hk : k ≤ 10) (x : Fin 10 → ℝ) (hx : x ∈ Lambda) :
    ∃ z ∈ Lambda, z-x ∈ prefixSpan10 v k hk ∧
      (∀ i : Fin 10, i.val < k → 0 ≤ F z i ∧ F z i < 1) ∧
      (∀ i : Fin 10, k ≤ i.val → F z i = F x i) := by
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
    have hk0 : k ≤ 10 := by omega
    let a : Fin 10 := ⟨k, by omega⟩
    let n : ℤ := Int.floor (F x a)
    let x' : Fin 10 → ℝ := x-(n : ℝ) • v a
    have hx'L : x' ∈ Lambda := by
      apply Lambda.sub_mem hx
      simpa only [Int.cast_smul_eq_zsmul] using Lambda.smul_mem n (hvL a)
    obtain ⟨z, hzL, hzspan, hzlo, hzhi⟩ := ih hk0 x' hx'L
    have hdelta : x'-x ∈ prefixSpan10 v (k+1) hk := by
      have hva : v a ∈ prefixSpan10 v (k+1) hk :=
        Submodule.subset_span ⟨⟨k, Nat.lt_succ_self k⟩, rfl⟩
      have he : x'-x = -((n : ℝ) • v a) := by dsimp [x']; abel
      rw [he]
      exact (prefixSpan10 v (k+1) hk).neg_mem ((prefixSpan10 v (k+1) hk).smul_mem (n : ℝ) hva)
    have hfrac : F x' a = Int.fract (F x a) := by
      simp only [x', map_sub, map_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
        hdiag a, mul_one, n, Int.self_sub_floor]
    refine ⟨z, hzL, ?_, ?_, ?_⟩
    · have he : z-x = (z-x')+(x'-x) := by abel
      rw [he]
      exact (prefixSpan10 v (k+1) hk).add_mem
        (prefixSpan10_mono v hk0 hk (Nat.le_succ k) hzspan) hdelta
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

theorem basis_prefix_coordinate_zero10 (b : Basis (Fin 10) ℝ (Fin 10 → ℝ))
    (j i : Fin 10) (hji : j ≤ i) (x : Fin 10 → ℝ) (hx : x ∈ minimaFlag10 b j) :
    b.equivFun x i = 0 := by
  let g : (Fin 10 → ℝ) →ₗ[ℝ] ℝ := (LinearMap.proj i).comp b.equivFun.toLinearMap
  have hs : minimaFlag10 b j ≤ LinearMap.ker g := by
    apply Submodule.span_le.mpr
    rintro _ ⟨k, rfl⟩
    change b.equivFun (b (Fin.castLE (by omega) k)) i = 0
    rw [b.equivFun_self]
    have hne : (Fin.castLE (by omega) k : Fin 10) ≠ i := by
      intro heq
      have he := congrArg Fin.val heq
      change k.val = i.val at he
      omega
    exact if_neg hne
  exact hs hx

theorem davenport_adapted_basis10 (v y : Fin 10 → (Fin 10 → ℝ)) (hv : LinearIndependent ℝ v)
    (hadapt : ∀ j, v j-y j ∈ minimaFlag10 v j) :
    ∃ b : Basis (Fin 10) ℝ (Fin 10 → ℝ), (∀ i, b i = y i) ∧
      ∀ j i : Fin 10, j ≤ i → b.equivFun (v j) i = if j = i then 1 else 0 := by
  classical
  have hy : LinearIndependent ℝ y := independent_prefix_adjustment10 v y hv (by
    intro j
    simpa only [neg_sub] using (minimaFlag10 v j).neg_mem (hadapt j))
  let b := basisOfLinearIndependentOfCardEqFinrank hy (by simp)
  have hb (i : Fin 10) : b i = y i :=
    congrFun (coe_basisOfLinearIndependentOfCardEqFinrank hy _) i
  have hbfun : (b : Fin 10 → (Fin 10 → ℝ)) = y := funext hb
  have hflags (j : Fin 10) : minimaFlag10 b j = minimaFlag10 v j := by
    apply Submodule.eq_of_le_of_finrank_eq
    · apply Submodule.span_le.mpr
      rintro _ ⟨k, rfl⟩
      let i : Fin 10 := Fin.castLE (by omega) k
      change b i ∈ minimaFlag10 v j
      rw [hb i]
      have hij : i ≤ j := by change k.val ≤ j.val; omega
      have hvj : v i ∈ minimaFlag10 v j := Submodule.subset_span ⟨k, rfl⟩
      have hwj : v i-y i ∈ minimaFlag10 v j := minimaFlag10_mono v _ _ hij (hadapt i)
      have he : v i-(v i-y i) = y i := by abel
      rw [← he]
      exact (minimaFlag10 v j).sub_mem hvj hwj
    · rw [minimaFlag10_finrank _ b.linearIndependent, minimaFlag10_finrank v hv]
  refine ⟨b, hb, ?_⟩
  intro j i hji
  have hx : v j-y j ∈ minimaFlag10 b j := (hflags j).symm ▸ hadapt j
  have hz := basis_prefix_coordinate_zero10 b j i hji (v j-y j) hx
  have he : b.equivFun (v j-y j) i = b.equivFun (v j) i-b.equivFun (y j) i := by
    rw [map_sub]
    rfl
  rw [he] at hz
  have hycoord : b.equivFun (y j) i = if j = i then 1 else 0 := by
    rw [← hb j]
    exact b.equivFun_self j i
  rw [← hycoord]
  exact sub_eq_zero.mp hz

theorem davenportCoordinates10_comp (e : (Fin 10 → ℝ) ≃ₗ[ℝ] (Fin 10 → ℝ))
    (deform : Fin 10 → ℝ) (sigma : Equiv.Perm (Fin 10)) (hd : ∀ i, 0 < deform i)
    (x : Fin 10 → ℝ) :
    davenportCoordinates10 e deform sigma hd x =
      davenportCoordinates10 (LinearEquiv.refl ℝ (Fin 10 → ℝ)) deform sigma hd (e x) := by
  ext i
  rw [davenportCoordinates10_apply, davenportCoordinates10_apply]
  rfl

theorem davenport_row_gauge_bound10 (y : Fin 10 → ℝ) (p : Equiv.Perm (Fin 10))
    (deform : Fin 10 → ℝ) (hd : ∀ i, 0 < deform i) (hanti : Antitone deform)
    (j : Fin 10) (hzero : ∀ i : Fin 10, i < j → y (p i) = 0) :
    coordinateGauge10 (davenportCoordinates10 (LinearEquiv.refl ℝ (Fin 10 → ℝ)) deform p.symm hd) y ≤
      deform j * ‖y‖ := by
  change ‖davenportCoordinates10 (LinearEquiv.refl ℝ (Fin 10 → ℝ)) deform p.symm hd y‖ ≤ _
  apply (pi_norm_le_iff_of_nonempty _).mpr
  intro a
  rw [Real.norm_eq_abs, davenportCoordinates10_apply]
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

theorem davenport_reduced_frame10 (b : Basis (Fin 10) ℝ (Fin 10 → ℝ))
    (e : (Fin 10 → ℝ) ≃ₗ[ℝ] (Fin 10 → ℝ)) (v : Fin 10 → (Fin 10 → ℝ))
    (hv : LinearIndependent ℝ v) (hvL : ∀ i, v i ∈ lattice10Span b)
    (hvr : ∀ i, coordinateGauge10 e (v i) = successiveRadius10 b e i)
    (deform : Fin 10 → ℝ) (hd : ∀ i, 0 < deform i) (hanti : Antitone deform)
    (hscaled : Monotone (fun i => deform i * successiveRadius10 b e i)) :
    ∃ p : Equiv.Perm (Fin 10), ∃ z : Fin 10 → (Fin 10 → ℝ), LinearIndependent ℝ z ∧
      (∀ i, z i ∈ lattice10Span b) ∧
      (∀ j, coordinateGauge10 (davenportCoordinates10 e deform p.symm hd) (z j) ≤
        1024 * (deform j * successiveRadius10 b e j)) ∧
      ∀ j : Fin 10, ∀ x ∈ prefixSpan10 (e ∘ v) (j.val+1) (by omega), ∀ M : ℝ, 0 ≤ M →
        (∀ i : Fin (j.val+1), |x (p (Fin.castLE (by omega) i))| ≤ M) → ‖x‖ ≤ 1024*M := by
  classical
  have he : LinearIndependent ℝ (e ∘ v) :=
    hv.map' e.toLinearMap (LinearMap.ker_eq_bot.mpr e.injective)
  obtain ⟨p, y, hyspan, hyzero, hynorm, hp⟩ := davenport_adapted_rows10 (e ∘ v) he
  obtain ⟨B, hB, hcoeff⟩ := davenport_adapted_basis10 (e ∘ v) y he hyspan
  let F : (Fin 10 → ℝ) ≃ₗ[ℝ] (Fin 10 → ℝ) := e.trans B.equivFun
  have htri (i j : Fin 10) (hji : j < i) : F (v j) i = 0 := by
    have h := hcoeff j i hji.le
    change B.equivFun (e (v j)) i = 0
    simpa only [Function.comp_apply, ne_of_lt hji, if_false] using h
  have hdiag (i : Fin 10) : F (v i) i = 1 := by
    simpa only [Function.comp_apply, if_pos rfl] using hcoeff i i le_rfl
  have hex (j : Fin 10) : ∃ z ∈ lattice10Span b, z-v j ∈ minimaFlag10 v j ∧
      (∀ i : Fin 10, i < j → 0 ≤ F z i ∧ F z i < 1) ∧
      (∀ i : Fin 10, j ≤ i → F z i = if j = i then 1 else 0) := by
    obtain ⟨z, hzL, hzspan, hzlo, hzhi⟩ :=
      davenport_integral_reduce10 (lattice10Span b) v hvL F htri hdiag j.val (by omega) (v j) (hvL j)
    refine ⟨z, hzL, hzspan, hzlo, ?_⟩
    intro i hji
    rw [hzhi i hji]
    exact hcoeff j i hji
  choose z hzL hzspan hzlo hzhi using hex
  have hz : LinearIndependent ℝ z := independent_prefix_adjustment10 v z hv hzspan
  let D := davenportCoordinates10 (LinearEquiv.refl ℝ (Fin 10 → ℝ)) deform p.symm hd
  have hybound (i : Fin 10) : coordinateGauge10 D (y i) ≤
      (2 : ℝ)^i.val * (deform i * successiveRadius10 b e i) := by
    have h0 := davenport_row_gauge_bound10 (y i) p deform hd hanti i (hyzero i)
    have h1 := mul_le_mul_of_nonneg_left (hynorm i) (hd i).le
    have h2 : deform i * ((2 : ℝ)^i.val * ‖(e ∘ v) i‖) =
        (2 : ℝ)^i.val * (deform i * successiveRadius10 b e i) := by
      change deform i * ((2 : ℝ)^i.val * coordinateGauge10 e (v i)) = _
      rw [hvr i]
      ring
    exact h0.trans (h1.trans_eq h2)
  refine ⟨p, z, hz, hzL, ?_, hp⟩
  intro j
  have haj : 0 ≤ deform j * successiveRadius10 b e j := by
    apply mul_nonneg (hd j).le
    rw [← hvr j]
    exact norm_nonneg _
  have hrepr : e (z j) = ∑ i : Fin 10, F (z j) i • y i := by
    have hh := B.sum_equivFun (e (z j))
    simpa only [hB] using hh.symm
  have hnorm : coordinateGauge10 (davenportCoordinates10 e deform p.symm hd) (z j) ≤
      ∑ i : Fin 10, (2 : ℝ)^i.val * (deform j * successiveRadius10 b e j) := by
    change ‖davenportCoordinates10 e deform p.symm hd (z j)‖ ≤ _
    rw [davenportCoordinates10_comp, hrepr, map_sum]
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
  have hsum : (∑ i : Fin 10, (2 : ℝ)^i.val * (deform j * successiveRadius10 b e j)) =
      1023 * (deform j * successiveRadius10 b e j) := by
    have hpow : (∑ i : Fin 10, (2 : ℝ)^i.val) = 1023 := by
      norm_num [Fin.sum_univ_succ]
    rw [← Finset.sum_mul, hpow]
  rw [hsum] at hnorm
  exact hnorm.trans (mul_le_mul_of_nonneg_right (by norm_num : (1023 : ℝ) ≤ 1024) haj)

theorem davenport_lemma10 (b : Basis (Fin 10) ℝ (Fin 10 → ℝ))
    (e : (Fin 10 → ℝ) ≃ₗ[ℝ] (Fin 10 → ℝ)) (v : Fin 10 → (Fin 10 → ℝ))
    (hv : LinearIndependent ℝ v) (hvL : ∀ i, v i ∈ lattice10Span b)
    (hvr : ∀ i, coordinateGauge10 e (v i) = successiveRadius10 b e i)
    (deform : Fin 10 → ℝ) (hd : ∀ i, 0 < deform i) (hprod : (∏ i, deform i) = 1)
    (hanti : Antitone deform) (hscaled : Monotone (fun i => deform i * successiveRadius10 b e i)) :
    ∃ sigma : Equiv.Perm (Fin 10),
      (∀ j, deform j * successiveRadius10 b e j / 1024 ≤
          successiveRadius10 b (davenportCoordinates10 e deform sigma hd) j ∧
        successiveRadius10 b (davenportCoordinates10 e deform sigma hd) j ≤
          1024 * (deform j * successiveRadius10 b e j)) ∧
      MeasureTheory.volume.real (parallelepipedBody10 (davenportCoordinates10 e deform sigma hd)) =
        MeasureTheory.volume.real (parallelepipedBody10 e) ∧
      ∀ j : Fin 10, ∀ x ∈ lattice10Span b, x ∉ minimaFlag10 v j →
        deform j * successiveRadius10 b e j / 1024 ≤
          coordinateGauge10 (davenportCoordinates10 e deform sigma hd) x := by
  obtain ⟨p, z, hz, hzL, hzbound, hp⟩ := davenport_reduced_frame10 b e v hv hvL hvr deform hd hanti hscaled
  have hsep := davenport_off_flag10_of_pivot b e v hv hvL hvr deform hd hanti hscaled p hp
  refine ⟨p.symm, ?_, davenportBody10_volume e deform p.symm hd hprod, hsep⟩
  intro j
  refine ⟨davenport_minima_lower10 b _ v hv _ hsep j, ?_⟩
  let f : Fin (j.val+1) → Fin 10 := Fin.castLE (by omega)
  apply successiveRadius10_le_family b _ j (z ∘ f) (hz.comp f (Fin.castLE_injective _))
    (fun i => hzL (f i))
  intro i
  have hi : f i ≤ j := by change i.val ≤ j.val; omega
  exact (hzbound (f i)).trans (mul_le_mul_of_nonneg_left (hscaled hi) (by norm_num : (0 : ℝ) ≤ 1024))

end
end CompoundFeasibility
