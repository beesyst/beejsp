import SubspaceBridge.CompoundSourceFamily42
open scoped BigOperators Matrix
namespace CompoundFeasibility
noncomputable section

def minimaFlag6 (v : Fin 6 → (Fin 6 → ℝ)) (k : Fin 6) : Submodule ℝ (Fin 6 → ℝ) :=
  Submodule.span ℝ (Set.range (fun i : Fin k.val => v (Fin.castLE (by omega) i)))

theorem minimaFlag6_finrank (v : Fin 6 → (Fin 6 → ℝ))
    (hv : LinearIndependent ℝ v) (k : Fin 6) :
    Module.finrank ℝ (minimaFlag6 v k) = k.val := by
  have hi := hv.comp (Fin.castLE (by omega) : Fin k.val → Fin 6) (Fin.castLE_injective _)
  simpa only [minimaFlag6, Fintype.card_fin] using finrank_span_eq_card hi

theorem minimaFlag6_mono (v : Fin 6 → (Fin 6 → ℝ)) {i j : Fin 6} (h : i ≤ j) :
    minimaFlag6 v i ≤ minimaFlag6 v j := by
  apply Submodule.span_mono
  rintro _ ⟨k, rfl⟩
  exact ⟨⟨k.val, lt_of_lt_of_le k.isLt h⟩, rfl⟩

theorem successiveRadius6_le_family (b : Basis (Fin 6) ℝ (Fin 6 → ℝ))
    (e : (Fin 6 → ℝ) ≃ₗ[ℝ] (Fin 6 → ℝ)) (k : Fin 6)
    (u : Fin (k.val+1) → (Fin 6 → ℝ)) (hu : LinearIndependent ℝ u)
    (huL : ∀ i, u i ∈ lattice6Span b) (r : ℝ)
    (hr : ∀ i, coordinateGauge6 e (u i) ≤ r) : successiveRadius6 b e k ≤ r := by
  apply csInf_le (s := {s : ℝ | ∃ w : Fin (k.val+1) → (Fin 6 → ℝ),
    LinearIndependent ℝ w ∧ (∀ i, w i ∈ lattice6Span b) ∧
      ∀ i, coordinateGauge6 e (w i) ≤ s}) _ ⟨u, hu, huL, hr⟩
  refine ⟨0, ?_⟩
  rintro s ⟨w, _, _, hw⟩
  exact (norm_nonneg (e (w 0))).trans (hw 0)

theorem lattice6Span_short_mem_minimaFlag (b : Basis (Fin 6) ℝ (Fin 6 → ℝ))
    (e : (Fin 6 → ℝ) ≃ₗ[ℝ] (Fin 6 → ℝ)) (v : Fin 6 → (Fin 6 → ℝ))
    (hv : LinearIndependent ℝ v) (hvL : ∀ i, v i ∈ lattice6Span b)
    (hvr : ∀ i, coordinateGauge6 e (v i) = successiveRadius6 b e i)
    (k : Fin 6) (hgap : ∀ i : Fin 6, i < k →
      successiveRadius6 b e i < successiveRadius6 b e k)
    (x : Fin 6 → ℝ) (hx : x ∈ lattice6Span b)
    (hxr : coordinateGauge6 e x < successiveRadius6 b e k) : x ∈ minimaFlag6 v k := by
  classical
  by_contra hxW
  let u : Fin k.val → (Fin 6 → ℝ) := fun i => v (Fin.castLE (by omega) i)
  have hu : LinearIndependent ℝ u := hv.comp _ (Fin.castLE_injective _)
  let w : Fin (k.val+1) → (Fin 6 → ℝ) := Fin.snoc u x
  have hux : LinearIndependent ℝ w := linearIndependent_fin_snoc.mpr ⟨hu, hxW⟩
  have hL : ∀ i : Fin (k.val+1), w i ∈ lattice6Span b := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa [w] using hx
    · simpa [w, u] using hvL (Fin.castLE (by omega) j)
  have hlt : ∀ i : Fin (k.val+1), coordinateGauge6 e (w i) < successiveRadius6 b e k := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa [w] using hxr
    · simpa [w, u, hvr] using hgap (Fin.castLE (by omega) j) (by exact j.isLt)
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ
    (fun i => coordinateGauge6 e (w i)) Finset.univ_nonempty
  have hle := successiveRadius6_le_family b e k w hux hL _ (fun j => hi j (Finset.mem_univ j))
  exact (not_lt_of_ge hle) (hlt i)

theorem davenport_original_off_flag6 (b : Basis (Fin 6) ℝ (Fin 6 → ℝ))
    (e : (Fin 6 → ℝ) ≃ₗ[ℝ] (Fin 6 → ℝ)) (v : Fin 6 → (Fin 6 → ℝ))
    (hv : LinearIndependent ℝ v) (hvL : ∀ i, v i ∈ lattice6Span b)
    (hvr : ∀ i, coordinateGauge6 e (v i) = successiveRadius6 b e i)
    (j : Fin 6) (x : Fin 6 → ℝ) (hx : x ∈ lattice6Span b)
    (houtside : x ∉ minimaFlag6 v j) : successiveRadius6 b e j ≤ coordinateGauge6 e x := by
  classical
  obtain ⟨_, _, _, _, hm, _⟩ := exists_successive_minima6 b e
  let s := Finset.univ.filter (fun i => successiveRadius6 b e i = successiveRadius6 b e j)
  have hjs : j ∈ s := by simp [s]
  obtain ⟨r, hrs, hmin⟩ := Finset.exists_min_image s Fin.val ⟨j, hjs⟩
  have hr : successiveRadius6 b e r = successiveRadius6 b e j := (Finset.mem_filter.mp hrs).2
  have hrj : r ≤ j := hmin j hjs
  have hgap : ∀ i : Fin 6, i < r → successiveRadius6 b e i < successiveRadius6 b e r := by
    intro i hir
    have hle := hm (le_of_lt hir)
    apply lt_of_le_of_ne hle
    intro heq
    have his : i ∈ s := by simp [s, heq, hr]
    exact (not_le_of_gt hir) (hmin i his)
  by_contra h
  have hshort : coordinateGauge6 e x < successiveRadius6 b e r := by
    rw [hr]
    exact lt_of_not_ge h
  exact houtside (minimaFlag6_mono v hrj
    (lattice6Span_short_mem_minimaFlag b e v hv hvL hvr r hgap x hx hshort))

theorem direct_original_off_flag42 (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L) (Q : ℝ) (hQ : 1 < Q)
    (c₀ c₂ c₃ : Fin 4 → ℝ) (u : Fin 6 → directCompoundGroup42 A₂ A₃ Q c₂ c₃)
    (hu : LinearIndependent ℝ (fun i => integerReal (u i : Fin 6 → ℤ)))
    (hatt : ∀ i, coordinateGauge6 (compoundCoordinates42 L hL Q hQ c₀)
      (integerReal (u i : Fin 6 → ℤ)) = directMinima42 A₂ A₃ L hL Q hQ c₀ c₂ c₃ i)
    (j : Fin 6) (z : directCompoundGroup42 A₂ A₃ Q c₂ c₃)
    (hout : integerReal (z : Fin 6 → ℤ) ∉
      minimaFlag6 (fun i => integerReal (u i : Fin 6 → ℤ)) j) :
    directMinima42 A₂ A₃ L hL Q hQ c₀ c₂ c₃ j ≤
      coordinateGauge6 (compoundCoordinates42 L hL Q hQ c₀) (integerReal (z : Fin 6 → ℤ)) := by
  rw [directMinima42_eq_radius]
  apply davenport_original_off_flag6 _ _ _ hu
  · intro i
    rw [directRealBasis42_span]
    exact ⟨(u i : Fin 6 → ℤ), (u i).property, rfl⟩
  · intro i
    rw [← directMinima42_eq_radius]
    exact hatt i
  · rw [directRealBasis42_span]
    exact ⟨(z : Fin 6 → ℤ), z.property, rfl⟩
  · exact hout

theorem davenport_pivot_step6 (k : ℕ) (W V : Submodule ℝ (Fin 6 → ℝ))
    (hW : Module.finrank ℝ W = k) (hV : Module.finrank ℝ V = k+1) (hWV : W ≤ V)
    (p : Fin k → Fin 6) (C : ℝ)
    (hbound : ∀ x ∈ W, ∀ M : ℝ, 0 ≤ M → (∀ i, |x (p i)| ≤ M) → ‖x‖ ≤ C*M) :
    ∃ a : Fin 6, a ∉ Set.range p ∧
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
  let y : Fin 6 → ℝ := z.val
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

def prefixSpan6 (v : Fin 6 → (Fin 6 → ℝ)) (k : ℕ) (hk : k ≤ 6) :
    Submodule ℝ (Fin 6 → ℝ) :=
  Submodule.span ℝ (Set.range (fun i : Fin k => v (Fin.castLE hk i)))

theorem prefixSpan6_finrank (v : Fin 6 → (Fin 6 → ℝ)) (hv : LinearIndependent ℝ v)
    (k : ℕ) (hk : k ≤ 6) : Module.finrank ℝ (prefixSpan6 v k hk) = k := by
  simpa only [prefixSpan6, Fintype.card_fin] using
    finrank_span_eq_card (hv.comp (Fin.castLE hk) (Fin.castLE_injective _))

theorem prefixSpan6_mono (v : Fin 6 → (Fin 6 → ℝ)) {i j : ℕ}
    (hi : i ≤ 6) (hj : j ≤ 6) (hij : i ≤ j) : prefixSpan6 v i hi ≤ prefixSpan6 v j hj := by
  apply Submodule.span_mono
  rintro _ ⟨k, rfl⟩
  exact ⟨Fin.castLE hij k, rfl⟩

theorem davenport_pivot_prefix6 (v : Fin 6 → (Fin 6 → ℝ)) (hv : LinearIndependent ℝ v)
    (k : ℕ) (hk : k ≤ 6) :
    ∃ p : Fin k → Fin 6, Function.Injective p ∧
      ∀ (j : ℕ) (hj : j ≤ k), ∀ x ∈ prefixSpan6 v j (hj.trans hk), ∀ M : ℝ, 0 ≤ M →
        (∀ i : Fin j, |x (p (Fin.castLE hj i))| ≤ M) → ‖x‖ ≤ ((2 : ℝ)^j-1)*M := by
  induction k with
  | zero =>
    refine ⟨Fin.elim0, ?_, ?_⟩
    · intro i
      exact Fin.elim0 i
    · intro j hj x hx M hM hcoords
      have hj0 : j = 0 := by omega
      subst j
      have hx0 : x = 0 := by simpa [prefixSpan6] using hx
      simp [hx0]
  | succ k ih =>
    have hk0 : k ≤ 6 := by omega
    obtain ⟨p, hp, hb⟩ := ih hk0
    have hbound : ∀ x ∈ prefixSpan6 v k hk0, ∀ M : ℝ, 0 ≤ M →
        (∀ i, |x (p i)| ≤ M) → ‖x‖ ≤ ((2 : ℝ)^k-1)*M := by
      intro x hx M hM hc
      exact hb k le_rfl x hx M hM hc
    obtain ⟨a, ha, hab⟩ := davenport_pivot_step6 k
      (prefixSpan6 v k hk0) (prefixSpan6 v (k+1) hk)
      (prefixSpan6_finrank v hv k hk0) (prefixSpan6_finrank v hv (k+1) hk)
      (prefixSpan6_mono v hk0 hk (Nat.le_succ k)) p ((2 : ℝ)^k-1) hbound
    let q : Fin (k+1) → Fin 6 := Fin.snoc p a
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

theorem prefixSpan6_map (e : (Fin 6 → ℝ) ≃ₗ[ℝ] (Fin 6 → ℝ))
    (v : Fin 6 → (Fin 6 → ℝ)) (k : ℕ) (hk : k ≤ 6) (x : Fin 6 → ℝ)
    (hx : x ∈ prefixSpan6 v k hk) : e x ∈ prefixSpan6 (e ∘ v) k hk := by
  have hs : (prefixSpan6 v k hk).map e.toLinearMap = prefixSpan6 (e ∘ v) k hk := by
    simp only [prefixSpan6, Submodule.map_span, ← Set.range_comp, Function.comp_def]
    rfl
  rw [← hs]
  exact Submodule.mem_map.mpr ⟨x, hx, rfl⟩

theorem davenport_flag_pivot6 (v : Fin 6 → (Fin 6 → ℝ)) (hv : LinearIndependent ℝ v) :
    ∃ p : Equiv.Perm (Fin 6), ∀ j : Fin 6,
      ∀ x ∈ prefixSpan6 v (j.val+1) (by omega), ∀ M : ℝ, 0 ≤ M →
        (∀ i : Fin (j.val+1), |x (p (Fin.castLE (by omega) i))| ≤ M) → ‖x‖ ≤ 64*M := by
  obtain ⟨p, hp, hb⟩ := davenport_pivot_prefix6 v hv 6 le_rfl
  let q : Equiv.Perm (Fin 6) := Equiv.ofBijective p (Finite.injective_iff_bijective.mp hp)
  refine ⟨q, ?_⟩
  intro j x hx M hM hc
  have hn := hb (j.val+1) (by omega) x hx M hM hc
  have hC : (2 : ℝ)^(j.val+1)-1 ≤ 64 := by fin_cases j <;> norm_num
  exact hn.trans (mul_le_mul_of_nonneg_right hC hM)

noncomputable def davenportCoordinates6 (e : (Fin 6 → ℝ) ≃ₗ[ℝ] (Fin 6 → ℝ))
    (deform : Fin 6 → ℝ) (sigma : Equiv.Perm (Fin 6)) (hd : ∀ i, 0 < deform i) :
    (Fin 6 → ℝ) ≃ₗ[ℝ] (Fin 6 → ℝ) :=
  weightedCoordinates6 e (fun i => (deform (sigma i))⁻¹) (fun i => inv_pos.mpr (hd _))

theorem davenportCoordinates6_apply (e : (Fin 6 → ℝ) ≃ₗ[ℝ] (Fin 6 → ℝ))
    (deform : Fin 6 → ℝ) (sigma : Equiv.Perm (Fin 6)) (hd : ∀ i, 0 < deform i)
    (x : Fin 6 → ℝ) (i : Fin 6) :
    davenportCoordinates6 e deform sigma hd x i = deform (sigma i) * e x i := by
  change e x i / (deform (sigma i))⁻¹ = _
  rw [div_inv_eq_mul, mul_comm]

theorem davenport_off_flag6_of_pivot (b : Basis (Fin 6) ℝ (Fin 6 → ℝ))
    (e : (Fin 6 → ℝ) ≃ₗ[ℝ] (Fin 6 → ℝ)) (v : Fin 6 → (Fin 6 → ℝ))
    (hv : LinearIndependent ℝ v) (hvL : ∀ i, v i ∈ lattice6Span b)
    (hvr : ∀ i, coordinateGauge6 e (v i) = successiveRadius6 b e i)
    (deform : Fin 6 → ℝ) (hd : ∀ i, 0 < deform i) (hanti : Antitone deform)
    (hscaled : Monotone (fun i => deform i * successiveRadius6 b e i))
    (p : Equiv.Perm (Fin 6))
    (hp : ∀ j : Fin 6, ∀ x ∈ prefixSpan6 (e ∘ v) (j.val+1) (by omega), ∀ M : ℝ, 0 ≤ M →
      (∀ i : Fin (j.val+1), |x (p (Fin.castLE (by omega) i))| ≤ M) → ‖x‖ ≤ 64*M) :
    ∀ j : Fin 6, ∀ x ∈ lattice6Span b, x ∉ minimaFlag6 v j →
      deform j * successiveRadius6 b e j / 64 ≤
        coordinateGauge6 (davenportCoordinates6 e deform p.symm hd) x := by
  classical
  intro j x hx hout
  let g := coordinateGauge6 (davenportCoordinates6 e deform p.symm hd) x
  have hg : 0 ≤ g := norm_nonneg _
  have hc (i : Fin 6) : deform i * |e x (p i)| ≤ g := by
    have hn := norm_le_pi_norm (davenportCoordinates6 e deform p.symm hd x) (p i)
    simpa only [Real.norm_eq_abs, davenportCoordinates6_apply, p.symm_apply_apply,
      abs_mul, abs_of_pos (hd i)] using hn
  let S := Finset.univ.filter (fun k : Fin 6 => x ∉ minimaFlag6 v k)
  have hjs : j ∈ S := by simp [S, hout]
  obtain ⟨k, hkS, hmax⟩ := Finset.exists_max_image S Fin.val ⟨j, hjs⟩
  have hkout : x ∉ minimaFlag6 v k := (Finset.mem_filter.mp hkS).2
  have hjk : j ≤ k := hmax j hjs
  have hxpre : x ∈ prefixSpan6 v (k.val+1) (by omega) := by
    by_cases hk : k.val+1 < 6
    · by_contra hnot
      let l : Fin 6 := ⟨k.val+1, hk⟩
      have hlS : l ∈ S := by
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        exact hnot
      have hle := hmax l hlS
      change k.val+1 ≤ k.val at hle
      omega
    · have htop : prefixSpan6 v (k.val+1) (by omega) = ⊤ := by
        apply Submodule.eq_top_of_finrank_eq
        rw [prefixSpan6_finrank v hv]
        simp only [Module.finrank_pi, Module.finrank_self, Fintype.card_fin, mul_one]
        omega
      rw [htop]
      exact Submodule.mem_top
  have hk6 : k.val+1 ≤ 6 := by omega
  let f : Fin (k.val+1) → Fin 6 := Fin.castLE hk6
  have hcoord (i : Fin (k.val+1)) : |e x (p (f i))| ≤ g / deform k := by
    apply (le_div_iff₀ (hd k)).mpr
    let l : Fin 6 := f i
    have hl : l ≤ k := by change i.val ≤ k.val; omega
    have hweight := mul_le_mul_of_nonneg_right (hanti hl) (abs_nonneg (e x (p l)))
    simpa only [mul_comm] using hweight.trans (hc l)
  have hnorm := hp k (e x) (prefixSpan6_map e v _ _ x hxpre) (g / deform k)
    (div_nonneg hg (hd k).le) hcoord
  have hlower := davenport_original_off_flag6 b e v hv hvL hvr k x hx hkout
  have hmul := mul_le_mul_of_nonneg_left (hlower.trans hnorm) (hd k).le
  have hcancel : deform k * (64 * (g / deform k)) = 64*g := by
    field_simp [(hd k).ne']
  rw [hcancel] at hmul
  have hmono := hscaled hjk
  change deform j * successiveRadius6 b e j / 64 ≤ g
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 64)).mpr
  exact hmono.trans (hmul.trans_eq (mul_comm 64 g))

theorem davenport_off_flag6 (b : Basis (Fin 6) ℝ (Fin 6 → ℝ))
    (e : (Fin 6 → ℝ) ≃ₗ[ℝ] (Fin 6 → ℝ)) (v : Fin 6 → (Fin 6 → ℝ))
    (hv : LinearIndependent ℝ v) (hvL : ∀ i, v i ∈ lattice6Span b)
    (hvr : ∀ i, coordinateGauge6 e (v i) = successiveRadius6 b e i)
    (deform : Fin 6 → ℝ) (hd : ∀ i, 0 < deform i) (hanti : Antitone deform)
    (hscaled : Monotone (fun i => deform i * successiveRadius6 b e i)) :
    ∃ sigma : Equiv.Perm (Fin 6), ∀ j : Fin 6, ∀ x ∈ lattice6Span b,
      x ∉ minimaFlag6 v j → deform j * successiveRadius6 b e j / 64 ≤
        coordinateGauge6 (davenportCoordinates6 e deform sigma hd) x := by
  have he : LinearIndependent ℝ (e ∘ v) :=
    hv.map' e.toLinearMap (LinearMap.ker_eq_bot.mpr e.injective)
  obtain ⟨p, hp⟩ := davenport_flag_pivot6 (e ∘ v) he
  exact ⟨p.symm, davenport_off_flag6_of_pivot b e v hv hvL hvr deform hd hanti hscaled p hp⟩

theorem direct_davenport_off_flag42 (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L) (Q : ℝ) (hQ : 1 < Q)
    (c₀ c₂ c₃ : Fin 4 → ℝ) (u : Fin 6 → directCompoundGroup42 A₂ A₃ Q c₂ c₃)
    (hu : LinearIndependent ℝ (fun i => integerReal (u i : Fin 6 → ℤ)))
    (hatt : ∀ i, coordinateGauge6 (compoundCoordinates42 L hL Q hQ c₀)
      (integerReal (u i : Fin 6 → ℤ)) = directMinima42 A₂ A₃ L hL Q hQ c₀ c₂ c₃ i)
    (deform : Fin 6 → ℝ) (hd : ∀ i, 0 < deform i) (hanti : Antitone deform)
    (hscaled : Monotone (fun i => deform i * directMinima42 A₂ A₃ L hL Q hQ c₀ c₂ c₃ i)) :
    ∃ sigma : Equiv.Perm (Fin 6), ∀ j : Fin 6, ∀ z : directCompoundGroup42 A₂ A₃ Q c₂ c₃,
      integerReal (z : Fin 6 → ℤ) ∉ minimaFlag6 (fun i => integerReal (u i : Fin 6 → ℤ)) j →
      deform j * directMinima42 A₂ A₃ L hL Q hQ c₀ c₂ c₃ j / 64 ≤
        coordinateGauge6 (davenportCoordinates6 (compoundCoordinates42 L hL Q hQ c₀)
          deform sigma hd) (integerReal (z : Fin 6 → ℤ)) := by
  let b := directRealBasis42 A₂ A₃ Q c₂ c₃
  let e := compoundCoordinates42 L hL Q hQ c₀
  have hrad (i : Fin 6) : directMinima42 A₂ A₃ L hL Q hQ c₀ c₂ c₃ i =
      successiveRadius6 b e i := directMinima42_eq_radius A₂ A₃ L hL Q hQ c₀ c₂ c₃ i
  have hmem (z : directCompoundGroup42 A₂ A₃ Q c₂ c₃) :
      integerReal (z : Fin 6 → ℤ) ∈ lattice6Span b := by
    rw [directRealBasis42_span]
    exact ⟨(z : Fin 6 → ℤ), z.property, rfl⟩
  have hatt' (i : Fin 6) : coordinateGauge6 e (integerReal (u i : Fin 6 → ℤ)) =
      successiveRadius6 b e i := (hatt i).trans (hrad i)
  have hscaled' : Monotone (fun i => deform i * successiveRadius6 b e i) := by
    simpa only [← hrad] using hscaled
  obtain ⟨sigma, hsep⟩ := davenport_off_flag6 b e
    (fun i => integerReal (u i : Fin 6 → ℤ)) hu (fun i => hmem (u i)) hatt' deform hd hanti hscaled'
  refine ⟨sigma, ?_⟩
  intro j z hout
  rw [hrad]
  exact hsep j _ (hmem z) hout

def parallelepipedBody6 (e : (Fin 6 → ℝ) ≃ₗ[ℝ] (Fin 6 → ℝ)) : Set (Fin 6 → ℝ) :=
  e ⁻¹' Set.pi Set.univ (fun _ : Fin 6 => Set.Icc (-1 : ℝ) 1)

theorem mem_parallelepipedBody6_iff (e : (Fin 6 → ℝ) ≃ₗ[ℝ] (Fin 6 → ℝ)) (x : Fin 6 → ℝ) :
    x ∈ parallelepipedBody6 e ↔ coordinateGauge6 e x ≤ 1 := by
  simp [parallelepipedBody6, coordinateGauge6, pi_norm_le_iff_of_nonempty,
    Real.norm_eq_abs, abs_le, Pi.le_def, forall_and]

theorem parallelepipedBody6_volume (e : (Fin 6 → ℝ) ≃ₗ[ℝ] (Fin 6 → ℝ)) :
    MeasureTheory.volume.real (parallelepipedBody6 e) = 64 / |LinearMap.det e.toLinearMap| := by
  rw [MeasureTheory.measureReal_def, parallelepipedBody6,
    MeasureTheory.Measure.addHaar_preimage_linearEquiv,
    MeasureTheory.volume_pi, MeasureTheory.Measure.pi_pi]
  simp only [Real.volume_Icc, LinearEquiv.det_coe_symm, abs_inv,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal, abs_nonneg, div_eq_mul_inv]
  norm_num
  ring

theorem weightedCoordinates6_det (e : (Fin 6 → ℝ) ≃ₗ[ℝ] (Fin 6 → ℝ)) (w : Fin 6 → ℝ)
    (hw : ∀ i, 0 < w i) :
    LinearMap.det (weightedCoordinates6 e w hw).toLinearMap = LinearMap.det e.toLinearMap / ∏ i, w i := by
  let B := Pi.basisFun ℝ (Fin 6)
  have hm : LinearMap.toMatrix B B (weightedCoordinates6 e w hw).toLinearMap =
      Matrix.diagonal (fun i => (w i)⁻¹) * LinearMap.toMatrix B B e.toLinearMap := by
    ext i j
    simp [LinearMap.toMatrix_apply, B, Pi.basisFun_repr, Matrix.diagonal_mul,
      weightedCoordinates6, div_eq_mul_inv, mul_comm]
  rw [← LinearMap.det_toMatrix B, hm, Matrix.det_mul, Matrix.det_diagonal,
    Finset.prod_inv_distrib, LinearMap.det_toMatrix]
  ring

theorem davenportCoordinates6_det (e : (Fin 6 → ℝ) ≃ₗ[ℝ] (Fin 6 → ℝ))
    (deform : Fin 6 → ℝ) (sigma : Equiv.Perm (Fin 6)) (hd : ∀ i, 0 < deform i)
    (hprod : (∏ i, deform i) = 1) :
    LinearMap.det (davenportCoordinates6 e deform sigma hd).toLinearMap = LinearMap.det e.toLinearMap := by
  rw [davenportCoordinates6, weightedCoordinates6_det, Finset.prod_inv_distrib,
    Equiv.prod_comp, hprod, inv_one, div_one]

theorem davenportBody6_volume (e : (Fin 6 → ℝ) ≃ₗ[ℝ] (Fin 6 → ℝ))
    (deform : Fin 6 → ℝ) (sigma : Equiv.Perm (Fin 6)) (hd : ∀ i, 0 < deform i)
    (hprod : (∏ i, deform i) = 1) :
    MeasureTheory.volume.real (parallelepipedBody6 (davenportCoordinates6 e deform sigma hd)) =
      MeasureTheory.volume.real (parallelepipedBody6 e) := by
  rw [parallelepipedBody6_volume, parallelepipedBody6_volume, davenportCoordinates6_det e deform sigma hd hprod]

noncomputable def directDavenportMinima42 (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L) (Q : ℝ) (hQ : 1 < Q)
    (c₀ c₂ c₃ : Fin 4 → ℝ) (deform : Fin 6 → ℝ) (sigma : Equiv.Perm (Fin 6))
    (hd : ∀ i, 0 < deform i) (j : Fin 6) : ℝ :=
  successiveRadius6 (directRealBasis42 A₂ A₃ Q c₂ c₃)
    (davenportCoordinates6 (compoundCoordinates42 L hL Q hQ c₀) deform sigma hd) j

theorem directDavenportMinima42_eq_inf (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L) (Q : ℝ) (hQ : 1 < Q)
    (c₀ c₂ c₃ : Fin 4 → ℝ) (deform : Fin 6 → ℝ) (sigma : Equiv.Perm (Fin 6))
    (hd : ∀ i, 0 < deform i) (j : Fin 6) :
    directDavenportMinima42 A₂ A₃ L hL Q hQ c₀ c₂ c₃ deform sigma hd j =
      sInf {r : ℝ | ∃ u : Fin (j.val+1) → (Fin 6 → ℝ), LinearIndependent ℝ u ∧
        (∀ i, u i ∈ integerRealImage (directCompoundGroup42 A₂ A₃ Q c₂ c₃)) ∧
        ∀ i, coordinateGauge6
          (davenportCoordinates6 (compoundCoordinates42 L hL Q hQ c₀) deform sigma hd) (u i) ≤ r} := by
  simp only [directDavenportMinima42, successiveRadius6, directRealBasis42_span]

theorem exists_directDavenportMinima42_attaining (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L) (Q : ℝ) (hQ : 1 < Q)
    (c₀ c₂ c₃ : Fin 4 → ℝ) (deform : Fin 6 → ℝ) (sigma : Equiv.Perm (Fin 6))
    (hd : ∀ i, 0 < deform i) :
    ∃ u : Fin 6 → directCompoundGroup42 A₂ A₃ Q c₂ c₃,
      LinearIndependent ℝ (fun i => integerReal (u i : Fin 6 → ℤ)) ∧
      (∀ i, 0 < directDavenportMinima42 A₂ A₃ L hL Q hQ c₀ c₂ c₃ deform sigma hd i) ∧
      Monotone (directDavenportMinima42 A₂ A₃ L hL Q hQ c₀ c₂ c₃ deform sigma hd) ∧
      ∀ i, coordinateGauge6
        (davenportCoordinates6 (compoundCoordinates42 L hL Q hQ c₀) deform sigma hd)
          (integerReal (u i : Fin 6 → ℤ)) =
        directDavenportMinima42 A₂ A₃ L hL Q hQ c₀ c₂ c₃ deform sigma hd i := by
  classical
  let b := directRealBasis42 A₂ A₃ Q c₂ c₃
  let e' := davenportCoordinates6 (compoundCoordinates42 L hL Q hQ c₀) deform sigma hd
  obtain ⟨v, hv, hvL, hpos, hmono, hatt⟩ := exists_successive_minima6 b e'
  have hlift (j : Fin 6) : ∃ x : directCompoundGroup42 A₂ A₃ Q c₂ c₃,
      integerReal (x : Fin 6 → ℤ) = v j := by
    have hmem := hvL j
    rw [directRealBasis42_span] at hmem
    obtain ⟨x, hx, he⟩ := hmem
    exact ⟨⟨x, hx⟩, he⟩
  choose u hu using hlift
  have hfun : (fun j => integerReal (u j : Fin 6 → ℤ)) = v := funext hu
  refine ⟨u, ?_, hpos, hmono, ?_⟩
  · rw [hfun]
    exact hv
  · intro i
    rw [hu i]
    exact hatt i

theorem davenport_minima_lower6 (b : Basis (Fin 6) ℝ (Fin 6 → ℝ))
    (e' : (Fin 6 → ℝ) ≃ₗ[ℝ] (Fin 6 → ℝ)) (v : Fin 6 → (Fin 6 → ℝ))
    (hv : LinearIndependent ℝ v) (s : Fin 6 → ℝ)
    (hsep : ∀ j, ∀ x ∈ lattice6Span b, x ∉ minimaFlag6 v j → s j ≤ coordinateGauge6 e' x)
    (j : Fin 6) : s j ≤ successiveRadius6 b e' j := by
  obtain ⟨u, hu, huL, _, hm, hur⟩ := exists_successive_minima6 b e'
  let f : Fin (j.val+1) → Fin 6 := Fin.castLE (by omega)
  have hf : Function.Injective f := Fin.castLE_injective _
  obtain ⟨i, hi⟩ := independent_family_escapes_subspace6 (u ∘ f) (hu.comp f hf)
    (minimaFlag6 v j) (by rw [minimaFlag6_finrank v hv j]; omega)
  have hh := hsep j (u (f i)) (huL (f i)) hi
  rw [hur] at hh
  exact hh.trans (hm (show f i ≤ j from (by change i.val ≤ j.val; omega)))

theorem davenport_lower6 (b : Basis (Fin 6) ℝ (Fin 6 → ℝ))
    (e : (Fin 6 → ℝ) ≃ₗ[ℝ] (Fin 6 → ℝ)) (v : Fin 6 → (Fin 6 → ℝ))
    (hv : LinearIndependent ℝ v) (hvL : ∀ i, v i ∈ lattice6Span b)
    (hvr : ∀ i, coordinateGauge6 e (v i) = successiveRadius6 b e i)
    (deform : Fin 6 → ℝ) (hd : ∀ i, 0 < deform i) (hanti : Antitone deform)
    (hscaled : Monotone (fun i => deform i * successiveRadius6 b e i)) :
    ∃ sigma : Equiv.Perm (Fin 6),
      (∀ j, deform j * successiveRadius6 b e j / 64 ≤
        successiveRadius6 b (davenportCoordinates6 e deform sigma hd) j) ∧
      ∀ j : Fin 6, ∀ x ∈ lattice6Span b, x ∉ minimaFlag6 v j →
        deform j * successiveRadius6 b e j / 64 ≤
          coordinateGauge6 (davenportCoordinates6 e deform sigma hd) x := by
  obtain ⟨sigma, hsep⟩ := davenport_off_flag6 b e v hv hvL hvr deform hd hanti hscaled
  exact ⟨sigma, fun j => davenport_minima_lower6 b _ v hv _ hsep j, hsep⟩

noncomputable def gapRadius6 (rho : Fin 6 → ℝ) : ℝ :=
  (rho 0 * rho 1 * rho 2 * rho 3 * rho 4 ^ 2) ^ ((1 : ℝ) / 6)

noncomputable def gapDeformation6 (rho : Fin 6 → ℝ) (i : Fin 6) : ℝ :=
  gapRadius6 rho / rho (min i 4)

theorem gapRadius6_pos (rho : Fin 6 → ℝ) (hrho : ∀ i, 0 < rho i) : 0 < gapRadius6 rho :=
  Real.rpow_pos_of_pos
    (mul_pos (mul_pos (mul_pos (mul_pos (hrho 0) (hrho 1)) (hrho 2)) (hrho 3)) (pow_pos (hrho 4) 2)) _

theorem gapRadius6_power (rho : Fin 6 → ℝ) (hrho : ∀ i, 0 < rho i) :
    gapRadius6 rho ^ (6 : ℕ) = rho 0 * rho 1 * rho 2 * rho 3 * rho 4 ^ 2 := by
  unfold gapRadius6
  have hpos : 0 < rho 0 * rho 1 * rho 2 * rho 3 * rho 4 ^ 2 :=
    mul_pos (mul_pos (mul_pos (mul_pos (hrho 0) (hrho 1)) (hrho 2)) (hrho 3)) (pow_pos (hrho 4) 2)
  rw [← Real.rpow_natCast, ← Real.rpow_mul hpos.le]
  norm_num

theorem gapDeformation6_pos (rho : Fin 6 → ℝ) (hrho : ∀ i, 0 < rho i) :
    ∀ i, 0 < gapDeformation6 rho i := fun i => div_pos (gapRadius6_pos rho hrho) (hrho _)

theorem gapDeformation6_product (rho : Fin 6 → ℝ) (hrho : ∀ i, 0 < rho i) :
    (∏ i, gapDeformation6 rho i) = 1 := by
  change (∏ i, gapRadius6 rho / rho (min i 4)) = 1
  rw [Finset.prod_div_distrib]
  have hn : (∏ _i : Fin 6, gapRadius6 rho) = gapRadius6 rho ^ (6 : ℕ) := by simp
  have hden : (∏ i : Fin 6, rho (min i 4)) = rho 0 * rho 1 * rho 2 * rho 3 * rho 4 ^ 2 := by
    rw [Fin.prod_univ_six]
    change rho 0 * rho 1 * rho 2 * rho 3 * rho 4 * rho 4 = _
    ring
  rw [hn, hden, gapRadius6_power rho hrho]
  exact div_self (ne_of_gt
    (mul_pos (mul_pos (mul_pos (mul_pos (hrho 0) (hrho 1)) (hrho 2)) (hrho 3)) (pow_pos (hrho 4) 2)))

theorem gapDeformation6_antitone (rho : Fin 6 → ℝ) (hrho : ∀ i, 0 < rho i)
    (hm : Monotone rho) : Antitone (gapDeformation6 rho) := by
  intro i j hij
  exact div_le_div_of_nonneg_left (gapRadius6_pos rho hrho).le (hrho _)
    (hm (min_le_min hij le_rfl))

theorem gapDeformation6_scaled (rho : Fin 6 → ℝ) (hrho : ∀ i, 0 < rho i)
    (hm : Monotone rho) : Monotone (fun i => gapDeformation6 rho i * rho i) := by
  have hfirst (i : Fin 6) (hi : i ≤ 4) : gapDeformation6 rho i * rho i = gapRadius6 rho := by
    unfold gapDeformation6
    rw [min_eq_left hi]
    exact div_mul_cancel₀ _ (hrho i).ne'
  have hlast : gapRadius6 rho ≤ gapDeformation6 rho 5 * rho 5 := by
    calc
      _ = (gapRadius6 rho / rho 4) * rho 4 := (div_mul_cancel₀ _ (hrho 4).ne').symm
      _ ≤ (gapRadius6 rho / rho 4) * rho 5 :=
        mul_le_mul_of_nonneg_left (hm (by decide : (4 : Fin 6) ≤ 5))
          (div_pos (gapRadius6_pos rho hrho) (hrho 4)).le
      _ = _ := rfl
  intro i j hij
  change gapDeformation6 rho i * rho i ≤ gapDeformation6 rho j * rho j
  by_cases hj : j ≤ 4
  · rw [hfirst i (hij.trans hj), hfirst j hj]
  · have hj5 : j = 5 := by omega
    subst j
    by_cases hi : i ≤ 4
    · rw [hfirst i hi]
      exact hlast
    · have hi5 : i = 5 := by omega
      subst i
      exact le_rfl

theorem gapRadius6_source_formula (rho : Fin 6 → ℝ) (hrho : ∀ i, 0 < rho i) :
    gapRadius6 rho ^ (6 : ℕ) = (∏ i, rho i) * (rho 4 / rho 5) := by
  rw [gapRadius6_power rho hrho]
  rw [Fin.prod_univ_six]
  field_simp [(hrho 5).ne']
  ring

theorem davenportBody6_mem (e : (Fin 6 → ℝ) ≃ₗ[ℝ] (Fin 6 → ℝ))
    (deform : Fin 6 → ℝ) (sigma : Equiv.Perm (Fin 6)) (hd : ∀ i, 0 < deform i)
    (x : Fin 6 → ℝ) :
    x ∈ parallelepipedBody6 (davenportCoordinates6 e deform sigma hd) ↔
      ∀ i, deform (sigma i) * |e x i| ≤ 1 := by
  rw [mem_parallelepipedBody6_iff]
  change ‖davenportCoordinates6 e deform sigma hd x‖ ≤ 1 ↔ _
  rw [pi_norm_le_iff_of_nonempty]
  simp only [Real.norm_eq_abs, davenportCoordinates6_apply, abs_mul, abs_of_pos (hd _)]

theorem direct_davenportCoordinates42_apply (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c₀ : Fin 4 → ℝ)
    (deform : Fin 6 → ℝ) (sigma : Equiv.Perm (Fin 6)) (hd : ∀ i, 0 < deform i)
    (x : Fin 6 → ℝ) (i : Fin 6) :
    davenportCoordinates6 (compoundCoordinates42 L hL Q hQ c₀) deform sigma hd x i =
      deform (sigma i) * ((compound L *ᵥ x) i / Q ^ pairWeights42 c₀ i) := by
  rw [davenportCoordinates6_apply]
  change deform (sigma i) * ((compound L *ᵥ x) i /
    (Q ^ c₀ (lo i) * Q ^ c₀ (hi i))) = _
  rw [pairWeights42, Real.rpow_add (lt_trans zero_lt_one hQ)]

theorem source_davenport_lower42 (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (_h₂ : A₂.det = 1) (_h₃ : A₃.det = 1)
    (hL : L.det = 1) (_hAlg : ∀ i j, IsAlgebraic ℚ (L i j))
    (c₀ c₂ c₃ : Fin 4 → ℝ) (_hc₀ : ∀ i, |c₀ i| ≤ 1)
    (_hc₂ : ∀ i, -1 ≤ c₂ i ∧ c₂ i ≤ 0) (_hc₃ : ∀ i, -1 ≤ c₃ i ∧ c₃ i ≤ 0)
    (_hb : ∑ i, (c₀ i + c₂ i + c₃ i) = 0)
    (Q : ℝ) (hQ : 1 < Q) (u : Fin 6 → directCompoundGroup42 A₂ A₃ Q c₂ c₃)
    (hu : LinearIndependent ℝ (fun i => integerReal (u i : Fin 6 → ℤ)))
    (hatt : ∀ i, coordinateGauge6 (compoundCoordinates42 L (sourceUnit42 L hL) Q hQ c₀)
      (integerReal (u i : Fin 6 → ℤ)) =
        directMinima42 A₂ A₃ L (sourceUnit42 L hL) Q hQ c₀ c₂ c₃ i) :
    let rho := directMinima42 A₂ A₃ L (sourceUnit42 L hL) Q hQ c₀ c₂ c₃
    let deform := gapDeformation6 rho
    ∃ hd : ∀ i, 0 < deform i, (∏ i, deform i) = 1 ∧ Antitone deform ∧
      Monotone (fun i => deform i * rho i) ∧
      ∃ sigma : Equiv.Perm (Fin 6),
        (∀ j, deform j * rho j / 64 ≤
          directDavenportMinima42 A₂ A₃ L (sourceUnit42 L hL) Q hQ c₀ c₂ c₃ deform sigma hd j) ∧
        MeasureTheory.volume.real (parallelepipedBody6
          (davenportCoordinates6 (compoundCoordinates42 L (sourceUnit42 L hL) Q hQ c₀) deform sigma hd)) =
            MeasureTheory.volume.real (compoundBody42 L Q c₀) ∧
        ∀ j : Fin 6, ∀ z : directCompoundGroup42 A₂ A₃ Q c₂ c₃,
          integerReal (z : Fin 6 → ℤ) ∉ minimaFlag6 (fun i => integerReal (u i : Fin 6 → ℤ)) j →
          deform j * rho j / 64 ≤ coordinateGauge6
            (davenportCoordinates6 (compoundCoordinates42 L (sourceUnit42 L hL) Q hQ c₀) deform sigma hd)
              (integerReal (z : Fin 6 → ℤ)) := by
  dsimp only
  let b := directRealBasis42 A₂ A₃ Q c₂ c₃
  let e := compoundCoordinates42 L (sourceUnit42 L hL) Q hQ c₀
  let rho := directMinima42 A₂ A₃ L (sourceUnit42 L hL) Q hQ c₀ c₂ c₃
  let deform := gapDeformation6 rho
  obtain ⟨hrho, hm⟩ := directMinima42_pos_mono A₂ A₃ L (sourceUnit42 L hL) Q hQ c₀ c₂ c₃
  have hd : ∀ i, 0 < deform i := gapDeformation6_pos rho hrho
  have hprod : (∏ i, deform i) = 1 := gapDeformation6_product rho hrho
  have hanti : Antitone deform := gapDeformation6_antitone rho hrho hm
  have hscaled : Monotone (fun i => deform i * rho i) := gapDeformation6_scaled rho hrho hm
  have hrad (i : Fin 6) : rho i = successiveRadius6 b e i :=
    directMinima42_eq_radius A₂ A₃ L (sourceUnit42 L hL) Q hQ c₀ c₂ c₃ i
  have hmem (z : directCompoundGroup42 A₂ A₃ Q c₂ c₃) :
      integerReal (z : Fin 6 → ℤ) ∈ lattice6Span b := by
    rw [directRealBasis42_span]
    exact ⟨(z : Fin 6 → ℤ), z.property, rfl⟩
  have hatt' (i : Fin 6) : coordinateGauge6 e (integerReal (u i : Fin 6 → ℤ)) =
      successiveRadius6 b e i := (hatt i).trans (hrad i)
  have hscaled' : Monotone (fun i => deform i * successiveRadius6 b e i) := by
    simpa only [← hrad] using hscaled
  obtain ⟨sigma, hlower, hsep⟩ := davenport_lower6 b e
    (fun i => integerReal (u i : Fin 6 → ℤ)) hu (fun i => hmem (u i)) hatt' deform hd hanti hscaled'
  refine ⟨hd, hprod, hanti, hscaled, sigma, ?_, ?_, ?_⟩
  · intro j
    change deform j * rho j / 64 ≤ successiveRadius6 b (davenportCoordinates6 e deform sigma hd) j
    rw [hrad]
    exact hlower j
  · have hbody : parallelepipedBody6 e = compoundBody42 L Q c₀ := by
      ext x
      rw [mem_parallelepipedBody6_iff,
        compoundBody42_mem_iff L (sourceUnit42 L hL) Q hQ c₀ x]
      rfl
    rw [← hbody]
    exact davenportBody6_volume e deform sigma hd hprod
  · intro j z hout
    change deform j * rho j / 64 ≤
      coordinateGauge6 (davenportCoordinates6 e deform sigma hd) (integerReal (z : Fin 6 → ℤ))
    rw [hrad]
    exact hsep j _ (hmem z) hout

theorem davenport_adapted_rows6 (v : Fin 6 → (Fin 6 → ℝ)) (hv : LinearIndependent ℝ v) :
    ∃ p : Equiv.Perm (Fin 6), ∃ y : Fin 6 → (Fin 6 → ℝ),
      (∀ j, v j - y j ∈ minimaFlag6 v j) ∧
      (∀ j i : Fin 6, i < j → y j (p i) = 0) ∧
      (∀ j : Fin 6, ‖y j‖ ≤ (2 : ℝ)^j.val * ‖v j‖) ∧
      ∀ j : Fin 6, ∀ x ∈ prefixSpan6 v (j.val+1) (by omega), ∀ M : ℝ, 0 ≤ M →
        (∀ i : Fin (j.val+1), |x (p (Fin.castLE (by omega) i))| ≤ M) → ‖x‖ ≤ 64*M := by
  classical
  obtain ⟨p, hp, hb⟩ := davenport_pivot_prefix6 v hv 6 le_rfl
  let q : Equiv.Perm (Fin 6) := Equiv.ofBijective p (Finite.injective_iff_bijective.mp hp)
  have hex (j : Fin 6) : ∃ w : minimaFlag6 v j,
      (∀ i : Fin j.val, w.val (q (Fin.castLE (by omega) i)) = v j (q (Fin.castLE (by omega) i))) ∧
      ‖w.val‖ ≤ ((2 : ℝ)^j.val-1)*‖v j‖ := by
    have hj6 : j.val ≤ 6 := Nat.le_of_lt j.isLt
    let f : minimaFlag6 v j →ₗ[ℝ] (Fin j.val → ℝ) :=
      { toFun := fun x i => x.val (q (Fin.castLE hj6 i))
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    have hf : Function.Injective f := by
      intro x1 x2 he
      apply Subtype.ext
      apply sub_eq_zero.mp
      apply norm_eq_zero.mp
      apply le_antisymm ?_ (norm_nonneg _)
      have hxW : x1.val-x2.val ∈ prefixSpan6 v j.val hj6 :=
        (minimaFlag6 v j).sub_mem x1.property x2.property
      have hzero (i : Fin j.val) : |(x1.val-x2.val) (p (Fin.castLE hj6 i))| ≤ (0 : ℝ) := by
        have hi := congrFun he i
        change x1.val (p (Fin.castLE hj6 i)) = x2.val (p (Fin.castLE hj6 i)) at hi
        change |x1.val (p (Fin.castLE hj6 i))-x2.val (p (Fin.castLE hj6 i))| ≤ (0 : ℝ)
        exact le_of_eq ((congrArg abs (sub_eq_zero.mpr hi)).trans abs_zero)
      have hn := hb j.val hj6 (x1.val-x2.val) hxW 0 le_rfl hzero
      simpa using hn
    have hdim : Module.finrank ℝ (minimaFlag6 v j) = Module.finrank ℝ (Fin j.val → ℝ) := by
      rw [minimaFlag6_finrank v hv j]
      simp
    have hsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim (f := f)).mp hf
    obtain ⟨w, hw⟩ := hsurj (fun i => v j (q (Fin.castLE hj6 i)))
    have hcoords (i : Fin j.val) : w.val (q (Fin.castLE hj6 i)) = v j (q (Fin.castLE hj6 i)) :=
      congrFun hw i
    refine ⟨w, hcoords, ?_⟩
    apply hb j.val hj6 w.val w.property ‖v j‖ (norm_nonneg _)
    intro i
    rw [show p (Fin.castLE hj6 i) = q (Fin.castLE hj6 i) from rfl, hcoords]
    simpa only [Real.norm_eq_abs] using norm_le_pi_norm (v j) (q (Fin.castLE hj6 i))
  choose w hw hnorm using hex
  refine ⟨q, fun j => v j-(w j).val, ?_, ?_, ?_, ?_⟩
  · intro j
    have he : v j-(v j-(w j).val) = (w j).val := by abel
    rw [he]
    exact (w j).property
  · intro j i hij
    let t : Fin j.val := ⟨i.val, hij⟩
    have hi : (Fin.castLE (by omega) t : Fin 6) = i := Fin.ext rfl
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
    have hC : (2 : ℝ)^(j.val+1)-1 ≤ 64 := by fin_cases j <;> norm_num
    exact hn.trans (mul_le_mul_of_nonneg_right hC hM)

theorem independent_prefix_adjustment6 (v w : Fin 6 → (Fin 6 → ℝ))
    (hv : LinearIndependent ℝ v) (hw : ∀ j, w j-v j ∈ minimaFlag6 v j) :
    LinearIndependent ℝ w := by
  classical
  let b := basisOfLinearIndependentOfCardEqFinrank hv (by simp)
  have hb (i : Fin 6) : b i = v i :=
    congrFun (coe_basisOfLinearIndependentOfCardEqFinrank hv _) i
  let f := b.equivFun
  have hbase (j i : Fin 6) : f (v j) i = if j = i then 1 else 0 := by
    rw [← hb j]
    exact b.equivFun_self j i
  have hzero (j i : Fin 6) (hji : j ≤ i) (x : Fin 6 → ℝ) (hx : x ∈ minimaFlag6 v j) :
      f x i = 0 := by
    let g : (Fin 6 → ℝ) →ₗ[ℝ] ℝ := (LinearMap.proj i).comp f.toLinearMap
    have hs : minimaFlag6 v j ≤ LinearMap.ker g := by
      apply Submodule.span_le.mpr
      rintro _ ⟨k, rfl⟩
      change f (v (Fin.castLE (by omega) k)) i = 0
      rw [hbase]
      have hne : (Fin.castLE (by omega) k : Fin 6) ≠ i := by
        intro heq
        have he := congrArg Fin.val heq
        change k.val = i.val at he
        omega
      simp only [hne, if_false]
    exact hs hx
  have hcoeff (j i : Fin 6) (hji : j ≤ i) : f (w j) i = f (v j) i := by
    have hz := hzero j i hji (w j-v j) (hw j)
    have he : f (w j-v j) i = f (w j) i-f (v j) i := by
      rw [map_sub]
      rfl
    rw [he] at hz
    exact sub_eq_zero.mp hz
  let T : Matrix (Fin 6) (Fin 6) ℝ := fun j i => f (w j) i
  have hdiag (i : Fin 6) : T i i = 1 := by
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

theorem davenport_integral_reduce6 (Lambda : Submodule ℤ (Fin 6 → ℝ))
    (v : Fin 6 → (Fin 6 → ℝ)) (hvL : ∀ i, v i ∈ Lambda)
    (F : (Fin 6 → ℝ) ≃ₗ[ℝ] (Fin 6 → ℝ))
    (htri : ∀ i j : Fin 6, j < i → F (v j) i = 0)
    (hdiag : ∀ i : Fin 6, F (v i) i = 1)
    (k : ℕ) (hk : k ≤ 6) (x : Fin 6 → ℝ) (hx : x ∈ Lambda) :
    ∃ z ∈ Lambda, z-x ∈ prefixSpan6 v k hk ∧
      (∀ i : Fin 6, i.val < k → 0 ≤ F z i ∧ F z i < 1) ∧
      (∀ i : Fin 6, k ≤ i.val → F z i = F x i) := by
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
    have hk0 : k ≤ 6 := by omega
    let a : Fin 6 := ⟨k, by omega⟩
    let n : ℤ := Int.floor (F x a)
    let x' : Fin 6 → ℝ := x-(n : ℝ) • v a
    have hx'L : x' ∈ Lambda := by
      apply Lambda.sub_mem hx
      simpa only [Int.cast_smul_eq_zsmul] using Lambda.smul_mem n (hvL a)
    obtain ⟨z, hzL, hzspan, hzlo, hzhi⟩ := ih hk0 x' hx'L
    have hdelta : x'-x ∈ prefixSpan6 v (k+1) hk := by
      have hva : v a ∈ prefixSpan6 v (k+1) hk :=
        Submodule.subset_span ⟨⟨k, Nat.lt_succ_self k⟩, rfl⟩
      have he : x'-x = -((n : ℝ) • v a) := by dsimp [x']; abel
      rw [he]
      exact (prefixSpan6 v (k+1) hk).neg_mem ((prefixSpan6 v (k+1) hk).smul_mem (n : ℝ) hva)
    have hfrac : F x' a = Int.fract (F x a) := by
      simp only [x', map_sub, map_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
        hdiag a, mul_one, n, Int.self_sub_floor]
    refine ⟨z, hzL, ?_, ?_, ?_⟩
    · have he : z-x = (z-x')+(x'-x) := by abel
      rw [he]
      exact (prefixSpan6 v (k+1) hk).add_mem
        (prefixSpan6_mono v hk0 hk (Nat.le_succ k) hzspan) hdelta
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

theorem basis_prefix_coordinate_zero6 (b : Basis (Fin 6) ℝ (Fin 6 → ℝ))
    (j i : Fin 6) (hji : j ≤ i) (x : Fin 6 → ℝ) (hx : x ∈ minimaFlag6 b j) :
    b.equivFun x i = 0 := by
  let g : (Fin 6 → ℝ) →ₗ[ℝ] ℝ := (LinearMap.proj i).comp b.equivFun.toLinearMap
  have hs : minimaFlag6 b j ≤ LinearMap.ker g := by
    apply Submodule.span_le.mpr
    rintro _ ⟨k, rfl⟩
    change b.equivFun (b (Fin.castLE (by omega) k)) i = 0
    rw [b.equivFun_self]
    have hne : (Fin.castLE (by omega) k : Fin 6) ≠ i := by
      intro heq
      have he := congrArg Fin.val heq
      change k.val = i.val at he
      omega
    exact if_neg hne
  exact hs hx

theorem davenport_adapted_basis6 (v y : Fin 6 → (Fin 6 → ℝ)) (hv : LinearIndependent ℝ v)
    (hadapt : ∀ j, v j-y j ∈ minimaFlag6 v j) :
    ∃ b : Basis (Fin 6) ℝ (Fin 6 → ℝ), (∀ i, b i = y i) ∧
      ∀ j i : Fin 6, j ≤ i → b.equivFun (v j) i = if j = i then 1 else 0 := by
  classical
  have hy : LinearIndependent ℝ y := independent_prefix_adjustment6 v y hv (by
    intro j
    simpa only [neg_sub] using (minimaFlag6 v j).neg_mem (hadapt j))
  let b := basisOfLinearIndependentOfCardEqFinrank hy (by simp)
  have hb (i : Fin 6) : b i = y i :=
    congrFun (coe_basisOfLinearIndependentOfCardEqFinrank hy _) i
  have hbfun : (b : Fin 6 → (Fin 6 → ℝ)) = y := funext hb
  have hflags (j : Fin 6) : minimaFlag6 b j = minimaFlag6 v j := by
    apply Submodule.eq_of_le_of_finrank_eq
    · apply Submodule.span_le.mpr
      rintro _ ⟨k, rfl⟩
      let i : Fin 6 := Fin.castLE (by omega) k
      change b i ∈ minimaFlag6 v j
      rw [hb i]
      have hij : i ≤ j := by change k.val ≤ j.val; omega
      have hvj : v i ∈ minimaFlag6 v j := Submodule.subset_span ⟨k, rfl⟩
      have hwj : v i-y i ∈ minimaFlag6 v j := minimaFlag6_mono v hij (hadapt i)
      have he : v i-(v i-y i) = y i := by abel
      rw [← he]
      exact (minimaFlag6 v j).sub_mem hvj hwj
    · rw [minimaFlag6_finrank _ b.linearIndependent, minimaFlag6_finrank v hv]
  refine ⟨b, hb, ?_⟩
  intro j i hji
  have hx : v j-y j ∈ minimaFlag6 b j := (hflags j).symm ▸ hadapt j
  have hz := basis_prefix_coordinate_zero6 b j i hji (v j-y j) hx
  have he : b.equivFun (v j-y j) i = b.equivFun (v j) i-b.equivFun (y j) i := by
    rw [map_sub]
    rfl
  rw [he] at hz
  have hycoord : b.equivFun (y j) i = if j = i then 1 else 0 := by
    rw [← hb j]
    exact b.equivFun_self j i
  rw [← hycoord]
  exact sub_eq_zero.mp hz

theorem davenportCoordinates6_comp (e : (Fin 6 → ℝ) ≃ₗ[ℝ] (Fin 6 → ℝ))
    (deform : Fin 6 → ℝ) (sigma : Equiv.Perm (Fin 6)) (hd : ∀ i, 0 < deform i)
    (x : Fin 6 → ℝ) :
    davenportCoordinates6 e deform sigma hd x =
      davenportCoordinates6 (LinearEquiv.refl ℝ (Fin 6 → ℝ)) deform sigma hd (e x) := by
  ext i
  rw [davenportCoordinates6_apply, davenportCoordinates6_apply]
  rfl

theorem davenport_row_gauge_bound6 (y : Fin 6 → ℝ) (p : Equiv.Perm (Fin 6))
    (deform : Fin 6 → ℝ) (hd : ∀ i, 0 < deform i) (hanti : Antitone deform)
    (j : Fin 6) (hzero : ∀ i : Fin 6, i < j → y (p i) = 0) :
    coordinateGauge6 (davenportCoordinates6 (LinearEquiv.refl ℝ (Fin 6 → ℝ)) deform p.symm hd) y ≤
      deform j * ‖y‖ := by
  change ‖davenportCoordinates6 (LinearEquiv.refl ℝ (Fin 6 → ℝ)) deform p.symm hd y‖ ≤ _
  apply (pi_norm_le_iff_of_nonempty _).mpr
  intro a
  rw [Real.norm_eq_abs, davenportCoordinates6_apply]
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

theorem davenport_reduced_frame6 (b : Basis (Fin 6) ℝ (Fin 6 → ℝ))
    (e : (Fin 6 → ℝ) ≃ₗ[ℝ] (Fin 6 → ℝ)) (v : Fin 6 → (Fin 6 → ℝ))
    (hv : LinearIndependent ℝ v) (hvL : ∀ i, v i ∈ lattice6Span b)
    (hvr : ∀ i, coordinateGauge6 e (v i) = successiveRadius6 b e i)
    (deform : Fin 6 → ℝ) (hd : ∀ i, 0 < deform i) (hanti : Antitone deform)
    (hscaled : Monotone (fun i => deform i * successiveRadius6 b e i)) :
    ∃ p : Equiv.Perm (Fin 6), ∃ z : Fin 6 → (Fin 6 → ℝ), LinearIndependent ℝ z ∧
      (∀ i, z i ∈ lattice6Span b) ∧
      (∀ j, coordinateGauge6 (davenportCoordinates6 e deform p.symm hd) (z j) ≤
        64 * (deform j * successiveRadius6 b e j)) ∧
      ∀ j : Fin 6, ∀ x ∈ prefixSpan6 (e ∘ v) (j.val+1) (by omega), ∀ M : ℝ, 0 ≤ M →
        (∀ i : Fin (j.val+1), |x (p (Fin.castLE (by omega) i))| ≤ M) → ‖x‖ ≤ 64*M := by
  classical
  have he : LinearIndependent ℝ (e ∘ v) :=
    hv.map' e.toLinearMap (LinearMap.ker_eq_bot.mpr e.injective)
  obtain ⟨p, y, hyspan, hyzero, hynorm, hp⟩ := davenport_adapted_rows6 (e ∘ v) he
  obtain ⟨B, hB, hcoeff⟩ := davenport_adapted_basis6 (e ∘ v) y he hyspan
  let F : (Fin 6 → ℝ) ≃ₗ[ℝ] (Fin 6 → ℝ) := e.trans B.equivFun
  have htri (i j : Fin 6) (hji : j < i) : F (v j) i = 0 := by
    have h := hcoeff j i hji.le
    change B.equivFun (e (v j)) i = 0
    simpa only [Function.comp_apply, ne_of_lt hji, if_false] using h
  have hdiag (i : Fin 6) : F (v i) i = 1 := by
    simpa only [Function.comp_apply, if_pos rfl] using hcoeff i i le_rfl
  have hex (j : Fin 6) : ∃ z ∈ lattice6Span b, z-v j ∈ minimaFlag6 v j ∧
      (∀ i : Fin 6, i < j → 0 ≤ F z i ∧ F z i < 1) ∧
      (∀ i : Fin 6, j ≤ i → F z i = if j = i then 1 else 0) := by
    obtain ⟨z, hzL, hzspan, hzlo, hzhi⟩ :=
      davenport_integral_reduce6 (lattice6Span b) v hvL F htri hdiag j.val (by omega) (v j) (hvL j)
    refine ⟨z, hzL, hzspan, hzlo, ?_⟩
    intro i hji
    rw [hzhi i hji]
    exact hcoeff j i hji
  choose z hzL hzspan hzlo hzhi using hex
  have hz : LinearIndependent ℝ z := independent_prefix_adjustment6 v z hv hzspan
  let D := davenportCoordinates6 (LinearEquiv.refl ℝ (Fin 6 → ℝ)) deform p.symm hd
  have hybound (i : Fin 6) : coordinateGauge6 D (y i) ≤
      (2 : ℝ)^i.val * (deform i * successiveRadius6 b e i) := by
    have h0 := davenport_row_gauge_bound6 (y i) p deform hd hanti i (hyzero i)
    have h1 := mul_le_mul_of_nonneg_left (hynorm i) (hd i).le
    have h2 : deform i * ((2 : ℝ)^i.val * ‖(e ∘ v) i‖) =
        (2 : ℝ)^i.val * (deform i * successiveRadius6 b e i) := by
      change deform i * ((2 : ℝ)^i.val * coordinateGauge6 e (v i)) = _
      rw [hvr i]
      ring
    exact h0.trans (h1.trans_eq h2)
  refine ⟨p, z, hz, hzL, ?_, hp⟩
  intro j
  have haj : 0 ≤ deform j * successiveRadius6 b e j := by
    apply mul_nonneg (hd j).le
    rw [← hvr j]
    exact norm_nonneg _
  have hrepr : e (z j) = ∑ i : Fin 6, F (z j) i • y i := by
    have hh := B.sum_equivFun (e (z j))
    simpa only [hB] using hh.symm
  have hnorm : coordinateGauge6 (davenportCoordinates6 e deform p.symm hd) (z j) ≤
      ∑ i : Fin 6, (2 : ℝ)^i.val * (deform j * successiveRadius6 b e j) := by
    change ‖davenportCoordinates6 e deform p.symm hd (z j)‖ ≤ _
    rw [davenportCoordinates6_comp, hrepr, map_sum]
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
  have hsum : (∑ i : Fin 6, (2 : ℝ)^i.val * (deform j * successiveRadius6 b e j)) =
      63 * (deform j * successiveRadius6 b e j) := by
    have hpow : (∑ i : Fin 6, (2 : ℝ)^i.val) = 63 := by
      rw [Fin.sum_univ_six]
      change (2 : ℝ)^0+2^1+2^2+2^3+2^4+2^5 = 63
      norm_num
    rw [← Finset.sum_mul, hpow]
  rw [hsum] at hnorm
  exact hnorm.trans (mul_le_mul_of_nonneg_right (by norm_num : (63 : ℝ) ≤ 64) haj)

theorem davenport_lemma6 (b : Basis (Fin 6) ℝ (Fin 6 → ℝ))
    (e : (Fin 6 → ℝ) ≃ₗ[ℝ] (Fin 6 → ℝ)) (v : Fin 6 → (Fin 6 → ℝ))
    (hv : LinearIndependent ℝ v) (hvL : ∀ i, v i ∈ lattice6Span b)
    (hvr : ∀ i, coordinateGauge6 e (v i) = successiveRadius6 b e i)
    (deform : Fin 6 → ℝ) (hd : ∀ i, 0 < deform i) (hprod : (∏ i, deform i) = 1)
    (hanti : Antitone deform) (hscaled : Monotone (fun i => deform i * successiveRadius6 b e i)) :
    ∃ sigma : Equiv.Perm (Fin 6),
      (∀ j, deform j * successiveRadius6 b e j / 64 ≤
          successiveRadius6 b (davenportCoordinates6 e deform sigma hd) j ∧
        successiveRadius6 b (davenportCoordinates6 e deform sigma hd) j ≤
          64 * (deform j * successiveRadius6 b e j)) ∧
      MeasureTheory.volume.real (parallelepipedBody6 (davenportCoordinates6 e deform sigma hd)) =
        MeasureTheory.volume.real (parallelepipedBody6 e) ∧
      ∀ j : Fin 6, ∀ x ∈ lattice6Span b, x ∉ minimaFlag6 v j →
        deform j * successiveRadius6 b e j / 64 ≤
          coordinateGauge6 (davenportCoordinates6 e deform sigma hd) x := by
  obtain ⟨p, z, hz, hzL, hzbound, hp⟩ := davenport_reduced_frame6 b e v hv hvL hvr deform hd hanti hscaled
  have hsep := davenport_off_flag6_of_pivot b e v hv hvL hvr deform hd hanti hscaled p hp
  refine ⟨p.symm, ?_, davenportBody6_volume e deform p.symm hd hprod, hsep⟩
  intro j
  refine ⟨davenport_minima_lower6 b _ v hv _ hsep j, ?_⟩
  let f : Fin (j.val+1) → Fin 6 := Fin.castLE (by omega)
  apply successiveRadius6_le_family b _ j (z ∘ f) (hz.comp f (Fin.castLE_injective _))
    (fun i => hzL (f i))
  intro i
  have hi : f i ≤ j := by change i.val ≤ j.val; omega
  exact (hzbound (f i)).trans (mul_le_mul_of_nonneg_left (hscaled hi) (by norm_num : (0 : ℝ) ≤ 64))

theorem source_davenport42 (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (_h₂ : A₂.det = 1) (_h₃ : A₃.det = 1)
    (hL : L.det = 1) (_hAlg : ∀ i j, IsAlgebraic ℚ (L i j))
    (c₀ c₂ c₃ : Fin 4 → ℝ) (_hc₀ : ∀ i, |c₀ i| ≤ 1)
    (_hc₂ : ∀ i, -1 ≤ c₂ i ∧ c₂ i ≤ 0) (_hc₃ : ∀ i, -1 ≤ c₃ i ∧ c₃ i ≤ 0)
    (_hb : ∑ i, (c₀ i + c₂ i + c₃ i) = 0)
    (Q : ℝ) (hQ : 1 < Q) (u : Fin 6 → directCompoundGroup42 A₂ A₃ Q c₂ c₃)
    (hu : LinearIndependent ℝ (fun i => integerReal (u i : Fin 6 → ℤ)))
    (hatt : ∀ i, coordinateGauge6 (compoundCoordinates42 L (sourceUnit42 L hL) Q hQ c₀)
      (integerReal (u i : Fin 6 → ℤ)) =
        directMinima42 A₂ A₃ L (sourceUnit42 L hL) Q hQ c₀ c₂ c₃ i) :
    let rho := directMinima42 A₂ A₃ L (sourceUnit42 L hL) Q hQ c₀ c₂ c₃
    let deform := gapDeformation6 rho
    ∃ hd : ∀ i, 0 < deform i, (∏ i, deform i) = 1 ∧ Antitone deform ∧
      Monotone (fun i => deform i * rho i) ∧
      ∃ sigma : Equiv.Perm (Fin 6),
        (∀ j, deform j * rho j / 64 ≤
            directDavenportMinima42 A₂ A₃ L (sourceUnit42 L hL) Q hQ c₀ c₂ c₃ deform sigma hd j ∧
          directDavenportMinima42 A₂ A₃ L (sourceUnit42 L hL) Q hQ c₀ c₂ c₃ deform sigma hd j ≤
            64 * (deform j * rho j)) ∧
        MeasureTheory.volume.real (parallelepipedBody6
          (davenportCoordinates6 (compoundCoordinates42 L (sourceUnit42 L hL) Q hQ c₀) deform sigma hd)) =
            MeasureTheory.volume.real (compoundBody42 L Q c₀) ∧
        ∀ j : Fin 6, ∀ z : directCompoundGroup42 A₂ A₃ Q c₂ c₃,
          integerReal (z : Fin 6 → ℤ) ∉ minimaFlag6 (fun i => integerReal (u i : Fin 6 → ℤ)) j →
          deform j * rho j / 64 ≤ coordinateGauge6
            (davenportCoordinates6 (compoundCoordinates42 L (sourceUnit42 L hL) Q hQ c₀) deform sigma hd)
              (integerReal (z : Fin 6 → ℤ)) := by
  dsimp only
  let b := directRealBasis42 A₂ A₃ Q c₂ c₃
  let e := compoundCoordinates42 L (sourceUnit42 L hL) Q hQ c₀
  let rho := directMinima42 A₂ A₃ L (sourceUnit42 L hL) Q hQ c₀ c₂ c₃
  let deform := gapDeformation6 rho
  obtain ⟨hrho, hm⟩ := directMinima42_pos_mono A₂ A₃ L (sourceUnit42 L hL) Q hQ c₀ c₂ c₃
  have hd : ∀ i, 0 < deform i := gapDeformation6_pos rho hrho
  have hprod : (∏ i, deform i) = 1 := gapDeformation6_product rho hrho
  have hanti : Antitone deform := gapDeformation6_antitone rho hrho hm
  have hscaled : Monotone (fun i => deform i * rho i) := gapDeformation6_scaled rho hrho hm
  have hrad (i : Fin 6) : rho i = successiveRadius6 b e i :=
    directMinima42_eq_radius A₂ A₃ L (sourceUnit42 L hL) Q hQ c₀ c₂ c₃ i
  have hmem (z : directCompoundGroup42 A₂ A₃ Q c₂ c₃) :
      integerReal (z : Fin 6 → ℤ) ∈ lattice6Span b := by
    rw [directRealBasis42_span]
    exact ⟨(z : Fin 6 → ℤ), z.property, rfl⟩
  have hatt' (i : Fin 6) : coordinateGauge6 e (integerReal (u i : Fin 6 → ℤ)) =
      successiveRadius6 b e i := (hatt i).trans (hrad i)
  have hscaled' : Monotone (fun i => deform i * successiveRadius6 b e i) := by
    simpa only [← hrad] using hscaled
  obtain ⟨sigma, hbounds, _, hsep⟩ := davenport_lemma6 b e
    (fun i => integerReal (u i : Fin 6 → ℤ)) hu (fun i => hmem (u i)) hatt' deform hd hprod hanti hscaled'
  refine ⟨hd, hprod, hanti, hscaled, sigma, ?_, ?_, ?_⟩
  · intro j
    change deform j * rho j / 64 ≤ successiveRadius6 b (davenportCoordinates6 e deform sigma hd) j ∧
      successiveRadius6 b (davenportCoordinates6 e deform sigma hd) j ≤ 64 * (deform j * rho j)
    rw [hrad]
    exact hbounds j
  · have hbody : parallelepipedBody6 e = compoundBody42 L Q c₀ := by
      ext x
      rw [mem_parallelepipedBody6_iff,
        compoundBody42_mem_iff L (sourceUnit42 L hL) Q hQ c₀ x]
      rfl
    rw [← hbody]
    exact davenportBody6_volume e deform sigma hd hprod
  · intro j z hout
    change deform j * rho j / 64 ≤
      coordinateGauge6 (davenportCoordinates6 e deform sigma hd) (integerReal (z : Fin 6 → ℤ))
    rw [hrad]
    exact hsep j _ (hmem z) hout

end
end CompoundFeasibility
