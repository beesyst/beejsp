import SubspaceBridge.SelectedProductVanishing3
import Mathlib.LinearAlgebra.CrossProduct
open scoped BigOperators
open MeasureTheory
namespace JSP000334

noncomputable def davenportWidths3 (A rho : Fin 3 → ℝ) (sigma : Equiv.Perm (Fin 3)) : Fin 3 → ℝ :=
  fun i => A i/rho (sigma i)

theorem davenportWidths3_pos (A rho : Fin 3 → ℝ) (sigma : Equiv.Perm (Fin 3))
    (hA : ∀ i, 0 < A i) (hrho : ∀ i, 0 < rho i) : ∀ i, 0 < davenportWidths3 A rho sigma i :=
  fun i => div_pos (hA i) (hrho (sigma i))

noncomputable def davenportCoordinates3 (L : RealTriple ≃ₗ[ℝ] RealTriple)
    (A rho : Fin 3 → ℝ) (sigma : Equiv.Perm (Fin 3))
    (hA : ∀ i, 0 < A i) (hrho : ∀ i, 0 < rho i) : RealTriple ≃ₗ[ℝ] RealTriple :=
  archCoordinates3 L (davenportWidths3 A rho sigma) (davenportWidths3_pos A rho sigma hA hrho)

noncomputable def davenportBody3 (L : RealTriple ≃ₗ[ℝ] RealTriple)
    (A rho : Fin 3 → ℝ) (sigma : Equiv.Perm (Fin 3)) : Set RealTriple :=
  archBody3 L (davenportWidths3 A rho sigma)

theorem davenportCoordinates3_apply (L : RealTriple ≃ₗ[ℝ] RealTriple)
    (A rho : Fin 3 → ℝ) (sigma : Equiv.Perm (Fin 3))
    (hA : ∀ i, 0 < A i) (hrho : ∀ i, 0 < rho i) (x : RealTriple) (i : Fin 3) :
    davenportCoordinates3 L A rho sigma hA hrho x i = rho (sigma i)/A i*L x i := by
  change L x i/(A i/rho (sigma i)) = _
  field_simp
  ring

theorem davenportCoordinates3_inverse (L : RealTriple ≃ₗ[ℝ] RealTriple)
    (A rho : Fin 3 → ℝ) (sigma : Equiv.Perm (Fin 3))
    (hA : ∀ i, 0 < A i) (hrho : ∀ i, 0 < rho i) (x : RealTriple) (i : Fin 3) :
    L ((davenportCoordinates3 L A rho sigma hA hrho).symm x) i =
      A i/rho (sigma i)*x i := by
  have h := congrArg (fun y : RealTriple => y i)
    ((davenportCoordinates3 L A rho sigma hA hrho).apply_symm_apply x)
  dsimp only at h
  rw [davenportCoordinates3_apply] at h
  have hAi := (hA i).ne'
  have hr := (hrho (sigma i)).ne'
  field_simp at h ⊢
  nlinarith

theorem davenportBody3_eq_parallelepiped (L : RealTriple ≃ₗ[ℝ] RealTriple)
    (A rho : Fin 3 → ℝ) (sigma : Equiv.Perm (Fin 3))
    (hA : ∀ i, 0 < A i) (hrho : ∀ i, 0 < rho i) :
    davenportBody3 L A rho sigma =
      parallelepipedBody3 (davenportCoordinates3 L A rho sigma hA hrho) :=
  archBody3_eq_parallelepiped L _ (davenportWidths3_pos A rho sigma hA hrho)

theorem davenportBody3_mem (L : RealTriple ≃ₗ[ℝ] RealTriple)
    (A rho : Fin 3 → ℝ) (sigma : Equiv.Perm (Fin 3))
    (hA : ∀ i, 0 < A i) (hrho : ∀ i, 0 < rho i) (x : RealTriple) :
    x ∈ davenportBody3 L A rho sigma ↔
      ∀ i, rho (sigma i)/A i*|L x i| ≤ 1 := by
  rw [davenportBody3_eq_parallelepiped L A rho sigma hA hrho,mem_parallelepipedBody3_iff]
  change ‖davenportCoordinates3 L A rho sigma hA hrho x‖ ≤ 1 ↔ _
  rw [pi_norm_le_iff_of_nonempty]
  simp only [davenportCoordinates3_apply,Real.norm_eq_abs,abs_mul,
    abs_of_pos (div_pos (hrho _) (hA _))]

theorem davenportWidths3_product (A rho : Fin 3 → ℝ) (sigma : Equiv.Perm (Fin 3))
    (hprod : (∏ i, rho i) = 1) : (∏ i, davenportWidths3 A rho sigma i) = ∏ i, A i := by
  unfold davenportWidths3
  rw [Finset.prod_div_distrib,Equiv.prod_comp,hprod,div_one]

theorem davenportBody3_volume (L : RealTriple ≃ₗ[ℝ] RealTriple)
    (A rho : Fin 3 → ℝ) (sigma : Equiv.Perm (Fin 3))
    (hA : ∀ i, 0 < A i) (hrho : ∀ i, 0 < rho i) (hprod : (∏ i, rho i) = 1) :
    volume.real (davenportBody3 L A rho sigma) = volume.real (archBody3 L A) := by
  rw [davenportBody3,archBody3_volume L _ (davenportWidths3_pos A rho sigma hA hrho),
    archBody3_volume L A hA,davenportWidths3_product A rho sigma hprod]


theorem davenport_plane_pivot_bound3 (n y : Fin 3 → ℝ)
    (hn : n 0*y 0+n 1*y 1+n 2*y 2=0)
    (h0 : |n 0| ≤ |n 2|) (h1 : |n 1| ≤ |n 2|) (h2 : n 2 ≠ 0) :
    |y 2| ≤ |y 0|+|y 1| := by
  have hrel : n 2*y 2 = -(n 0*y 0+n 1*y 1) := by linarith
  have hb : |n 2| * |y 2| ≤ |n 0| * |y 0|+|n 1| * |y 1| := by
    rw [← abs_mul, hrel, abs_neg]
    simpa only [abs_mul] using abs_add_le (n 0*y 0) (n 1*y 1)
  have ha := mul_le_mul_of_nonneg_right h0 (abs_nonneg (y 0))
  have hc := mul_le_mul_of_nonneg_right h1 (abs_nonneg (y 1))
  have hd := abs_pos.mpr h2
  nlinarith

theorem davenport_flag_pivot3 (v : Fin 3 → RealTriple)
    (hv : LinearIndependent ℝ v) :
    ∃ p : Equiv.Perm (Fin 3),
      (∀ x ∈ minimaFlag3 v 1, ‖x‖ ≤ 4*|x (p 0)|) ∧
      (∀ x ∈ minimaFlag3 v 2, ‖x‖ ≤ 2*(|x (p 0)|+|x (p 1)|)) := by
  classical
  let n := crossProduct (v 0) (v 1)
  have hpair : LinearIndependent ℝ ![v 0,v 1] := by
    let f : Fin 2 ↪ Fin 3 := Fin.castLEEmb (Nat.le_succ 2)
    have hi := hv.comp f f.injective
    convert hi using 1
    ext i
    fin_cases i <;> rfl
  have hn : n ≠ 0 := crossProduct_ne_zero_iff_linearIndependent.mpr hpair
  obtain ⟨a, _, ha⟩ := Finset.exists_max_image Finset.univ (fun i => |n i|) Finset.univ_nonempty
  have hna : n a ≠ 0 := by
    intro hzero
    apply hn
    ext i
    have hi := ha i (Finset.mem_univ i)
    simp only [hzero,abs_zero,abs_nonpos_iff] at hi
    exact hi
  let t : Equiv.Perm (Fin 3) := Equiv.swap 2 a
  have ht : t 2=a := by simp [t]
  let p : Equiv.Perm (Fin 3) :=
    if |v 0 (t 1)| ≤ |v 0 (t 0)| then t else (Equiv.swap 0 1).trans t
  have hp2 : p 2=a := by
    dsimp [p]
    split_ifs <;> simp [ht, Equiv.swap_apply_of_ne_of_ne]
  have hp01 : |v 0 (p 1)| ≤ |v 0 (p 0)| := by
    dsimp [p]
    split_ifs with h
    · exact h
    · simpa using (le_of_lt (lt_of_not_ge h))
  have hplane : ∀ x ∈ minimaFlag3 v 2, ∑ i, n i*x i=0 := by
    intro x hx
    let f : RealTriple →ₗ[ℝ] ℝ :=
      { toFun := fun y => dotProduct n y
        map_add' := fun y z => dotProduct_add n y z
        map_smul' := fun c y => by simp [dotProduct_smul] }
    have hsub : minimaFlag3 v 2 ≤ LinearMap.ker f := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      fin_cases i
      · change dotProduct n (v 0)=0
        simpa only [dotProduct_comm] using dot_self_cross (v 0) (v 1)
      · change dotProduct n (v 1)=0
        simpa only [dotProduct_comm] using dot_cross_self (v 0) (v 1)
    exact hsub hx
  have hlast : ∀ x ∈ minimaFlag3 v 2, |x (p 2)| ≤ |x (p 0)|+|x (p 1)| := by
    intro x hx
    apply davenport_plane_pivot_bound3 (n ∘ p) (x ∘ p)
    · have hh := hplane x hx
      rw [← Equiv.sum_comp p (fun i => n i*x i), Fin.sum_univ_three] at hh
      exact hh
    · simpa only [Function.comp_apply,hp2] using ha (p 0) (Finset.mem_univ _)
    · simpa only [Function.comp_apply,hp2] using ha (p 1) (Finset.mem_univ _)
    · simpa only [Function.comp_apply,hp2] using hna
  have hnorm : ∀ x : RealTriple, ‖x‖ ≤ |x (p 0)|+|x (p 1)|+|x (p 2)| := by
    intro x
    apply (pi_norm_le_iff_of_nonempty x).mpr
    intro i
    have hi : |x i| ≤ ∑ j, |x j| := Finset.single_le_sum (fun j _ => abs_nonneg (x j)) (Finset.mem_univ i)
    rw [← Equiv.sum_comp p (fun j => |x j|), Fin.sum_univ_three] at hi
    exact hi
  refine ⟨p, ?_, ?_⟩
  · intro x hx
    have hx2 : x ∈ minimaFlag3 v 2 := by
      apply (show minimaFlag3 v 1 ≤ minimaFlag3 v 2 from ?_) hx
      apply Submodule.span_mono
      rintro _ ⟨i, rfl⟩
      refine ⟨⟨i.val, by omega⟩, rfl⟩
    have hxline : x ∈ Submodule.span ℝ {v 0} := by
      simpa [minimaFlag3, Set.range_unique] using hx
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hxline
    have hh : |(c • v 0) (p 1)| ≤ |(c • v 0) (p 0)| := by
      simpa only [Pi.smul_apply,smul_eq_mul,abs_mul] using
        mul_le_mul_of_nonneg_left hp01 (abs_nonneg c)
    have hl := hlast (c • v 0) hx2
    have hb := hnorm (c • v 0)
    linarith
  · intro x hx
    have hl := hlast x hx
    have hb := hnorm x
    linarith


theorem davenport_original_off_flag3 (b : Basis (Fin 3) ℝ RealTriple)
    (e : RealTriple ≃ₗ[ℝ] RealTriple) (v : Fin 3 → RealTriple)
    (hv : LinearIndependent ℝ v) (hvL : ∀ i, v i ∈ lattice3 b)
    (hvr : ∀ i, coordinateGauge3 e (v i) = successiveRadius3 b e i)
    (j : Fin 3) (x : RealTriple) (hx : x ∈ lattice3 b)
    (houtside : x ∉ minimaFlag3 v j) :
    successiveRadius3 b e j ≤ coordinateGauge3 e x := by
  classical
  let s := Finset.univ.filter (fun i => successiveRadius3 b e i = successiveRadius3 b e j)
  have hjs : j ∈ s := by simp [s]
  obtain ⟨r, hrs, hmin⟩ := Finset.exists_min_image s Fin.val ⟨j, hjs⟩
  have hr : successiveRadius3 b e r = successiveRadius3 b e j := (Finset.mem_filter.mp hrs).2
  have hrj : r ≤ j := hmin j hjs
  have hgap : ∀ i : Fin 3, i < r → successiveRadius3 b e i < successiveRadius3 b e r := by
    intro i hir
    have hle := successiveRadius3_monotone b e (le_of_lt hir)
    apply lt_of_le_of_ne hle
    intro heq
    have his : i ∈ s := by simp [s, heq, hr]
    have hri := hmin i his
    exact (not_le_of_gt hir) hri
  have hflag : minimaFlag3 v r ≤ minimaFlag3 v j := by
    apply Submodule.span_mono
    rintro _ ⟨i, rfl⟩
    refine ⟨⟨i.val, lt_of_lt_of_le i.isLt hrj⟩, ?_⟩
    rfl
  by_contra h
  have hshort : coordinateGauge3 e x < successiveRadius3 b e r := by
    rw [hr]
    exact lt_of_not_ge h
  exact houtside (hflag (lattice3_short_mem_minimaFlag b e v hv hvL hvr r hgap x hx hshort))



theorem davenport_flag_map3 (e : RealTriple ≃ₗ[ℝ] RealTriple)
    (v : Fin 3 → RealTriple) (j : Fin 3) (x : RealTriple)
    (hx : x ∈ minimaFlag3 v j) : e x ∈ minimaFlag3 (e ∘ v) j := by
  have hs : (minimaFlag3 v j).map e.toLinearMap = minimaFlag3 (e ∘ v) j := by
    simp only [minimaFlag3,Submodule.map_span,← Set.range_comp,Function.comp_def]
    rfl
  rw [← hs]
  exact Submodule.mem_map.mpr ⟨x,hx,rfl⟩

theorem davenport_flag_mono3 (v : Fin 3 → RealTriple) {i j : Fin 3} (h : i ≤ j) :
    minimaFlag3 v i ≤ minimaFlag3 v j := by
  apply Submodule.span_mono
  rintro _ ⟨k,rfl⟩
  exact ⟨⟨k.val,lt_of_lt_of_le k.isLt h⟩,rfl⟩

theorem davenport_off_span3 (b : Basis (Fin 3) ℝ RealTriple)
    (L : RealTriple ≃ₗ[ℝ] RealTriple) (A rho : Fin 3 → ℝ)
    (hA : ∀ i, 0 < A i) (hrho : ∀ i, 0 < rho i)
    (hr01 : rho 1 ≤ rho 0) (hr12 : rho 2 ≤ rho 1)
    (v : Fin 3 → RealTriple) (hv : LinearIndependent ℝ v)
    (hvL : ∀ i, v i ∈ lattice3 b)
    (hvr : ∀ i, coordinateGauge3 (archCoordinates3 L A hA) (v i) =
      successiveRadius3 b (archCoordinates3 L A hA) i)
    (hm01 : rho 0*successiveRadius3 b (archCoordinates3 L A hA) 0 ≤
      rho 1*successiveRadius3 b (archCoordinates3 L A hA) 1)
    (hm12 : rho 1*successiveRadius3 b (archCoordinates3 L A hA) 1 ≤
      rho 2*successiveRadius3 b (archCoordinates3 L A hA) 2) :
    ∃ sigma : Equiv.Perm (Fin 3), ∀ j : Fin 3, ∀ x ∈ lattice3 b,
      x ∉ minimaFlag3 v j →
      rho j*successiveRadius3 b (archCoordinates3 L A hA) j/8 ≤
        coordinateGauge3 (davenportCoordinates3 L A rho sigma hA hrho) x := by
  let e := archCoordinates3 L A hA
  have he : LinearIndependent ℝ (e ∘ v) := hv.map' e.toLinearMap (LinearMap.ker_eq_bot.mpr e.injective)
  obtain ⟨p,hline,hplane⟩ := davenport_flag_pivot3 (e ∘ v) he
  refine ⟨p.symm, ?_⟩
  intro j x hx hout
  let g := coordinateGauge3 (davenportCoordinates3 L A rho p.symm hA hrho) x
  have hg : 0 ≤ g := norm_nonneg _
  have hc : ∀ i, rho i*|e x (p i)| ≤ g := by
    intro i
    have hb := norm_le_pi_norm (davenportCoordinates3 L A rho p.symm hA hrho x) (p i)
    rw [Real.norm_eq_abs,davenportCoordinates3_apply,abs_mul,
      abs_of_pos (div_pos (hrho _) (hA _)), p.symm_apply_apply] at hb
    change rho i*|L x (p i)/A (p i)| ≤ g
    rw [abs_div,abs_of_pos (hA _)]
    convert hb using 1 <;> ring
  have hlower (k : Fin 3) (hk : x ∉ minimaFlag3 v k) :
      successiveRadius3 b e k ≤ ‖e x‖ :=
    davenport_original_off_flag3 b e v hv hvL hvr k x hx hk
  have hzero : minimaFlag3 v 0 = ⊥ := by simp [minimaFlag3]
  have hnonzero : x ∉ minimaFlag3 v 0 := by
    intro hz
    exact hout (davenport_flag_mono3 v (by omega : (0 : Fin 3) ≤ j) hz)
  have hsmall : x ∈ minimaFlag3 v 1 → rho 0*successiveRadius3 b e 0 ≤ 4*g := by
    intro h
    have hh := hline (e x) (davenport_flag_map3 e v 1 x h)
    have hn := mul_le_mul_of_nonneg_left (hlower 0 hnonzero) (le_of_lt (hrho 0))
    have hw := mul_le_mul_of_nonneg_left hh (le_of_lt (hrho 0))
    have hp := hc 0
    nlinarith
  have hmiddle : x ∈ minimaFlag3 v 2 → x ∉ minimaFlag3 v 1 →
      rho 1*successiveRadius3 b e 1 ≤ 4*g := by
    intro h hnot
    have hh := hplane (e x) (davenport_flag_map3 e v 2 x h)
    have hn := mul_le_mul_of_nonneg_left (hlower 1 hnot) (le_of_lt (hrho 1))
    have hw := mul_le_mul_of_nonneg_left hh (le_of_lt (hrho 1))
    have hp0 := (mul_le_mul_of_nonneg_right hr01 (abs_nonneg (e x (p 0)))).trans (hc 0)
    have hp1 := hc 1
    nlinarith
  have hlarge : x ∉ minimaFlag3 v 2 → rho 2*successiveRadius3 b e 2 ≤ g := by
    intro hnot
    have hnorm : ‖e x‖ ≤ g/rho 2 := by
      apply (pi_norm_le_iff_of_nonempty (e x)).mpr
      intro i
      rw [Real.norm_eq_abs,le_div_iff₀ (hrho 2)]
      have hrall : ∀ k : Fin 3, rho 2 ≤ rho k := by
        intro k
        fin_cases k
        · exact hr12.trans hr01
        · exact hr12
        · exact le_rfl
      have hr := hrall (p.symm i)
      have hb := (mul_le_mul_of_nonneg_right hr (abs_nonneg (e x i))).trans (by simpa using hc (p.symm i))
      simpa [mul_comm] using hb
    have hn := (hlower 2 hnot).trans hnorm
    simpa only [mul_comm] using (le_div_iff₀ (hrho 2)).mp hn
  fin_cases j
  · by_cases h1 : x ∈ minimaFlag3 v 1
    · have hh := hsmall h1
      change rho 0*successiveRadius3 b e 0/8 ≤ g
      linarith
    · by_cases h2 : x ∈ minimaFlag3 v 2
      · have hh := hmiddle h2 h1
        change rho 0*successiveRadius3 b e 0/8 ≤ g
        linarith
      · have hh := hlarge h2
        change rho 0*successiveRadius3 b e 0/8 ≤ g
        linarith
  · by_cases h2 : x ∈ minimaFlag3 v 2
    · have hh := hmiddle h2 hout
      change rho 1*successiveRadius3 b e 1/8 ≤ g
      linarith
    · have hh := hlarge h2
      change rho 1*successiveRadius3 b e 1/8 ≤ g
      linarith
  · have hh := hlarge hout
    change rho 2*successiveRadius3 b e 2/8 ≤ g
    linarith


theorem davenport_independent_outside_flag3 (v : Fin 3 → RealTriple)
    (hv : LinearIndependent ℝ v) (j : Fin 3)
    (u : Fin (j.val+1) → RealTriple) (hu : LinearIndependent ℝ u) :
    ∃ i, u i ∉ minimaFlag3 v j := by
  by_contra h
  push_neg at h
  let w : Fin (j.val+1) → minimaFlag3 v j := fun i => ⟨u i,h i⟩
  have hw : LinearIndependent ℝ w := hu.of_comp (minimaFlag3 v j).subtype
  have hd := hw.fintype_card_le_finrank
  rw [Fintype.card_fin,minimaFlag3_finrank v hv j] at hd
  omega

theorem davenport_minima_lower3 (b : Basis (Fin 3) ℝ RealTriple)
    (e' : RealTriple ≃ₗ[ℝ] RealTriple) (v : Fin 3 → RealTriple)
    (hv : LinearIndependent ℝ v) (s : Fin 3 → ℝ)
    (hsep : ∀ j, ∀ x ∈ lattice3 b, x ∉ minimaFlag3 v j → s j ≤ coordinateGauge3 e' x)
    (j : Fin 3) : s j ≤ successiveRadius3 b e' j := by
  obtain ⟨u,hu,huL,_,_,hur⟩ := exists_successive_minima3 b e'
  let f : Fin (j.val+1) → Fin 3 := Fin.castLE (by omega)
  have hf : Function.Injective f := Fin.castLE_injective _
  obtain ⟨i,hi⟩ := davenport_independent_outside_flag3 v hv j (u ∘ f) (hu.comp f hf)
  have hh := hsep j (u (f i)) (huL (f i)) hi
  rw [hur] at hh
  exact hh.trans (successiveRadius3_monotone b e' (by change i.val ≤ j.val; omega))

theorem davenport_minima_product3 (b : Basis (Fin 3) ℝ RealTriple)
    (L : RealTriple ≃ₗ[ℝ] RealTriple) (A rho : Fin 3 → ℝ)
    (sigma : Equiv.Perm (Fin 3)) (hA : ∀ i, 0 < A i) (hrho : ∀ i, 0 < rho i)
    (hprod : (∏ i,rho i)=1) :
    (∏ i, successiveRadius3 b (davenportCoordinates3 L A rho sigma hA hrho) i) ≤
      6*∏ i, successiveRadius3 b (archCoordinates3 L A hA) i := by
  let e := archCoordinates3 L A hA
  let e' := davenportCoordinates3 L A rho sigma hA hrho
  have heq : volume.real (parallelepipedBody3 e') = volume.real (parallelepipedBody3 e) := by
    rw [← davenportBody3_eq_parallelepiped L A rho sigma hA hrho,
      ← archBody3_eq_parallelepiped L A hA]
    exact davenportBody3_volume L A rho sigma hA hrho hprod
  have hv : 0 < volume.real (parallelepipedBody3 e) := by
    rw [parallelepipedBody3_volume]
    exact div_pos (by norm_num) (abs_pos.mpr e.isUnit_det'.ne_zero)
  have hl := successive_minima3_parallelepiped_volume_lower b e
  have hu := successive_minima3_parallelepiped_volume_upper b e'
  rw [heq] at hu
  apply (mul_le_mul_right hv).mp
  nlinarith

theorem davenport_three_ratios_bound3 (r : Fin 3 → ℝ)
    (hr : ∀ i, (1:ℝ)/8 ≤ r i) (hprod : (∏ i,r i) ≤ 6) (i : Fin 3) :
    r i ≤ 384 := by
  have h0 := hr 0
  have h1 := hr 1
  have h2 := hr 2
  rw [Fin.prod_univ_three] at hprod
  have hb12 : (1:ℝ)/64 ≤ r 1*r 2 := by nlinarith [mul_nonneg (by linarith : 0 ≤ r 1-1/8) (by linarith : 0 ≤ r 2-1/8)]
  have hb02 : (1:ℝ)/64 ≤ r 0*r 2 := by nlinarith [mul_nonneg (by linarith : 0 ≤ r 0-1/8) (by linarith : 0 ≤ r 2-1/8)]
  have hb01 : (1:ℝ)/64 ≤ r 0*r 1 := by nlinarith [mul_nonneg (by linarith : 0 ≤ r 0-1/8) (by linarith : 0 ≤ r 1-1/8)]
  fin_cases i
  · change r 0 ≤ 384
    have h := mul_le_mul_of_nonneg_left hb12 (by linarith : 0 ≤ r 0)
    nlinarith
  · change r 1 ≤ 384
    have h := mul_le_mul_of_nonneg_left hb02 (by linarith : 0 ≤ r 1)
    nlinarith
  · change r 2 ≤ 384
    have h := mul_le_mul_of_nonneg_left hb01 (by linarith : 0 ≤ r 2)
    nlinarith


theorem davenport_lemma3 (b : Basis (Fin 3) ℝ RealTriple)
    (L : RealTriple ≃ₗ[ℝ] RealTriple) (A rho : Fin 3 → ℝ)
    (hA : ∀ i, 0 < A i) (hrho : ∀ i, 0 < rho i)
    (hprod : (∏ i,rho i)=1) (hr01 : rho 1 ≤ rho 0) (hr12 : rho 2 ≤ rho 1)
    (v : Fin 3 → RealTriple) (hv : LinearIndependent ℝ v)
    (hvL : ∀ i, v i ∈ lattice3 b)
    (hvr : ∀ i, coordinateGauge3 (archCoordinates3 L A hA) (v i) =
      successiveRadius3 b (archCoordinates3 L A hA) i)
    (hm01 : rho 0*successiveRadius3 b (archCoordinates3 L A hA) 0 ≤
      rho 1*successiveRadius3 b (archCoordinates3 L A hA) 1)
    (hm12 : rho 1*successiveRadius3 b (archCoordinates3 L A hA) 1 ≤
      rho 2*successiveRadius3 b (archCoordinates3 L A hA) 2) :
    ∃ sigma : Equiv.Perm (Fin 3),
      (∀ j, rho j*successiveRadius3 b (archCoordinates3 L A hA) j/8 ≤
        successiveRadius3 b (davenportCoordinates3 L A rho sigma hA hrho) j ∧
        successiveRadius3 b (davenportCoordinates3 L A rho sigma hA hrho) j ≤
          3072*(rho j*successiveRadius3 b (archCoordinates3 L A hA) j)) ∧
      ∀ j : Fin 3, ∀ x ∈ lattice3 b, x ∉ minimaFlag3 v j →
        rho j*successiveRadius3 b (archCoordinates3 L A hA) j/8 ≤
          coordinateGauge3 (davenportCoordinates3 L A rho sigma hA hrho) x := by
  obtain ⟨sigma,hsep⟩ := davenport_off_span3 b L A rho hA hrho hr01 hr12 v hv hvL hvr hm01 hm12
  refine ⟨sigma,?_,hsep⟩
  let e := archCoordinates3 L A hA
  let e' := davenportCoordinates3 L A rho sigma hA hrho
  let a : Fin 3 → ℝ := fun i => rho i*successiveRadius3 b e i
  let r : Fin 3 → ℝ := fun i => successiveRadius3 b e' i/a i
  obtain ⟨_,_,_,hpos,_,_⟩ := exists_successive_minima3 b e
  have ha : ∀ i, 0 < a i := fun i => mul_pos (hrho i) (hpos i)
  have hl : ∀ i, a i/8 ≤ successiveRadius3 b e' i := fun i =>
    davenport_minima_lower3 b e' v hv (fun j => a j/8) hsep i
  have hr : ∀ i, (1:ℝ)/8 ≤ r i := by
    intro i
    apply (le_div_iff₀ (ha i)).mpr
    nlinarith [hl i]
  have hpa : (∏ i,a i) = ∏ i,successiveRadius3 b e i := by
    simp only [a,Finset.prod_mul_distrib,hprod,one_mul]
  have hpr : (∏ i,r i) ≤ 6 := by
    simp only [r,Finset.prod_div_distrib]
    apply (div_le_iff₀ (Finset.prod_pos (fun i _ => ha i))).mpr
    rw [hpa]
    exact davenport_minima_product3 b L A rho sigma hA hrho hprod
  intro i
  refine ⟨hl i,?_⟩
  have hb := davenport_three_ratios_bound3 r hr hpr i
  have hc : successiveRadius3 b e' i ≤ 384*a i := (div_le_iff₀ (ha i)).mp hb
  change successiveRadius3 b e' i ≤ 3072*a i
  nlinarith [ha i]


theorem source_davenport_lemma3 (k₂ k₃ : Fin 3) (f₂ f₃ : Fin 3 → ℤ)
    (L : RealTriple ≃ₗ[ℝ] RealTriple) (A rho : Fin 3 → ℝ)
    (hA : ∀ i, 0 < A i) (hrho : ∀ i, 0 < rho i)
    (hprod : (∏ i,rho i)=1) (hr01 : rho 1 ≤ rho 0) (hr12 : rho 2 ≤ rho 1)
    (B : Basis (Fin 3) ℝ RealTriple) (u : Fin 3 → sourceIntegralLattice3 k₂ k₃ f₂ f₃)
    (hB : lattice3 B = (sourceIntegralLattice3 k₂ k₃ f₂ f₃).toIntSubmodule.map integerTripleReal3)
    (hu : LinearIndependent ℝ (fun j => integerTripleReal3 (u j : IntegerTriple)))
    (hatt : ∀ j, coordinateGauge3 (archCoordinates3 L A hA) (integerTripleReal3 (u j : IntegerTriple)) =
      successiveRadius3 B (archCoordinates3 L A hA) j)
    (hm01 : rho 0*successiveRadius3 B (archCoordinates3 L A hA) 0 ≤
      rho 1*successiveRadius3 B (archCoordinates3 L A hA) 1)
    (hm12 : rho 1*successiveRadius3 B (archCoordinates3 L A hA) 1 ≤
      rho 2*successiveRadius3 B (archCoordinates3 L A hA) 2) :
    dualFrameRelativeIndex3 (sourceIntegralLattice3 k₂ k₃ f₂ f₃) u ≤ 6 ∧
    ∃ sigma : Equiv.Perm (Fin 3),
      (∀ j, rho j*successiveRadius3 B (archCoordinates3 L A hA) j/8 ≤
        successiveRadius3 B (davenportCoordinates3 L A rho sigma hA hrho) j ∧
        successiveRadius3 B (davenportCoordinates3 L A rho sigma hA hrho) j ≤
          3072*(rho j*successiveRadius3 B (archCoordinates3 L A hA) j)) ∧
      ∀ j : Fin 3, ∀ z : sourceIntegralLattice3 k₂ k₃ f₂ f₃,
        integerTripleReal3 (z : IntegerTriple) ∉
          minimaFlag3 (fun k => integerTripleReal3 (u k : IntegerTriple)) j →
        rho j*successiveRadius3 B (archCoordinates3 L A hA) j/8 ≤
          coordinateGauge3 (davenportCoordinates3 L A rho sigma hA hrho)
            (integerTripleReal3 (z : IntegerTriple)) := by
  refine ⟨source_attaining_frame_index_le_six3 _ B _ u hB hu hatt,?_⟩
  have hmem (z : sourceIntegralLattice3 k₂ k₃ f₂ f₃) :
      integerTripleReal3 (z : IntegerTriple) ∈ lattice3 B := by
    rw [hB]
    exact Submodule.mem_map.mpr ⟨(z : IntegerTriple),z.property,rfl⟩
  obtain ⟨sigma,hbounds,hsep⟩ := davenport_lemma3 B L A rho hA hrho hprod hr01 hr12
    (fun j => integerTripleReal3 (u j : IntegerTriple)) hu (fun j => hmem (u j)) hatt hm01 hm12
  exact ⟨sigma,hbounds,fun j z hz => hsep j _ (hmem z) hz⟩


theorem davenportBody3_compact_convex (L : RealTriple ≃ₗ[ℝ] RealTriple)
    (A rho : Fin 3 → ℝ) (sigma : Equiv.Perm (Fin 3))
    (hA : ∀ i, 0 < A i) (hrho : ∀ i, 0 < rho i) :
    IsCompact (davenportBody3 L A rho sigma) ∧ Convex ℝ (davenportBody3 L A rho sigma) := by
  rw [davenportBody3_eq_parallelepiped L A rho sigma hA hrho]
  exact parallelepipedBody3_compact_convex _

end JSP000334
