import SubspaceBridge.SourceFixedBody235
import SubspaceBridge.SourceShortLine226
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceFixedGeometry235
open SourceFixedArithmetic234 SourceOriginalDual10 OriginalDual10 SourceSatz51Entry218
  SourceDualGeometry219 SourceDualAnnihilation222 SourceSecondMinimum226 SourceCofactorGeometry233

theorem rescaled_rational_line235 (v : Fin 10 → ℤ) (hv : v ≠ 0) (t : ℤ) (ht : t ≠ 0) :
    let z : Fin 10 → ℚ := fun i => ((t • v) i : ℚ)
    z ≠ 0 ∧ Submodule.span ℚ {fun i => (v i : ℚ)} = Submodule.span ℚ {z} := by
  intro z
  have he : z = (t : ℚ) • (fun i => (v i : ℚ)) := by
    funext i
    simp only [z,Pi.smul_apply,smul_eq_mul,Int.cast_mul]
  have hvQ : (fun i => (v i : ℚ)) ≠ 0 := by
    intro h
    apply hv
    funext i
    have hi := congrFun h i
    simp only [Pi.zero_apply] at hi
    change v i = 0
    exact_mod_cast hi
  have htQ : (t : ℚ) ≠ 0 := by exact_mod_cast ht
  rw [he]
  exact ⟨smul_ne_zero htQ hvQ,
    (Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr htQ) _).symm⟩

theorem short_body_line235 (delta : ℝ) (hd : 0 < delta) :
    ∃ T : ℝ, 1 < T ∧ ∀ (A2 A3 : Matrix (Fin 10) (Fin 10) ℚ)
      (L : Matrix (Fin 10) (Fin 10) ℝ) (hL : IsUnit L) (q : ℝ), T < q →
      ∀ (hq : 1 < q) (c2 c3 A : Fin 10 → ℝ)
        (D : SourceData218 A2 A3 L hL q hq c2 c3 A delta) (z : Fin 10 → ℚ),
        z ≠ 0 → z ∈ scaledDual219 (originalSourceGroup10 A2 A3 q c2 c3) →
        ratReal222 z ∈ dualBody222 L
          (ZLattice.covolume (integerRealImage (originalSourceGroup10 A2 A3 q c2 c3))) A →
        Submodule.span ℚ {z} = Submodule.span ℚ
          {lastDual10 (fun j i => (D.u j i : ℚ))
            (integer_frame_rational_independent10 D.u D.independent)} := by
  obtain ⟨T,hT,hline⟩ := source_short_line226 delta hd
  refine ⟨T,hT,?_⟩
  intro A2 A3 L hL q hqT hq c2 c3 A D z hz hm hb
  have hg := (dualBody_gauge222 L hL _ (ZLattice.covolume_pos _ MeasureTheory.volume)
    A D.positive (ratReal222 z)).mp hb
  have hl := hline A2 A3 L hL q hqT hq c2 c3 A D z hm (hg.trans (by norm_num))
  obtain ⟨a,ha⟩ := Submodule.mem_span_singleton.mp hl
  have hn : a ≠ 0 := by
    intro he
    apply hz
    rw [← ha,he,zero_smul]
  calc
    _ = Submodule.span ℚ {fun i => (integerLastDual10 D.u i : ℚ)} := by
      rw [← ha,Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr hn)]
    _ = _ := source_cofactor_line233 D

open SourceFixedArithmetic234 SourceOriginalDual10 OriginalDual10 SourceSatz51Entry218
  SourceSelectedUpper10 SourceDualGeometry219 SourceDualAnnihilation222

theorem source_fixed_line235
    (A2 A3 : Matrix (Fin 10) (Fin 10) ℚ) (L : Matrix (Fin 10) (Fin 10) ℝ)
    (h2d : A2.det = 1) (h3d : A3.det = 1) (hLd : L.det = 1) (hL : IsUnit L)
    (hAlg : ∀ i j, IsAlgebraic ℚ (L i j)) (c2 c3 : Fin 10 → ℝ)
    (h2 : ∀ i, -1 ≤ c2 i ∧ c2 i ≤ 0) (h3 : ∀ i, -1 ≤ c3 i ∧ c3 i ≤ 0)
    (delta : ℝ) (hd : 0 < delta) (Omega : Set ℝ) (hO : ¬ BddAbove Omega)
    (hq : ∀ q ∈ Omega, 1 < q) (A : ℝ → Fin 10 → ℝ)
    (D : ∀ q : Omega, SourceData218 A2 A3 L hL q.val (hq q.val q.property) c2 c3 (A q.val) delta) :
    let hA2 : IsUnit A2 := (Matrix.isUnit_iff_isUnit_det A2).mpr (by rw [h2d]; exact isUnit_one)
    let hA3 : IsUnit A3 := (Matrix.isUnit_iff_isUnit_det A3).mpr (by rw [h3d]; exact isUnit_one)
    ∃ S0 : Finset (Fin 3 → Fin 10), S0.Nonempty ∧ ∃ B : ℝ, 6 < B ∧
      ∃ U : Set ℝ, U ⊆ Omega ∧ ¬ BddAbove U ∧
        ∃ q1 : Omega, q1.val ∈ U ∧ B < q1.val ∧
          ∃ (v0 : Fin 10 → ℤ) (hv0 : v0 ≠ 0), v0 = integerLastDual10 (D q1).u ∧
            (∀ s ∈ S0, mixedProduct10 A2 A3 L v0 s = 0) ∧
            ∃ C : ℤ, 0 < C ∧ ∃ t : ℝ → ℤ,
              (∀ q, t q = C*2^((9-floorMin234 2 A2 hA2 q c2 v0 hv0).toNat)*
                3^((9-floorMin234 3 A3 hA3 q c3 v0 hv0).toNat)) ∧
              ∃ T : ℝ, 1 < T ∧ B ≤ T ∧ ∃ V : Set ℝ,
                V = {q | q ∈ U ∧ T < q} ∧ V ⊆ Omega ∧ ¬ BddAbove V ∧
                  ∀ q : Omega, q.val ∈ V → sourceSet218 q.val delta (A q.val) c2 c3 = S0 ∧
                    let z : Fin 10 → ℚ := fun i => (((t q.val) • v0) i : ℚ)
                    z ≠ 0 ∧ 0 < t q.val ∧
                      z ∈ scaledDual219 (originalSourceGroup10 A2 A3 q.val c2 c3) ∧
                      ratReal222 z ∈ dualBody222 L
                        (ZLattice.covolume (integerRealImage (originalSourceGroup10 A2 A3 q.val c2 c3))) (A q.val) ∧
                      Submodule.span ℚ {fun i => (v0 i : ℚ)} = Submodule.span ℚ
                        {lastDual10 (fun j i => ((D q).u j i : ℚ))
                          (integer_frame_rational_independent10 (D q).u (D q).independent)} := by
  intro hA2 hA3
  obtain ⟨S0,hS0,B,hB,U,hUO,hU,q1,hq1U,hq1B,v0,hv0,hveq,hzero,hpattern,C,hC,t,ht,hm⟩ :=
    source_fixed_membership234 A2 A3 L h2d h3d hLd hL hAlg c2 c3 h2 h3
      delta hd Omega hO hq A D
  let a : Fin 10 → ℝ := fun i => (L⁻¹.transpose *ᵥ integerReal v0) i
  let H : ℝ := 1+∑ i, |a i|
  let K0 : ℝ := (C : ℝ)*2^10*3^10*H
  have hK0 : 0 < K0 := mul_pos (by positivity) (coefficient_bound235 a).1
  obtain ⟨Tb,hTb,hbodycut⟩ := fixed_cutoff235 delta hd K0 hK0
  obtain ⟨Tl,_,hline⟩ := short_body_line235 delta hd
  let T := max B (max Tb Tl)
  let V : Set ℝ := {q | q ∈ U ∧ T < q}
  have hBT : B ≤ T := le_max_left _ _
  have hTbT : Tb ≤ T := (le_max_left Tb Tl).trans (le_max_right B _)
  have hTlT : Tl ≤ T := (le_max_right Tb Tl).trans (le_max_right B _)
  have hV : ¬ BddAbove V := by
    rintro ⟨b,hb⟩
    obtain ⟨q,hqU,hqgt⟩ := not_bddAbove_iff.mp hU (max T b)
    exact (not_le_of_gt ((le_max_right T b).trans_lt hqgt))
      (hb ⟨hqU,(le_max_left T b).trans_lt hqgt⟩)
  refine ⟨S0,hS0,B,hB,U,hUO,hU,q1,hq1U,hq1B,v0,hv0,hveq,hzero,C,hC,t,ht,
    T,hTb.trans_le hTbT,hBT,V,rfl,fun _ h => hUO h.1,hV,?_⟩
  intro q hqV
  have hqB : B < q.val := hBT.trans_lt hqV.2
  have hpat := hpattern q hqV.1
  have hmem := hm q.val hqV.1 hqB
  have hpos : 0 < t q.val := by rw [ht]; exact positive_scale235 C hC _ _
  have hn := rescaled_rational_line235 v0 hv0 (t q.val) hmem.1
  have hb := fixed_body235 h2d h3d hA2 hA3 (fun i => (h2 i).2) (fun i => (h3 i).2)
    (D q) S0 hpat v0 hv0 hzero C hC (t q.val) (ht q.val)
    (hbodycut q.val (hTbT.trans_lt hqV.2))
  have hl := hline A2 A3 L hL q.val (hTlT.trans_lt hqV.2) (hq q.val q.property)
    c2 c3 (A q.val) (D q) _ hn.1 hmem.2 hb
  exact ⟨hpat,hn.1,hpos,hmem.2,hb,hn.2.trans hl⟩

end CompoundFeasibility.SourceFixedGeometry235
