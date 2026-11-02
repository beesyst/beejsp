import SubspaceBridge.SourceFlagLine236
import SubspaceBridge.SourcePowerDomain236
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceRatioLine236
open OriginalDeformation10 SourceOriginalVariable10 SourceSatz51Entry218
  OriginalDual10 SourceOriginalDual10 SourceFixedGeometry235

def sourceData_transport236
    {A2 A3 : Matrix (Fin 10) (Fin 10) ℚ} {L : Matrix (Fin 10) (Fin 10) ℝ}
    {hL : IsUnit L} {q r : ℝ} {hq : 1 < q} {hr : 1 < r} {c2 c3 A B : Fin 10 → ℝ} {delta : ℝ}
    (he : q = r) (hA : A = B) (D : SourceData218 A2 A3 L hL q hq c2 c3 A delta) :
    SourceData218 A2 A3 L hL r hr c2 c3 B delta := by
  subst r
  subst B
  exact D

theorem sourceData_transport_frame236
    {A2 A3 : Matrix (Fin 10) (Fin 10) ℚ} {L : Matrix (Fin 10) (Fin 10) ℝ}
    {hL : IsUnit L} {q r : ℝ} {hq : 1 < q} {hr : 1 < r} {c2 c3 A B : Fin 10 → ℝ} {delta : ℝ}
    (he : q = r) (hA : A = B) (D : SourceData218 A2 A3 L hL q hq c2 c3 A delta) :
    (sourceData_transport236 (hr := hr) he hA D).u = D.u := by
  subst r
  subst B
  rfl

theorem lastDual_frame_eq236 (u w : Fin 10 → Fin 10 → ℤ)
    (hu : LinearIndependent ℚ (fun j i => (u j i : ℚ)))
    (hw : LinearIndependent ℚ (fun j i => (w j i : ℚ))) (he : u = w) :
    lastDual10 (fun j i => (u j i : ℚ)) hu = lastDual10 (fun j i => (w j i : ℚ)) hw := by
  subst w
  rfl

theorem source_ratio_fixed_line236
    (A2 A3 : Matrix (Fin 10) (Fin 10) ℚ) (L : Matrix (Fin 10) (Fin 10) ℝ)
    (h2d : A2.det = 1) (h3d : A3.det = 1) (hLd : L.det = 1) (hL : IsUnit L)
    (hAlg : ∀ i j, IsAlgebraic ℚ (L i j)) (c0 c2 c3 : Fin 10 → ℝ)
    (hc0 : ∀ i, |c0 i| ≤ 1)
    (hc2 : ∀ i, -1 ≤ c2 i ∧ c2 i ≤ 0) (hc3 : ∀ i, -1 ≤ c3 i ∧ c3 i ≤ 0)
    (hb : (∑ i, (c0 i+c2 i+c3 i)) = 0)
    (delta : ℝ) (hd : 0 < delta) (Omega : Set ℝ) (hO : ¬ BddAbove Omega)
    (hq : ∀ q ∈ Omega, 1 < q)
    (u : ∀ q : Omega, Fin 10 → originalSourceGroup10 A2 A3 q.val c2 c3)
    (hu : ∀ q : Omega, LinearIndependent ℝ (fun j => integerReal (u q j : Fin 10 → ℤ)))
    (hatt : ∀ (q : Omega) j, coordinateGauge10
      (originalCoordinates10 L hL q.val (hq q.val q.property) c0)
      (integerReal (u q j : Fin 10 → ℤ)) =
        sourceMinima10 A2 A3 L hL q.val (hq q.val q.property) c0 c2 c3 j)
    (hgap : ∀ q : Omega, sourceMinima10 A2 A3 L hL q.val (hq q.val q.property) c0 c2 c3 8 <
      sourceMinima10 A2 A3 L hL q.val (hq q.val q.property) c0 c2 c3 9*q.val^(-delta)) :
    ∃ b : Fin 10 → ℤ, b ≠ 0 ∧ ∃ V : Set ℝ, V ⊆ Omega ∧ ¬ BddAbove V ∧
      ∀ q : Omega, q.val ∈ V →
        Submodule.span ℚ {lastDual10 (fun j i => ((u q j : Fin 10 → ℤ) i : ℚ))
          (integer_frame_rational_independent10 _ (hu q))} =
        Submodule.span ℚ {fun i => (b i : ℚ)} := by
  have h2 : IsUnit A2 := (Matrix.isUnit_iff_isUnit_det A2).mpr (by rw [h2d]; exact isUnit_one)
  have h3 : IsUnit A3 := (Matrix.isUnit_iff_isUnit_det A3).mpr (by rw [h3d]; exact isUnit_one)
  obtain ⟨Td,hTd,hready⟩ := source_uniform_deformation10 A2 A3 L h2 h3 hL delta hd
  obtain ⟨Tf,hTf,hflagcut⟩ := flag_cutoff236 delta hd
  let B := max Td Tf
  have hB : 1 < B := hTd.trans_le (le_max_left _ _)
  let P := powerDomain236 Omega B
  have hP : ¬ BddAbove P := powerDomain_unbounded236 Omega hO B
  obtain ⟨lift,hlift⟩ := exists_power_section236 Omega B
  let orig (p : P) : Omega := ⟨(lift p).val,(lift p).property.1⟩
  have horigB (p : P) : B < (orig p).val := (lift p).property.2
  have hpow (p : P) : (orig p).val^5 = p.val := hlift p
  have hpq (p : ℝ) (hp : p ∈ P) : 1 < p := by
    have he : (orig ⟨p,hp⟩).val^5 = p := hpow ⟨p,hp⟩
    exact he ▸ powered_gt_one236 _ (hq _ (orig ⟨p,hp⟩).property)
  have hF (p : P) : Nonempty (DeformedAttaining236 A2 A3 L hL (orig p).val
      (hq _ (orig p).property) c0 c2 c3 delta (u (orig p))) := by
    apply attaining_of_ready236
    exact hready _ _ c0 c2 c3 hc0 hc2 hc3 hb
      ((le_max_left Td Tf).trans_lt (horigB p)) _ (hu _) (hatt _) (hgap _)
  let F (p : P) := Classical.choice (hF p)
  let widths (p : P) := deformedWidths10 (orig p).val c0
    (gapDeformation10 (sourceMinima10 A2 A3 L hL (orig p).val (hq _ (orig p).property) c0 c2 c3))
    (F p).sigma
  let A (p : ℝ) : Fin 10 → ℝ := if hp : p ∈ P then widths ⟨p,hp⟩ else fun _ => 1
  have hA (p : P) : widths p = A p.val := by simp only [A,dif_pos p.property]
  let D (p : P) : SourceData218 A2 A3 L hL p.val (hpq p.val p.property)
      (fun i => c2 i/5) (fun i => c3 i/5) (A p.val) (delta/60) :=
    sourceData_transport236 (hpow p) (hA p) (toSourceData236 (F p))
  have hframe (p : P) : (D p).u = fun j => ((F p).w j : Fin 10 → ℤ) :=
    sourceData_transport_frame236 (hpow p) (hA p) (toSourceData236 (F p))
  obtain ⟨S0,hS0,B0,hB0,U,hUP,hU,q1,hq1U,hq1B,b,hbn,hbe,hzero,C,hC,t,ht,T,hT,hBT,V,hVe,hVP,hV,hline⟩ :=
    source_fixed_line235 A2 A3 L h2d h3d hLd hL hAlg
      (fun i => c2 i/5) (fun i => c3 i/5)
      (scaled_exponents236 c2 hc2) (scaled_exponents236 c3 hc3)
      (delta/60) (by positivity) P hP hpq A D
  let W : Set ℝ := {Q | ∃ p : P, p.val ∈ V ∧ (lift p).val = Q}
  refine ⟨b,hbn,W,?_,power_pullback_unbounded236 Omega B hB lift hlift V hVP hV,?_⟩
  · rintro Q ⟨p,hp,rfl⟩
    exact (lift p).property.1
  · intro q hqW
    obtain ⟨p,hp,he⟩ := hqW
    have hqe : orig p = q := Subtype.ext he
    subst q
    have hcut := hflagcut _ ((le_max_right Td Tf).trans_lt (horigB p))
    have htransfer := deformed_line_transfer236 (F p) (hu (orig p)) (hgap (orig p)) hcut
    obtain ⟨_,_,_,_,_,hl⟩ := hline p hp
    have hl' : Submodule.span ℚ {fun i => (b i : ℚ)} =
        Submodule.span ℚ {lastDual10 (fun j i => (((F p).w j : Fin 10 → ℤ) i : ℚ))
          (F p).rational_independent} := by
      exact hl.trans (congrArg (fun z : Fin 10 → ℚ => Submodule.span ℚ {z})
        (lastDual_frame_eq236 (D p).u _ _ (F p).rational_independent (hframe p)))
    exact htransfer.trans hl'.symm

end CompoundFeasibility.SourceRatioLine236
