import SubspaceBridge.SourceAuxiliarySample10
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceSampling10
open SourceMultiblock10 SourceNormalHighIndex10 SchmidtPolynomial10

theorem source_auxiliary_samples10
    (A2 A3 : Matrix (Fin 10) (Fin 10) ℚ) (L : Matrix (Fin 10) (Fin 10) ℝ)
    (h2 : A2.det = 1) (h3 : A3.det = 1) (hL : L.det = 1)
    (ha : ∀ i j, IsAlgebraic ℚ (L i j)) :
    ∃ K : IntermediateField ℚ ℝ, FiniteDimensional ℚ K ∧
    ∃ D E : ℝ, 1 ≤ D ∧ 1 ≤ E ∧
    ∀ (c2 c3 : Fin 10 → ℝ) (V : Set ℝ), ¬ BddAbove V →
    ∀ v : V → Fin 10 → Fin 10 → ℤ,
    (∀ q, LinearIndependent ℝ (fun j => integerReal (v q j))) →
    ∀ w : (q : V) → Fin 10 → originalSourceGroup10 A2 A3 q.val c2 c3,
    (∀ q, LinearIndependent ℝ (fun j => integerReal (w q j : Fin 10 → ℤ))) →
    (∀ q, minimaFlag10 (fun j => integerReal (v q j)) 9 =
      minimaFlag10 (fun j => integerReal (w q j : Fin 10 → ℤ)) 9) →
    ∀ (c : Fin 3 → Fin 10 → ℝ) (epsilon : ℝ), 0 < epsilon → epsilon < 1 →
    (∀ tau i, |c tau i| ≤ 1) → (∑ tau, ∑ i, c tau i) = 0 →
    (∀ q : V, ∀ (j : Fin 9) i, ‖(L *ᵥ integerReal (w q j.castSucc : Fin 10 → ℤ)) i‖ ≤
      (q.val^5)^(c 0 i-epsilon)) →
    (∀ q : V, ∀ (j : Fin 9) i, ‖(SourceForms10.finiteMatrix10 2 A2 *ᵥ
      (fun k => ((w q j.castSucc : Fin 10 → ℤ) k : ℚ_[2]))) i‖ ≤ (q.val^5)^(c 1 i)) →
    (∀ q : V, ∀ (j : Fin 9) i, ‖(SourceForms10.finiteMatrix10 3 A3 *ᵥ
      (fun k => ((w q j.castSucc : Fin 10 → ℤ) k : ℚ_[3]))) i‖ ≤ (q.val^5)^(c 2 i)) →
    ∃ eta : ℝ, 0 < eta ∧ 4000*eta < epsilon ∧
    ∃ m : ℕ, ∃ hm : 0 < m,
      4*(eta^2)⁻¹*Real.log (60*(Module.finrank ℚ K : ℝ)) ≤ (m : ℝ) ∧
      ∀ rho : ℝ, 0 < rho → ∀ B : ℝ,
        Nonempty (OriginalAuxiliarySample10 A2 A3 L c2 c3 V v c epsilon eta D E B rho m hm) := by
  obtain ⟨K,hK,hmem,D,E,hD,hE,haux⟩ := Auxiliary10.source_auxiliary_polynomial10 A2 A3 L h2 h3 hL ha
  refine ⟨K,hK,D,E,hD,hE,?_⟩
  intro c2 c3 V hV v hv w hw hflag c epsilon he he1 hc hbal hw0 hw2 hw3
  let eta := epsilon/8000
  have heta : 0 < eta := by dsimp [eta]; positivity
  have hmargin : 4000*eta < epsilon := by dsimp [eta]; linarith
  obtain ⟨m,hm⟩ := exists_nat_gt (max 1 (4*(eta^2)⁻¹*Real.log (60*(Module.finrank ℚ K : ℝ))))
  have hmp : 0 < m := by
    have hh : (1 : ℝ) < m := (le_max_left _ _).trans_lt hm
    exact_mod_cast (zero_lt_one.trans hh)
  have hcount := ((le_max_right _ _).trans_lt hm).le
  refine ⟨eta,heta,hmargin,m,hmp,hcount,?_⟩
  intro rho hrho B
  obtain ⟨t,r,hmono,hlarge,hr,hsep,hlog⟩ := normalized_tail_parameters10 V hV eta E rho B heta hE hrho m hmp
  have hnorm (h : Fin m) := actual_frame_normals10 (v (t h))
    (fun j => (w (t h) j : Fin 10 → ℤ)) (hv (t h)) (hw (t h)) (hflag (t h))
  choose M a hM ha' hprim hku hkw hru hrw using hnorm
  obtain ⟨P,hn,hhom,hblock,hdegree,hheight,hfield,hreal,hp2,hp3,hclaims,hcfs,hgrid⟩ :=
    haux eta heta m hcount r hr
  have hactual := hgrid (fun h => (t h).val^5) (fun h => (hlarge h).2.2.1)
    ⟨0,hmp⟩ epsilon hmargin he1 (fun h => (hlarge h).2.2.2.1)
    (fun h => (hlarge h).2.2.2.2) hlog c hc hbal
    (fun h j => (w (t h) j.castSucc : Fin 10 → ℤ))
    (fun h => hw0 (t h)) (fun h => hw2 (t h)) (fun h => hw3 (t h))
  have hnormal := hactual.2 M hM hkw hrw
  let S : OriginalSampleData10 V m := {
    t := t
    r := r
    w := fun h j => (w (t h) j : Fin 10 → ℤ)
    M := M
    a := a
    P := P }
  have hconditions : OriginalSampleConditions10 A2 A3 L c2 c3 V v c epsilon eta D E B rho m hmp S := {
    increasing := hmono
    large := hlarge
    positive_degrees := hr
    degree_separation := hsep
    logarithmic_balance := hlog
    member := fun h j => (w (t h) j).property
    independent := fun h => hw (t h)
    original_flag := fun h => hflag (t h)
    real_bound := fun h => hw0 (t h)
    two_bound := fun h => hw2 (t h)
    three_bound := fun h => hw3 (t h)
    normal_nonzero := hM
    bezout := ha'
    primitive := hprim
    original_rational_kernel := hku
    original_real_kernel := hru
    rational_kernel := hkw
    real_kernel := hrw
    polynomial_nonzero := hn
    homogeneous := hhom
    block_degrees := hblock
    variable_degrees := hdegree
    height := hheight
    grid := hactual.1
    rational_restrictions := fun J hJ => (hnormal.1 J hJ).1
    real_restrictions := fun J hJ => (hnormal.1 J hJ).2
    normal_ideal := hnormal.2 }
  exact ⟨⟨S,hconditions⟩⟩

end CompoundFeasibility.SourceSampling10
