import SubspaceBridge.SourceWeights4
import SubspaceBridge.SourceBlocks6
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceBlocks4
open SourceWeights4 SourceMultiblock4 Auxiliary4 Auxiliary4.SourceBalance4
  Auxiliary4.SourceVanishing4 Auxiliary4.SourceGrid4 Auxiliary4.SourceEvaluation4
open OriginalDeformedSource4

theorem original_blocks4 (V : Set ℝ) (hV : ¬ BddAbove V)
    (eta E rho : ℝ) (he : 0 < eta) (hE : 1 ≤ E) (hp : 0 < rho) (m : ℕ) :
    ∃ t : Fin m → V, StrictMono (fun h => (t h).val) ∧
      Set.Finite (Set.range t) ∧
      (∀ h, 1 < (t h).val^(5 : ℕ) ∧
        16*E < ((t h).val^(5 : ℕ))^eta ∧
        4*(eta⁻¹+1) < ((t h).val^(5 : ℕ))^eta) ∧
      ∀ (h : Fin m) (hh : h.val+1 < m),
        (1+eta)*Real.log ((t h).val^(5 : ℕ)) ≤
          rho*Real.log ((t ⟨h.val+1,hh⟩).val^(5 : ℕ)) := by
  let B := max (Real.log (16*E)/eta) (Real.log (4*(eta⁻¹+1))/eta)
  obtain ⟨q,hq,hmono,hsep⟩ := JSP000334.parameter_sparse_Q V hV (Real.exp B)
    ((1+eta)/rho) m
  let t : Fin m → V := fun h => ⟨q h,(hq h).1⟩
  have hlog (h) : B < Real.log (q h) := by
    simpa only [Real.log_exp] using Real.log_lt_log (Real.exp_pos B) (hq h).2.1
  have hQ (h) : 1 < (q h)^(5 : ℕ) := one_lt_pow₀ (hq h).2.2 (by decide)
  have hlogpow (h) : B < Real.log ((q h)^(5 : ℕ)) := by
    rw [Real.log_pow]
    have hl := Real.log_pos (hq h).2.2
    norm_num only [Nat.cast_ofNat]
    linarith [hlog h]
  refine ⟨t,hmono,Set.finite_range t,?_,?_⟩
  · intro h
    refine ⟨hQ h,?_,?_⟩
    · exact JSP000334.parameter_rpow_threshold _ eta _ (hQ h) he (by linarith)
        (lt_of_le_of_lt (le_max_left _ _) (hlogpow h))
    · exact JSP000334.parameter_rpow_threshold _ eta _ (hQ h) he (by positivity)
        (lt_of_le_of_lt (le_max_right _ _) (hlogpow h))
  · intro h hh
    have hs0 := hsep h hh
    rw [div_mul_eq_mul_div] at hs0
    have hs := (div_lt_iff₀ hp).mp hs0
    dsimp [t]
    rw [Real.log_pow,Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    nlinarith

variable {A2 A3 : Matrix (Fin 4) (Fin 4) ℚ} {L : Matrix (Fin 4) (Fin 4) ℝ}
  {hL : IsUnit L} {c0 c2 c3 : Fin 4 → ℝ} {delta : ℝ}
  {U : Set ℝ} {hQU : ∀ q ∈ U, 1 < q}
  {u : (q : U) → Fin 4 → originalSourceGroup4 A2 A3 q.val c2 c3}

theorem same_selected_frame_grid4
    (h2 : A2.det = 1) (h3 : A3.det = 1) (hLdet : L.det = 1)
    (ha : ∀ i j, IsAlgebraic ℚ (L i j))
    (F : (q : U) → DeformedAttaining4 A2 A3 L hL q.val
      (hQU q.val q.property) c0 c2 c3 delta (u q))
    (hU : ¬ BddAbove U) (hd : 0 < delta)
    (hc2 : ∀ i, -1 ≤ c2 i ∧ c2 i ≤ 0) (hc3 : ∀ i, -1 ≤ c3 i ∧ c3 i ≤ 0) :
    ∃ eta : ℝ, 0 < eta ∧ eta < 1 ∧ ∃ m : ℕ, 0 < m ∧
      ∃ K : IntermediateField ℚ ℝ, FiniteDimensional ℚ K ∧
      (∀ tau i j, SourceForms4.forms4 A2 A3 L tau i j ∈ K) ∧
      ∃ D E : ℝ, 1 ≤ D ∧ 1 ≤ E ∧
      ∀ rho : ℝ, 0 < rho → ∃ t : Fin m → U,
        StrictMono (fun h => (t h).val) ∧
        ∃ r : Fin m → ℕ, (∀ h, 0 < r h) ∧
        (∀ (h : Fin m) (hh : h.val+1 < m), (r ⟨h.val+1,hh⟩ : ℝ) ≤ rho*(r h : ℝ)) ∧
        ∃ P : MvPolynomial (Vars4 m) ℤ, P ≠ 0 ∧ homogeneous4 r P ∧
          (height4 P : ℝ) ≤ D^(∑ h, r h) ∧
          matrixIndex4 L r eta P ∧ matrixIndex4 (SourceForms4.finiteMatrix4 2 A2) r eta P ∧
          matrixIndex4 (SourceForms4.finiteMatrix4 3 A3) r eta P ∧
          (∀ J b : Vars4 m →₀ ℕ,
            ‖(Auxiliary4.SourceExpansion4.expansion L J P).coeff b‖ ≤ E^(∑ h,r h) ∧
            ‖(Auxiliary4.SourceExpansion4.expansion (SourceForms4.finiteMatrix4 2 A2) J P).coeff b‖ ≤ E^(∑ h,r h) ∧
            ‖(Auxiliary4.SourceExpansion4.expansion (SourceForms4.finiteMatrix4 3 A3) J P).coeff b‖ ≤ E^(∑ h,r h)) ∧
          ∀ a : Fin m → Fin 3 → ℕ, (∀ h j, 1 ≤ a h j ∧ a h j ≤ Nat.floor eta⁻¹+1) →
          ∀ J : Vars4 m →₀ ℕ, rothSourceDerivativeWeight r J < 2*eta*m →
            integerValue J P (gridPoint (fun h j => ((F (t h)).w j.castSucc : Fin 4 → ℤ)) a) = 0 := by
  obtain ⟨V,hVU,hV,d,hdp,hd1,c,hc,hbal,hfin,hframe⟩ := fixed_weights_same_frame4 F hU hd hc2 hc3
  obtain ⟨K,hK,hmem,D,E,hD,hE,haux⟩ := source_auxiliary4_grid_vanishing A2 A3 L h2 h3 hLdet ha
  let eta := d/3456
  have he : 0 < eta := by dsimp [eta]; positivity
  have he1 : eta < 1 := by dsimp [eta]; linarith
  have hde : 1728*eta < d := by dsimp [eta]; linarith
  obtain ⟨m,hm⟩ := exists_nat_gt (max 1 (4*(eta^2)⁻¹*Real.log (24*(Module.finrank ℚ K : ℝ))))
  have hmp : 0 < m := by
    have h1 : (1 : ℝ) < m := lt_of_le_of_lt (le_max_left _ _) hm
    exact_mod_cast (lt_trans zero_lt_one h1)
  have hcut := (lt_of_le_of_lt (le_max_right _ _) hm).le
  refine ⟨eta,he,he1,m,hmp,K,hK,hmem,D,E,hD,hE,?_⟩
  intro rho hp
  obtain ⟨t,ht,hfinite,hgrowth,hsep⟩ := original_blocks4 V hV eta E rho he hE hp m
  let lift : V → U := fun q => ⟨q.val,hVU q.property⟩
  let Q : Fin m → ℝ := fun h => (t h).val^(5 : ℕ)
  have hQ : ∀ h, 1 < Q h := fun h => (hgrowth h).1
  obtain ⟨h0,r,hr,hlogs,hA,hrsep,hrbal⟩ := SourceBlocks.positive_degrees m hmp eta rho he hp Q hQ hsep
  obtain ⟨P,hP,hhom,hheight,hfield,hreal,hp2,hp3,hclaims,hcfs,hvan⟩ := haux eta he m hcut r hr
  refine ⟨fun h => lift (t h),ht,r,hr,hrsep,P,hP,hhom,hheight,hreal 0,hp2,hp3,hcfs,?_⟩
  apply hvan Q hQ h0 d hde hd1 (fun h => (hgrowth h).2.1)
    (fun h => (hgrowth h).2.2) hrbal c hc hbal
    (fun h j => ((F (lift (t h))).w j.castSucc : Fin 4 → ℤ))
  · intro h j i
    exact (hframe (lift (t h)) (t h).property).1 j i
  · intro h j i
    exact (hframe (lift (t h)) (t h).property).2.1 j i
  · intro h j i
    exact (hframe (lift (t h)) (t h).property).2.2 j i

end CompoundFeasibility.SourceBlocks4
