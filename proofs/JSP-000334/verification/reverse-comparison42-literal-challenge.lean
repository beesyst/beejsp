import SubspaceBridge.CompoundComparisonReverse42
open scoped BigOperators Matrix
open MeasureTheory CompoundFeasibility
namespace Reverse42Literal
noncomputable section

def threshold (p : ℕ) (Q c : ℝ) : ℕ := Nat.ceil (-c * Real.log Q / Real.log p)

def realMember (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (Q : ℝ) (c₂ c₃ : Fin 4 → ℝ) (x : Fin 4 → ℝ) : Prop :=
  ∃ z : Fin 4 → ℤ, (fun i => (z i : ℝ)) = x ∧
    (∀ i, padicNorm 2 ((A₂ *ᵥ (fun j => (z j : ℚ))) i) ≤
      (2 : ℚ) ^ (-(threshold 2 Q (c₂ i) : ℤ))) ∧
    ∀ i, padicNorm 3 ((A₃ *ᵥ (fun j => (z j : ℚ))) i) ≤
      (3 : ℚ) ^ (-(threshold 3 Q (c₃ i) : ℤ))

def minima (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ)
    (Q : ℝ) (c₀ c₂ c₃ : Fin 4 → ℝ) (k : Fin 4) : ℝ :=
  sInf {r : ℝ | ∃ u : Fin (k.val+1) → (Fin 4 → ℝ), LinearIndependent ℝ u ∧
    (∀ j, realMember A₂ A₃ Q c₂ c₃ (u j)) ∧
    ∀ j, ‖fun i => (L *ᵥ u j) i / Q ^ c₀ i‖ ≤ r}

theorem membership (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (Q : ℝ) (c₂ c₃ : Fin 4 → ℝ) (x : Fin 4 → ℝ) :
    x ∈ integerRealImage (originalSourceGroup4 A₂ A₃ Q c₂ c₃) ↔
      realMember A₂ A₃ Q c₂ c₃ x := by
  constructor
  · rintro ⟨z,hz,he⟩
    exact ⟨z,he,(lattice4_spec 2 A₂ _ z).mp hz.1,(lattice4_spec 3 A₃ _ z).mp hz.2⟩
  · rintro ⟨z,he,h2,h3⟩
    exact ⟨z,⟨(lattice4_spec 2 A₂ _ z).mpr h2,(lattice4_spec 3 A₃ _ z).mpr h3⟩,he⟩

theorem minima_equality (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L) (Q : ℝ) (hQ : 1 < Q)
    (c₀ c₂ c₃ : Fin 4 → ℝ) (j : Fin 4) :
    sourceMinima4 A₂ A₃ L hL Q hQ c₀ c₂ c₃ j = minima A₂ A₃ L Q c₀ c₂ c₃ j := by
  unfold sourceMinima4 minima
  simp only [membership]
  rfl


def C {R : Type*} [CommRing R] (L : Matrix (Fin 4) (Fin 4) R) : Matrix (Fin 6) (Fin 6) R :=
  fun s t => L (lo s) (lo t) * L (hi s) (hi t) - L (lo s) (hi t) * L (hi s) (lo t)

noncomputable def E (p : ℕ) (Q c : ℝ) : ℕ := Nat.ceil (-c * Real.log Q / Real.log p)

def H (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) (Q : ℝ) (c₂ c₃ : Fin 4 → ℝ) : Set (Fin 6 → ℤ) :=
  {z | (∀ s, padicNorm 2 (∑ t, C A₂ s t * (z t : ℚ)) ≤
      (2 : ℚ) ^ (-((E 2 Q (c₂ (lo s)) + E 2 Q (c₂ (hi s)) : ℕ) : ℤ))) ∧
    (∀ s, padicNorm 3 (∑ t, C A₃ s t * (z t : ℚ)) ≤
      (3 : ℚ) ^ (-((E 3 Q (c₃ (lo s)) + E 3 Q (c₃ (hi s)) : ℕ) : ℤ)))}

def realImage (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) (Q : ℝ) (c₂ c₃ : Fin 4 → ℝ) : Set (Fin 6 → ℝ) :=
  {x | ∃ z : Fin 6 → ℤ, z ∈ H A₂ A₃ Q c₂ c₃ ∧ (fun i => (z i : ℝ)) = x}

noncomputable def gauge (L : Matrix (Fin 4) (Fin 4) ℝ) (Q : ℝ) (c₀ : Fin 4 → ℝ) (x : Fin 6 → ℝ) : ℝ :=
  ‖fun s : Fin 6 => (∑ t : Fin 6, C L s t * x t) / (Q ^ c₀ (lo s) * Q ^ c₀ (hi s))‖

noncomputable def nu (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ)
    (Q : ℝ) (c₀ c₂ c₃ : Fin 4 → ℝ) (j : Fin 6) : ℝ :=
  sInf {r : ℝ | ∃ v : Fin (j.val+1) → (Fin 6 → ℝ), LinearIndependent ℝ v ∧
    (∀ i, v i ∈ realImage A₂ A₃ Q c₂ c₃) ∧ ∀ i, gauge L Q c₀ (v i) ≤ r}

theorem membership6 (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) (Q : ℝ) (c₂ c₃ : Fin 4 → ℝ) (z : Fin 6 → ℤ) :
    z ∈ compoundSourceGroup6 A₂ A₃ Q c₂ c₃ ↔ z ∈ H A₂ A₃ Q c₂ c₃ := by
  change (z ∈ lattice6 2 A₂ _ ∧ z ∈ lattice6 3 A₃ _) ↔ _
  rw [lattice6_spec,lattice6_spec]
  rfl

theorem image_eq6 (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) (Q : ℝ) (c₂ c₃ : Fin 4 → ℝ) :
    realImage A₂ A₃ Q c₂ c₃ = (integerRealImage (compoundSourceGroup6 A₂ A₃ Q c₂ c₃) : Set (Fin 6 → ℝ)) := by
  ext x
  constructor
  · rintro ⟨z,hz,rfl⟩
    exact ⟨z,(membership6 A₂ A₃ Q c₂ c₃ z).mpr hz,rfl⟩
  · rintro ⟨z,hz,rfl⟩
    exact ⟨z,(membership6 A₂ A₃ Q c₂ c₃ z).mp hz,rfl⟩

theorem gauge_eq6 (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c₀ : Fin 4 → ℝ) (x : Fin 6 → ℝ) :
    gauge L Q c₀ x = coordinateGauge6 (compoundCoordinates42 L hL Q hQ c₀) x := rfl

theorem minima_eq6 (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c₀ c₂ c₃ : Fin 4 → ℝ) (j : Fin 6) :
    sourceMinima6 A₂ A₃ L hL Q hQ c₀ c₂ c₃ j = nu A₂ A₃ L Q c₀ c₂ c₃ j := by
  simp only [sourceMinima6,nu,image_eq6,gauge_eq6 L hL Q hQ c₀]
  rfl

def sorted (a : Fin 4 → ℝ) : Fin 6 → ℝ := fun j =>
  if j = 0 then a 0 * a 1 else if j = 1 then a 0 * a 2 else
  if j = 2 then min (a 0 * a 3) (a 1 * a 2) else
  if j = 3 then max (a 0 * a 3) (a 1 * a 2) else
  if j = 4 then a 1 * a 3 else a 2 * a 3

def leftIndex : Fin 6 → Fin 4 := ![0,0,0,1,1,2]
def rightIndex : Fin 6 → Fin 4 := ![1,2,3,2,3,3]

theorem sorted_equality (a : Fin 4 → ℝ) : sortedPairProducts42 a = sorted a := by
  ext j
  fin_cases j <;> simp [sortedPairProducts42,sorted]

theorem uniform_export (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (h₂ : IsUnit A₂) (h₃ : IsUnit A₃) (hL : IsUnit L) :
    ∃ C₄ c₆ κ : ℝ, 0 < C₄ ∧ 0 < c₆ ∧ 0 < κ ∧ κ = c₆ / (32 * C₄ ^ 3) ∧
      ∀ (Q : ℝ), 1 < Q → ∀ c₀ c₂ c₃ : Fin 4 → ℝ,
        (∀ i, c₂ i ≤ 0) → (∀ i, c₃ i ≤ 0) →
        (∑ i, (c₀ i + c₂ i + c₃ i) = 0) →
        ∀ j : Fin 6,
          κ * sorted (minima A₂ A₃ L Q c₀ c₂ c₃) j ≤ nu A₂ A₃ L Q c₀ c₂ c₃ j ∧
          nu A₂ A₃ L Q c₀ c₂ c₃ j ≤ 2 * sorted (minima A₂ A₃ L Q c₀ c₂ c₃) j := by
  obtain ⟨C₄,c₆,κ,hC,hc,hk,he,h⟩ := source_compound_uniform_comparison42 A₂ A₃ L h₂ h₃ hL
  refine ⟨C₄,c₆,κ,hC,hc,hk,he,?_⟩
  intro Q hQ c₀ c₂ c₃ hc₂ hc₃ hb j
  have hfour : sourceMinima4 A₂ A₃ L hL Q hQ c₀ c₂ c₃ = minima A₂ A₃ L Q c₀ c₂ c₃ :=
    funext (minima_equality A₂ A₃ L hL Q hQ c₀ c₂ c₃)
  simpa only [sourcePairProducts42,hfour,sorted_equality,minima_eq6] using
    h Q hQ c₀ c₂ c₃ hc₂ hc₃ hb j

theorem expanded_product_route (A₂ A₃ : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (h₂ : IsUnit A₂) (h₃ : IsUnit A₃) (hL : IsUnit L) :
    ∃ C₄ c₆ : ℝ, 0 < C₄ ∧ 0 < c₆ ∧
      ∀ (Q : ℝ), 1 < Q → ∀ c₀ c₂ c₃ : Fin 4 → ℝ,
        (∀ i, c₂ i ≤ 0) → (∀ i, c₃ i ≤ 0) →
        (∑ i, (c₀ i + c₂ i + c₃ i) = 0) →
        let mu := sorted (minima A₂ A₃ L Q c₀ c₂ c₃)
        let v := nu A₂ A₃ L Q c₀ c₂ c₃
        (∀ k, 0 < mu k ∧ 0 < v k) ∧
        (∏ k, mu k) = (∏ i, minima A₂ A₃ L Q c₀ c₂ c₃ i) ^ 3 ∧
        (∏ k, mu k) ≤ C₄ ^ 3 ∧ c₆ ≤ (∏ k, v k) ∧
        ∀ j : Fin 6,
          (∏ k ∈ Finset.univ.erase j, v k) ≤ 32 * (∏ k ∈ Finset.univ.erase j, mu k) ∧
          c₆ * mu j ≤ 32 * v j * (∏ k, mu k) ∧
          (c₆ / (32 * C₄ ^ 3)) * mu j ≤ v j := by
  obtain ⟨_,C₄,_,hC,_,hfour⟩ := source_original_uniform_minima_upper4 A₂ A₃ L h₂ h₃ hL
  obtain ⟨c₆,hc,_,hsix⟩ := source_compound_uniform_minima_lower6 A₂ A₃ L h₂ h₃ hL
  refine ⟨C₄,c₆,hC,hc,?_⟩
  intro Q hQ c₀ c₂ c₃ hc₂ hc₃ hb
  let mu := sorted (minima A₂ A₃ L Q c₀ c₂ c₃)
  let v := nu A₂ A₃ L Q c₀ c₂ c₃
  have he4 : sourceMinima4 A₂ A₃ L hL Q hQ c₀ c₂ c₃ = minima A₂ A₃ L Q c₀ c₂ c₃ :=
    funext (minima_equality A₂ A₃ L hL Q hQ c₀ c₂ c₃)
  have hemu : sourcePairProducts42 A₂ A₃ L hL Q hQ c₀ c₂ c₃ = mu := by
    simp only [sourcePairProducts42,he4,sorted_equality,mu]
  have hev : sourceMinima6 A₂ A₃ L hL Q hQ c₀ c₂ c₃ = v :=
    funext (minima_eq6 A₂ A₃ L hL Q hQ c₀ c₂ c₃)
  have hp : ∀ k, 0 < mu k := hemu ▸ (sourcePairProducts42_pos_mono A₂ A₃ L hL Q hQ c₀ c₂ c₃).1
  have hv : ∀ k, 0 < v k := hev ▸ (sourceMinima6_pos_mono A₂ A₃ L hL Q hQ c₀ c₂ c₃).1
  have hu : ∀ k, v k ≤ 2 * mu k := by
    simpa only [hemu,hev] using source_compound_minima_upper42 A₂ A₃ L hL Q hQ c₀ c₂ c₃
  have hid : (∏ k, mu k) = (∏ i, minima A₂ A₃ L Q c₀ c₂ c₃ i) ^ 3 := by
    simpa only [hemu,he4] using sourcePairProducts42_product A₂ A₃ L hL Q hQ c₀ c₂ c₃
  have hm : (∏ k, mu k) ≤ C₄ ^ 3 := by
    rw [hid]
    have hb4 : (∏ i, minima A₂ A₃ L Q c₀ c₂ c₃ i) ≤ C₄ := by
      simpa only [he4] using hfour Q hQ c₀ c₂ c₃ hc₂ hc₃ hb
    exact pow_le_pow_left₀ (Finset.prod_pos (fun i _ => by
      simpa only [he4] using (sourceMinima4_pos_mono A₂ A₃ L hL Q hQ c₀ c₂ c₃).1 i)).le hb4 3
  have hl : c₆ ≤ ∏ k, v k := by simpa only [hev] using hsix Q hQ c₀ c₂ c₃ hb
  refine ⟨fun k => ⟨hp k,hv k⟩,hid,hm,hl,?_⟩
  intro j
  have herase : (∏ k ∈ Finset.univ.erase j, v k) ≤ 32 * (∏ k ∈ Finset.univ.erase j, mu k) := by
    calc
      _ ≤ ∏ k ∈ Finset.univ.erase j, 2 * mu k :=
        Finset.prod_le_prod (fun k _ => (hv k).le) (fun k _ => hu k)
      _ = _ := by rw [Finset.prod_mul_distrib]; norm_num
  have hdec (f : Fin 6 → ℝ) : f j * (∏ k ∈ Finset.univ.erase j, f k) = ∏ k, f k :=
    Finset.mul_prod_erase _ _ (Finset.mem_univ j)
  have hstep : c₆ * mu j ≤ 32 * v j * (∏ k, mu k) := by
    calc
      _ ≤ (∏ k, v k) * mu j := mul_le_mul_of_nonneg_right hl (hp j).le
      _ = v j * (∏ k ∈ Finset.univ.erase j, v k) * mu j := by rw [hdec]
      _ ≤ v j * (32 * (∏ k ∈ Finset.univ.erase j, mu k)) * mu j :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left herase (hv j).le) (hp j).le
      _ = _ := by rw [← hdec mu]; ring
  refine ⟨herase,hstep,?_⟩
  rw [div_mul_eq_mul_div,div_le_iff₀ (show 0 < 32 * C₄ ^ 3 by positivity)]
  calc
    _ ≤ 32 * v j * (∏ k, mu k) := hstep
    _ ≤ 32 * v j * C₄ ^ 3 := mul_le_mul_of_nonneg_left hm (mul_nonneg (by norm_num) (hv j).le)
    _ = _ := by ring

end
#check threshold
#print axioms threshold
#check realMember
#print axioms realMember
#check minima
#print axioms minima
#check membership
#print axioms membership
#check minima_equality
#print axioms minima_equality
#check C
#print axioms C
#check E
#print axioms E
#check H
#print axioms H
#check realImage
#print axioms realImage
#check gauge
#print axioms gauge
#check nu
#print axioms nu
#check membership6
#print axioms membership6
#check image_eq6
#print axioms image_eq6
#check gauge_eq6
#print axioms gauge_eq6
#check minima_eq6
#print axioms minima_eq6
#check sorted
#print axioms sorted
#check leftIndex
#print axioms leftIndex
#check rightIndex
#print axioms rightIndex
#check sorted_equality
#print axioms sorted_equality
#check uniform_export
#print axioms uniform_export
#check expanded_product_route
#print axioms expanded_product_route
end Reverse42Literal
