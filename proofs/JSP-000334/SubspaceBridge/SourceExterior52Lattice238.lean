import SubspaceBridge.SourceExterior52Algebra238
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.Exterior52_238
open Exterior52_237

def pairWeights238 (c : Fin 5 → ℝ) : Fin 10 → ℝ := fun s => c (lo237 s)+c (hi237 s)

def directGroup238 (A2 A3 : Matrix (Fin 5) (Fin 5) ℚ) (Q : ℝ) (c2 c3 : Fin 5 → ℝ) :
    AddSubgroup (Fin 10 → ℤ) :=
  sourceLattice10 (compound237 A2) (compound237 A3)
    (fun s => Nat.ceil (JSP000334.qThreshold 2 Q (pairWeights238 c2 s)))
    (fun s => Nat.ceil (JSP000334.qThreshold 3 Q (pairWeights238 c3 s)))

def summedGroup238 (A2 A3 : Matrix (Fin 5) (Fin 5) ℚ) (Q : ℝ) (c2 c3 : Fin 5 → ℝ) :
    AddSubgroup (Fin 10 → ℤ) :=
  sourceLattice10 (compound237 A2) (compound237 A3)
    (fun s => Nat.ceil (JSP000334.qThreshold 2 Q (c2 (lo237 s)))+
      Nat.ceil (JSP000334.qThreshold 2 Q (c2 (hi237 s))))
    (fun s => Nat.ceil (JSP000334.qThreshold 3 Q (c3 (lo237 s)))+
      Nat.ceil (JSP000334.qThreshold 3 Q (c3 (hi237 s))))

theorem local_raw238 (p : ℕ) [Fact p.Prime] (A : Matrix (Fin 5) (Fin 5) ℚ)
    (Q : ℝ) (hQ : 1 < Q) (c : Fin 5 → ℝ) (hc : ∀ i, c i ≤ 0) (z : Fin 10 → ℤ) :
    z ∈ lattice10 p (compound237 A) (fun s => Nat.ceil (JSP000334.qThreshold p Q (pairWeights238 c s))) ↔
      ∀ s, (padicNorm p ((compound237 A *ᵥ (fun t => (z t : ℚ))) s) : ℝ) ≤ Q^(pairWeights238 c s) := by
  rw [lattice10_spec]
  simp only [zpow_neg,zpow_natCast]
  apply forall_congr'
  intro s
  exact (padic_rpow_ceil42 p Q _ hQ (add_nonpos (hc _) (hc _)) _).symm

theorem direct_raw238 (A2 A3 : Matrix (Fin 5) (Fin 5) ℚ) (Q : ℝ) (hQ : 1 < Q)
    (c2 c3 : Fin 5 → ℝ) (hc2 : ∀ i, c2 i ≤ 0) (hc3 : ∀ i, c3 i ≤ 0) (z : Fin 10 → ℤ) :
    z ∈ directGroup238 A2 A3 Q c2 c3 ↔
      (∀ s, (padicNorm 2 ((compound237 A2 *ᵥ (fun t => (z t : ℚ))) s) : ℝ) ≤ Q^(pairWeights238 c2 s)) ∧
      (∀ s, (padicNorm 3 ((compound237 A3 *ᵥ (fun t => (z t : ℚ))) s) : ℝ) ≤ Q^(pairWeights238 c3 s)) := by
  exact and_congr (local_raw238 2 A2 Q hQ c2 hc2 z) (local_raw238 3 A3 Q hQ c3 hc3 z)

theorem local_summed_le238 (p : ℕ) [Fact p.Prime] (A : Matrix (Fin 5) (Fin 5) ℚ)
    (Q : ℝ) (c : Fin 5 → ℝ) :
    lattice10 p (compound237 A) (fun s => Nat.ceil (JSP000334.qThreshold p Q (c (lo237 s)))+
      Nat.ceil (JSP000334.qThreshold p Q (c (hi237 s)))) ≤
    lattice10 p (compound237 A) (fun s => Nat.ceil (JSP000334.qThreshold p Q (pairWeights238 c s))) := by
  intro z hz
  simp only [lattice10,AddSubgroup.mem_iInf,AddSubgroup.mem_comap] at hz ⊢
  intro s
  apply normBall_antitone42 p _ _ _ (hz s)
  rw [pairWeights238,qThreshold_add42]
  exact Nat.ceil_add_le _ _

theorem summed_le_direct238 (A2 A3 : Matrix (Fin 5) (Fin 5) ℚ) (Q : ℝ) (c2 c3 : Fin 5 → ℝ) :
    summedGroup238 A2 A3 Q c2 c3 ≤ directGroup238 A2 A3 Q c2 c3 := by
  intro z hz
  exact ⟨local_summed_le238 2 A2 Q c2 hz.1,local_summed_le238 3 A3 Q c3 hz.2⟩

theorem local_wedge238 (p : ℕ) [Fact p.Prime] (A : Matrix (Fin 5) (Fin 5) ℚ)
    (e : Fin 5 → ℕ) (x y : Fin 5 → ℤ) (hx : x ∈ lattice5 p A e) (hy : y ∈ lattice5 p A e) :
    wedge237 x y ∈ lattice10 p (compound237 A) (fun s => e (lo237 s)+e (hi237 s)) := by
  rw [lattice5_spec] at hx hy
  rw [lattice10_spec]
  simp only [zpow_neg,zpow_natCast] at hx hy ⊢
  rw [wedge_cast237,wedge_transform237]
  intro s
  have hpos (i : Fin 5) : 0 ≤ ((p : ℚ)^e i)⁻¹ := by positivity
  have h1 := mul_le_mul (hx (lo237 s)) (hy (hi237 s)) (padicNorm.nonneg _) (hpos _)
  have h2 := mul_le_mul (hx (hi237 s)) (hy (lo237 s)) (padicNorm.nonneg _) (hpos _)
  change padicNorm p (_-_) ≤ _
  apply padicNorm.sub.trans
  rw [padicNorm.mul,padicNorm.mul]
  apply max_le
  · simpa only [pow_add,mul_inv] using h1
  · simpa only [pow_add,mul_inv,mul_comm] using h2

theorem wedge_summed238 (A2 A3 : Matrix (Fin 5) (Fin 5) ℚ) (Q : ℝ) (c2 c3 : Fin 5 → ℝ)
    (x y : originalSourceGroup5 A2 A3 Q c2 c3) :
    wedge237 (x : Fin 5 → ℤ) (y : Fin 5 → ℤ) ∈ summedGroup238 A2 A3 Q c2 c3 := by
  let e2 : Fin 5 → ℕ := fun i => Nat.ceil (JSP000334.qThreshold 2 Q (c2 i))
  let e3 : Fin 5 → ℕ := fun i => Nat.ceil (JSP000334.qThreshold 3 Q (c3 i))
  have hx2 : (x : Fin 5 → ℤ) ∈ lattice5 2 A2 e2 := x.property.1
  have hy2 : (y : Fin 5 → ℤ) ∈ lattice5 2 A2 e2 := y.property.1
  have hx3 : (x : Fin 5 → ℤ) ∈ lattice5 3 A3 e3 := x.property.2
  have hy3 : (y : Fin 5 → ℤ) ∈ lattice5 3 A3 e3 := y.property.2
  have h2 := local_wedge238 2 A2 e2 (x : Fin 5 → ℤ) (y : Fin 5 → ℤ) hx2 hy2
  have h3 := local_wedge238 3 A3 e3 (x : Fin 5 → ℤ) (y : Fin 5 → ℤ) hx3 hy3
  exact ⟨h2,h3⟩

theorem wedge_direct238 (A2 A3 : Matrix (Fin 5) (Fin 5) ℚ) (Q : ℝ) (c2 c3 : Fin 5 → ℝ)
    (x y : originalSourceGroup5 A2 A3 Q c2 c3) :
    wedge237 (x : Fin 5 → ℤ) (y : Fin 5 → ℤ) ∈ directGroup238 A2 A3 Q c2 c3 :=
  summed_le_direct238 A2 A3 Q c2 c3 (wedge_summed238 A2 A3 Q c2 c3 x y)

theorem local_scale238 (p : ℕ) [hp : Fact p.Prime] (M : Matrix (Fin 10) (Fin 10) ℚ)
    (a : Fin 5 → ℝ) (ha : ∀ i, 0 ≤ a i) (m : ℤ) (hm : padicNorm p (m : ℚ) ≤ (p : ℚ)⁻¹)
    (z : Fin 10 → ℤ)
    (hz : z ∈ lattice10 p M (fun s => Nat.ceil (a (lo237 s)+a (hi237 s)))) :
    m • z ∈ lattice10 p M (fun s => Nat.ceil (a (lo237 s))+Nat.ceil (a (hi237 s))) := by
  have hp0 : (0 : ℚ) < p := by exact_mod_cast hp.out.pos
  have hz' := (lattice10_spec p M _ z).mp hz
  simp only [zpow_neg,zpow_natCast] at hz'
  apply (lattice10_spec p M _ (m • z)).mpr
  intro s
  rw [zpow_neg,zpow_natCast]
  change padicNorm p (row10 M s (m • z)) ≤ _
  have he : row10 M s (m • z) = (m : ℚ)*row10 M s z := by
    simpa only [zsmul_eq_mul] using (row10 M s).map_zsmul z m
  rw [he,padicNorm.mul]
  have hd := (ceil_pair_prime_powers p hp.out.one_le (a (lo237 s)) (a (hi237 s)) (ha _) (ha _)).2
  have hdQ : (p : ℚ)^(Nat.ceil (a (lo237 s))+Nat.ceil (a (hi237 s))) ≤
      (p : ℚ)*(p : ℚ)^Nat.ceil (a (lo237 s)+a (hi237 s)) := by exact_mod_cast hd
  have hfirst : padicNorm p (m : ℚ)*padicNorm p (row10 M s z) ≤
      (p : ℚ)⁻¹*((p : ℚ)^Nat.ceil (a (lo237 s)+a (hi237 s)))⁻¹ :=
    mul_le_mul hm (hz' s) (padicNorm.nonneg _) (inv_nonneg.mpr hp0.le)
  have hsecond : ((p : ℚ)*(p : ℚ)^Nat.ceil (a (lo237 s)+a (hi237 s)))⁻¹ ≤
      ((p : ℚ)^(Nat.ceil (a (lo237 s))+Nat.ceil (a (hi237 s))))⁻¹ :=
    (inv_le_inv₀ (mul_pos hp0 (pow_pos hp0 _)) (pow_pos hp0 _)).mpr hdQ
  exact hfirst.trans (by simpa only [mul_inv] using hsecond)

theorem six_direct_summed238 (A2 A3 : Matrix (Fin 5) (Fin 5) ℚ) (Q : ℝ) (hQ : 1 < Q)
    (c2 c3 : Fin 5 → ℝ) (hc2 : ∀ i, c2 i ≤ 0) (hc3 : ∀ i, c3 i ≤ 0)
    (z : Fin 10 → ℤ) (hz : z ∈ directGroup238 A2 A3 Q c2 c3) :
    (6 : ℤ) • z ∈ summedGroup238 A2 A3 Q c2 c3 := by
  have h2 : z ∈ lattice10 2 (compound237 A2) (fun s => Nat.ceil
      (JSP000334.qThreshold 2 Q (c2 (lo237 s))+JSP000334.qThreshold 2 Q (c2 (hi237 s)))) := by
    simpa only [pairWeights238,qThreshold_add42] using hz.1
  have h3 : z ∈ lattice10 3 (compound237 A3) (fun s => Nat.ceil
      (JSP000334.qThreshold 3 Q (c3 (lo237 s))+JSP000334.qThreshold 3 Q (c3 (hi237 s)))) := by
    simpa only [pairWeights238,qThreshold_add42] using hz.2
  exact ⟨local_scale238 2 (compound237 A2) _
      (fun i => JSP000334.qThreshold_nonneg 2 (by decide) Q (c2 i) hQ (hc2 i))
      6 six_norm2_42.le z h2,
    local_scale238 3 (compound237 A3) _
      (fun i => JSP000334.qThreshold_nonneg 3 (by decide) Q (c3 i) hQ (hc3 i))
      6 six_norm3_42.le z h3⟩
end CompoundFeasibility.Exterior52_238
