import SubspaceBridge.SourceExterior53_242
import SubspaceBridge.SourceExterior52Normalize238
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.Exterior53_242

def tripleWeights242 (c : Fin 5 → ℝ) : Fin 10 → ℝ := fun s => c (lo242 s)+c (mid242 s)+c (hi242 s)

def directGroup3242 (A2 A3 : Matrix (Fin 5) (Fin 5) ℚ) (Q : ℝ) (c2 c3 : Fin 5 → ℝ) :
    AddSubgroup (Fin 10 → ℤ) :=
  sourceLattice10 (compound3242 A2) (compound3242 A3)
    (fun s => Nat.ceil (JSP000334.qThreshold 2 Q (tripleWeights242 c2 s)))
    (fun s => Nat.ceil (JSP000334.qThreshold 3 Q (tripleWeights242 c3 s)))

theorem local_raw3242 (p : ℕ) [Fact p.Prime] (A : Matrix (Fin 5) (Fin 5) ℚ)
    (Q : ℝ) (hQ : 1<Q) (c : Fin 5 → ℝ) (hc : ∀ i, c i ≤ 0) (z : Fin 10 → ℤ) :
    z ∈ lattice10 p (compound3242 A) (fun s => Nat.ceil (JSP000334.qThreshold p Q (tripleWeights242 c s))) ↔
      ∀ s, (padicNorm p ((compound3242 A *ᵥ (fun t => (z t : ℚ))) s) : ℝ) ≤ Q^(tripleWeights242 c s) := by
  rw [lattice10_spec]
  simp only [zpow_neg,zpow_natCast]
  apply forall_congr'
  intro s
  exact (padic_rpow_ceil42 p Q _ hQ (add_nonpos (add_nonpos (hc _) (hc _)) (hc _)) _).symm

theorem direct_raw3242 (A2 A3 : Matrix (Fin 5) (Fin 5) ℚ) (Q : ℝ) (hQ : 1<Q)
    (c2 c3 : Fin 5 → ℝ) (hc2 : ∀ i, c2 i ≤ 0) (hc3 : ∀ i, c3 i ≤ 0) (z : Fin 10 → ℤ) :
    z ∈ directGroup3242 A2 A3 Q c2 c3 ↔
      (∀ s, (padicNorm 2 ((compound3242 A2 *ᵥ (fun t => (z t : ℚ))) s) : ℝ) ≤ Q^(tripleWeights242 c2 s)) ∧
      (∀ s, (padicNorm 3 ((compound3242 A3 *ᵥ (fun t => (z t : ℚ))) s) : ℝ) ≤ Q^(tripleWeights242 c3 s)) :=
  and_congr (local_raw3242 2 A2 Q hQ c2 hc2 z) (local_raw3242 3 A3 Q hQ c3 hc3 z)

theorem local_wedge3242 (p : ℕ) [Fact p.Prime] (A : Matrix (Fin 5) (Fin 5) ℚ)
    (e : Fin 5 → ℕ) (x y z : Fin 5 → ℤ)
    (hx : x ∈ lattice5 p A e) (hy : y ∈ lattice5 p A e) (hz : z ∈ lattice5 p A e) :
    wedge3242 x y z ∈ lattice10 p (compound3242 A) (fun s => e (lo242 s)+e (mid242 s)+e (hi242 s)) := by
  rw [lattice5_spec] at hx hy hz
  rw [lattice10_spec]
  simp only [zpow_neg,zpow_natCast] at hx hy hz ⊢
  rw [wedge_cast3242,wedge_transform3242]
  have term (u v w : Fin 5 → ℚ)
      (hu : ∀ i, padicNorm p (u i) ≤ ((p : ℚ)^e i)⁻¹)
      (hv : ∀ i, padicNorm p (v i) ≤ ((p : ℚ)^e i)⁻¹)
      (hw : ∀ i, padicNorm p (w i) ≤ ((p : ℚ)^e i)⁻¹) (a b c : Fin 5) :
      padicNorm p (u a*v b*w c) ≤ ((p : ℚ)^(e a+e b+e c))⁻¹ := by
    rw [padicNorm.mul,padicNorm.mul]
    have h := mul_le_mul (mul_le_mul (hu a) (hv b) (padicNorm.nonneg _) (by positivity))
      (hw c) (padicNorm.nonneg _) (by positivity)
    simpa only [pow_add,mul_inv] using h
  have addBound {a b r : ℚ} (ha : padicNorm p a ≤ r) (hb : padicNorm p b ≤ r) :
      padicNorm p (a+b) ≤ r := padicNorm.nonarchimedean.trans (max_le ha hb)
  have subBound {a b r : ℚ} (ha : padicNorm p a ≤ r) (hb : padicNorm p b ≤ r) :
      padicNorm p (a-b) ≤ r := padicNorm.sub.trans (max_le ha hb)
  intro s
  unfold wedge3242 det3242
  apply subBound (subBound (subBound (addBound (addBound ?_ ?_) ?_) ?_) ?_) ?_
  · exact term _ _ _ hx hy hz _ _ _
  · simpa only [add_comm,add_left_comm,add_assoc] using term _ _ _ hy hz hx (lo242 s) (mid242 s) (hi242 s)
  · simpa only [add_comm,add_left_comm,add_assoc] using term _ _ _ hz hx hy (lo242 s) (mid242 s) (hi242 s)
  · simpa only [add_comm,add_left_comm,add_assoc] using term _ _ _ hz hy hx (lo242 s) (mid242 s) (hi242 s)
  · simpa only [add_comm,add_left_comm,add_assoc] using term _ _ _ hy hx hz (lo242 s) (mid242 s) (hi242 s)
  · simpa only [add_comm,add_left_comm,add_assoc] using term _ _ _ hx hz hy (lo242 s) (mid242 s) (hi242 s)

theorem local_ceiling_inclusion3242 (p : ℕ) [Fact p.Prime] (A : Matrix (Fin 5) (Fin 5) ℚ)
    (Q : ℝ) (c : Fin 5 → ℝ) :
    lattice10 p (compound3242 A) (fun s => Nat.ceil (JSP000334.qThreshold p Q (c (lo242 s)))+
      Nat.ceil (JSP000334.qThreshold p Q (c (mid242 s)))+Nat.ceil (JSP000334.qThreshold p Q (c (hi242 s)))) ≤
    lattice10 p (compound3242 A) (fun s => Nat.ceil (JSP000334.qThreshold p Q (tripleWeights242 c s))) := by
  intro z hz
  simp only [lattice10,AddSubgroup.mem_iInf,AddSubgroup.mem_comap] at hz ⊢
  intro s
  apply normBall_antitone42 p _ _ _ (hz s)
  rw [tripleWeights242,qThreshold_add42,qThreshold_add42]
  exact (Nat.ceil_add_le _ _).trans (Nat.add_le_add_right (Nat.ceil_add_le _ _) _)

theorem wedge_direct3242 (A2 A3 : Matrix (Fin 5) (Fin 5) ℚ) (Q : ℝ) (c2 c3 : Fin 5 → ℝ)
    (x y z : originalSourceGroup5 A2 A3 Q c2 c3) :
    wedge3242 (x : Fin 5 → ℤ) (y : Fin 5 → ℤ) (z : Fin 5 → ℤ) ∈ directGroup3242 A2 A3 Q c2 c3 := by
  let e2 : Fin 5 → ℕ := fun i => Nat.ceil (JSP000334.qThreshold 2 Q (c2 i))
  let e3 : Fin 5 → ℕ := fun i => Nat.ceil (JSP000334.qThreshold 3 Q (c3 i))
  have hx2 : (x : Fin 5 → ℤ) ∈ lattice5 2 A2 e2 := x.property.1
  have hy2 : (y : Fin 5 → ℤ) ∈ lattice5 2 A2 e2 := y.property.1
  have hz2 : (z : Fin 5 → ℤ) ∈ lattice5 2 A2 e2 := z.property.1
  have hx3 : (x : Fin 5 → ℤ) ∈ lattice5 3 A3 e3 := x.property.2
  have hy3 : (y : Fin 5 → ℤ) ∈ lattice5 3 A3 e3 := y.property.2
  have hz3 : (z : Fin 5 → ℤ) ∈ lattice5 3 A3 e3 := z.property.2
  have h2 := local_wedge3242 2 A2 e2 (x : Fin 5 → ℤ) (y : Fin 5 → ℤ) (z : Fin 5 → ℤ) hx2 hy2 hz2
  have h3 := local_wedge3242 3 A3 e3 (x : Fin 5 → ℤ) (y : Fin 5 → ℤ) (z : Fin 5 → ℤ) hx3 hy3 hz3
  exact ⟨local_ceiling_inclusion3242 2 A2 Q c2 h2,local_ceiling_inclusion3242 3 A3 Q c3 h3⟩

end CompoundFeasibility.Exterior53_242
