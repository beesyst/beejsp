import SubspaceBridge.SchlickeweiAuxiliaryDual6
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SchlickeweiIntegerPairing6
open SourceReadiness6 SchlickeweiDualVanishing6 SchlickeweiEquation4116
open SchlickeweiAuxiliaryDual6 Auxiliary6.SourceExpansion

def integerPairing6 (x y : Fin 6 → ℤ) : ℤ := ∑ i, x i * y i

theorem integer_cast_pairing6 (p : ℕ) [Fact p.Prime] (x y : Fin 6 → ℤ) :
    (integerPairing6 x y : ℚ_[p]) = ∑ i, (x i : ℚ_[p]) * (y i : ℚ_[p]) := by
  simp only [integerPairing6, Int.cast_sum, Int.cast_mul]


theorem native_matrix_pairing6 (p : ℕ) [Fact p.Prime]
    (B : Matrix (Fin 6) (Fin 6) ℚ_[p]) (hB : B.det ≠ 0)
    (xp yp : Fin 6 → ℚ_[p]) :
    (∑ k, xp k * yp k) = ∑ i, (B *ᵥ xp) i * (B⁻¹.transpose *ᵥ yp) i := by
  change xp ⬝ᵥ yp = (B *ᵥ xp) ⬝ᵥ (B⁻¹.transpose *ᵥ yp)
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hB), Matrix.one_mulVec]

theorem native_integer_pairing6 (p : ℕ) [Fact p.Prime]
    (B : Matrix (Fin 6) (Fin 6) ℚ_[p]) (hB : B.det ≠ 0) (x y : Fin 6 → ℤ) :
    (integerPairing6 x y : ℚ_[p]) =
      ∑ i, (B *ᵥ (fun k => (x k : ℚ_[p]))) i *
        (B⁻¹.transpose *ᵥ (fun k => (y k : ℚ_[p]))) i := by
  let xp : Fin 6 → ℚ_[p] := fun k => (x k : ℚ_[p])
  let yp : Fin 6 → ℚ_[p] := fun k => (y k : ℚ_[p])
  exact (integer_cast_pairing6 p x y).trans (native_matrix_pairing6 p B hB xp yp)


theorem native_dual_coordinates6 (p : ℕ) [Fact p.Prime]
    (B : Matrix (Fin 6) (Fin 6) ℚ_[p]) (y : Fin 6 → ℤ) (i : Fin 6) :
    dualFormValue6 B (fun k => (y k : ℚ)) i =
      (B⁻¹.transpose *ᵥ (fun k => (y k : ℚ_[p]))) i := by
  simp only [dualFormValue6, map_intCast, Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro k _
  ring


theorem native_ultrametric_pairing6 (p : ℕ) [Fact p.Prime]
    (B : Matrix (Fin 6) (Fin 6) ℚ_[p]) (hB : B.det ≠ 0)
    (f : Fin 6 → ℤ) (x y : Fin 6 → ℤ)
    (hx : ∀ i, ‖(B *ᵥ (fun k => (x k : ℚ_[p]))) i‖ ≤ (p : ℝ) ^ f i)
    (hy : ∀ i, ‖(B⁻¹.transpose *ᵥ (fun k => (y k : ℚ_[p]))) i‖ ≤
      (p : ℝ) ^ (∑ k : Fin 5, f (i.succAbove k))) :
    ‖(integerPairing6 x y : ℚ_[p])‖ ≤ (p : ℝ) ^ (∑ i, f i) := by
  have he := native_integer_pairing6 p B hB x y
  have hn := congrArg (fun z : ℚ_[p] => ‖z‖) he
  apply hn.trans_le
  apply SourceLocalUpper6.padic_sum_bound6 p Finset.univ _ _ (by positivity)
  intro i _
  rw [norm_mul]
  calc
    _ ≤ (p : ℝ) ^ f i * (p : ℝ) ^ (∑ k : Fin 5, f (i.succAbove k)) :=
      mul_le_mul (hx i) (hy i) (norm_nonneg _) (by positivity)
    _ = _ := by
      rw [← zpow_add₀ (by exact_mod_cast (Fact.out : p.Prime).ne_zero),
        ← Fin.sum_univ_succAbove f i]


theorem integer_norm_dvd6 (p : ℕ) [Fact p.Prime] (z : ℤ) (N : ℕ) :
    ‖(z : ℚ_[p])‖ ≤ (p : ℝ) ^ (-(N : ℤ)) ↔ (p : ℤ) ^ N ∣ z := by
  have hn : ‖(z : ℚ_[p])‖ = (padicNorm p (z : ℚ) : ℝ) := by
    simpa only [map_intCast] using finite_norm p (z : ℚ)
  rw [hn]
  have hc := (Rat.cast_le (K := ℝ) (p := padicNorm p (z : ℚ))
    (q := (p : ℚ) ^ (-(N : ℤ))))
  simpa only [Rat.cast_zpow, Rat.cast_natCast, Nat.cast_pow] using
    hc.trans (padicNorm.dvd_iff_norm_le (p := p) (n := N) (z := z)).symm



theorem dual_bounds_native6 (p : ℕ) [Fact p.Prime]
    (B : Matrix (Fin 6) (Fin 6) ℚ_[p]) (y : Fin 6 → ℤ) (f : Fin 6 → ℤ)
    (hy : ∀ i, ‖dualFormValue6 B (fun k => (y k : ℚ)) i‖ ≤
      (p : ℝ) ^ (∑ k : Fin 5, f (i.succAbove k))) :
    ∀ i, ‖(B⁻¹.transpose *ᵥ (fun k => (y k : ℚ_[p]))) i‖ ≤
      (p : ℝ) ^ (∑ k : Fin 5, f (i.succAbove k)) := by
  intro i
  have he := native_dual_coordinates6 p B y i
  have hn := congrArg (fun z : ℚ_[p] => ‖z‖) he
  exact hn.symm.trans_le (hy i)

theorem native_pairing_dvd6 (p : ℕ) [Fact p.Prime]
    (B : Matrix (Fin 6) (Fin 6) ℚ_[p]) (hB : B.det ≠ 0)
    (e : Fin 6 → ℕ) (x y : Fin 6 → ℤ)
    (hx : ∀ i, ‖(B *ᵥ (fun k => (x k : ℚ_[p]))) i‖ ≤ (p : ℝ) ^ (-(e i : ℤ)))
    (hy : ∀ i, ‖(B⁻¹.transpose *ᵥ (fun k => (y k : ℚ_[p]))) i‖ ≤
      (p : ℝ) ^ (∑ k : Fin 5, -(e (i.succAbove k) : ℤ))) :
    (p : ℤ) ^ (∑ i, e i) ∣ integerPairing6 x y := by
  have h := native_ultrametric_pairing6 p B hB (fun i => -(e i : ℤ)) x y hx hy
  apply (integer_norm_dvd6 p (integerPairing6 x y) (∑ i, e i)).mp
  simpa only [Finset.sum_neg_distrib, ← Nat.cast_sum] using h


variable {A2 A3 : Matrix (Fin 4) (Fin 4) ℚ} {L : Matrix (Fin 4) (Fin 4) ℝ}
  {hL : IsUnit L} {c0 c2 c3 : Fin 4 → ℝ} {delta4 : ℝ} {V : Set ℝ}
  {hQV : ∀ q ∈ V, 1 < q}

def sourceAuxiliaryInteger6
    (R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV)
    (q : V) (y : Fin 6 → ℤ) : Prop :=
  let Q := q.val ^ (11 : ℕ)
  let d := ZLattice.covolume (integerRealImage (directCompoundGroup42 A2 A3 q.val c2 c3))
  (∀ i, ‖dualFormValue6 (compound L) (fun k => (y k : ℚ)) i‖ ≤ d / Q ^ (R.c 0 i)) ∧
  (∀ i, ‖dualFormValue6 (finiteMatrix 2 A2) (fun k => (y k : ℚ)) i‖ ≤
    (2 : ℝ) ^ (∑ k : Fin 5, sourceExponent6 2 q.val c2 (i.succAbove k))) ∧
  (∀ i, ‖dualFormValue6 (finiteMatrix 3 A3) (fun k => (y k : ℚ)) i‖ ≤
    (3 : ℝ) ^ (∑ k : Fin 5, sourceExponent6 3 q.val c3 (i.succAbove k)))


theorem source_pairing_p2_6
    (R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV)
    (h2 : A2.det = 1) (q : V) (y : Fin 6 → ℤ)
    (hy : sourceAuxiliaryInteger6 R q y) (j : Fin 5) :
    (2 : ℤ) ^ (∑ i : Fin 6, Nat.ceil
      (JSP000334.qThreshold 2 q.val (pairWeights42 c2 i))) ∣
      integerPairing6 (R.w q j.castSucc : Fin 6 → ℤ) y := by
  let B : Matrix (Fin 6) (Fin 6) ℚ_[2] := finiteMatrix 2 A2
  let e : Fin 6 → ℕ := fun i => Nat.ceil
    (JSP000334.qThreshold 2 q.val (pairWeights42 c2 i))
  have hB : B.det ≠ 0 := by
    rw [finite_matrix_det_one6 2 A2 h2]
    norm_num
  have hxall := source_first_five_integer_bounds6 R q
  rcases hy with ⟨_, hy2, _⟩
  have hyn := dual_bounds_native6 2 B y (sourceExponent6 2 q.val c2) hy2
  have hx : ∀ i, ‖(B *ᵥ
      (fun k => ((R.w q j.castSucc : Fin 6 → ℤ) k : ℚ_[2]))) i‖ ≤
        (2 : ℝ) ^ (-(e i : ℤ)) := by
    intro i
    have hi := hxall.1 j i
    simpa only [sourceExponent6, e, B, Nat.cast_ofNat] using hi
  have hyN : ∀ i, ‖(B⁻¹.transpose *ᵥ (fun k => (y k : ℚ_[2]))) i‖ ≤
      (2 : ℝ) ^ (∑ k : Fin 5, -(e (i.succAbove k) : ℤ)) := by
    intro i
    have hi := hyn i
    simpa only [sourceExponent6, e, B, Nat.cast_ofNat] using hi
  have hd := native_pairing_dvd6 2 B hB e (R.w q j.castSucc : Fin 6 → ℤ) y hx hyN
  exact hd


theorem source_pairing_p3_6
    (R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV)
    (h3 : A3.det = 1) (q : V) (y : Fin 6 → ℤ)
    (hy : sourceAuxiliaryInteger6 R q y) (j : Fin 5) :
    (3 : ℤ) ^ (∑ i : Fin 6, Nat.ceil
      (JSP000334.qThreshold 3 q.val (pairWeights42 c3 i))) ∣
      integerPairing6 (R.w q j.castSucc : Fin 6 → ℤ) y := by
  let B : Matrix (Fin 6) (Fin 6) ℚ_[3] := finiteMatrix 3 A3
  let e : Fin 6 → ℕ := fun i => Nat.ceil
    (JSP000334.qThreshold 3 q.val (pairWeights42 c3 i))
  have hB : B.det ≠ 0 := by
    rw [finite_matrix_det_one6 3 A3 h3]
    norm_num
  have hxall := source_first_five_integer_bounds6 R q
  rcases hy with ⟨_, _, hy3⟩
  have hyn := dual_bounds_native6 3 B y (sourceExponent6 3 q.val c3) hy3
  have hx : ∀ i, ‖(B *ᵥ
      (fun k => ((R.w q j.castSucc : Fin 6 → ℤ) k : ℚ_[3]))) i‖ ≤
        (3 : ℝ) ^ (-(e i : ℤ)) := by
    intro i
    have hi := hxall.2 j i
    simpa only [sourceExponent6, e, B, Nat.cast_ofNat] using hi
  have hyN : ∀ i, ‖(B⁻¹.transpose *ᵥ (fun k => (y k : ℚ_[3]))) i‖ ≤
      (3 : ℝ) ^ (∑ k : Fin 5, -(e (i.succAbove k) : ℤ)) := by
    intro i
    have hi := hyn i
    simpa only [sourceExponent6, e, B, Nat.cast_ofNat] using hi
  have hd := native_pairing_dvd6 3 B hB e (R.w q j.castSucc : Fin 6 → ℤ) y hx hyN
  exact hd


theorem source_pairing_primeProduct6
    (R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV)
    (h2 : A2.det = 1) (h3 : A3.det = 1) (q : V) (y : Fin 6 → ℤ)
    (hy : sourceAuxiliaryInteger6 R q y) (j : Fin 5) :
    (primeProduct6 q.val c2 c3 : ℤ) ∣
      integerPairing6 (R.w q j.castSucc : Fin 6 → ℤ) y := by
  have hcop : IsCoprime
      ((2 : ℤ) ^ (∑ i : Fin 6, Nat.ceil
        (JSP000334.qThreshold 2 q.val (pairWeights42 c2 i))))
      ((3 : ℤ) ^ (∑ i : Fin 6, Nat.ceil
        (JSP000334.qThreshold 3 q.val (pairWeights42 c3 i)))) :=
    IsCoprime.pow (show IsCoprime (2 : ℤ) 3 from ⟨-1, 1, by norm_num⟩)
  have hd := hcop.mul_dvd (source_pairing_p2_6 R h2 q y hy j)
    (source_pairing_p3_6 R h3 q y hy j)
  simpa only [primeProduct6, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using hd

end CompoundFeasibility.SchlickeweiIntegerPairing6
