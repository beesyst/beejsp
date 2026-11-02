import SubspaceBridge.OriginalVariableGap4
import SubspaceBridge.CompoundDualLine42
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.OriginalLastDualLiteral171

def rawMinima4 (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsUnit L)
    (Q : ℝ) (hQ : 1 < Q) (c0 c2 c3 : Fin 4 → ℝ) (j : Fin 4) : ℝ :=
  sInf {r : ℝ | ∃ v : Fin (j.val+1) → (Fin 4 → ℝ), LinearIndependent ℝ v ∧
    (∀ i, ∃ x : Fin 4 → ℤ,
      x ∈ sourceLattice4 A2 A3
        (fun k => Nat.ceil (JSP000334.qThreshold 2 Q (c2 k)))
        (fun k => Nat.ceil (JSP000334.qThreshold 3 Q (c3 k))) ∧ integerReal x = v i) ∧
    ∀ i, ‖originalCoordinates4 L hL Q hQ c0 (v i)‖ ≤ r}

def normalForm4 (b : Fin 4 → ℤ) : Module.Dual ℚ (Fin 4 → ℚ) :=
  ∑ i, (b i : ℚ) • LinearMap.proj i

theorem normalForm4_apply (b : Fin 4 → ℤ) (x : Fin 4 → ℚ) :
    normalForm4 b x = ∑ i, (b i : ℚ) * x i := by
  simp [normalForm4]

theorem normalForm4_nonzero (b : Fin 4 → ℤ) (hb : b ≠ 0) : normalForm4 b ≠ 0 := by
  intro hz
  apply hb
  funext i
  have hi := congrArg (fun f : Module.Dual ℚ (Fin 4 → ℚ) => f (Pi.single i 1)) hz
  simp [normalForm4,Pi.single_apply] at hi
  exact_mod_cast hi

def lastDual4 (u : Fin 4 → Fin 4 → ℚ) (hu : LinearIndependent ℚ u) : Fin 4 → ℚ :=
  fun i => rationalFrameDual42 u hu 3 (Pi.single i 1)

def firstThreeSpan4 (u : Fin 4 → Fin 4 → ℚ) : Submodule ℚ (Fin 4 → ℚ) :=
  Submodule.span ℚ (Set.range (fun i : Fin 3 => u i.castSucc))

theorem firstThreeSpan4_eq (u : Fin 4 → Fin 4 → ℚ) :
    firstThreeSpan4 u = Submodule.span ℚ {u 0,u 1,u 2} := by
  unfold firstThreeSpan4
  congr 1
  ext x
  simp only [Set.mem_range,Set.mem_insert_iff,Set.mem_singleton_iff]
  constructor
  · rintro ⟨i,rfl⟩
    fin_cases i <;> simp
  · rintro (rfl | rfl | rfl)
    · exact ⟨0,rfl⟩
    · exact ⟨1,rfl⟩
    · exact ⟨2,rfl⟩

theorem firstThreeSpan4_finrank (u : Fin 4 → Fin 4 → ℚ) (hu : LinearIndependent ℚ u) :
    Module.finrank ℚ (firstThreeSpan4 u) = 3 := by
  simpa [firstThreeSpan4] using finrank_span_eq_card (hu.comp Fin.castSucc (Fin.castSucc_injective 3))

theorem lastDual4_nonzero (u : Fin 4 → Fin 4 → ℚ) (hu : LinearIndependent ℚ u) :
    lastDual4 u hu ≠ 0 := by
  intro hz
  have hf : rationalFrameDual42 u hu 3 = 0 := by
    apply LinearMap.ext
    intro x
    rw [functional_coordinates42]
    change (∑ i, x i * lastDual4 u hu i) = 0
    simp [hz]
  have hp := rationalFrameDual42_pairing u hu 3 3
  rw [hf] at hp
  norm_num at hp

theorem lastDual4_kernel (u : Fin 4 → Fin 4 → ℚ) (hu : LinearIndependent ℚ u) :
    LinearMap.ker (rationalFrameDual42 u hu 3) = firstThreeSpan4 u := by
  apply le_antisymm
  · intro x hx
    have hz : (rationalFrameBasis42 u hu).repr x 3 = 0 := by
      rw [← Basis.dualBasis_apply]
      exact (show rationalFrameDual42 u hu 3 x = 0 from hx)
    have he := (rationalFrameBasis42 u hu).sum_repr x
    rw [Fin.sum_univ_castSucc,show Fin.last 3 = (3 : Fin 4) from rfl,
      hz,zero_smul,add_zero] at he
    rw [← he]
    apply Submodule.sum_mem
    intro i _
    apply Submodule.smul_mem
    rw [rationalFrameBasis42_apply]
    exact Submodule.subset_span ⟨i,rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    change rationalFrameDual42 u hu 3 (u i.castSucc) = 0
    rw [rationalFrameDual42_pairing,if_neg]
    intro h
    have := congrArg Fin.val h
    simp at this
    omega

theorem functional_lastDual4 (u : Fin 4 → Fin 4 → ℚ) (hu : LinearIndependent ℚ u)
    (f : Module.Dual ℚ (Fin 4 → ℚ)) (hf : ∀ i : Fin 3, f (u i.castSucc) = 0) :
    f = f (u 3) • rationalFrameDual42 u hu 3 := by
  apply (rationalFrameBasis42 u hu).ext
  intro j
  rw [rationalFrameBasis42_apply,LinearMap.smul_apply,rationalFrameDual42_pairing]
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp
  · rw [hf]
    simp [show i.castSucc ≠ (3 : Fin 4) by
      intro h
      have := congrArg Fin.val h
      simp at this
      omega]

def integerLastDual4 (u : Fin 4 → Fin 4 → ℤ) : Fin 4 → ℤ :=
  fun i => Matrix.adjugate (u : Matrix (Fin 4) (Fin 4) ℤ) i 3

theorem integerLastDual4_pairing (u : Fin 4 → Fin 4 → ℤ) (j : Fin 4) :
    ∑ i, u j i * integerLastDual4 u i =
      if j = 3 then Matrix.det (u : Matrix (Fin 4) (Fin 4) ℤ) else 0 := by
  have he := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℤ => M j 3)
    (Matrix.mul_adjugate (u : Matrix (Fin 4) (Fin 4) ℤ))
  simpa [Matrix.mul_apply,integerLastDual4,Matrix.smul_apply,Matrix.one_apply] using he

theorem fixed_line_kernel4 (u : Fin 4 → Fin 4 → ℚ) (hu : LinearIndependent ℚ u)
    (b : Fin 4 → ℤ) (hb : b ≠ 0)
    (hline : Submodule.span ℚ {lastDual4 u hu} =
      Submodule.span ℚ {fun i => (b i : ℚ)}) :
    normalForm4 b ≠ 0 ∧ LinearMap.ker (normalForm4 b) = firstThreeSpan4 u ∧
      Module.finrank ℚ (LinearMap.ker (normalForm4 b)) = 3 := by
  have hm : (fun i => (b i : ℚ)) ∈ Submodule.span ℚ {lastDual4 u hu} := by
    rw [hline]
    exact Submodule.subset_span (Set.mem_singleton _)
  obtain ⟨a,ha⟩ := Submodule.mem_span_singleton.mp hm
  have he : normalForm4 b = a • rationalFrameDual42 u hu 3 := by
    apply LinearMap.ext
    intro x
    rw [normalForm4_apply,LinearMap.smul_apply,
      functional_coordinates42 (rationalFrameDual42 u hu 3) x]
    simp only [LinearMap.smul_apply,smul_eq_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    have hi := congrFun ha i
    change a * lastDual4 u hu i = (b i : ℚ) at hi
    rw [← hi]
    dsimp [lastDual4]
    ring
  have hn : a ≠ 0 := by
    intro hz
    exact normalForm4_nonzero b hb (by rw [he,hz,zero_smul])
  have hk : LinearMap.ker (normalForm4 b) = firstThreeSpan4 u := by
    rw [he,LinearMap.ker_smul _ _ hn,lastDual4_kernel]
  exact ⟨normalForm4_nonzero b hb,hk,hk ▸ firstThreeSpan4_finrank u hu⟩

theorem selected_j2_gap4
    (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ)
    (hL : IsUnit L) (c0 c2 c3 : Fin 4 → ℝ) (delta : ℝ)
    (V : Set ℝ) (hQV : ∀ Q ∈ V, 1 < Q) (j : Fin 3) (hj : j = 2)
    (hgap : ∀ (Q : ℝ) (hQ : Q ∈ V),
      rawMinima4 A2 A3 L hL Q (hQV Q hQ) c0 c2 c3 j.castSucc <
        rawMinima4 A2 A3 L hL Q (hQV Q hQ) c0 c2 c3 j.succ * Q^(-delta)) :
    ∀ (Q : ℝ) (hQ : Q ∈ V),
      rawMinima4 A2 A3 L hL Q (hQV Q hQ) c0 c2 c3 2 <
        rawMinima4 A2 A3 L hL Q (hQV Q hQ) c0 c2 c3 3 * Q^(-delta) := by
  subst j
  exact hgap

theorem source_original_last_dual_frame4
    (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ) (L : Matrix (Fin 4) (Fin 4) ℝ)
    (hL : IsUnit L) (c0 c2 c3 : Fin 4 → ℝ) (delta : ℝ)
    (V : Set ℝ) (hV : ¬ BddAbove V) (hQV : ∀ Q ∈ V, 1 < Q)
    (hgap : ∀ (Q : ℝ) (hQ : Q ∈ V),
      rawMinima4 A2 A3 L hL Q (hQV Q hQ) c0 c2 c3 2 <
        rawMinima4 A2 A3 L hL Q (hQV Q hQ) c0 c2 c3 3 * Q^(-delta)) :
    ∃ u : (q : V) → Fin 4 → originalSourceGroup4 A2 A3 q.val c2 c3,
      ¬ BddAbove V ∧ ∀ q : V,
      LinearIndependent ℝ (fun j => integerReal (u q j : Fin 4 → ℤ)) ∧
      ∃ hu : LinearIndependent ℚ (fun j i => ((u q j : Fin 4 → ℤ) i : ℚ)),
      (∀ j, coordinateGauge4 (originalCoordinates4 L hL q.val (hQV q.val q.property) c0)
        (integerReal (u q j : Fin 4 → ℤ)) =
          rawMinima4 A2 A3 L hL q.val (hQV q.val q.property) c0 c2 c3 j) ∧
      (∀ j, 0 < rawMinima4 A2 A3 L hL q.val (hQV q.val q.property) c0 c2 c3 j) ∧
      Monotone (rawMinima4 A2 A3 L hL q.val (hQV q.val q.property) c0 c2 c3) ∧
      rawMinima4 A2 A3 L hL q.val (hQV q.val q.property) c0 c2 c3 2 <
        rawMinima4 A2 A3 L hL q.val (hQV q.val q.property) c0 c2 c3 3 * q.val^(-delta) ∧
      lastDual4 (fun j i => ((u q j : Fin 4 → ℤ) i : ℚ)) hu ≠ 0 ∧
      LinearMap.ker (rationalFrameDual42 (fun j i => ((u q j : Fin 4 → ℤ) i : ℚ)) hu 3) =
        firstThreeSpan4 (fun j i => ((u q j : Fin 4 → ℤ) i : ℚ)) ∧
      Module.finrank ℚ (firstThreeSpan4 (fun j i => ((u q j : Fin 4 → ℤ) i : ℚ))) = 3 := by
  have hex (q : V) := exists_sourceMinima4_attaining A2 A3 L hL q.val
    (hQV q.val q.property) c0 c2 c3
  choose u hu hp hm ha hpoint using hex
  refine ⟨u,hV,?_⟩
  intro q
  have hrat := integral_frame_rational_independent (fun j => (u q j : Fin 4 → ℤ)) (hu q)
  exact ⟨hu q,hrat,ha q,hp q,hm q,hgap q.val q.property,
    lastDual4_nonzero _ hrat,lastDual4_kernel _ hrat,firstThreeSpan4_finrank _ hrat⟩

end CompoundFeasibility.OriginalLastDualLiteral171

#print axioms CompoundFeasibility.OriginalLastDualLiteral171.normalForm4
#print axioms CompoundFeasibility.OriginalLastDualLiteral171.normalForm4_apply
#print axioms CompoundFeasibility.OriginalLastDualLiteral171.normalForm4_nonzero
#print axioms CompoundFeasibility.OriginalLastDualLiteral171.lastDual4
#print axioms CompoundFeasibility.OriginalLastDualLiteral171.firstThreeSpan4
#print axioms CompoundFeasibility.OriginalLastDualLiteral171.firstThreeSpan4_eq
#print axioms CompoundFeasibility.OriginalLastDualLiteral171.firstThreeSpan4_finrank
#print axioms CompoundFeasibility.OriginalLastDualLiteral171.lastDual4_nonzero
#print axioms CompoundFeasibility.OriginalLastDualLiteral171.lastDual4_kernel
#print axioms CompoundFeasibility.OriginalLastDualLiteral171.functional_lastDual4
#print axioms CompoundFeasibility.OriginalLastDualLiteral171.integerLastDual4
#print axioms CompoundFeasibility.OriginalLastDualLiteral171.integerLastDual4_pairing
#print axioms CompoundFeasibility.OriginalLastDualLiteral171.fixed_line_kernel4
#print axioms CompoundFeasibility.OriginalLastDualLiteral171.selected_j2_gap4
#print axioms CompoundFeasibility.OriginalLastDualLiteral171.source_original_last_dual_frame4
