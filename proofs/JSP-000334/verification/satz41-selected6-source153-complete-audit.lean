import SubspaceBridge.SchlickeweiSatz41Selected6
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.Satz41Selected152Bridges
open SourceMixed6 SourceReadiness6 SourceNormalHeight SourceNormalIndex SchlickeweiDualVanishing6

theorem dual_expansion6 (u : Fin 6 → Fin 6 → ℤ)
    (hu : LinearIndependent ℚ (fun j i => (u j i : ℚ))) :
    dualVector6 u hu = fun k =>
      rationalFrameDual42 (fun j i => (u j i : ℚ)) hu 5 (Pi.single k 1) := by
  funext k
  rfl

variable {A2 A3 : Matrix (Fin 4) (Fin 4) ℚ} {L : Matrix (Fin 4) (Fin 4) ℝ}
  {hL : IsUnit L} {c0 c2 c3 : Fin 4 → ℝ} {delta4 : ℝ} {V : Set ℝ}
  {hQV : ∀ q ∈ V, 1 < q}

theorem source_dual_expansion6
    (R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV) (q : V) :
    dualVector6 (fun j => (R.w q j : Fin 6 → ℤ)) (sourceFrameIndependent6 R q) =
      fun k => rationalFrameDual42 (fun j i => ((R.w q j : Fin 6 → ℤ) i : ℚ))
        (sourceFrameIndependent6 R q) 5 (Pi.single k 1) := by
  exact dual_expansion6 _ (sourceFrameIndependent6 R q)

theorem index_expansion6 {n : ℕ} (G : AddSubgroup (Fin n → ℤ)) (w : Fin n → G) :
    SourceRelativeIndex6.frameRelativeIndex G w =
      (Submodule.span ℤ (Set.range w)).toAddSubgroup.index := by
  rfl

theorem admissible_expansion6 (c : Fin 3 → Fin 6 → ℝ) (delta : ℝ) :
    admissibleMixed6 c delta =
      Finset.univ.filter (fun s : Fin 3 → Fin 6 => -(3*delta)/4 ≤ ∑ tau, c tau (s tau)) := by
  rfl

theorem exponent_expansion6 (p : ℕ) (q : ℝ) (c : Fin 4 → ℝ) (i : Fin 6) :
    SchlickeweiEquation4116.sourceExponent6 p q c i =
      -(Nat.ceil (JSP000334.qThreshold p q (pairWeights42 c i)) : ℤ) := by
  rfl

theorem matrix_expansion6 (p : ℕ) [Fact p.Prime] (A : Matrix (Fin 4) (Fin 4) ℚ) :
    Auxiliary6.SourceExpansion.finiteMatrix p A = (compound A).map (algebraMap ℚ ℚ_[p]) := by
  rfl

theorem published_expansion6 (A2 A3 : Matrix (Fin 4) (Fin 4) ℚ)
    (L : Matrix (Fin 4) (Fin 4) ℝ) (D : Fin 6 → ℚ) (s : Fin 3 → Fin 6) :
    SchlickeweiEquation4126.publishedDualProduct6 A2 A3 L D s =
      ‖∑ k, algebraMap ℚ ℝ (D k) * (compound L)⁻¹.transpose (s 0) k‖ *
      ‖∑ k, algebraMap ℚ ℚ_[2] (D k) *
        ((compound A2).map (algebraMap ℚ ℚ_[2]))⁻¹.transpose (s 1) k‖ *
      ‖∑ k, algebraMap ℚ ℚ_[3] (D k) *
        ((compound A3).map (algebraMap ℚ ℚ_[3]))⁻¹.transpose (s 2) k‖ := by
  unfold SchlickeweiEquation4126.publishedDualProduct6 dualFormValue6
  rw [matrix_expansion6, matrix_expansion6]


theorem finite_bound_transport6 (p : ℕ) [Fact p.Prime] (N : ℕ)
    (B B' : Matrix (Fin 6) (Fin 6) ℚ_[p]) (D : Fin 6 → ℚ)
    (f f' : Fin 6 → ℤ) (i : Fin 6) (hB : B = B') (hf : f = f')
    (h : ‖∑ k, ((N : ℚ_[p]) * algebraMap ℚ ℚ_[p] (D k)) * B⁻¹.transpose i k‖ ≤
      (p : ℝ) ^ (∑ k : Fin 5, f (i.succAbove k))) :
    ‖∑ k, ((N : ℚ_[p]) * algebraMap ℚ ℚ_[p] (D k)) * B'⁻¹.transpose i k‖ ≤
      (p : ℝ) ^ (∑ k : Fin 5, f' (i.succAbove k)) := by
  subst B'
  subst f'
  exact h


open SchlickeweiEquation4116
def SourceLocal6 (R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV) (q : V) : Prop :=
let G := directCompoundGroup42 A2 A3 q.val c2 c3
let Q := q.val ^ (11 : ℕ)
let J := SourceRelativeIndex6.frameRelativeIndex G (R.w q)
let d := ZLattice.covolume (integerRealImage G)
let v : Matrix (Fin 6) (Fin 6) ℤ := Matrix.of (fun j => (R.w q j : Fin 6 → ℤ))
let D := dualVector6 (fun j => (R.w q j : Fin 6 → ℤ)) (sourceFrameIndependent6 R q)
sourceFrames6 A2 A3 L hL c0 c2 c3 V hQV R.delta R.c R.sigma R.widths_pos R.w q ∧
sourceNormals6 A2 A3 c2 c3 V R.w R.M R.a q ∧
Finite (G ⧸ Submodule.span ℤ (Set.range (R.w q))) ∧
0 < J ∧ J * G.index = v.det.natAbs ∧
|(v.det : ℝ)| = (J : ℝ) * d ∧ v.det ≠ 0 ∧ 0 < d ∧
d = (G.index : ℝ) ∧ ((J * G.index : ℕ) : ℝ) = (J : ℝ) * d ∧
(∀ i, sourceExponent6 2 q.val c2 i =
  -(Nat.ceil (JSP000334.qThreshold 2 Q (R.c 1 i)) : ℤ)) ∧
(∀ i, sourceExponent6 3 q.val c3 i =
  -(Nat.ceil (JSP000334.qThreshold 3 Q (R.c 2 i)) : ℤ)) ∧
(∀ i, ‖∑ k, ((J : ℝ) * d * algebraMap ℚ ℝ (D k)) *
    (compound L)⁻¹.transpose i k‖ ≤
  120 * (Q ^ (R.c 0 i))⁻¹ * d * Q ^ (-5 * R.delta)) ∧
(∀ i, (‖∑ k, (((J * G.index : ℕ) : ℚ_[2]) * algebraMap ℚ ℚ_[2] (D k)) *
    (Auxiliary6.SourceExpansion.finiteMatrix 2 A2)⁻¹.transpose i k‖ ≤
  (2 : ℝ) ^ (∑ k : Fin 5, sourceExponent6 2 q.val c2 (i.succAbove k))) ∧
  (‖∑ k, (((J * G.index : ℕ) : ℚ_[3]) * algebraMap ℚ ℚ_[3] (D k)) *
    (Auxiliary6.SourceExpansion.finiteMatrix 3 A3)⁻¹.transpose i k‖ ≤
  (3 : ℝ) ^ (∑ k : Fin 5, sourceExponent6 3 q.val c3 (i.succAbove k)))) ∧
∃ a : ℚ, a ≠ 0 ∧
  normalForm6 (R.M q) = a • rationalFrameDual42
    (fun j i => ((R.w q j : Fin 6 → ℤ) i : ℚ)) (sourceFrameIndependent6 R q) 5 ∧
  (∀ k, (R.M q k : ℚ) = a * D k) ∧
  (∀ k, D k = a⁻¹ * (R.M q k : ℚ)) ∧
  ∀ s ∈ admissibleMixed6 R.c (R.delta/2),
    dualNormProduct6 A2 A3 L D s = 0 ∧
    SchlickeweiEquation4126.publishedDualProduct6 A2 A3 L D s = 0

def LiteralA6 (R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV) (q : V) : Prop :=
let G := directCompoundGroup42 A2 A3 q.val c2 c3
let Q := q.val ^ (11 : ℕ)
let J := (Submodule.span ℤ (Set.range (R.w q))).toAddSubgroup.index
let d := ZLattice.covolume (integerRealImage G)
let v : Matrix (Fin 6) (Fin 6) ℤ := Matrix.of (fun j => (R.w q j : Fin 6 → ℤ))
let D := (fun k => rationalFrameDual42 (fun j a => ((R.w q j : Fin 6 → ℤ) a : ℚ)) (sourceFrameIndependent6 R q) 5 (Pi.single k 1))
sourceFrames6 A2 A3 L hL c0 c2 c3 V hQV R.delta R.c R.sigma R.widths_pos R.w q ∧
sourceNormals6 A2 A3 c2 c3 V R.w R.M R.a q

theorem component_A6 (R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV) (q : V) (h : SourceLocal6 R q) : LiteralA6 R q := by
  rcases h with ⟨hA, hN, hquot, hpos, hdet, habs, hne, hdpos,
    hdindex, hscale, he2, he3, hreal, hfinite, hdual⟩
  exact ⟨hA, hN⟩

def LiteralB6 (R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV) (q : V) : Prop :=
let G := directCompoundGroup42 A2 A3 q.val c2 c3
let Q := q.val ^ (11 : ℕ)
let J := (Submodule.span ℤ (Set.range (R.w q))).toAddSubgroup.index
let d := ZLattice.covolume (integerRealImage G)
let v : Matrix (Fin 6) (Fin 6) ℤ := Matrix.of (fun j => (R.w q j : Fin 6 → ℤ))
let D := (fun k => rationalFrameDual42 (fun j a => ((R.w q j : Fin 6 → ℤ) a : ℚ)) (sourceFrameIndependent6 R q) 5 (Pi.single k 1))
Finite (G ⧸ Submodule.span ℤ (Set.range (R.w q))) ∧
0 < J

theorem component_B6 (R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV) (q : V) (h : SourceLocal6 R q) : LiteralB6 R q := by
  rcases h with ⟨hA, hN, hquot, hpos, hdet, habs, hne, hdpos,
    hdindex, hscale, he2, he3, hreal, hfinite, hdual⟩
  rw [index_expansion6] at hpos
  exact ⟨hquot, hpos⟩

def LiteralC6 (R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV) (q : V) : Prop :=
let G := directCompoundGroup42 A2 A3 q.val c2 c3
let Q := q.val ^ (11 : ℕ)
let J := (Submodule.span ℤ (Set.range (R.w q))).toAddSubgroup.index
let d := ZLattice.covolume (integerRealImage G)
let v : Matrix (Fin 6) (Fin 6) ℤ := Matrix.of (fun j => (R.w q j : Fin 6 → ℤ))
let D := (fun k => rationalFrameDual42 (fun j a => ((R.w q j : Fin 6 → ℤ) a : ℚ)) (sourceFrameIndependent6 R q) 5 (Pi.single k 1))
J * G.index = v.det.natAbs ∧
|(v.det : ℝ)| = (J : ℝ) * d ∧
v.det ≠ 0 ∧
0 < d

theorem component_C6 (R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV) (q : V) (h : SourceLocal6 R q) : LiteralC6 R q := by
  rcases h with ⟨hA, hN, hquot, hpos, hdet, habs, hne, hdpos,
    hdindex, hscale, he2, he3, hreal, hfinite, hdual⟩
  rw [index_expansion6] at hdet habs
  exact ⟨hdet, habs, hne, hdpos⟩

def LiteralD6 (R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV) (q : V) : Prop :=
let G := directCompoundGroup42 A2 A3 q.val c2 c3
let Q := q.val ^ (11 : ℕ)
let J := (Submodule.span ℤ (Set.range (R.w q))).toAddSubgroup.index
let d := ZLattice.covolume (integerRealImage G)
let v : Matrix (Fin 6) (Fin 6) ℤ := Matrix.of (fun j => (R.w q j : Fin 6 → ℤ))
let D := (fun k => rationalFrameDual42 (fun j a => ((R.w q j : Fin 6 → ℤ) a : ℚ)) (sourceFrameIndependent6 R q) 5 (Pi.single k 1))
d = (G.index : ℝ) ∧
((J * G.index : ℕ) : ℝ) = (J : ℝ) * d

theorem component_D6 (R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV) (q : V) (h : SourceLocal6 R q) : LiteralD6 R q := by
  rcases h with ⟨hA, hN, hquot, hpos, hdet, habs, hne, hdpos,
    hdindex, hscale, he2, he3, hreal, hfinite, hdual⟩
  rw [index_expansion6] at hscale
  exact ⟨hdindex, hscale⟩

def LiteralE6 (R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV) (q : V) : Prop :=
let G := directCompoundGroup42 A2 A3 q.val c2 c3
let Q := q.val ^ (11 : ℕ)
let J := (Submodule.span ℤ (Set.range (R.w q))).toAddSubgroup.index
let d := ZLattice.covolume (integerRealImage G)
let v : Matrix (Fin 6) (Fin 6) ℤ := Matrix.of (fun j => (R.w q j : Fin 6 → ℤ))
let D := (fun k => rationalFrameDual42 (fun j a => ((R.w q j : Fin 6 → ℤ) a : ℚ)) (sourceFrameIndependent6 R q) 5 (Pi.single k 1))
(∀ i, (-(Nat.ceil (JSP000334.qThreshold 2 q.val (pairWeights42 c2 i)) : ℤ)) =
  -(Nat.ceil (JSP000334.qThreshold 2 Q (R.c 1 i)) : ℤ)) ∧
(∀ i, (-(Nat.ceil (JSP000334.qThreshold 3 q.val (pairWeights42 c3 i)) : ℤ)) =
  -(Nat.ceil (JSP000334.qThreshold 3 Q (R.c 2 i)) : ℤ))

theorem component_E6 (R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV) (q : V) (h : SourceLocal6 R q) : LiteralE6 R q := by
  rcases h with ⟨hA, hN, hquot, hpos, hdet, habs, hne, hdpos,
    hdindex, hscale, he2, he3, hreal, hfinite, hdual⟩
  simp only [exponent_expansion6] at he2 he3
  exact ⟨he2, he3⟩

def LiteralF6 (R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV) (q : V) : Prop :=
let G := directCompoundGroup42 A2 A3 q.val c2 c3
let Q := q.val ^ (11 : ℕ)
let J := (Submodule.span ℤ (Set.range (R.w q))).toAddSubgroup.index
let d := ZLattice.covolume (integerRealImage G)
let v : Matrix (Fin 6) (Fin 6) ℤ := Matrix.of (fun j => (R.w q j : Fin 6 → ℤ))
let D := (fun k => rationalFrameDual42 (fun j a => ((R.w q j : Fin 6 → ℤ) a : ℚ)) (sourceFrameIndependent6 R q) 5 (Pi.single k 1))
(∀ i, ‖∑ k, ((J : ℝ) * d * algebraMap ℚ ℝ (D k)) *
    (compound L)⁻¹.transpose i k‖ ≤
  120 * (Q ^ (R.c 0 i))⁻¹ * d * Q ^ (-5 * R.delta))

theorem component_F6 (R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV) (q : V) (h : SourceLocal6 R q) : LiteralF6 R q := by
  rcases h with ⟨hA, hN, hquot, hpos, hdet, habs, hne, hdpos,
    hdindex, hscale, he2, he3, hreal, hfinite, hdual⟩
  rw [index_expansion6, source_dual_expansion6 R q] at hreal
  exact hreal

def FiniteBound153 (p : ℕ) [Fact p.Prime] (N : ℕ) (D : Fin 6 → ℚ)
    (B : Matrix (Fin 6) (Fin 6) ℚ_[p]) (f : Fin 6 → ℤ) (i : Fin 6) : Prop :=
  ‖∑ k, ((N : ℚ_[p]) * algebraMap ℚ ℚ_[p] (D k)) * B⁻¹.transpose i k‖ ≤
    (p : ℝ) ^ (∑ k : Fin 5, f (i.succAbove k))

theorem finite_bound_symbolic153 (p : ℕ) [Fact p.Prime] (N : ℕ) (D : Fin 6 → ℚ)
    (B B' : Matrix (Fin 6) (Fin 6) ℚ_[p]) (f f' : Fin 6 → ℤ) (i : Fin 6)
    (hB : B = B') (hf : f = f') (h : FiniteBound153 p N D B f i) :
    FiniteBound153 p N D B' f' i := by
  exact finite_bound_transport6 p N B B' D f f' i hB hf h

theorem finite_bound_coordinates153 (p : ℕ) [Fact p.Prime] (N N' : ℕ)
    (D D' : Fin 6 → ℚ) (B : Matrix (Fin 6) (Fin 6) ℚ_[p])
    (f : Fin 6 → ℤ) (i : Fin 6) (hN : N = N') (hD : D = D')
    (h : FiniteBound153 p N D B f i) : FiniteBound153 p N' D' B f i := by
  cases hN
  cases hD
  exact h
theorem finite_bound_two153 (N : ℕ) (D : Fin 6 → ℚ)
    (B : Matrix (Fin 6) (Fin 6) ℚ_[2]) (f : Fin 6 → ℤ) (i : Fin 6) :
    FiniteBound153 2 N D B f i ↔
      ‖∑ k, ((N : ℚ_[2]) * algebraMap ℚ ℚ_[2] (D k)) * B⁻¹.transpose i k‖ ≤
        (2 : ℝ) ^ (∑ k : Fin 5, f (i.succAbove k)) := by
  simp only [FiniteBound153, Nat.cast_ofNat]

theorem finite_bound_three153 (N : ℕ) (D : Fin 6 → ℚ)
    (B : Matrix (Fin 6) (Fin 6) ℚ_[3]) (f : Fin 6 → ℤ) (i : Fin 6) :
    FiniteBound153 3 N D B f i ↔
      ‖∑ k, ((N : ℚ_[3]) * algebraMap ℚ ℚ_[3] (D k)) * B⁻¹.transpose i k‖ ≤
        (3 : ℝ) ^ (∑ k : Fin 5, f (i.succAbove k)) := by
  simp only [FiniteBound153, Nat.cast_ofNat]

theorem boundary_p2_153 (R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV) (q : V)
    (h : SourceLocal6 R q) (i : Fin 6) :
    let G := directCompoundGroup42 A2 A3 q.val c2 c3
    let N : ℕ := (Submodule.span ℤ (Set.range (R.w q))).toAddSubgroup.index * G.index
    let D : Fin 6 → ℚ := fun k => rationalFrameDual42
      (fun j a => ((R.w q j : Fin 6 → ℤ) a : ℚ)) (sourceFrameIndependent6 R q) 5 (Pi.single k 1)
    let B : Matrix (Fin 6) (Fin 6) ℚ_[2] := (compound A2).map (algebraMap ℚ ℚ_[2])
    let f : Fin 6 → ℤ := fun k => -(Nat.ceil
      (JSP000334.qThreshold 2 q.val (pairWeights42 c2 k)) : ℤ)
    FiniteBound153 2 N D B f i := by
  rcases h with ⟨hA, hN0, hquot, hpos, hdet, habs, hne, hdpos,
    hdindex, hscale, he2, he3, hreal, hfinite, hdual⟩
  let G := directCompoundGroup42 A2 A3 q.val c2 c3
  let J : ℕ := SourceRelativeIndex6.frameRelativeIndex G (R.w q)
  let J' : ℕ := (Submodule.span ℤ (Set.range (R.w q))).toAddSubgroup.index
  let N : ℕ := J * G.index
  let N' : ℕ := J' * G.index
  let D : Fin 6 → ℚ := dualVector6
    (fun j => (R.w q j : Fin 6 → ℤ)) (sourceFrameIndependent6 R q)
  let D' : Fin 6 → ℚ := fun k => rationalFrameDual42
    (fun j a => ((R.w q j : Fin 6 → ℤ) a : ℚ)) (sourceFrameIndependent6 R q) 5 (Pi.single k 1)
  let B : Matrix (Fin 6) (Fin 6) ℚ_[2] := Auxiliary6.SourceExpansion.finiteMatrix 2 A2
  let B' : Matrix (Fin 6) (Fin 6) ℚ_[2] := (compound A2).map (algebraMap ℚ ℚ_[2])
  let f : Fin 6 → ℤ := SchlickeweiEquation4116.sourceExponent6 2 q.val c2
  let f' : Fin 6 → ℤ := fun k => -(Nat.ceil
    (JSP000334.qThreshold 2 q.val (pairWeights42 c2 k)) : ℤ)
  have hN : N = N' := congrArg (fun j : ℕ => j * G.index) (index_expansion6 G (R.w q))
  have hD : D = D' := source_dual_expansion6 R q
  have hB : B = B' := matrix_expansion6 2 A2
  have hf : f = f' := by
    funext k
    exact exponent_expansion6 2 q.val c2 k
  have hraw := (hfinite i).1
  have hsource : FiniteBound153 2 N D B f i := by
    apply (finite_bound_two153 N D B f i).mpr
    with_reducible exact hraw
  have hmatrix : FiniteBound153 2 N D B' f' i :=
    finite_bound_symbolic153 2 N D B B' f f' i hB hf hsource
  have htarget : FiniteBound153 2 N' D' B' f' i :=
    finite_bound_coordinates153 2 N N' D D' B' f' i hN hD hmatrix
  exact htarget

theorem boundary_p3_153 (R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV) (q : V)
    (h : SourceLocal6 R q) (i : Fin 6) :
    let G := directCompoundGroup42 A2 A3 q.val c2 c3
    let N : ℕ := (Submodule.span ℤ (Set.range (R.w q))).toAddSubgroup.index * G.index
    let D : Fin 6 → ℚ := fun k => rationalFrameDual42
      (fun j a => ((R.w q j : Fin 6 → ℤ) a : ℚ)) (sourceFrameIndependent6 R q) 5 (Pi.single k 1)
    let B : Matrix (Fin 6) (Fin 6) ℚ_[3] := (compound A3).map (algebraMap ℚ ℚ_[3])
    let f : Fin 6 → ℤ := fun k => -(Nat.ceil
      (JSP000334.qThreshold 3 q.val (pairWeights42 c3 k)) : ℤ)
    FiniteBound153 3 N D B f i := by
  rcases h with ⟨hA, hN0, hquot, hpos, hdet, habs, hne, hdpos,
    hdindex, hscale, he2, he3, hreal, hfinite, hdual⟩
  let G := directCompoundGroup42 A2 A3 q.val c2 c3
  let J : ℕ := SourceRelativeIndex6.frameRelativeIndex G (R.w q)
  let J' : ℕ := (Submodule.span ℤ (Set.range (R.w q))).toAddSubgroup.index
  let N : ℕ := J * G.index
  let N' : ℕ := J' * G.index
  let D : Fin 6 → ℚ := dualVector6
    (fun j => (R.w q j : Fin 6 → ℤ)) (sourceFrameIndependent6 R q)
  let D' : Fin 6 → ℚ := fun k => rationalFrameDual42
    (fun j a => ((R.w q j : Fin 6 → ℤ) a : ℚ)) (sourceFrameIndependent6 R q) 5 (Pi.single k 1)
  let B : Matrix (Fin 6) (Fin 6) ℚ_[3] := Auxiliary6.SourceExpansion.finiteMatrix 3 A3
  let B' : Matrix (Fin 6) (Fin 6) ℚ_[3] := (compound A3).map (algebraMap ℚ ℚ_[3])
  let f : Fin 6 → ℤ := SchlickeweiEquation4116.sourceExponent6 3 q.val c3
  let f' : Fin 6 → ℤ := fun k => -(Nat.ceil
    (JSP000334.qThreshold 3 q.val (pairWeights42 c3 k)) : ℤ)
  have hN : N = N' := congrArg (fun j : ℕ => j * G.index) (index_expansion6 G (R.w q))
  have hD : D = D' := source_dual_expansion6 R q
  have hB : B = B' := matrix_expansion6 3 A3
  have hf : f = f' := by
    funext k
    exact exponent_expansion6 3 q.val c3 k
  have hraw := (hfinite i).2
  have hsource : FiniteBound153 3 N D B f i := by
    apply (finite_bound_three153 N D B f i).mpr
    with_reducible exact hraw
  have hmatrix : FiniteBound153 3 N D B' f' i :=
    finite_bound_symbolic153 3 N D B B' f f' i hB hf hsource
  have htarget : FiniteBound153 3 N' D' B' f' i :=
    finite_bound_coordinates153 3 N N' D D' B' f' i hN hD hmatrix
  exact htarget

def LiteralG6 (R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV) (q : V) : Prop :=
let G := directCompoundGroup42 A2 A3 q.val c2 c3
let Q := q.val ^ (11 : ℕ)
let J := (Submodule.span ℤ (Set.range (R.w q))).toAddSubgroup.index
let d := ZLattice.covolume (integerRealImage G)
let v : Matrix (Fin 6) (Fin 6) ℤ := Matrix.of (fun j => (R.w q j : Fin 6 → ℤ))
let D := (fun k => rationalFrameDual42 (fun j a => ((R.w q j : Fin 6 → ℤ) a : ℚ)) (sourceFrameIndependent6 R q) 5 (Pi.single k 1))
(∀ i, (‖∑ k, (((J * G.index : ℕ) : ℚ_[2]) * algebraMap ℚ ℚ_[2] (D k)) *
    (((compound A2).map (algebraMap ℚ ℚ_[2])))⁻¹.transpose i k‖ ≤
  (2 : ℝ) ^ (∑ k : Fin 5, (-(Nat.ceil (JSP000334.qThreshold 2 q.val (pairWeights42 c2 (i.succAbove k))) : ℤ)))) ∧
  (‖∑ k, (((J * G.index : ℕ) : ℚ_[3]) * algebraMap ℚ ℚ_[3] (D k)) *
    (((compound A3).map (algebraMap ℚ ℚ_[3])))⁻¹.transpose i k‖ ≤
  (3 : ℝ) ^ (∑ k : Fin 5, (-(Nat.ceil (JSP000334.qThreshold 3 q.val (pairWeights42 c3 (i.succAbove k))) : ℤ)))))

theorem component_G6 (R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV)
    (q : V) (h : SourceLocal6 R q) : LiteralG6 R q := by
  let G := directCompoundGroup42 A2 A3 q.val c2 c3
  let N : ℕ := (Submodule.span ℤ (Set.range (R.w q))).toAddSubgroup.index * G.index
  let D : Fin 6 → ℚ := fun k => rationalFrameDual42
    (fun j a => ((R.w q j : Fin 6 → ℤ) a : ℚ)) (sourceFrameIndependent6 R q) 5 (Pi.single k 1)
  let B2 : Matrix (Fin 6) (Fin 6) ℚ_[2] := (compound A2).map (algebraMap ℚ ℚ_[2])
  let B3 : Matrix (Fin 6) (Fin 6) ℚ_[3] := (compound A3).map (algebraMap ℚ ℚ_[3])
  let f2 : Fin 6 → ℤ := fun k => -(Nat.ceil
    (JSP000334.qThreshold 2 q.val (pairWeights42 c2 k)) : ℤ)
  let f3 : Fin 6 → ℤ := fun k => -(Nat.ceil
    (JSP000334.qThreshold 3 q.val (pairWeights42 c3 k)) : ℤ)
  intro i
  constructor
  · have h2 : FiniteBound153 2 N D B2 f2 i := boundary_p2_153 R q h i
    have hraw := (finite_bound_two153 N D B2 f2 i).mp h2
    with_reducible exact hraw
  · have h3 : FiniteBound153 3 N D B3 f3 i := boundary_p3_153 R q h i
    have hraw := (finite_bound_three153 N D B3 f3 i).mp h3
    with_reducible exact hraw

def LiteralH6 (R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV) (q : V) : Prop :=
let G := directCompoundGroup42 A2 A3 q.val c2 c3
let Q := q.val ^ (11 : ℕ)
let J := (Submodule.span ℤ (Set.range (R.w q))).toAddSubgroup.index
let d := ZLattice.covolume (integerRealImage G)
let v : Matrix (Fin 6) (Fin 6) ℤ := Matrix.of (fun j => (R.w q j : Fin 6 → ℤ))
let D := (fun k => rationalFrameDual42 (fun j a => ((R.w q j : Fin 6 → ℤ) a : ℚ)) (sourceFrameIndependent6 R q) 5 (Pi.single k 1))
∃ a : ℚ, a ≠ 0 ∧
  normalForm6 (R.M q) = a • rationalFrameDual42
    (fun j i => ((R.w q j : Fin 6 → ℤ) i : ℚ)) (sourceFrameIndependent6 R q) 5 ∧
  (∀ k, (R.M q k : ℚ) = a * D k) ∧
  (∀ k, D k = a⁻¹ * (R.M q k : ℚ))

theorem component_H6 (R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV) (q : V) (h : SourceLocal6 R q) : LiteralH6 R q := by
  rcases h with ⟨hA, hN, hquot, hpos, hdet, habs, hne, hdpos,
    hdindex, hscale, he2, he3, hreal, hfinite, hdual⟩
  obtain ⟨a, ha, hform, hforward, hinverse, hzero⟩ := hdual
  rw [source_dual_expansion6 R q] at hforward hinverse
  exact ⟨a, ha, hform, hforward, hinverse⟩

def LiteralI6 (R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV) (q : V) : Prop :=
let G := directCompoundGroup42 A2 A3 q.val c2 c3
let Q := q.val ^ (11 : ℕ)
let J := (Submodule.span ℤ (Set.range (R.w q))).toAddSubgroup.index
let d := ZLattice.covolume (integerRealImage G)
let v : Matrix (Fin 6) (Fin 6) ℤ := Matrix.of (fun j => (R.w q j : Fin 6 → ℤ))
let D := (fun k => rationalFrameDual42 (fun j a => ((R.w q j : Fin 6 → ℤ) a : ℚ)) (sourceFrameIndependent6 R q) 5 (Pi.single k 1))
∀ s ∈ (Finset.univ.filter (fun s : Fin 3 → Fin 6 => -(3*(R.delta/2))/4 ≤ ∑ tau, R.c tau (s tau))),
    dualNormProduct6 A2 A3 L D s = 0

theorem component_I6 (R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV) (q : V) (h : SourceLocal6 R q) : LiteralI6 R q := by
  rcases h with ⟨hA, hN, hquot, hpos, hdet, habs, hne, hdpos,
    hdindex, hscale, he2, he3, hreal, hfinite, hdual⟩
  obtain ⟨a, ha, hform, hforward, hinverse, hzero⟩ := hdual
  intro s hs
  have hs0 : s ∈ admissibleMixed6 R.c (R.delta/2) := by
    rw [admissible_expansion6]
    exact hs
  have hz := (hzero s hs0).1
  rw [source_dual_expansion6 R q] at hz
  exact hz

def LiteralJ6 (R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV) (q : V) : Prop :=
let G := directCompoundGroup42 A2 A3 q.val c2 c3
let Q := q.val ^ (11 : ℕ)
let J := (Submodule.span ℤ (Set.range (R.w q))).toAddSubgroup.index
let d := ZLattice.covolume (integerRealImage G)
let v : Matrix (Fin 6) (Fin 6) ℤ := Matrix.of (fun j => (R.w q j : Fin 6 → ℤ))
let D := (fun k => rationalFrameDual42 (fun j a => ((R.w q j : Fin 6 → ℤ) a : ℚ)) (sourceFrameIndependent6 R q) 5 (Pi.single k 1))
∀ s ∈ (Finset.univ.filter (fun s : Fin 3 → Fin 6 => -(3*(R.delta/2))/4 ≤ ∑ tau, R.c tau (s tau))),
    (‖∑ k, algebraMap ℚ ℝ (D k) * (compound L)⁻¹.transpose (s 0) k‖ *
      ‖∑ k, algebraMap ℚ ℚ_[2] (D k) * ((compound A2).map (algebraMap ℚ ℚ_[2]))⁻¹.transpose (s 1) k‖ *
      ‖∑ k, algebraMap ℚ ℚ_[3] (D k) * ((compound A3).map (algebraMap ℚ ℚ_[3]))⁻¹.transpose (s 2) k‖) = 0

theorem component_J6 (R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV) (q : V) (h : SourceLocal6 R q) : LiteralJ6 R q := by
  rcases h with ⟨hA, hN, hquot, hpos, hdet, habs, hne, hdpos,
    hdindex, hscale, he2, he3, hreal, hfinite, hdual⟩
  obtain ⟨a, ha, hform, hforward, hinverse, hzero⟩ := hdual
  intro s hs
  have hs0 : s ∈ admissibleMixed6 R.c (R.delta/2) := by
    rw [admissible_expansion6]
    exact hs
  have hz := (hzero s hs0).2
  rw [source_dual_expansion6 R q] at hz
  rw [published_expansion6] at hz
  with_reducible exact hz

end CompoundFeasibility.Satz41Selected152Bridges
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.Satz41Selected151Literal
open SourceMixed6 SourceReadiness6 SourceNormalHeight SourceNormalIndex SchlickeweiDualVanishing6
open Satz41Selected152Bridges
variable {A2 A3 : Matrix (Fin 4) (Fin 4) ℚ} {L : Matrix (Fin 4) (Fin 4) ℝ}
  {hL : IsUnit L} {c0 c2 c3 : Fin 4 → ℝ} {delta4 : ℝ} {V : Set ℝ}
  {hQV : ∀ q ∈ V, 1 < q}
theorem complete_literal
    (R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV)
    (h2 : A2.det = 1) (h3 : A3.det = 1) (hLdet : L.det = 1) :
    ∃ B : ℝ, ((Finset.univ.filter (fun s : Fin 3 → Fin 6 => -(3*(R.delta/2))/4 ≤ ∑ tau, R.c tau (s tau)))).Nonempty ∧
      (∀ q : V, B < q.val → ∀ s ∈ (Finset.univ.filter (fun s : Fin 3 → Fin 6 => -(3*(R.delta/2))/4 ≤ ∑ tau, R.c tau (s tau))),
        actualNormProduct6 A2 A3 L (R.M q) s = 0) ∧
      ∀ q : V, B < q.val →
        let G := directCompoundGroup42 A2 A3 q.val c2 c3
        let Q := q.val ^ (11 : ℕ)
        let J := (Submodule.span ℤ (Set.range (R.w q))).toAddSubgroup.index
        let d := ZLattice.covolume (integerRealImage G)
        let v : Matrix (Fin 6) (Fin 6) ℤ := Matrix.of (fun j => (R.w q j : Fin 6 → ℤ))
        let D := (fun k => rationalFrameDual42 (fun j a => ((R.w q j : Fin 6 → ℤ) a : ℚ)) (sourceFrameIndependent6 R q) 5 (Pi.single k 1))
        sourceFrames6 A2 A3 L hL c0 c2 c3 V hQV R.delta R.c R.sigma R.widths_pos R.w q ∧
        sourceNormals6 A2 A3 c2 c3 V R.w R.M R.a q ∧
        Finite (G ⧸ Submodule.span ℤ (Set.range (R.w q))) ∧
        0 < J ∧ J * G.index = v.det.natAbs ∧
        |(v.det : ℝ)| = (J : ℝ) * d ∧ v.det ≠ 0 ∧ 0 < d ∧
        d = (G.index : ℝ) ∧ ((J * G.index : ℕ) : ℝ) = (J : ℝ) * d ∧
        (∀ i, (-(Nat.ceil (JSP000334.qThreshold 2 q.val (pairWeights42 c2 i)) : ℤ)) =
          -(Nat.ceil (JSP000334.qThreshold 2 Q (R.c 1 i)) : ℤ)) ∧
        (∀ i, (-(Nat.ceil (JSP000334.qThreshold 3 q.val (pairWeights42 c3 i)) : ℤ)) =
          -(Nat.ceil (JSP000334.qThreshold 3 Q (R.c 2 i)) : ℤ)) ∧
        (∀ i, ‖∑ k, ((J : ℝ) * d * algebraMap ℚ ℝ (D k)) *
            (compound L)⁻¹.transpose i k‖ ≤
          120 * (Q ^ (R.c 0 i))⁻¹ * d * Q ^ (-5 * R.delta)) ∧
        (∀ i, (‖∑ k, (((J * G.index : ℕ) : ℚ_[2]) * algebraMap ℚ ℚ_[2] (D k)) *
            (((compound A2).map (algebraMap ℚ ℚ_[2])))⁻¹.transpose i k‖ ≤
          (2 : ℝ) ^ (∑ k : Fin 5, (-(Nat.ceil (JSP000334.qThreshold 2 q.val (pairWeights42 c2 (i.succAbove k))) : ℤ)))) ∧
          (‖∑ k, (((J * G.index : ℕ) : ℚ_[3]) * algebraMap ℚ ℚ_[3] (D k)) *
            (((compound A3).map (algebraMap ℚ ℚ_[3])))⁻¹.transpose i k‖ ≤
          (3 : ℝ) ^ (∑ k : Fin 5, (-(Nat.ceil (JSP000334.qThreshold 3 q.val (pairWeights42 c3 (i.succAbove k))) : ℤ))))) ∧
        ∃ a : ℚ, a ≠ 0 ∧
          normalForm6 (R.M q) = a • rationalFrameDual42
            (fun j i => ((R.w q j : Fin 6 → ℤ) i : ℚ)) (sourceFrameIndependent6 R q) 5 ∧
          (∀ k, (R.M q k : ℚ) = a * D k) ∧
          (∀ k, D k = a⁻¹ * (R.M q k : ℚ)) ∧
          ∀ s ∈ (Finset.univ.filter (fun s : Fin 3 → Fin 6 => -(3*(R.delta/2))/4 ≤ ∑ tau, R.c tau (s tau))),
            dualNormProduct6 A2 A3 L D s = 0 ∧
            (‖∑ k, algebraMap ℚ ℝ (D k) * (compound L)⁻¹.transpose (s 0) k‖ *
              ‖∑ k, algebraMap ℚ ℚ_[2] (D k) * ((compound A2).map (algebraMap ℚ ℚ_[2]))⁻¹.transpose (s 1) k‖ *
              ‖∑ k, algebraMap ℚ ℚ_[3] (D k) * ((compound A3).map (algebraMap ℚ ℚ_[3]))⁻¹.transpose (s 2) k‖) = 0 := by
  obtain ⟨B, hS, hzero, hq⟩ :=
    SchlickeweiSatz41Selected6.source_satz41_selected6 R h2 h3 hLdet
  have hS' : (Finset.univ.filter (fun s : Fin 3 → Fin 6 =>
      -(3*(R.delta/2))/4 ≤ ∑ tau, R.c tau (s tau))).Nonempty := by
    rw [← admissible_expansion6]
    exact hS
  have hzero' : ∀ q : V, B < q.val →
      ∀ s ∈ Finset.univ.filter (fun s : Fin 3 → Fin 6 =>
        -(3*(R.delta/2))/4 ≤ ∑ tau, R.c tau (s tau)),
        actualNormProduct6 A2 A3 L (R.M q) s = 0 := by
    intro q hB s hs
    apply hzero q hB s
    rw [admissible_expansion6]
    exact hs
  refine ⟨B, hS', hzero', ?_⟩
  intro q hB
  have hlocal : SourceLocal6 R q := hq q hB
  obtain ⟨hframes, hnormals⟩ := component_A6 R q hlocal
  obtain ⟨hquot, hpos⟩ := component_B6 R q hlocal
  obtain ⟨hdet, habs, hne, hdpos⟩ := component_C6 R q hlocal
  obtain ⟨hdindex, hscale⟩ := component_D6 R q hlocal
  obtain ⟨he2, he3⟩ := component_E6 R q hlocal
  have hreal := component_F6 R q hlocal
  have hfinite := component_G6 R q hlocal
  obtain ⟨a, ha, hform, hforward, hinverse⟩ := component_H6 R q hlocal
  have hnormzero := component_I6 R q hlocal
  have hpublishedzero := component_J6 R q hlocal
  refine ⟨hframes, hnormals, hquot, hpos, hdet, habs, hne, hdpos,
    hdindex, hscale, he2, he3, ?_, ?_, a, ha, hform, hforward, hinverse, ?_⟩
  · intro i
    have hr := hreal i
    with_reducible exact hr
  · intro i
    have hf := hfinite i
    with_reducible exact hf
  · intro s hs
    have hz0 := hnormzero s hs
    have hz1 := hpublishedzero s hs
    with_reducible exact ⟨hz0, hz1⟩

end CompoundFeasibility.Satz41Selected151Literal
#check CompoundFeasibility.Satz41Selected152Bridges.dual_expansion6
#print CompoundFeasibility.Satz41Selected152Bridges.dual_expansion6
#print axioms CompoundFeasibility.Satz41Selected152Bridges.dual_expansion6

#check CompoundFeasibility.Satz41Selected152Bridges.source_dual_expansion6
#print CompoundFeasibility.Satz41Selected152Bridges.source_dual_expansion6
#print axioms CompoundFeasibility.Satz41Selected152Bridges.source_dual_expansion6

#check CompoundFeasibility.Satz41Selected152Bridges.index_expansion6
#print CompoundFeasibility.Satz41Selected152Bridges.index_expansion6
#print axioms CompoundFeasibility.Satz41Selected152Bridges.index_expansion6

#check CompoundFeasibility.Satz41Selected152Bridges.admissible_expansion6
#print CompoundFeasibility.Satz41Selected152Bridges.admissible_expansion6
#print axioms CompoundFeasibility.Satz41Selected152Bridges.admissible_expansion6

#check CompoundFeasibility.Satz41Selected152Bridges.exponent_expansion6
#print CompoundFeasibility.Satz41Selected152Bridges.exponent_expansion6
#print axioms CompoundFeasibility.Satz41Selected152Bridges.exponent_expansion6

#check CompoundFeasibility.Satz41Selected152Bridges.matrix_expansion6
#print CompoundFeasibility.Satz41Selected152Bridges.matrix_expansion6
#print axioms CompoundFeasibility.Satz41Selected152Bridges.matrix_expansion6

#check CompoundFeasibility.Satz41Selected152Bridges.published_expansion6
#print CompoundFeasibility.Satz41Selected152Bridges.published_expansion6
#print axioms CompoundFeasibility.Satz41Selected152Bridges.published_expansion6

#check CompoundFeasibility.Satz41Selected152Bridges.finite_bound_transport6
#print CompoundFeasibility.Satz41Selected152Bridges.finite_bound_transport6
#print axioms CompoundFeasibility.Satz41Selected152Bridges.finite_bound_transport6

#check CompoundFeasibility.Satz41Selected152Bridges.SourceLocal6
#print CompoundFeasibility.Satz41Selected152Bridges.SourceLocal6
#print axioms CompoundFeasibility.Satz41Selected152Bridges.SourceLocal6

#check CompoundFeasibility.Satz41Selected152Bridges.LiteralA6
#print CompoundFeasibility.Satz41Selected152Bridges.LiteralA6
#print axioms CompoundFeasibility.Satz41Selected152Bridges.LiteralA6

#check CompoundFeasibility.Satz41Selected152Bridges.component_A6
#print CompoundFeasibility.Satz41Selected152Bridges.component_A6
#print axioms CompoundFeasibility.Satz41Selected152Bridges.component_A6

#check CompoundFeasibility.Satz41Selected152Bridges.LiteralB6
#print CompoundFeasibility.Satz41Selected152Bridges.LiteralB6
#print axioms CompoundFeasibility.Satz41Selected152Bridges.LiteralB6

#check CompoundFeasibility.Satz41Selected152Bridges.component_B6
#print CompoundFeasibility.Satz41Selected152Bridges.component_B6
#print axioms CompoundFeasibility.Satz41Selected152Bridges.component_B6

#check CompoundFeasibility.Satz41Selected152Bridges.LiteralC6
#print CompoundFeasibility.Satz41Selected152Bridges.LiteralC6
#print axioms CompoundFeasibility.Satz41Selected152Bridges.LiteralC6

#check CompoundFeasibility.Satz41Selected152Bridges.component_C6
#print CompoundFeasibility.Satz41Selected152Bridges.component_C6
#print axioms CompoundFeasibility.Satz41Selected152Bridges.component_C6

#check CompoundFeasibility.Satz41Selected152Bridges.LiteralD6
#print CompoundFeasibility.Satz41Selected152Bridges.LiteralD6
#print axioms CompoundFeasibility.Satz41Selected152Bridges.LiteralD6

#check CompoundFeasibility.Satz41Selected152Bridges.component_D6
#print CompoundFeasibility.Satz41Selected152Bridges.component_D6
#print axioms CompoundFeasibility.Satz41Selected152Bridges.component_D6

#check CompoundFeasibility.Satz41Selected152Bridges.LiteralE6
#print CompoundFeasibility.Satz41Selected152Bridges.LiteralE6
#print axioms CompoundFeasibility.Satz41Selected152Bridges.LiteralE6

#check CompoundFeasibility.Satz41Selected152Bridges.component_E6
#print CompoundFeasibility.Satz41Selected152Bridges.component_E6
#print axioms CompoundFeasibility.Satz41Selected152Bridges.component_E6

#check CompoundFeasibility.Satz41Selected152Bridges.LiteralF6
#print CompoundFeasibility.Satz41Selected152Bridges.LiteralF6
#print axioms CompoundFeasibility.Satz41Selected152Bridges.LiteralF6

#check CompoundFeasibility.Satz41Selected152Bridges.component_F6
#print CompoundFeasibility.Satz41Selected152Bridges.component_F6
#print axioms CompoundFeasibility.Satz41Selected152Bridges.component_F6

#check CompoundFeasibility.Satz41Selected152Bridges.FiniteBound153
#print CompoundFeasibility.Satz41Selected152Bridges.FiniteBound153
#print axioms CompoundFeasibility.Satz41Selected152Bridges.FiniteBound153

#check CompoundFeasibility.Satz41Selected152Bridges.finite_bound_symbolic153
#print CompoundFeasibility.Satz41Selected152Bridges.finite_bound_symbolic153
#print axioms CompoundFeasibility.Satz41Selected152Bridges.finite_bound_symbolic153

#check CompoundFeasibility.Satz41Selected152Bridges.finite_bound_coordinates153
#print CompoundFeasibility.Satz41Selected152Bridges.finite_bound_coordinates153
#print axioms CompoundFeasibility.Satz41Selected152Bridges.finite_bound_coordinates153

#check CompoundFeasibility.Satz41Selected152Bridges.finite_bound_two153
#print CompoundFeasibility.Satz41Selected152Bridges.finite_bound_two153
#print axioms CompoundFeasibility.Satz41Selected152Bridges.finite_bound_two153

#check CompoundFeasibility.Satz41Selected152Bridges.finite_bound_three153
#print CompoundFeasibility.Satz41Selected152Bridges.finite_bound_three153
#print axioms CompoundFeasibility.Satz41Selected152Bridges.finite_bound_three153

#check CompoundFeasibility.Satz41Selected152Bridges.boundary_p2_153
#print CompoundFeasibility.Satz41Selected152Bridges.boundary_p2_153
#print axioms CompoundFeasibility.Satz41Selected152Bridges.boundary_p2_153

#check CompoundFeasibility.Satz41Selected152Bridges.boundary_p3_153
#print CompoundFeasibility.Satz41Selected152Bridges.boundary_p3_153
#print axioms CompoundFeasibility.Satz41Selected152Bridges.boundary_p3_153

#check CompoundFeasibility.Satz41Selected152Bridges.LiteralG6
#print CompoundFeasibility.Satz41Selected152Bridges.LiteralG6
#print axioms CompoundFeasibility.Satz41Selected152Bridges.LiteralG6

#check CompoundFeasibility.Satz41Selected152Bridges.component_G6
#print CompoundFeasibility.Satz41Selected152Bridges.component_G6
#print axioms CompoundFeasibility.Satz41Selected152Bridges.component_G6

#check CompoundFeasibility.Satz41Selected152Bridges.LiteralH6
#print CompoundFeasibility.Satz41Selected152Bridges.LiteralH6
#print axioms CompoundFeasibility.Satz41Selected152Bridges.LiteralH6

#check CompoundFeasibility.Satz41Selected152Bridges.component_H6
#print CompoundFeasibility.Satz41Selected152Bridges.component_H6
#print axioms CompoundFeasibility.Satz41Selected152Bridges.component_H6

#check CompoundFeasibility.Satz41Selected152Bridges.LiteralI6
#print CompoundFeasibility.Satz41Selected152Bridges.LiteralI6
#print axioms CompoundFeasibility.Satz41Selected152Bridges.LiteralI6

#check CompoundFeasibility.Satz41Selected152Bridges.component_I6
#print CompoundFeasibility.Satz41Selected152Bridges.component_I6
#print axioms CompoundFeasibility.Satz41Selected152Bridges.component_I6

#check CompoundFeasibility.Satz41Selected152Bridges.LiteralJ6
#print CompoundFeasibility.Satz41Selected152Bridges.LiteralJ6
#print axioms CompoundFeasibility.Satz41Selected152Bridges.LiteralJ6

#check CompoundFeasibility.Satz41Selected152Bridges.component_J6
#print CompoundFeasibility.Satz41Selected152Bridges.component_J6
#print axioms CompoundFeasibility.Satz41Selected152Bridges.component_J6

#check CompoundFeasibility.Satz41Selected151Literal.complete_literal
#print CompoundFeasibility.Satz41Selected151Literal.complete_literal
#print axioms CompoundFeasibility.Satz41Selected151Literal.complete_literal
