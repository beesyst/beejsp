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

end CompoundFeasibility.Satz41Selected152Bridges

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
