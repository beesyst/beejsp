import Statement
import Mathlib.Data.Finset.NAry
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
Source-faithful arithmetic infrastructure for the final set in Verstraëte's
Theorem 1. The paper adjoins the finite prefix `[2^120]` to its sparse set
`S'`; this file proves that the prefix alone satisfies the project's exact
`SourceSparsity099` predicate.
-/

namespace JSP000089

/-- The sumset `A + B` used in source Lemmas 4.1--4.3.  It is represented as
the finite image of addition, so multiplicities of representations are not
counted. -/
def additiveSumset (A B : Finset ℕ) : Finset ℕ :=
  Finset.image₂ (· + ·) A B

/-- The collision-free event in the proof of source Lemma 4.1: among the
selected elements of `A` and `B`, equal sums have the same ordered pair of
summands. -/
def PairSumsInjective (A B : Finset ℕ) : Prop :=
  Set.InjOn (fun pair : ℕ × ℕ => pair.1 + pair.2) (↑A ×ˢ ↑B)

/-- The finite sample space of independently selecting one subset of each
source set.  It is the counting representation of the random selections in
source Lemma 4.1. -/
def subsetSelectionPairs (A B : Finset ℕ) : Finset (Finset ℕ × Finset ℕ) :=
  A.powerset.product B.powerset

/-- Membership in the finite sample space says exactly that both selections
are subsets of their respective source sets. -/
lemma mem_subsetSelectionPairs {A B A' B' : Finset ℕ} :
    (A', B') ∈ subsetSelectionPairs A B ↔ A' ⊆ A ∧ B' ⊆ B := by
  simp [subsetSelectionPairs]

/-- The full independent subset-selection sample space has the expected
`2^(|A| + |B|)` outcomes. -/
lemma card_subsetSelectionPairs (A B : Finset ℕ) :
    (subsetSelectionPairs A B).card = 2 ^ (A.card + B.card) := by
  simp [subsetSelectionPairs, pow_add]

/-- The fixed-size sample space used to count uniform selections without
introducing a general probability framework. -/
def fixedSizeSelectionPairs (A B : Finset ℕ) (m : ℕ) : Finset (Finset ℕ × Finset ℕ) :=
  (A.powersetCard m).product (B.powersetCard m)

/-- Membership in the fixed-size sample space records both containment and
the selected cardinalities. -/
lemma mem_fixedSizeSelectionPairs {A B A' B' : Finset ℕ} {m : ℕ} :
    (A', B') ∈ fixedSizeSelectionPairs A B m ↔
      A' ⊆ A ∧ B' ⊆ B ∧ A'.card = m ∧ B'.card = m := by
  simp [fixedSizeSelectionPairs, and_assoc, and_left_comm, and_comm]

/-- Exact number of fixed-size selection pairs.  This is the denominator for
the finite counting form of the source Lemma 4.1 sampling argument. -/
lemma card_fixedSizeSelectionPairs (A B : Finset ℕ) (m : ℕ) :
    (fixedSizeSelectionPairs A B m).card = A.card.choose m * B.card.choose m := by
  simp [fixedSizeSelectionPairs]

/-- The deterministic counting conclusion used by the source's Lemma 4.1.
Once the random selection has no colliding ordered pair sums, its sumset has
one element for every selected ordered pair. -/
lemma card_additiveSumset_eq_of_pairSumsInjective {A B : Finset ℕ}
    (hInjective : PairSumsInjective A B) :
    (additiveSumset A B).card = A.card * B.card := by
  exact Finset.card_image₂_iff.mpr hInjective

/-- A lower-bound form of the deterministic Lemma 4.1 counting step.  This
is the form that will consume the lower bounds on the two random selected
sets once the source sampling argument is formalized. -/
lemma le_card_additiveSumset_of_pairSumsInjective {A B : Finset ℕ}
    (hInjective : PairSumsInjective A B) {a b : ℕ}
    (hA : a ≤ A.card) (hB : b ≤ B.card) :
    a * b ≤ (additiveSumset A B).card := by
  rw [card_additiveSumset_eq_of_pairSumsInjective hInjective]
  exact Nat.mul_le_mul hA hB

/-- The collision-free fixed-size outcomes relevant to source Lemma 4.1. -/
noncomputable def sourceLemma41CollisionFreeSelections (A B : Finset ℕ) (m : ℕ) :
    Finset (Finset ℕ × Finset ℕ) := by
  classical
  exact (fixedSizeSelectionPairs A B m).filter fun selected =>
    PairSumsInjective selected.1 selected.2

/-- The complementary outcomes, whose ordered pair sums contain a collision. -/
noncomputable def sourceLemma41CollidingSelections (A B : Finset ℕ) (m : ℕ) :
    Finset (Finset ℕ × Finset ℕ) := by
  classical
  exact (fixedSizeSelectionPairs A B m).filter fun selected =>
    ¬ PairSumsInjective selected.1 selected.2

/-- Membership records all properties a selected pair must have before the
source collision count can establish that such a pair exists. -/
lemma mem_sourceLemma41CollisionFreeSelections {A B A' B' : Finset ℕ} {m : ℕ} :
    (A', B') ∈ sourceLemma41CollisionFreeSelections A B m ↔
      A' ⊆ A ∧ B' ⊆ B ∧ A'.card = m ∧ B'.card = m ∧ PairSumsInjective A' B' := by
  classical
  simp [sourceLemma41CollisionFreeSelections, fixedSizeSelectionPairs,
    and_assoc, and_left_comm, and_comm]

/-- Once the source's finite collision count proves that its good-selection
space is nonempty, the selected sets satisfy the exact deterministic
conditions needed for the Lemma 4.1 sumset lower bound. -/
lemma sourceLemma41_selection_conclusion_of_nonempty {A B : Finset ℕ} {m : ℕ}
    (hNonempty : (sourceLemma41CollisionFreeSelections A B m).Nonempty) :
    ∃ A' B', A' ⊆ A ∧ B' ⊆ B ∧ A'.card = m ∧ B'.card = m ∧
      PairSumsInjective A' B' ∧ m * m ≤ (additiveSumset A' B').card := by
  obtain ⟨selected, hSelected⟩ := hNonempty
  obtain ⟨hA, hB, hCardA, hCardB, hInjective⟩ :=
    mem_sourceLemma41CollisionFreeSelections.mp hSelected
  exact ⟨selected.1, selected.2, hA, hB, hCardA, hCardB, hInjective,
    le_card_additiveSumset_of_pairSumsInjective hInjective hCardA.symm.le hCardB.symm.le⟩

/-- A strict finite count of colliding outcomes yields a collision-free
selection.  Establishing this strict inequality for the source's selected
size is the remaining probabilistic/counting core of Lemma 4.1. -/
lemma sourceLemma41_collisionFreeSelections_nonempty_of_colliding_card_lt
    {A B : Finset ℕ} {m : ℕ}
    (hColliding : (sourceLemma41CollidingSelections A B m).card <
      (fixedSizeSelectionPairs A B m).card) :
    (sourceLemma41CollisionFreeSelections A B m).Nonempty := by
  apply Finset.card_pos.mp
  by_contra hNotPositive
  have hZero : (sourceLemma41CollisionFreeSelections A B m).card = 0 :=
    Nat.eq_zero_of_not_pos hNotPositive
  have hPartition :
      (sourceLemma41CollisionFreeSelections A B m).card +
          (sourceLemma41CollidingSelections A B m).card =
        (fixedSizeSelectionPairs A B m).card := by
    classical
    simpa [sourceLemma41CollisionFreeSelections, sourceLemma41CollidingSelections] using
      (Finset.filter_card_add_filter_neg_card_eq_card
        (s := fixedSizeSelectionPairs A B m)
        (p := fun selected => PairSumsInjective selected.1 selected.2))
  omega

/-- The finite collision-count criterion in the exact form consumed by the
already-proved sumset lower-bound lemma. -/
lemma sourceLemma41_selection_conclusion_of_colliding_card_lt {A B : Finset ℕ} {m : ℕ}
    (hColliding : (sourceLemma41CollidingSelections A B m).card <
      (fixedSizeSelectionPairs A B m).card) :
    ∃ A' B', A' ⊆ A ∧ B' ⊆ B ∧ A'.card = m ∧ B'.card = m ∧
      PairSumsInjective A' B' ∧ m * m ≤ (additiveSumset A' B').card :=
  sourceLemma41_selection_conclusion_of_nonempty
    (sourceLemma41_collisionFreeSelections_nonempty_of_colliding_card_lt hColliding)

/-- A fourth-root-scale integral selected size for the finite counting
reformulation of source Lemma 4.1. -/
def sourceLemma41SelectedSize (k : ℕ) : ℕ :=
  (Nat.sqrt (Nat.sqrt k) + 2) / 2

/-- Division-free quantitative bounds for the selected size.  The left bound
means that a collision-free pair of selections of this size has a sumset large
enough for the source conclusion; the right bound is the source's
`O(k^(1/4))` selected-set size condition. -/
lemma sourceLemma41_selectedSize_quantitative_bounds {k : ℕ} (hk : 2 ^ 24 ≤ k) :
    k ≤ 16 * sourceLemma41SelectedSize k ^ 4 ∧
      sourceLemma41SelectedSize k ^ 4 ≤ 16 * k := by
  let r := Nat.sqrt (Nat.sqrt k)
  let m := (r + 2) / 2
  change k ≤ 16 * m ^ 4 ∧ m ^ 4 ≤ 16 * k
  have hkPositive : 0 < k := lt_of_lt_of_le (by norm_num : 0 < 2 ^ 24) hk
  have hrPositive : 0 < r := by
    dsimp [r]
    exact Nat.sqrt_pos.mpr (Nat.sqrt_pos.mpr hkPositive)
  have hrle : r ^ 4 ≤ k := by
    dsimp [r]
    nlinarith [Nat.sqrt_le' (Nat.sqrt k), Nat.sqrt_le' k]
  have hrlt : k < (r + 1) ^ 4 := by
    have hs : Nat.sqrt k < (r + 1) ^ 2 := by
      dsimp [r]
      exact Nat.lt_succ_sqrt' (Nat.sqrt k)
    have hks : k < (Nat.sqrt k + 1) ^ 2 := Nat.lt_succ_sqrt' k
    calc
      k < (Nat.sqrt k + 1) ^ 2 := hks
      _ ≤ ((r + 1) ^ 2) ^ 2 := Nat.pow_le_pow_left (Nat.succ_le_iff.mpr hs) 2
      _ = (r + 1) ^ 4 := by rw [← pow_mul]
  have hUpper : m ≤ 2 * r := by
    have hDiv : m ≤ r + 1 := by
      dsimp [m]
      omega
    have hrOne : 1 ≤ r := hrPositive
    omega
  have hLower : r + 1 ≤ 2 * m := by
    dsimp [m]
    omega
  constructor
  · exact Nat.le_of_lt (calc
      k < (r + 1) ^ 4 := hrlt
      _ ≤ (2 * m) ^ 4 := Nat.pow_le_pow_left hLower 4
      _ = 16 * m ^ 4 := by norm_num [mul_pow])
  · calc
      m ^ 4 ≤ (2 * r) ^ 4 := Nat.pow_le_pow_left hUpper 4
      _ = 16 * r ^ 4 := by norm_num [mul_pow]
      _ ≤ 16 * k := Nat.mul_le_mul_left _ hrle

/-- The chosen fourth-root-scale size is available in each source set of
cardinality `k` in the Lemma 4.1 regime. -/
lemma sourceLemma41_selectedSize_le {k : ℕ} (hk : 2 ^ 24 ≤ k) :
    sourceLemma41SelectedSize k ≤ k := by
  let r := Nat.sqrt (Nat.sqrt k)
  let m := (r + 2) / 2
  change m ≤ k
  have hm : m ≤ r + 1 := by
    dsimp [m]
    omega
  have hr : r ≤ Nat.sqrt k := by
    dsimp [r]
    exact Nat.sqrt_le_self _
  have hkTwo : 1 < k := by
    calc
      1 < 2 ^ 24 := by norm_num
      _ ≤ k := hk
  have hsqrt : Nat.sqrt k < k := Nat.sqrt_lt_self hkTwo
  omega

/-- The selected size is at most the integer fourth-root lower approximation.
This sharper estimate is the numerical input to the source collision count. -/
lemma sourceLemma41_selectedSize_le_fourthRoot {k : ℕ} (hk : 2 ^ 24 ≤ k) :
    sourceLemma41SelectedSize k ≤ Nat.sqrt (Nat.sqrt k) := by
  let r := Nat.sqrt (Nat.sqrt k)
  let m := (r + 2) / 2
  change m ≤ r
  have hSqrtK : 4 ≤ Nat.sqrt k := by
    apply Nat.le_sqrt.mpr
    norm_num
    exact le_trans (by norm_num : 16 ≤ 2 ^ 24) hk
  have hRoot : 2 ≤ r := by
    dsimp [r]
    exact Nat.le_sqrt.mpr hSqrtK
  dsimp [m]
  omega

/-- In the source Lemma 4.1 regime, the fourth power of the selected size is
at most `k`; this is the scale that makes the collision union bound strict. -/
lemma sourceLemma41_selectedSize_pow_four_le {k : ℕ} (hk : 2 ^ 24 ≤ k) :
    sourceLemma41SelectedSize k ^ 4 ≤ k := by
  calc
    sourceLemma41SelectedSize k ^ 4 ≤ (Nat.sqrt (Nat.sqrt k)) ^ 4 :=
      Nat.pow_le_pow_left (sourceLemma41_selectedSize_le_fourthRoot hk) 4
    _ ≤ k := by
      nlinarith [Nat.sqrt_le' (Nat.sqrt k), Nat.sqrt_le' k]

/-- Before excluding colliding selections, the source-valid fixed-size sample
space is nonempty for any two sets of cardinality `k`. -/
lemma sourceLemma41_fixedSizeSelectionPairs_nonempty {A B : Finset ℕ} {k : ℕ}
    (hk : 2 ^ 24 ≤ k) (hA : A.card = k) (hB : B.card = k) :
    (fixedSizeSelectionPairs A B (sourceLemma41SelectedSize k)).Nonempty := by
  have hSizeA : sourceLemma41SelectedSize k ≤ A.card := by
    simpa [hA] using sourceLemma41_selectedSize_le hk
  have hSizeB : sourceLemma41SelectedSize k ≤ B.card := by
    simpa [hB] using sourceLemma41_selectedSize_le hk
  obtain ⟨A', hSubsetA, hCardA⟩ :=
    Finset.exists_subset_card_eq hSizeA
  obtain ⟨B', hSubsetB, hCardB⟩ :=
    Finset.exists_subset_card_eq hSizeB
  refine ⟨(A', B'), ?_⟩
  simp [fixedSizeSelectionPairs, hSubsetA, hSubsetB, hCardA, hCardB]

/-- Ordered equal-sum pairs that witness a collision in the source Lemma 4.1
sampling argument.  Ordering the two representations avoids a quotient by
the symmetry of a collision and is sufficient for the finite union bound. -/
noncomputable def sourceLemma41CollisionWitnesses (A B : Finset ℕ) :
    Finset ((ℕ × ℕ) × (ℕ × ℕ)) := by
  classical
  exact ((A.product B).product (A.product B)).filter fun witness =>
    witness.1.1 + witness.1.2 = witness.2.1 + witness.2.2 ∧
      witness.1 ≠ witness.2

/-- A selected pair is colliding precisely when it contains an ordered
equal-sum witness.  This is the source collision event expressed without any
probability infrastructure. -/
lemma mem_sourceLemma41CollidingSelections_iff_exists_witness
    {A B A' B' : Finset ℕ} {m : ℕ}
    (hSelected : (A', B') ∈ fixedSizeSelectionPairs A B m) :
    (A', B') ∈ sourceLemma41CollidingSelections A B m ↔
      ∃ witness ∈ sourceLemma41CollisionWitnesses A B,
        witness.1.1 ∈ A' ∧ witness.1.2 ∈ B' ∧
          witness.2.1 ∈ A' ∧ witness.2.2 ∈ B' := by
  classical
  constructor
  · intro hColliding
    rw [sourceLemma41CollidingSelections, Finset.mem_filter] at hColliding
    rw [PairSumsInjective] at hColliding
    obtain ⟨pair₁, hpair₁⟩ := not_forall.mp hColliding.2
    obtain ⟨hpair₁, hpair₁'⟩ := Classical.not_imp.mp hpair₁
    obtain ⟨pair₂, hpair₂⟩ := not_forall.mp hpair₁'
    obtain ⟨hpair₂, hpair₂'⟩ := Classical.not_imp.mp hpair₂
    obtain ⟨hsum, hne⟩ := Classical.not_imp.mp hpair₂'
    have hpair₁Selected : pair₁.1 ∈ A' ∧ pair₁.2 ∈ B' := by
      simpa only [Set.mem_prod] using hpair₁
    have hpair₂Selected : pair₂.1 ∈ A' ∧ pair₂.2 ∈ B' := by
      simpa only [Set.mem_prod] using hpair₂
    have hSourceSelected := mem_fixedSizeSelectionPairs.mp hSelected
    have hpair₁Source : pair₁ ∈ A.product B :=
      Finset.mem_product.mpr ⟨hSourceSelected.1 hpair₁Selected.1,
        hSourceSelected.2.1 hpair₁Selected.2⟩
    have hpair₂Source : pair₂ ∈ A.product B :=
      Finset.mem_product.mpr ⟨hSourceSelected.1 hpair₂Selected.1,
        hSourceSelected.2.1 hpair₂Selected.2⟩
    refine ⟨(pair₁, pair₂), ?_, hpair₁Selected.1, hpair₁Selected.2,
      hpair₂Selected.1, hpair₂Selected.2⟩
    simp only [sourceLemma41CollisionWitnesses, Finset.mem_filter,
      Finset.mem_product]
    exact ⟨Finset.mem_product.mpr ⟨hpair₁Source, hpair₂Source⟩, hsum, hne⟩
  · rintro ⟨witness, hWitness, hA₁, hB₁, hA₂, hB₂⟩
    rw [sourceLemma41CollidingSelections, Finset.mem_filter]
    refine ⟨hSelected, ?_⟩
    intro hInjective
    have hEqual := hInjective ⟨hA₁, hB₁⟩ ⟨hA₂, hB₂⟩ ?_
    · exact (Finset.mem_filter.mp hWitness).2.2 hEqual
    · exact (Finset.mem_filter.mp hWitness).2.1

/-- The two representations in an ordered collision differ in both
coordinates: equality of one summand would cancel the equal-sum equation and
contradict that the witness is a genuine collision. -/
lemma sourceLemma41CollisionWitnesses_distinct_coordinates
    {A B : Finset ℕ} {witness : (ℕ × ℕ) × (ℕ × ℕ)}
    (hWitness : witness ∈ sourceLemma41CollisionWitnesses A B) :
    witness.1.1 ≠ witness.2.1 ∧ witness.1.2 ≠ witness.2.2 := by
  classical
  have hCollision := (Finset.mem_filter.mp hWitness).2
  constructor
  · intro hFirst
    apply hCollision.2
    apply Prod.ext
    · exact hFirst
    · exact Nat.add_left_cancel (n := witness.1.1)
        (by simpa [hFirst] using hCollision.1)
  · intro hSecond
    apply hCollision.2
    apply Prod.ext
    · exact Nat.add_right_cancel (m := witness.1.2)
        (by simpa [hSecond] using hCollision.1)
    · exact hSecond

/-- Ordered collision witnesses satisfy the source union-bound estimate.  A
witness is determined by its first `A` coordinate and its ordered pair of
distinct `B` coordinates, since the equal-sum equation then determines its
second `A` coordinate. -/
lemma card_sourceLemma41CollisionWitnesses_le {A B : Finset ℕ} {k : ℕ}
    (hA : A.card = k) (hB : B.card = k) :
    (sourceLemma41CollisionWitnesses A B).card ≤ k ^ 2 * (k - 1) := by
  classical
  let encode : ((ℕ × ℕ) × (ℕ × ℕ)) → ℕ × (ℕ × ℕ) :=
    fun witness => (witness.1.1, (witness.1.2, witness.2.2))
  let target : Finset (ℕ × (ℕ × ℕ)) := A.product (Finset.offDiag B)
  have hMap : ∀ witness ∈ sourceLemma41CollisionWitnesses A B,
      encode witness ∈ target := by
    intro witness hWitness
    have hMembership := (Finset.mem_filter.mp hWitness).1
    have hDistinct := sourceLemma41CollisionWitnesses_distinct_coordinates hWitness
    have hFirstPair : witness.1 ∈ A.product B :=
      (Finset.mem_product.mp hMembership).1
    have hSecondPair : witness.2 ∈ A.product B :=
      (Finset.mem_product.mp hMembership).2
    change encode witness ∈ A.product (Finset.offDiag B)
    refine Finset.mem_product.mpr ⟨(Finset.mem_product.mp hFirstPair).1, ?_⟩
    exact Finset.mem_offDiag.mpr ⟨(Finset.mem_product.mp hFirstPair).2,
      (Finset.mem_product.mp hSecondPair).2, hDistinct.2⟩
  have hInj : (↑(sourceLemma41CollisionWitnesses A B) : Set ((ℕ × ℕ) × (ℕ × ℕ))).InjOn
      encode := by
    intro witness₁ hwitness₁ witness₂ hwitness₂ hEncode
    have hCollision₁ := (Finset.mem_filter.mp hwitness₁).2
    have hCollision₂ := (Finset.mem_filter.mp hwitness₂).2
    have hFirst : witness₁.1.1 = witness₂.1.1 := by
      simpa only [encode, Prod.mk.injEq] using congrArg Prod.fst hEncode
    have hSecond : witness₁.1.2 = witness₂.1.2 := by
      have := congrArg (fun encoded => encoded.2.1) hEncode
      simpa [encode] using this
    have hFourth : witness₁.2.2 = witness₂.2.2 := by
      have := congrArg (fun encoded => encoded.2.2) hEncode
      simpa [encode] using this
    have hThird : witness₁.2.1 = witness₂.2.1 := by
      apply Nat.add_right_cancel (m := witness₁.2.2)
      calc
        witness₁.2.1 + witness₁.2.2 = witness₁.1.1 + witness₁.1.2 := hCollision₁.1.symm
        _ = witness₂.1.1 + witness₂.1.2 := by rw [hFirst, hSecond]
        _ = witness₂.2.1 + witness₂.2.2 := hCollision₂.1
        _ = witness₂.2.1 + witness₁.2.2 := by rw [hFourth]
    apply Prod.ext
    · apply Prod.ext <;> assumption
    · apply Prod.ext <;> assumption
  calc
    (sourceLemma41CollisionWitnesses A B).card ≤ target.card :=
      Finset.card_le_card_of_injOn encode hMap hInj
    _ = k ^ 2 * (k - 1) := by
      change (A.product (Finset.offDiag B)).card = k ^ 2 * (k - 1)
      calc
        (A.product (Finset.offDiag B)).card = A.card * (Finset.offDiag B).card :=
          Finset.card_product A (Finset.offDiag B)
        _ = k * (k * k - k) := by rw [Finset.offDiag_card, hA, hB]
        _ = k * (k * (k - 1)) := by
          congr 1
          rw [Nat.mul_sub_left_distrib, Nat.mul_one]
        _ = k ^ 2 * (k - 1) := by simp [pow_two, Nat.mul_assoc]

/-- The source regime supplies the two selected elements required on each
side by every collision witness. -/
lemma sourceLemma41_two_le_selectedSize {k : ℕ} (hk : 2 ^ 24 ≤ k) :
    2 ≤ sourceLemma41SelectedSize k := by
  let r := Nat.sqrt (Nat.sqrt k)
  let m := (r + 2) / 2
  change 2 ≤ m
  have hSqrtK : 4 ≤ Nat.sqrt k := by
    apply Nat.le_sqrt.mpr
    norm_num
    exact le_trans (by norm_num : 16 ≤ 2 ^ 24) hk
  have hRoot : 2 ≤ r := by
    dsimp [r]
    exact Nat.le_sqrt.mpr hSqrtK
  dsimp [m]
  omega

/-- The fixed-size outcomes containing all four coordinates of one ordered
collision witness.  Its cardinality is the remaining marked-subset count in
the finite reformulation of source Lemma 4.1. -/
noncomputable def sourceLemma41SelectionsContainingWitness
    (A B : Finset ℕ) (m : ℕ) (witness : (ℕ × ℕ) × (ℕ × ℕ)) :
    Finset (Finset ℕ × Finset ℕ) := by
  classical
  exact (fixedSizeSelectionPairs A B m).filter fun selected =>
    witness.1.1 ∈ selected.1 ∧ witness.1.2 ∈ selected.2 ∧
      witness.2.1 ∈ selected.1 ∧ witness.2.2 ∈ selected.2

/-- A colliding selection belongs to the finite union of the fixed-witness
families.  This is the set-theoretic input to `Finset.card_biUnion_le`. -/
lemma sourceLemma41CollidingSelections_subset_biUnion_witnesses
    (A B : Finset ℕ) (m : ℕ) :
    sourceLemma41CollidingSelections A B m ⊆
      (sourceLemma41CollisionWitnesses A B).biUnion
        (sourceLemma41SelectionsContainingWitness A B m) := by
  classical
  intro selected hSelected
  have hFixed : selected ∈ fixedSizeSelectionPairs A B m :=
    (Finset.mem_filter.mp hSelected).1
  obtain ⟨witness, hWitness, hA₁, hB₁, hA₂, hB₂⟩ :=
    (mem_sourceLemma41CollidingSelections_iff_exists_witness hFixed).mp hSelected
  refine Finset.mem_biUnion.mpr ⟨witness, hWitness, ?_⟩
  simp only [sourceLemma41SelectionsContainingWitness, Finset.mem_filter]
  exact ⟨hFixed, hA₁, hB₁, hA₂, hB₂⟩

/-- The finite collision union bound before evaluating the marked-subset
summands. -/
lemma card_sourceLemma41CollidingSelections_le_sum_witnessSelections
    (A B : Finset ℕ) (m : ℕ) :
    (sourceLemma41CollidingSelections A B m).card ≤
      ∑ witness ∈ sourceLemma41CollisionWitnesses A B,
        (sourceLemma41SelectionsContainingWitness A B m witness).card := by
  calc
    (sourceLemma41CollidingSelections A B m).card ≤
        ((sourceLemma41CollisionWitnesses A B).biUnion
          (sourceLemma41SelectionsContainingWitness A B m)).card :=
      Finset.card_le_card (sourceLemma41CollidingSelections_subset_biUnion_witnesses A B m)
    _ ≤ ∑ witness ∈ sourceLemma41CollisionWitnesses A B,
        (sourceLemma41SelectionsContainingWitness A B m witness).card :=
      Finset.card_biUnion_le

/-- Removing the two distinct `A` coordinates of a collision witness leaves
exactly two fewer source elements. -/
lemma sourceLemma41_card_remainingA_of_witness
    {A B : Finset ℕ} {witness : (ℕ × ℕ) × (ℕ × ℕ)}
    (hWitness : witness ∈ sourceLemma41CollisionWitnesses A B) :
    ((A.erase witness.1.1).erase witness.2.1).card = A.card - 2 := by
  classical
  have hMembership := (Finset.mem_filter.mp hWitness).1
  have hFirst : witness.1.1 ∈ A :=
    (Finset.mem_product.mp (Finset.mem_product.mp hMembership).1).1
  have hSecond : witness.2.1 ∈ A :=
    (Finset.mem_product.mp (Finset.mem_product.mp hMembership).2).1
  have hDistinct := (sourceLemma41CollisionWitnesses_distinct_coordinates hWitness).1
  have hSecondErase : witness.2.1 ∈ A.erase witness.1.1 :=
    Finset.mem_erase.mpr ⟨hDistinct.symm, hSecond⟩
  calc
    ((A.erase witness.1.1).erase witness.2.1).card =
        (A.erase witness.1.1).card - 1 := Finset.card_erase_of_mem hSecondErase
    _ = (A.card - 1) - 1 := by rw [Finset.card_erase_of_mem hFirst]
    _ = A.card - 2 := by omega

/-- Removing the two distinct `B` coordinates of a collision witness leaves
exactly two fewer source elements. -/
lemma sourceLemma41_card_remainingB_of_witness
    {A B : Finset ℕ} {witness : (ℕ × ℕ) × (ℕ × ℕ)}
    (hWitness : witness ∈ sourceLemma41CollisionWitnesses A B) :
    ((B.erase witness.1.2).erase witness.2.2).card = B.card - 2 := by
  classical
  have hMembership := (Finset.mem_filter.mp hWitness).1
  have hFirst : witness.1.2 ∈ B :=
    (Finset.mem_product.mp (Finset.mem_product.mp hMembership).1).2
  have hSecond : witness.2.2 ∈ B :=
    (Finset.mem_product.mp (Finset.mem_product.mp hMembership).2).2
  have hDistinct := (sourceLemma41CollisionWitnesses_distinct_coordinates hWitness).2
  have hSecondErase : witness.2.2 ∈ B.erase witness.1.2 :=
    Finset.mem_erase.mpr ⟨hDistinct.symm, hSecond⟩
  calc
    ((B.erase witness.1.2).erase witness.2.2).card =
        (B.erase witness.1.2).card - 1 := Finset.card_erase_of_mem hSecondErase
    _ = (B.card - 1) - 1 := by rw [Finset.card_erase_of_mem hFirst]
    _ = B.card - 2 := by omega

/-- Reinserting the two marked `A` coordinates after deleting them is inverse
on selections which contain the collision witness. -/
lemma sourceLemma41_insert_erase_A_of_witness_coordinates
    {A' : Finset ℕ} {a₁ a₂ : ℕ}
    (ha₁ : a₁ ∈ A') (ha₂ : a₂ ∈ A') :
    insert a₁ (insert a₂ ((A'.erase a₁).erase a₂)) = A' := by
  ext x
  by_cases hx₁ : x = a₁
  · subst x
    simp [ha₁]
  by_cases hx₂ : x = a₂
  · subst x
    simp [ha₂]
  simp [hx₁, hx₂]

/-- Deleting the two witness coordinates after reinserting them is inverse on
residual selections avoiding those coordinates. -/
lemma sourceLemma41_erase_insert_A_of_witness_coordinates
    {R : Finset ℕ} {a₁ a₂ : ℕ}
    (ha₁ : a₁ ∉ R) (ha₂ : a₂ ∉ R) (hne : a₁ ≠ a₂) :
    ((insert a₁ (insert a₂ R)).erase a₁).erase a₂ = R := by
  ext x
  by_cases hx₁ : x = a₁
  · subst x
    simp [hne, ha₁]
  by_cases hx₂ : x = a₂
  · subst x
    simp [hx₁, ha₂]
  simp [hx₁, hx₂]

/-- Deleting the two marked `A` coordinates sends a marked size-`m`
selection into the residual size-`m - 2` powerset. -/
lemma sourceLemma41_erase_markedA_mem_residualPowersetCard
    {A A' : Finset ℕ} {a₁ a₂ m : ℕ}
    (hSubset : A' ⊆ A) (hCard : A'.card = m)
    (ha₁ : a₁ ∈ A') (ha₂ : a₂ ∈ A') (hne : a₁ ≠ a₂) :
    ((A'.erase a₁).erase a₂) ∈ ((A.erase a₁).erase a₂).powersetCard (m - 2) := by
  rw [Finset.mem_powersetCard]
  constructor
  · intro x hx
    have hxOuter := Finset.mem_erase.mp hx
    have hxInner := Finset.mem_erase.mp hxOuter.2
    exact Finset.mem_erase.mpr
      ⟨hxOuter.1, Finset.mem_erase.mpr ⟨hxInner.1, hSubset hxInner.2⟩⟩
  · have ha₂Erase : a₂ ∈ A'.erase a₁ :=
      Finset.mem_erase.mpr ⟨hne.symm, ha₂⟩
    calc
      ((A'.erase a₁).erase a₂).card = (A'.erase a₁).card - 1 :=
        Finset.card_erase_of_mem ha₂Erase
      _ = (A'.card - 1) - 1 := by rw [Finset.card_erase_of_mem ha₁]
      _ = m - 2 := by omega

/-- Reinserting the two marked `A` coordinates sends a residual size-`m - 2`
selection back to a marked size-`m` selection. -/
lemma sourceLemma41_insert_residualA_mem_powersetCard
    {A R : Finset ℕ} {a₁ a₂ m : ℕ}
    (ha₁ : a₁ ∈ A) (ha₂ : a₂ ∈ A) (hne : a₁ ≠ a₂) (hm : 2 ≤ m)
    (hR : R ∈ ((A.erase a₁).erase a₂).powersetCard (m - 2)) :
    insert a₁ (insert a₂ R) ∈ A.powersetCard m := by
  rw [Finset.mem_powersetCard] at hR ⊢
  have hRnotA₁ : a₁ ∉ R := by
    intro h
    have := hR.1 h
    simp at this
  have hRnotA₂ : a₂ ∉ R := by
    intro h
    have := hR.1 h
    simp at this
  constructor
  · intro x hx
    rw [Finset.mem_insert] at hx
    rcases hx with rfl | hx
    · exact ha₁
    rw [Finset.mem_insert] at hx
    rcases hx with rfl | hx
    · exact ha₂
    have hResidual := hR.1 hx
    exact (Finset.mem_erase.mp (Finset.mem_erase.mp hResidual).2).2
  · have hA₁notInsert : a₁ ∉ insert a₂ R := by
      simp [hne, hRnotA₁]
    calc
      (insert a₁ (insert a₂ R)).card = (insert a₂ R).card + 1 :=
        Finset.card_insert_of_not_mem hA₁notInsert
      _ = R.card + 1 + 1 := by rw [Finset.card_insert_of_not_mem hRnotA₂]
      _ = m := by omega

/-- The proof-local equivalence between marked size-`m` selections and
size-`m - 2` selections of the two-element residual set. -/
noncomputable def sourceLemma41MarkedAEquiv
    (A : Finset ℕ) (a₁ a₂ m : ℕ)
    (ha₁ : a₁ ∈ A) (ha₂ : a₂ ∈ A) (hne : a₁ ≠ a₂) (hm : 2 ≤ m) :
    {A' // A' ∈ (A.powersetCard m).filter (fun A' => a₁ ∈ A' ∧ a₂ ∈ A')} ≃
      {R // R ∈ ((A.erase a₁).erase a₂).powersetCard (m - 2)} := by
  classical
  refine
    { toFun := fun selected => ⟨(selected.1.erase a₁).erase a₂,
        sourceLemma41_erase_markedA_mem_residualPowersetCard
          (Finset.mem_powersetCard.mp (Finset.mem_filter.mp selected.2).1).1
          (Finset.mem_powersetCard.mp (Finset.mem_filter.mp selected.2).1).2
          (Finset.mem_filter.mp selected.2).2.1
          (Finset.mem_filter.mp selected.2).2.2 hne⟩
      invFun := fun residual => ⟨insert a₁ (insert a₂ residual.1),
        Finset.mem_filter.mpr ⟨sourceLemma41_insert_residualA_mem_powersetCard
          ha₁ ha₂ hne hm residual.2, by simp⟩⟩
      left_inv := by
        intro selected
        apply Subtype.ext
        exact sourceLemma41_insert_erase_A_of_witness_coordinates
          (Finset.mem_filter.mp selected.2).2.1
          (Finset.mem_filter.mp selected.2).2.2
      right_inv := by
        intro residual
        apply Subtype.ext
        have hResidual := (Finset.mem_powersetCard.mp residual.2).1
        have hNotA₁ : a₁ ∉ residual.1 := by
          intro h
          have := hResidual h
          simp at this
        have hNotA₂ : a₂ ∉ residual.1 := by
          intro h
          have := hResidual h
          simp at this
        exact sourceLemma41_erase_insert_A_of_witness_coordinates hNotA₁ hNotA₂ hne }

/-- Cardinality form of the marked `A`-selection correspondence. -/
lemma card_sourceLemma41_markedASelections
    (A : Finset ℕ) (a₁ a₂ m : ℕ)
    (ha₁ : a₁ ∈ A) (ha₂ : a₂ ∈ A) (hne : a₁ ≠ a₂) (hm : 2 ≤ m) :
    ((A.powersetCard m).filter (fun A' => a₁ ∈ A' ∧ a₂ ∈ A')).card =
      (((A.erase a₁).erase a₂).powersetCard (m - 2)).card := by
  simpa using Fintype.card_congr (sourceLemma41MarkedAEquiv A a₁ a₂ m ha₁ ha₂ hne hm)

/-- For one collision witness, the fixed-size selection family factors into
the independent marked-selection families on `A` and `B`. -/
lemma sourceLemma41SelectionsContainingWitness_eq_product_markedSelections
    (A B : Finset ℕ) (m : ℕ) (witness : (ℕ × ℕ) × (ℕ × ℕ)) :
    sourceLemma41SelectionsContainingWitness A B m witness =
      ((A.powersetCard m).filter
        (fun A' => witness.1.1 ∈ A' ∧ witness.2.1 ∈ A')).product
      ((B.powersetCard m).filter
        (fun B' => witness.1.2 ∈ B' ∧ witness.2.2 ∈ B')) := by
  classical
  ext selected
  simp [sourceLemma41SelectionsContainingWitness, fixedSizeSelectionPairs,
    and_assoc, and_left_comm, and_comm]

/-- Exact finite marked-subset count for a valid ordered collision witness. -/
lemma card_sourceLemma41SelectionsContainingWitness
    {A B : Finset ℕ} {m : ℕ} {witness : (ℕ × ℕ) × (ℕ × ℕ)}
    (hWitness : witness ∈ sourceLemma41CollisionWitnesses A B) (hm : 2 ≤ m) :
    (sourceLemma41SelectionsContainingWitness A B m witness).card =
      (A.card - 2).choose (m - 2) * (B.card - 2).choose (m - 2) := by
  classical
  have hMembership := (Finset.mem_filter.mp hWitness).1
  have hA₁ : witness.1.1 ∈ A :=
    (Finset.mem_product.mp (Finset.mem_product.mp hMembership).1).1
  have hB₁ : witness.1.2 ∈ B :=
    (Finset.mem_product.mp (Finset.mem_product.mp hMembership).1).2
  have hA₂ : witness.2.1 ∈ A :=
    (Finset.mem_product.mp (Finset.mem_product.mp hMembership).2).1
  have hB₂ : witness.2.2 ∈ B :=
    (Finset.mem_product.mp (Finset.mem_product.mp hMembership).2).2
  have hDistinct := sourceLemma41CollisionWitnesses_distinct_coordinates hWitness
  rw [sourceLemma41SelectionsContainingWitness_eq_product_markedSelections]
  change (Multiset.card (((A.powersetCard m).filter
      (fun A' => witness.1.1 ∈ A' ∧ witness.2.1 ∈ A')).val ×ˢ
      ((B.powersetCard m).filter
        (fun B' => witness.1.2 ∈ B' ∧ witness.2.2 ∈ B')).val)) = _
  rw [Multiset.card_product]
  change ((A.powersetCard m).filter (fun A' => witness.1.1 ∈ A' ∧ witness.2.1 ∈ A')).card *
      ((B.powersetCard m).filter (fun B' => witness.1.2 ∈ B' ∧ witness.2.2 ∈ B')).card = _
  rw [card_sourceLemma41_markedASelections A witness.1.1 witness.2.1 m hA₁ hA₂ hDistinct.1 hm,
    card_sourceLemma41_markedASelections B witness.1.2 witness.2.2 m hB₁ hB₂ hDistinct.2 hm,
    Finset.card_powersetCard, Finset.card_powersetCard,
    sourceLemma41_card_remainingA_of_witness hWitness,
    sourceLemma41_card_remainingB_of_witness hWitness]

/-- The fixed-witness count in the equal-cardinality source regime. -/
lemma card_sourceLemma41SelectionsContainingWitness_eq_square
    {A B : Finset ℕ} {k m : ℕ} {witness : (ℕ × ℕ) × (ℕ × ℕ)}
    (hWitness : witness ∈ sourceLemma41CollisionWitnesses A B) (hm : 2 ≤ m)
    (hA : A.card = k) (hB : B.card = k) :
    (sourceLemma41SelectionsContainingWitness A B m witness).card =
      ((k - 2).choose (m - 2)) ^ 2 := by
  rw [card_sourceLemma41SelectionsContainingWitness hWitness hm, hA, hB]
  simp [pow_two]

/-- The source finite union bound evaluated by the exact witness count. -/
lemma card_sourceLemma41CollidingSelections_le_collision_bound
    {A B : Finset ℕ} {k m : ℕ} (hA : A.card = k) (hB : B.card = k)
    (hm : 2 ≤ m) :
    (sourceLemma41CollidingSelections A B m).card ≤
      k ^ 2 * (k - 1) * ((k - 2).choose (m - 2)) ^ 2 := by
  calc
    (sourceLemma41CollidingSelections A B m).card ≤
        ∑ witness ∈ sourceLemma41CollisionWitnesses A B,
          (sourceLemma41SelectionsContainingWitness A B m witness).card :=
      card_sourceLemma41CollidingSelections_le_sum_witnessSelections A B m
    _ = ∑ witness ∈ sourceLemma41CollisionWitnesses A B,
        ((k - 2).choose (m - 2)) ^ 2 := by
      apply Finset.sum_congr rfl
      intro witness hWitness
      rw [card_sourceLemma41SelectionsContainingWitness_eq_square hWitness hm hA hB]
    _ = (sourceLemma41CollisionWitnesses A B).card *
        ((k - 2).choose (m - 2)) ^ 2 := by simp
    _ ≤ k ^ 2 * (k - 1) * ((k - 2).choose (m - 2)) ^ 2 :=
      Nat.mul_le_mul_right _ (card_sourceLemma41CollisionWitnesses_le hA hB)

/-- The elementary strict gap that turns the fourth-root selected-size bound
into a strict collision count. -/
lemma sourceLemma41_collision_factor_square_lt {m : ℕ} (hm : 2 ≤ m) :
    (m * (m - 1)) ^ 2 < m ^ 4 - 1 := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hm
  norm_num
  have hident : (r + 2) ^ 4 = ((r + 2) * (r + 1)) ^ 2 +
      (r + 2) ^ 2 * (2 * r + 3) := by ring
  have hp : 4 ≤ (r + 2) ^ 2 := by
    exact Nat.pow_le_pow_left (by omega : 2 ≤ r + 2) 2
  have hq : 3 ≤ 2 * r + 3 := by omega
  have hlarge : 1 < (r + 2) ^ 2 * (2 * r + 3) := by
    have hmul := Nat.mul_le_mul hp hq
    omega
  simp [Nat.add_comm] at hident ⊢
  omega

/-- The two standard adjacent-binomial identities combined in the exact form
needed by the collision count. -/
lemma sourceLemma41_choose_cross_multiply {k m : ℕ}
    (hm : 2 ≤ m) (hmk : m ≤ k) :
    k * (k - 1) * (k - 2).choose (m - 2) =
      k.choose m * m * (m - 1) := by
  have hk1 : k - 1 + 1 = k := by omega
  have hm1 : m - 1 + 1 = m := by omega
  have hk2 : k - 2 + 1 = k - 1 := by omega
  have hm2 : m - 2 + 1 = m - 1 := by omega
  have hfirst : k * (k - 1).choose (m - 1) = k.choose m * m := by
    simpa [hk1, hm1] using Nat.succ_mul_choose_eq (k - 1) (m - 1)
  have hsecond : (k - 1) * (k - 2).choose (m - 2) =
      (k - 1).choose (m - 1) * (m - 1) := by
    simpa [hk2, hm2] using Nat.succ_mul_choose_eq (k - 2) (m - 2)
  calc
    k * (k - 1) * (k - 2).choose (m - 2) =
        k * ((k - 1) * (k - 2).choose (m - 2)) := by ac_rfl
    _ = k * ((k - 1).choose (m - 1) * (m - 1)) := by rw [hsecond]
    _ = (k * (k - 1).choose (m - 1)) * (m - 1) := by ac_rfl
    _ = k.choose m * m * (m - 1) := by rw [hfirst]

/-- The direct finite comparison between the collision bound and the complete
fixed-size sample-space count. -/
lemma sourceLemma41_collision_bound_lt_fixedSize_count {k m : ℕ}
    (hm : 2 ≤ m) (hmk : m ≤ k) (hm4 : m ^ 4 ≤ k) :
    k ^ 2 * (k - 1) * ((k - 2).choose (m - 2)) ^ 2 < (k.choose m) ^ 2 := by
  have hgap : (m * (m - 1)) ^ 2 < m ^ 4 - 1 :=
    sourceLemma41_collision_factor_square_lt hm
  have hsmall : (m * (m - 1)) ^ 2 < k - 1 := by
    exact lt_of_lt_of_le hgap (Nat.sub_le_sub_right hm4 1)
  have hcross := sourceLemma41_choose_cross_multiply hm hmk
  have hsquare := congrArg (fun x : ℕ => x ^ 2) hcross
  have htarget : k ^ 2 * (k - 1) * ((k - 2).choose (m - 2)) ^ 2 * (k - 1) =
      (k.choose m) ^ 2 * (m * (m - 1)) ^ 2 := by
    calc
      k ^ 2 * (k - 1) * ((k - 2).choose (m - 2)) ^ 2 * (k - 1) =
          (k * (k - 1) * (k - 2).choose (m - 2)) ^ 2 := by ring
      _ = (k.choose m * m * (m - 1)) ^ 2 := hsquare
      _ = (k.choose m) ^ 2 * (m * (m - 1)) ^ 2 := by ring
  have hbadpos : 0 < k ^ 2 * (k - 1) * ((k - 2).choose (m - 2)) ^ 2 := by
    have hkpos : 0 < k := by omega
    have hkpred : 0 < k - 1 := by omega
    have hc : 0 < (k - 2).choose (m - 2) := Nat.choose_pos (by omega)
    positivity
  have hmult := Nat.mul_lt_mul_of_pos_left hsmall hbadpos
  rw [htarget] at hmult
  exact Nat.lt_of_mul_lt_mul_right hmult

/-- The source-valid selected size makes colliding fixed-size selections
strictly fewer than all fixed-size selections. -/
lemma sourceLemma41_colliding_card_lt_fixedSizeSelectionPairs
    {A B : Finset ℕ} {k : ℕ} (hk : 2 ^ 24 ≤ k)
    (hA : A.card = k) (hB : B.card = k) :
    (sourceLemma41CollidingSelections A B (sourceLemma41SelectedSize k)).card <
      (fixedSizeSelectionPairs A B (sourceLemma41SelectedSize k)).card := by
  have hm : 2 ≤ sourceLemma41SelectedSize k := sourceLemma41_two_le_selectedSize hk
  have hmk : sourceLemma41SelectedSize k ≤ k := sourceLemma41_selectedSize_le hk
  have hm4 : sourceLemma41SelectedSize k ^ 4 ≤ k :=
    sourceLemma41_selectedSize_pow_four_le hk
  calc
    (sourceLemma41CollidingSelections A B (sourceLemma41SelectedSize k)).card ≤
        k ^ 2 * (k - 1) * ((k - 2).choose (sourceLemma41SelectedSize k - 2)) ^ 2 :=
      card_sourceLemma41CollidingSelections_le_collision_bound hA hB hm
    _ < (k.choose (sourceLemma41SelectedSize k)) ^ 2 :=
      sourceLemma41_collision_bound_lt_fixedSize_count hm hmk hm4
    _ = (fixedSizeSelectionPairs A B (sourceLemma41SelectedSize k)).card := by
      rw [card_fixedSizeSelectionPairs, hA, hB]
      simp [pow_two]

/-- Complete finite-counting form of source Lemma 4.1.  In the source regime,
equal-cardinality sets have collision-free fourth-root-scale subsets whose
sumset has at least one element for every selected ordered pair. -/
theorem sourceLemma41_complete {A B : Finset ℕ} {k : ℕ}
    (hk : 2 ^ 24 ≤ k) (hA : A.card = k) (hB : B.card = k) :
    ∃ A' B', A' ⊆ A ∧ B' ⊆ B ∧
      A'.card = sourceLemma41SelectedSize k ∧ B'.card = sourceLemma41SelectedSize k ∧
      PairSumsInjective A' B' ∧
      sourceLemma41SelectedSize k * sourceLemma41SelectedSize k ≤ (additiveSumset A' B').card ∧
      k ≤ 16 * sourceLemma41SelectedSize k ^ 4 ∧
      sourceLemma41SelectedSize k ^ 4 ≤ 16 * k := by
  obtain ⟨A', B', hSubsetA, hSubsetB, hCardA, hCardB, hInjective, hSumset⟩ :=
    sourceLemma41_selection_conclusion_of_colliding_card_lt
      (sourceLemma41_colliding_card_lt_fixedSizeSelectionPairs hk hA hB)
  exact ⟨A', B', hSubsetA, hSubsetB, hCardA, hCardB, hInjective, hSumset,
    (sourceLemma41_selectedSize_quantitative_bounds hk).1,
    (sourceLemma41_selectedSize_quantitative_bounds hk).2⟩

/-- The finite prefix in the source final set has at most `2^120` positive
members in every initial segment. -/
lemma initialSegmentCount_sourceShortCycleLengths_le (n : ℕ) :
    initialSegmentCount sourceShortCycleLengths n ≤ 2 ^ 120 := by
  classical
  rw [initialSegmentCount]
  calc
    {length ∈ Finset.range (n + 1) | 0 < length ∧ length ∈ sourceShortCycleLengths}.card ≤
        (Finset.Icc 1 (2 ^ 120)).card := by
      refine Finset.card_le_card ?_
      intro length hLength
      rw [Finset.mem_filter] at hLength
      rw [Finset.mem_Icc]
      simpa [sourceShortCycleLengths] using hLength.2
    _ = 2 ^ 120 := by simp

/-- The finite prefix `[2^120]` has the `O(n^0.99)` form required by the
statement contract. This is one component of the eventual proof for
`S = S' ∪ [2^120]`. -/
theorem sourceSparsity099_sourceShortCycleLengths :
    SourceSparsity099 sourceShortCycleLengths := by
  classical
  refine ⟨2 ^ 120, by positivity, ?_⟩
  intro n
  by_cases hn : n = 0
  · subst n
    have hEmpty :
        ({0} : Finset ℕ).filter (fun k => 0 < k ∧ k ∈ sourceShortCycleLengths) = ∅ := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_singleton, Finset.not_mem_empty, iff_false]
      omega
    simp [initialSegmentCount, hEmpty]
  have hnPower : 1 ≤ n ^ 99 :=
    Nat.one_le_iff_ne_zero.mpr (pow_ne_zero 99 hn)
  calc
    initialSegmentCount sourceShortCycleLengths n ^ 100 ≤ (2 ^ 120) ^ 100 :=
      Nat.pow_le_pow_left (initialSegmentCount_sourceShortCycleLengths_le n) 100
    _ = (2 ^ 120) ^ 100 * 1 := (Nat.mul_one _).symm
    _ ≤ (2 ^ 120) ^ 100 * n ^ 99 := Nat.mul_le_mul_left _ hnPower

end JSP000089

namespace JSP000089

/-- Sumsets are monotone in both source sets.  This is the containment step
used when Lemma 4.2 reduces a large pair to the small pair supplied by Lemma
4.1. -/
lemma additiveSumset_subset_additiveSumset {A A' B B' : Finset ℕ}
    (hA : A ⊆ A') (hB : B ⊆ B') :
    additiveSumset A B ⊆ additiveSumset A' B' := by
  intro x hx
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_image₂.mp hx
  exact Finset.mem_image₂.mpr ⟨a, hA ha, b, hB hb, rfl⟩

/-- The finite ambient interval used by the range-contained invocation of
source Lemma 4.2 in the later construction of `S'`. -/
def sourceLemma42Universe (n : ℕ) : Finset ℕ :=
  Finset.Icc 1 n

/-- The reduced finite family in source Lemma 4.2.  Its members are precisely
the fourth-root-scale pairs whose sumsets have the lower bound obtained from
Lemma 4.1 and remain in the ambient interval. -/
noncomputable def sourceLemma42ReducedPairs (n k : ℕ) :
    Finset (Finset ℕ × Finset ℕ) := by
  classical
  let m := sourceLemma41SelectedSize k
  exact ((fixedSizeSelectionPairs (sourceLemma42Universe n)
    (sourceLemma42Universe n) m).filter fun selected =>
      m * m ≤ (additiveSumset selected.1 selected.2).card ∧
        additiveSumset selected.1 selected.2 ⊆ sourceLemma42Universe n)

/-- A candidate source Lemma 4.2 set is contained in the ambient interval and
hits the sumset of every reduced pair. -/
def sourceLemma42HitsReducedPairs (n k : ℕ) (S : Finset ℕ) : Prop :=
  S ⊆ sourceLemma42Universe n ∧
    ∀ selected ∈ sourceLemma42ReducedPairs n k,
      (S ∩ additiveSumset selected.1 selected.2).Nonempty

/-- Membership in the reduced source Lemma 4.2 family exposes the exact
selected-size, sumset-cardinality, and range conditions used by its counting
argument. -/
lemma mem_sourceLemma42ReducedPairs {n k : ℕ} {A B : Finset ℕ} :
    (A, B) ∈ sourceLemma42ReducedPairs n k ↔
      A ⊆ sourceLemma42Universe n ∧ B ⊆ sourceLemma42Universe n ∧
        A.card = sourceLemma41SelectedSize k ∧
        B.card = sourceLemma41SelectedSize k ∧
        sourceLemma41SelectedSize k * sourceLemma41SelectedSize k ≤
          (additiveSumset A B).card ∧
        additiveSumset A B ⊆ sourceLemma42Universe n := by
  classical
  simp [sourceLemma42ReducedPairs, fixedSizeSelectionPairs,
    and_assoc, and_left_comm, and_comm]

/-- The complete Lemma 4.1 conclusion supplies a member of the reduced
Lemma 4.2 family inside every source-valid large pair. -/
lemma sourceLemma42_exists_reducedPair_of_largePair
    {n k : ℕ} {A B : Finset ℕ} (hk : 2 ^ 24 ≤ k)
    (hA : A ⊆ sourceLemma42Universe n) (hB : B ⊆ sourceLemma42Universe n)
    (hCardA : k ≤ A.card) (hCardB : k ≤ B.card)
    (hRange : additiveSumset A B ⊆ sourceLemma42Universe n) :
    ∃ A' B', (A', B') ∈ sourceLemma42ReducedPairs n k ∧
      additiveSumset A' B' ⊆ additiveSumset A B := by
  obtain ⟨A₀, hA₀Subset, hA₀Card⟩ := Finset.exists_subset_card_eq hCardA
  obtain ⟨B₀, hB₀Subset, hB₀Card⟩ := Finset.exists_subset_card_eq hCardB
  obtain ⟨A', B', hA'Subset, hB'Subset, hA'Card, hB'Card, _, hSmall, _, _⟩ :=
    sourceLemma41_complete hk hA₀Card hB₀Card
  have hSmallBig : additiveSumset A' B' ⊆ additiveSumset A B :=
    additiveSumset_subset_additiveSumset
      (fun x hx => hA₀Subset (hA'Subset hx))
      (fun x hx => hB₀Subset (hB'Subset hx))
  refine ⟨A', B', ?_, hSmallBig⟩
  apply mem_sourceLemma42ReducedPairs.mpr
  exact ⟨fun x hx => hA (hA₀Subset (hA'Subset hx)),
    fun x hx => hB (hB₀Subset (hB'Subset hx)), hA'Card, hB'Card, hSmall,
    hSmallBig.trans hRange⟩

/-- Deterministic reduction at the heart of source Lemma 4.2: once a set
hits every finite reduced sumset, it hits the sumset of every source-valid
pair of cardinality at least `k`.  The remaining source obligation is the
quantitative count proving that such a small hitting set exists. -/
theorem sourceLemma42_largePairs_hit_of_hitsReducedPairs
    {n k : ℕ} {S A B : Finset ℕ} (hk : 2 ^ 24 ≤ k)
    (hHits : sourceLemma42HitsReducedPairs n k S)
    (hA : A ⊆ sourceLemma42Universe n) (hB : B ⊆ sourceLemma42Universe n)
    (hCardA : k ≤ A.card) (hCardB : k ≤ B.card)
    (hRange : additiveSumset A B ⊆ sourceLemma42Universe n) :
    (S ∩ additiveSumset A B).Nonempty := by
  obtain ⟨A', B', hReduced, hSmallBig⟩ :=
    sourceLemma42_exists_reducedPair_of_largePair hk hA hB hCardA hCardB hRange
  obtain ⟨x, hx⟩ := hHits.2 (A', B') hReduced
  obtain ⟨hxS, hxSmall⟩ := Finset.mem_inter.mp hx
  exact ⟨x, Finset.mem_inter.mpr ⟨hxS, hSmallBig hxSmall⟩⟩

end JSP000089

namespace JSP000089

/-- The finite candidate space for the source Lemma 4.2 random selection,
restricted to a cardinality budget `r`. -/
noncomputable def sourceLemma42BoundedCandidates (n r : ℕ) : Finset (Finset ℕ) := by
  classical
  exact (sourceLemma42Universe n).powerset.filter fun S => S.card ≤ r

/-- The candidates which hit every reduced source Lemma 4.2 sumset. -/
noncomputable def sourceLemma42GoodCandidates (n k r : ℕ) : Finset (Finset ℕ) := by
  classical
  exact (sourceLemma42BoundedCandidates n r).filter fun S =>
    ∀ selected ∈ sourceLemma42ReducedPairs n k,
      (S ∩ additiveSumset selected.1 selected.2).Nonempty

/-- The complementary candidates missed by at least one reduced sumset. -/
noncomputable def sourceLemma42BadCandidates (n k r : ℕ) : Finset (Finset ℕ) := by
  classical
  exact (sourceLemma42BoundedCandidates n r).filter fun S =>
    ¬ ∀ selected ∈ sourceLemma42ReducedPairs n k,
      (S ∩ additiveSumset selected.1 selected.2).Nonempty

/-- Membership in a good candidate gives precisely its range, size, and
finite hitting conditions. -/
lemma mem_sourceLemma42GoodCandidates {n k r : ℕ} {S : Finset ℕ} :
    S ∈ sourceLemma42GoodCandidates n k r ↔
      S ⊆ sourceLemma42Universe n ∧ S.card ≤ r ∧
        ∀ selected ∈ sourceLemma42ReducedPairs n k,
          (S ∩ additiveSumset selected.1 selected.2).Nonempty := by
  classical
  simp [sourceLemma42GoodCandidates, sourceLemma42BoundedCandidates,
    and_assoc, and_left_comm, and_comm]

/-- The source's strict bad-outcome count forces a good bounded candidate.
This is the exact finite counting bridge used by the random-selection proof
of Lemma 4.2. -/
lemma sourceLemma42_goodCandidates_nonempty_of_bad_card_lt {n k r : ℕ}
    (hBad : (sourceLemma42BadCandidates n k r).card <
      (sourceLemma42BoundedCandidates n r).card) :
    (sourceLemma42GoodCandidates n k r).Nonempty := by
  apply Finset.card_pos.mp
  by_contra hNotPositive
  have hZero : (sourceLemma42GoodCandidates n k r).card = 0 :=
    Nat.eq_zero_of_not_pos hNotPositive
  have hPartition :
      (sourceLemma42GoodCandidates n k r).card +
          (sourceLemma42BadCandidates n k r).card =
        (sourceLemma42BoundedCandidates n r).card := by
    classical
    simpa [sourceLemma42GoodCandidates, sourceLemma42BadCandidates] using
      (Finset.filter_card_add_filter_neg_card_eq_card
        (s := sourceLemma42BoundedCandidates n r)
        (p := fun S => ∀ selected ∈ sourceLemma42ReducedPairs n k,
          (S ∩ additiveSumset selected.1 selected.2).Nonempty))
  omega

/-- Conditional finite form of source Lemma 4.2.  Once its source
random-selection count proves that bad bounded candidates are strictly fewer
than all bounded candidates, this produces the required small set hitting
every source-valid large sumset. -/
theorem sourceLemma42_of_bad_card_lt {n k r : ℕ} (hk : 2 ^ 24 ≤ k)
    (hBad : (sourceLemma42BadCandidates n k r).card <
      (sourceLemma42BoundedCandidates n r).card) :
    ∃ S, S ⊆ sourceLemma42Universe n ∧ S.card ≤ r ∧
      ∀ A B, A ⊆ sourceLemma42Universe n → B ⊆ sourceLemma42Universe n →
        k ≤ A.card → k ≤ B.card →
        additiveSumset A B ⊆ sourceLemma42Universe n →
          (S ∩ additiveSumset A B).Nonempty := by
  obtain ⟨S, hGood⟩ :=
    sourceLemma42_goodCandidates_nonempty_of_bad_card_lt hBad
  obtain ⟨hSubset, hCard, hHits⟩ := mem_sourceLemma42GoodCandidates.mp hGood
  refine ⟨S, hSubset, hCard, ?_⟩
  intro A B hA hB hCardA hCardB hRange
  exact sourceLemma42_largePairs_hit_of_hitsReducedPairs hk
    ⟨hSubset, hHits⟩ hA hB hCardA hCardB hRange

end JSP000089


namespace JSP000089

/-- The coarse branch of the repaired range-contained Lemma 4.2: when the
budget already covers the ambient interval, that interval itself is a hitting
set. The complementary branch is the finite-colouring count. -/
theorem sourceLemma42_rangeContained_of_universe_budget {n k r : ℕ}
    (hk : 2 ^ 24 ≤ k) (hBudget : n ≤ r) :
    ∃ S, S ⊆ sourceLemma42Universe n ∧ S.card ≤ r ∧
      ∀ A B, A ⊆ sourceLemma42Universe n → B ⊆ sourceLemma42Universe n →
        k ≤ A.card → k ≤ B.card →
        additiveSumset A B ⊆ sourceLemma42Universe n →
          (S ∩ additiveSumset A B).Nonempty := by
  classical
  refine ⟨sourceLemma42Universe n, subset_rfl, ?_, ?_⟩
  · simpa [sourceLemma42Universe] using hBudget
  · intro A B _ _ hCardA hCardB hRange
    have hkPositive : 0 < k := lt_of_lt_of_le (by norm_num : 0 < 2 ^ 24) hk
    obtain ⟨a, ha⟩ := Finset.card_pos.mp (lt_of_lt_of_le hkPositive hCardA)
    obtain ⟨b, hb⟩ := Finset.card_pos.mp (lt_of_lt_of_le hkPositive hCardB)
    have hab : a + b ∈ additiveSumset A B :=
      Finset.mem_image₂.mpr ⟨a, ha, b, hb, rfl⟩
    exact ⟨a + b, Finset.mem_inter.mpr ⟨hRange hab, hab⟩⟩

end JSP000089

namespace JSP000089

/-- The finite space of all uniform `q`-colourings of the Lemma 4.2 ambient
interval. -/
noncomputable def sourceLemma42Colourings (n q : ℕ) :
    Finset (sourceLemma42Universe n → Fin q) := by
  classical
  exact Fintype.piFinset (fun _ => Finset.univ)

/-- Exact cardinality of the proof-local uniform colouring space. -/
lemma card_sourceLemma42Colourings (n q : ℕ) :
    (sourceLemma42Colourings n q).card =
      q ^ (sourceLemma42Universe n).card := by
  classical
  simp [sourceLemma42Colourings, Fintype.card_piFinset]

/-- The distinguished colour used to select a candidate hitting set. -/
noncomputable def sourceLemma42SelectedColour (q : ℕ) (hq : 0 < q) : Fin q :=
  ⟨0, hq⟩

/-- The vertices carrying the distinguished colour in one colouring. -/
noncomputable def sourceLemma42SelectedColourClass {n q : ℕ} (hq : 0 < q)
    (colouring : sourceLemma42Universe n → Fin q) : Finset ℕ := by
  classical
  exact (Finset.univ.filter fun x =>
    colouring x = sourceLemma42SelectedColour q hq).image Subtype.val

/-- The selected colour class is always contained in the ambient interval. -/
lemma sourceLemma42SelectedColourClass_subset {n q : ℕ} (hq : 0 < q)
    (colouring : sourceLemma42Universe n → Fin q) :
    sourceLemma42SelectedColourClass hq colouring ⊆ sourceLemma42Universe n := by
  classical
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
  exact y.property

/-- Membership in the selected colour class has the expected coordinate
characterization. -/
lemma mem_sourceLemma42SelectedColourClass {n q : ℕ} (hq : 0 < q)
    (colouring : sourceLemma42Universe n → Fin q) {x : ℕ} :
    x ∈ sourceLemma42SelectedColourClass hq colouring ↔
      ∃ hx : x ∈ sourceLemma42Universe n,
        colouring ⟨x, hx⟩ = sourceLemma42SelectedColour q hq := by
  classical
  constructor
  · rintro hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    exact ⟨y.property, (Finset.mem_filter.mp hy).2⟩
  · rintro ⟨hx, hcolour⟩
    exact Finset.mem_image.mpr ⟨⟨x, hx⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcolour⟩, rfl⟩

/-- Colourings whose distinguished colour class misses a fixed finite set. -/
noncomputable def sourceLemma42ColouringsMissing (n q : ℕ) (hq : 0 < q)
    (T : Finset ℕ) : Finset (sourceLemma42Universe n → Fin q) := by
  classical
  exact Fintype.piFinset fun x =>
    if x.val ∈ T then Finset.univ.erase (sourceLemma42SelectedColour q hq)
    else Finset.univ

/-- Fixed-set avoidance colourings form a subspace of all colourings. -/
lemma sourceLemma42ColouringsMissing_subset {n q : ℕ} (hq : 0 < q)
    (T : Finset ℕ) :
    sourceLemma42ColouringsMissing n q hq T ⊆ sourceLemma42Colourings n q := by
  classical
  intro colouring hcolouring
  simp [sourceLemma42Colourings]

/-- Membership in the fixed-set avoidance space is pointwise avoidance of
the distinguished colour on that set. -/
lemma mem_sourceLemma42ColouringsMissing {n q : ℕ} (hq : 0 < q)
    (T : Finset ℕ) (colouring : sourceLemma42Universe n → Fin q) :
    colouring ∈ sourceLemma42ColouringsMissing n q hq T ↔
      ∀ x : sourceLemma42Universe n, x.val ∈ T →
        colouring x ≠ sourceLemma42SelectedColour q hq := by
  classical
  simp only [sourceLemma42ColouringsMissing, Fintype.mem_piFinset]
  constructor
  · intro h x hx
    have hmem := h x
    rw [if_pos hx] at hmem
    exact (Finset.mem_erase.mp hmem).1
  · intro h x
    by_cases hx : x.val ∈ T
    · rw [if_pos hx]
      exact Finset.mem_erase.mpr ⟨h x hx, Finset.mem_univ _⟩
    · rw [if_neg hx]
      exact Finset.mem_univ _

/-- The avoidance space is exactly the event that the selected colour class
is disjoint from the fixed finite set. -/
lemma mem_sourceLemma42ColouringsMissing_iff_disjoint {n q : ℕ} (hq : 0 < q)
    (T : Finset ℕ) (colouring : sourceLemma42Universe n → Fin q) :
    colouring ∈ sourceLemma42ColouringsMissing n q hq T ↔
      Disjoint (sourceLemma42SelectedColourClass hq colouring) T := by
  constructor
  · intro h
    rw [Finset.disjoint_left]
    intro x hxSelected hxT
    obtain ⟨hxUniverse, hxColour⟩ :=
      (mem_sourceLemma42SelectedColourClass hq colouring).mp hxSelected
    exact ((mem_sourceLemma42ColouringsMissing hq T colouring).mp h
      ⟨x, hxUniverse⟩ hxT) hxColour
  · intro h
    apply (mem_sourceLemma42ColouringsMissing hq T colouring).mpr
    intro x hxT hxColour
    have hxSelected : x.val ∈ sourceLemma42SelectedColourClass hq colouring :=
      (mem_sourceLemma42SelectedColourClass hq colouring).mpr
        ⟨x.property, hxColour⟩
    exact Finset.disjoint_left.mp h hxSelected hxT

/-- The coordinates of the ambient interval corresponding to a contained
finite set have exactly that set's cardinality. -/
lemma card_sourceLemma42ColouringCoordinates_mem {n : ℕ} (T : Finset ℕ)
    (hT : T ⊆ sourceLemma42Universe n) :
    (Finset.univ.filter (fun x : sourceLemma42Universe n => x.val ∈ T)).card =
      T.card := by
  classical
  let R : Finset (sourceLemma42Universe n) :=
    Finset.univ.filter (fun x => x.val ∈ T)
  have hImage : R.image Subtype.val = T := by
    ext x
    constructor
    · intro hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      exact (Finset.mem_filter.mp hy).2
    · intro hx
      exact Finset.mem_image.mpr ⟨⟨x, hT hx⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩, rfl⟩
  have hInj : Set.InjOn Subtype.val (↑R : Set (sourceLemma42Universe n)) := by
    intro x hx y hy hxy
    exact Subtype.ext hxy
  have hCard : R.card = (R.image Subtype.val).card :=
    (Finset.card_image_iff.mpr hInj).symm
  change R.card = T.card
  rw [hCard, hImage]

/-- The remaining coordinates have the complementary cardinality. -/
lemma card_sourceLemma42ColouringCoordinates_not_mem {n : ℕ} (T : Finset ℕ)
    (hT : T ⊆ sourceLemma42Universe n) :
    (Finset.univ.filter (fun x : sourceLemma42Universe n => x.val ∉ T)).card =
      (sourceLemma42Universe n).card - T.card := by
  classical
  have hPartition :
      (Finset.univ.filter (fun x : sourceLemma42Universe n => x.val ∈ T)).card +
        (Finset.univ.filter (fun x : sourceLemma42Universe n => x.val ∉ T)).card =
          (sourceLemma42Universe n).card := by
    simpa using (Finset.filter_card_add_filter_neg_card_eq_card
      (s := (Finset.univ : Finset (sourceLemma42Universe n)))
      (p := fun x => x.val ∈ T))
  rw [card_sourceLemma42ColouringCoordinates_mem T hT] at hPartition
  omega

/-- Exact finite count of colourings whose selected class misses `T`. -/
lemma card_sourceLemma42ColouringsMissing {n q : ℕ} (hq : 0 < q)
    (T : Finset ℕ) (hT : T ⊆ sourceLemma42Universe n) :
    (sourceLemma42ColouringsMissing n q hq T).card =
      (q - 1) ^ T.card * q ^ ((sourceLemma42Universe n).card - T.card) := by
  classical
  have hZero : sourceLemma42SelectedColour q hq ∈ (Finset.univ : Finset (Fin q)) :=
    Finset.mem_univ _
  have hErase :
      (Finset.univ.erase (sourceLemma42SelectedColour q hq) : Finset (Fin q)).card =
        q - 1 := by
    rw [Finset.card_erase_of_mem hZero]
    simp
  rw [sourceLemma42ColouringsMissing, Fintype.card_piFinset]
  calc
    (∏ i : sourceLemma42Universe n,
        (if i.val ∈ T then Finset.univ.erase (sourceLemma42SelectedColour q hq)
        else Finset.univ).card) =
        ∏ i : sourceLemma42Universe n, if i.val ∈ T then (q - 1) else q := by
      apply Finset.prod_congr rfl
      intro i hi
      split_ifs with hmem
      · simp [hErase]
      · simp
    _ = (∏ i ∈ (Finset.univ.filter fun x : sourceLemma42Universe n => x.val ∈ T),
        (q - 1)) * ∏ i ∈
          (Finset.univ.filter fun x : sourceLemma42Universe n => x.val ∉ T), q := by
      rw [Finset.prod_ite]
    _ = (q - 1) ^ T.card * q ^ ((sourceLemma42Universe n).card - T.card) := by
      simp only [Finset.prod_const]
      rw [card_sourceLemma42ColouringCoordinates_mem T hT,
        card_sourceLemma42ColouringCoordinates_not_mem T hT]
end JSP000089


namespace JSP000089

/-- The reduced family is a filtered subset of the product of the two
fixed-size selection spaces. -/
lemma card_sourceLemma42ReducedPairs_le (n k : ℕ) :
    (sourceLemma42ReducedPairs n k).card ≤
      ((sourceLemma42Universe n).card.choose (sourceLemma41SelectedSize k)) ^ 2 := by
  classical
  rw [sourceLemma42ReducedPairs]
  calc
    ((fixedSizeSelectionPairs (sourceLemma42Universe n) (sourceLemma42Universe n)
      (sourceLemma41SelectedSize k)).filter fun selected =>
        sourceLemma41SelectedSize k * sourceLemma41SelectedSize k ≤
          (additiveSumset selected.1 selected.2).card ∧
        additiveSumset selected.1 selected.2 ⊆ sourceLemma42Universe n).card ≤
      (fixedSizeSelectionPairs (sourceLemma42Universe n) (sourceLemma42Universe n)
        (sourceLemma41SelectedSize k)).card := Finset.card_filter_le _ _
    _ = (sourceLemma42Universe n).card.choose (sourceLemma41SelectedSize k) *
        (sourceLemma42Universe n).card.choose (sourceLemma41SelectedSize k) :=
      card_fixedSizeSelectionPairs _ _ _
    _ = ((sourceLemma42Universe n).card.choose (sourceLemma41SelectedSize k)) ^ 2 := by
      ring

/-- The proof-local bad event for one reduced pair: the selected colour class
misses that pair's additive sumset. -/
noncomputable def sourceLemma42BadColouringsForPair (n q : ℕ) (hq : 0 < q)
    (selected : Finset ℕ × Finset ℕ) :
    Finset (sourceLemma42Universe n → Fin q) :=
  sourceLemma42ColouringsMissing n q hq (additiveSumset selected.1 selected.2)

/-- A colouring belongs to a pair's bad event exactly when its selected colour
class is disjoint from that pair's sumset. -/
lemma mem_sourceLemma42BadColouringsForPair_iff {n q : ℕ} (hq : 0 < q)
    (selected : Finset ℕ × Finset ℕ)
    (colouring : sourceLemma42Universe n → Fin q) :
    colouring ∈ sourceLemma42BadColouringsForPair n q hq selected ↔
      Disjoint (sourceLemma42SelectedColourClass hq colouring)
        (additiveSumset selected.1 selected.2) := by
  exact mem_sourceLemma42ColouringsMissing_iff_disjoint hq _ colouring

/-- The proof-local union of all bad events for the reduced Lemma 4.2
family. -/
noncomputable def sourceLemma42BadColourings (n k q : ℕ) (hq : 0 < q) :
    Finset (sourceLemma42Universe n → Fin q) := by
  classical
  exact (sourceLemma42ReducedPairs n k).biUnion
    (sourceLemma42BadColouringsForPair n q hq)

/-- Membership in the total bad-colouring event is failure to hit at least
one reduced sumset. -/
lemma mem_sourceLemma42BadColourings_iff {n k q : ℕ} (hq : 0 < q)
    (colouring : sourceLemma42Universe n → Fin q) :
    colouring ∈ sourceLemma42BadColourings n k q hq ↔
      ∃ selected ∈ sourceLemma42ReducedPairs n k,
        Disjoint (sourceLemma42SelectedColourClass hq colouring)
          (additiveSumset selected.1 selected.2) := by
  classical
  rw [sourceLemma42BadColourings, Finset.mem_biUnion]
  constructor
  · rintro ⟨selected, hselected, hbad⟩
    exact ⟨selected, hselected,
      (mem_sourceLemma42BadColouringsForPair_iff hq selected colouring).mp hbad⟩
  · rintro ⟨selected, hselected, hdisjoint⟩
    exact ⟨selected, hselected,
      (mem_sourceLemma42BadColouringsForPair_iff hq selected colouring).mpr hdisjoint⟩

/-- Enlarging the missed set can only reduce the exact fixed-set miss-count
upper bound after its lower cardinality threshold is fixed. -/
lemma sourceLemma42_miss_count_le_of_card_le {q u t m : ℕ}
    (hm : m ≤ t) (htu : t ≤ u) :
    (q - 1) ^ t * q ^ (u - t) ≤ (q - 1) ^ m * q ^ (u - m) := by
  have hpow : (q - 1) ^ (t - m) ≤ q ^ (t - m) :=
    Nat.pow_le_pow_left (Nat.sub_le q 1) _
  calc
    (q - 1) ^ t * q ^ (u - t) =
        ((q - 1) ^ m * (q - 1) ^ (t - m)) * q ^ (u - t) := by
      rw [← Nat.pow_add]
      congr
      omega
    _ ≤ ((q - 1) ^ m * q ^ (t - m)) * q ^ (u - t) := by
      exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hpow)
    _ = (q - 1) ^ m * q ^ (u - m) := by
      rw [Nat.mul_assoc, ← Nat.pow_add]
      congr
      omega

/-- Uniform upper bound for the bad-colouring event of one reduced pair. -/
lemma card_sourceLemma42BadColouringsForPair_le {n k q : ℕ} (hq : 0 < q)
    {selected : Finset ℕ × Finset ℕ}
    (hselected : selected ∈ sourceLemma42ReducedPairs n k) :
    (sourceLemma42BadColouringsForPair n q hq selected).card ≤
      (q - 1) ^ (sourceLemma41SelectedSize k * sourceLemma41SelectedSize k) *
        q ^ ((sourceLemma42Universe n).card -
          sourceLemma41SelectedSize k * sourceLemma41SelectedSize k) := by
  obtain ⟨_, _, _, _, hsumCard, hsumSubset⟩ :=
    mem_sourceLemma42ReducedPairs.mp hselected
  rw [sourceLemma42BadColouringsForPair,
    card_sourceLemma42ColouringsMissing hq _ hsumSubset]
  exact sourceLemma42_miss_count_le_of_card_le hsumCard
    (Finset.card_le_card hsumSubset)

/-- A finite-union bound for all bad events indexed by reduced pairs. -/
lemma card_sourceLemma42BadColourings_le_reducedPairs_mul {n k q : ℕ}
    (hq : 0 < q) :
    (sourceLemma42BadColourings n k q hq).card ≤
      (sourceLemma42ReducedPairs n k).card *
        ((q - 1) ^ (sourceLemma41SelectedSize k * sourceLemma41SelectedSize k) *
          q ^ ((sourceLemma42Universe n).card -
            sourceLemma41SelectedSize k * sourceLemma41SelectedSize k)) := by
  classical
  rw [sourceLemma42BadColourings]
  exact Finset.card_biUnion_le_card_mul _ _ _
    (fun selected hselected => card_sourceLemma42BadColouringsForPair_le hq hselected)

/-- The source-sufficient global bad-colouring bound: fixed-set miss count
combined with the count of reduced pairs. -/
lemma card_sourceLemma42BadColourings_le {n k q : ℕ} (hq : 0 < q) :
    (sourceLemma42BadColourings n k q hq).card ≤
      ((sourceLemma42Universe n).card.choose (sourceLemma41SelectedSize k)) ^ 2 *
        ((q - 1) ^ (sourceLemma41SelectedSize k * sourceLemma41SelectedSize k) *
          q ^ ((sourceLemma42Universe n).card -
            sourceLemma41SelectedSize k * sourceLemma41SelectedSize k)) := by
  exact (card_sourceLemma42BadColourings_le_reducedPairs_mul hq).trans
    (Nat.mul_le_mul_right _ (card_sourceLemma42ReducedPairs_le n k))

end JSP000089

namespace JSP000089

/-- The integer logarithmic scale used by the repaired finite-colouring
argument.  The added one makes the bound meaningful at every positive `n`. -/
def sourceLemma42LogScale (n : ℕ) : ℕ :=
  n.log2 + 1

/-- The number of colours in the repaired Lemma 4.2 count.  Its reciprocal
has the source fourth-root/logarithmic scale `16 * log₂(n) / m`, with
`m = sourceLemma41SelectedSize k`, but is an actual finite integer. -/
def sourceLemma42ColourCount (n k : ℕ) : ℕ :=
  sourceLemma41SelectedSize k / (16 * sourceLemma42LogScale n)

lemma sourceLemma42LogScale_pos (n : ℕ) : 0 < sourceLemma42LogScale n := by
  simp [sourceLemma42LogScale]

lemma sourceLemma42_le_two_pow_logScale {n : ℕ} (hn : n ≠ 0) :
    n ≤ 2 ^ sourceLemma42LogScale n := by
  apply Nat.le_of_lt
  rw [sourceLemma42LogScale]
  exact (Nat.log2_lt hn).mp (Nat.lt_succ_self _)

/-- Rounding the colour count down retains the required scale inequality. -/
lemma sourceLemma42ColourCount_mul_scale_le (n k : ℕ) :
    sourceLemma42ColourCount n k * (16 * sourceLemma42LogScale n) ≤
      sourceLemma41SelectedSize k := by
  rw [sourceLemma42ColourCount]
  simpa [Nat.mul_comm] using
    (Nat.mul_div_le (sourceLemma41SelectedSize k) (16 * sourceLemma42LogScale n))

/-- In the non-coarse branch, the integer colour parameter has at least two
colours, so its distinguished colour is a proper selected class. -/
lemma two_le_sourceLemma42ColourCount {n k : ℕ}
    (hlarge : 2 * (16 * sourceLemma42LogScale n) ≤ sourceLemma41SelectedSize k) :
    2 ≤ sourceLemma42ColourCount n k := by
  rw [sourceLemma42ColourCount]
  exact (Nat.le_div_iff_mul_le
    (Nat.mul_pos (by norm_num) (sourceLemma42LogScale_pos n))).mpr
    (by simpa [Nat.mul_comm] using hlarge)

lemma sourceLemma42ColourCount_pos {n k : ℕ}
    (hlarge : 2 * (16 * sourceLemma42LogScale n) ≤ sourceLemma41SelectedSize k) :
    0 < sourceLemma42ColourCount n k :=
  lt_of_lt_of_le (by omega) (two_le_sourceLemma42ColourCount hlarge)

/-- The selected-pair sumset exponent supplies at least sixteen logarithmic
blocks of miss-event decay in the non-coarse branch. -/
lemma sourceLemma42_miss_exponent_lower {n k : ℕ}
    (hlarge : 2 * (16 * sourceLemma42LogScale n) ≤ sourceLemma41SelectedSize k) :
    16 * sourceLemma41SelectedSize k * sourceLemma42LogScale n ≤
      (sourceLemma41SelectedSize k * sourceLemma41SelectedSize k) /
        sourceLemma42ColourCount n k := by
  apply (Nat.le_div_iff_mul_le (sourceLemma42ColourCount_pos hlarge)).mpr
  have hscale := sourceLemma42ColourCount_mul_scale_le n k
  calc
    (16 * sourceLemma41SelectedSize k * sourceLemma42LogScale n) *
        sourceLemma42ColourCount n k =
      (sourceLemma42ColourCount n k * (16 * sourceLemma42LogScale n)) *
        sourceLemma41SelectedSize k := by ring
    _ ≤ sourceLemma41SelectedSize k * sourceLemma41SelectedSize k :=
      Nat.mul_le_mul_right _ hscale

/-- One `q`-block of avoided colours loses at least a factor two.  This is a
finite binomial estimate, replacing the defective Bernoulli calculation. -/
lemma sourceLemma42_two_mul_pred_pow_le_pow {q : ℕ} (hq : 2 ≤ q) :
    2 * (q - 1) ^ q ≤ q ^ q := by
  have hsub : q - 1 < q := by omega
  have hpred : q - 1 + 1 = q := Nat.sub_add_cancel (by omega)
  have hmemSub : q - 1 ∈ Finset.range (q + 1) :=
    Finset.mem_range.mpr (by omega)
  have hmemQ : q ∈ Finset.range (q + 1) :=
    Finset.mem_range.mpr (by omega)
  let f : ℕ → ℕ := fun j => (q - 1) ^ j * 1 ^ (q - j) * q.choose j
  have hsum : (∑ j ∈ ({q - 1, q} : Finset ℕ), f j) ≤
      ∑ j ∈ Finset.range (q + 1), f j :=
    Finset.sum_le_sum_of_subset (by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hmemSub
      · exact hmemQ)
  have hpow : (∑ j ∈ Finset.range (q + 1), f j) = q ^ q := by
    calc
      _ = ((q - 1) + 1) ^ q := by
        simpa only [f, one_pow, mul_one] using (add_pow (q - 1) 1 q).symm
      _ = q ^ q := by rw [hpred]
  have hchoose : q.choose (q - 1) = q := by
    calc
      q.choose (q - 1) = ((q - 1) + 1).choose (q - 1) := by rw [hpred]
      _ = (q - 1) + 1 := Nat.choose_succ_self_right _
      _ = q := hpred
  have hpair : (∑ j ∈ ({q - 1, q} : Finset ℕ), f j) =
      (q - 1) ^ (q - 1) * q + (q - 1) ^ q := by
    rw [Finset.sum_pair hsub.ne]
    simp only [f, one_pow, mul_one, Nat.choose_self]
    rw [hchoose]
  have hpowfactor : (q - 1) ^ q = (q - 1) ^ (q - 1) * (q - 1) := by
    calc
      (q - 1) ^ q = (q - 1) ^ ((q - 1) + 1) := by
        congr 1
        exact hpred.symm
      _ = (q - 1) ^ (q - 1) * (q - 1) := pow_succ _ _
  have hsplit : 2 * (q - 1) ^ q ≤
      (q - 1) ^ (q - 1) * q + (q - 1) ^ q := by
    rw [hpowfactor, two_mul]
    exact Nat.add_le_add_right
      (Nat.mul_le_mul_left _ (Nat.sub_le q 1)) _
  rw [← hpow]
  exact hsplit.trans_eq hpair.symm |>.trans hsum

/-- Repeating the one-block estimate. -/
lemma sourceLemma42_pred_pow_blocks_le {q a : ℕ} (hq : 2 ≤ q) :
    2 ^ a * (q - 1) ^ (q * a) ≤ q ^ (q * a) := by
  have h := Nat.pow_le_pow_left (sourceLemma42_two_mul_pred_pow_le_pow hq) a
  simpa [Nat.mul_pow, Nat.pow_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h

/-- The finite exponential-decay estimate for any missed set of coordinates. -/
lemma sourceLemma42_pred_pow_decay_le {q M : ℕ} (hq : 2 ≤ q) :
    2 ^ (M / q) * (q - 1) ^ M ≤ q ^ M := by
  let a := M / q
  let r := M % q
  have hM : M = q * a + r := by
    simpa [a, r] using (Nat.div_add_mod M q).symm
  change 2 ^ a * (q - 1) ^ M ≤ q ^ M
  rw [hM, Nat.pow_add, Nat.pow_add]
  calc
    2 ^ a * ((q - 1) ^ (q * a) * (q - 1) ^ r) =
        (2 ^ a * (q - 1) ^ (q * a)) * (q - 1) ^ r := by ring
    _ ≤ q ^ (q * a) * (q - 1) ^ r :=
      Nat.mul_le_mul_right _ (sourceLemma42_pred_pow_blocks_le hq)
    _ ≤ q ^ (q * a) * q ^ r := Nat.mul_le_mul_left _
      (Nat.pow_le_pow_left (Nat.sub_le q 1) _)

end JSP000089

namespace JSP000089

/-- In the non-vacuous range `k ≤ n`, the selected-pair sumset exponent fits
inside the ambient interval. -/
lemma sourceLemma42_selectedSquare_le_universe {n k : ℕ}
    (hk : 2 ^ 24 ≤ k) (hkn : k ≤ n) :
    sourceLemma41SelectedSize k * sourceLemma41SelectedSize k ≤
      (sourceLemma42Universe n).card := by
  have hmTwo : 2 ≤ sourceLemma41SelectedSize k :=
    sourceLemma41_two_le_selectedSize hk
  have hmPos : 0 < sourceLemma41SelectedSize k := by omega
  have hSquare : sourceLemma41SelectedSize k * sourceLemma41SelectedSize k ≤
      sourceLemma41SelectedSize k ^ 4 := by
    simpa [pow_two] using
      (Nat.pow_le_pow_right hmPos (by omega : 2 ≤ 4))
  calc
    _ ≤ sourceLemma41SelectedSize k ^ 4 := hSquare
    _ ≤ k := sourceLemma41_selectedSize_pow_four_le hk
    _ ≤ n := hkn
    _ = (sourceLemma42Universe n).card := by simp [sourceLemma42Universe]

/-- The reduced-pair count is at most a logarithmic-scale power of two. -/
lemma sourceLemma42_reducedPair_bound_le_power_two {n k : ℕ} (hn : n ≠ 0) :
    ((sourceLemma42Universe n).card.choose (sourceLemma41SelectedSize k)) ^ 2 ≤
      2 ^ (sourceLemma42LogScale n * (2 * sourceLemma41SelectedSize k)) := by
  have hUniverse : (sourceLemma42Universe n).card ≤
      2 ^ sourceLemma42LogScale n := by
    simpa [sourceLemma42Universe] using sourceLemma42_le_two_pow_logScale hn
  calc
    _ ≤ ((sourceLemma42Universe n).card ^ sourceLemma41SelectedSize k) ^ 2 :=
      Nat.pow_le_pow_left (Nat.choose_le_pow _ _) 2
    _ = (sourceLemma42Universe n).card ^ (sourceLemma41SelectedSize k * 2) := by
      rw [← Nat.pow_mul]
    _ ≤ (2 ^ sourceLemma42LogScale n) ^ (sourceLemma41SelectedSize k * 2) :=
      Nat.pow_le_pow_left hUniverse _
    _ = 2 ^ (sourceLemma42LogScale n * (sourceLemma41SelectedSize k * 2)) := by
      simp only [Nat.pow_mul]
    _ ≤ 2 ^ (sourceLemma42LogScale n * (2 * sourceLemma41SelectedSize k)) := by
      simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]

/-- The repaired colour count gives more decay blocks than the reduced-pair
family count, with explicit strict slack. -/
lemma sourceLemma42_reducedPair_factor_lt_decay {n k : ℕ}
    (hk : 2 ^ 24 ≤ k) (hn : n ≠ 0)
    (hlarge : 2 * (16 * sourceLemma42LogScale n) ≤ sourceLemma41SelectedSize k) :
    2 * ((sourceLemma42Universe n).card.choose (sourceLemma41SelectedSize k)) ^ 2 <
      2 ^ ((sourceLemma41SelectedSize k * sourceLemma41SelectedSize k) /
        sourceLemma42ColourCount n k) := by
  let m := sourceLemma41SelectedSize k
  let L := sourceLemma42LogScale n
  let q := sourceLemma42ColourCount n k
  have hmTwo : 2 ≤ m := by
    simpa [m] using sourceLemma41_two_le_selectedSize hk
  have hL : 1 ≤ L := by
    dsimp [L, sourceLemma42LogScale]
    omega
  have hmL : 2 ≤ m * L := by
    calc
      2 = 2 * 1 := by norm_num
      _ ≤ m * L := Nat.mul_le_mul hmTwo hL
  have hDecayExponent : 16 * m * L ≤ (m * m) / q := by
    simpa [m, L, q] using sourceLemma42_miss_exponent_lower hlarge
  have hExponent : L * (2 * m) + 1 < (m * m) / q := by
    apply lt_of_lt_of_le ?_ hDecayExponent
    calc
      L * (2 * m) + 1 = 2 * (m * L) + 1 := by ring
      _ < 16 * (m * L) := by omega
      _ = 16 * m * L := by ring
  have hFamily : ((sourceLemma42Universe n).card.choose m) ^ 2 ≤
      2 ^ (L * (2 * m)) := by
    simpa [m, L] using sourceLemma42_reducedPair_bound_le_power_two (k := k) hn
  calc
    2 * ((sourceLemma42Universe n).card.choose m) ^ 2 ≤
        2 * 2 ^ (L * (2 * m)) := Nat.mul_le_mul_left _ hFamily
    _ = 2 ^ (L * (2 * m) + 1) := by
      rw [Nat.pow_succ]
      ring
    _ < 2 ^ ((m * m) / q) := Nat.pow_lt_pow_right (by omega) hExponent

end JSP000089

namespace JSP000089

/-- Source-specific strict miss-bad comparison for the repaired finite
colouring argument.  In the non-coarse branch, fewer than half of all
colourings miss a reduced-pair sumset. -/
lemma two_mul_card_sourceLemma42BadColourings_lt {n k : ℕ}
    (hk : 2 ^ 24 ≤ k) (hn : n ≠ 0) (hkn : k ≤ n)
    (hlarge : 2 * (16 * sourceLemma42LogScale n) ≤ sourceLemma41SelectedSize k) :
    2 * (sourceLemma42BadColourings n k (sourceLemma42ColourCount n k)
      (sourceLemma42ColourCount_pos hlarge)).card <
      (sourceLemma42Colourings n (sourceLemma42ColourCount n k)).card := by
  let m := sourceLemma41SelectedSize k
  let q := sourceLemma42ColourCount n k
  let M := m * m
  let N := (sourceLemma42Universe n).card
  have hqTwo : 2 ≤ q := by
    simpa [q] using two_le_sourceLemma42ColourCount hlarge
  have hqPos : 0 < q := by omega
  have hMN : M ≤ N := by
    simpa [m, M, N] using sourceLemma42_selectedSquare_le_universe hk hkn
  have hFactor : 2 * (N.choose m) ^ 2 < 2 ^ (M / q) := by
    simpa [m, M, N, q] using sourceLemma42_reducedPair_factor_lt_decay hk hn hlarge
  have hDecay : 2 ^ (M / q) * (q - 1) ^ M ≤ q ^ M :=
    sourceLemma42_pred_pow_decay_le hqTwo
  have hXPos : 0 < (q - 1) ^ M * q ^ (N - M) := by
    exact Nat.mul_pos (pow_pos (by omega) _) (pow_pos hqPos _)
  have hScaled : (2 * (N.choose m) ^ 2) * ((q - 1) ^ M * q ^ (N - M)) <
      2 ^ (M / q) * ((q - 1) ^ M * q ^ (N - M)) :=
    (Nat.mul_lt_mul_right hXPos).mpr hFactor
  have hBound := card_sourceLemma42BadColourings_le (n := n) (k := k) (q := q) hqPos
  have hBound' : (sourceLemma42BadColourings n k q hqPos).card ≤
      (N.choose m) ^ 2 * ((q - 1) ^ M * q ^ (N - M)) := by
    simpa [m, M, N] using hBound
  change 2 * (sourceLemma42BadColourings n k q hqPos).card <
    (sourceLemma42Colourings n q).card
  rw [card_sourceLemma42Colourings]
  calc
    2 * (sourceLemma42BadColourings n k q hqPos).card ≤
        2 * (N.choose m) ^ 2 * ((q - 1) ^ M * q ^ (N - M)) := by
      simpa [Nat.mul_assoc] using Nat.mul_le_mul_left 2 hBound'
    _ < 2 ^ (M / q) * ((q - 1) ^ M * q ^ (N - M)) := hScaled
    _ = (2 ^ (M / q) * (q - 1) ^ M) * q ^ (N - M) := by ring
    _ ≤ q ^ M * q ^ (N - M) := Nat.mul_le_mul_right _ hDecay
    _ = q ^ N := by
      rw [← Nat.pow_add]
      congr 1
      exact Nat.add_sub_of_le hMN

end JSP000089

namespace JSP000089

/-- Colourings selecting the distinguished colour at one fixed ambient
coordinate.  This is the finite double-counting fibre for selected classes. -/
noncomputable def sourceLemma42ColouringsSelectingAt (n q : ℕ) (hq : 0 < q)
    (x : sourceLemma42Universe n) : Finset (sourceLemma42Universe n → Fin q) := by
  classical
  exact Fintype.piFinset fun y =>
    if y.val ∈ ({x.val} : Finset ℕ) then {sourceLemma42SelectedColour q hq}
    else Finset.univ

lemma mem_sourceLemma42ColouringsSelectingAt {n q : ℕ} (hq : 0 < q)
    (x : sourceLemma42Universe n) (colouring : sourceLemma42Universe n → Fin q) :
    colouring ∈ sourceLemma42ColouringsSelectingAt n q hq x ↔
      colouring x = sourceLemma42SelectedColour q hq := by
  classical
  rw [sourceLemma42ColouringsSelectingAt, Fintype.mem_piFinset]
  constructor
  · intro h
    simpa using h x
  · intro h y
    by_cases heq : y = x
    · subst y
      simpa using h
    · have hval : y.val ≠ x.val := fun e => heq (Subtype.ext e)
      simp [hval]

/-- Exact count of colourings selecting the distinguished colour at one
coordinate. -/
lemma card_sourceLemma42ColouringsSelectingAt {n q : ℕ} (hq : 0 < q)
    (x : sourceLemma42Universe n) :
    (sourceLemma42ColouringsSelectingAt n q hq x).card =
      q ^ ((sourceLemma42Universe n).card - 1) := by
  classical
  have hT : ({x.val} : Finset ℕ) ⊆ sourceLemma42Universe n := by
    simpa using x.property
  rw [sourceLemma42ColouringsSelectingAt, Fintype.card_piFinset]
  calc
    (∏ y : sourceLemma42Universe n,
        (if y.val ∈ ({x.val} : Finset ℕ) then {sourceLemma42SelectedColour q hq}
        else Finset.univ).card) =
        ∏ y : sourceLemma42Universe n,
          if y.val ∈ ({x.val} : Finset ℕ) then 1 else q := by
      apply Finset.prod_congr rfl
      intro y hy
      split_ifs with hmem <;> simp
    _ = (∏ y ∈ (Finset.univ.filter fun y : sourceLemma42Universe n =>
        y.val ∈ ({x.val} : Finset ℕ)), 1) *
        ∏ y ∈ (Finset.univ.filter fun y : sourceLemma42Universe n =>
          y.val ∉ ({x.val} : Finset ℕ)), q := by
      rw [Finset.prod_ite]
    _ = q ^ ((sourceLemma42Universe n).card - 1) := by
      simp only [Finset.prod_const, Nat.one_pow, Finset.card_singleton]
      rw [card_sourceLemma42ColouringCoordinates_not_mem ({x.val} : Finset ℕ) hT]
      simp


/-- The finite set of pairs consisting of an ambient coordinate and a colouring
that selects the distinguished colour at that coordinate. -/
noncomputable def sourceLemma42SelectedColourIncidences (n q : ℕ) (hq : 0 < q) :
    Finset ((x : sourceLemma42Universe n) × (sourceLemma42Universe n → Fin q)) := by
  classical
  exact (Finset.univ : Finset (sourceLemma42Universe n)).sigma
    (sourceLemma42ColouringsSelectingAt n q hq)

/-- Exact division-free count of selected-colour incidences. -/
lemma card_sourceLemma42SelectedColourIncidences {n q : ℕ} (hq : 0 < q) :
    (sourceLemma42SelectedColourIncidences n q hq).card =
      (sourceLemma42Universe n).card * q ^ ((sourceLemma42Universe n).card - 1) := by
  classical
  rw [sourceLemma42SelectedColourIncidences, Finset.card_sigma]
  simp_rw [card_sourceLemma42ColouringsSelectingAt hq]
  simp [Finset.sum_const]

end JSP000089

namespace JSP000089

/-- A selected colour class can be counted as its coordinate-wise indicator
sum over the ambient finite interval. -/
lemma card_sourceLemma42SelectedColourClass_eq_indicator_sum {n q : ℕ} (hq : 0 < q)
    (colouring : sourceLemma42Universe n → Fin q) :
    (sourceLemma42SelectedColourClass hq colouring).card =
      ∑ x : sourceLemma42Universe n,
        if colouring x = sourceLemma42SelectedColour q hq then 1 else 0 := by
  classical
  rw [sourceLemma42SelectedColourClass]
  have hInj : Set.InjOn Subtype.val
      (↑(Finset.univ.filter fun x : sourceLemma42Universe n =>
        colouring x = sourceLemma42SelectedColour q hq) : Set (sourceLemma42Universe n)) := by
    intro x hx y hy hxy
    exact Subtype.ext hxy
  rw [Finset.card_image_iff.mpr hInj]
  induction (Finset.univ : Finset (sourceLemma42Universe n)) using Finset.induction_on with
  | empty => simp
  | insert x s hx ih =>
      by_cases hcolour : colouring x = sourceLemma42SelectedColour q hq <;> simp [hcolour, hx, ih]

/-- Summing the selected-colour indicator over a finite colouring family counts
exactly the colourings in its corresponding fibre. -/
lemma sourceLemma42_indicator_sum_eq_card_filter {n q : ℕ} (hq : 0 < q)
    (x : sourceLemma42Universe n) (s : Finset (sourceLemma42Universe n → Fin q)) :
    (∑ colouring ∈ s,
      if colouring x = sourceLemma42SelectedColour q hq then 1 else 0) =
      (s.filter fun colouring =>
        colouring x = sourceLemma42SelectedColour q hq).card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert colouring s hcolouring ih =>
      by_cases hselected : colouring x = sourceLemma42SelectedColour q hq <;>
        simp [hcolouring, hselected, ih]

/-- The fixed-coordinate fibre is the corresponding filter of the full
uniform colouring space. -/
lemma sourceLemma42ColouringsSelectingAt_eq_filter {n q : ℕ} (hq : 0 < q)
    (x : sourceLemma42Universe n) :
    sourceLemma42ColouringsSelectingAt n q hq x =
      (sourceLemma42Colourings n q).filter fun colouring =>
        colouring x = sourceLemma42SelectedColour q hq := by
  classical
  ext colouring
  rw [Finset.mem_filter]
  constructor
  · intro h
    exact ⟨by simp [sourceLemma42Colourings],
      (mem_sourceLemma42ColouringsSelectingAt hq x colouring).mp h⟩
  · rintro ⟨_, h⟩
    exact (mem_sourceLemma42ColouringsSelectingAt hq x colouring).mpr h

end JSP000089

namespace JSP000089

/-- Exact first-moment identity for the distinguished selected colour class. -/
lemma sum_card_sourceLemma42SelectedColourClass {n q : ℕ} (hq : 0 < q) :
    (∑ colouring in sourceLemma42Colourings n q,
      (sourceLemma42SelectedColourClass hq colouring).card) =
      (sourceLemma42Universe n).card * q ^ ((sourceLemma42Universe n).card - 1) := by
  classical
  calc
    (∑ colouring in sourceLemma42Colourings n q,
        (sourceLemma42SelectedColourClass hq colouring).card) =
        ∑ colouring in sourceLemma42Colourings n q,
          ∑ x : sourceLemma42Universe n,
            if colouring x = sourceLemma42SelectedColour q hq then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro colouring hcolouring
      exact card_sourceLemma42SelectedColourClass_eq_indicator_sum hq colouring
    _ = ∑ x : sourceLemma42Universe n,
          ∑ colouring in sourceLemma42Colourings n q,
            if colouring x = sourceLemma42SelectedColour q hq then 1 else 0 :=
      Finset.sum_comm
    _ = ∑ x : sourceLemma42Universe n,
          (sourceLemma42ColouringsSelectingAt n q hq x).card := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [sourceLemma42_indicator_sum_eq_card_filter hq]
      exact congrArg Finset.card
        (sourceLemma42ColouringsSelectingAt_eq_filter hq x).symm
    _ = (sourceLemma42Universe n).card * q ^ ((sourceLemma42Universe n).card - 1) := by
      simp_rw [card_sourceLemma42ColouringsSelectingAt hq]
      simp [Finset.sum_const]

end JSP000089

namespace JSP000089

/-- The proof-local rounded size budget for one distinguished colour class.
The ceiling is essential for the exact finite half-event estimate. -/
def sourceLemma42SelectedClassBudget (n k : ℕ) : ℕ :=
  2 * ((sourceLemma42Universe n).card ⌈/⌉ sourceLemma42ColourCount n k)

/-- The rounded budget is large enough for the elementary Markov numerator. -/
lemma two_mul_card_sourceLemma42Universe_le_colourCount_mul_budget {n k : ℕ}
    (hq : 0 < sourceLemma42ColourCount n k) :
    2 * (sourceLemma42Universe n).card ≤
      sourceLemma42ColourCount n k * sourceLemma42SelectedClassBudget n k := by
  have hceil : (sourceLemma42Universe n).card ≤
      sourceLemma42ColourCount n k *
        ((sourceLemma42Universe n).card ⌈/⌉ sourceLemma42ColourCount n k) :=
    by simpa using (le_smul_ceilDiv (a := sourceLemma42ColourCount n k)
      (b := (sourceLemma42Universe n).card) hq)
  calc
    2 * (sourceLemma42Universe n).card ≤
        2 * (sourceLemma42ColourCount n k *
          ((sourceLemma42Universe n).card ⌈/⌉ sourceLemma42ColourCount n k)) :=
      Nat.mul_le_mul_left 2 hceil
    _ = sourceLemma42ColourCount n k * sourceLemma42SelectedClassBudget n k := by
      simp [sourceLemma42SelectedClassBudget]
      ring

end JSP000089

namespace JSP000089

/-- The proof-local event that the distinguished selected colour class exceeds
its rounded finite budget. -/
noncomputable def sourceLemma42OversizedColourings (n k : ℕ)
    (hq : 0 < sourceLemma42ColourCount n k) :
    Finset (sourceLemma42Universe n → Fin (sourceLemma42ColourCount n k)) := by
  classical
  exact (sourceLemma42Colourings n (sourceLemma42ColourCount n k)).filter fun colouring =>
    sourceLemma42SelectedClassBudget n k <
      (sourceLemma42SelectedColourClass hq colouring).card

/-- Membership in the oversized event is exactly failure of the selected-class
size budget. -/
lemma mem_sourceLemma42OversizedColourings_iff {n k : ℕ}
    (hq : 0 < sourceLemma42ColourCount n k)
    (colouring : sourceLemma42Universe n → Fin (sourceLemma42ColourCount n k)) :
    colouring ∈ sourceLemma42OversizedColourings n k hq ↔
      colouring ∈ sourceLemma42Colourings n (sourceLemma42ColourCount n k) ∧
        sourceLemma42SelectedClassBudget n k <
          (sourceLemma42SelectedColourClass hq colouring).card := by
  simp [sourceLemma42OversizedColourings]

end JSP000089
namespace JSP000089

/-- The sum of selected-class sizes over oversized colourings is bounded by
the corresponding sum over the whole colouring space. -/
lemma sum_card_sourceLemma42OversizedColourings_le {n k : ℕ}
    (hq : 0 < sourceLemma42ColourCount n k) :
    (∑ colouring ∈ sourceLemma42OversizedColourings n k hq,
      (sourceLemma42SelectedColourClass hq colouring).card) ≤
      ∑ colouring ∈ sourceLemma42Colourings n (sourceLemma42ColourCount n k),
        (sourceLemma42SelectedColourClass hq colouring).card := by
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
  intro colouring hcolouring hnot
  exact Nat.zero_le _

end JSP000089
namespace JSP000089

/-- Every oversized colouring contributes at least the budget to the selected
class-size sum. -/
lemma budget_mul_card_sourceLemma42OversizedColourings_le_sum {n k : ℕ}
    (hq : 0 < sourceLemma42ColourCount n k) :
    sourceLemma42SelectedClassBudget n k *
      (sourceLemma42OversizedColourings n k hq).card ≤
      ∑ colouring ∈ sourceLemma42OversizedColourings n k hq,
        (sourceLemma42SelectedColourClass hq colouring).card := by
  simpa [nsmul_eq_mul, Nat.mul_comm] using
    (Finset.card_nsmul_le_sum (sourceLemma42OversizedColourings n k hq)
      (fun colouring => (sourceLemma42SelectedColourClass hq colouring).card)
      (sourceLemma42SelectedClassBudget n k)
      (fun colouring hcolouring => Nat.le_of_lt
        (mem_sourceLemma42OversizedColourings_iff hq colouring |>.mp hcolouring).2))

/-- The ambient interval has positive cardinality whenever its endpoint is
positive. -/
lemma sourceLemma42Universe_card_pos {n : ℕ} (hn : n ≠ 0) :
    0 < (sourceLemma42Universe n).card := by
  have hmem : 1 ∈ sourceLemma42Universe n := by
    simp [sourceLemma42Universe, Nat.one_le_iff_ne_zero.mpr hn]
  exact Finset.card_pos.mpr ⟨1, hmem⟩

/-- First-moment upper bound for the cardinality of the oversized event. -/
lemma budget_mul_card_sourceLemma42OversizedColourings_le {n k : ℕ}
    (hq : 0 < sourceLemma42ColourCount n k) :
    sourceLemma42SelectedClassBudget n k *
      (sourceLemma42OversizedColourings n k hq).card ≤
      (sourceLemma42Universe n).card *
        (sourceLemma42ColourCount n k) ^ ((sourceLemma42Universe n).card - 1) := by
  calc
    sourceLemma42SelectedClassBudget n k *
        (sourceLemma42OversizedColourings n k hq).card ≤
        ∑ colouring ∈ sourceLemma42OversizedColourings n k hq,
          (sourceLemma42SelectedColourClass hq colouring).card :=
      budget_mul_card_sourceLemma42OversizedColourings_le_sum hq
    _ ≤ ∑ colouring ∈ sourceLemma42Colourings n (sourceLemma42ColourCount n k),
          (sourceLemma42SelectedColourClass hq colouring).card :=
      sum_card_sourceLemma42OversizedColourings_le hq
    _ = (sourceLemma42Universe n).card *
        (sourceLemma42ColourCount n k) ^ ((sourceLemma42Universe n).card - 1) :=
      sum_card_sourceLemma42SelectedColourClass hq

end JSP000089
namespace JSP000089

/-- In the non-coarse regime, at most half of uniform colourings have an
oversized distinguished colour class. -/
lemma two_mul_card_sourceLemma42OversizedColourings_le {n k : ℕ}
    (hn : n ≠ 0) (hq : 0 < sourceLemma42ColourCount n k) :
    2 * (sourceLemma42OversizedColourings n k hq).card ≤
      (sourceLemma42Colourings n (sourceLemma42ColourCount n k)).card := by
  let N := (sourceLemma42Universe n).card
  let q := sourceLemma42ColourCount n k
  let B := sourceLemma42SelectedClassBudget n k
  let e := (sourceLemma42OversizedColourings n k hq).card
  let R := q ^ (N - 1)
  have hN : 0 < N := by simpa [N] using sourceLemma42Universe_card_pos hn
  have hBudget : 2 * N ≤ q * B := by
    simpa [N, q, B] using two_mul_card_sourceLemma42Universe_le_colourCount_mul_budget hq
  have hMoment : B * e ≤ N * R := by
    simpa [N, q, B, e, R] using budget_mul_card_sourceLemma42OversizedColourings_le hq
  have hScaled : q * (B * e) ≤ q * (N * R) := Nat.mul_le_mul_left q hMoment
  have hCore : N * (2 * e) ≤ N * (q * R) := by
    calc
      N * (2 * e) = (2 * N) * e := by ring
      _ ≤ (q * B) * e := Nat.mul_le_mul_right e hBudget
      _ = q * (B * e) := by ring
      _ ≤ q * (N * R) := hScaled
      _ = N * (q * R) := by ring
  have hHalf : 2 * e ≤ q * R := Nat.le_of_mul_le_mul_left hCore hN
  change 2 * e ≤ (sourceLemma42Colourings n q).card
  rw [card_sourceLemma42Colourings]
  change 2 * e ≤ q ^ N
  rw [show N = (N - 1) + 1 by omega, Nat.pow_succ]
  simpa [R, Nat.mul_comm] using hHalf

end JSP000089
namespace JSP000089

/-- The proof-local union of the miss-bad and oversized colouring events. -/
noncomputable def sourceLemma42CombinedBadColourings (n k : ℕ)
    (hq : 0 < sourceLemma42ColourCount n k) :
    Finset (sourceLemma42Universe n → Fin (sourceLemma42ColourCount n k)) :=
  sourceLemma42BadColourings n k (sourceLemma42ColourCount n k) hq ∪
    sourceLemma42OversizedColourings n k hq

lemma mem_sourceLemma42CombinedBadColourings_iff {n k : ℕ}
    (hq : 0 < sourceLemma42ColourCount n k)
    (colouring : sourceLemma42Universe n → Fin (sourceLemma42ColourCount n k)) :
    colouring ∈ sourceLemma42CombinedBadColourings n k hq ↔
      colouring ∈ sourceLemma42BadColourings n k (sourceLemma42ColourCount n k) hq ∨
        colouring ∈ sourceLemma42OversizedColourings n k hq := by
  simp [sourceLemma42CombinedBadColourings]

lemma card_sourceLemma42CombinedBadColourings_lt {n k : ℕ}
    (hn : n ≠ 0) (hlarge : 2 * (16 * sourceLemma42LogScale n) ≤ sourceLemma41SelectedSize k)
    (hk : 2 ^ 24 ≤ k) (hkn : k ≤ n) :
    (sourceLemma42CombinedBadColourings n k (sourceLemma42ColourCount_pos hlarge)).card <
      (sourceLemma42Colourings n (sourceLemma42ColourCount n k)).card := by
  let q := sourceLemma42ColourCount n k
  let hq := sourceLemma42ColourCount_pos hlarge
  have hMiss : 2 * (sourceLemma42BadColourings n k q hq).card <
      (sourceLemma42Colourings n q).card := by
    simpa [q, hq] using two_mul_card_sourceLemma42BadColourings_lt hk hn hkn hlarge
  have hOver : 2 * (sourceLemma42OversizedColourings n k hq).card ≤
      (sourceLemma42Colourings n q).card := by
    simpa [q, hq] using two_mul_card_sourceLemma42OversizedColourings_le hn hq
  change (sourceLemma42BadColourings n k q hq ∪
    sourceLemma42OversizedColourings n k hq).card < (sourceLemma42Colourings n q).card
  exact (Finset.card_union_le _ _).trans_lt (by omega)

lemma sourceLemma42BadColourings_subset {n k q : ℕ} (hq : 0 < q) :
    sourceLemma42BadColourings n k q hq ⊆ sourceLemma42Colourings n q := by
  intro colouring hbad
  obtain ⟨selected, hselected, hdisjoint⟩ :=
    (mem_sourceLemma42BadColourings_iff hq colouring).mp hbad
  have hpair : colouring ∈ sourceLemma42BadColouringsForPair n q hq selected :=
    (mem_sourceLemma42BadColouringsForPair_iff hq selected colouring).mpr hdisjoint
  exact sourceLemma42ColouringsMissing_subset hq _ hpair

lemma sourceLemma42CombinedBadColourings_subset {n k : ℕ}
    (hq : 0 < sourceLemma42ColourCount n k) :
    sourceLemma42CombinedBadColourings n k hq ⊆
      sourceLemma42Colourings n (sourceLemma42ColourCount n k) := by
  intro colouring hcombined
  rcases (mem_sourceLemma42CombinedBadColourings_iff hq colouring).mp hcombined with hbad | hover
  · exact sourceLemma42BadColourings_subset hq hbad
  · exact Finset.filter_subset _ _ hover

theorem sourceLemma42_exists_goodSmallSelectedSet {n k : ℕ}
    (hk : 2 ^ 24 ≤ k) (hn : n ≠ 0) (hkn : k ≤ n)
    (hlarge : 2 * (16 * sourceLemma42LogScale n) ≤ sourceLemma41SelectedSize k) :
    ∃ S, S ⊆ sourceLemma42Universe n ∧ S.card ≤ sourceLemma42SelectedClassBudget n k ∧
      sourceLemma42HitsReducedPairs n k S := by
  let q := sourceLemma42ColourCount n k
  let hq := sourceLemma42ColourCount_pos hlarge
  let bad := sourceLemma42CombinedBadColourings n k hq
  let all := sourceLemma42Colourings n q
  have hcard : bad.card < all.card := by
    simpa [bad, all, q, hq] using card_sourceLemma42CombinedBadColourings_lt hn hlarge hk hkn
  obtain ⟨colouring, hmem, hnot⟩ := Finset.exists_mem_not_mem_of_card_lt_card hcard
  let S := sourceLemma42SelectedColourClass hq colouring
  have hnotBad : colouring ∉ sourceLemma42BadColourings n k q hq := by
    intro h
    exact hnot ((mem_sourceLemma42CombinedBadColourings_iff hq colouring).mpr (Or.inl h))
  have hnotOver : colouring ∉ sourceLemma42OversizedColourings n k hq := by
    intro h
    exact hnot ((mem_sourceLemma42CombinedBadColourings_iff hq colouring).mpr (Or.inr h))
  refine ⟨S, sourceLemma42SelectedColourClass_subset hq colouring, ?_, ?_⟩
  · exact Nat.le_of_not_lt (fun h => hnotOver
      ((mem_sourceLemma42OversizedColourings_iff hq colouring).mpr ⟨hmem, h⟩))
  · refine ⟨sourceLemma42SelectedColourClass_subset hq colouring, ?_⟩
    intro selected hselected
    by_contra hnone
    have heq : S ∩ additiveSumset selected.1 selected.2 = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hnone
    have hdisjoint : Disjoint S (additiveSumset selected.1 selected.2) := by
      rw [Finset.disjoint_left]
      intro x hxS hxT
      have hx : x ∈ S ∩ additiveSumset selected.1 selected.2 :=
        Finset.mem_inter.mpr ⟨hxS, hxT⟩
      rw [heq] at hx
      exact Finset.not_mem_empty _ hx
    exact hnotBad ((mem_sourceLemma42BadColourings_iff hq colouring).mpr
      ⟨selected, hselected, hdisjoint⟩)

end JSP000089


namespace JSP000089

/-- The explicit proof-local budget joining the coarse and non-coarse
range-contained branches of the repaired Lemma 4.2 argument. -/
def sourceLemma42FinalBudget (n k : ℕ) : ℕ :=
  if 2 * (16 * sourceLemma42LogScale n) ≤ sourceLemma41SelectedSize k then
    sourceLemma42SelectedClassBudget n k else n

theorem sourceLemma42_rangeContained_repaired {n k : ℕ}
    (hk : 2 ^ 24 ≤ k) (hkn : k ≤ n) :
    ∃ S, S ⊆ sourceLemma42Universe n ∧ S.card ≤ sourceLemma42FinalBudget n k ∧
      ∀ A B, A ⊆ sourceLemma42Universe n → B ⊆ sourceLemma42Universe n →
        k ≤ A.card → k ≤ B.card → additiveSumset A B ⊆ sourceLemma42Universe n →
          (S ∩ additiveSumset A B).Nonempty := by
  have hn : n ≠ 0 := by
    exact ne_of_gt (lt_of_lt_of_le (by norm_num : 0 < 2 ^ 24) (le_trans hk hkn))
  by_cases hlarge : 2 * (16 * sourceLemma42LogScale n) ≤ sourceLemma41SelectedSize k
  · obtain ⟨S, hS, hcard, hhits⟩ :=
      sourceLemma42_exists_goodSmallSelectedSet hk hn hkn hlarge
    refine ⟨S, hS, ?_, ?_⟩
    · simpa [sourceLemma42FinalBudget, hlarge] using hcard
    · intro A B hA hB hAcard hBcard hrange
      exact sourceLemma42_largePairs_hit_of_hitsReducedPairs hk hhits hA hB hAcard hBcard hrange
  · exact sourceLemma42_rangeContained_of_universe_budget hk
      (by simp [sourceLemma42FinalBudget, hlarge])

end JSP000089

namespace JSP000089

lemma sourceLemma42_quotient_bridge {m d : ℕ} (hd : 0 < d) (hlarge : 2 * d ≤ m) :
    m ≤ 2 * (m / d) * d := by
  have hq : 2 ≤ m / d := (Nat.le_div_iff_mul_le hd).mpr (by simpa [Nat.mul_comm] using hlarge)
  have hmod : m % d < d := Nat.mod_lt _ hd
  have hdecomp : m = m % d + d * (m / d) := (Nat.mod_add_div _ _).symm
  calc
    m = m % d + d * (m / d) := hdecomp
    _ ≤ d + d * (m / d) := Nat.add_le_add_right (Nat.le_of_lt hmod) _
    _ ≤ 2 * (m / d) * d := by
      calc
        d + d * (m / d) = ((m / d) + 1) * d := by ring
        _ ≤ (2 * (m / d)) * d := Nat.mul_le_mul_right d (by omega)
        _ = 2 * (m / d) * d := by ring

lemma sourceLemma42_selectedSize_quotient_bridge {n k : ℕ}
    (hlarge : 2 * (16 * sourceLemma42LogScale n) ≤ sourceLemma41SelectedSize k) :
    sourceLemma41SelectedSize k ≤ 2 * sourceLemma42ColourCount n k *
      (16 * sourceLemma42LogScale n) := by
  simpa [sourceLemma42ColourCount] using
    sourceLemma42_quotient_bridge (m := sourceLemma41SelectedSize k)
      (d := 16 * sourceLemma42LogScale n)
      (Nat.mul_pos (by norm_num) (sourceLemma42LogScale_pos n)) hlarge

end JSP000089

namespace JSP000089

lemma sourceLemma42_ceilDiv_le_div_add_one {a q : ℕ} (hq : 0 < q) :
    a ⌈/⌉ q ≤ a / q + 1 := by
  apply (ceilDiv_le_iff_le_mul hq).mpr
  have hmod : a % q < q := Nat.mod_lt _ hq
  calc
    a = a % q + q * (a / q) := (Nat.mod_add_div _ _).symm
    _ ≤ q + q * (a / q) := Nat.add_le_add_right (Nat.le_of_lt hmod) _
    _ = q * (a / q + 1) := by ring

end JSP000089

namespace JSP000089

lemma sourceLemma42_selectedClassBudget_quantitative_noncoarse {n k : ℕ}
    (hk : 2 ^ 24 ≤ k) (hkn : k ≤ n)
    (hlarge : 2 * (16 * sourceLemma42LogScale n) ≤ sourceLemma41SelectedSize k) :
    sourceLemma41SelectedSize k * sourceLemma42SelectedClassBudget n k ≤
      68 * n * sourceLemma42LogScale n := by
  let m := sourceLemma41SelectedSize k
  let L := sourceLemma42LogScale n
  let q := sourceLemma42ColourCount n k
  have hq : 0 < q := by simpa [q] using sourceLemma42ColourCount_pos hlarge
  have hbridge0 := sourceLemma42_selectedSize_quotient_bridge hlarge
  have hbridge : m ≤ 32 * q * L := by
    calc
      m ≤ 2 * q * (16 * L) := by simpa [m, q, L] using hbridge0
      _ = 32 * q * L := by ring
  have hceil : n ⌈/⌉ q ≤ n / q + 1 := sourceLemma42_ceilDiv_le_div_add_one hq
  have hfloor : q * (n / q) ≤ n := by
    simpa [Nat.mul_comm] using Nat.div_mul_le_self n q
  have hscale : q * (16 * L) ≤ m := by
    simpa [m, q, L] using sourceLemma42ColourCount_mul_scale_le n k
  have hm : m ≤ n := (sourceLemma41_selectedSize_le hk).trans hkn
  have hL : 1 ≤ L := Nat.succ_le_iff.mpr (sourceLemma42LogScale_pos n)
  simp [sourceLemma42SelectedClassBudget, sourceLemma42Universe, m, q, L]
  nlinarith

end JSP000089

namespace JSP000089

theorem sourceLemma42_finalBudget_quantitative_bound {n k : ℕ}
    (hk : 2 ^ 24 ≤ k) (hkn : k ≤ n) :
    sourceLemma41SelectedSize k * sourceLemma42FinalBudget n k ≤
      68 * n * sourceLemma42LogScale n := by
  by_cases hlarge : 2 * (16 * sourceLemma42LogScale n) ≤ sourceLemma41SelectedSize k
  · simpa [sourceLemma42FinalBudget, hlarge] using
      sourceLemma42_selectedClassBudget_quantitative_noncoarse hk hkn hlarge
  · have hcoarse : sourceLemma41SelectedSize k < 32 * sourceLemma42LogScale n := by
      omega
    rw [sourceLemma42FinalBudget, if_neg hlarge]
    nlinarith

end JSP000089


namespace JSP000089

/-- The dyadic interval `I_j = [2^(j-1), 2^j - 1]` used in the source proof
of Lemma 4.3. Keeping the endpoints integral makes its later use with the
range-contained repair of Lemma 4.2 exact. -/
def sourceLemma43DyadicBlock (j : ℕ) : Finset ℕ :=
  Finset.Icc (2 ^ (j - 1)) (2 ^ j - 1)

/-- Every positive natural belongs to a source dyadic block. This gives the
finite block partition used by the Lemma 4.3 extraction argument. -/
lemma sourceLemma43_exists_mem_dyadicBlock {x : ℕ} (hx : 0 < x) :
    ∃ j : ℕ, 1 ≤ j ∧ x ∈ sourceLemma43DyadicBlock j := by
  refine ⟨Nat.log 2 x + 1, by omega, ?_⟩
  rw [sourceLemma43DyadicBlock, Finset.mem_Icc]
  have hlow : 2 ^ Nat.log 2 x ≤ x :=
    Nat.pow_log_le_self 2 (Nat.ne_of_gt hx)
  have hupp0 : x < 2 ^ (Nat.log 2 x).succ :=
    Nat.lt_pow_succ_log_self (by norm_num) x
  have hupp : x ≤ 2 ^ (Nat.log 2 x + 1) - 1 := by omega
  simpa using And.intro hlow hupp

/-- Every dyadic block used at scale `r` lies in the ambient interval on
which the source invokes Lemma 4.2. -/
lemma sourceLemma43DyadicBlock_subset_universe {r j : ℕ} (hj : j ≤ r) :
    sourceLemma43DyadicBlock j ⊆ sourceLemma42Universe (2 ^ (r + 1)) := by
  intro x hx
  rw [sourceLemma43DyadicBlock, Finset.mem_Icc] at hx
  rw [sourceLemma42Universe, Finset.mem_Icc]
  constructor
  · have hpos : 0 < 2 ^ (j - 1) := pow_pos (by norm_num) _
    omega
  · have hpow : 2 ^ j ≤ 2 ^ r := Nat.pow_le_pow_right (by omega) hj
    calc
      x ≤ 2 ^ j - 1 := hx.2
      _ ≤ 2 ^ r := (Nat.sub_le _ _).trans hpow
      _ ≤ 2 ^ (r + 1) := by
        rw [pow_succ]
        nlinarith [pow_pos (by norm_num : 0 < 2) r]

/-- A dyadic block itself is contained in the interval ending at its upper power of two. -/
lemma sourceLemma43DyadicBlock_subset_ownUniverse (j : ℕ) :
    sourceLemma43DyadicBlock j ⊆ sourceLemma42Universe (2 ^ j) := by
  intro x hx
  rw [sourceLemma43DyadicBlock, Finset.mem_Icc] at hx
  rw [sourceLemma42Universe, Finset.mem_Icc]
  constructor
  · have hpos : 0 < 2 ^ (j - 1) := pow_pos (by norm_num) _
    omega
  · exact hx.2.trans (Nat.sub_le _ _)

/-- The source dyadic localization: if the first summand comes from the
largest occupied block, then all ordinary sums lie in that block or the next
one. -/
lemma sourceLemma43_additiveSumset_subset_dyadicUnion
    {r s : ℕ} (hs : s ≤ r) {A B : Finset ℕ}
    (hA : A ⊆ sourceLemma43DyadicBlock r)
    (hB : B ⊆ sourceLemma43DyadicBlock s) :
    additiveSumset A B ⊆
      sourceLemma43DyadicBlock r ∪ sourceLemma43DyadicBlock (r + 1) := by
  intro z hz
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_image₂.mp hz
  have haI : 2 ^ (r - 1) ≤ a ∧ a ≤ 2 ^ r - 1 := by
    simpa [sourceLemma43DyadicBlock] using Finset.mem_Icc.mp (hA ha)
  have hbI : 2 ^ (s - 1) ≤ b ∧ b ≤ 2 ^ s - 1 := by
    simpa [sourceLemma43DyadicBlock] using Finset.mem_Icc.mp (hB hb)
  have hbpos : 0 < b := by
    have hpowpos : 0 < 2 ^ (s - 1) := pow_pos (by norm_num) _
    omega
  have hpow : 2 ^ s ≤ 2 ^ r := Nat.pow_le_pow_right (by omega) hs
  have hlow : 2 ^ (r - 1) ≤ a + b := by omega
  have hb_le : b ≤ 2 ^ r - 1 :=
    hbI.2.trans (Nat.sub_le_sub_right hpow 1)
  have hupp0 : a + b ≤ (2 ^ r - 1) + (2 ^ r - 1) :=
    Nat.add_le_add haI.2 hb_le
  have hupp : a + b ≤ 2 ^ (r + 1) - 1 := by
    rw [pow_succ]
    have hpowpos : 0 < 2 ^ r := pow_pos (by norm_num) _
    omega
  by_cases hsplit : a + b ≤ 2 ^ r - 1
  · apply Finset.mem_union_left
    exact Finset.mem_Icc.mpr ⟨hlow, hsplit⟩
  · apply Finset.mem_union_right
    have hnext : 2 ^ r ≤ a + b := by omega
    exact Finset.mem_Icc.mpr ⟨by simpa using hnext, hupp⟩

/-- A single source Lemma 4.2 set, restricted to the two dyadic blocks where
source Lemma 4.3 needs it, still hits every qualifying localized pair. This
is the finite gluing kernel; the infinite union and sparsity estimate are
intentionally left to the subsequent source obligation. -/
theorem sourceLemma43_exists_blockLocalisedHittingSet
    {r s k : ℕ} (hk : 2 ^ 24 ≤ k) (hkRange : k ≤ 2 ^ (r + 1))
    (hs : s ≤ r) :
    ∃ S, S ⊆ sourceLemma43DyadicBlock r ∪ sourceLemma43DyadicBlock (r + 1) ∧
      S.card ≤ sourceLemma42FinalBudget (2 ^ (r + 1)) k ∧
      ∀ A B, A ⊆ sourceLemma43DyadicBlock r →
        B ⊆ sourceLemma43DyadicBlock s → k ≤ A.card → k ≤ B.card →
        (S ∩ additiveSumset A B).Nonempty := by
  obtain ⟨T, hTsub, hTcard, hThit⟩ :=
    sourceLemma42_rangeContained_repaired hk hkRange
  let D := sourceLemma43DyadicBlock r ∪ sourceLemma43DyadicBlock (r + 1)
  refine ⟨T ∩ D, Finset.inter_subset_right, ?_, ?_⟩
  · exact (Finset.card_le_card Finset.inter_subset_left).trans hTcard
  intro A B hA hB hAcard hBcard
  have hArange : A ⊆ sourceLemma42Universe (2 ^ (r + 1)) := by
    intro x hx
    exact sourceLemma43DyadicBlock_subset_universe (show r ≤ r by rfl) (hA hx)
  have hBrange : B ⊆ sourceLemma42Universe (2 ^ (r + 1)) := by
    intro x hx
    exact sourceLemma43DyadicBlock_subset_universe hs (hB hx)
  have hsumD : additiveSumset A B ⊆ D := by
    simpa [D] using sourceLemma43_additiveSumset_subset_dyadicUnion hs hA hB
  have hDrange : D ⊆ sourceLemma42Universe (2 ^ (r + 1)) := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact sourceLemma43DyadicBlock_subset_universe (show r ≤ r by rfl) hx
    · exact sourceLemma43DyadicBlock_subset_ownUniverse (r + 1) hx
  obtain ⟨x, hx⟩ :=
    hThit A B hArange hBrange hAcard hBcard (hsumD.trans hDrange)
  obtain ⟨hxT, hxsum⟩ := Finset.mem_inter.mp hx
  exact ⟨x, Finset.mem_inter.mpr ⟨Finset.mem_inter.mpr ⟨hxT, hsumD hxsum⟩, hxsum⟩⟩


/-- The exact source parameter `k_j` from Lemma 4.3 after specializing its
constants to the final proof: `eta = 1/24` and `c = 1/32`. The manuscript
uses the natural floor of `c * j⁻¹ * 2^(eta * (j - 1)) - j⁻¹`; in particular,
the literal `k_j = 0` branch is meaningful at small scales. -/
noncomputable def sourceLemma43BlockThreshold (j : ℕ) : ℕ :=
  ⌊((1 : ℝ) / 32) * ((j : ℝ)⁻¹) *
    ((2 : ℝ) ^ (((j - 1 : ℕ) : ℝ) / 24)) - ((j : ℝ)⁻¹)⌋₊

/-- The exact real expression defining the source threshold diverges along
the natural dyadic scale index. -/
lemma sourceLemma43BlockThreshold_real_tendsto :
    Filter.Tendsto (fun j : ℕ => ((1 : ℝ) / 32) * ((j : ℝ)⁻¹) *
      ((2 : ℝ) ^ (((j - 1 : ℕ) : ℝ) / 24)) - ((j : ℝ)⁻¹)) Filter.atTop Filter.atTop := by
  have hb : 0 < Real.log 2 / 24 := by positivity
  have hbase := tendsto_exp_mul_div_rpow_atTop (1 : ℝ) (Real.log 2 / 24) hb
  have hnat := hbase.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hc : 0 < ((1 : ℝ) / 32) * Real.exp (-(Real.log 2 / 24)) := by positivity
  have hlead : Filter.Tendsto
      (fun j : ℕ => ((1 : ℝ) / 32) * Real.exp (-(Real.log 2 / 24)) *
        (Real.exp ((Real.log 2 / 24) * (j : ℝ)) / (j : ℝ) ^ (1 : ℝ)))
      Filter.atTop Filter.atTop := hnat.const_mul_atTop hc
  refine Filter.tendsto_atTop.2 fun R => ?_
  obtain ⟨J, hJ⟩ := Filter.eventually_atTop.mp ((Filter.tendsto_atTop.1 hlead) (R + 1))
  apply Filter.eventually_atTop.mpr
  refine ⟨max J 1, fun j hj => ?_⟩
  have hj1 : 1 ≤ j := le_trans (le_max_right _ _) hj
  have hleadJ : R + 1 ≤ ((1 : ℝ) / 32) * Real.exp (-(Real.log 2 / 24)) *
        (Real.exp ((Real.log 2 / 24) * (j : ℝ)) / (j : ℝ) ^ (1 : ℝ)) :=
    hJ j (le_trans (le_max_left _ _) hj)
  have hinv : (j : ℝ)⁻¹ ≤ 1 := by
    apply inv_le_one_of_one_le₀
    exact_mod_cast hj1
  have hrew : ((1 : ℝ) / 32) * ((j : ℝ)⁻¹) *
      ((2 : ℝ) ^ (((j - 1 : ℕ) : ℝ) / 24)) - ((j : ℝ)⁻¹) =
      ((1 : ℝ) / 32) * Real.exp (-(Real.log 2 / 24)) *
        (Real.exp ((Real.log 2 / 24) * (j : ℝ)) / (j : ℝ) ^ (1 : ℝ)) - ((j : ℝ)⁻¹) := by
    have hj : (0 : ℝ) < (j : ℝ) := by exact_mod_cast (show 0 < j by omega)
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    rw [Nat.cast_sub (show 1 ≤ j by omega)]
    norm_num only [Nat.cast_one]
    have hexp : Real.exp (Real.log 2 * (((j : ℝ) - 1) / 24)) =
        Real.exp (-(Real.log 2 / 24)) * Real.exp ((Real.log 2 / 24) * (j : ℝ)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hexp]
    field_simp
  rw [hrew]
  linarith

/-- The lower source threshold is eventually at least the repaired Lemma 4.2
minimum selected size. -/
lemma sourceLemma43BlockThreshold_eventually_lower :
    ∃ J : ℕ, ∀ j ≥ J, 2 ^ 24 ≤ sourceLemma43BlockThreshold j := by
  have hfloor : Filter.Tendsto sourceLemma43BlockThreshold Filter.atTop Filter.atTop := by
    refine Filter.Tendsto.congr
      (f₁ := fun j : ℕ => ⌊((1 : ℝ) / 32) * ((j : ℝ)⁻¹) *
        ((2 : ℝ) ^ (((j - 1 : ℕ) : ℝ) / 24)) - ((j : ℝ)⁻¹)⌋₊) ?_
      (tendsto_nat_floor_atTop.comp sourceLemma43BlockThreshold_real_tendsto)
    intro j
    unfold sourceLemma43BlockThreshold
    congr 1
  exact Filter.eventually_atTop.mp
    ((Filter.tendsto_atTop.mp hfloor) (2 ^ 24))

/-- The source threshold is always within the ambient dyadic universe at its
scale; this supplies the upper repaired-Lemma-4.2 hypothesis. -/
lemma sourceLemma43BlockThreshold_le_universe (j : ℕ) :
    sourceLemma43BlockThreshold j ≤ 2 ^ (j + 1) := by
  unfold sourceLemma43BlockThreshold
  apply Nat.floor_le_of_le
  by_cases hz : j = 0
  · subst j
    norm_num
  have hj : 1 ≤ (j : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hz
  have hinv : (j : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hj
  have hinv0 : 0 ≤ (j : ℝ)⁻¹ := inv_nonneg.mpr (by positivity)
  have hcoef : ((1 : ℝ) / 32) * ((j : ℝ)⁻¹) ≤ 1 := by nlinarith
  have hpow0 : 0 ≤ (2 : ℝ) ^ (((j - 1 : ℕ) : ℝ) / 24) :=
    Real.rpow_nonneg (by norm_num) _
  have hm : ((1 : ℝ) / 32) * ((j : ℝ)⁻¹) *
      ((2 : ℝ) ^ (((j - 1 : ℕ) : ℝ) / 24)) - ((j : ℝ)⁻¹) ≤
      (2 : ℝ) ^ (((j - 1 : ℕ) : ℝ) / 24) := by nlinarith
  have he : (((j - 1 : ℕ) : ℝ) / 24) ≤ ((j + 1 : ℕ) : ℝ) := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 24)).mpr
    exact_mod_cast (show j - 1 ≤ (j + 1) * 24 by omega)
  have hR := Real.rpow_le_rpow_of_exponent_le (x := (2 : ℝ)) (by norm_num) he
  calc
    _ ≤ 2 ^ ((j + 1 : ℕ) : ℝ) := hm.trans hR
    _ = (2 ^ (j + 1) : ℕ) := by
      rw [Real.rpow_natCast]
      norm_cast

/-- Beyond one explicit finite cutoff, both hypotheses of the repaired Lemma
4.2 call hold for the exact source threshold. -/
theorem sourceLemma43BlockThreshold_eventually_admissible :
    ∃ J : ℕ, ∀ j ≥ J,
      2 ^ 24 ≤ sourceLemma43BlockThreshold j ∧
        sourceLemma43BlockThreshold j ≤ 2 ^ (j + 1) := by
  obtain ⟨J, hJ⟩ := sourceLemma43BlockThreshold_eventually_lower
  exact ⟨J, fun j hj => ⟨hJ j hj, sourceLemma43BlockThreshold_le_universe j⟩⟩

/-- A fixed cutoff selected from the proved eventual source threshold regime. -/
noncomputable def sourceLemma43ThresholdCutoff : ℕ :=
  Classical.choose sourceLemma43BlockThreshold_eventually_admissible

lemma sourceLemma43_threshold_admissible_of_cutoff_le {j : ℕ}
    (hj : sourceLemma43ThresholdCutoff ≤ j) :
    2 ^ 24 ≤ sourceLemma43BlockThreshold j ∧
      sourceLemma43BlockThreshold j ≤ 2 ^ (j + 1) := by
  exact Classical.choose_spec sourceLemma43BlockThreshold_eventually_admissible j hj

/-- The exceptional scales are a literal finite set: those below the selected
cutoff for which the repaired Lemma 4.2 assumptions do not hold. -/
noncomputable def sourceLemma43ExceptionalScales : Finset ℕ :=
  (Finset.range sourceLemma43ThresholdCutoff).filter fun j =>
    ¬ (2 ^ 24 ≤ sourceLemma43BlockThreshold j ∧
      sourceLemma43BlockThreshold j ≤ 2 ^ (j + 1))

lemma sourceLemma43_not_admissible_mem_exceptionalScales {j : ℕ}
    (h : ¬ (2 ^ 24 ≤ sourceLemma43BlockThreshold j ∧
      sourceLemma43BlockThreshold j ≤ 2 ^ (j + 1))) :
    j ∈ sourceLemma43ExceptionalScales := by
  apply Finset.mem_filter.mpr
  constructor
  · rw [Finset.mem_range]
    by_contra hnot
    exact h (sourceLemma43_threshold_admissible_of_cutoff_le
      (Nat.le_of_not_gt hnot))
  · exact h

lemma sourceLemma43ExceptionalScales_card_le :
    sourceLemma43ExceptionalScales.card ≤ sourceLemma43ThresholdCutoff := by
  unfold sourceLemma43ExceptionalScales
  simpa using Finset.card_filter_le (Finset.range sourceLemma43ThresholdCutoff)
    (fun j => ¬ (2 ^ 24 ≤ sourceLemma43BlockThreshold j ∧
      sourceLemma43BlockThreshold j ≤ 2 ^ (j + 1)))

/-- The two adjacent blocks retained by the source at dyadic scale `j`. -/
def sourceLemma43AdjacentBlocks (j : ℕ) : Finset ℕ :=
  sourceLemma43DyadicBlock j ∪ sourceLemma43DyadicBlock (j + 1)

/-- At scales where the repaired Lemma 4.2 applies, choose its finite hitting
set and retain only the two source dyadic blocks. At explicitly separated
exceptional scales retain those two finite blocks themselves. -/
noncomputable def sourceLemma43LocalSet (j : ℕ) : Finset ℕ := by
  classical
  let k := sourceLemma43BlockThreshold j
  let D := sourceLemma43AdjacentBlocks j
  by_cases h : 2 ^ 24 ≤ k ∧ k ≤ 2 ^ (j + 1)
  · exact (Classical.choose (sourceLemma42_rangeContained_repaired h.1 h.2)) ∩ D
  · exact D

/-- The finite support contributed by all exceptional source scales. Its
cardinality is a fixed natural constant available to the later initial-
segment estimate. -/
noncomputable def sourceLemma43ExceptionalSupport : Finset ℕ :=
  sourceLemma43ExceptionalScales.biUnion sourceLemma43LocalSet

lemma sourceLemma43_mem_exceptionalSupport {j x : ℕ}
    (hj : j ∈ sourceLemma43ExceptionalScales)
    (hx : x ∈ sourceLemma43LocalSet j) :
    x ∈ sourceLemma43ExceptionalSupport := by
  exact Finset.mem_biUnion.mpr ⟨j, hj, hx⟩

lemma sourceLemma43ExceptionalSupport_card_le :
    sourceLemma43ExceptionalSupport.card ≤
      ∑ j ∈ sourceLemma43ExceptionalScales, (sourceLemma43LocalSet j).card := by
  exact Finset.card_biUnion_le

/-- The global source S-prime: the infinite union of the local two-block
sets, indexed exactly by the positive dyadic scales of Lemma 4.3. -/
noncomputable def sourceLemma43Set : Set ℕ :=
  {x | ∃ j : ℕ, 1 ≤ j ∧ x ∈ sourceLemma43LocalSet j}

lemma sourceLemma43LocalSet_subset_adjacentBlocks (j : ℕ) :
    sourceLemma43LocalSet j ⊆ sourceLemma43AdjacentBlocks j := by
  classical
  unfold sourceLemma43LocalSet
  dsimp only
  split
  · exact Finset.inter_subset_right
  · exact subset_rfl

lemma sourceLemma43LocalSet_subset_global (j : ℕ) (hj : 1 ≤ j) :
    ↑(sourceLemma43LocalSet j) ⊆ sourceLemma43Set := by
  intro x hx
  exact ⟨j, hj, hx⟩

/-- Every local contribution is supported in the finite interval used for
its Lemma 4.2 call. This is the support estimate needed before summing the
local budgets in the source Lemma 4.3 sparsity argument. -/
lemma sourceLemma43LocalSet_subset_universe (j : ℕ) :
    sourceLemma43LocalSet j ⊆ sourceLemma42Universe (2 ^ (j + 1)) := by
  intro x hx
  rcases Finset.mem_union.mp
      (sourceLemma43LocalSet_subset_adjacentBlocks j hx) with hxj | hxnext
  · exact sourceLemma43DyadicBlock_subset_universe (show j ≤ j by rfl) hxj
  · exact sourceLemma43DyadicBlock_subset_ownUniverse (j + 1) hxnext

/-- A local Lemma 4.3 contribution has at most the cardinality of its
ambient interval. The stronger eventual budget bound remains a separate
quantitative source obligation. -/
lemma sourceLemma43LocalSet_card_le (j : ℕ) :
    (sourceLemma43LocalSet j).card ≤ 2 ^ (j + 1) := by
  calc
    (sourceLemma43LocalSet j).card ≤ (sourceLemma42Universe (2 ^ (j + 1))).card :=
      Finset.card_le_card (sourceLemma43LocalSet_subset_universe j)
    _ = 2 ^ (j + 1) := by simp [sourceLemma42Universe]

/-- The exceptional branch is a literal finite two-block correction, not an
informal appeal to finiteness. -/
lemma sourceLemma43LocalSet_eq_adjacentBlocks_of_exceptional {j : ℕ}
    (h : ¬ (2 ^ 24 ≤ sourceLemma43BlockThreshold j ∧
      sourceLemma43BlockThreshold j ≤ 2 ^ (j + 1))) :
    sourceLemma43LocalSet j = sourceLemma43AdjacentBlocks j := by
  classical
  unfold sourceLemma43LocalSet
  dsimp only
  split
  · rename_i hgood
    exact False.elim (h hgood)
  · rfl


/-- The source local set hits each qualifying pair of dyadic blocks. The
proof explicitly splits the repaired Lemma 4.2 large-scale branch from the
finite exceptional correction branch. -/
theorem sourceLemma43LocalSet_hits_dyadicPair {j s : ℕ}
    (hj : 1 ≤ j) (hs : s ≤ j) {A B : Finset ℕ}
    (hA : A ⊆ sourceLemma43DyadicBlock j)
    (hB : B ⊆ sourceLemma43DyadicBlock s)
    (hAcard : sourceLemma43BlockThreshold j ≤ A.card)
    (hBcard : sourceLemma43BlockThreshold j ≤ B.card)
    (hApos : A.Nonempty) (hBpos : B.Nonempty) :
    (sourceLemma43LocalSet j ∩ additiveSumset A B).Nonempty := by
  classical
  let k := sourceLemma43BlockThreshold j
  let D := sourceLemma43AdjacentBlocks j
  have hsumD : additiveSumset A B ⊆ D := by
    simpa [D, sourceLemma43AdjacentBlocks] using
      sourceLemma43_additiveSumset_subset_dyadicUnion hs hA hB
  by_cases hlarge : 2 ^ 24 ≤ k ∧ k ≤ 2 ^ (j + 1)
  · let T := Classical.choose (sourceLemma42_rangeContained_repaired hlarge.1 hlarge.2)
    have hT := Classical.choose_spec (sourceLemma42_rangeContained_repaired hlarge.1 hlarge.2)
    have hArange : A ⊆ sourceLemma42Universe (2 ^ (j + 1)) := by
      intro x hx
      exact sourceLemma43DyadicBlock_subset_universe (show j ≤ j by rfl) (hA hx)
    have hBrange : B ⊆ sourceLemma42Universe (2 ^ (j + 1)) := by
      intro x hx
      exact sourceLemma43DyadicBlock_subset_universe hs (hB hx)
    have hDrange : D ⊆ sourceLemma42Universe (2 ^ (j + 1)) := by
      intro x hx
      rcases Finset.mem_union.mp hx with hx | hx
      · exact sourceLemma43DyadicBlock_subset_universe (show j ≤ j by rfl) hx
      · exact sourceLemma43DyadicBlock_subset_ownUniverse (j + 1) hx
    obtain ⟨x, hx⟩ := hT.2.2 A B hArange hBrange hAcard hBcard (hsumD.trans hDrange)
    obtain ⟨hxT, hxsum⟩ := Finset.mem_inter.mp hx
    have hlocal : sourceLemma43LocalSet j = T ∩ D := by
      unfold sourceLemma43LocalSet
      dsimp only
      split
      · rfl
      · rename_i hnot
        exact False.elim (hnot hlarge)
    rw [hlocal]
    exact ⟨x, Finset.mem_inter.mpr
      ⟨Finset.mem_inter.mpr ⟨hxT, hsumD hxsum⟩, hxsum⟩⟩
  · have hlocal : sourceLemma43LocalSet j = D := by
      unfold sourceLemma43LocalSet
      dsimp only
      split
      · rename_i hgood
        exact False.elim (hlarge hgood)
      · rfl
    obtain ⟨a, ha⟩ := hApos
    obtain ⟨b, hb⟩ := hBpos
    have hab : a + b ∈ additiveSumset A B :=
      Finset.mem_image₂.mpr ⟨a, ha, b, hb, rfl⟩
    rw [hlocal]
    exact ⟨a + b, Finset.mem_inter.mpr ⟨hsumD hab, hab⟩⟩

/-- The dyadic local hit is a global hit in the actual infinite source set. -/
theorem sourceLemma43Set_hits_of_dyadicPair {j s : ℕ}
    (hj : 1 ≤ j) (hs : s ≤ j) {A B : Finset ℕ}
    (hA : A ⊆ sourceLemma43DyadicBlock j)
    (hB : B ⊆ sourceLemma43DyadicBlock s)
    (hAcard : sourceLemma43BlockThreshold j ≤ A.card)
    (hBcard : sourceLemma43BlockThreshold j ≤ B.card)
    (hApos : A.Nonempty) (hBpos : B.Nonempty) :
    ∃ x, x ∈ sourceLemma43Set ∧ x ∈ additiveSumset A B := by
  obtain ⟨x, hx⟩ :=
    sourceLemma43LocalSet_hits_dyadicPair hj hs hA hB hAcard hBcard hApos hBpos
  obtain ⟨hxlocal, hxsum⟩ := Finset.mem_inter.mp hx
  exact ⟨x, sourceLemma43LocalSet_subset_global j hj hxlocal, hxsum⟩


lemma sourceLemma43BlockThreshold_eq_zero_of_le_64 {j : ℕ} (hj : 1 ≤ j) (h64 : j ≤ 64) :
  sourceLemma43BlockThreshold j = 0 := by
  unfold sourceLemma43BlockThreshold
  rw [Nat.floor_eq_zero]
  have hsub : j - 1 ≤ 63 := by omega
  have he : (((j - 1 : ℕ) : ℝ) / 24) ≤ (63 : ℝ) / 24 := by
    gcongr
    exact_mod_cast hsub
  have hp : (2 : ℝ) ^ (((j - 1 : ℕ) : ℝ) / 24) ≤ (2 : ℝ) ^ ((63 : ℝ) / 24) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) he
  have hp63 : (2 : ℝ) ^ ((63 : ℝ) / 24) < 32 := by
    calc
      (2 : ℝ) ^ ((63 : ℝ) / 24) < (2 : ℝ) ^ (5 : ℝ) :=
        Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by norm_num)
      _ = 32 := by norm_num [Real.rpow_natCast]
  have hinv : 0 ≤ (j : ℝ)⁻¹ := inv_nonneg.mpr (by positivity)
  have hp' : (2 : ℝ) ^ (((j - 1 : ℕ) : ℝ) / 24) < 32 := lt_of_le_of_lt hp hp63
  have hcoeff : ((1 : ℝ) / 32) * ((j : ℝ)⁻¹) *
      ((2 : ℝ) ^ (((j - 1 : ℕ) : ℝ) / 24)) < 1 := by
    have hjinv : (j : ℝ)⁻¹ ≤ 1 := by
      apply inv_le_one_of_one_le₀
      exact_mod_cast hj
    calc
      ((1 : ℝ) / 32) * ((j : ℝ)⁻¹) *
          ((2 : ℝ) ^ (((j - 1 : ℕ) : ℝ) / 24)) ≤
        ((1 : ℝ) / 32) * 1 * ((2 : ℝ) ^ (((j - 1 : ℕ) : ℝ) / 24)) := by gcongr
      _ < ((1 : ℝ) / 32) * 1 * 32 := by gcongr
      _ = 1 := by norm_num
  linarith


lemma sourceLemma43BlockThreshold_real_adjacent_le_of_64_le {j : ℕ} (hj : 64 ≤ j) :
  ((1 : ℝ) / 32) * ((j : ℝ)⁻¹) * ((2 : ℝ) ^ (((j - 1 : ℕ) : ℝ) / 24)) - ((j : ℝ)⁻¹) ≤
  ((1 : ℝ) / 32) * (((j + 1 : ℕ) : ℝ)⁻¹) * ((2 : ℝ) ^ ((((j + 1 : ℕ) - 1 : ℕ) : ℝ) / 24)) - (((j + 1 : ℕ) : ℝ)⁻¹) := by
  have hq : (65 : ℝ) / 64 ≤ (2 : ℝ) ^ ((1 : ℝ) / 24) := by
    apply (Real.rpow_le_rpow_iff (by positivity) (by positivity) (by norm_num : (0 : ℝ) < 24)).mp
    have h : ((65 : ℝ) / 64) ^ (24 : ℕ) ≤ 2 := by norm_num
    rw [← Real.rpow_natCast] at h
    convert h using 1
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hq' : (1 : ℝ) / 64 ≤ (2 : ℝ) ^ ((1 : ℝ) / 24) - 1 := by linarith
  have hjR : (64 : ℝ) ≤ j := by exact_mod_cast hj
  have hprod : 1 ≤ (j : ℝ) * ((2 : ℝ) ^ ((1 : ℝ) / 24) - 1) := by nlinarith
  have hscale : (2 : ℝ) ^ ((((j + 1 : ℕ) - 1 : ℕ) : ℝ) / 24) =
      (2 : ℝ) ^ ((1 : ℝ) / 24) * (2 : ℝ) ^ (((j - 1 : ℕ) : ℝ) / 24) := by
    rw [show j + 1 - 1 = j by omega]
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1
    have : ((j - 1 : ℕ) : ℝ) = (j : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]
      norm_num
    rw [this]
    ring
  rw [hscale]
  have hJ : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
  have hJs : (0 : ℝ) < (j + 1 : ℕ) := by positivity
  have ha : 0 ≤ ((1 : ℝ) / 32) * (2 : ℝ) ^ (((j - 1 : ℕ) : ℝ) / 24) := by positivity
  have hleft : ((1 : ℝ) / 32) * ((j : ℝ)⁻¹) *
      ((2 : ℝ) ^ (((j - 1 : ℕ) : ℝ) / 24)) - ((j : ℝ)⁻¹) =
      ((((1 : ℝ) / 32) * ((2 : ℝ) ^ (((j - 1 : ℕ) : ℝ) / 24)) - 1) / (j : ℝ)) := by
    field_simp
    ring
  have hright : ((1 : ℝ) / 32) * (((j + 1 : ℕ) : ℝ)⁻¹) *
      ((2 : ℝ) ^ ((1 : ℝ) / 24) * (2 : ℝ) ^ (((j - 1 : ℕ) : ℝ) / 24)) -
        (((j + 1 : ℕ) : ℝ)⁻¹) =
      ((((1 : ℝ) / 32) * ((2 : ℝ) ^ ((1 : ℝ) / 24) *
        (2 : ℝ) ^ (((j - 1 : ℕ) : ℝ) / 24)) - 1) / ((j + 1 : ℕ) : ℝ)) := by
    field_simp
    ring
  rw [hleft, hright]
  apply (div_le_div_iff₀ hJ hJs).mpr
  have hinter : 0 ≤ (j : ℝ) * ((2 : ℝ) ^ ((1 : ℝ) / 24) - 1) - 1 := by linarith
  have hnon : 0 ≤ (((1 : ℝ) / 32) * (2 : ℝ) ^ (((j - 1 : ℕ) : ℝ) / 24)) *
      ((j : ℝ) * ((2 : ℝ) ^ ((1 : ℝ) / 24) - 1) - 1) := mul_nonneg ha hinter
  calc
    (((1 : ℝ) / 32) * (2 : ℝ) ^ (((j - 1 : ℕ) : ℝ) / 24) - 1) * (j + 1 : ℕ) ≤
        (((1 : ℝ) / 32) * (2 : ℝ) ^ (((j - 1 : ℕ) : ℝ) / 24) - 1) * (j + 1 : ℕ) +
          (((1 : ℝ) / 32) * (2 : ℝ) ^ (((j - 1 : ℕ) : ℝ) / 24)) *
            ((j : ℝ) * ((2 : ℝ) ^ ((1 : ℝ) / 24) - 1) - 1) + 1 := by linarith
    _ = (((1 : ℝ) / 32) * ((2 : ℝ) ^ ((1 : ℝ) / 24) *
      (2 : ℝ) ^ (((j - 1 : ℕ) : ℝ) / 24)) - 1) * (j : ℝ) := by
      push_cast
      ring

/-- The exact specialized floor threshold from source Lemma 4.3 is
nondecreasing on positive dyadic indices. -/
theorem sourceLemma43BlockThreshold_mono {r j : ℕ}
    (hr : 1 ≤ r) (hrj : r ≤ j) :
    sourceLemma43BlockThreshold r ≤ sourceLemma43BlockThreshold j := by
  by_cases hsmall : r ≤ 64
  · rw [sourceLemma43BlockThreshold_eq_zero_of_le_64 hr hsmall]
    exact Nat.zero_le _
  have hr64 : 64 ≤ r := by omega
  induction j, hrj using Nat.le_induction with
  | base => exact le_rfl
  | succ j hj ih =>
      exact ih.trans (Nat.floor_le_floor
        (sourceLemma43BlockThreshold_real_adjacent_le_of_64_le (by omega)))


lemma sourceLemma43_mem_dyadicBlock_le_of_mem_universe {n j x : ℕ} (hj : 1 ≤ j)
    (hnj : n ∈ sourceLemma43DyadicBlock j)
    (hx : x ∈ sourceLemma42Universe n) :
    ∃ r ∈ Finset.Icc 1 j, x ∈ sourceLemma43DyadicBlock r := by
  have hxpos : 0 < x := by
    simpa [sourceLemma42Universe] using (Finset.mem_Icc.mp hx).1
  obtain ⟨r, hr1, hxr⟩ := sourceLemma43_exists_mem_dyadicBlock hxpos
  refine ⟨r, Finset.mem_Icc.mpr ⟨hr1, ?_⟩, hxr⟩
  have hlow : 2 ^ (r - 1) ≤ x := (Finset.mem_Icc.mp hxr).1
  have hxle : x ≤ n := (Finset.mem_Icc.mp hx).2
  have hnle : n ≤ 2 ^ j - 1 := (Finset.mem_Icc.mp hnj).2
  by_contra hnot
  have hjr : j + 1 ≤ r := by omega
  have hp : 2 ^ j ≤ 2 ^ (r - 1) := by
    apply Nat.pow_le_pow_right (by omega)
    omega
  have hpowx : 2 ^ j ≤ x := hp.trans hlow
  omega


theorem sourceLemma43_exists_large_dyadicFiber {n j : ℕ} {A : Finset ℕ}
    (hj : 1 ≤ j) (hnj : n ∈ sourceLemma43DyadicBlock j)
    (hA : A ⊆ sourceLemma42Universe n)
    (hcard : j * sourceLemma43BlockThreshold j ≤ A.card) :
    ∃ r : ℕ, 1 ≤ r ∧ r ≤ j ∧ sourceLemma43BlockThreshold j ≤
      (A ∩ sourceLemma43DyadicBlock r).card := by
  let k := sourceLemma43BlockThreshold j
  let R := Finset.Icc 1 j
  let f : ℕ → Finset ℕ := fun r => A ∩ sourceLemma43DyadicBlock r
  by_cases hk : k = 0
  · refine ⟨1, by omega, hj, ?_⟩
    simp [k, hk]
  have hkpos : 0 < k := Nat.pos_of_ne_zero hk
  by_contra h
  push_neg at h
  have hf : ∀ r ∈ R, (f r).card ≤ k - 1 := by
    intro r hr
    have hr' : 1 ≤ r ∧ r ≤ j := by simpa [R] using hr
    have hlt : (f r).card < k := by
      apply h r hr'.1 hr'.2
    omega
  have hcover : A ⊆ R.biUnion f := by
    intro x hx
    obtain ⟨r, hr, hxr⟩ := sourceLemma43_mem_dyadicBlock_le_of_mem_universe hj hnj (hA hx)
    exact Finset.mem_biUnion.mpr ⟨r, by simpa [R] using hr,
      Finset.mem_inter.mpr ⟨hx, hxr⟩⟩
  have hcardle : A.card ≤ R.card * (k - 1) :=
    (Finset.card_le_card hcover).trans (Finset.card_biUnion_le_card_mul R f (k - 1) hf)
  have hR : R.card = j := by simp [R, Nat.card_Icc, hj]
  have hless : j * (k - 1) < j * k := by
    apply Nat.mul_lt_mul_of_pos_left
    · omega
    · omega
  rw [hR] at hcardle
  have hstrict : A.card < j * k := hcardle.trans_lt hless
  change j * k ≤ A.card at hcard
  exact (not_lt_of_ge hcard) hstrict
end JSP000089


namespace JSP000089

lemma sourceLemma43_exists_occupied_dyadicFiber {n j : ℕ} {A : Finset ℕ}
    (hj : 1 ≤ j) (hnj : n ∈ sourceLemma43DyadicBlock j)
    (hA : A ⊆ sourceLemma42Universe n) (hApos : A.Nonempty) :
    ∃ r : ℕ, 1 ≤ r ∧ r ≤ j ∧ (A ∩ sourceLemma43DyadicBlock r).Nonempty := by
  obtain ⟨x, hx⟩ := hApos
  obtain ⟨r, hr, hxr⟩ := sourceLemma43_mem_dyadicBlock_le_of_mem_universe hj hnj (hA hx)
  have hr' : 1 ≤ r ∧ r ≤ j := by simpa using hr
  exact ⟨r, hr'.1, hr'.2, ⟨x, Finset.mem_inter.mpr ⟨hx, hxr⟩⟩⟩
end JSP000089


namespace JSP000089

lemma sourceLemma43_additiveSumset_comm (A B : Finset ℕ) :
    additiveSumset A B = additiveSumset B A := by
  ext x
  constructor <;> intro hx
  · obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_image₂.mp hx
    exact Finset.mem_image₂.mpr ⟨b, hb, a, ha, Nat.add_comm b a⟩
  · obtain ⟨b, hb, a, ha, rfl⟩ := Finset.mem_image₂.mp hx
    exact Finset.mem_image₂.mpr ⟨a, ha, b, hb, Nat.add_comm a b⟩

theorem sourceLemma43_exists_two_dyadicFibers {n j : ℕ} {A B : Finset ℕ}
    (hj : 1 ≤ j) (hnj : n ∈ sourceLemma43DyadicBlock j)
    (hA : A ⊆ sourceLemma42Universe n) (hB : B ⊆ sourceLemma42Universe n)
    (hAc : j * sourceLemma43BlockThreshold j ≤ A.card)
    (hBc : j * sourceLemma43BlockThreshold j ≤ B.card)
    (hAp : A.Nonempty) (hBp : B.Nonempty) :
    ∃ r s, 1 ≤ r ∧ r ≤ j ∧ 1 ≤ s ∧ s ≤ j ∧
      sourceLemma43BlockThreshold j ≤ (A ∩ sourceLemma43DyadicBlock r).card ∧
      sourceLemma43BlockThreshold j ≤ (B ∩ sourceLemma43DyadicBlock s).card ∧
      (A ∩ sourceLemma43DyadicBlock r).Nonempty ∧
      (B ∩ sourceLemma43DyadicBlock s).Nonempty := by
  let k := sourceLemma43BlockThreshold j
  by_cases hk : k = 0
  · obtain ⟨r, hr1, hrj, hrp⟩ := sourceLemma43_exists_occupied_dyadicFiber hj hnj hA hAp
    obtain ⟨s, hs1, hsj, hsp⟩ := sourceLemma43_exists_occupied_dyadicFiber hj hnj hB hBp
    refine ⟨r,s,hr1,hrj,hs1,hsj,?_,?_,hrp,hsp⟩ <;> simp [k,hk]
  · obtain ⟨r, hr1, hrj, hrc⟩ := sourceLemma43_exists_large_dyadicFiber hj hnj hA hAc
    obtain ⟨s, hs1, hsj, hsc⟩ := sourceLemma43_exists_large_dyadicFiber hj hnj hB hBc
    have hkpos : 0 < k := Nat.pos_of_ne_zero hk
    refine ⟨r,s,hr1,hrj,hs1,hsj,hrc,hsc,?_,?_⟩
    · exact Finset.card_pos.mp (lt_of_lt_of_le (by simpa [k] using hkpos) hrc)
    · exact Finset.card_pos.mp (lt_of_lt_of_le (by simpa [k] using hkpos) hsc)

theorem sourceLemma43_global_hitting {n j : ℕ} {A B : Finset ℕ}
    (hj : 1 ≤ j) (hnj : n ∈ sourceLemma43DyadicBlock j)
    (hA : A ⊆ sourceLemma42Universe n) (hB : B ⊆ sourceLemma42Universe n)
    (hAc : j * sourceLemma43BlockThreshold j ≤ A.card)
    (hBc : j * sourceLemma43BlockThreshold j ≤ B.card)
    (hAp : A.Nonempty) (hBp : B.Nonempty) :
    ∃ x, x ∈ sourceLemma43Set ∧ x ∈ additiveSumset A B := by
  obtain ⟨r,s,hr1,hrj,hs1,hsj,hrc,hsc,hrp,hsp⟩ := sourceLemma43_exists_two_dyadicFibers hj hnj hA hB hAc hBc hAp hBp
  by_cases hsr : s ≤ r
  · have hkr : sourceLemma43BlockThreshold r ≤ sourceLemma43BlockThreshold j :=
      sourceLemma43BlockThreshold_mono hr1 hrj
    obtain ⟨x,hxS,hx⟩ := sourceLemma43Set_hits_of_dyadicPair hr1 hsr
      Finset.inter_subset_right Finset.inter_subset_right
      (hkr.trans hrc) (hkr.trans hsc) hrp hsp
    exact ⟨x,hxS, additiveSumset_subset_additiveSumset Finset.inter_subset_left Finset.inter_subset_left hx⟩
  · have hrs : r ≤ s := by omega
    have hks : sourceLemma43BlockThreshold s ≤ sourceLemma43BlockThreshold j :=
      sourceLemma43BlockThreshold_mono hs1 hsj
    obtain ⟨x,hxS,hx⟩ := sourceLemma43Set_hits_of_dyadicPair hs1 hrs
      Finset.inter_subset_right Finset.inter_subset_right
      (hks.trans hsc) (hks.trans hrc) hsp hrp
    have hx' : x ∈ additiveSumset (B ∩ sourceLemma43DyadicBlock s) (A ∩ sourceLemma43DyadicBlock r) := hx
    rw [sourceLemma43_additiveSumset_comm] at hx'
    exact ⟨x,hxS, additiveSumset_subset_additiveSumset Finset.inter_subset_left Finset.inter_subset_left hx'⟩


end JSP000089


namespace JSP000089

lemma sourceLemma43LocalSet_card_le_finalBudget_of_admissible {j : ℕ}
    (h : 2 ^ 24 ≤ sourceLemma43BlockThreshold j ∧
      sourceLemma43BlockThreshold j ≤ 2 ^ (j + 1)) :
    (sourceLemma43LocalSet j).card ≤
      sourceLemma42FinalBudget (2 ^ (j + 1)) (sourceLemma43BlockThreshold j) := by
  classical
  let k := sourceLemma43BlockThreshold j
  let D := sourceLemma43AdjacentBlocks j
  let T := Classical.choose (sourceLemma42_rangeContained_repaired h.1 h.2)
  have hT := Classical.choose_spec (sourceLemma42_rangeContained_repaired h.1 h.2)
  have hlocal : sourceLemma43LocalSet j = T ∩ D := by
    unfold sourceLemma43LocalSet
    dsimp only
    split
    · rfl
    · rename_i hnot
      exact False.elim (hnot h)
  have hTcard : T.card ≤
      sourceLemma42FinalBudget (2 ^ (j + 1)) (sourceLemma43BlockThreshold j) := by
    simpa [T] using hT.2.1
  rw [hlocal]
  exact (Finset.card_le_card Finset.inter_subset_left).trans hTcard

end JSP000089


namespace JSP000089

noncomputable def sourceLemma43ExceptionalContribution : ℕ :=
  ∑ j ∈ sourceLemma43ExceptionalScales, (sourceLemma43LocalSet j).card
lemma sourceLemma43ExceptionalContribution_bound : sourceLemma43ExceptionalSupport.card ≤ sourceLemma43ExceptionalContribution := by
  exact sourceLemma43ExceptionalSupport_card_le

end JSP000089


namespace JSP000089

lemma sourceLemma43_regular_selectedSize_mul_card_le {j : ℕ}
    (h : 2 ^ 24 ≤ sourceLemma43BlockThreshold j ∧
      sourceLemma43BlockThreshold j ≤ 2 ^ (j + 1)) :
    sourceLemma41SelectedSize (sourceLemma43BlockThreshold j) *
      (sourceLemma43LocalSet j).card ≤
      68 * 2 ^ (j + 1) * sourceLemma42LogScale (2 ^ (j + 1)) := by
  have hlocal := sourceLemma43LocalSet_card_le_finalBudget_of_admissible h
  calc
    sourceLemma41SelectedSize (sourceLemma43BlockThreshold j) *
        (sourceLemma43LocalSet j).card ≤
      sourceLemma41SelectedSize (sourceLemma43BlockThreshold j) *
        sourceLemma42FinalBudget (2 ^ (j + 1)) (sourceLemma43BlockThreshold j) :=
      Nat.mul_le_mul_left _ hlocal
    _ ≤ 68 * 2 ^ (j + 1) * sourceLemma42LogScale (2 ^ (j + 1)) :=
      sourceLemma42_finalBudget_quantitative_bound h.1 h.2

end JSP000089


namespace JSP000089

lemma sourceLemma43_regular_quartic_local_estimate {j : ℕ}
    (h : 2 ^ 24 ≤ sourceLemma43BlockThreshold j ∧
      sourceLemma43BlockThreshold j ≤ 2 ^ (j + 1)) :
    sourceLemma43BlockThreshold j * (sourceLemma43LocalSet j).card ^ 4 ≤
      16 * (68 * 2 ^ (j + 1) * sourceLemma42LogScale (2 ^ (j + 1))) ^ 4 := by
  let k := sourceLemma43BlockThreshold j
  let m := sourceLemma41SelectedSize k
  let L := (sourceLemma43LocalSet j).card
  let B := 68 * 2 ^ (j + 1) * sourceLemma42LogScale (2 ^ (j + 1))
  have hk : k ≤ 16 * m ^ 4 := by
    simpa [k] using (sourceLemma41_selectedSize_quantitative_bounds h.1).1
  have hml : m * L ≤ B := by
    simpa [k, m, L, B] using sourceLemma43_regular_selectedSize_mul_card_le h
  calc
    k * L ^ 4 ≤ (16 * m ^ 4) * L ^ 4 := Nat.mul_le_mul_right _ hk
    _ = 16 * (m * L) ^ 4 := by ring
    _ ≤ 16 * B ^ 4 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hml 4)
end JSP000089



namespace JSP000089

lemma sourceLemma43_threshold_exponential_le {j : ℕ} (hj : 1 ≤ j)
    (hk : 2 ^ 24 ≤ sourceLemma43BlockThreshold j) :
    (2 : ℝ) ^ (((j - 1 : ℕ) : ℝ) / 24) ≤
      128 * (j : ℝ) * (sourceLemma43BlockThreshold j : ℝ) := by
  let x : ℝ := ((1 : ℝ) / 32) * ((j : ℝ)⁻¹) *
    ((2 : ℝ) ^ (((j - 1 : ℕ) : ℝ) / 24)) - ((j : ℝ)⁻¹)
  let k := sourceLemma43BlockThreshold j
  have hfloor : x < (k : ℝ) + 1 := by
    simpa [x, k, sourceLemma43BlockThreshold] using Nat.lt_floor_add_one x
  have hjpos : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
  have hkpos : (1 : ℝ) ≤ k := by
    exact_mod_cast (show 1 ≤ k by omega)
  have hpow : 0 ≤ (2 : ℝ) ^ (((j - 1 : ℕ) : ℝ) / 24) := Real.rpow_nonneg (by norm_num) _
  have hkinv : 0 ≤ (j : ℝ)⁻¹ := inv_nonneg.mpr (by positivity)
  have hinv : (j : ℝ) * (j : ℝ)⁻¹ = 1 := by field_simp
  have hkbound : (k : ℝ) + 1 ≤ 2 * k := by nlinarith
  have hmain : (2 : ℝ) ^ (((j - 1 : ℕ) : ℝ) / 24) <
      32 * ((j : ℝ) * ((k : ℝ) + 1) + 1) := by
    dsimp [x] at hfloor
    have := (mul_lt_mul_of_pos_left hfloor hjpos)
    field_simp at this
    nlinarith
  have hjone : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hjk : (1 : ℝ) ≤ (j : ℝ) * k := by
    calc
      (1 : ℝ) = 1 * 1 := by ring
      _ ≤ (j : ℝ) * k := mul_le_mul hjone hkpos (by positivity) (by norm_num)
  calc
    (2 : ℝ) ^ (((j - 1 : ℕ) : ℝ) / 24) ≤
        32 * ((j : ℝ) * ((k : ℝ) + 1) + 1) := hmain.le
    _ ≤ 128 * (j : ℝ) * k := by nlinarith
end JSP000089



namespace JSP000089

lemma sourceLemma43_regular_exponential_quartic_estimate {j : ℕ} (hj : 1 ≤ j)
    (h : 2 ^ 24 ≤ sourceLemma43BlockThreshold j ∧
      sourceLemma43BlockThreshold j ≤ 2 ^ (j + 1)) :
    (2 : ℝ) ^ (((j - 1 : ℕ) : ℝ) / 24) *
      ((sourceLemma43LocalSet j).card : ℝ) ^ 4 ≤
      2048 * (j : ℝ) *
        (68 * 2 ^ (j + 1) * sourceLemma42LogScale (2 ^ (j + 1)) : ℝ) ^ 4 := by
  let k := sourceLemma43BlockThreshold j
  let L := (sourceLemma43LocalSet j).card
  let B := 68 * 2 ^ (j + 1) * sourceLemma42LogScale (2 ^ (j + 1))
  have ht := sourceLemma43_threshold_exponential_le hj h.1
  have hq : k * L ^ 4 ≤ 16 * B ^ 4 := by
    simpa [k, L, B] using sourceLemma43_regular_quartic_local_estimate h
  have hqR : (k : ℝ) * (L : ℝ) ^ 4 ≤ 16 * (B : ℝ) ^ 4 := by exact_mod_cast hq
  have hL : 0 ≤ (L : ℝ) ^ 4 := by positivity
  calc
    (2 : ℝ) ^ (((j - 1 : ℕ) : ℝ) / 24) * (L : ℝ) ^ 4 ≤
        (128 * (j : ℝ) * k) * (L : ℝ) ^ 4 := mul_le_mul_of_nonneg_right ht hL
    _ = 128 * (j : ℝ) * ((k : ℝ) * (L : ℝ) ^ 4) := by ring
    _ ≤ 128 * (j : ℝ) * (16 * (B : ℝ) ^ 4) := by gcongr
    _ = 2048 * (j : ℝ) * (B : ℝ) ^ 4 := by ring
    _ = 2048 * (j : ℝ) *
        (68 * 2 ^ (j + 1) * sourceLemma42LogScale (2 ^ (j + 1)) : ℝ) ^ 4 := by simp [B]
end JSP000089



namespace JSP000089

lemma sourceLemma43_regular_exponential_power100_estimate {j : ℕ} (hj : 1 ≤ j)
    (h : 2 ^ 24 ≤ sourceLemma43BlockThreshold j ∧
      sourceLemma43BlockThreshold j ≤ 2 ^ (j + 1)) :
    ((2 : ℝ) ^ (((j - 1 : ℕ) : ℝ) / 24)) ^ 25 *
      ((sourceLemma43LocalSet j).card : ℝ) ^ 100 ≤
      (2048 * (j : ℝ) *
        (68 * 2 ^ (j + 1) * sourceLemma42LogScale (2 ^ (j + 1)) : ℝ) ^ 4) ^ 25 := by
  let E : ℝ := (2 : ℝ) ^ (((j - 1 : ℕ) : ℝ) / 24)
  let L : ℝ := (sourceLemma43LocalSet j).card
  have hq := sourceLemma43_regular_exponential_quartic_estimate hj h
  have hp := pow_le_pow_left (by positivity : 0 ≤ E * L ^ 4) (by simpa [E, L] using hq) 25
  change E ^ 25 * L ^ 100 ≤ _
  calc
    E ^ 25 * L ^ 100 = (E * L ^ 4) ^ 25 := by ring
    _ ≤ _ := hp
end JSP000089






namespace JSP000089

lemma sourceLemma42LogScale_two_pow (j : ℕ) :
    sourceLemma42LogScale (2 ^ (j + 1)) = j + 2 := by
  simp [sourceLemma42LogScale, Nat.log2_two_pow]

end JSP000089


namespace JSP000089

lemma sourceLemma43_dyadicBudget_real (j : ℕ) :
    (68 * 2 ^ (j + 1) * sourceLemma42LogScale (2 ^ (j + 1)) : ℝ) =
      68 * (2 : ℝ) ^ (j + 1) * (j + 2) := by
  norm_num [Nat.cast_mul, Nat.cast_pow, sourceLemma42LogScale_two_pow]

end JSP000089



namespace JSP000089

lemma sourceLemma43_dyadicBudget_fourth_factor (j : ℕ) :
    (68 * 2 ^ (j + 1) * sourceLemma42LogScale (2 ^ (j + 1)) : ℝ) ^ 4 =
      68 ^ 4 * (2 : ℝ) ^ (4 * (j + 1)) * (j + 2) ^ 4 := by
  rw [sourceLemma43_dyadicBudget_real]
  rw [mul_pow]
  rw [mul_pow]
  ring

end JSP000089



namespace JSP000089

lemma sourceLemma43_power100_rhs_outer_factor (j : ℕ) :
    (2048 * (j : ℝ) *
      (68 * 2 ^ (j + 1) * sourceLemma42LogScale (2 ^ (j + 1)) : ℝ) ^ 4) ^ 25 =
    (2048 * (j : ℝ)) ^ 25 *
      (68 * 2 ^ (j + 1) * sourceLemma42LogScale (2 ^ (j + 1)) : ℝ) ^ 100 := by
  rw [mul_pow]
  rw [← pow_mul]

end JSP000089


namespace JSP000089

lemma sourceLemma43_dyadicBudget_power100_factor (j : ℕ) :
    (68 * 2 ^ (j + 1) * sourceLemma42LogScale (2 ^ (j + 1)) : ℝ) ^ 100 =
      (68 : ℝ) ^ 100 * ((2 : ℝ) ^ (j + 1)) ^ 100 * (j + 2 : ℝ) ^ 100 := by
  rw [sourceLemma43_dyadicBudget_real]
  rw [mul_pow]
  rw [mul_pow]

end JSP000089


namespace JSP000089

lemma sourceLemma43_power100_rhs_normalized (j : ℕ) :
    (2048 * (j : ℝ) *
      (68 * 2 ^ (j + 1) * sourceLemma42LogScale (2 ^ (j + 1)) : ℝ) ^ 4) ^ 25 =
    (2048 : ℝ) ^ 25 * (68 : ℝ) ^ 100 * (j : ℝ) ^ 25 *
      (j + 2 : ℝ) ^ 100 * ((2 : ℝ) ^ (j + 1)) ^ 100 := by
  rw [sourceLemma43_power100_rhs_outer_factor]
  rw [sourceLemma43_dyadicBudget_power100_factor]
  rw [mul_pow]
  ring

end JSP000089


namespace JSP000089

lemma sourceLemma43_polynomial_factor_le (j : ℕ) :
    (j : ℝ) ^ 25 * (j + 2 : ℝ) ^ 100 ≤ (j + 2 : ℝ) ^ 125 := by
  have hj : (j : ℝ) ≤ j + 2 := le_add_of_nonneg_right (by norm_num)
  have hpow : (j : ℝ) ^ 25 ≤ (j + 2 : ℝ) ^ 25 :=
    pow_le_pow_left₀ (by positivity) hj 25
  calc
    (j : ℝ) ^ 25 * (j + 2 : ℝ) ^ 100 ≤
        (j + 2 : ℝ) ^ 25 * (j + 2 : ℝ) ^ 100 :=
      mul_le_mul_of_nonneg_right hpow (by positivity)
    _ = (j + 2 : ℝ) ^ 125 := by ring

end JSP000089


namespace JSP000089

lemma sourceLemma43_polynomial_absorbed_with_slack :
    ∃ J : ℕ, ∀ j : ℕ, J ≤ j →
      (j + 2 : ℝ) ^ 125 ≤
        ((2 : ℝ) ^ ((1 : ℝ) / 48)) ^ 2 *
          ((2 : ℝ) ^ ((1 : ℝ) / 48)) ^ j := by
  let r : ℝ := (2 : ℝ) ^ ((1 : ℝ) / 48)
  have hr : 1 < r := by
    dsimp [r]
    exact Real.one_lt_rpow (by norm_num) (by norm_num)
  have hlim := tendsto_pow_const_div_const_pow_of_one_lt 125 hr
  have hev : ∀ᶠ m : ℕ in Filter.atTop, (m : ℝ) ^ 125 / r ^ m ≤ 1 :=
    hlim.eventually_le_const (by norm_num)
  rcases Filter.eventually_atTop.1 hev with ⟨J, hJ⟩
  refine ⟨J, fun j hj => ?_⟩
  have hdiv : ((j + 2 : ℕ) : ℝ) ^ 125 / r ^ (j + 2) ≤ 1 := by
    apply hJ
    omega
  have hden : 0 < r ^ (j + 2) := pow_pos (by linarith) _
  have hpow : (j + 2 : ℝ) ^ 125 ≤ r ^ (j + 2) := by
    have := (div_le_iff₀ hden).mp hdiv
    simpa using this
  calc
    (j + 2 : ℝ) ^ 125 ≤ r ^ (j + 2) := hpow
    _ = r ^ 2 * r ^ j := by simpa [Nat.add_comm] using (pow_add r 2 j)
    _ = ((2 : ℝ) ^ ((1 : ℝ) / 48)) ^ 2 *
          ((2 : ℝ) ^ ((1 : ℝ) / 48)) ^ j := by rfl

end JSP000089


namespace JSP000089

lemma sourceLemma43_slack_base_pow (j : ℕ) :
    ((2 : ℝ) ^ ((1 : ℝ) / 48)) ^ j = (2 : ℝ) ^ ((j : ℝ) / 48) := by
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  congr 1
  ring

end JSP000089


namespace JSP000089

lemma sourceLemma43_slack_exponential_comparison {j : ℕ} (hj : 1 ≤ j) :
    ((2 : ℝ) ^ ((1 : ℝ) / 48)) ^ j * ((2 : ℝ) ^ (j + 1)) ^ 100 ≤
      ((2 : ℝ) ^ (((j - 1 : ℕ) : ℝ) / 24)) ^ 25 *
        (2 : ℝ) ^ (102 : ℝ) * (2 : ℝ) ^ ((((4751 : ℕ) * j : ℕ) : ℝ) / 48) := by
  have hleft : ((2 : ℝ) ^ (j + 1)) ^ 100 =
      (2 : ℝ) ^ ((100 : ℝ) * ((j + 1 : ℕ) : ℝ)) := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  have hright : ((2 : ℝ) ^ (((j - 1 : ℕ) : ℝ) / 24)) ^ 25 =
      (2 : ℝ) ^ ((25 : ℝ) * (((j - 1 : ℕ) : ℝ) / 24)) := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  rw [sourceLemma43_slack_base_pow, hleft, hright]
  have hexp : (j : ℝ) / 48 + 100 * ((j + 1 : ℕ) : ℝ) ≤
      (25 : ℝ) * (((j - 1 : ℕ) : ℝ) / 24) + 102 +
        (((4751 : ℕ) * j : ℕ) : ℝ) / 48 := by
    norm_num [Nat.cast_sub hj, Nat.cast_mul, Nat.cast_add]
    linarith
  calc
    (2 : ℝ) ^ ((j : ℝ) / 48) *
        (2 : ℝ) ^ ((100 : ℝ) * ((j + 1 : ℕ) : ℝ)) =
        (2 : ℝ) ^ ((j : ℝ) / 48 + 100 * ((j + 1 : ℕ) : ℝ)) := by
      rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    _ ≤ (2 : ℝ) ^ ((25 : ℝ) * (((j - 1 : ℕ) : ℝ) / 24) + 102 +
        (((4751 : ℕ) * j : ℕ) : ℝ) / 48) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hexp
    _ = (2 : ℝ) ^ ((25 : ℝ) * (((j - 1 : ℕ) : ℝ) / 24)) *
        (2 : ℝ) ^ (102 : ℝ) * (2 : ℝ) ^ ((((4751 : ℕ) * j : ℕ) : ℝ) / 48) := by
      rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2)]

end JSP000089


namespace JSP000089

theorem sourceLemma43_regular_local_power100_with_slack :
    ∃ J : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ j : ℕ, J ≤ j →
      ∀ h : 2 ^ 24 ≤ sourceLemma43BlockThreshold j ∧
        sourceLemma43BlockThreshold j ≤ 2 ^ (j + 1),
        ((sourceLemma43LocalSet j).card : ℝ) ^ 100 ≤
          C * (2 : ℝ) ^ ((((4751 : ℕ) * j : ℕ) : ℝ) / 48) := by
  rcases sourceLemma43_polynomial_absorbed_with_slack with ⟨J₀, hJ₀⟩
  let A : ℝ := (2048 : ℝ) ^ 25 * (68 : ℝ) ^ 100
  let r : ℝ := (2 : ℝ) ^ ((1 : ℝ) / 48)
  let R : ℝ := (2 : ℝ) ^ (102 : ℝ)
  refine ⟨max 1 J₀, A * r ^ 2 * R, by positivity, ?_⟩
  intro j hj h
  let E : ℝ := (2 : ℝ) ^ (((j - 1 : ℕ) : ℝ) / 24)
  let L : ℝ := ((sourceLemma43LocalSet j).card : ℝ)
  let P : ℝ := ((2 : ℝ) ^ (j + 1)) ^ 100
  let T : ℝ := (2 : ℝ) ^ ((((4751 : ℕ) * j : ℕ) : ℝ) / 48)
  have hjone : 1 ≤ j := (le_max_left 1 J₀).trans hj
  have hjlarge : J₀ ≤ j := (le_max_right 1 J₀).trans hj
  have hApos : 0 < A := by
    dsimp [A]
    positivity
  have hrpos : 0 < r := by
    dsimp [r]
    positivity
  have hPnonneg : 0 ≤ P := by
    dsimp [P]
    positivity
  have hmain : E ^ 25 * L ^ 100 ≤
      A * (j : ℝ) ^ 25 * (j + 2 : ℝ) ^ 100 * P := by
    have hraw := sourceLemma43_regular_exponential_power100_estimate hjone h
    rw [sourceLemma43_power100_rhs_normalized] at hraw
    simpa [E, L, A, P] using hraw
  have hpoly : (j : ℝ) ^ 25 * (j + 2 : ℝ) ^ 100 ≤ r ^ 2 * r ^ j := by
    calc
      (j : ℝ) ^ 25 * (j + 2 : ℝ) ^ 100 ≤ (j + 2 : ℝ) ^ 125 :=
        sourceLemma43_polynomial_factor_le j
      _ ≤ r ^ 2 * r ^ j := by
        simpa [r] using hJ₀ j hjlarge
  have hmain_small : E ^ 25 * L ^ 100 ≤ A * (r ^ 2 * r ^ j) * P := by
    calc
      E ^ 25 * L ^ 100 ≤ A * (j : ℝ) ^ 25 * (j + 2 : ℝ) ^ 100 * P := hmain
      _ = A * ((j : ℝ) ^ 25 * (j + 2 : ℝ) ^ 100) * P := by ring
      _ ≤ A * (r ^ 2 * r ^ j) * P := by
        have hscaled := mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hpoly hPnonneg) hApos.le
        convert hscaled using 1 <;> ring
  have hcomparison : r ^ j * P ≤ E ^ 25 * R * T := by
    simpa [r, P, E, R, T] using sourceLemma43_slack_exponential_comparison hjone
  have hfinal : E ^ 25 * L ^ 100 ≤ E ^ 25 * (A * r ^ 2 * R * T) := by
    calc
      E ^ 25 * L ^ 100 ≤ A * (r ^ 2 * r ^ j) * P := hmain_small
      _ = (A * r ^ 2) * (r ^ j * P) := by ring
      _ ≤ (A * r ^ 2) * (E ^ 25 * R * T) :=
        mul_le_mul_of_nonneg_left hcomparison (mul_nonneg hApos.le (sq_nonneg r))
      _ = E ^ 25 * (A * r ^ 2 * R * T) := by ring
  have hEpos : 0 < E ^ 25 := by positivity
  have hresult : L ^ 100 ≤ A * r ^ 2 * R * T :=
    (mul_le_mul_left hEpos).mp hfinal
  simpa [L, T] using hresult

end JSP000089


namespace JSP000089

lemma sourceLemma43LocalSet_lower_support {j x : ℕ}
    (hx : x ∈ sourceLemma43LocalSet j) :
    2 ^ (j - 1) ≤ x := by
  rcases Finset.mem_union.mp (sourceLemma43LocalSet_subset_adjacentBlocks j hx) with hxj | hxnext
  · exact (Finset.mem_Icc.mp (by simpa [sourceLemma43DyadicBlock] using hxj)).1
  · have hnext := (Finset.mem_Icc.mp (by simpa [sourceLemma43DyadicBlock] using hxnext)).1
    have hpow : 2 ^ (j - 1) ≤ 2 ^ j := by
      exact Nat.pow_le_pow_right (by omega) (by omega)
    exact hpow.trans hnext

end JSP000089


namespace JSP000089

lemma sourceLemma43LocalSet_scale_le_log {j x n : ℕ}
    (hx : x ∈ sourceLemma43LocalSet j) (hxn : x ≤ n) :
    j ≤ Nat.log2 n + 1 := by
  have hpow : 2 ^ (j - 1) ≤ n :=
    (sourceLemma43LocalSet_lower_support hx).trans hxn
  have hlog : j - 1 ≤ Nat.log 2 n :=
    Nat.le_log_of_pow_le (by norm_num) hpow
  rw [← Nat.log2_eq_log_two] at hlog
  omega

end JSP000089


namespace JSP000089

noncomputable def sourceLemma43LocalUnionUpTo (n : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (Nat.log2 n + 1)).biUnion sourceLemma43LocalSet

lemma initialSegmentCount_sourceLemma43Set_le_localSum (n : ℕ) :
    initialSegmentCount sourceLemma43Set n ≤
      ∑ j ∈ Finset.Icc 1 (Nat.log2 n + 1), (sourceLemma43LocalSet j).card := by
  classical
  rw [initialSegmentCount]
  calc
    {x ∈ Finset.range (n + 1) | 0 < x ∧ x ∈ sourceLemma43Set}.card ≤
        (sourceLemma43LocalUnionUpTo n).card := by
      refine Finset.card_le_card ?_
      intro x hx
      rw [Finset.mem_filter] at hx
      rcases hx.2.2 with ⟨j, hj, hxlocal⟩
      have hxn : x ≤ n := by
        have : x < n + 1 := Finset.mem_range.mp hx.1
        omega
      have hjupper : j ≤ Nat.log2 n + 1 :=
        sourceLemma43LocalSet_scale_le_log hxlocal hxn
      exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_Icc.mpr ⟨hj, hjupper⟩, hxlocal⟩
    _ ≤ ∑ j ∈ Finset.Icc 1 (Nat.log2 n + 1), (sourceLemma43LocalSet j).card := by
      exact Finset.card_biUnion_le

end JSP000089


namespace JSP000089

lemma card_sourceLemma43_contributingScales (n : ℕ) :
    (Finset.Icc 1 (Nat.log2 n + 1)).card ≤ Nat.log2 n + 1 := by
  simp

end JSP000089


namespace JSP000089

lemma sourceLemma43_power_sum_100 (s : Finset ℕ) (f : ℕ → ℕ) :
    (∑ j ∈ s, f j) ^ 100 ≤ s.card ^ 99 * ∑ j ∈ s, (f j) ^ 100 := by
  simpa using (pow_sum_le_card_mul_sum_pow (s := s)
    (f := f) (fun _ _ => Nat.zero_le _) 99)

end JSP000089


namespace JSP000089

lemma initialSegmentCount_sourceLemma43Set_pow100_le_weightedLocalPowers (n : ℕ) :
    initialSegmentCount sourceLemma43Set n ^ 100 ≤
      (Finset.Icc 1 (Nat.log2 n + 1)).card ^ 99 *
        ∑ j ∈ Finset.Icc 1 (Nat.log2 n + 1),
          (sourceLemma43LocalSet j).card ^ 100 := by
  have hsum := initialSegmentCount_sourceLemma43Set_le_localSum n
  calc
    initialSegmentCount sourceLemma43Set n ^ 100 ≤
        (∑ j ∈ Finset.Icc 1 (Nat.log2 n + 1),
          (sourceLemma43LocalSet j).card) ^ 100 :=
      Nat.pow_le_pow_left hsum 100
    _ ≤ _ := sourceLemma43_power_sum_100
      (Finset.Icc 1 (Nat.log2 n + 1)) (fun j => (sourceLemma43LocalSet j).card)

end JSP000089


namespace JSP000089

lemma sourceLemma43_exists_regular_power_bound :
    ∃ J : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ j : ℕ, J ≤ j →
      ((sourceLemma43LocalSet j).card : ℝ) ^ 100 ≤
        C * (2 : ℝ) ^ ((((4751 : ℕ) * j : ℕ) : ℝ) / 48) := by
  rcases sourceLemma43_regular_local_power100_with_slack with ⟨J, C, hC, h⟩
  refine ⟨max J sourceLemma43ThresholdCutoff, C, hC, ?_⟩
  intro j hj
  exact h j ((le_max_left J sourceLemma43ThresholdCutoff).trans hj)
    (sourceLemma43_threshold_admissible_of_cutoff_le
      ((le_max_right J sourceLemma43ThresholdCutoff).trans hj))

end JSP000089


namespace JSP000089

lemma sourceLemma43_regular_power_sum_le {J : ℕ} {C : ℝ}
    (hC : 0 ≤ C)
    (hregular : ∀ j : ℕ, J ≤ j →
      ((sourceLemma43LocalSet j).card : ℝ) ^ 100 ≤
        C * (2 : ℝ) ^ ((((4751 : ℕ) * j : ℕ) : ℝ) / 48))
    (s : Finset ℕ) (hs : ∀ j ∈ s, J ≤ j) :
    ∑ j ∈ s, ((sourceLemma43LocalSet j).card : ℝ) ^ 100 ≤
      C * ∑ j ∈ s, (2 : ℝ) ^ ((((4751 : ℕ) * j : ℕ) : ℝ) / 48) := by
  calc
    ∑ j ∈ s, ((sourceLemma43LocalSet j).card : ℝ) ^ 100 ≤
        ∑ j ∈ s, C * (2 : ℝ) ^ ((((4751 : ℕ) * j : ℕ) : ℝ) / 48) := by
      exact Finset.sum_le_sum fun j hj => hregular j (hs j hj)
    _ = C * ∑ j ∈ s, (2 : ℝ) ^ ((((4751 : ℕ) * j : ℕ) : ℝ) / 48) := by
      rw [Finset.mul_sum]

end JSP000089


namespace JSP000089

lemma sourceLemma43_rpow_tail_le_endpoint {s : Finset ℕ} {J : ℕ}
    (hs : ∀ j ∈ s, j ≤ J) :
    ∑ j ∈ s, (2 : ℝ) ^ ((((4751 : ℕ) * j : ℕ) : ℝ) / 48) ≤
      s.card * (2 : ℝ) ^ ((((4751 : ℕ) * J : ℕ) : ℝ) / 48) := by
  calc
    ∑ j ∈ s, (2 : ℝ) ^ ((((4751 : ℕ) * j : ℕ) : ℝ) / 48) ≤
        ∑ _j ∈ s, (2 : ℝ) ^ ((((4751 : ℕ) * J : ℕ) : ℝ) / 48) := by
      exact Finset.sum_le_sum fun j hj => by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
        apply div_le_div_of_nonneg_right _ (by norm_num)
        exact_mod_cast (Nat.mul_le_mul_left 4751 (hs j hj))
    _ = s.card * (2 : ℝ) ^ ((((4751 : ℕ) * J : ℕ) : ℝ) / 48) := by
      simp [mul_comm]

end JSP000089


namespace JSP000089

lemma sourceLemma43_scale_count_absorbed : ∃ J : ℕ, ∀ j : ℕ, J ≤ j →
    (j : ℝ) ^ 100 ≤ ((2 : ℝ) ^ ((1 : ℝ) / 48)) ^ 2 *
      ((2 : ℝ) ^ ((1 : ℝ) / 48)) ^ j := by
  rcases sourceLemma43_polynomial_absorbed_with_slack with ⟨J, hJ⟩
  refine ⟨J, fun j hj => ?_⟩
  calc
    (j : ℝ) ^ 100 ≤ (j + 2 : ℝ) ^ 125 := by
      calc
        (j : ℝ) ^ 100 ≤ (j + 2 : ℝ) ^ 100 :=
          pow_le_pow_left₀ (by positivity) (by norm_num) 100
        _ ≤ (j + 2 : ℝ) ^ 125 :=
          pow_le_pow_right₀ (by nlinarith [show (0 : ℝ) ≤ j by positivity]) (by omega)
    _ ≤ _ := hJ j hj

end JSP000089


namespace JSP000089

lemma sourceLemma43_regular_power_sum_endpoint {J₀ J : ℕ} {C : ℝ}
    (hC : 0 ≤ C)
    (hregular : ∀ j : ℕ, J₀ ≤ j → ((sourceLemma43LocalSet j).card : ℝ) ^ 100 ≤ C * (2 : ℝ) ^ ((((4751 : ℕ) * j : ℕ) : ℝ) / 48))
    (s : Finset ℕ) (hlow : ∀ j ∈ s, J₀ ≤ j) (hupp : ∀ j ∈ s, j ≤ J) :
    ∑ j ∈ s, ((sourceLemma43LocalSet j).card : ℝ) ^ 100 ≤
      C * (s.card * (2 : ℝ) ^ ((((4751 : ℕ) * J : ℕ) : ℝ) / 48)) := by
  calc
    _ ≤ C * ∑ j ∈ s, (2 : ℝ) ^ ((((4751 : ℕ) * j : ℕ) : ℝ) / 48) := sourceLemma43_regular_power_sum_le hC hregular s hlow
    _ ≤ C * (s.card * (2 : ℝ) ^ ((((4751 : ℕ) * J : ℕ) : ℝ) / 48)) :=
      mul_le_mul_of_nonneg_left (sourceLemma43_rpow_tail_le_endpoint hupp) hC

end JSP000089


namespace JSP000089

lemma sourceLemma43_regular_power_sum_endpoint_le {J₀ J : ℕ} {C : ℝ}
    (hC : 0 ≤ C)
    (hregular : ∀ j : ℕ, J₀ ≤ j →
      ((sourceLemma43LocalSet j).card : ℝ) ^ 100 ≤
        C * (2 : ℝ) ^ ((((4751 : ℕ) * j : ℕ) : ℝ) / 48))
    (s : Finset ℕ) (hlow : ∀ j ∈ s, J₀ ≤ j) (hupp : ∀ j ∈ s, j ≤ J) :
    ∑ j ∈ s, ((sourceLemma43LocalSet j).card : ℝ) ^ 100 ≤
      C * (s.card * (2 : ℝ) ^ ((((4751 : ℕ) * J : ℕ) : ℝ) / 48)) := by
  calc
    ∑ j ∈ s, ((sourceLemma43LocalSet j).card : ℝ) ^ 100 ≤
        C * ∑ j ∈ s, (2 : ℝ) ^ ((((4751 : ℕ) * j : ℕ) : ℝ) / 48) :=
      sourceLemma43_regular_power_sum_le hC hregular s hlow
    _ ≤ C * (s.card * (2 : ℝ) ^ ((((4751 : ℕ) * J : ℕ) : ℝ) / 48)) :=
      mul_le_mul_of_nonneg_left (sourceLemma43_rpow_tail_le_endpoint hupp) hC

end JSP000089
namespace JSP000089

lemma sourceLemma43_global_local_power_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ j : ℕ,
      ((sourceLemma43LocalSet j).card : ℝ) ^ 100 ≤
        C * (2 : ℝ) ^ ((((4751 : ℕ) * j : ℕ) : ℝ) / 48) := by
  rcases sourceLemma43_exists_regular_power_bound with ⟨J, C, hC, hregular⟩
  let E : ℝ := ∑ j ∈ Finset.range J, ((sourceLemma43LocalSet j).card : ℝ) ^ 100
  refine ⟨C + E + 1, by positivity, ?_⟩
  intro j
  have hexp : 1 ≤ (2 : ℝ) ^ ((((4751 : ℕ) * j : ℕ) : ℝ) / 48) := by
    apply Real.one_le_rpow
    · norm_num
    · positivity
  by_cases hj : J ≤ j
  · calc
      ((sourceLemma43LocalSet j).card : ℝ) ^ 100 ≤
          C * (2 : ℝ) ^ ((((4751 : ℕ) * j : ℕ) : ℝ) / 48) := hregular j hj
      _ ≤ (C + E + 1) * (2 : ℝ) ^ ((((4751 : ℕ) * j : ℕ) : ℝ) / 48) := by
        gcongr
        have hE : 0 ≤ E := by
          dsimp [E]
          exact Finset.sum_nonneg (fun i _ =>
            pow_nonneg (by positivity : (0 : ℝ) ≤ (sourceLemma43LocalSet i).card) 100)
        nlinarith
  · have hjmem : j ∈ Finset.range J := Finset.mem_range.mpr (Nat.lt_of_not_ge hj)
    have hterm : ((sourceLemma43LocalSet j).card : ℝ) ^ 100 ≤ E := by
      dsimp [E]
      exact Finset.single_le_sum (s := Finset.range J)
        (f := fun i => ((sourceLemma43LocalSet i).card : ℝ) ^ 100)
        (fun i _ => pow_nonneg (by positivity :
          (0 : ℝ) ≤ (sourceLemma43LocalSet i).card) 100) hjmem
    calc
      ((sourceLemma43LocalSet j).card : ℝ) ^ 100 ≤ E := hterm
      _ ≤ C + E + 1 := by linarith
      _ ≤ (C + E + 1) * (2 : ℝ) ^ ((((4751 : ℕ) * j : ℕ) : ℝ) / 48) :=
        le_mul_of_one_le_right (by positivity) hexp

lemma sourceLemma43_global_scale_count_bound :
    ∃ D : ℝ, 0 < D ∧ ∀ j : ℕ,
      (j : ℝ) ^ 100 ≤ D * ((2 : ℝ) ^ ((1 : ℝ) / 48)) ^ j := by
  rcases sourceLemma43_scale_count_absorbed with ⟨J, hJ⟩
  let E : ℝ := ∑ j ∈ Finset.range J, (j : ℝ) ^ 100
  let r : ℝ := (2 : ℝ) ^ ((1 : ℝ) / 48)
  refine ⟨r ^ 2 + E + 1, by positivity, ?_⟩
  intro j
  have hr : 1 ≤ r ^ j := by
    apply one_le_pow₀
    dsimp [r]
    exact Real.one_le_rpow (by norm_num) (by positivity)
  by_cases hj : J ≤ j
  · calc
      (j : ℝ) ^ 100 ≤ r ^ 2 * r ^ j := by simpa [r] using hJ j hj
      _ ≤ (r ^ 2 + E + 1) * r ^ j := by
        gcongr
        have hE : 0 ≤ E := by
          dsimp [E]
          exact Finset.sum_nonneg (fun i _ =>
            pow_nonneg (by positivity : (0 : ℝ) ≤ i) 100)
        nlinarith
  · have hjmem : j ∈ Finset.range J := Finset.mem_range.mpr (Nat.lt_of_not_ge hj)
    have hterm : (j : ℝ) ^ 100 ≤ E := by
      dsimp [E]
      exact Finset.single_le_sum (s := Finset.range J) (f := fun i : ℕ => (i : ℝ) ^ 100)
        (fun i _ => pow_nonneg (by positivity : (0 : ℝ) ≤ i) 100) hjmem
    calc
      (j : ℝ) ^ 100 ≤ E := hterm
      _ ≤ r ^ 2 + E + 1 := by nlinarith [sq_nonneg r]
      _ ≤ (r ^ 2 + E + 1) * r ^ j :=
        le_mul_of_one_le_right (by positivity) hr

end JSP000089
namespace JSP000089

lemma sourceLemma43_initialSegmentCount_real_bound :
    ∃ A : ℝ, 0 < A ∧ ∀ n : ℕ, 0 < n →
      (initialSegmentCount sourceLemma43Set n : ℝ) ^ 100 ≤ A * (n : ℝ) ^ 99 := by
  rcases sourceLemma43_global_local_power_bound with ⟨C, hC, hlocal⟩
  rcases sourceLemma43_global_scale_count_bound with ⟨D, hD, hscale⟩
  let r : ℝ := (2 : ℝ) ^ ((1 : ℝ) / 48)
  let A : ℝ := D * C * (2 : ℝ) ^ 99
  refine ⟨A, by positivity, ?_⟩
  intro n hn
  let J := Nat.log2 n + 1
  let s := Finset.Icc 1 J
  have hcard : (s.card : ℝ) ≤ J := by
    exact_mod_cast card_sourceLemma43_contributingScales n
  have hsum : ∑ j ∈ s, ((sourceLemma43LocalSet j).card : ℝ) ^ 100 ≤
      C * (s.card * (2 : ℝ) ^ ((((4751 : ℕ) * J : ℕ) : ℝ) / 48)) := by
    exact sourceLemma43_regular_power_sum_endpoint (J₀ := 0) hC.le
      (fun j _ => hlocal j) s (fun _ _ => Nat.zero_le _) (fun j hj => (Finset.mem_Icc.mp hj).2)
  have hcount : (initialSegmentCount sourceLemma43Set n : ℝ) ^ 100 ≤
      (s.card : ℝ) ^ 99 * ∑ j ∈ s, ((sourceLemma43LocalSet j).card : ℝ) ^ 100 := by
    exact_mod_cast initialSegmentCount_sourceLemma43Set_pow100_le_weightedLocalPowers n
  have hcombined : (initialSegmentCount sourceLemma43Set n : ℝ) ^ 100 ≤
      C * (J : ℝ) ^ 100 * (2 : ℝ) ^ ((((4751 : ℕ) * J : ℕ) : ℝ) / 48) := by
    have hs_nonneg : (0 : ℝ) ≤ (s.card : ℝ) := by
      exact_mod_cast Nat.zero_le s.card
    have hs99_nonneg : 0 ≤ (s.card : ℝ) ^ 99 := pow_nonneg hs_nonneg 99
    have hcard100 : (s.card : ℝ) ^ 100 ≤ (J : ℝ) ^ 100 :=
      pow_le_pow_left₀ hs_nonneg hcard 100
    have hE_nonneg : 0 ≤ (2 : ℝ) ^ ((((4751 : ℕ) * J : ℕ) : ℝ) / 48) :=
      Real.rpow_nonneg (by norm_num) _
    calc
      (initialSegmentCount sourceLemma43Set n : ℝ) ^ 100 ≤
          (s.card : ℝ) ^ 99 * ∑ j ∈ s, ((sourceLemma43LocalSet j).card : ℝ) ^ 100 := hcount
      _ ≤ (s.card : ℝ) ^ 99 *
          (C * ((s.card : ℝ) * (2 : ℝ) ^ ((((4751 : ℕ) * J : ℕ) : ℝ) / 48))) :=
        mul_le_mul_of_nonneg_left hsum hs99_nonneg
      _ = C * (s.card : ℝ) ^ 100 *
          (2 : ℝ) ^ ((((4751 : ℕ) * J : ℕ) : ℝ) / 48) := by ring
      _ ≤ C * (J : ℝ) ^ 100 *
          (2 : ℝ) ^ ((((4751 : ℕ) * J : ℕ) : ℝ) / 48) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hcard100 hC.le) hE_nonneg
  have hslack : (J : ℝ) ^ 100 ≤ D * r ^ J := by
    simpa [r] using hscale J
  have hpower : r ^ J * (2 : ℝ) ^ ((((4751 : ℕ) * J : ℕ) : ℝ) / 48) =
      (2 : ℝ) ^ ((99 : ℝ) * J) := by
    have hexponent :
        (J : ℝ) / 48 + ((((4751 : ℕ) * J : ℕ) : ℝ) / 48) =
          (99 : ℝ) * (J : ℝ) := by
      norm_num [Nat.cast_mul]
      ring
    rw [sourceLemma43_slack_base_pow J]
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    rw [hexponent]
  have hdyadic : (2 : ℝ) ^ ((99 : ℝ) * J) = ((2 : ℝ) ^ J) ^ 99 := by
    have hexponent99 :
        (99 : ℝ) * (J : ℝ) = ((J * 99 : ℕ) : ℝ) := by
      norm_num [Nat.cast_mul]
      ring
    rw [hexponent99, Real.rpow_natCast, pow_mul]
  have hendpoint : (2 : ℝ) ^ J ≤ 2 * n := by
    have hlogNat : (2 : ℕ) ^ Nat.log2 n ≤ n := by
      rw [Nat.log2_eq_log_two]
      exact Nat.pow_log_le_self 2 (Nat.ne_of_gt hn)
    have hJpowNat : (2 : ℕ) ^ J = 2 * (2 : ℕ) ^ Nat.log2 n := by
      calc
        (2 : ℕ) ^ J = (2 : ℕ) ^ Nat.log2 n * 2 := by simp [J, pow_succ]
        _ = 2 * (2 : ℕ) ^ Nat.log2 n := Nat.mul_comm _ _
    have hendpointNat : (2 : ℕ) ^ J ≤ 2 * n := by
      rw [hJpowNat]
      exact Nat.mul_le_mul_left 2 hlogNat
    exact_mod_cast hendpointNat
  have hendpointpow : ((2 : ℝ) ^ J) ^ 99 ≤ (2 * n) ^ 99 :=
    pow_le_pow_left₀ (by positivity) hendpoint 99
  calc
    (initialSegmentCount sourceLemma43Set n : ℝ) ^ 100 ≤
        C * (J : ℝ) ^ 100 * (2 : ℝ) ^ ((((4751 : ℕ) * J : ℕ) : ℝ) / 48) := hcombined
    _ ≤ C * (D * r ^ J) * (2 : ℝ) ^ ((((4751 : ℕ) * J : ℕ) : ℝ) / 48) := by
      gcongr
    _ = D * C * (2 : ℝ) ^ ((99 : ℝ) * J) := by
      calc
        C * (D * r ^ J) * (2 : ℝ) ^ ((((4751 : ℕ) * J : ℕ) : ℝ) / 48) =
            D * C * (r ^ J * (2 : ℝ) ^ ((((4751 : ℕ) * J : ℕ) : ℝ) / 48)) := by ring
        _ = D * C * (2 : ℝ) ^ ((99 : ℝ) * J) := by rw [hpower]
    _ = D * C * ((2 : ℝ) ^ J) ^ 99 := by rw [hdyadic]
    _ ≤ D * C * (2 * n) ^ 99 :=
      mul_le_mul_of_nonneg_left hendpointpow (by positivity)
    _ = A * (n : ℝ) ^ 99 := by
      dsimp [A]
      ring

end JSP000089

namespace JSP000089

theorem sourceSparsity099_sourceLemma43Set :
    SourceSparsity099 sourceLemma43Set := by
  rcases sourceLemma43_initialSegmentCount_real_bound with ⟨A, hA, hbound⟩
  obtain ⟨K, hK⟩ := exists_nat_ge (A + 1)
  refine ⟨K, ?_, ?_⟩
  · have hKreal : 0 < (K : ℝ) := by linarith
    exact_mod_cast hKreal
  · intro n
    by_cases hn : n = 0
    · subst n
      classical
      have hzero : initialSegmentCount sourceLemma43Set 0 = 0 := by
        rw [initialSegmentCount, Finset.card_eq_zero, Finset.eq_empty_iff_forall_not_mem]
        intro k hk
        rw [Finset.mem_filter] at hk
        have hklt : k < 1 := Finset.mem_range.mp hk.1
        omega
      simp [hzero]
    · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
      have hmain := hbound n hnpos
      have hKone : 1 ≤ (K : ℝ) := by linarith
      have hKpow : (K : ℝ) ≤ (K : ℝ) ^ 100 := by
        calc
          (K : ℝ) = (K : ℝ) ^ 1 := by ring
          _ ≤ (K : ℝ) ^ 100 := pow_le_pow_right₀ hKone (by omega)
      have hAtoK : A ≤ (K : ℝ) ^ 100 := le_trans (by linarith) hKpow
      have hreal : (initialSegmentCount sourceLemma43Set n : ℝ) ^ 100 ≤
          (K : ℝ) ^ 100 * (n : ℝ) ^ 99 := by
        calc
          (initialSegmentCount sourceLemma43Set n : ℝ) ^ 100 ≤ A * (n : ℝ) ^ 99 := hmain
          _ ≤ (K : ℝ) ^ 100 * (n : ℝ) ^ 99 :=
            mul_le_mul_of_nonneg_right hAtoK (by positivity)
      exact_mod_cast hreal

end JSP000089

namespace JSP000089

/-- The exact `0.99` sparsity estimate is closed under a finite union. -/
theorem SourceSparsity099.union {S T : Set ℕ}
    (hS : SourceSparsity099 S) (hT : SourceSparsity099 T) :
    SourceSparsity099 (S ∪ T) := by
  classical
  obtain ⟨KS, hKS, hSbound⟩ := hS
  obtain ⟨KT, hKT, hTbound⟩ := hT
  refine ⟨2 * (KS + KT), by positivity, ?_⟩
  intro n
  let a := initialSegmentCount S n
  let b := initialSegmentCount T n
  have hcount : initialSegmentCount (S ∪ T) n ≤ a + b := by
    rw [initialSegmentCount]
    apply le_trans ?_ (Finset.card_union_le _ _)
    apply le_of_eq
    apply congrArg Finset.card
    ext k
    simp only [Finset.mem_filter, Finset.mem_union, Set.mem_union]
    aesop
  have hSpow : a ^ 100 ≤ KS ^ 100 * n ^ 99 := by
    simpa only [a] using hSbound n
  have hTpow : b ^ 100 ≤ KT ^ 100 * n ^ 99 := by
    simpa only [b] using hTbound n
  have hpow : initialSegmentCount (S ∪ T) n ^ 100 ≤ (a + b) ^ 100 :=
    Nat.pow_le_pow_left hcount 100
  have hreal : (a + b : ℝ) ^ 100 ≤
      (2 * (KS + KT) : ℝ) ^ 100 * (n : ℝ) ^ 99 := by
    have hSpowReal : (a : ℝ) ^ 100 ≤ (KS : ℝ) ^ 100 * (n : ℝ) ^ 99 := by
      exact_mod_cast hSpow
    have hTpowReal : (b : ℝ) ^ 100 ≤ (KT : ℝ) ^ 100 * (n : ℝ) ^ 99 := by
      exact_mod_cast hTpow
    have hsum : (a : ℝ) ^ 100 + (b : ℝ) ^ 100 ≤
        ((KS : ℝ) ^ 100 + (KT : ℝ) ^ 100) * (n : ℝ) ^ 99 := by
      rw [add_mul]
      exact add_le_add hSpowReal hTpowReal
    have hbinomial : (a + b : ℝ) ^ 100 ≤
        (2 : ℝ) ^ 99 * ((a : ℝ) ^ 100 + (b : ℝ) ^ 100) := by
      simpa using add_pow_le (a := (a : ℝ)) (b := (b : ℝ))
        (by positivity) (by positivity) 100
    have hbase : (KS : ℝ) ^ 100 + (KT : ℝ) ^ 100 ≤
        ((KS : ℝ) + (KT : ℝ)) ^ 100 := by
      exact pow_add_pow_le (by positivity) (by positivity) (by norm_num)
    have htwo : (2 : ℝ) ^ 99 ≤ 2 ^ 100 := by norm_num
    have hnPowNonneg : 0 ≤ (n : ℝ) ^ 99 :=
      pow_nonneg (Nat.cast_nonneg n) _
    have hKSsumNonneg : 0 ≤ (KS : ℝ) ^ 100 + (KT : ℝ) ^ 100 := by positivity
    calc
      (a + b : ℝ) ^ 100 ≤ (2 : ℝ) ^ 99 * ((a : ℝ) ^ 100 + (b : ℝ) ^ 100) :=
        hbinomial
      _ ≤ (2 : ℝ) ^ 99 * (((KS : ℝ) ^ 100 + (KT : ℝ) ^ 100) * (n : ℝ) ^ 99) := by
        gcongr
      _ ≤ (2 : ℝ) ^ 100 * (((KS : ℝ) + (KT : ℝ)) ^ 100 * (n : ℝ) ^ 99) := by
        have hbaseMul :
            ((KS : ℝ) ^ 100 + (KT : ℝ) ^ 100) * (n : ℝ) ^ 99 ≤
              ((KS : ℝ) + (KT : ℝ)) ^ 100 * (n : ℝ) ^ 99 :=
          mul_le_mul_of_nonneg_right hbase hnPowNonneg
        have hsumMulNonneg : 0 ≤
            ((KS : ℝ) ^ 100 + (KT : ℝ) ^ 100) * (n : ℝ) ^ 99 :=
          mul_nonneg hKSsumNonneg hnPowNonneg
        calc
          (2 : ℝ) ^ 99 * (((KS : ℝ) ^ 100 + (KT : ℝ) ^ 100) * (n : ℝ) ^ 99) ≤
              (2 : ℝ) ^ 100 * (((KS : ℝ) ^ 100 + (KT : ℝ) ^ 100) * (n : ℝ) ^ 99) :=
            mul_le_mul_of_nonneg_right htwo hsumMulNonneg
          _ ≤ (2 : ℝ) ^ 100 * (((KS : ℝ) + (KT : ℝ)) ^ 100 * (n : ℝ) ^ 99) :=
            mul_le_mul_of_nonneg_left hbaseMul (by positivity)
      _ = (2 * (KS + KT) : ℝ) ^ 100 * (n : ℝ) ^ 99 := by
        norm_num [mul_pow]
        ring
  have hrealNat : (a + b) ^ 100 ≤
      (2 * (KS + KT)) ^ 100 * n ^ 99 := by
    exact_mod_cast hreal
  exact hpow.trans hrealNat

/-- The source final set is the union of its Lemma 4.3 set and the finite
short-cycle prefix, and has the exact required sparsity estimate. -/
theorem sourceSparsity099_finalSet :
    SourceSparsity099 (sourceLemma43Set ∪ sourceShortCycleLengths) :=
  sourceSparsity099_sourceLemma43Set.union sourceSparsity099_sourceShortCycleLengths

end JSP000089
