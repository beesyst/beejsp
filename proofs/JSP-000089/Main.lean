import Mathlib.Combinatorics.SimpleGraph.Girth
import Mathlib.Combinatorics.SimpleGraph.Path

/-!
The Iteration 5 formalization retains the Iteration 4 finite cycle-length
representation. It additionally proves the source proof's short-cycle branch:
a graph with a positive girth at most `2^120` has a cycle length in the finite
prefix included in Verstraëte's final set. The high-girth graph theorem
remains in `STATEMENT.md` as an unproved obligation; the sparse construction
is formalized in `Construction.lean`.
-/

namespace JSP000089

/-- `length` is the length of a simple cycle of the finite graph `G`. -/
def IsCycleLength {V : Type*} (G : SimpleGraph V) (length : ℕ) : Prop :=
  ∃ vertex : V, ∃ walk : G.Walk vertex vertex, walk.IsCycle ∧ walk.length = length

/-- A simple cycle in a finite graph has at most as many edges as the graph has vertices. -/
lemma isCycleLength_le_card {V : Type*} [Fintype V] {G : SimpleGraph V} {vertex : V}
    {walk : G.Walk vertex vertex} (hCycle : walk.IsCycle) :
    walk.length ≤ Fintype.card V := by
  have hLength : walk.length = walk.support.tail.length := by
    simp [SimpleGraph.Walk.length_support]
  rw [hLength]
  exact hCycle.support_nodup.length_le_card

/-- The finite set of all simple-cycle lengths of a finite simple graph. -/
noncomputable def cycleLengths {V : Type*} [Fintype V] (G : SimpleGraph V) : Finset ℕ := by
  classical
  exact (Finset.range (Fintype.card V + 1)).filter fun length => IsCycleLength G length

/-- A graph has a cycle whose length belongs to the prescribed source set. -/
def HasCycleLengthIn {V : Type*} [Fintype V] (G : SimpleGraph V)
    (lengths : Set ℕ) : Prop :=
  ∃ length, IsCycleLength G length ∧ length ∈ lengths

/-- The finite prefix `[2^120]` included in Verstraëte's final source set. -/
def sourceShortCycleLengths : Set ℕ :=
  {length | 0 < length ∧ length ≤ 2 ^ 120}

/-- Source proof final-case infrastructure: a graph whose positive girth is at
most `2^120` has a cycle length in the finite prefix `[2^120]`. -/
theorem hasCycleLengthIn_sourceShortCycleLengths_of_girth_le {V : Type*} [Fintype V]
    (G : SimpleGraph V) (hPositiveGirth : 0 < G.girth) (hGirth : G.girth ≤ 2 ^ 120) :
    HasCycleLengthIn G sourceShortCycleLengths := by
  have hNotAcyclic : ¬ G.IsAcyclic := by
    intro hAcyclic
    have hZero : G.girth = 0 := hAcyclic.girth_eq_zero
    omega
  obtain ⟨vertex, walk, hCycle, hLength⟩ := (SimpleGraph.exists_girth_eq_length.mpr hNotAcyclic)
  exact ⟨G.girth, ⟨vertex, walk, hCycle, hLength.symm⟩, hPositiveGirth, hGirth⟩

/-- The finite cycle-length witness set selected by a source set. -/
noncomputable def permittedCycleLengths {V : Type*} [Fintype V] (G : SimpleGraph V)
    (lengths : Set ℕ) : Finset ℕ := by
  classical
  exact (cycleLengths G).filter fun length => length ∈ lengths

/-- The source-style existential cycle claim is exactly a nonempty filtered
finite set of cycle lengths. -/
theorem hasCycleLengthIn_iff_filter_nonempty {V : Type*} [Fintype V]
    (G : SimpleGraph V) (lengths : Set ℕ) :
    HasCycleLengthIn G lengths ↔ (permittedCycleLengths G lengths).Nonempty := by
  classical
  constructor
  · rintro ⟨length, hCycleLength, hAllowed⟩
    refine ⟨length, Finset.mem_filter.mpr ⟨?_, hAllowed⟩⟩
    rw [cycleLengths, Finset.mem_filter]
    obtain ⟨vertex, walk, hCycle, hLength⟩ := hCycleLength
    exact ⟨Finset.mem_range.mpr (Nat.lt_succ_iff.mpr (hLength ▸ isCycleLength_le_card hCycle)),
      ⟨vertex, walk, hCycle, hLength⟩⟩
  · rintro ⟨length, hLength⟩
    have hCycleLength : IsCycleLength G length := by
      have hCycle := (Finset.mem_filter.mp hLength).1
      rw [cycleLengths, Finset.mem_filter] at hCycle
      exact hCycle.2
    exact ⟨length, hCycleLength, (Finset.mem_filter.mp hLength).2⟩

end JSP000089
