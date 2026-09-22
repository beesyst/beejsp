import Mathlib.Combinatorics.SimpleGraph.Path

/-!
The bounded Iteration 4 spike for JSP-000089 is kept deliberately below the
source theorem: it represents the finite graph/cycle-length boundary and proves
its finite-set witness equivalence. `STATEMENT.md` records the unproved full
source theorem contract.
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
