import SubspaceBridge.WeightedPairLinear2
import SubspaceBridge.WeightedPairCover2
namespace JSP000334

def weightedPairFiber (A B C : ℚ) (P : Submodule ℚ (Fin 2 → ℚ)) :
    Set (fixedSUnitGroup × fixedSUnitGroup) :=
  {p | p ∈ weightedFixedSUnitPairs A B C ∧
    ![((p.1 : ℚˣ) : ℚ),((p.2 : ℚˣ) : ℚ)] ∈ P}

theorem weighted_pair_fiber_subsingleton (A B C : ℚ) (hA : A ≠ 0) (hC : C ≠ 0)
    (P : Submodule ℚ (Fin 2 → ℚ)) (hP : P ≠ ⊤) :
    (weightedPairFiber A B C P).Subsingleton := by
  obtain ⟨b0,b1,hb,hann⟩ := binary_proper_annihilator P hP
  intro p hp q hq
  have hlp : b0*((p.1 : ℚˣ) : ℚ)+b1*((p.2 : ℚˣ) : ℚ)=0 :=
    hann _ hp.2
  have hlq : b0*((q.1 : ℚˣ) : ℚ)+b1*((q.2 : ℚˣ) : ℚ)=0 :=
    hann _ hq.2
  have hd := weighted_pair_determinant A B C b0 b1 _ _ hA hC hb hp.1 hlp
  have ep := weighted_pair_exact_values A B C b0 b1 _ _ hd hp.1 hlp
  have eq := weighted_pair_exact_values A B C b0 b1 _ _ hd hq.1 hlq
  apply Prod.ext
  · apply Subtype.ext
    apply Units.ext
    exact ep.1.trans eq.1.symm
  · apply Subtype.ext
    apply Units.ext
    exact ep.2.trans eq.2.symm

theorem weighted_pair_fiber_finite (A B C : ℚ) (hA : A ≠ 0) (hC : C ≠ 0)
    (P : Submodule ℚ (Fin 2 → ℚ)) (hP : P ≠ ⊤) :
    (weightedPairFiber A B C P).Finite :=
  (weighted_pair_fiber_subsingleton A B C hA hC P hP).finite

theorem weighted_fixed_sunit_pair_finite
    (A B C : ℚ)
    (hA : A ≠ 0)
    (hB : B ≠ 0)
    (hC : C ≠ 0) :
    (weightedFixedSUnitPairs A B C).Finite := by
  obtain ⟨F,hF,hproper,hcover⟩ := weighted_pair_finite_proper_cover A B C hA hB hC
  have hU : (⋃ P ∈ F, weightedPairFiber A B C P).Finite :=
    hF.biUnion (fun P hP => weighted_pair_fiber_finite A B C hA hC P (hproper P hP))
  apply hU.subset
  intro p hp
  obtain ⟨P,hPF,hpP⟩ := hcover p hp
  exact Set.mem_iUnion.mpr ⟨P,Set.mem_iUnion.mpr ⟨hPF,⟨hp,hpP⟩⟩⟩

end JSP000334
