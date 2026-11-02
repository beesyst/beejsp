import SubspaceBridge.SourceSatz51Data218
import SubspaceBridge.SourceOriginalSatz215
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceSatz51Entry218
open SourceOriginalVariable10 SourceOriginalDual10 SourceOriginalBounds215 OriginalDual10

theorem source_product_transport218
    {A2 A3 : Matrix (Fin 10) (Fin 10) ℚ} {L : Matrix (Fin 10) (Fin 10) ℝ} {hL : IsUnit L}
    {q : ℝ} {hq : 1 < q} {c2 c3 A : Fin 10 → ℝ} {delta : ℝ}
    (h2 : ∀ i, -1 ≤ c2 i ∧ c2 i ≤ 0) (h3 : ∀ i, -1 ≤ c3 i ∧ c3 i ≤ 0)
    (D : SourceData218 A2 A3 L hL q hq c2 c3 A delta) (hq6 : 6 < q)
    (hslack : 6 ≤ q^(delta/4)) (S0 : Finset (Fin 3 → Fin 10))
    (hS : sourceSet218 q delta A c2 c3 = S0) (s : Fin 3 → Fin 10) :
    dataRationalDualProduct10 (toOriginalData218 h2 h3 D hq6 hslack S0 hS) s =
      originalRationalDualProduct10 A2 A3 L D.u
        (integer_frame_rational_independent10 D.u D.independent) s := by
  exact congrArg (fun hu => originalRationalDualProduct10 A2 A3 L D.u hu s)
    (Subsingleton.elim (dataRationalDualProduct10._proof_6 (toOriginalData218 h2 h3 D hq6 hslack S0 hS))
      (integer_frame_rational_independent10 D.u D.independent))

theorem source_entry_cutoff218 (delta : ℝ) (hd : 0 < delta) :
    ∃ T : ℝ, 6 < T ∧ ∀ q : ℝ, T < q → 6 ≤ q^(delta/4) := by
  obtain ⟨B,hB⟩ := Filter.eventually_atTop.mp
    ((tendsto_rpow_atTop (show 0 < delta/4 by linarith)).eventually (Filter.eventually_gt_atTop (6 : ℝ)))
  refine ⟨max 7 B,lt_of_lt_of_le (by norm_num : (6 : ℝ) < 7) (le_max_left _ _),?_⟩
  intro q hq
  exact (hB q ((le_max_right _ _).trans hq.le)).le

theorem source_entry_fixed_set_vanishing218
    (A2 A3 : Matrix (Fin 10) (Fin 10) ℚ) (L : Matrix (Fin 10) (Fin 10) ℝ)
    (h2d : A2.det = 1) (h3d : A3.det = 1) (hLd : L.det = 1) (hL : IsUnit L)
    (hAlg : ∀ i j, IsAlgebraic ℚ (L i j)) (c2 c3 : Fin 10 → ℝ)
    (h2 : ∀ i, -1 ≤ c2 i ∧ c2 i ≤ 0) (h3 : ∀ i, -1 ≤ c3 i ∧ c3 i ≤ 0)
    (delta : ℝ) (hd : 0 < delta) (Omega : Set ℝ) (hO : ¬ BddAbove Omega)
    (hq : ∀ q ∈ Omega, 1 < q) (A : ℝ → Fin 10 → ℝ)
    (D : ∀ q : Omega, SourceData218 A2 A3 L hL q.val (hq q.val q.property) c2 c3 (A q.val) delta) :
    ∃ S0 : Finset (Fin 3 → Fin 10), S0.Nonempty ∧ ∃ B : ℝ, 6 < B ∧
      ∃ U : Set ℝ, U ⊆ Omega ∧ ¬ BddAbove U ∧
        ∀ q : Omega, q.val ∈ U → B < q.val ∧ sourceSet218 q.val delta (A q.val) c2 c3 = S0 ∧
          ∀ s ∈ S0, originalRationalDualProduct10 A2 A3 L (D q).u
            (integer_frame_rational_independent10 (D q).u (D q).independent) s = 0 := by
  obtain ⟨S0,hS0,V,hVO,hV,hpattern⟩ := source_set_unbounded_selection218 Omega hO delta A c2 c3
    (fun q hqO => source_set_nonempty218 q delta (hq q hqO) hd (A q) c2 c3
      (D ⟨q,hqO⟩).positive (D ⟨q,hqO⟩).balance)
  obtain ⟨Q0,_hQ0,hzero⟩ := original_satz41_fin10_two_places215 A2 A3 L h2d h3d hLd hL hAlg
    (delta/2) (by linarith) S0
  obtain ⟨T,hT,hslack⟩ := source_entry_cutoff218 delta hd
  let B := max T Q0
  let U := {q : ℝ | q ∈ V ∧ B < q}
  have hU : ¬ BddAbove U := by
    rintro ⟨C,hC⟩
    obtain ⟨q,hqV,hqgt⟩ := (not_bddAbove_iff.mp hV) (max B C)
    have hqU : q ∈ U := ⟨hqV,(le_max_left _ _).trans_lt hqgt⟩
    exact (not_le_of_gt ((le_max_right _ _).trans_lt hqgt)) (hC hqU)
  refine ⟨S0,hS0,B,hT.trans_le (le_max_left _ _),U,fun _ h => hVO h.1,hU,?_⟩
  intro q hqU
  have hBQ : B < q.val := hqU.2
  have hTQ : T < q.val := (le_max_left _ _).trans_lt hBQ
  have hq6 : 6 < q.val := hT.trans hTQ
  have hpat := hpattern q.val hqU.1
  refine ⟨hBQ,hpat,?_⟩
  intro s hs
  let D' := toOriginalData218 h2 h3 (D q) hq6 (hslack q.val hTQ) S0 hpat
  have hQ0 : Q0 < q.val^2 := by
    have hQq : Q0 < q.val := (le_max_right _ _).trans_lt hBQ
    have hqq : q.val < q.val^2 := by nlinarith [hq q.val q.property]
    exact hQq.trans hqq
  have hz := (hzero (q.val^2) (squared_parameter218 q.val (hq q.val q.property)) hQ0 D').2.2 s hs
  exact (source_product_transport218 h2 h3 (D q) hq6 (hslack q.val hTQ) S0 hpat s).symm.trans hz

end CompoundFeasibility.SourceSatz51Entry218
