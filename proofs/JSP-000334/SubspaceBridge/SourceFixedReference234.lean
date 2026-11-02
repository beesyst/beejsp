import SubspaceBridge.SourceFixedIndex234
import SubspaceBridge.SourceFixedPairing234
import SubspaceBridge.SourceCofactorGeometry233
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceFixedArithmetic234
open SourceOriginalDual10 SourceDualGeometry219

theorem fixed_rescale_mem234 (A2 A3 : Matrix (Fin 10) (Fin 10) ℚ)
    (h2 : IsUnit A2) (h3 : IsUnit A3) (v : Fin 10 → ℤ) (hv : v ≠ 0) :
    ∃ C : ℤ, 0 < C ∧ ∀ (q : ℝ), 1 < q → ∀ (c2 c3 : Fin 10 → ℝ),
      (∀ i, c2 i ≤ 0) → (∀ i, c3 i ≤ 0) →
      let t : ℤ := C*2^((9-floorMin234 2 A2 h2 q c2 v hv).toNat)*
        3^((9-floorMin234 3 A3 h3 q c3 v hv).toNat)
      t ≠ 0 ∧ (fun i => ((t • v) i : ℚ)) ∈ scaledDual219
        (originalSourceGroup10 A2 A3 q c2 c3) := by
  obtain ⟨I,hI,hindex⟩ := source_index_dvd234 A2 A3 h2 h3
  obtain ⟨d2,hd2,M2,hM2⟩ := clear_positive234 A2
  obtain ⟨f2,hf2,N2,hN2⟩ := clear_positive234 A2⁻¹.transpose
  obtain ⟨d3,hd3,M3,hM3⟩ := clear_positive234 A3
  obtain ⟨f3,hf3,N3,hN3⟩ := clear_positive234 A3⁻¹.transpose
  let C : ℤ := (I : ℤ)*d2*f2*d3*f3
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro q hq c2 c3 hc2 hc3 t
  have ht : t ≠ 0 := by dsimp [t,C]; positivity
  refine ⟨ht,?_⟩
  let e2 := fun i => Nat.ceil (JSP000334.qThreshold 2 q (c2 i))
  let e3 := fun i => Nat.ceil (JSP000334.qThreshold 3 q (c3 i))
  let P2 : ℤ := 2^((9-floorMin234 2 A2 h2 q c2 v hv).toNat)
  let P3 : ℤ := 3^((9-floorMin234 3 A3 h3 q c3 v hv).toNat)
  let G := originalSourceGroup10 A2 A3 q c2 c3
  have hdi : G.index ∣ I*2^(∑ i, e2 i)*3^(∑ i, e3 i) := hindex e2 e3
  have hG : G.index ≠ 0 := ne_zero_of_dvd_ne_zero (by positivity) hdi
  apply (scaledDual_pairing219 G hG _).mpr
  intro x
  have hx : (x : Fin 10 → ℤ) ∈ sourceLattice10 A2 A3 e2 e3 := x.property
  have hlocal2 := local_rescale_dvd234 2 (by decide) A2 h2 d2 f2 M2 N2 hM2 hN2
    q hq c2 hc2 v hv x hx.1
  have hlocal3 := local_rescale_dvd234 3 (by decide) A3 h3 d3 f3 M3 N3 hM3 hN3
    q hq c3 hc3 v hv x hx.2
  let z : ℤ := d2*f2*d3*f3*P2*P3*(∑ i, (x : Fin 10 → ℤ) i*v i)
  have hz2 : (2 : ℤ)^(∑ i, e2 i) ∣ z := by
    simpa only [z,P2,mul_assoc,mul_left_comm,mul_comm] using
      dvd_mul_of_dvd_left hlocal2 (d3*f3*P3)
  have hz3 : (3 : ℤ)^(∑ i, e3 i) ∣ z := by
    simpa only [z,P3,mul_assoc,mul_left_comm,mul_comm] using
      dvd_mul_of_dvd_left hlocal3 (d2*f2*P2)
  have hcop : IsCoprime ((2 : ℤ)^(∑ i, e2 i)) ((3 : ℤ)^(∑ i, e3 i)) :=
    IsCoprime.pow (show IsCoprime (2 : ℤ) 3 from ⟨-1,1,by norm_num⟩)
  have hz := hcop.mul_dvd hz2 hz3
  have hzI : (I : ℤ)*2^(∑ i, e2 i)*3^(∑ i, e3 i) ∣
      t*(∑ i, (x : Fin 10 → ℤ) i*v i) := by
    have hh := mul_dvd_mul_left (I : ℤ) hz
    simpa only [t,C,z,P2,P3,mul_assoc,mul_left_comm,mul_comm] using hh
  have hiZ : (G.index : ℤ) ∣ (I : ℤ)*2^(∑ i, e2 i)*3^(∑ i, e3 i) := by
    exact_mod_cast hdi
  obtain ⟨a,ha⟩ := hiZ.trans hzI
  refine ⟨a,?_⟩
  have he : (∑ i, (x : Fin 10 → ℤ) i*(t • v) i) =
      t*(∑ i, (x : Fin 10 → ℤ) i*v i) := by
    simp only [Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  change (∑ i, ((x : Fin 10 → ℤ) i : ℚ)*((t • v) i : ℚ)) = _
  exact_mod_cast he.trans ha
open SourceSelectedUpper10 OriginalDual10 SourceSatz51Entry218 SourceOriginalDual10 SourceGlobalSelected10
  SourceCofactorGeometry233

theorem source_fixed_reference234
    (A2 A3 : Matrix (Fin 10) (Fin 10) ℚ) (L : Matrix (Fin 10) (Fin 10) ℝ)
    (h2d : A2.det = 1) (h3d : A3.det = 1) (hLd : L.det = 1) (hL : IsUnit L)
    (hAlg : ∀ i j, IsAlgebraic ℚ (L i j)) (c2 c3 : Fin 10 → ℝ)
    (h2 : ∀ i, -1 ≤ c2 i ∧ c2 i ≤ 0) (h3 : ∀ i, -1 ≤ c3 i ∧ c3 i ≤ 0)
    (delta : ℝ) (hd : 0 < delta) (Omega : Set ℝ) (hO : ¬ BddAbove Omega)
    (hq : ∀ q ∈ Omega, 1 < q) (A : ℝ → Fin 10 → ℝ)
    (D : ∀ q : Omega, SourceData218 A2 A3 L hL q.val (hq q.val q.property) c2 c3 (A q.val) delta) :
    ∃ S0 : Finset (Fin 3 → Fin 10), S0.Nonempty ∧ ∃ B : ℝ, 6 < B ∧
      ∃ U : Set ℝ, U ⊆ Omega ∧ ¬ BddAbove U ∧
        ∃ q1 : Omega, q1.val ∈ U ∧ B < q1.val ∧
          ∃ v0 : Fin 10 → ℤ, v0 = integerLastDual10 (D q1).u ∧ v0 ≠ 0 ∧
            (∀ s ∈ S0, mixedProduct10 A2 A3 L v0 s = 0) ∧
            ∀ q : Omega, q.val ∈ U → sourceSet218 q.val delta (A q.val) c2 c3 = S0 := by
  obtain ⟨S0,hS0,B,hB,U,hUO,hU,hzero⟩ := source_entry_fixed_set_vanishing218
    A2 A3 L h2d h3d hLd hL hAlg c2 c3 h2 h3 delta hd Omega hO hq A D
  obtain ⟨T,_,hpoint⟩ := source_uniform_cofactor233 delta hd
  obtain ⟨q1,hq1U,hq1gt⟩ := not_bddAbove_iff.mp hU (max B T)
  let q1O : Omega := ⟨q1,hUO hq1U⟩
  have hp := hpoint A2 A3 h2d h3d L hL hLd q1
    ((le_max_right B T).trans_lt hq1gt) (hq q1 q1O.property) c2 c3 (A q1) (D q1O)
  have hn : integerLastDual10 (D q1O).u ≠ 0 := by
    intro he
    apply hp.1
    funext i
    have hi := congrFun he i
    change (integerLastDual10 (D q1O).u i : ℚ) = 0
    exact_mod_cast hi
  refine ⟨S0,hS0,max B T,hB.trans_le (le_max_left _ _),U,hUO,hU,
    q1O,hq1U,hq1gt,integerLastDual10 (D q1O).u,rfl,hn,?_,?_⟩
  · intro s hs
    by_contra hnz
    have hh := (original_rational_product_nonzero_iff A2 A3 L (D q1O).u
      (integer_frame_rational_independent10 (D q1O).u (D q1O).independent) s).mpr hnz
    exact hh ((hzero q1O hq1U).2.2 s hs)
  · intro q hqU
    exact (hzero q hqU).2.1

theorem source_fixed_membership234
    (A2 A3 : Matrix (Fin 10) (Fin 10) ℚ) (L : Matrix (Fin 10) (Fin 10) ℝ)
    (h2d : A2.det = 1) (h3d : A3.det = 1) (hLd : L.det = 1) (hL : IsUnit L)
    (hAlg : ∀ i j, IsAlgebraic ℚ (L i j)) (c2 c3 : Fin 10 → ℝ)
    (h2 : ∀ i, -1 ≤ c2 i ∧ c2 i ≤ 0) (h3 : ∀ i, -1 ≤ c3 i ∧ c3 i ≤ 0)
    (delta : ℝ) (hd : 0 < delta) (Omega : Set ℝ) (hO : ¬ BddAbove Omega)
    (hq : ∀ q ∈ Omega, 1 < q) (A : ℝ → Fin 10 → ℝ)
    (D : ∀ q : Omega, SourceData218 A2 A3 L hL q.val (hq q.val q.property) c2 c3 (A q.val) delta) :
    let hA2 : IsUnit A2 := (Matrix.isUnit_iff_isUnit_det A2).mpr (by rw [h2d]; exact isUnit_one)
    let hA3 : IsUnit A3 := (Matrix.isUnit_iff_isUnit_det A3).mpr (by rw [h3d]; exact isUnit_one)
    ∃ S0 : Finset (Fin 3 → Fin 10), S0.Nonempty ∧ ∃ B : ℝ, 6 < B ∧
      ∃ U : Set ℝ, U ⊆ Omega ∧ ¬ BddAbove U ∧
        ∃ q1 : Omega, q1.val ∈ U ∧ B < q1.val ∧
          ∃ (v0 : Fin 10 → ℤ) (hv0 : v0 ≠ 0), v0 = integerLastDual10 (D q1).u ∧
            (∀ s ∈ S0, mixedProduct10 A2 A3 L v0 s = 0) ∧
            (∀ q : Omega, q.val ∈ U → sourceSet218 q.val delta (A q.val) c2 c3 = S0) ∧
            ∃ C : ℤ, 0 < C ∧ ∃ t : ℝ → ℤ,
              (∀ q, t q = C*2^((9-floorMin234 2 A2 hA2 q c2 v0 hv0).toNat)*
                3^((9-floorMin234 3 A3 hA3 q c3 v0 hv0).toNat)) ∧
              ∀ q ∈ U, B < q → t q ≠ 0 ∧
                (fun i => (((t q) • v0) i : ℚ)) ∈ scaledDual219
                  (originalSourceGroup10 A2 A3 q c2 c3) := by
  intro hA2 hA3
  obtain ⟨S0,hS0,B,hB,U,hUO,hU,q1,hq1U,hq1B,v0,hveq,hv0,hzero,hpattern⟩ :=
    source_fixed_reference234 A2 A3 L h2d h3d hLd hL hAlg c2 c3 h2 h3
      delta hd Omega hO hq A D
  obtain ⟨C,hC,hm⟩ := fixed_rescale_mem234 A2 A3 hA2 hA3 v0 hv0
  let t : ℝ → ℤ := fun q => C*2^((9-floorMin234 2 A2 hA2 q c2 v0 hv0).toNat)*
    3^((9-floorMin234 3 A3 hA3 q c3 v0 hv0).toNat)
  refine ⟨S0,hS0,B,hB,U,hUO,hU,q1,hq1U,hq1B,v0,hv0,hveq,hzero,hpattern,
    C,hC,t,fun _ => rfl,?_⟩
  intro q hqU _
  exact hm q (hq q (hUO hqU)) c2 c3 (fun i => (h2 i).2) (fun i => (h3 i).2)

end CompoundFeasibility.SourceFixedArithmetic234
