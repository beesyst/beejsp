import SubspaceBridge.SchlickeweiDualVanishing6
open scoped Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceRelativeIndex6
theorem integer_basis_det_eq_matrix_det
    {ι M : Type*} [Fintype ι] [DecidableEq ι] [AddCommGroup M]
    (c : Basis ι ℤ M) (u : ι → M) :
    c.det u = (c.toMatrix u).det := by
  exact Basis.det_apply c u

theorem integer_span_index_det
    {ι M : Type*} [Fintype ι] [DecidableEq ι] [AddCommGroup M]
    (c : Basis ι ℤ M) (u : ι → M) (hu : LinearIndependent ℤ u) :
    Finite (M ⧸ Submodule.span ℤ (Set.range u)) ∧
      (Submodule.span ℤ (Set.range u)).toAddSubgroup.index = (c.toMatrix u).det.natAbs ∧
      (c.toMatrix u).det ≠ 0 := by
  letI : Module.Free ℤ M := Module.Free.of_basis c
  letI : Module.Finite ℤ M := Module.Finite.of_basis c
  let N := Submodule.span ℤ (Set.range u)
  let e : M ≃+ N := by
    letI : Module ℤ N := N.module
    exact (c.equiv (Basis.span hu) (Equiv.refl _)).toAddEquiv
  have hfinite : Finite (M ⧸ N) :=
    Submodule.finiteQuotientOfFreeOfRankEq N e.toIntLinearEquiv.symm.finrank_eq
  have hcard : Nat.card (M ⧸ N) = (c.toMatrix u).det.natAbs := by
    have h := (Submodule.natAbs_det_basis_change c N (Basis.span hu)).symm

    have hspan :
        (Subtype.val ∘ (Basis.span hu : ι → N)) = u := by
      funext i
      exact Basis.span_apply hu i

    have he : (c.det (Subtype.val ∘ (Basis.span hu : ι → N))).natAbs =
        (c.det u).natAbs := congrArg (fun w : ι → M => (c.det w).natAbs) hspan
    have hd : (c.det u).natAbs = (c.toMatrix u).det.natAbs :=
      congrArg Int.natAbs (integer_basis_det_eq_matrix_det c u)
    exact h.trans (he.trans hd)
  refine ⟨hfinite, hcard, ?_⟩
  letI := hfinite
  have hpos := Nat.card_pos (α := M ⧸ N)
  rw [hcard] at hpos
  exact Int.natAbs_ne_zero.mp (ne_of_gt hpos)

theorem integer_span6_index_det
    {M : Type*} [AddCommGroup M]
    (c : Basis (Fin 6) ℤ M) (u : Fin 6 → M) (hu : LinearIndependent ℤ u) :
    Finite (M ⧸ Submodule.span ℤ (Set.range u)) ∧
      (Submodule.span ℤ (Set.range u)).toAddSubgroup.index = (c.toMatrix u).det.natAbs ∧
      (c.toMatrix u).det ≠ 0 :=
  integer_span_index_det c u hu

def frameRelativeIndex {n : ℕ} (G : AddSubgroup (Fin n → ℤ)) (u : Fin n → G) : ℕ :=
  (Submodule.span ℤ (Set.range u)).toAddSubgroup.index

theorem frameRelativeIndex_mul_index {n : ℕ}
    (G : AddSubgroup (Fin n → ℤ)) (c : Basis (Fin n) ℤ G) (u : Fin n → G)
    (hu : LinearIndependent ℤ u) :
    frameRelativeIndex G u * G.index =
      (Matrix.of (fun j => (u j : Fin n → ℤ))).det.natAbs := by
  obtain ⟨_, hJ, _⟩ := integer_span_index_det c u hu
  have hD := AddSubgroup.index_eq_natAbs_det (Pi.basisFun ℤ (Fin n)) G c
  let B : Matrix (Fin n) (Fin n) ℤ := fun i j => (c j : Fin n → ℤ) i
  have hmul : B * c.toMatrix u =
      (Matrix.of (fun j => (u j : Fin n → ℤ))).transpose := by
    ext i j
    have he := congrArg (fun x : G => (x : Fin n → ℤ) i) (c.sum_repr (u j))
    simpa [B, Matrix.mul_apply, Basis.toMatrix_apply, Finset.sum_apply,
      mul_comm] using he
  have hB : B.det.natAbs = G.index := by
    rw [hD, integer_basis_det_eq_matrix_det]
    rfl
  unfold frameRelativeIndex
  rw [hJ, ← hB, ← Int.natAbs_mul, mul_comm (c.toMatrix u).det,
    ← Matrix.det_mul, hmul, Matrix.det_transpose]

theorem frameRelativeIndex_pos {n : ℕ}
    (G : AddSubgroup (Fin n → ℤ)) (c : Basis (Fin n) ℤ G) (u : Fin n → G)
    (hu : LinearIndependent ℤ u) : 0 < frameRelativeIndex G u := by
  obtain ⟨_, hJ, hd⟩ := integer_span_index_det c u hu
  change 0 < (Submodule.span ℤ (Set.range u)).toAddSubgroup.index
  rw [hJ]
  exact Int.natAbs_pos.mpr hd

theorem frame_abs_det_covolume {n : ℕ}
    (G : AddSubgroup (Fin n → ℤ)) [IsZLattice ℝ (integerRealImage G)]
    (c : Basis (Fin n) ℤ G) (u : Fin n → G) (hu : LinearIndependent ℤ u) :
    |((Matrix.of (fun j => (u j : Fin n → ℤ))).det : ℝ)| =
      (frameRelativeIndex G u : ℝ) * ZLattice.covolume (integerRealImage G) := by
  rw [integerRealImage_covolume_index G c, ← Nat.cast_mul,
    frameRelativeIndex_mul_index G c u hu, Int.cast_natAbs, Int.cast_abs]

theorem frame_normalization6
    (G : AddSubgroup (Fin 6 → ℤ)) [IsZLattice ℝ (integerRealImage G)]
    (c : Basis (Fin 6) ℤ G) (u : Fin 6 → G)
    (hu : LinearIndependent ℝ (fun j => integerReal (u j : Fin 6 → ℤ))) :
    Finite (G ⧸ Submodule.span ℤ (Set.range u)) ∧
    0 < frameRelativeIndex G u ∧
    frameRelativeIndex G u * G.index =
      (Matrix.of (fun j => (u j : Fin 6 → ℤ))).det.natAbs ∧
    |((Matrix.of (fun j => (u j : Fin 6 → ℤ))).det : ℝ)| =
      (frameRelativeIndex G u : ℝ) * ZLattice.covolume (integerRealImage G) ∧
    (Matrix.of (fun j => (u j : Fin 6 → ℤ))).det ≠ 0 ∧
    0 < ZLattice.covolume (integerRealImage G) := by
  have huZ : LinearIndependent ℤ u :=
    LinearIndependent.of_comp (integerReal.comp G.subtype.toIntLinearMap)
      (hu.restrict_scalars' ℤ)
  have hdR : ((Matrix.of (fun j => (u j : Fin 6 → ℤ))).map (Int.castRingHom ℝ)).det ≠ 0 :=
    isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp
      (Matrix.linearIndependent_rows_iff_isUnit.mp hu))
  have hd : (Matrix.of (fun j => (u j : Fin 6 → ℤ))).det ≠ 0 := by
    intro h
    apply hdR
    rw [← integer_matrix_det_cast, h, Int.cast_zero]
  exact ⟨(integer_span6_index_det c u huZ).1, frameRelativeIndex_pos G c u huZ,
    frameRelativeIndex_mul_index G c u huZ, frame_abs_det_covolume G c u huZ, hd,
    ZLattice.covolume_pos (integerRealImage G) MeasureTheory.volume⟩

open SourceNormalIndex SourceReadiness6 SourceHeightBounds6 SourceNormalHeight SchlickeweiDualVanishing6

variable {A2 A3 : Matrix (Fin 4) (Fin 4) ℚ} {L : Matrix (Fin 4) (Fin 4) ℝ}
  {hL : IsUnit L} {c0 c2 c3 : Fin 4 → ℝ} {delta4 : ℝ} {V : Set ℝ}
  {hQV : ∀ q ∈ V, 1 < q}

theorem source_frame_normalization6
    (R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV) (q : V) :
    let G := directCompoundGroup42 A2 A3 q.val c2 c3
    let v : Matrix (Fin 6) (Fin 6) ℤ := Matrix.of (fun j => (R.w q j : Fin 6 → ℤ))
    Finite (G ⧸ Submodule.span ℤ (Set.range (R.w q))) ∧
    0 < frameRelativeIndex G (R.w q) ∧
    frameRelativeIndex G (R.w q) * G.index = v.det.natAbs ∧
    |(v.det : ℝ)| = (frameRelativeIndex G (R.w q) : ℝ) *
      ZLattice.covolume (integerRealImage G) ∧
    v.det ≠ 0 ∧ 0 < ZLattice.covolume (integerRealImage G) := by
  obtain ⟨c⟩ := directCompoundGroup42_has_basis A2 A3 q.val c2 c3
  exact frame_normalization6 _ c (R.w q) (R.frames q).1

theorem source_signed_minors6
    (R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV) (q : V) :
    let v : Matrix (Fin 6) (Fin 6) ℤ := Matrix.of (fun j => (R.w q j : Fin 6 → ℤ))
    let g : ℤ := ∑ k, R.a q k * rawNormal6 v k
    g ≠ 0 ∧ (∀ k, rawNormal6 v k = g * R.M q k) ∧
      actualTransformedCofactors6 A2 A3 L v (R.M q) (R.a q) := by
  have hm := R.minors q
  exact ⟨hm.1.2.1, hm.1.2.2.1, hm.2⟩

theorem source_index_covolume_cofactors6
    (R : SourceReadiness42 A2 A3 L hL c0 c2 c3 delta4 V hQV) (q : V) :
    let G := directCompoundGroup42 A2 A3 q.val c2 c3
    let Q := q.val ^ (11 : ℕ)
    let v : Matrix (Fin 6) (Fin 6) ℤ := Matrix.of (fun j => (R.w q j : Fin 6 → ℤ))
    let g : ℤ := ∑ k, R.a q k * rawNormal6 v k
    directCompoundGroup42 A2 A3 Q (fun i => c2 i / 11) (fun i => c3 i / 11) = G ∧
    sourceFrames6 A2 A3 L hL c0 c2 c3 V hQV R.delta R.c R.sigma R.widths_pos R.w q ∧
    sourceNormals6 A2 A3 c2 c3 V R.w R.M R.a q ∧
    Finite (G ⧸ Submodule.span ℤ (Set.range (R.w q))) ∧
    0 < frameRelativeIndex G (R.w q) ∧
    frameRelativeIndex G (R.w q) * G.index = v.det.natAbs ∧
    |(v.det : ℝ)| = (frameRelativeIndex G (R.w q) : ℝ) *
      ZLattice.covolume (integerRealImage G) ∧
    v.det ≠ 0 ∧ 0 < ZLattice.covolume (integerRealImage G) ∧
    g ≠ 0 ∧ (∀ k, rawNormal6 v k = g * R.M q k) ∧
    minorNormalization6 v (R.M q) (R.a q) ∧
    actualTransformedCofactors6 A2 A3 L v (R.M q) (R.a q) ∧
    ∃ b : ℚ, b ≠ 0 ∧
      normalForm6 (R.M q) = b • rationalFrameDual42
        (fun j i => ((R.w q j : Fin 6 → ℤ) i : ℚ)) (sourceFrameIndependent6 R q) 5 ∧
      (∀ k, (R.M q k : ℚ) = b * dualVector6
        (fun j => (R.w q j : Fin 6 → ℤ)) (sourceFrameIndependent6 R q) k) ∧
      (∀ k, dualVector6 (fun j => (R.w q j : Fin 6 → ℤ))
        (sourceFrameIndependent6 R q) k = b⁻¹ * (R.M q k : ℚ)) := by
  have hn := source_frame_normalization6 R q
  have hm := source_signed_minors6 R q
  exact ⟨(R.frames q).2.2.1, R.frames q, R.normals q,
    hn.1, hn.2.1, hn.2.2.1, hn.2.2.2.1, hn.2.2.2.2.1, hn.2.2.2.2.2,
    hm.1, hm.2.1, (R.minors q).1, hm.2.2, source_normal_dual6 R q⟩

end CompoundFeasibility.SourceRelativeIndex6
