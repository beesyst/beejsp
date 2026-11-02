import SubspaceBridge.SourceExterior54Cofactor246
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.Exterior54_246

theorem compound_map4246 {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (A : Matrix (Fin 5) (Fin 5) R) :
    (compound4246 A).map f = compound4246 (A.map f) := by
  have ha : A.adjugate.map f = (A.map f).adjugate := f.map_adjugate A
  simpa only [compound4246, Matrix.transpose_map] using congrArg Matrix.transpose ha

theorem wedge_map4246 {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (x : Fin 4 → Fin 5 → R) :
    (fun i => f (wedge4246 x i)) = wedge4246 (fun j k => f (x j k)) := by
  have hm : (Matrix.of (Fin.snoc x 0)).map f =
      Matrix.of (Fin.snoc (fun j k => f (x j k)) 0) := by
    ext i k
    refine Fin.lastCases ?_ (fun j => ?_) i
    · change f 0 = 0
      exact f.map_zero
    · simp only [Matrix.map_apply, Matrix.of_apply, Fin.snoc_castSucc]
  funext i
  change ((Matrix.of (Fin.snoc x 0)).adjugate.map f) i 4 = _
  have ha : (Matrix.of (Fin.snoc x 0)).adjugate.map f =
      ((Matrix.of (Fin.snoc x 0)).map f).adjugate := f.map_adjugate _
  rw [ha, hm]
  rfl

end CompoundFeasibility.Exterior54_246
