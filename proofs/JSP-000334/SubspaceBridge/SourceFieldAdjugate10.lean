import SubspaceBridge.SourceHeightUpper10
import SubspaceBridge.AlgebraicLiouville10
open scoped BigOperators Classical Matrix
noncomputable section
namespace CompoundFeasibility.SourceHeightEnvelope10

theorem mapped_adjugate10 (K : IntermediateField ℚ ℝ)
    (B : Matrix (Fin 10) (Fin 10) K) (L : Matrix (Fin 10) (Fin 10) ℝ)
    (hmap : B.map K.val.toRingHom = L) :
    B.adjugate.map K.val.toRingHom = L.adjugate := by
  have hh := K.val.toRingHom.map_adjugate B
  exact hh.trans (congrArg Matrix.adjugate hmap)

theorem mapped_transpose10 (K : IntermediateField ℚ ℝ)
    (B : Matrix (Fin 10) (Fin 10) K) :
    B.transpose.map K.val.toRingHom = (B.map K.val.toRingHom).transpose := by
  rfl

theorem number_field_adjugate_dual10 (K : IntermediateField ℚ ℝ)
    (B : Matrix (Fin 10) (Fin 10) K) (L : Matrix (Fin 10) (Fin 10) ℝ)
    (hmap : B.map K.val.toRingHom = L) (hL : L.det = 1) :
    B.adjugate.transpose.map K.val.toRingHom = L⁻¹.transpose := by
  rw [mapped_transpose10,mapped_adjugate10 K B L hmap,
    OriginalDual10.inverse_adjugate_fin10 L hL]

end CompoundFeasibility.SourceHeightEnvelope10
