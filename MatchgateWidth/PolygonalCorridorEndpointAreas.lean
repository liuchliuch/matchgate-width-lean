import MatchgateWidth.IndexedPolygonalRadialTrimming
import MatchgateWidth.PolygonalRibbonAssembly

/-! # Derived signed endpoint areas for actual radial-trimmed corridors -/
namespace MatchgateWidth
noncomputable section

@[simp] theorem orientedArea_smul_left (t : ℝ) (x y : ℂ) :
    orientedArea (t•x) y = t*orientedArea x y := by
  simp only [orientedArea,Complex.smul_re,Complex.smul_im,smul_eq_mul]
  ring

@[simp] theorem orientedArea_neg_left (x y : ℂ) :
    orientedArea (-x) y = -orientedArea x y := by
  simp [orientedArea]
  ring

namespace IndexedSimplePolygonalRoute
variable {U : Set ℂ} {x y : ℂ} (R : IndexedSimplePolygonalRoute U x y)

/-- Positive transversality of the first trimmed edge gives positive area
relative to the original outward source-cut ray. -/
theorem trimmed_source_area_positive (δ : ℝ) (hδ : 0<δ)
    (hfirst : 3*δ<‖R.vertex R.firstEdge.succ-R.vertex R.firstEdge.castSucc‖)
    (hlast : 3*δ<‖R.vertex R.lastEdge.succ-R.vertex R.lastEdge.castSucc‖)
    (T : TransversePolygonalRoute R.edgeCount)
    (hv : T.vertex=(R.trimAtRadius δ hδ hfirst hlast).vertex) :
    0<orientedArea (R.radialSourceCut δ-x) (T.transverse 0) := by
  have hp := T.start_positive R.firstEdge
  rw [hv] at hp
  change 0<orientedArea
    ((R.trimAtRadius δ hδ hfirst hlast).vertex (R.trimAtRadius δ hδ hfirst hlast).firstEdge.succ-
      (R.trimAtRadius δ hδ hfirst hlast).vertex (R.trimAtRadius δ hδ hfirst hlast).firstEdge.castSucc)
    (T.transverse 0) at hp
  rw [R.trimAtRadius_first_difference,orientedArea_smul_left] at hp
  have hbase := (mul_pos_iff_of_pos_left (R.radialTrimCoefficient_pos δ _ hδ hfirst)).mp hp
  have hn : 0<‖R.vertex R.firstEdge.succ-R.vertex R.firstEdge.castSucc‖ := by linarith
  have hcut : R.radialSourceCut δ-x=
      (δ/‖R.vertex R.firstEdge.succ-R.vertex R.firstEdge.castSucc‖)•
        (R.vertex R.firstEdge.succ-R.vertex R.firstEdge.castSucc) := by
    simp only [radialSourceCut,radialSegmentCut,R.firstEdge_castSucc,R.source,add_sub_cancel_left]
  rw [hcut,orientedArea_smul_left]
  exact mul_pos (div_pos hδ hn) hbase

/-- At the target the original outward cut ray points opposite the final
forward edge. Its signed transverse area is therefore strictly negative. -/
theorem trimmed_target_area_negative (δ : ℝ) (hδ : 0<δ)
    (hfirst : 3*δ<‖R.vertex R.firstEdge.succ-R.vertex R.firstEdge.castSucc‖)
    (hlast : 3*δ<‖R.vertex R.lastEdge.succ-R.vertex R.lastEdge.castSucc‖)
    (T : TransversePolygonalRoute R.edgeCount)
    (hv : T.vertex=(R.trimAtRadius δ hδ hfirst hlast).vertex) :
    orientedArea (R.radialTargetCut δ-y) (T.transverse (Fin.last R.edgeCount))<0 := by
  have hp := T.end_positive R.lastEdge
  rw [hv] at hp
  change 0<orientedArea
    ((R.trimAtRadius δ hδ hfirst hlast).vertex (R.trimAtRadius δ hδ hfirst hlast).lastEdge.succ-
      (R.trimAtRadius δ hδ hfirst hlast).vertex (R.trimAtRadius δ hδ hfirst hlast).lastEdge.castSucc)
    (T.transverse R.lastEdge.succ) at hp
  rw [R.lastEdge_succ,R.trimAtRadius_last_difference,orientedArea_smul_left] at hp
  have hbase := (mul_pos_iff_of_pos_left (R.radialTrimCoefficient_pos δ _ hδ hlast)).mp hp
  have hn : 0<‖R.vertex R.lastEdge.succ-R.vertex R.lastEdge.castSucc‖ := by linarith
  have hcut : R.radialTargetCut δ-y=
      -(δ/‖R.vertex R.lastEdge.succ-R.vertex R.lastEdge.castSucc‖)•
        (R.vertex R.lastEdge.succ-R.vertex R.lastEdge.castSucc) := by
    simp only [radialTargetCut,radialSegmentCut,R.lastEdge_succ,R.target,add_sub_cancel_left,norm_sub_rev]
    module
  rw [hcut,orientedArea_smul_left]
  exact mul_neg_of_neg_of_pos (neg_neg_of_pos (div_pos hδ hn)) hbase

end IndexedSimplePolygonalRoute

/-- An inward target-cut ray has negative area while its boundary-centered
position vector has positive area, provided the cut remains inside radius one. -/
theorem radial_target_global_area_positive {z w : ℂ} {δ : ℝ}
    (hδ : 0<δ) (hδ1 : δ<1)
    (hneg : orientedArea ((1-δ)•z-z) w<0) :
    0<orientedArea ((1-δ)•z) w := by
  have heq : (1-δ)•z-z=(-δ)•z := by module
  rw [heq,orientedArea_smul_left] at hneg
  have hb : 0<orientedArea z w := by nlinarith
  rw [orientedArea_smul_left]
  exact mul_pos (sub_pos.mpr hδ1) hb

end
end MatchgateWidth
