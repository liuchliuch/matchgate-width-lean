import MatchgateWidth.AllLeftCapCoordinates
import MatchgateWidth.AllLeftScaffoldEndpointAreas
import MatchgateWidth.RoundCollarConnectorBank

/-! # Simultaneous actual connector banks for all primitive occurrences

Ordered source collar angles, signed physical lane coordinates and native
matching-graph external angles determine every bank. The physical inner disk
radius is uniformly r/4 even for nonunit local frames. One common positive
width works for all left and right occurrences, including nullary occurrences.
-/
namespace MatchgateWidth
noncomputable section
namespace AllLeftGadget.TransverseScaffold
variable {S : LabelledShape} {a b c n t : ℕ} {I : AllLeftGadget S a b c n}
    (K : I.TransverseScaffold)

/-- Fixed before selecting any common ribbon width. -/
def leftAngles (v : Fin a) := Classical.choice (K.left_cut_angles v)
def rightAngles (v : Fin b) := Classical.choice (K.right_cut_angles v)

theorem leftCutVector_norm (v : Fin a) (i : Fin (S.leftArity (I.leftLabel v))) :
    ‖K.ordered.leftCutVector K.indexed K.cutRadius v i‖ = 2*K.collars.radius := by
  have h := (K.indexed (I.leftIncidence ⟨v,i⟩)).radialSourceCut_dist K.cutRadius K.cutRadius_pos.le
  simpa [OrderedPlanar.leftCutVector,cutRadius,OrderedPlanar.primitiveCenter,AllLeftGadget.graph,
    dist_eq_norm] using h

theorem rightCutVector_norm (v : Fin b) (i : Fin (S.rightArity (I.rightLabel v))) :
    ‖K.ordered.rightCutVector K.indexed K.cutRadius v i‖ = 2*K.collars.radius := by
  have h := (K.indexed (Sum.inl (I.rightIncidence ⟨v,i⟩))).radialTargetCut_dist K.cutRadius K.cutRadius_pos.le
  simpa [OrderedPlanar.rightCutVector,cutRadius,OrderedPlanar.primitiveCenter,AllLeftGadget.graph,
    dist_eq_norm] using h

theorem left_local_area_positive (v : Fin a) (i : Fin (S.leftArity (I.leftLabel v))) :
    0 < orientedArea (K.ordered.leftCutVector K.indexed K.cutRadius v i) (K.leftTransverse v i) := by
  simpa [OrderedPlanar.leftCutVector,OrderedPlanar.primitiveCenter,AllLeftGadget.graph,leftTransverse]
    using K.source_area_positive (I.leftIncidence ⟨v,i⟩)

theorem right_local_area_negative (v : Fin b) (i : Fin (S.rightArity (I.rightLabel v))) :
    orientedArea (K.ordered.rightCutVector K.indexed K.cutRadius v i) (K.rightTransverse v i) < 0 := by
  simpa [OrderedPlanar.rightCutVector,OrderedPlanar.primitiveCenter,AllLeftGadget.graph,rightTransverse]
    using K.target_area_negative (Sum.inl (I.rightIncidence ⟨v,i⟩))

theorem left_signed_lane_order (v : Fin a) (i : Fin (S.leftArity (I.leftLabel v)))
    (j l : Fin t) (hjl : j < l) :
    0 < (K.leftCoefficients v i l-K.leftCoefficients v i j) *
      orientedArea (K.ordered.leftCutVector K.indexed K.cutRadius v i) (K.leftTransverse v i) :=
  mul_pos (sub_pos.mpr (TransversePolygonalRoute.laneOffset_strictMono (by norm_num : (0:ℝ)<1) t hjl))
    (K.left_local_area_positive v i)

theorem right_signed_lane_order (v : Fin b) (i : Fin (S.rightArity (I.rightLabel v)))
    (j l : Fin t) (hjl : j < l) :
    0 < (K.rightCoefficients v i l-K.rightCoefficients v i j) *
      orientedArea (K.ordered.rightCutVector K.indexed K.cutRadius v i) (K.rightTransverse v i) :=
  mul_pos_of_neg_of_neg
    (sub_neg.mpr (TransversePolygonalRoute.laneOffset_strictMono (by norm_num : (0:ℝ)<1) t
      (Fin.rev_lt_rev.mpr hjl))) (K.right_local_area_negative v i)

/-- The actual local graph similarity agrees exactly with the connector start. -/
def leftFactor (v : Fin a) : ℂ := (K.leftAngles v).collarFactor K.collars.radius
def rightFactor (v : Fin b) : ℂ := (K.rightAngles v).collarFactor K.collars.radius

theorem leftFactor_ne_zero (v : Fin a) : K.leftFactor v ≠ 0 :=
  (K.leftAngles v).collarFactor_ne_zero K.collars.positive

theorem rightFactor_ne_zero (v : Fin b) : K.rightFactor v ≠ 0 :=
  (K.rightAngles v).collarFactor_ne_zero K.collars.positive

theorem norm_leftFactor (v : Fin a) : ‖K.leftFactor v‖ = K.collars.radius/4 :=
  (K.leftAngles v).norm_collarFactor K.collars.positive

theorem norm_rightFactor (v : Fin b) : ‖K.rightFactor v‖ = K.collars.radius/4 :=
  (K.rightAngles v).norm_collarFactor K.collars.positive

abbrev LeftBank (L : I.LeftMatchingFamily (t := t)) (hL : L.DiskDrawn) (ε : ℝ) (v : Fin a) :=
  LocalConnectorBank (K.ordered.primitiveCenter (Sum.inl v)) (K.leftAngles v).rotation
    (K.collars.radius/(4*‖(K.leftAngles v).rotation‖)) (3*K.collars.radius/‖(K.leftAngles v).rotation‖)
    (L.nativeDrawing hL v).angle
    ((K.leftAngles v).blockEndpoint (K.leftTransverse v) (K.leftCoefficients v) ε)

abbrev RightBank (R : I.RightMatchingFamily (t := t)) (hR : R.DiskDrawn) (ε : ℝ) (v : Fin b) :=
  LocalConnectorBank (K.ordered.primitiveCenter (Sum.inr v)) (K.rightAngles v).rotation
    (K.collars.radius/(4*‖(K.rightAngles v).rotation‖)) (3*K.collars.radius/‖(K.rightAngles v).rotation‖)
    (R.nativeDrawing hR v).angle
    ((K.rightAngles v).blockEndpoint (K.rightTransverse v) (K.rightCoefficients v) ε)

/-- The whole finite source gadget has actual native-order connector banks at
one common width, with formulas needed for uniform cross-stage perturbation. -/
theorem exists_uniform_local_banks
    (L : I.LeftMatchingFamily (t := t)) (R : I.RightMatchingFamily (t := t))
    (hL : L.DiskDrawn) (hR : R.DiskDrawn) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε, 0 < ε → ε < ε₀ →
      ∃ (BL : ∀ v, K.LeftBank L hL ε v) (BR : ∀ v, K.RightBank R hR ε v),
        (∀ v q u, (BL v).path q u = (K.leftAngles v).localBlockConnector
          (K.ordered.primitiveCenter (Sum.inl v)) (K.leftTransverse v) (K.leftCoefficients v)
          (L.nativeDrawing hL v).angle (K.collars.radius/(4*‖(K.leftAngles v).rotation‖))
          (K.collars.radius/(2*‖(K.leftAngles v).rotation‖)) ε q u) ∧
        (∀ v q u, (BR v).path q u = (K.rightAngles v).localBlockConnector
          (K.ordered.primitiveCenter (Sum.inr v)) (K.rightTransverse v) (K.rightCoefficients v)
          (R.nativeDrawing hR v).angle (K.collars.radius/(4*‖(K.rightAngles v).rotation‖))
          (K.collars.radius/(2*‖(K.rightAngles v).rotation‖)) ε q u) := by
  classical
  have hexL (v : Fin a) := (K.leftAngles v).exists_roundCollarBank
    (K.ordered.primitiveCenter (Sum.inl v)) K.collars.radius K.collars.positive
    (K.leftCutVector_norm v) (K.leftTransverse v) (K.leftCoefficients v)
    (K.left_signed_lane_order v) (L.nativeDrawing hL v).angle
    (L.nativeDrawing hL v).angle_strictMono (L.nativeDrawing hL v).angle_pos
    (L.nativeDrawing hL v).angle_lt_one
  have hexR (v : Fin b) := (K.rightAngles v).exists_roundCollarBank
    (K.ordered.primitiveCenter (Sum.inr v)) K.collars.radius K.collars.positive
    (K.rightCutVector_norm v) (K.rightTransverse v) (K.rightCoefficients v)
    (K.right_signed_lane_order v) (R.nativeDrawing hR v).angle
    (R.nativeDrawing hR v).angle_strictMono (R.nativeDrawing hR v).angle_pos
    (R.nativeDrawing hR v).angle_lt_one
  choose εL hεL hbankL using hexL
  choose εR hεR hbankR using hexR
  obtain ⟨ε₀,hε₀,hsmall⟩ := finite_positive_lower_bound (Sum.elim εL εR)
    (by rintro (v|v); exact hεL v; exact hεR v)
  refine ⟨ε₀,hε₀,?_⟩
  intro ε hε hεlt
  choose BL hBL using fun v => hbankL v ε hε (hεlt.trans_le (hsmall (Sum.inl v)))
  choose BR hBR using fun v => hbankR v ε hε (hεlt.trans_le (hsmall (Sum.inr v)))
  exact ⟨BL,BR,hBL,hBR⟩

end AllLeftGadget.TransverseScaffold
end
end MatchgateWidth
