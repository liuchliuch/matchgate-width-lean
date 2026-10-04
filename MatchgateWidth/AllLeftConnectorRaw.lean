import MatchgateWidth.AllLeftConnectorFamilies
import MatchgateWidth.AllLeftMiddlePieces
import MatchgateWidth.CollaredConnectorSeparation
import MatchgateWidth.ConnectorRibbonJoints

/-! # Literal source-indexed local connector curves and derived stage geometry -/
namespace MatchgateWidth
noncomputable section
set_option maxHeartbeats 600000

namespace OrderedRayAngles
variable {m : ℕ} {p : Fin m → ℂ} (A : OrderedRayAngles p)

theorem round_connector_parameters (r : ℝ) (hr : 0 < r)
    (hround : ∀ i, ‖p i‖ = 2*r) :
    0 < r/(4*‖A.rotation‖) ∧
    r/(4*‖A.rotation‖) < r/(2*‖A.rotation‖) ∧
    (∀ i, r/(2*‖A.rotation‖) < A.radius i) ∧
    ‖A.rotation‖*(r/(2*‖A.rotation‖)) = r/2 := by
  have hn : 0 < ‖A.rotation‖ := norm_pos_iff.mpr A.rotation_ne_zero
  refine ⟨div_pos hr (by positivity), ?_, ?_, ?_⟩
  · apply (div_lt_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith
  · intro i
    rw [A.radius_eq_of_round_cut hround i]
    apply (div_lt_div_iff₀ (by positivity) hn).mpr
    nlinarith
  · field_simp

end OrderedRayAngles

namespace AllLeftGadget.TransverseScaffold
variable {S : LabelledShape} {a b c n t : ℕ} {I : AllLeftGadget S a b c n}
    (K : I.TransverseScaffold)

def leftRaw (L : I.LeftMatchingFamily (t := t)) (hL : L.DiskDrawn) (v : Fin a)
    (q : Fin (S.leftArity (I.leftLabel v)*t)) (ε : ℝ) : unitInterval → ℂ :=
  (K.leftAngles v).localBlockConnector (K.ordered.primitiveCenter (Sum.inl v))
    (K.leftTransverse v) (K.leftCoefficients v) (L.nativeDrawing hL v).angle
    (K.collars.radius/(4*‖(K.leftAngles v).rotation‖))
    (K.collars.radius/(2*‖(K.leftAngles v).rotation‖)) ε q

def rightRaw (R : I.RightMatchingFamily (t := t)) (hR : R.DiskDrawn) (v : Fin b)
    (q : Fin (S.rightArity (I.rightLabel v)*t)) (ε : ℝ) : unitInterval → ℂ :=
  (K.rightAngles v).localBlockConnector (K.ordered.primitiveCenter (Sum.inr v))
    (K.rightTransverse v) (K.rightCoefficients v) (R.nativeDrawing hR v).angle
    (K.collars.radius/(4*‖(K.rightAngles v).rotation‖))
    (K.collars.radius/(2*‖(K.rightAngles v).rotation‖)) ε q

theorem leftRaw_continuousAt_zero (L : I.LeftMatchingFamily (t := t)) (hL : L.DiskDrawn)
    (v : Fin a) (q : Fin (S.leftArity (I.leftLabel v)*t)) (u : unitInterval) :
    ContinuousAt (fun z : ℝ × unitInterval => K.leftRaw L hL v q z.1 z.2) (0,u) :=
  (K.leftAngles v).localBlockConnector_continuousAt_zero _ _ _ _ _ _ q u

theorem rightRaw_continuousAt_zero (R : I.RightMatchingFamily (t := t)) (hR : R.DiskDrawn)
    (v : Fin b) (q : Fin (S.rightArity (I.rightLabel v)*t)) (u : unitInterval) :
    ContinuousAt (fun z : ℝ × unitInterval => K.rightRaw R hR v q z.1 z.2) (0,u) :=
  (K.rightAngles v).localBlockConnector_continuousAt_zero _ _ _ _ _ _ q u

theorem leftRaw_zero_continuous (L : I.LeftMatchingFamily (t := t)) (hL : L.DiskDrawn)
    (v : Fin a) (q : Fin (S.leftArity (I.leftLabel v)*t)) : Continuous (K.leftRaw L hL v q 0) := by
  unfold leftRaw
  have hlevel : Continuous (annularLevel
      (K.collars.radius/(4*‖(K.leftAngles v).rotation‖))
      (K.collars.radius/(2*‖(K.leftAngles v).rotation‖))) := by
    unfold annularLevel
    exact continuous_projIcc.comp (by fun_prop)
  unfold OrderedRayAngles.localBlockConnector affineBlend boundaryPoint circleMap
  fun_prop

theorem rightRaw_zero_continuous (R : I.RightMatchingFamily (t := t)) (hR : R.DiskDrawn)
    (v : Fin b) (q : Fin (S.rightArity (I.rightLabel v)*t)) : Continuous (K.rightRaw R hR v q 0) := by
  unfold rightRaw
  have hlevel : Continuous (annularLevel
      (K.collars.radius/(4*‖(K.rightAngles v).rotation‖))
      (K.collars.radius/(2*‖(K.rightAngles v).rotation‖))) := by
    unfold annularLevel
    exact continuous_projIcc.comp (by fun_prop)
  unfold OrderedRayAngles.localBlockConnector affineBlend boundaryPoint circleMap
  fun_prop

/-- Every non-adjoining original middle piece is genuinely disjoint from the
left connector's zero trace, as a consequence of source collars and incidence. -/
theorem leftRaw_zero_piece_disjoint (L : I.LeftMatchingFamily (t := t)) (hL : L.DiskDrawn)
    (v : Fin a) (q : Fin (S.leftArity (I.leftLabel v)*t)) (e : Fin c ⊕ Fin n)
    (k : Fin t) (j : Fin (K.indexed e).edgeCount)
    (haway : I.leftIncidence ⟨v,(finProdFinEquiv.symm q).1⟩ ≠ e ∨ j.val ≠ 0) :
    Disjoint (Set.range (K.leftRaw L hL v q 0)) (Set.range (K.middlePiece e k j 0)) := by
  let i := (finProdFinEquiv.symm q).1
  let f := I.leftIncidence ⟨v,i⟩
  have hc : K.ordered.drawing.vertex (I.graph.left f) = K.ordered.primitiveCenter (Sum.inl v) := by
    simp [f,AllLeftGadget.graph,OrderedPlanar.primitiveCenter]
  have hcut : K.ordered.drawing.vertex (I.graph.left f) +
      K.ordered.leftCutVector K.indexed K.cutRadius v i = (K.indexed f).radialSourceCut K.cutRadius := by
    calc
      _ = K.ordered.primitiveCenter (Sum.inl v) + K.ordered.leftCutVector K.indexed K.cutRadius v i :=
        congrArg (fun z => z + K.ordered.leftCutVector K.indexed K.cutRadius v i) hc
      _ = _ := by dsimp [OrderedPlanar.leftCutVector,f]; abel
  have hp := (K.leftAngles v).round_connector_parameters K.collars.radius K.collars.positive (K.leftCutVector_norm v)
  rw [K.middlePiece_zero_range]
  have h := K.collars.source_connector_piece_disjoint (K.leftAngles v) (K.leftTransverse v)
    (K.leftCoefficients v) (L.nativeDrawing hL v).angle _ _ hp.1 hp.2.1
    (fun i => (hp.2.2.1 i).le) q K.cutRadius K.cutRadius_pos
    (by dsimp [cutRadius]; linarith [K.collars.positive]) f e j hcut haway
  simpa only [hc,leftRaw,cutRadius] using h

/-- The target-side version, excluding only the final piece of its own edge. -/
theorem rightRaw_zero_piece_disjoint (R : I.RightMatchingFamily (t := t)) (hR : R.DiskDrawn)
    (v : Fin b) (q : Fin (S.rightArity (I.rightLabel v)*t)) (e : Fin c ⊕ Fin n)
    (k : Fin t) (j : Fin (K.indexed e).edgeCount)
    (haway : Sum.inl (I.rightIncidence ⟨v,(finProdFinEquiv.symm q).1⟩) ≠ e ∨
      j.val+1 ≠ (K.indexed e).edgeCount) :
    Disjoint (Set.range (K.rightRaw R hR v q 0)) (Set.range (K.middlePiece e k j 0)) := by
  let i := (finProdFinEquiv.symm q).1
  let f : Fin c ⊕ Fin n := Sum.inl (I.rightIncidence ⟨v,i⟩)
  have hc : K.ordered.drawing.vertex (I.graph.right f) = K.ordered.primitiveCenter (Sum.inr v) := by
    simp [f,AllLeftGadget.graph,OrderedPlanar.primitiveCenter]
  have hcut : K.ordered.drawing.vertex (I.graph.right f) +
      K.ordered.rightCutVector K.indexed K.cutRadius v i = (K.indexed f).radialTargetCut K.cutRadius := by
    calc
      _ = K.ordered.primitiveCenter (Sum.inr v) + K.ordered.rightCutVector K.indexed K.cutRadius v i :=
        congrArg (fun z => z + K.ordered.rightCutVector K.indexed K.cutRadius v i) hc
      _ = _ := by dsimp [OrderedPlanar.rightCutVector,f]; abel
  have hp := (K.rightAngles v).round_connector_parameters K.collars.radius K.collars.positive (K.rightCutVector_norm v)
  rw [K.middlePiece_zero_range]
  have h := K.collars.target_connector_piece_disjoint (K.rightAngles v) (K.rightTransverse v)
    (K.rightCoefficients v) (R.nativeDrawing hR v).angle _ _ hp.1 hp.2.1
    (fun i => (hp.2.2.1 i).le) q K.cutRadius K.cutRadius_pos
    (by dsimp [cutRadius]; linarith [K.collars.positive]) f e j hcut haway
  simpa only [hc,rightRaw,cutRadius] using h

/-- The actual local banks have a uniform radial tail window with a physical
head radius r/2; all middle corridors stay outside radius r. -/
theorem exists_uniform_connector_tails
    (L : I.LeftMatchingFamily (t := t)) (R : I.RightMatchingFamily (t := t))
    (hL : L.DiskDrawn) (hR : R.DiskDrawn) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε, |ε| < ε₀ →
      (∀ v q, RadialTailProperty (K.leftRaw L hL v q ε)
        (K.ordered.primitiveCenter (Sum.inl v))
        (K.leftCap ε ⟨v,q⟩ - K.ordered.primitiveCenter (Sum.inl v)) (K.collars.radius/2)) ∧
      (∀ v q, RadialTailProperty (K.rightRaw R hR v q ε)
        (K.ordered.primitiveCenter (Sum.inr v))
        (K.rightCap ε ⟨v,q⟩ - K.ordered.primitiveCenter (Sum.inr v)) (K.collars.radius/2)) := by
  classical
  have hexL (v : Fin a) := (K.leftAngles v).exists_radialTail_radius
    (K.ordered.primitiveCenter (Sum.inl v)) (K.leftTransverse v) (K.leftCoefficients v)
    (L.nativeDrawing hL v).angle _ _
    ((K.leftAngles v).round_connector_parameters K.collars.radius K.collars.positive (K.leftCutVector_norm v)).1
    ((K.leftAngles v).round_connector_parameters K.collars.radius K.collars.positive (K.leftCutVector_norm v)).2.1
    ((K.leftAngles v).round_connector_parameters K.collars.radius K.collars.positive (K.leftCutVector_norm v)).2.2.1
  have hexR (v : Fin b) := (K.rightAngles v).exists_radialTail_radius
    (K.ordered.primitiveCenter (Sum.inr v)) (K.rightTransverse v) (K.rightCoefficients v)
    (R.nativeDrawing hR v).angle _ _
    ((K.rightAngles v).round_connector_parameters K.collars.radius K.collars.positive (K.rightCutVector_norm v)).1
    ((K.rightAngles v).round_connector_parameters K.collars.radius K.collars.positive (K.rightCutVector_norm v)).2.1
    ((K.rightAngles v).round_connector_parameters K.collars.radius K.collars.positive (K.rightCutVector_norm v)).2.2.1
  choose ηL hηL hspecL using hexL
  choose ηR hηR hspecR using hexR
  obtain ⟨ε₀,hε₀,hmin⟩ := finite_positive_lower_bound (Sum.elim ηL ηR)
    (by rintro (v|v); exact hηL v; exact hηR v)
  refine ⟨ε₀,hε₀,?_⟩
  intro ε hε
  constructor
  · intro v q
    have h := hspecL v ε (hε.trans_le (hmin (Sum.inl v))) q
    have hp := (K.leftAngles v).round_connector_parameters K.collars.radius K.collars.positive (K.leftCutVector_norm v)
    rw [hp.2.2.2] at h
    rw [K.leftCap_eq_blockEndpoint ε v (K.leftAngles v) q,add_sub_cancel_left]
    exact h
  · intro v q
    have h := hspecR v ε (hε.trans_le (hmin (Sum.inr v))) q
    have hp := (K.rightAngles v).round_connector_parameters K.collars.radius K.collars.positive (K.rightCutVector_norm v)
    rw [hp.2.2.2] at h
    rw [K.rightCap_eq_blockEndpoint ε v (K.rightAngles v) q,add_sub_cancel_left]
    exact h

end AllLeftGadget.TransverseScaffold
end
end MatchgateWidth
