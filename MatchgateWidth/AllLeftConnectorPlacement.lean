import MatchgateWidth.AllLeftConnectorFamilies
import MatchgateWidth.AllLeftOuterAccessBank

/-! # Concrete placed graphs and mapped local connector paths

Every connector starts at the literal external vertex in the occurrence's
inserted matching graph and ends at the literal physical corridor cap.
All native local and cross-occurrence connector separation is derived.
-/
namespace MatchgateWidth
noncomputable section
namespace AllLeftGadget.TransverseScaffold
variable {S : LabelledShape} {a b c n t : ℕ} {I : AllLeftGadget S a b c n}
    (K : I.TransverseScaffold)

/-- Actual independently drawn local graphs in the selected common collars. -/
def leftDrawings (L : I.LeftMatchingFamily (t := t)) (hL : L.DiskDrawn) :=
  K.ordered.placedLeft L hL K.leftFactor K.leftFactor_ne_zero

def rightDrawings (R : I.RightMatchingFamily (t := t)) (hR : R.DiskDrawn) :=
  K.ordered.placedRight R hR K.rightFactor K.rightFactor_ne_zero

/-- Radius-three primitive disks are pairwise disjoint, derived from collars. -/
theorem primitive_three_disjoint : Pairwise (fun u v : Fin a ⊕ Fin b =>
    Disjoint (Metric.closedBall (K.ordered.primitiveCenter u) (3*K.collars.radius))
      (Metric.closedBall (K.ordered.primitiveCenter v) (3*K.collars.radius))) := by
  intro u v huv
  exact (K.collars.disks_disjoint (fun h => huv (Sum.inl_injective h))).mono
    (Metric.closedBall_subset_closedBall (by linarith [K.collars.positive]))
    (Metric.closedBall_subset_closedBall (by linarith [K.collars.positive]))

def leftCarriers (L : I.LeftMatchingFamily (t := t)) (hL : L.DiskDrawn) :
    PlaneDrawing.FamilyCarriers (K.leftDrawings L hL) :=
  L.insertedCarriers hL (fun v => K.ordered.primitiveCenter (Sum.inl v)) K.leftFactor
    K.leftFactor_ne_zero (by
      intro v w hvw
      rw [K.norm_leftFactor,K.norm_leftFactor]
      exact (K.primitive_three_disjoint (fun h => hvw (Sum.inl_injective h))).mono
        (Metric.closedBall_subset_closedBall (by linarith [K.collars.positive]))
        (Metric.closedBall_subset_closedBall (by linarith [K.collars.positive])))

def rightCarriers (R : I.RightMatchingFamily (t := t)) (hR : R.DiskDrawn) :
    PlaneDrawing.FamilyCarriers (K.rightDrawings R hR) :=
  R.insertedCarriers hR (fun v => K.ordered.primitiveCenter (Sum.inr v)) K.rightFactor
    K.rightFactor_ne_zero (by
      intro v w hvw
      rw [K.norm_rightFactor,K.norm_rightFactor]
      exact (K.primitive_three_disjoint (fun h => hvw (Sum.inr_injective h))).mono
        (Metric.closedBall_subset_closedBall (by linarith [K.collars.positive]))
        (Metric.closedBall_subset_closedBall (by linarith [K.collars.positive])))

theorem carriers_cross (L : I.LeftMatchingFamily (t := t)) (R : I.RightMatchingFamily (t := t))
    (hL : L.DiskDrawn) (hR : R.DiskDrawn) (v : Fin a) (w : Fin b) :
    Disjoint ((K.leftCarriers L hL).carrier v) ((K.rightCarriers R hR).carrier w) := by
  change Disjoint (Metric.closedBall _ ‖K.leftFactor v‖) (Metric.closedBall _ ‖K.rightFactor w‖)
  rw [K.norm_leftFactor,K.norm_rightFactor]
  exact (K.primitive_three_disjoint (by simp : (Sum.inl v : Fin a ⊕ Fin b) ≠ Sum.inr w)).mono
    (Metric.closedBall_subset_closedBall (by linarith [K.collars.positive]))
    (Metric.closedBall_subset_closedBall (by linarith [K.collars.positive]))

/-- The exact graph-vertex and cap endpoints, before choosing an internal or
exposed source wire. Path casting does not change any geometric trace. -/
def leftConnector (L : I.LeftMatchingFamily (t := t)) (hL : L.DiskDrawn) {ε : ℝ}
    (BL : ∀ v, K.LeftBank L hL ε v) (q : Σ v : Fin a, Fin (S.leftArity (I.leftLabel v)*t)) :
    Path ((K.leftDrawings L hL q.1).vertex (L.external q.1 q.2)) (K.leftCap ε q) :=
  ((BL q.1).path q.2).cast (by
    rw [show (K.leftDrawings L hL q.1).vertex (L.external q.1 q.2) =
      K.ordered.primitiveCenter (Sum.inl q.1) + K.leftFactor q.1 *
        boundaryPoint ((L.nativeDrawing hL q.1).angle q.2) from L.inserted_external hL (fun v => K.ordered.primitiveCenter (Sum.inl v))
          K.leftFactor K.leftFactor_ne_zero q.1 q.2]
    simp only [leftFactor,OrderedRayAngles.collarFactor,mul_assoc])
    (K.leftCap_eq_blockEndpoint ε q.1 (K.leftAngles q.1) q.2)

def rightConnector (R : I.RightMatchingFamily (t := t)) (hR : R.DiskDrawn) {ε : ℝ}
    (BR : ∀ v, K.RightBank R hR ε v) (q : Σ v : Fin b, Fin (S.rightArity (I.rightLabel v)*t)) :
    Path ((K.rightDrawings R hR q.1).vertex (R.external q.1 q.2)) (K.rightCap ε q) :=
  ((BR q.1).path q.2).cast (by
    rw [show (K.rightDrawings R hR q.1).vertex (R.external q.1 q.2) =
      K.ordered.primitiveCenter (Sum.inr q.1) + K.rightFactor q.1 *
        boundaryPoint ((R.nativeDrawing hR q.1).angle q.2) from R.inserted_external hR (fun v => K.ordered.primitiveCenter (Sum.inr v))
          K.rightFactor K.rightFactor_ne_zero q.1 q.2]
    simp only [rightFactor,OrderedRayAngles.collarFactor,mul_assoc])
    (K.rightCap_eq_blockEndpoint ε q.1 (K.rightAngles q.1) q.2)

theorem leftConnector_simple (L : I.LeftMatchingFamily (t := t)) (hL : L.DiskDrawn) {ε : ℝ}
    (BL : ∀ v, K.LeftBank L hL ε v) (q) : Function.Injective (K.leftConnector L hL BL q) :=
  (BL q.1).simple q.2

theorem rightConnector_simple (R : I.RightMatchingFamily (t := t)) (hR : R.DiskDrawn) {ε : ℝ}
    (BR : ∀ v, K.RightBank R hR ε v) (q) : Function.Injective (K.rightConnector R hR BR q) :=
  (BR q.1).simple q.2

theorem leftConnector_bound (L : I.LeftMatchingFamily (t := t)) (hL : L.DiskDrawn) {ε : ℝ}
    (BL : ∀ v, K.LeftBank L hL ε v) (q) (u : unitInterval) :
    dist (K.leftConnector L hL BL q u) (K.ordered.primitiveCenter (Sum.inl q.1)) ≤ 3*K.collars.radius :=
  (K.leftAngles q.1).roundCollarBank_bound _ _ _ _ (BL q.1) q.2 u

theorem rightConnector_bound (R : I.RightMatchingFamily (t := t)) (hR : R.DiskDrawn) {ε : ℝ}
    (BR : ∀ v, K.RightBank R hR ε v) (q) (u : unitInterval) :
    dist (K.rightConnector R hR BR q u) (K.ordered.primitiveCenter (Sum.inr q.1)) ≤ 3*K.collars.radius :=
  (K.rightAngles q.1).roundCollarBank_bound _ _ _ _ (BR q.1) q.2 u

theorem leftConnectors_disjoint (L : I.LeftMatchingFamily (t := t)) (hL : L.DiskDrawn) {ε : ℝ}
    (BL : ∀ v, K.LeftBank L hL ε v) : Pairwise (fun q s =>
      Disjoint (Set.range (K.leftConnector L hL BL q)) (Set.range (K.leftConnector L hL BL s))) := by
  rintro ⟨v,i⟩ ⟨w,j⟩ hne
  by_cases hvw : v = w
  · subst w
    exact (BL v).disjoint (fun hij => hne (congrArg (Sigma.mk v) hij))
  · exact (K.primitive_three_disjoint (fun h => hvw (Sum.inl_injective h))).mono
      (by rintro z ⟨u,rfl⟩; exact K.leftConnector_bound L hL BL ⟨v,i⟩ u)
      (by rintro z ⟨u,rfl⟩; exact K.leftConnector_bound L hL BL ⟨w,j⟩ u)

theorem rightConnectors_disjoint (R : I.RightMatchingFamily (t := t)) (hR : R.DiskDrawn) {ε : ℝ}
    (BR : ∀ v, K.RightBank R hR ε v) : Pairwise (fun q s =>
      Disjoint (Set.range (K.rightConnector R hR BR q)) (Set.range (K.rightConnector R hR BR s))) := by
  rintro ⟨v,i⟩ ⟨w,j⟩ hne
  by_cases hvw : v = w
  · subst w
    exact (BR v).disjoint (fun hij => hne (congrArg (Sigma.mk v) hij))
  · exact (K.primitive_three_disjoint (fun h => hvw (Sum.inr_injective h))).mono
      (by rintro z ⟨u,rfl⟩; exact K.rightConnector_bound R hR BR ⟨v,i⟩ u)
      (by rintro z ⟨u,rfl⟩; exact K.rightConnector_bound R hR BR ⟨w,j⟩ u)

theorem connectors_cross_disjoint (L : I.LeftMatchingFamily (t := t)) (R : I.RightMatchingFamily (t := t))
    (hL : L.DiskDrawn) (hR : R.DiskDrawn) {ε : ℝ}
    (BL : ∀ v, K.LeftBank L hL ε v) (BR : ∀ v, K.RightBank R hR ε v) (q) (s) :
    Disjoint (Set.range (K.leftConnector L hL BL q)) (Set.range (K.rightConnector R hR BR s)) :=
  (K.primitive_three_disjoint (by simp : (Sum.inl q.1 : Fin a ⊕ Fin b) ≠ Sum.inr s.1)).mono
    (by rintro z ⟨u,rfl⟩; exact K.leftConnector_bound L hL BL q u)
    (by rintro z ⟨u,rfl⟩; exact K.rightConnector_bound R hR BR s u)

end AllLeftGadget.TransverseScaffold
end
end MatchgateWidth
