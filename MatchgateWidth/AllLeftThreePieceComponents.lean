import MatchgateWidth.AllLeftMiddleBank
import MatchgateWidth.ThreePieceWireRouting

/-! # Exact components for simultaneous internal and external wire assembly

All scalar source edges are treated in one finite index set. Internal paths
end at the right matching graph; external paths end at the surrounding circle.
The three-stage construction therefore gives internal/external disjointness
in one operation, preserving the actual inherited boundary positions.
-/
namespace MatchgateWidth
noncomputable section
namespace AllLeftGadget.TransverseScaffold
variable {S : LabelledShape} {a b c n t : ℕ} {I : AllLeftGadget S a b c n}
    (K : I.TransverseScaffold)

/-- Full geometric start point, retaining the concrete local graph vertex. -/
def allSource (L : I.LeftMatchingFamily (t := t)) (hL : L.DiskDrawn)
    (w : (Fin c ⊕ Fin n) × Fin t) : ℂ :=
  let q := I.leftWireEquiv w
  (K.leftDrawings L hL q.1).vertex (L.external q.1 q.2)

/-- Internal targets are literal right graph vertices; external targets use
exactly the global native-order angles of the derived outer access bank. -/
def allTarget (R : I.RightMatchingFamily (t := t)) (hR : R.DiskDrawn) {ε : ℝ}
    (B : K.OuterAccessBank (t := t) ε) (w : (Fin c ⊕ Fin n) × Fin t) : ℂ :=
  match w.1 with
  | Sum.inl e =>
    let q := I.rightWireEquiv (e,w.2)
    (K.rightDrawings R hR q.1).vertex (R.external q.1 q.2)
  | Sum.inr p => (2:ℂ)*boundaryPoint (B.angle (finProdFinEquiv (p,w.2)))

theorem leftCap_equiv (ε : ℝ) (w : (Fin c ⊕ Fin n) × Fin t) :
    K.leftCap ε (I.leftWireEquiv w) =
      (K.route w.1).laneVertex (physicalLaneOffset ε w.1 w.2) 0 :=
  congrArg (fun z : (Fin c ⊕ Fin n) × Fin t =>
    (K.route z.1).laneVertex (physicalLaneOffset ε z.1 z.2) ⟨0,Nat.zero_lt_succ _⟩)
    (I.leftWireEquiv.symm_apply_apply w)

theorem rightCap_equiv (ε : ℝ) (e : Fin c) (k : Fin t) :
    K.rightCap ε (I.rightWireEquiv (e,k)) =
      (K.route (Sum.inl e)).laneVertex (physicalLaneOffset ε (Sum.inl e : Fin c ⊕ Fin n) k)
        (Fin.last (K.indexed (Sum.inl e)).edgeCount) :=
  congrArg (fun z : Fin c × Fin t =>
    (K.route (Sum.inl z.1)).laneVertex (physicalLaneOffset ε (Sum.inl z.1 : Fin c ⊕ Fin n) z.2)
      (Fin.last (K.indexed (Sum.inl z.1)).edgeCount)) (I.rightWireEquiv.symm_apply_apply (e,k))

def allMiddle {ε : ℝ} (M : K.MiddleBank (t := t) ε) (w : (Fin c ⊕ Fin n) × Fin t) :
    Path (K.leftCap ε (I.leftWireEquiv w))
      ((K.route w.1).laneVertex (physicalLaneOffset ε w.1 w.2) (Fin.last (K.indexed w.1).edgeCount)) :=
  (M.path w.1 w.2).cast (K.leftCap_equiv ε w) rfl

/-- The right piece is outgoing from a right graph, or incoming from the
outer circle. The final wire will traverse this piece backwards. -/
def allRight (R : I.RightMatchingFamily (t := t)) (hR : R.DiskDrawn) {ε : ℝ}
    (BR : ∀ v, K.RightBank R hR ε v) (B : K.OuterAccessBank (t := t) ε)
    (w : (Fin c ⊕ Fin n) × Fin t) :
    Path (K.allTarget R hR B w)
      ((K.route w.1).laneVertex (physicalLaneOffset ε w.1 w.2) (Fin.last (K.indexed w.1).edgeCount)) := by
  rcases w with ⟨e,k⟩
  cases e with
  | inl e =>
    exact (K.rightConnector R hR BR (I.rightWireEquiv (e,k))).cast rfl
      (K.rightCap_equiv ε e k).symm
  | inr p =>
    exact (B.path (finProdFinEquiv (p,k))).symm.cast rfl
      ((congrArg (fun z : Fin n × Fin t =>
        (K.route (Sum.inr z.1)).laneVertex (physicalLaneOffset ε (Sum.inr z.1 : Fin c ⊕ Fin n) z.2)
          (Fin.last (K.indexed (Sum.inr z.1)).edgeCount))
        (finProdFinEquiv.symm_apply_apply (p,k))).symm)

theorem allRight_range_internal (R : I.RightMatchingFamily (t := t)) (hR : R.DiskDrawn) {ε : ℝ}
    (BR : ∀ v, K.RightBank R hR ε v) (B : K.OuterAccessBank (t := t) ε) (e : Fin c) (k : Fin t) :
    Set.range (K.allRight R hR BR B (Sum.inl e,k)) =
      Set.range (K.rightConnector R hR BR (I.rightWireEquiv (e,k))) := rfl

theorem allRight_range_boundary (R : I.RightMatchingFamily (t := t)) (hR : R.DiskDrawn) {ε : ℝ}
    (BR : ∀ v, K.RightBank R hR ε v) (B : K.OuterAccessBank (t := t) ε) (p : Fin n) (k : Fin t) :
    Set.range (K.allRight R hR BR B (Sum.inr p,k)) = Set.range (B.path (finProdFinEquiv (p,k))) :=
  (B.path (finProdFinEquiv (p,k))).symm_range

theorem allRight_simple (R : I.RightMatchingFamily (t := t)) (hR : R.DiskDrawn) {ε : ℝ}
    (BR : ∀ v, K.RightBank R hR ε v) (B : K.OuterAccessBank (t := t) ε)
    (w : (Fin c ⊕ Fin n) × Fin t) : Function.Injective (K.allRight R hR BR B w) := by
  rcases w with ⟨e,k⟩
  cases e with
  | inl e => exact K.rightConnector_simple R hR BR _
  | inr p => exact (B.simple _).comp unitInterval.symm_bijective.injective

theorem allRight_disjoint (R : I.RightMatchingFamily (t := t)) (hR : R.DiskDrawn) {ε : ℝ}
    (BR : ∀ v, K.RightBank R hR ε v) (B : K.OuterAccessBank (t := t) ε) :
    Pairwise (fun w z => Disjoint (Set.range (K.allRight R hR BR B w))
      (Set.range (K.allRight R hR BR B z))) := by
  rintro ⟨e,k⟩ ⟨f,l⟩ hne
  cases e with
  | inl e =>
    cases f with
    | inl f =>
      rw [K.allRight_range_internal,K.allRight_range_internal]
      apply K.rightConnectors_disjoint R hR BR
      intro he
      have hh := I.rightWireEquiv.injective he
      exact hne (congrArg (fun z : Fin c × Fin t => (Sum.inl z.1,z.2)) hh)
    | inr p =>
      rw [K.allRight_range_internal,K.allRight_range_boundary]
      exact (B.disjoint_rightConnector R hR BR _ _).symm
  | inr p =>
    cases f with
    | inl f =>
      rw [K.allRight_range_boundary,K.allRight_range_internal]
      exact B.disjoint_rightConnector R hR BR _ _
    | inr q =>
      rw [K.allRight_range_boundary,K.allRight_range_boundary]
      apply B.disjoint
      intro he
      have hh := finProdFinEquiv.injective he
      exact hne (congrArg (fun z : Fin n × Fin t => (Sum.inr z.1,z.2)) hh)

theorem allLeft_allRight_disjoint
    (L : I.LeftMatchingFamily (t := t)) (R : I.RightMatchingFamily (t := t))
    (hL : L.DiskDrawn) (hR : R.DiskDrawn) {ε : ℝ}
    (BL : ∀ v, K.LeftBank L hL ε v) (BR : ∀ v, K.RightBank R hR ε v)
    (B : K.OuterAccessBank (t := t) ε) (w z : (Fin c ⊕ Fin n) × Fin t) :
    Disjoint (Set.range (K.leftConnector L hL BL (I.leftWireEquiv w)))
      (Set.range (K.allRight R hR BR B z)) := by
  rcases z with ⟨e,k⟩
  cases e with
  | inl e =>
    rw [K.allRight_range_internal]
    exact K.connectors_cross_disjoint L R hL hR BL BR _ _
  | inr p =>
    rw [K.allRight_range_boundary]
    exact (B.disjoint_leftConnector L hL BL _ _).symm

/-- Assemble all internal and boundary scalar wires together. The remaining
four inputs are the whole-support contact lemmas proved for the actual stages;
all other simplicity and disjointness fields are derived above. -/
def threePieces
    (L : I.LeftMatchingFamily (t := t)) (R : I.RightMatchingFamily (t := t))
    (hL : L.DiskDrawn) (hR : R.DiskDrawn) {ε : ℝ}
    (BL : ∀ v, K.LeftBank L hL ε v) (BR : ∀ v, K.RightBank R hR ε v)
    (M : K.MiddleBank (t := t) ε) (B : K.OuterAccessBank (t := t) ε)
    (hLM : ∀ w, Set.range (K.leftConnector L hL BL (I.leftWireEquiv w)) ∩
      Set.range (K.allMiddle M w) ⊆ {K.leftCap ε (I.leftWireEquiv w)})
    (hMR : ∀ w, Set.range (K.allMiddle M w) ∩ Set.range (K.allRight R hR BR B w) ⊆
      {(K.route w.1).laneVertex (physicalLaneOffset ε w.1 w.2) (Fin.last (K.indexed w.1).edgeCount)})
    (hLMoff : ∀ w z, w ≠ z → Disjoint
      (Set.range (K.leftConnector L hL BL (I.leftWireEquiv w))) (Set.range (K.allMiddle M z)))
    (hMRoff : ∀ w z, w ≠ z → Disjoint
      (Set.range (K.allMiddle M w)) (Set.range (K.allRight R hR BR B z))) :
    ThreePieceRouting (K.allSource L hL)
      (fun w => K.leftCap ε (I.leftWireEquiv w))
      (fun w => (K.route w.1).laneVertex (physicalLaneOffset ε w.1 w.2)
        (Fin.last (K.indexed w.1).edgeCount)) (K.allTarget R hR B) where
  left w := K.leftConnector L hL BL (I.leftWireEquiv w)
  middle := K.allMiddle M
  right := K.allRight R hR BR B
  left_simple w := K.leftConnector_simple L hL BL _
  middle_simple w := M.simple w.1 w.2
  right_simple := K.allRight_simple R hR BR B
  left_middle_join := hLM
  middle_right_join := hMR
  left_disjoint := by
    intro w z hwz
    exact K.leftConnectors_disjoint L hL BL (fun he => hwz (I.leftWireEquiv.injective he))
  middle_disjoint := M.disjoint
  right_disjoint := K.allRight_disjoint R hR BR B
  left_middle_off := hLMoff
  left_right := K.allLeft_allRight_disjoint L R hL hR BL BR B
  middle_right_off := hMRoff

end AllLeftGadget.TransverseScaffold
end
end MatchgateWidth
