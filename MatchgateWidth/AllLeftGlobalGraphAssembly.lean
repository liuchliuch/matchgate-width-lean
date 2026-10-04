import MatchgateWidth.AllLeftAssembledCarriers

/-! # Concrete global graph/access assembly from the constructed stage contacts

Internal and external scalar wires are assembled in one noncrossing family.
The resulting graph is literally `I.substitutionGraph L R`, and its exterior
access starts at literally `I.substitutionExternal L R` in inherited order.
The source-only existence theorem supplies the four local contact facts from
independent geometric constructions; no output MGI is used here.
-/
namespace MatchgateWidth
noncomputable section
namespace AllLeftGadget.TransverseScaffold
variable {S : LabelledShape} {a b c n t : ℕ} {I : AllLeftGadget S a b c n}
    (K : I.TransverseScaffold)

structure PieceContacts (L : I.LeftMatchingFamily (t := t)) (R : I.RightMatchingFamily (t := t))
    (hL : L.DiskDrawn) (hR : R.DiskDrawn) {ε : ℝ}
    (BL : ∀ v, K.LeftBank L hL ε v) (BR : ∀ v, K.RightBank R hR ε v)
    (M : K.MiddleBank (t := t) ε) (B : K.OuterAccessBank (t := t) ε) : Prop where
  left_join : ∀ w, Set.range (K.leftConnector L hL BL (I.leftWireEquiv w)) ∩
    Set.range (K.allMiddle M w) ⊆ {K.leftCap ε (I.leftWireEquiv w)}
  right_join : ∀ w, Set.range (K.allMiddle M w) ∩ Set.range (K.allRight R hR BR B w) ⊆
    {(K.route w.1).laneVertex (physicalLaneOffset ε w.1 w.2) (Fin.last (K.indexed w.1).edgeCount)}
  left_off : ∀ w z, w ≠ z → Disjoint
    (Set.range (K.leftConnector L hL BL (I.leftWireEquiv w))) (Set.range (K.allMiddle M z))
  right_off : ∀ w z, w ≠ z → Disjoint
    (Set.range (K.allMiddle M w)) (Set.range (K.allRight R hR BR B z))

def internalIndex (_K : I.TransverseScaffold) (w : Fin (c*t)) : (Fin c ⊕ Fin n) × Fin t :=
  (Sum.inl (finProdFinEquiv.symm w).1,(finProdFinEquiv.symm w).2)

def boundaryIndex (_K : I.TransverseScaffold) (w : Fin (n*t)) : (Fin c ⊕ Fin n) × Fin t :=
  (Sum.inr (finProdFinEquiv.symm w).1,(finProdFinEquiv.symm w).2)

theorem internalIndex_injective : Function.Injective (K.internalIndex (t := t)) := by
  intro w z h
  apply (finProdFinEquiv : Fin c × Fin t ≃ Fin (c*t)).symm.injective
  exact Prod.ext (Sum.inl.inj (congrArg Prod.fst h))
    (congrArg (fun q : (Fin c ⊕ Fin n) × Fin t => q.2) h)

theorem boundaryIndex_injective : Function.Injective (K.boundaryIndex (t := t)) := by
  intro w z h
  apply (finProdFinEquiv : Fin n × Fin t ≃ Fin (n*t)).symm.injective
  exact Prod.ext (Sum.inr.inj (congrArg Prod.fst h))
    (congrArg (fun q : (Fin c ⊕ Fin n) × Fin t => q.2) h)

/-- Actual graph drawing and strong exterior access, built by finite geometric
concatenation on all original scalar wire identities. -/
theorem substitutionRoutable_of_pieceContacts
    (L : I.LeftMatchingFamily (t := t)) (R : I.RightMatchingFamily (t := t))
    (hL : L.DiskDrawn) (hR : R.DiskDrawn) {ε : ℝ} (hε : 0 < ε)
    (BL : ∀ v, K.LeftBank L hL ε v) (BR : ∀ v, K.RightBank R hR ε v)
    (M : K.MiddleBank (t := t) ε) (B : K.OuterAccessBank (t := t) ε)
    (H : K.PieceContacts L R hL hR BL BR M B) : I.SubstitutionRoutable L R := by
  let T := K.threePieces L R hL hR BL BR M B H.left_join H.right_join H.left_off H.right_off
  let TI := T.reindex K.internalIndex K.internalIndex_injective
  let P := K.leftPlane L hL
  let Q := K.rightPlane R hR
  let C := K.familyCarriers L R hL hR
  let extL := sigmaExternal L.external ∘ I.internalLeftWire
  let extR := sigmaExternal R.external ∘ I.internalRightWire
  have hCA : TI.CarrierAvoidance C.left C.right := by
    refine {
      left_meets_left := ?_
      left_avoids_right := ?_
      middle_avoids_left := ?_
      middle_avoids_right := ?_
      right_avoids_left := ?_
      right_meets_right := ?_ }
    · intro w
      exact K.leftConnector_meets_left L hL BL (I.internalLeftWire w)
    · intro w
      exact K.leftConnector_avoids_right L R hL hR BL (I.internalLeftWire w)
    · intro w
      exact (M.avoids_inner hε _ _).mono Set.Subset.rfl (K.leftUnion_subset_inner L hL)
    · intro w
      exact (M.avoids_inner hε _ _).mono Set.Subset.rfl (K.rightUnion_subset_inner R hR)
    · intro w
      exact K.rightConnector_avoids_left L R hL hR BR (I.internalRightWire w)
    · intro w
      exact K.rightConnector_meets_right R hR BR (I.internalRightWire w)
  let routes := ThreePieceRouting.toBridgeRouting P Q C extL extR TI hCA
  let D := P.bridge Q C extL extR routes
  let ext := sigmaExternal L.external ∘ I.boundaryLeftWire
  let access (w : Fin (n*t)) : Path (P.vertex (ext w)) ((2:ℂ)*boundaryPoint (B.angle w)) :=
    (T.wirePath (K.boundaryIndex w)).cast rfl (by
      simp only [allTarget,boundaryIndex,Prod.mk.eta,Equiv.apply_symm_apply])
  have hwireBound (w : (Fin c ⊕ Fin n) × Fin t) (u : unitInterval) : ‖T.wirePath w u‖ ≤ 2 := by
    have hz : T.wirePath w u ∈ Set.range (T.wirePath w) := ⟨u,rfl⟩
    rw [T.wirePath_range] at hz
    rcases hz with hl | hm | hr
    · obtain ⟨v,hv⟩ := hl
      have hb := K.norm_lt_three_quarters_of_primitive_disk _
        (K.leftConnector_bound L hL BL (I.leftWireEquiv w) v)
      change K.leftConnector L hL BL (I.leftWireEquiv w) v = T.wirePath w u at hv
      rw [hv] at hb
      linarith
    · obtain ⟨v,hv⟩ := hm
      have hb := M.norm_lt_one hε w.1 w.2 v
      change M.path w.1 w.2 v = T.wirePath w u at hv
      rw [hv] at hb
      linarith
    · exact K.allRight_norm_le_two R hR BR B w hr
  have hAL (w : Fin (n*t)) : Set.range (access w) ∩ C.left ⊆ {P.vertex (ext w)} := by
    intro z hz
    have hp : z ∈ Set.range (T.wirePath (K.boundaryIndex w)) := hz.1
    rw [T.wirePath_range] at hp
    rcases hp with hl | hm | hr
    · exact K.leftConnector_meets_left L hL BL (I.boundaryLeftWire w) ⟨hl,hz.2⟩
    · exact (Set.disjoint_left.mp (M.avoids_inner hε _ _) hm
        (K.leftUnion_subset_inner L hL hz.2)).elim
    · change z ∈ Set.range (K.allRight R hR BR B
        (Sum.inr (finProdFinEquiv.symm w).1,(finProdFinEquiv.symm w).2)) at hr
      rw [K.allRight_range_boundary] at hr
      exact (Set.disjoint_left.mp (B.avoids_inner _) hr
        (K.leftUnion_subset_inner L hL hz.2)).elim
  have hAR (w : Fin (n*t)) : Disjoint (Set.range (access w)) C.right := by
    apply Set.disjoint_left.mpr
    intro z hz hc
    have hp : z ∈ Set.range (T.wirePath (K.boundaryIndex w)) := hz
    rw [T.wirePath_range] at hp
    rcases hp with hl | hm | hr
    · exact Set.disjoint_left.mp (K.leftConnector_avoids_right L R hL hR BL (I.boundaryLeftWire w)) hl hc
    · exact Set.disjoint_left.mp (M.avoids_inner hε _ _) hm (K.rightUnion_subset_inner R hR hc)
    · change z ∈ Set.range (K.allRight R hR BR B
        (Sum.inr (finProdFinEquiv.symm w).1,(finProdFinEquiv.symm w).2)) at hr
      rw [K.allRight_range_boundary] at hr
      exact Set.disjoint_left.mp (B.avoids_inner _) hr (K.rightUnion_subset_inner R hR hc)
  have hAB (w : Fin (n*t)) (v : Fin (c*t)) :
      Disjoint (Set.range (access w)) (Set.range (routes.arc v)) := by
    exact T.wirePaths_disjoint (i := K.boundaryIndex w) (j := K.internalIndex v)
      (fun h => Sum.inr_ne_inl (congrArg Prod.fst h))
  have hPv (v) : ‖P.vertex v‖ ≤ (2:ℝ) :=
    K.norm_le_two_of_inner (K.leftCarrier_subset_inner L hL v.1 ((K.leftCarriers L hL).vertex_mem v.1 v.2))
  have hQv (v) : ‖Q.vertex v‖ ≤ (2:ℝ) :=
    K.norm_le_two_of_inner (K.rightCarrier_subset_inner R hR v.1 ((K.rightCarriers R hR).vertex_mem v.1 v.2))
  have hPe (e) (u : unitInterval) : ‖P.edge e u‖ ≤ (2:ℝ) :=
    K.norm_le_two_of_inner (K.leftCarrier_subset_inner L hL e.1 ((K.leftCarriers L hL).edge_mem e.1 e.2 u))
  have hQe (e) (u : unitInterval) : ‖Q.edge e u‖ ≤ (2:ℝ) :=
    K.norm_le_two_of_inner (K.rightCarrier_subset_inner R hR e.1 ((K.rightCarriers R hR).edge_mem e.1 e.2 u))
  refine ⟨D,⟨P.bridgeStrongExteriorAccess Q C extL extR routes ext
    ((sigmaExternal_injective L.external L.external_injective).comp I.boundaryLeftWire_injective)
    2 (by norm_num) B.angle B.angle_pos B.angle_lt_one B.angle_strictMono access
    (fun w => T.wirePath_injective (K.boundaryIndex w))
    (fun _ _ hwz => T.wirePaths_disjoint (fun he => hwz (K.boundaryIndex_injective he)))
    hAL hAR hAB hPv hQv hPe hQe
    (fun w u => hwireBound (K.internalIndex w) u) (fun w u => hwireBound (K.boundaryIndex w) u)⟩⟩

end AllLeftGadget.TransverseScaffold
end
end MatchgateWidth
