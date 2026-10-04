import MatchgateWidth.AllLeftGlobalStages
import MatchgateWidth.AllLeftLeftConnectorMiddle
import MatchgateWidth.AllLeftRightConnectorMiddle
import MatchgateWidth.AllLeftOuterMiddleSeparation

/-! # Unconditional geometric substitution of actual ordered all-left gadgets

Every choice is derived from the original ordered source drawing and the
independent actual local matching-graph disk drawings. A single width is chosen
below the three proved whole-stage contact thresholds. The literal substituted
graph receives a plane drawing and strong global exterior access in the exact
inherited scalar boundary order. No routing or output-MGI premise remains.
-/
namespace MatchgateWidth
noncomputable section
namespace AllLeftGadget
variable {S : LabelledShape} {a b c n t : ℕ} {I : AllLeftGadget S a b c n}

/-- The derived source scaffold routes every family of actual local matching
graphs, preserving all vertices, edges, external indices, and nullary cases. -/
theorem TransverseScaffold.substitutionRoutable (K : I.TransverseScaffold)
    (L : I.LeftMatchingFamily (t := t)) (R : I.RightMatchingFamily (t := t))
    (hL : L.DiskDrawn) (hR : R.DiskDrawn) : I.SubstitutionRoutable L R := by
  obtain ⟨ηL,hηL,hcontactL⟩ := K.exists_uniform_leftConnector_middle_contact L hL
  obtain ⟨ηR,hηR,hcontactR⟩ := K.exists_uniform_rightConnector_middle_contact R hR
  obtain ⟨ηO,hηO,hcontactO⟩ := K.exists_uniform_outerAccess_middle_contact t
  obtain ⟨G,hG⟩ := K.exists_globalStages_below L R hL hR (min ηL (min ηR ηO))
    (lt_min hηL (lt_min hηR hηO))
  have hLsmall : G.width < ηL := hG.trans_le (min_le_left _ _)
  have hRsmall : G.width < ηR := hG.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hOsmall : G.width < ηO := hG.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  apply K.substitutionRoutable_of_pieceContacts L R hL hR G.positive G.left G.right G.middle G.outer
  apply K.pieceContacts_of_point_contacts L R hL hR G.left G.right G.middle G.outer
  · exact hcontactL G.width G.positive hLsmall G.middle.width G.left G.left_formula
  · intro q e k z hz hm
    obtain ⟨he,hk,hz⟩ := hcontactR G.width G.positive hRsmall G.middle.width
      G.right G.right_formula q e k z hz hm
    exact ⟨Prod.ext he hk,hz⟩
  · exact hcontactO G.width G.positive hOsmall G.middle.width G.outer

/-- The original ordered-planar gadget itself supplies all required geometric
data. Connectedness is unnecessary for this stronger actual drawing statement. -/
theorem OrderedPlanar.substitutionRoutable (P : I.OrderedPlanar)
    (L : I.LeftMatchingFamily (t := t)) (R : I.RightMatchingFamily (t := t))
    (hL : L.DiskDrawn) (hR : R.DiskDrawn) : I.SubstitutionRoutable L R := by
  obtain ⟨K,_⟩ := OrderedPlanar.exists_transverseScaffold I P
  exact K.substitutionRoutable L R hL hR

end AllLeftGadget

/-- Universal actual source routing at every width, including width zero.
There are no extra regularity, nonzero tensor, arity, or face assumptions. -/
theorem allLeftSubstitutionRouting (S : LabelledShape) (t : ℕ) : AllLeftSubstitutionRouting S t := by
  intro a b c n I _ hplan L R hL hR
  exact (Classical.choice hplan).substitutionRoutable L R hL hR

/-- All ordered all-left gadget boundary lifts are actual exact matchgates for
every valid full-rank qutrit presentation. Geometric closure is now proved. -/
theorem allLeftExactLifting_of_full_rank {S : LabelledShape} {t : ℕ}
    (p : LabelledCommonPresentation S (Fin 3) t) (hM : p.baseMatrix.rank = 3) :
    AllLeftExactLifting p :=
  allLeftExactLifting_of_substitutionRouting p hM (allLeftSubstitutionRouting S t)

end
end MatchgateWidth
