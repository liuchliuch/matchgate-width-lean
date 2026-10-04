import MatchgateWidth.AllLeftContactAssembly
import MatchgateWidth.AllLeftConnectorRaw

/-! # One globally chosen width and all actual source stage families

Every finite local graph drawing, connector bank, middle ribbon and outer
access is selected at the same positive width, below any additional prescribed
positive contact bound. Explicit raw-curve identities are preserved for the
proved uniform contact theorems.
-/
namespace MatchgateWidth
noncomputable section
namespace AllLeftGadget.TransverseScaffold
variable {S : LabelledShape} {a b c n t : ℕ} {I : AllLeftGadget S a b c n}
    (K : I.TransverseScaffold)

structure GlobalStages (L : I.LeftMatchingFamily (t := t)) (R : I.RightMatchingFamily (t := t))
    (hL : L.DiskDrawn) (hR : R.DiskDrawn) where
  width : ℝ
  positive : 0 < width
  left : ∀ v, K.LeftBank L hL width v
  right : ∀ v, K.RightBank R hR width v
  middle : K.MiddleBank (t := t) width
  outer : K.OuterAccessBank (t := t) width
  left_formula : ∀ v q u, (left v).path q u = K.leftRaw L hL v q width u
  right_formula : ∀ v q u, (right v).path q u = K.rightRaw R hR v q width u

/-- All actual stage families exist simultaneously below an arbitrary positive
bound. This finite choice includes all zero-width-arity and empty-family cases. -/
theorem exists_globalStages_below
    (L : I.LeftMatchingFamily (t := t)) (R : I.RightMatchingFamily (t := t))
    (hL : L.DiskDrawn) (hR : R.DiskDrawn) (η : ℝ) (hη : 0 < η) :
    ∃ G : K.GlobalStages L R hL hR, G.width < η := by
  obtain ⟨εM,hεM,hM⟩ := K.exists_uniform_middle_bank t
  obtain ⟨εB,hεB,hB⟩ := K.exists_uniform_local_banks L R hL hR
  obtain ⟨εO,hεO,hO⟩ := K.exists_uniform_outer_access t
  let δ := min η (min εM (min εB εO))
  have hδ : 0 < δ := lt_min hη (lt_min hεM (lt_min hεB hεO))
  let ε := δ/2
  have hε : 0 < ε := half_pos hδ
  have hεδ : ε < δ := half_lt_self hδ
  have hεη : ε < η := hεδ.trans_le (min_le_left _ _)
  have hεM' : ε < εM := hεδ.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hεB' : ε < εB := hεδ.trans_le ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _)))
  have hεO' : ε < εO := hεδ.trans_le ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _)))
  obtain ⟨M⟩ := hM ε hε hεM'.le
  obtain ⟨BL,BR,hBL,hBR⟩ := hB ε hε hεB'
  obtain ⟨B⟩ := hO ε hε hεO'
  exact ⟨⟨ε,hε,BL,BR,M,B,hBL,hBR⟩,hεη⟩

end AllLeftGadget.TransverseScaffold
end
end MatchgateWidth
