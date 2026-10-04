import MatchgateWidth.AllLeftGraphSubstitution

/-!
# Exact all-left lifting from concrete routing of the actual substituted graph

All graph selection, finite matching-sum algebra, block reversal and coordinate
identities are proved. The sole remaining geometric input is a genuine plane
drawing with the established strong ordered exterior access of the exact
assembled graph, using its unchanged inherited external boundary order.
-/
namespace MatchgateWidth
noncomputable section
open scoped Classical

/-- An actual finite graph with actual strong ordered exterior access realizes
its own deletion signature as an exact matchgate. -/
theorem exactMatchgate_of_finite_strongAccess {V E : Type*} [Fintype V] [Fintype E]
    {s : ℕ} (G : WeightedGraph V E ℂ) (ext : Fin s → V)
    (P : PlaneDrawing G) (A : StrongOrderedExteriorAccess P ext) :
    ExactMatchgate (fun z => deletionSignature G ext ((booleanWordEquiv s) z)) := by
  apply BooleanMatchgateIdentities.exactMatchgate
  have h := A.toOrderedExteriorAccess.deletionSignature_matchgateIdentities
  change MatchgateIdentities
    (fun U => deletionSignature G ext ((booleanWordEquiv s) ((booleanSubsetEquiv s).symm U)))
  convert h using 1
  funext U
  apply congrArg (deletionSignature G ext)
  funext i
  simp [booleanWordEquiv, booleanSubsetEquiv]

namespace AllLeftGadget
variable {S : LabelledShape} {a b c n t : ℕ} (I : AllLeftGadget S a b c n)

/-- The exact concrete geometric target. It contains graph drawing/access data
only, never an MGI or an assertion about the desired boundary tensor. -/
def SubstitutionRoutable (L : I.LeftMatchingFamily (t := t)) (R : I.RightMatchingFamily (t := t)) : Prop :=
  ∃ P : PlaneDrawing (I.substitutionGraph L R),
    Nonempty (StrongOrderedExteriorAccess P (I.substitutionExternal L R))

/-- Supplied concrete geometric routing turns the proved assembled matching
signature into the exact original gadget boundary lift. -/
theorem exact_lift_of_substitution_routing
    (p : LabelledCommonPresentation S (Fin 3) t)
    (L : I.LeftMatchingFamily (t := t)) (R : I.RightMatchingFamily (t := t))
    (hL : L.Realizes (I.correctedLeftTensor
      (fun l => leftBooleanLift p.baseMatrix (S.leftArity l) (p.left l))))
    (hR : R.Realizes (fun v => p.rightPreimage (I.rightLabel v)))
    (hrouting : I.SubstitutionRoutable L R) :
    ExactMatchgate (leftBooleanLift p.baseMatrix n (I.value p.language)) := by
  obtain ⟨P,⟨A⟩⟩ := hrouting
  have hgraph := exactMatchgate_of_finite_strongAccess
    (I.substitutionGraph L R) (I.substitutionExternal L R) P A
  have he : (fun z => deletionSignature (I.substitutionGraph L R) (I.substitutionExternal L R)
      ((booleanWordEquiv (n*t)) z)) = leftBooleanLift p.baseMatrix n (I.value p.language) := by
    funext z
    have hh := I.substitution_signature_eq_physical_network L R _ p.rightPreimage hL hR
      ((booleanBlocksEquiv n t).symm z)
    have hz : flattenBooleanBlocks ((booleanBlocksEquiv n t).symm z) = z :=
      (booleanBlocksEquiv n t).apply_symm_apply z
    rw [hz, I.internalPhysicalNetwork_presentation_eq_lift] at hh
    exact hh
  exact he ▸ hgraph

/-- The exact selected local families are provided together with the remaining
purely geometric implication. No arbitrary realization or output MGI is assumed. -/
theorem exists_corrected_graphs_with_lifting
    (p : LabelledCommonPresentation S (Fin 3) t) (hM : p.baseMatrix.rank = 3) :
    ∃ (L : I.LeftMatchingFamily (t := t)) (R : I.RightMatchingFamily (t := t)),
      L.DiskDrawn ∧ R.DiskDrawn ∧
      L.Realizes (I.correctedLeftTensor
        (fun l => leftBooleanLift p.baseMatrix (S.leftArity l) (p.left l))) ∧
      R.Realizes (fun v => p.rightPreimage (I.rightLabel v)) ∧
      (I.SubstitutionRoutable L R → ExactMatchgate (leftBooleanLift p.baseMatrix n (I.value p.language))) := by
  obtain ⟨L,R,hLd,hRd,hL,hR,he⟩ := I.exists_corrected_local_graphs p hM
  exact ⟨L,R,hLd,hRd,hL,hR,I.exact_lift_of_substitution_routing p L R hL hR⟩

end AllLeftGadget

/-- The independent source-topology routing interface, proved universally in
AllLeftSubstitutionRouting:
every actual connected ordered-planar gadget admits the specified scalar
substitution for any independently disk-drawn local matching graphs. -/
def AllLeftSubstitutionRouting (S : LabelledShape) (t : ℕ) : Prop :=
  ∀ a b c n (I : AllLeftGadget S a b c n), I.Connected → Nonempty I.OrderedPlanar →
    ∀ (L : I.LeftMatchingFamily (t := t)) (R : I.RightMatchingFamily (t := t)),
      L.DiskDrawn → R.DiskDrawn → I.SubstitutionRoutable L R

/-- The exact-lifting interface is discharged by concrete source routing.
Only the independent geometric routing obligation remains in this theorem. -/
theorem allLeftExactLifting_of_substitutionRouting {S : LabelledShape} {t : ℕ}
    (p : LabelledCommonPresentation S (Fin 3) t) (hM : p.baseMatrix.rank = 3)
    (hroute : AllLeftSubstitutionRouting S t) : AllLeftExactLifting p := by
  intro a b c n I hconn hplan
  obtain ⟨L,R,hLd,hRd,hL,hR,hglue⟩ := I.exists_corrected_graphs_with_lifting p hM
  exact hglue (hroute a b c n I hconn hplan L R hLd hRd)

end
end MatchgateWidth
