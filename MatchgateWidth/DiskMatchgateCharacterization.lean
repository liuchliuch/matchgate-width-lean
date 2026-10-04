import MatchgateWidth.DiskBoundaryNoncrossing
import MatchgateWidth.PivotCircuitRealization

/-! # Exact geometric/algebraic characterization of disk matchgates

Both directions are proved. This file does not identify an arbitrary
outer-face plane-embedding model with the disk-witness model.
-/
namespace MatchgateWidth
noncomputable section

/-- The same genuine disk realizability predicate in `Fin 2` coordinates. -/
def BooleanDiskRealizable {n : ℕ} (f : BooleanTable n ℂ) : Prop :=
  DiskRealizable (fun y => f ((booleanWordEquiv n).symm y))

theorem BooleanDiskRealizable.matchgateIdentities {n : ℕ}
    {f : BooleanTable n ℂ} (hf : BooleanDiskRealizable f) :
    BooleanMatchgateIdentities f := by
  have h := DiskRealizable.matchgateIdentities hf
  change MatchgateIdentities (fun S => f ((booleanWordEquiv n).symm
    (fun i => decide (i ∈ S)))) at h
  have heq : (fun S => (booleanWordEquiv n).symm (fun i => decide (i ∈ S))) =
      (booleanSubsetEquiv n).symm := by
    funext S i
    simp [booleanWordEquiv, booleanSubsetEquiv]
  change MatchgateIdentities (fun S => f ((booleanSubsetEquiv n).symm S))
  convert h using 1
  funext S
  exact congrArg f (congrFun heq S).symm

/-- Exact equivalence at every arity, including nullary and zero signatures. -/
theorem booleanDiskRealizable_iff_matchgateIdentities {n : ℕ} (f : BooleanTable n ℂ) :
    BooleanDiskRealizable f ↔ BooleanMatchgateIdentities f :=
  ⟨BooleanDiskRealizable.matchgateIdentities, BooleanMatchgateIdentities.diskRealizable⟩

/-- Restricting coefficients to a subfield preserves the literal equations. -/
theorem BooleanMatchgateIdentities.restrictSubfield {n : ℕ}
    {f : BooleanTable n ℂ} (hf : BooleanMatchgateIdentities f)
    (K : Subfield ℂ) (hK : ∀ z, f z ∈ K) :
    BooleanMatchgateIdentities (fun z => (⟨f z, hK z⟩ : K)) := by
  intro α β
  apply K.subtype.injective
  simpa [matchgateSum] using hf α β

/-- A disk signature whose values lie in K has an actual realization using
only edge weights in K. No weights of its original realizing graph are assumed
algebraic or in K. -/
theorem BooleanDiskRealizable.field_preserving {n : ℕ} {f : BooleanTable n ℂ}
    (hf : BooleanDiskRealizable f) (K : Subfield ℂ) (hK : ∀ z, f z ∈ K) :
    ∃ (v e : ℕ) (G : WeightedGraph (Fin v) (Fin e) ℂ) (ext : Fin n → Fin v),
      Nonempty (PlanarDrawing G ext) ∧ (∀ a, G.weight a ∈ K) ∧
      ∀ y, deletionSignature G ext y = f ((booleanWordEquiv n).symm y) := by
  obtain ⟨v,e,G,ext,hd,hw,hval⟩ :=
    (hf.matchgateIdentities.restrictSubfield K hK).diskWitness_map_all K.subtype
  refine ⟨v,e,G,ext,hd,?_,hval⟩
  intro a
  obtain ⟨q,hq⟩ := hw a
  rw [hq]
  exact q.property

end
end MatchgateWidth
