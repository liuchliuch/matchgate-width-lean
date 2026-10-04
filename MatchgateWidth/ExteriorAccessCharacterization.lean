import MatchgateWidth.DiskExteriorAccess
import MatchgateWidth.DiskMatchgateCharacterization

/-!
# Exact signatures with explicit ordered exterior access

The equivalence below is at the level of signatures. The forward geometric
map retains the original graph; the converse uses the proved constructive MGI
realization and may change the graph. This is not an embedding-normalization
or arbitrary ordered outer-face correspondence theorem.
-/
namespace MatchgateWidth
noncomputable section

/-- Exact signatures of finite plane drawings with explicit ordered exterior
access. No assertion identifies this predicate with an independently defined
source-paper outer-face model. -/
def ExteriorAccessRealizable {s : ℕ} (f : (Fin s → Bool) → ℂ) : Prop :=
  ∃ (n m : ℕ) (G : WeightedGraph (Fin n) (Fin m) ℂ) (ext : Fin s → Fin n)
    (P : PlaneDrawing G), Nonempty (OrderedExteriorAccess P ext) ∧
      ∀ x, f x = deletionSignature G ext x

theorem DiskRealizable.exteriorAccessRealizable {s : ℕ}
    {f : (Fin s → Bool) → ℂ} (hf : DiskRealizable f) : ExteriorAccessRealizable f := by
  obtain ⟨n, m, G, ext, ⟨D⟩, h⟩ := hf
  exact ⟨n, m, G, ext, D.toPlaneDrawing, ⟨D.orderedExteriorAccess⟩, h⟩

theorem ExteriorAccessRealizable.matchgateIdentities {s : ℕ}
    {f : (Fin s → Bool) → ℂ} (hf : ExteriorAccessRealizable f) :
    MatchgateIdentities (fun S => f (fun i => decide (i ∈ S))) := by
  obtain ⟨n, m, G, ext, P, ⟨A⟩, h⟩ := hf
  simpa only [h] using A.deletionSignature_matchgateIdentities

/-- Constructive disk realization of a signature with explicit exterior
access; the realizing graph need not be the original plane graph. -/
theorem ExteriorAccessRealizable.diskRealizable {s : ℕ}
    {f : (Fin s → Bool) → ℂ} (hf : ExteriorAccessRealizable f) : DiskRealizable f := by
  let g : BooleanTable s ℂ := fun x => f (booleanWordEquiv s x)
  have hg : BooleanMatchgateIdentities g := by
    change MatchgateIdentities (fun S => f (booleanWordEquiv s ((booleanSubsetEquiv s).symm S)))
    convert hf.matchgateIdentities using 1
    funext S
    congr 1
    funext i
    simp [booleanWordEquiv, booleanSubsetEquiv]
  simpa only [g, Equiv.apply_symm_apply] using hg.diskRealizable

/-- Equality of two explicitly geometric signature classes. This does not
supply access arcs for an arbitrary ordered outer-face plane embedding. -/
theorem exteriorAccessRealizable_iff_diskRealizable {s : ℕ}
    (f : (Fin s → Bool) → ℂ) : ExteriorAccessRealizable f ↔ DiskRealizable f :=
  ⟨ExteriorAccessRealizable.diskRealizable, DiskRealizable.exteriorAccessRealizable⟩

end
end MatchgateWidth
