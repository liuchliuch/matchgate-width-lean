import MatchgateWidth.CliffordProductCover
import MatchgateWidth.CliffordMatchgateMatrix
import MatchgateWidth.PivotCircuitRealization

/-!
# The isotropic-kernel cover theorem

Algebraic source Lemma 10.6, with the actual signed coefficient-spinor action.
The proof constructs dual Clifford factors and their kernel projection, realizes
those factors by literal ordered MGI matrices, and selects a full-row Gaussian
input cube. No Witt extension, Pin lift, canonical form, or cover is assumed.
The complex specialization also supplies a genuine certified disk graph.
-/
namespace MatchgateWidth
noncomputable section
variable {K : Type*} [Field K] [CharZero K] {t r : ℕ}

/-- Every `(t-r)`-dimensional isotropic subspace has an exact ordered-MGI
`r`-input, `t`-output cover whose row space is its entire genuine joint kernel. -/
theorem isotropic_kernel_cover
    (L : Submodule K (CliffordVector t K)) (hL : CliffordIsotropic L)
    (hr : r ≤ t) (hdim : Module.finrank K L = t - r) :
    ∃ P : Matrix (BooleanInput r) (BooleanInput t) K,
      OrderedMatchgateMatrix P ∧ P.rank = 2 ^ r ∧
      (orderedRowSpace P).map spinorSubsetEquiv.toLinearMap = cliffordJointKernel L := by
  apply exists_isotropic_kernel_cover_of_vector_mgi _ L hL hr hdim
  intro z
  change OrderedMatchgateMatrix (signedCliffordMatrix z)
  exact signedCliffordMatrix_isMatchgate z

/-- Source-facing complex version of Lemma 10.6, including an actual exact
weighted graph with a certified disk drawing. `spinorSubsetEquiv` sends a
Boolean word to its selected increasing subset; its coefficients are therefore
those of the ordered exterior basis `e_{i₁} ∧ ⋯ ∧ e_{iₖ}`. The Clifford action
uses the corresponding signed insertion/deletion convention throughout.
The disk's signature has increasing inputs followed by decreasing outputs,
exactly as specified by `orderedMatrixSignature`. -/
theorem isotropic_kernel_cover_disk
    (L : Submodule ℂ (CliffordVector t ℂ)) (hL : CliffordIsotropic L)
    (hr : r ≤ t) (hdim : Module.finrank ℂ L = t - r) :
    ∃ P : Matrix (BooleanInput r) (BooleanInput t) ℂ,
      OrderedMatchgateMatrix P ∧ P.rank = 2 ^ r ∧
      (orderedRowSpace P).map spinorSubsetEquiv.toLinearMap = cliffordJointKernel L ∧
      DiskRealizable (fun y => orderedMatrixSignature P ((booleanWordEquiv (r+t)).symm y)) := by
  obtain ⟨P, hP, hPr, hrow⟩ := isotropic_kernel_cover L hL hr hdim
  exact ⟨P, hP, hPr, hrow, BooleanMatchgateIdentities.diskRealizable hP⟩

end
end MatchgateWidth
