import MatchgateWidth.IsotropicKernelDimension
import MatchgateWidth.SpinorOperatorMatrix
import MatchgateWidth.MGIRowSpaceBasis

/-! # Ordered-MGI covers from actual Clifford-vector matrices
The geometric part is constructive: actual Clifford products project onto the
common kernel; Gaussian mode selection removes redundant Boolean inputs.
The only representation interface is that each actual vector-action matrix
satisfies MGI. This interface is discharged in CliffordMatchgateMatrix.
-/
namespace MatchgateWidth
noncomputable section
variable {K : Type*} [Field K] {t n r : ℕ}

/-- Ordered composition realizes the explicit common-kernel projection. -/
theorem fermionicKernelProjector_orderedMatchgate
    (A B : Fin n → Module.End K (SubsetSignature t K))
    (hA : ∀ i, OrderedMatchgateMatrix (spinorOperatorMatrix (A i)))
    (hB : ∀ i, OrderedMatchgateMatrix (spinorOperatorMatrix (B i))) :
    OrderedMatchgateMatrix (spinorOperatorMatrix (fermionicKernelProjector A B)) := by
  induction n with
  | zero => simpa [fermionicKernelProjector] using OrderedMatchgateMatrix.one (R := K) t
  | succ n ih =>
    simp only [fermionicKernelProjector, spinorOperatorMatrix_mul]
    exact ((hA 0).mul (hB 0)).mul
      (ih (fun i => A i.succ) (fun i => B i.succ) (fun i => hA i.succ) (fun i => hB i.succ))

variable [CharZero K]

/-- Once each actual Clifford-vector matrix is known to satisfy the literal
ordered identities, every isotropic common kernel has a full-row ordered cover.
The cover, kernel dimension, and reduction are all conclusions, not hypotheses. -/
theorem exists_isotropic_kernel_cover_of_vector_mgi
    (hvector : ∀ z : CliffordVector t K, OrderedMatchgateMatrix (spinorOperatorMatrix (signedCliffordAction z)))
    (L : Submodule K (CliffordVector t K)) (hL : CliffordIsotropic L)
    (hr : r ≤ t) (hdim : Module.finrank K L = t - r) :
    ∃ P : Matrix (BooleanInput r) (BooleanInput t) K,
      OrderedMatchgateMatrix P ∧ P.rank = 2 ^ r ∧
      (orderedRowSpace P).map spinorSubsetEquiv.toLinearMap = cliffordJointKernel L := by
  obtain ⟨a, b, hab⟩ := exists_signedClifford_jointKernel_product L hL
  let f := fermionicKernelProjector
    (fun i => signedCliffordAction (a i)) (fun i => signedCliffordAction (b i))
  let M := (spinorOperatorMatrix f).transpose
  have hM : OrderedMatchgateMatrix M :=
    (fermionicKernelProjector_orderedMatchgate _ _ (fun i => hvector (a i))
      (fun i => hvector (b i))).transpose
  have hMr : M.rank = 2 ^ r := by
    rw [Matrix.rank_transpose, spinorOperatorMatrix_rank, hab]
    exact cliffordJointKernel_finrank L hL hr hdim
  obtain ⟨P, hP, hPr, hrow⟩ := hM.exists_fullRow_cover hMr
  refine ⟨P, hP, hPr, ?_⟩
  rw [hrow, spinorOperatorMatrix_transpose_rowSpace, hab]

end
end MatchgateWidth
