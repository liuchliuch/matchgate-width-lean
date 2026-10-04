import MatchgateWidth.CliffordReversal

/-! # Common annihilators of ordered MGI row spaces
A full-row `r`-input ordered MGI matrix has exactly `t-r` common output
annihilators. The lower bound is computed inside the genuine total-tensor
annihilator; the upper bound uses the proved common-kernel dimension and rank.
-/
namespace MatchgateWidth
noncomputable section
variable {R : Type*} [CommRing R] {m t r : ℕ}

/-- Common signed Clifford annihilator of all literal Boolean matrix rows. -/
def rowCommonAnnihilator (P : Matrix (BooleanInput m) (BooleanInput t) R) :
    Submodule R (CliffordVector t R) :=
  ⨅ x : BooleanInput m, spinorAnnihilator (spinorSubsetEquiv (P.row x))

@[simp] theorem mem_rowCommonAnnihilator
    (P : Matrix (BooleanInput m) (BooleanInput t) R) (z : CliffordVector t R) :
    z ∈ rowCommonAnnihilator P ↔ ∀ x, signedCliffordAction z (spinorSubsetEquiv (P.row x)) = 0 := by
  simp [rowCommonAnnihilator, spinorAnnihilator]

/-- The ordered tensor's output slice is the actual unsigned reversal of a row. -/
theorem orderedMatrixSubsetSignature_slice
    (P : Matrix (BooleanInput m) (BooleanInput t) R) (X : Finset (Fin m)) :
    (fun Y => orderedMatrixSubsetSignature P (blockJoin X Y)) =
      reverseSpinor (spinorSubsetEquiv (P.row ((booleanSubsetEquiv m).symm X))) := by
  funext Y
  rw [orderedMatrixSubsetSignature_blockJoin]
  rfl

/-- Explicit reversal-corrected correspondence with the total tensor cut. -/
theorem reverseClifford_mem_sliceCommonAnnihilator
    (P : Matrix (BooleanInput m) (BooleanInput t) R) (z : CliffordVector t R) :
    reverseCliffordEquiv z ∈ sliceCommonAnnihilator (orderedMatrixSubsetSignature P) ↔
      z ∈ rowCommonAnnihilator P := by
  simp only [mem_sliceCommonAnnihilator, orderedMatrixSubsetSignature_slice]
  change (∀ X, reverseCliffordEquiv z ∈
    spinorAnnihilator (reverseSpinor (spinorSubsetEquiv (P.row ((booleanSubsetEquiv m).symm X))))) ↔ _
  simp only [reverseClifford_mem_annihilator_iff]
  constructor
  · intro h
    rw [mem_rowCommonAnnihilator]
    intro x
    have hx := h ((booleanSubsetEquiv m) x)
    change signedCliffordAction z (spinorSubsetEquiv (P.row ((booleanSubsetEquiv m).symm ((booleanSubsetEquiv m) x)))) = 0 at hx
    simpa using hx
  · intro h X
    exact (mem_rowCommonAnnihilator P z).mp h ((booleanSubsetEquiv m).symm X)

/-- The signed reversal map identifies both common-annihilator spaces exactly. -/
theorem rowCommonAnnihilator_map_reverse
    (P : Matrix (BooleanInput m) (BooleanInput t) R) :
    (rowCommonAnnihilator P).map reverseCliffordEquiv.toLinearMap =
      sliceCommonAnnihilator (orderedMatrixSubsetSignature P) := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact (reverseClifford_mem_sliceCommonAnnihilator P w).mpr hw
  · intro hz
    refine ⟨reverseCliffordEquiv.symm z, ?_, reverseCliffordEquiv.apply_symm_apply z⟩
    apply (reverseClifford_mem_sliceCommonAnnihilator P _).mp
    simpa using hz

/-- Every row, and therefore its full linear span, lies in the common kernel. -/
theorem rowSpace_le_commonKernel (P : Matrix (BooleanInput m) (BooleanInput t) R) :
    (orderedRowSpace P).map spinorSubsetEquiv.toLinearMap ≤ cliffordJointKernel (rowCommonAnnihilator P) := by
  rw [orderedRowSpace, Submodule.map_span]
  apply Submodule.span_le.mpr
  rintro _ ⟨v, ⟨x, rfl⟩, rfl⟩
  change spinorSubsetEquiv (P.row x) ∈ cliffordJointKernel (rowCommonAnnihilator P)
  rw [mem_cliffordJointKernel]
  intro z hz
  exact (mem_rowCommonAnnihilator P z).mp hz x

/-- The common annihilator depends only on the actual row space. -/
theorem rowCommonAnnihilator_eq_of_rowSpace_eq
    {P : Matrix (BooleanInput m) (BooleanInput t) R}
    {Q : Matrix (BooleanInput r) (BooleanInput t) R}
    (hPQ : orderedRowSpace P = orderedRowSpace Q) : rowCommonAnnihilator P = rowCommonAnnihilator Q := by
  have haux {a b : ℕ} {A : Matrix (BooleanInput a) (BooleanInput t) R}
      {B : Matrix (BooleanInput b) (BooleanInput t) R}
      (hAB : orderedRowSpace A ≤ orderedRowSpace B) :
      rowCommonAnnihilator B ≤ rowCommonAnnihilator A := by
    intro z hz
    rw [mem_rowCommonAnnihilator]
    intro x
    have hu : spinorSubsetEquiv (A.row x) ∈ cliffordJointKernel (rowCommonAnnihilator B) :=
      rowSpace_le_commonKernel B (Submodule.mem_map.mpr
        ⟨A.row x, hAB (row_mem_orderedRowSpace A x), rfl⟩)
    exact (mem_cliffordJointKernel _ _).mp hu z hz
  exact le_antisymm (haux hPQ.ge) (haux hPQ.le)

variable {K : Type*} [Field K] [CharZero K]

/-- A nonzero matrix has an isotropic common row annihilator. -/
theorem rowCommonAnnihilator_isotropic
    (P : Matrix (BooleanInput m) (BooleanInput t) K) (hne : P ≠ 0) :
    CliffordIsotropic (rowCommonAnnihilator P) := by
  classical
  obtain ⟨x, hx⟩ := Function.ne_iff.mp hne
  obtain ⟨y, hy⟩ := Function.ne_iff.mp hx
  have hu : spinorSubsetEquiv (P.row x) ≠ 0 := by
    intro h
    have h' := congrFun h ((booleanSubsetEquiv t) y)
    exact hy (by simpa using h')
  intro z hz w hw
  exact spinorAnnihilator_isotropic hu z ((mem_rowCommonAnnihilator P z).mp hz x)
    w ((mem_rowCommonAnnihilator P w).mp hw x)

/-- The complete tensor annihilator supplies the lower bound `t-m`. -/
theorem OrderedMatchgateMatrix.rowCommonAnnihilator_finrank_ge
    {P : Matrix (BooleanInput m) (BooleanInput t) K}
    (hP : OrderedMatchgateMatrix P) (hne : P ≠ 0) :
    t - m ≤ Module.finrank K (rowCommonAnnihilator P) := by
  have hF : MatchgateIdentities (orderedMatrixSubsetSignature P) := (orderedMatchgateMatrix_iff P).mp hP
  have hFn : orderedMatrixSubsetSignature P ≠ 0 := by
    intro hz
    apply hne
    ext x y
    have h := congrFun hz (blockJoin ((booleanSubsetEquiv m) x) (reversePortSubset ((booleanSubsetEquiv t) y)))
    simpa only [orderedMatrixSubsetSignature_blockJoin, Equiv.symm_apply_apply,
      reversePortSubset_reversePortSubset, Pi.zero_apply, Matrix.zero_apply] using h
  have h := hF.sliceCommonAnnihilator_finrank_ge hFn
  rw [← rowCommonAnnihilator_map_reverse P,
    ← (reverseCliffordEquiv.submoduleMap (rowCommonAnnihilator P)).finrank_eq] at h
  exact h

/-- Full-row ordered MGI matrices have exactly the source's common-annihilator
codimension, without a presumed Clifford normalizer. -/
theorem OrderedMatchgateMatrix.rowCommonAnnihilator_finrank
    {P : Matrix (BooleanInput r) (BooleanInput t) K}
    (hP : OrderedMatchgateMatrix P) (hrank : P.rank = 2 ^ r) :
    Module.finrank K (rowCommonAnnihilator P) = t - r := by
  have hne : P ≠ 0 := by
    intro hz
    rw [hz, Matrix.rank_zero] at hrank
    exact (Nat.ne_of_gt (Nat.two_pow_pos r)) hrank.symm
  have hIso := rowCommonAnnihilator_isotropic P hne
  have hle := hIso.finrank_le
  have hLower := hP.rowCommonAnnihilator_finrank_ge hne
  have hKdim := cliffordJointKernel_finrank (rowCommonAnnihilator P) hIso
    (Nat.sub_le t (Module.finrank K (rowCommonAnnihilator P)))
    (by omega : Module.finrank K (rowCommonAnnihilator P) = t - (t - Module.finrank K (rowCommonAnnihilator P)))
  have hbound := Submodule.finrank_mono (rowSpace_le_commonKernel P)
  rw [← (spinorSubsetEquiv.submoduleMap (orderedRowSpace P)).finrank_eq,
    orderedRowSpace, ← Matrix.rank_eq_finrank_span_row, hrank, hKdim] at hbound
  have hp := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hbound
  omega

/-- Any rank-`2^r` MGI row space has common-annihilator dimension `t-r`:
redundant Boolean inputs are removed by the proved Gaussian input-cube theorem. -/
theorem OrderedMatchgateMatrix.rowCommonAnnihilator_finrank_of_rank
    {P : Matrix (BooleanInput m) (BooleanInput t) K}
    (hP : OrderedMatchgateMatrix P) (hrank : P.rank = 2 ^ r) :
    Module.finrank K (rowCommonAnnihilator P) = t - r := by
  obtain ⟨Q, hQ, hQr, hrow⟩ := hP.exists_fullRow_cover hrank
  rw [← rowCommonAnnihilator_eq_of_rowSpace_eq hrow]
  exact hQ.rowCommonAnnihilator_finrank hQr

end
end MatchgateWidth
