import MatchgateWidth.MatchgateRowAnnihilator

/-! # Row-space annihilator geometry
Common annihilators depend on actual coefficient subspaces; two generators give
exactly the intersection of their annihilators. Every ordered-MGI row space is
the entire common kernel, and rank-two spaces give the `t-1` endpoint formula.
-/
namespace MatchgateWidth
noncomputable section
variable {R : Type*} [CommRing R] {m t r : ℕ}

/-- Common annihilator of an arbitrary genuine coefficient-spinor subspace. -/
def commonSpinorAnnihilator (U : Submodule R (SubsetSignature t R)) :
    Submodule R (CliffordVector t R) := ⨅ u : U, spinorAnnihilator (u : SubsetSignature t R)

@[simp] theorem mem_commonSpinorAnnihilator (U : Submodule R (SubsetSignature t R))
    (z : CliffordVector t R) :
    z ∈ commonSpinorAnnihilator U ↔ ∀ u ∈ U, signedCliffordAction z u = 0 := by
  simp [commonSpinorAnnihilator, spinorAnnihilator]

/-- Common annihilation can equivalently be tested as containment in one operator kernel. -/
theorem mem_commonSpinorAnnihilator_iff_le (U : Submodule R (SubsetSignature t R))
    (z : CliffordVector t R) :
    z ∈ commonSpinorAnnihilator U ↔ U ≤ LinearMap.ker (signedCliffordAction z) :=
  mem_commonSpinorAnnihilator U z

/-- Common annihilation of a two-generated plane is precisely the annihilator intersection. -/
theorem commonSpinorAnnihilator_span_pair (u v : SubsetSignature t R) :
    commonSpinorAnnihilator (Submodule.span R {u, v}) = spinorAnnihilator u ⊓ spinorAnnihilator v := by
  ext z
  rw [mem_commonSpinorAnnihilator_iff_le, Submodule.span_le]
  simp only [Set.insert_subset_iff, Set.singleton_subset_iff, Submodule.mem_inf]
  rfl

/-- Literal matrix-row and coefficient-subspace common annihilators coincide. -/
theorem rowCommonAnnihilator_eq_common
    (P : Matrix (BooleanInput m) (BooleanInput t) R) :
    rowCommonAnnihilator P = commonSpinorAnnihilator ((orderedRowSpace P).map spinorSubsetEquiv.toLinearMap) := by
  ext z
  rw [mem_commonSpinorAnnihilator]
  constructor
  · intro hz u hu
    exact (mem_cliffordJointKernel _ _).mp (rowSpace_le_commonKernel P hu) z hz
  · intro hz
    rw [mem_rowCommonAnnihilator]
    intro x
    exact hz (spinorSubsetEquiv (P.row x))
      (Submodule.mem_map.mpr ⟨P.row x, row_mem_orderedRowSpace P x, rfl⟩)

/-- Two spanning coefficient spinors compute the matrix's common annihilator exactly. -/
theorem rowCommonAnnihilator_eq_inf_of_span
    (P : Matrix (BooleanInput m) (BooleanInput t) R) (u v : SubsetSignature t R)
    (hspan : (orderedRowSpace P).map spinorSubsetEquiv.toLinearMap = Submodule.span R {u, v}) :
    rowCommonAnnihilator P = spinorAnnihilator u ⊓ spinorAnnihilator v := by
  rw [rowCommonAnnihilator_eq_common, hspan, commonSpinorAnnihilator_span_pair]

variable {K : Type*} [Field K] [CharZero K]

/-- An ordered-MGI row space fills its entire common Clifford kernel. -/
theorem OrderedMatchgateMatrix.rowSpace_eq_commonKernel
    {P : Matrix (BooleanInput m) (BooleanInput t) K}
    (hP : OrderedMatchgateMatrix P) (hrank : P.rank = 2 ^ r) :
    (orderedRowSpace P).map spinorSubsetEquiv.toLinearMap = cliffordJointKernel (rowCommonAnnihilator P) := by
  have hne : P ≠ 0 := by
    intro hz
    rw [hz, Matrix.rank_zero] at hrank
    exact (Nat.ne_of_gt (Nat.two_pow_pos r)) hrank.symm
  have hwidth : r ≤ t := by
    have h := P.rank_le_card_width
    rw [hrank] at h
    have h' : 2 ^ r ≤ 2 ^ t := by simpa [BooleanInput] using h
    exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp h'
  have hIso := rowCommonAnnihilator_isotropic P hne
  have hdim := hP.rowCommonAnnihilator_finrank_of_rank hrank
  have hk := cliffordJointKernel_finrank (rowCommonAnnihilator P) hIso hwidth hdim
  apply Submodule.eq_of_le_of_finrank_eq (rowSpace_le_commonKernel P)
  rw [← (spinorSubsetEquiv.submoduleMap (orderedRowSpace P)).finrank_eq,
    orderedRowSpace, ← Matrix.rank_eq_finrank_span_row, hrank, hk]

/-- The exact `t-1` common-annihilator formula for any two spanning rows of a
rank-two ordered matchgate space. This includes the opposite-parity endpoints
used in source Theorem 10.7 and requires no assumed Pin covariance. -/
theorem OrderedMatchgateMatrix.rank_two_annihilator_intersection
    {P : Matrix (BooleanInput m) (BooleanInput t) K}
    (hP : OrderedMatchgateMatrix P) (hrank : P.rank = 2)
    (u v : SubsetSignature t K)
    (hspan : (orderedRowSpace P).map spinorSubsetEquiv.toLinearMap = Submodule.span K {u, v}) :
    Module.finrank K (spinorAnnihilator u ⊓ spinorAnnihilator v : Submodule K (CliffordVector t K)) = t - 1 := by
  rw [← rowCommonAnnihilator_eq_inf_of_span P u v hspan]
  apply hP.rowCommonAnnihilator_finrank_of_rank
  simpa using hrank

end
end MatchgateWidth
