import MatchgateWidth.ParitySupportCover

/-!
# Exact disk covers from non-flag support incidence

Source-facing complex graph conclusions for the two geometric branches. The
hypotheses name actual pure coefficient rays and actual rank-two ordered MGI
planes. The outputs include the entire three-dimensional support and a genuine
certified disk graph with the specified ordered signature.
-/
namespace MatchgateWidth
noncomputable section
variable {K : Type*} [Field K] [CharZero K] {t m n : ℕ}

/-- The two-plane rank-four hull in the same ordered subset coordinates used
by the Clifford annihilator branch. -/
theorem exists_rank_four_subset_cover_of_two_planes
    (U : Submodule K (SubsetSignature t K)) (hU : Module.finrank K U = 3)
    {P : Matrix (BooleanInput m) (BooleanInput t) K}
    {Q : Matrix (BooleanInput n) (BooleanInput t) K}
    (hP : OrderedMatchgateMatrix P) (hQ : OrderedMatchgateMatrix Q)
    (hrP : P.rank = 2) (hrQ : Q.rank = 2)
    (hPU : (orderedRowSpace P).map spinorSubsetEquiv.toLinearMap ≤ U)
    (hQU : (orderedRowSpace Q).map spinorSubsetEquiv.toLinearMap ≤ U)
    (hne : orderedRowSpace P ≠ orderedRowSpace Q) :
    ∃ H : Matrix (BooleanInput 2) (BooleanInput t) K,
      OrderedMatchgateMatrix H ∧ H.rank = 4 ∧
      U ≤ (orderedRowSpace H).map spinorSubsetEquiv.toLinearMap := by
  let V := U.map spinorSubsetEquiv.symm.toLinearMap
  have hV : Module.finrank K V = 3 := by
    rw [← (spinorSubsetEquiv.symm.submoduleMap U).finrank_eq]
    exact hU
  have hPV : orderedRowSpace P ≤ V := by
    intro u hu
    refine ⟨spinorSubsetEquiv u, hPU ⟨u, hu, rfl⟩, spinorSubsetEquiv.symm_apply_apply u⟩
  have hQV : orderedRowSpace Q ≤ V := by
    intro u hu
    refine ⟨spinorSubsetEquiv u, hQU ⟨u, hu, rfl⟩, spinorSubsetEquiv.symm_apply_apply u⟩
  obtain ⟨H, hH, hHr, hVH⟩ := exists_rank_four_cover_of_two_planes V hV hP hQ hrP hrQ hPV hQV hne
  refine ⟨H, hH, hHr, ?_⟩
  intro u hu
  exact ⟨spinorSubsetEquiv.symm u, hVH ⟨u, hu, rfl⟩, spinorSubsetEquiv.apply_symm_apply u⟩

/-- Two realized Gaussian planes in a complex three-space yield a literal
rank-four ordered matrix and a certified exact disk graph realizing it. -/
theorem exists_rank_four_disk_cover_of_two_planes
    (U : Submodule ℂ (SubsetSignature t ℂ)) (hU : Module.finrank ℂ U = 3)
    {P : Matrix (BooleanInput m) (BooleanInput t) ℂ}
    {Q : Matrix (BooleanInput n) (BooleanInput t) ℂ}
    (hP : OrderedMatchgateMatrix P) (hQ : OrderedMatchgateMatrix Q)
    (hrP : P.rank = 2) (hrQ : Q.rank = 2)
    (hPU : (orderedRowSpace P).map spinorSubsetEquiv.toLinearMap ≤ U)
    (hQU : (orderedRowSpace Q).map spinorSubsetEquiv.toLinearMap ≤ U)
    (hne : orderedRowSpace P ≠ orderedRowSpace Q) :
    ∃ H : Matrix (BooleanInput 2) (BooleanInput t) ℂ,
      OrderedMatchgateMatrix H ∧ H.rank = 4 ∧
      U ≤ (orderedRowSpace H).map spinorSubsetEquiv.toLinearMap ∧
      DiskRealizable (fun y => orderedMatrixSignature H ((booleanWordEquiv (2+t)).symm y)) := by
  obtain ⟨H, hH, hHr, hUH⟩ := exists_rank_four_subset_cover_of_two_planes U hU hP hQ hrP hrQ hPU hQU hne
  exact ⟨H, hH, hHr, hUH, BooleanMatchgateIdentities.diskRealizable hH⟩

/-- A realized Gaussian plane and two distinct transverse pure rays in a
complex three-space yield a certified exact disk cover of width at most three.
Parity, pure endpoints, a mixed pure point, the common-annihilator dimension,
and the actual cover are all derived from these incidence hypotheses. -/
theorem exists_rank_eight_disk_cover_of_nonflag_rays
    (U : Submodule ℂ (SubsetSignature t ℂ)) (hU : Module.finrank ℂ U = 3)
    {P : Matrix (BooleanInput m) (BooleanInput t) ℂ}
    (hP : OrderedMatchgateMatrix P) (hPr : P.rank = 2)
    (hPU : (orderedRowSpace P).map spinorSubsetEquiv.toLinearMap ≤ U)
    (v s : SubsetSignature t ℂ) (hvU : v ∈ U) (hsU : s ∈ U)
    (hvout : v ∉ (orderedRowSpace P).map spinorSubsetEquiv.toLinearMap)
    (hsout : s ∉ (orderedRowSpace P).map spinorSubsetEquiv.toLinearMap)
    (hsline : s ∉ Submodule.span ℂ {v}) (hv : IsPureSpinor v) (hs : IsPureSpinor s) :
    ∃ r ≤ 3, ∃ H : Matrix (BooleanInput r) (BooleanInput t) ℂ,
      OrderedMatchgateMatrix H ∧ H.rank ≤ 8 ∧
      U ≤ (orderedRowSpace H).map spinorSubsetEquiv.toLinearMap ∧
      DiskRealizable (fun y => orderedMatrixSignature H ((booleanWordEquiv (r+t)).symm y)) := by
  apply ordered_small_cover_disk U
  exact exists_rank_eight_cover_of_nonflag_ray_incidence U hU hP hPr hPU v s hvU hsU hvout hsout hsline hv hs

end
end MatchgateWidth
