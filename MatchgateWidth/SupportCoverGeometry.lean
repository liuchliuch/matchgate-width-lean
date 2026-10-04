import MatchgateWidth.RowAnnihilatorGeometry
import MatchgateWidth.PurePencilThreePoint

/-!
# Non-flag support incidence produces actual small matchgate covers

The conclusions are explicit ordered MGI matrices and actual row-space
containments. The annihilator dimensions are proved from genuine tensor
identities; no desired cover or spinor-line classification is assumed.
-/
namespace MatchgateWidth
noncomputable section
variable {K : Type*} [Field K] [CharZero K] {t m n k : ℕ}

/-- A lower bound on a genuine common isotropic annihilator gives a cover of
at most the requested width, with small output arities handled automatically. -/
theorem exists_ordered_cover_of_isotropic_codimension
    (U : Submodule K (SubsetSignature t K))
    (L : Submodule K (CliffordVector t K)) (hL : CliffordIsotropic L)
    (hUL : U ≤ cliffordJointKernel L) (hdim : t - k ≤ Module.finrank K L) :
    ∃ r ≤ k, ∃ P : Matrix (BooleanInput r) (BooleanInput t) K,
      OrderedMatchgateMatrix P ∧ P.rank = 2 ^ r ∧
      U ≤ (orderedRowSpace P).map spinorSubsetEquiv.toLinearMap := by
  have hle := hL.finrank_le
  let r := t - Module.finrank K L
  have hrt : r ≤ t := Nat.sub_le _ _
  have hrk : r ≤ k := by dsimp [r]; omega
  obtain ⟨P, hP, hPr, hrow⟩ := isotropic_kernel_cover L hL hrt
    (by dsimp [r]; omega : Module.finrank K L = t - r)
  exact ⟨r, hrk, P, hP, hPr, hrow.symm ▸ hUL⟩

/-- Two large annihilator intersections inside one pure annihilator retain
at least `t-3` common dimensions. -/
theorem triple_annihilator_finrank_lower
    {u v w : SubsetSignature t K} (hu : MatchgateIdentities u) (hune : u ≠ 0)
    (huv : t - 2 ≤ Module.finrank K ↥(spinorAnnihilator u ⊓ spinorAnnihilator v))
    (huw : Module.finrank K ↥(spinorAnnihilator u ⊓ spinorAnnihilator w) = t - 1) :
    t - 3 ≤ Module.finrank K ↥((spinorAnnihilator u ⊓ spinorAnnihilator v) ⊓
      (spinorAnnihilator u ⊓ spinorAnnihilator w)) := by
  let A := spinorAnnihilator u ⊓ spinorAnnihilator v
  let B := spinorAnnihilator u ⊓ spinorAnnihilator w
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq A B
  have hsup := Submodule.finrank_mono
    (show A ⊔ B ≤ spinorAnnihilator u from sup_le inf_le_left inf_le_left)
  rw [hu.annihilator_finrank hune] at hsup
  change t - 2 ≤ Module.finrank K A at huv
  change Module.finrank K B = t - 1 at huw
  change t - 3 ≤ Module.finrank K ↥(A ⊓ B)
  omega

/-- A genuine pure pencil meeting an actual rank-two Gaussian plane in the
ray of `u` has a common ordered matchgate cover of rank at most eight.
No independence or large-arity assumption is needed for this upper bound. -/
theorem exists_rank_eight_cover_of_pencil_annihilator_plane
    {P : Matrix (BooleanInput m) (BooleanInput t) K}
    (hP : OrderedMatchgateMatrix P) (hPr : P.rank = 2)
    (u v w : SubsetSignature t K)
    (hplane : (orderedRowSpace P).map spinorSubsetEquiv.toLinearMap = Submodule.span K {u, w})
    (hu : MatchgateIdentities u) (hune : u ≠ 0)
    (hpencil : t - 2 ≤ Module.finrank K ↥(spinorAnnihilator u ⊓ spinorAnnihilator v)) :
    ∃ r ≤ 3, ∃ H : Matrix (BooleanInput r) (BooleanInput t) K,
      OrderedMatchgateMatrix H ∧ H.rank = 2 ^ r ∧
      Submodule.span K {u, v, w} ≤ (orderedRowSpace H).map spinorSubsetEquiv.toLinearMap := by
  let L := (spinorAnnihilator u ⊓ spinorAnnihilator v) ⊓
    (spinorAnnihilator u ⊓ spinorAnnihilator w)
  have hL : CliffordIsotropic L := by
    intro z hz q hq
    exact spinorAnnihilator_isotropic hune z hz.1.1 q hq.1.1
  have hdim : t - 3 ≤ Module.finrank K L :=
    triple_annihilator_finrank_lower hu hune
      hpencil
      (hP.rank_two_annihilator_intersection hPr u w hplane)
  apply exists_ordered_cover_of_isotropic_codimension (Submodule.span K {u, v, w}) L hL _ hdim
  apply Submodule.span_le.mpr
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · apply (mem_cliffordJointKernel L x).mpr
    intro z hz
    exact hz.1.1
  · apply (mem_cliffordJointKernel L x).mpr
    intro z hz
    exact hz.1.2
  · apply (mem_cliffordJointKernel L x).mpr
    intro z hz
    exact hz.2.2

/-- Pure-pencil specialization using the actual MGI on `u`, `v`, and `u+v`. -/
theorem exists_rank_eight_cover_of_pure_pencil_plane
    {P : Matrix (BooleanInput m) (BooleanInput t) K}
    (hP : OrderedMatchgateMatrix P) (hPr : P.rank = 2)
    (u v w : SubsetSignature t K)
    (hplane : (orderedRowSpace P).map spinorSubsetEquiv.toLinearMap = Submodule.span K {u, w})
    (hu : MatchgateIdentities u) (hune : u ≠ 0)
    (hv : MatchgateIdentities v) (hvne : v ≠ 0)
    (hpencil : MatchgateIdentities (u + v)) :
    ∃ r ≤ 3, ∃ H : Matrix (BooleanInput r) (BooleanInput t) K,
      OrderedMatchgateMatrix H ∧ H.rank = 2 ^ r ∧
      Submodule.span K {u, v, w} ≤ (orderedRowSpace H).map spinorSubsetEquiv.toLinearMap :=
  exists_rank_eight_cover_of_pencil_annihilator_plane hP hPr u v w hplane hu hune
    (hu.pencil_annihilator_finrank_lower hune hv hvne hpencil)

/-- Three distinct projective pure points in one component, represented by
`u`, `v`, and a genuinely mixed combination, together with the Gaussian
plane through `u,w`, produce the rank-at-most-eight common cover. -/
theorem exists_rank_eight_cover_of_three_pure_points
    {P : Matrix (BooleanInput m) (BooleanInput t) K}
    (hP : OrderedMatchgateMatrix P) (hPr : P.rank = 2)
    (u v w : SubsetSignature t K)
    (hplane : (orderedRowSpace P).map spinorSubsetEquiv.toLinearMap = Submodule.span K {u, w})
    (hu : MatchgateIdentities u) (hune : u ≠ 0)
    (hv : MatchgateIdentities v) (hvne : v ≠ 0)
    (a b : K) (ha : a ≠ 0) (hb : b ≠ 0)
    (hthird : MatchgateIdentities (a • u + b • v)) :
    ∃ r ≤ 3, ∃ H : Matrix (BooleanInput r) (BooleanInput t) K,
      OrderedMatchgateMatrix H ∧ H.rank = 2 ^ r ∧
      Submodule.span K {u, v, w} ≤ (orderedRowSpace H).map spinorSubsetEquiv.toLinearMap :=
  exists_rank_eight_cover_of_pencil_annihilator_plane hP hPr u v w hplane hu hune
    (hu.three_point_annihilator_finrank_lower hune hv hvne ha hb hthird)

/-- Two distinct realized Gaussian planes in a three-dimensional support
space give an actual rank-four cover of that whole support space. -/
theorem exists_rank_four_cover_of_two_planes
    (U : Submodule K (BooleanTable t K)) (hU : Module.finrank K U = 3)
    {P : Matrix (BooleanInput m) (BooleanInput t) K}
    {Q : Matrix (BooleanInput n) (BooleanInput t) K}
    (hP : OrderedMatchgateMatrix P) (hQ : OrderedMatchgateMatrix Q)
    (hrP : P.rank = 2) (hrQ : Q.rank = 2)
    (hPU : orderedRowSpace P ≤ U) (hQU : orderedRowSpace Q ≤ U)
    (hne : orderedRowSpace P ≠ orderedRowSpace Q) :
    ∃ H : Matrix (BooleanInput 2) (BooleanInput t) K,
      OrderedMatchgateMatrix H ∧ H.rank = 4 ∧ U ≤ orderedRowSpace H := by
  have hdP : Module.finrank K (orderedRowSpace P) = 2 := by
    rw [orderedRowSpace, ← Matrix.rank_eq_finrank_span_row, hrP]
  have hdQ : Module.finrank K (orderedRowSpace Q) = 2 := by
    rw [orderedRowSpace, ← Matrix.rank_eq_finrank_span_row, hrQ]
  have hsup : orderedRowSpace P ⊔ orderedRowSpace Q ≤ U := sup_le hPU hQU
  have hsupdim := Submodule.finrank_mono hsup
  rw [hU] at hsupdim
  have hnotle : ¬Module.finrank K ↥(orderedRowSpace P ⊔ orderedRowSpace Q) ≤ 2 := by
    intro h
    have hp : orderedRowSpace P = orderedRowSpace P ⊔ orderedRowSpace Q :=
      Submodule.eq_of_le_of_finrank_le le_sup_left (hdP ▸ h)
    have hq : orderedRowSpace Q = orderedRowSpace P ⊔ orderedRowSpace Q :=
      Submodule.eq_of_le_of_finrank_le le_sup_right (hdQ ▸ h)
    exact hne (hp.trans hq.symm)
  have hsupU : orderedRowSpace P ⊔ orderedRowSpace Q = U := by
    apply Submodule.eq_of_le_of_finrank_eq hsup
    omega
  have hmeet : orderedRowSpace P ⊓ orderedRowSpace Q ≠ ⊥ := by
    intro hbot
    have hsum := Submodule.finrank_sup_add_finrank_inf_eq (orderedRowSpace P) (orderedRowSpace Q)
    rw [hbot, finrank_bot, hdP, hdQ] at hsum
    omega
  obtain ⟨H, hH, hHr, hHL⟩ := exists_rank_two_gaussian_hull hP hQ hrP hrQ hne hmeet
  exact ⟨H, hH, hHr, hsupU ▸ hHL⟩

end
end MatchgateWidth
