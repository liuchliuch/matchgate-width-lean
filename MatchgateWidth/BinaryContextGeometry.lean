import MatchgateWidth.ExactFlagNormalForm
import MatchgateWidth.ConnectionPrimeCompression

/-! # Binary-context geometry without connection-primality
The source Corollary 10.10 needs one Gaussian plane and a transverse pure ray,
without port deficiency or connection-primality. All coordinates remain fixed.
-/
namespace MatchgateWidth
noncomputable section
set_option maxHeartbeats 800000

/-- At most one nonzero coefficient in each domain row and column. -/
def PartialMonomial (A : Matrix (Fin 3) (Fin 3) ℂ) : Prop :=
  (∀ i j k, A i j ≠ 0 → A i k ≠ 0 → j=k) ∧
  (∀ i j k, A i k ≠ 0 → A j k ≠ 0 → i=j)

/-- The source's two possible common exact covers. -/
def BinarySmallCover {t : ℕ} (M : Matrix (Fin 3) (BooleanInput t) ℂ) : Prop :=
  (∃ H : Matrix (BooleanInput 2) (BooleanInput t) ℂ,
    ExactMatchgateMatrix H ∧ H.rank = 4 ∧
    Submodule.span ℂ (Set.range M.row) ≤ orderedRowSpace H) ∨
  (∃ H : Matrix (BooleanInput 3) (BooleanInput t) ℂ,
    ExactMatchgateMatrix H ∧ H.rank = 8 ∧
    Submodule.span ℂ (Set.range M.row) ≤ orderedRowSpace H)

/-- A full-row cover of a three-space has width two or three. No rank-eight
matrix is postulated in a Boolean ambient space too small to contain one. -/
theorem binarySmallCover_of_width_le_three {t : ℕ}
    (M : Matrix (Fin 3) (BooleanInput t) ℂ) (hM : M.rank = 3)
    {r : ℕ} (hr : r ≤ 3) (H : Matrix (BooleanInput r) (BooleanInput t) ℂ)
    (hH : ExactMatchgateMatrix H) (hHr : H.rank = 2^r)
    (hc : baseSubsetSpace M ≤ (orderedRowSpace H).map spinorSubsetEquiv.toLinearMap) :
    BinarySmallCover M := by
  have hcover := (baseSubsetSpace_le_iff M H).mp hc
  have hdim := Submodule.finrank_mono hcover
  change Module.finrank ℂ (Submodule.span ℂ (Set.range M.row)) ≤
    Module.finrank ℂ (Submodule.span ℂ (Set.range H.row)) at hdim
  rw [← Matrix.rank_eq_finrank_span_row, ← Matrix.rank_eq_finrank_span_row, hM, hHr] at hdim
  have hr2 : 2 ≤ r := by
    by_contra hn
    have hh : r = 0 ∨ r = 1 := by omega
    rcases hh with rfl | rfl <;> norm_num at hdim
  have hh : r = 2 ∨ r = 3 := by omega
  rcases hh with rfl | rfl
  · exact Or.inl ⟨H,hH,hHr,hcover⟩
  · exact Or.inr ⟨H,hH,hHr,hcover⟩

/-- Two genuine planes in the original base produce alternative (a). -/
theorem binarySmallCover_of_two_planes {s r t : ℕ}
    (M : Matrix (Fin 3) (BooleanInput t) ℂ) (hM : M.rank = 3)
    (P : Matrix (BooleanInput s) (BooleanInput t) ℂ)
    (Q : Matrix (BooleanInput r) (BooleanInput t) ℂ)
    (hP : ExactMatchgateMatrix P) (hQ : ExactMatchgateMatrix Q)
    (hrP : P.rank = 2) (hrQ : Q.rank = 2)
    (hPM : orderedRowSpace P ≤ Submodule.span ℂ (Set.range M.row))
    (hQM : orderedRowSpace Q ≤ Submodule.span ℂ (Set.range M.row))
    (hne : orderedRowSpace P ≠ orderedRowSpace Q) : BinarySmallCover M := by
  obtain ⟨H,hH,hHr,hc⟩ := exists_rank_four_cover_of_two_planes
    (Submodule.span ℂ (Set.range M.row))
    (by rw [← Matrix.rank_eq_finrank_span_row,hM]) hP.identities hQ.identities
    hrP hrQ hPM hQM hne
  exact Or.inl ⟨H,hH.exactMatrix,hHr,hc⟩

/-- A third transverse pure ray gives the source's pure-pencil branch. -/
theorem binarySmallCover_of_nonflag_pure_ray {s t : ℕ}
    (M : Matrix (Fin 3) (BooleanInput t) ℂ) (hM : M.rank = 3)
    (P : Matrix (BooleanInput s) (BooleanInput t) ℂ)
    (hP : ExactMatchgateMatrix P) (hrP : P.rank = 2)
    (hPM : orderedRowSpace P ≤ Submodule.span ℂ (Set.range M.row))
    (v w : BooleanTable t ℂ) (hvM : v ∈ Submodule.span ℂ (Set.range M.row))
    (hwM : w ∈ Submodule.span ℂ (Set.range M.row))
    (hvP : v ∉ orderedRowSpace P) (hwP : w ∉ orderedRowSpace P)
    (hwv : w ∉ Submodule.span ℂ {v})
    (hv : ExactMatchgate v) (hw : ExactMatchgate w) : BinarySmallCover M := by
  have hinj := (spinorSubsetEquiv (R := ℂ) (t := t)).injective
  have hout (u : BooleanTable t ℂ) (hu : u ∉ orderedRowSpace P) :
      spinorSubsetEquiv u ∉ (orderedRowSpace P).map spinorSubsetEquiv.toLinearMap := by
    rintro ⟨z,hz,he⟩
    exact hu (hinj he ▸ hz)
  have hnzero (u : BooleanTable t ℂ) (hu : u ∉ orderedRowSpace P) : u ≠ 0 := by
    rintro rfl
    exact hu (Submodule.zero_mem _)
  have hpure (u : BooleanTable t ℂ) (hu : u ∉ orderedRowSpace P)
      (he : ExactMatchgate u) : IsPureSpinor (spinorSubsetEquiv u) := by
    apply (isPureSpinor_iff_matchgateIdentities _).mpr
    exact ⟨fun hz => hnzero u hu (hinj (hz.trans (map_zero _).symm)),he.matchgateIdentities⟩
  have hline : spinorSubsetEquiv w ∉ Submodule.span ℂ {spinorSubsetEquiv v} := by
    intro hh
    obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp hh
    apply hwv
    apply Submodule.mem_span_singleton.mpr
    exact ⟨c,hinj (by simpa only [map_smul] using hc)⟩
  obtain ⟨r,hr,H,hH,hHr,hc⟩ := exists_rank_eight_cover_of_nonflag_ray_incidence
    (baseSubsetSpace M) (by rw [baseSubsetSpace_finrank,hM]) hP.identities hrP
    (Submodule.map_mono hPM) (spinorSubsetEquiv v) (spinorSubsetEquiv w)
    ⟨v,hvM,rfl⟩ ⟨w,hwM,rfl⟩ (hout v hvP) (hout w hwP) hline
    (hpure v hvP hv) (hpure w hwP hw)
  exact binarySmallCover_of_width_le_three M hM hr H hH.exactMatrix hHr hc

/-- Without a small cover, pure rays lie in the plane or fixed transverse line. -/
theorem pure_ray_in_plane_or_line_of_no_binarySmallCover {s t : ℕ}
    (M : Matrix (Fin 3) (BooleanInput t) ℂ) (hM : M.rank = 3)
    (P : Matrix (BooleanInput s) (BooleanInput t) ℂ)
    (hP : ExactMatchgateMatrix P) (hrP : P.rank = 2)
    (hPM : orderedRowSpace P ≤ Submodule.span ℂ (Set.range M.row))
    (v : BooleanTable t ℂ) (hvM : v ∈ Submodule.span ℂ (Set.range M.row))
    (hvP : v ∉ orderedRowSpace P) (hv : ExactMatchgate v)
    (hno : ¬ BinarySmallCover M)
    (w : BooleanTable t ℂ) (hwM : w ∈ Submodule.span ℂ (Set.range M.row))
    (hw : ExactMatchgate w) : w ∈ orderedRowSpace P ∨ w ∈ Submodule.span ℂ {v} := by
  by_cases hwP : w ∈ orderedRowSpace P
  · exact Or.inl hwP
  · right
    by_contra hwv
    exact hno (binarySmallCover_of_nonflag_pure_ray M hM P hP hrP hPM v w
      hvM hwM hvP hwP hwv hv hw)

/-- Literal adapted endpoint coordinates of the common base. -/
structure BinaryAdaptedRows {t : ℕ}
    (M : Matrix (Fin 3) (BooleanInput t) ℂ)
    (Q : Matrix (BooleanInput 1) (BooleanInput t) ℂ) : Prop where
  exactPlane : ExactMatchgateMatrix Q
  planeRank : Q.rank = 2
  evenRow : Q.row (fun _ => 0) = M.row 0
  oddRow : Q.row (fun _ => 1) = M.row 1
  evenParity : M.row 0 ∈ booleanParitySubspace t 0
  oddParity : M.row 1 ∈ booleanParitySubspace t 1
  exactThird : ExactMatchgate (M.row 2)

@[simp] theorem transpose_mulVecLin_single_row {t : ℕ}
    (M : Matrix (Fin 3) (BooleanInput t) ℂ) (i : Fin 3) :
    M.transpose.mulVecLin (Pi.single i 1) = M.row i := by
  classical
  ext y
  simp [ ]

theorem fullrank_row_ne_zero {t : ℕ}
    (M : Matrix (Fin 3) (BooleanInput t) ℂ) (hM : M.rank=3) (i : Fin 3) :
    M.row i ≠ 0 := by
  have hi := transpose_injective_of_rank_eq_card M (by simpa using hM)
  intro hz
  have hh : (Pi.single i (1 : ℂ) : Fin 3 → ℂ) = 0 := hi (by simp [hz])
  have := congrFun hh i
  simpa using this

namespace BinaryAdaptedRows
variable {t : ℕ} {M : Matrix (Fin 3) (BooleanInput t) ℂ}
    {Q : Matrix (BooleanInput 1) (BooleanInput t) ℂ}

 theorem plane_space (d : BinaryAdaptedRows M Q) :
    orderedRowSpace Q = Submodule.span ℂ {M.row 0,M.row 1} := by
  rw [orderedRowSpace_one_input,d.evenRow,d.oddRow]

 theorem plane_le_base (d : BinaryAdaptedRows M Q) :
    orderedRowSpace Q ≤ Submodule.span ℂ (Set.range M.row) := by
  rw [d.plane_space]
  apply Submodule.span_le.mpr
  intro u hu
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hu
  rcases hu with rfl | rfl <;> exact Submodule.subset_span ⟨_,rfl⟩

 theorem third_outside (d : BinaryAdaptedRows M Q) (hM : M.rank=3) :
    M.row 2 ∉ orderedRowSpace Q := by
  rw [d.plane_space]
  intro hh
  obtain ⟨a,b,he⟩ := Submodule.mem_span_pair.mp hh
  have hi := transpose_injective_of_rank_eq_card M (by simpa using hM)
  have hc : a • (Pi.single 0 (1 : ℂ) : Fin 3 → ℂ) + b • Pi.single 1 1 = Pi.single 2 1 := by
    apply hi
    simpa only [map_add,map_smul,transpose_mulVecLin_single_row] using he
  have hz := congrFun hc 2
  norm_num at hz

/-- Matchgate parity leaves only the two fixed endpoint axes inside the plane. -/
 theorem pure_in_plane_endpoint (d : BinaryAdaptedRows M Q) (hM : M.rank=3)
    (w : BooleanTable t ℂ) (hwQ : w ∈ orderedRowSpace Q) (hw : ExactMatchgate w) :
    w ∈ Submodule.span ℂ {M.row 0} ∨ w ∈ Submodule.span ℂ {M.row 1} := by
  by_cases hz : w=0
  · simp [hz]
  have hpure : IsPureSpinor (spinorSubsetEquiv w) := by
    apply (isPureSpinor_iff_matchgateIdentities _).mpr
    exact ⟨fun he => hz (spinorSubsetEquiv.injective (he.trans (map_zero _).symm)),hw.matchgateIdentities⟩
  obtain ⟨k,hk,he⟩ := hpure.exists_subset_parity
  have hpar : w ∈ booleanParitySubspace t k := by
    intro y hy
    have hh := congrFun he ((booleanSubsetEquiv t) y)
    have hy' : ((booleanSubsetEquiv t) y).card % 2 ≠ k := hy
    simpa [subsetParityProjection, hy'] using hh.symm
  have he0 := span_pair_parity_endpoint (by decide : (0 : ℕ) ≠ 1)
    (M.row 0) (M.row 1) (fullrank_row_ne_zero M hM 1) d.evenParity d.oddParity
  have he1 := span_pair_parity_endpoint (by decide : (1 : ℕ) ≠ 0)
    (M.row 1) (M.row 0) (fullrank_row_ne_zero M hM 0) d.oddParity d.evenParity
  have hkw : w ∈ orderedRowSpace Q ⊓ booleanParitySubspace t k := ⟨hwQ,hpar⟩
  rcases (show k=0 ∨ k=1 by omega) with rfl | rfl
  · left
    simpa only [d.plane_space,he0] using hkw
  · right
    rw [d.plane_space,Set.pair_comm,he1] at hkw
    exact hkw

/-- The actual pure rays of the whole base are its three coordinate rays when
neither cover exists. This is a conclusion, not an assumed support restriction. -/
 theorem pure_coordinate_of_no_cover (d : BinaryAdaptedRows M Q) (hM : M.rank=3)
    (hno : ¬ BinarySmallCover M) (w : BooleanTable t ℂ)
    (hwM : w ∈ Submodule.span ℂ (Set.range M.row)) (hw : ExactMatchgate w) :
    ∃ i : Fin 3, w ∈ Submodule.span ℂ {M.row i} := by
  rcases pure_ray_in_plane_or_line_of_no_binarySmallCover M hM Q
    d.exactPlane d.planeRank d.plane_le_base (M.row 2)
    (Submodule.subset_span ⟨2,rfl⟩) (d.third_outside hM) d.exactThird hno w hwM hw with hp | hl
  · rcases d.pure_in_plane_endpoint hM w hp hw with h0 | h1
    · exact ⟨0,h0⟩
    · exact ⟨1,h1⟩
  · exact ⟨2,hl⟩

/-- Rank-one exact matrices have a pure generating row; without a small cover,
that whole mode support is one of the three fixed coordinate rays. -/
 theorem rank_one_space_coordinate (d : BinaryAdaptedRows M Q) (hM : M.rank=3)
    (hno : ¬ BinarySmallCover M) {s : ℕ}
    (B : Matrix (BooleanInput s) (BooleanInput t) ℂ)
    (hB : ExactMatchgateMatrix B) (hr : B.rank=1)
    (hBM : orderedRowSpace B ≤ Submodule.span ℂ (Set.range M.row)) :
    ∃ i : Fin 3, orderedRowSpace B ≤ Submodule.span ℂ {M.row i} := by
  have hne : B ≠ 0 := by rintro rfl; simp at hr
  obtain ⟨x,hx⟩ := Function.ne_iff.mp hne
  have hx' : B.row x ≠ 0 := hx
  have hs : Submodule.span ℂ {B.row x} = orderedRowSpace B := by
    apply Submodule.eq_of_le_of_finrank_eq
    · exact Submodule.span_le.mpr (by simpa using row_mem_orderedRowSpace B x)
    · rw [finrank_span_singleton hx']
      exact (show Module.finrank ℂ (Submodule.span ℂ (Set.range B.row)) = 1 by
        rw [← Matrix.rank_eq_finrank_span_row,hr]).symm
  obtain ⟨i,hi⟩ := d.pure_coordinate_of_no_cover hM hno (B.row x)
    (hBM (row_mem_orderedRowSpace B x)) (hB.identities.row x).exactMatchgate
  refine ⟨i,?_⟩
  rw [← hs]
  exact Submodule.span_le.mpr (by simpa using hi)

/-- Every rank-two exact mode support coincides with the original Gaussian
plane if no small cover exists. -/
 theorem rank_two_space_eq (d : BinaryAdaptedRows M Q) (hM : M.rank=3)
    (hno : ¬ BinarySmallCover M) {s : ℕ}
    (B : Matrix (BooleanInput s) (BooleanInput t) ℂ)
    (hB : ExactMatchgateMatrix B) (hr : B.rank=2)
    (hBM : orderedRowSpace B ≤ Submodule.span ℂ (Set.range M.row)) :
    orderedRowSpace B = orderedRowSpace Q := by
  by_contra hn
  exact hno (binarySmallCover_of_two_planes M hM Q B d.exactPlane hB
    d.planeRank hr d.plane_le_base hBM (Ne.symm hn))

end BinaryAdaptedRows
end
end MatchgateWidth
