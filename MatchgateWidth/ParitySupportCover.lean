import MatchgateWidth.SupportCoverGeometry

/-!
# Transverse same-parity pure rays force a small common cover

This is the actual incidence-to-cover step of the non-flag support argument.
A three-dimensional support, a realized Gaussian plane with its two parity
endpoints, and two distinct transverse pure rays in one parity component
supply the mixed pure point. The resulting cover is constructed by the proved
annihilator geometry, not assumed as an incidence axiom.
-/
namespace MatchgateWidth
noncomputable section
variable {K : Type*} [Field K] [CharZero K] {t m : ℕ}

/-- Projection onto the specified actual subset-cardinality parity. -/
def subsetParityProjection (k : ℕ) : Module.End K (SubsetSignature t K) where
  toFun u S := if S.card % 2 = k then u S else 0
  map_add' u v := by ext S; simp only [Pi.add_apply]; split_ifs <;> simp
  map_smul' c u := by ext S; simp only [Pi.smul_apply, RingHom.id_apply]; split_ifs <;> simp

/-- A vector of the first parity in `span{u,v,w}` loses the opposite-parity
coordinate exactly, so it lies in `span{u,v}`. -/
theorem mem_span_pair_of_parity_components
    (u v w s : SubsetSignature t K) (k : ℕ)
    (hu : subsetParityProjection k u = u) (hv : subsetParityProjection k v = v)
    (hw : subsetParityProjection k w = 0) (hs : subsetParityProjection k s = s)
    (hmem : s ∈ Submodule.span K {u, v, w}) : s ∈ Submodule.span K {u, v} := by
  obtain ⟨a, z, hz, heq⟩ := Submodule.mem_span_insert.mp hmem
  obtain ⟨b, c, hbc⟩ := Submodule.mem_span_pair.mp hz
  rw [← hbc] at heq
  have hp := congrArg (subsetParityProjection k) heq
  simp only [map_add, map_smul, hu, hv, hw, hs, smul_zero, add_zero] at hp
  exact Submodule.mem_span_pair.mpr ⟨a, b, hp.symm⟩

/-- A rank-two plane and any transverse vector span an ambient three-space. -/
theorem threeSpace_eq_span_of_gaussian_plane
    (U : Submodule K (SubsetSignature t K)) (hU : Module.finrank K U = 3)
    (P : Matrix (BooleanInput m) (BooleanInput t) K) (hPr : P.rank = 2)
    (u v w : SubsetSignature t K)
    (hplane : (orderedRowSpace P).map spinorSubsetEquiv.toLinearMap = Submodule.span K {u, w})
    (hPU : (orderedRowSpace P).map spinorSubsetEquiv.toLinearMap ≤ U)
    (hv : v ∈ U) (hvout : v ∉ (orderedRowSpace P).map spinorSubsetEquiv.toLinearMap) :
    U = Submodule.span K {u, v, w} := by
  have hdim : Module.finrank K (Submodule.span K {u, w}) = 2 := by
    rw [← hplane, ← (spinorSubsetEquiv.submoduleMap (orderedRowSpace P)).finrank_eq,
      orderedRowSpace, ← Matrix.rank_eq_finrank_span_row, hPr]
  rw [hplane] at hPU hvout
  have hsub : Submodule.span K {u, w} ⊔ Submodule.span K {v} ≤ U := by
    apply sup_le hPU
    apply Submodule.span_le.mpr
    intro x hx
    change x ∈ U
    rw [Set.mem_singleton_iff.mp hx]
    exact hv
  have hdimSup := Submodule.finrank_sup_span_singleton hvout
  rw [hdim] at hdimSup
  have heq : Submodule.span K {u, w} ⊔ Submodule.span K {v} = U :=
    Submodule.eq_of_le_of_finrank_eq hsub (hdimSup.trans hU.symm)
  have hset : ({u, w} : Set (SubsetSignature t K)) ∪ {v} = {u, v, w} := by
    ext x
    simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  rw [← Submodule.span_union, hset] at heq
  exact heq.symm

/-- The source's one-plane/two-transverse-pure-rays incidence supplies a
common cover of the entire three-space of width at most three. Uniqueness of
the Gaussian plane is unnecessary once this incidence configuration is given. -/
theorem exists_rank_eight_cover_of_transverse_pure_rays
    (U : Submodule K (SubsetSignature t K)) (hU : Module.finrank K U = 3)
    {P : Matrix (BooleanInput m) (BooleanInput t) K}
    (hP : OrderedMatchgateMatrix P) (hPr : P.rank = 2)
    (u v w s : SubsetSignature t K)
    (hplane : (orderedRowSpace P).map spinorSubsetEquiv.toLinearMap = Submodule.span K {u, w})
    (hPU : (orderedRowSpace P).map spinorSubsetEquiv.toLinearMap ≤ U)
    (hvU : v ∈ U) (hvout : v ∉ (orderedRowSpace P).map spinorSubsetEquiv.toLinearMap)
    (hsU : s ∈ U) (hsout : s ∉ (orderedRowSpace P).map spinorSubsetEquiv.toLinearMap)
    (hsline : s ∉ Submodule.span K {v})
    (hu : IsPureSpinor u) (hv : IsPureSpinor v) (hs : IsPureSpinor s)
    (k : ℕ) (huk : subsetParityProjection k u = u) (hvk : subsetParityProjection k v = v)
    (hwk : subsetParityProjection k w = 0) (hsk : subsetParityProjection k s = s) :
    ∃ r ≤ 3, ∃ H : Matrix (BooleanInput r) (BooleanInput t) K,
      OrderedMatchgateMatrix H ∧ H.rank = 2 ^ r ∧
      U ≤ (orderedRowSpace H).map spinorSubsetEquiv.toLinearMap := by
  have hspanU := threeSpace_eq_span_of_gaussian_plane U hU P hPr u v w hplane hPU hvU hvout
  have hsuv := mem_span_pair_of_parity_components u v w s k huk hvk hwk hsk (hspanU ▸ hsU)
  obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp hsuv
  have ha : a ≠ 0 := by
    intro ha
    apply hsline
    rw [← hab, ha, zero_smul, zero_add]
    exact Submodule.smul_mem _ b (Submodule.subset_span (by simp))
  have hb : b ≠ 0 := by
    intro hb
    apply hsout
    rw [hplane, ← hab, hb, zero_smul, add_zero]
    exact Submodule.smul_mem _ a (Submodule.subset_span (by simp))
  have humgi := (isPureSpinor_iff_matchgateIdentities u).mp hu
  have hvmgi := (isPureSpinor_iff_matchgateIdentities v).mp hv
  have hsmgi : MatchgateIdentities (a • u + b • v) := by
    rw [hab]
    exact ((isPureSpinor_iff_matchgateIdentities s).mp hs).2
  obtain ⟨r, hr, H, hH, hHr, hcover⟩ := exists_rank_eight_cover_of_three_pure_points
    hP hPr u v w hplane humgi.2 humgi.1 hvmgi.2 hvmgi.1 a b ha hb hsmgi
  exact ⟨r, hr, H, hH, hHr, hspanU.symm ▸ hcover⟩

/-- The parity endpoint and its opposite endpoint are derived from actual
pinned rows of a rank-two ordered MGI matrix. -/
theorem OrderedMatchgateMatrix.exists_subset_parity_endpoints
    {P : Matrix (BooleanInput m) (BooleanInput t) K}
    (hP : OrderedMatchgateMatrix P) (hPr : P.rank = 2) (k : ℕ) (hk : k < 2) :
    ∃ u w : SubsetSignature t K,
      (orderedRowSpace P).map spinorSubsetEquiv.toLinearMap = Submodule.span K {u, w} ∧
      IsPureSpinor u ∧ subsetParityProjection k u = u ∧ subsetParityProjection k w = 0 := by
  obtain ⟨x₀, x₁, b, hb, hx₀, hx₁, h₀, h₁, hspan⟩ := hP.rank_two_pinned_basis hPr
  let u₀ := spinorSubsetEquiv (P.row x₀)
  let u₁ := spinorSubsetEquiv (P.row x₁)
  have hpure (x : BooleanInput m) (hx : P.row x ≠ 0) : IsPureSpinor (spinorSubsetEquiv (P.row x)) := by
    apply (isPureSpinor_iff_matchgateIdentities _).mpr
    constructor
    · exact fun h => hx (spinorSubsetEquiv.injective (h.trans (map_zero _).symm))
    · exact hP.row x
  have heq : (orderedRowSpace P).map spinorSubsetEquiv.toLinearMap = Submodule.span K {u₀, u₁} := by
    rw [hspan, Submodule.map_span]
    simp only [Set.image_insert_eq, Set.image_singleton]
    rfl
  have hu₀zero (S : Finset (Fin t)) (h : S.card % 2 ≠ b) : u₀ S = 0 := by
    exact h₀ ((booleanSubsetEquiv t).symm S) (by simpa [booleanParity] using h)
  have hu₁zero (S : Finset (Fin t)) (h : S.card % 2 = b) : u₁ S = 0 := by
    exact h₁ ((booleanSubsetEquiv t).symm S) (by simpa [booleanParity] using h)
  by_cases hkb : k = b
  · refine ⟨u₀, u₁, heq, hpure x₀ hx₀, ?_, ?_⟩
    · ext S
      by_cases h : S.card % 2 = k
      · simp [subsetParityProjection, h]
      · simp [subsetParityProjection, h, hu₀zero S (by omega)]
    · ext S
      by_cases h : S.card % 2 = k
      · simp [subsetParityProjection, h, hu₁zero S (by omega)]
      · simp [subsetParityProjection, h]
  · refine ⟨u₁, u₀, ?_, hpure x₁ hx₁, ?_, ?_⟩
    · simpa only [Set.pair_comm u₀ u₁] using heq
    · ext S
      by_cases h : S.card % 2 = k
      · simp [subsetParityProjection, h]
      · have hmod := Nat.mod_lt S.card (by decide : 0 < 2)
        simp [subsetParityProjection, h, hu₁zero S (by omega)]
    · ext S
      by_cases h : S.card % 2 = k
      · simp [subsetParityProjection, h, hu₀zero S (by omega)]
      · simp [subsetParityProjection, h]

/-- Complete one-plane non-flag incidence-to-cover theorem: two distinct pure
rays transverse to a realized rank-two plane, lying in the same actual parity
component of a three-space, force an actual width-at-most-three common cover.
The plane's pure endpoints are derived, not hypothesized. -/
theorem exists_rank_eight_cover_of_parity_incidence
    (U : Submodule K (SubsetSignature t K)) (hU : Module.finrank K U = 3)
    {P : Matrix (BooleanInput m) (BooleanInput t) K}
    (hP : OrderedMatchgateMatrix P) (hPr : P.rank = 2)
    (hPU : (orderedRowSpace P).map spinorSubsetEquiv.toLinearMap ≤ U)
    (v s : SubsetSignature t K) (hvU : v ∈ U) (hsU : s ∈ U)
    (hvout : v ∉ (orderedRowSpace P).map spinorSubsetEquiv.toLinearMap)
    (hsout : s ∉ (orderedRowSpace P).map spinorSubsetEquiv.toLinearMap)
    (hsline : s ∉ Submodule.span K {v}) (hv : IsPureSpinor v) (hs : IsPureSpinor s)
    (k : ℕ) (hk : k < 2) (hvk : subsetParityProjection k v = v) (hsk : subsetParityProjection k s = s) :
    ∃ r ≤ 3, ∃ H : Matrix (BooleanInput r) (BooleanInput t) K,
      OrderedMatchgateMatrix H ∧ H.rank = 2 ^ r ∧
      U ≤ (orderedRowSpace H).map spinorSubsetEquiv.toLinearMap := by
  obtain ⟨u, w, hplane, hu, huk, hwk⟩ := hP.exists_subset_parity_endpoints hPr k hk
  exact exists_rank_eight_cover_of_transverse_pure_rays U hU hP hPr u v w s hplane hPU
    hvU hvout hsU hsout hsline hu hv hs k huk hvk hwk hsk

set_option backward.isDefEq.respectTransparency false in
/-- Purity forces one of the two actual subset-parity components. -/
theorem IsPureSpinor.exists_subset_parity {u : SubsetSignature t K} (hu : IsPureSpinor u) :
    ∃ k < 2, subsetParityProjection k u = u := by
  let f : BooleanTable t K := fun x => u ((booleanSubsetEquiv t) x)
  have hf : BooleanMatchgateIdentities f := by
    have h := ((isPureSpinor_iff_matchgateIdentities u).mp hu).2
    simpa only [BooleanMatchgateIdentities, f, Equiv.apply_symm_apply] using h
  obtain ⟨p, a, heq⟩ := hf.exists_pfaffianPivotChart
  refine ⟨booleanParity p, booleanParity_lt_two p, ?_⟩
  ext S
  by_cases hS : S.card % 2 = booleanParity p
  · simp [subsetParityProjection, hS]
  · have hzero : f ((booleanSubsetEquiv t).symm S) = 0 := by
      rw [heq]
      simp only [pfaffianPivotChart, Fin.val_zero, pow_zero, one_mul]
      apply pfaffianChart_odd
      have ho : booleanParity (pfaffianXor p ((booleanSubsetEquiv t).symm S)) = 1 := by
        rw [booleanParity_xor]
        have hp := booleanParity_lt_two p
        have hm := Nat.mod_lt S.card (by decide : 0 < 2)
        simp only [booleanParity, Equiv.apply_symm_apply] at *
        omega
      simpa [pfaffianSelectedPorts, booleanParity, booleanSubsetEquiv] using ho
    have huS : u S = 0 := by simpa [f] using hzero
    simp [subsetParityProjection, hS, huS]

/-- A vector fixed by one parity projection is killed by the other. -/
theorem subsetParityProjection_eq_zero_of_ne {u : SubsetSignature t K} {j k : ℕ}
    (hjk : j ≠ k) (hu : subsetParityProjection j u = u) : subsetParityProjection k u = 0 := by
  ext S
  have h := congrFun hu S
  by_cases hk : S.card % 2 = k
  · have hj : S.card % 2 ≠ j := by omega
    simpa [subsetParityProjection, hk, hj, hjk, Ne.symm hjk] using h.symm
  · simp [subsetParityProjection, hk]

/-- Any pure ray transverse to the same Gaussian plane must have the same
parity as the first transverse pure ray in a three-dimensional support. -/
theorem transverse_pure_ray_same_parity
    (U : Submodule K (SubsetSignature t K)) (hU : Module.finrank K U = 3)
    {P : Matrix (BooleanInput m) (BooleanInput t) K}
    (hP : OrderedMatchgateMatrix P) (hPr : P.rank = 2)
    (hPU : (orderedRowSpace P).map spinorSubsetEquiv.toLinearMap ≤ U)
    (v s : SubsetSignature t K) (hvU : v ∈ U) (hsU : s ∈ U)
    (hvout : v ∉ (orderedRowSpace P).map spinorSubsetEquiv.toLinearMap)
    (hsout : s ∉ (orderedRowSpace P).map spinorSubsetEquiv.toLinearMap)
    (hs : IsPureSpinor s) (k : ℕ) (hk : k < 2) (hvk : subsetParityProjection k v = v) :
    subsetParityProjection k s = s := by
  obtain ⟨u, w, hplane, _, huk, hwk⟩ := hP.exists_subset_parity_endpoints hPr k hk
  have hspanU := threeSpace_eq_span_of_gaussian_plane U hU P hPr u v w hplane hPU hvU hvout
  obtain ⟨j, _, hsj⟩ := hs.exists_subset_parity
  by_cases hjk : j = k
  · simpa only [hjk] using hsj
  · have hsk := subsetParityProjection_eq_zero_of_ne hjk hsj
    have hsSpan : s ∈ Submodule.span K {u, v, w} := hspanU ▸ hsU
    obtain ⟨a, z, hz, heq⟩ := Submodule.mem_span_insert.mp hsSpan
    obtain ⟨b, c, hbc⟩ := Submodule.mem_span_pair.mp hz
    rw [← hbc] at heq
    have hproj := congrArg (subsetParityProjection k) heq
    simp only [map_add, map_smul, huk, hvk, hwk, hsk, smul_zero, add_zero] at hproj
    rw [← add_assoc, ← hproj, zero_add] at heq
    exfalso
    apply hsout
    rw [hplane, heq]
    exact Submodule.smul_mem _ c (Submodule.subset_span (by simp))

/-- The complete non-flag ray-incidence implication without a supplied parity
or endpoint decomposition. A Gaussian plane and two distinct transverse pure
rays in a three-space force an actual ordered cover of width at most three. -/
theorem exists_rank_eight_cover_of_nonflag_ray_incidence
    (U : Submodule K (SubsetSignature t K)) (hU : Module.finrank K U = 3)
    {P : Matrix (BooleanInput m) (BooleanInput t) K}
    (hP : OrderedMatchgateMatrix P) (hPr : P.rank = 2)
    (hPU : (orderedRowSpace P).map spinorSubsetEquiv.toLinearMap ≤ U)
    (v s : SubsetSignature t K) (hvU : v ∈ U) (hsU : s ∈ U)
    (hvout : v ∉ (orderedRowSpace P).map spinorSubsetEquiv.toLinearMap)
    (hsout : s ∉ (orderedRowSpace P).map spinorSubsetEquiv.toLinearMap)
    (hsline : s ∉ Submodule.span K {v}) (hv : IsPureSpinor v) (hs : IsPureSpinor s) :
    ∃ r ≤ 3, ∃ H : Matrix (BooleanInput r) (BooleanInput t) K,
      OrderedMatchgateMatrix H ∧ H.rank = 2 ^ r ∧
      U ≤ (orderedRowSpace H).map spinorSubsetEquiv.toLinearMap := by
  obtain ⟨k, hk, hvk⟩ := hv.exists_subset_parity
  have hsk := transverse_pure_ray_same_parity U hU hP hPr hPU v s hvU hsU hvout hsout hs k hk hvk
  exact exists_rank_eight_cover_of_parity_incidence U hU hP hPr hPU v s hvU hsU hvout hsout
    hsline hv hs k hk hvk hsk

/-- Any cover produced in this branch has a certified exact disk realization
over the source field; no converse from arbitrary plane drawings is used. -/
theorem ordered_small_cover_disk
    (U : Submodule ℂ (SubsetSignature t ℂ))
    (hcover : ∃ r ≤ 3, ∃ H : Matrix (BooleanInput r) (BooleanInput t) ℂ,
      OrderedMatchgateMatrix H ∧ H.rank = 2 ^ r ∧
      U ≤ (orderedRowSpace H).map spinorSubsetEquiv.toLinearMap) :
    ∃ r ≤ 3, ∃ H : Matrix (BooleanInput r) (BooleanInput t) ℂ,
      OrderedMatchgateMatrix H ∧ H.rank ≤ 8 ∧
      U ≤ (orderedRowSpace H).map spinorSubsetEquiv.toLinearMap ∧
      DiskRealizable (fun y => orderedMatrixSignature H ((booleanWordEquiv (r+t)).symm y)) := by
  obtain ⟨r, hr, H, hH, hHr, hU⟩ := hcover
  refine ⟨r, hr, H, hH, ?_, hU, BooleanMatchgateIdentities.diskRealizable hH⟩
  rw [hHr]
  calc
    2 ^ r ≤ 2 ^ 3 := Nat.pow_le_pow_right (by decide) hr
    _ = 8 := by norm_num

end
end MatchgateWidth
