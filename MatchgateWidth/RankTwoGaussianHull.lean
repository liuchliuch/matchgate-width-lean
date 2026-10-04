import MatchgateWidth.FullRowMatchgateDecoder

/-!
# Rank-two ordered Gaussian row spaces

Algebraic statements about the literal ordered matchgate identities. No
correspondence with graph-realized signatures is assumed here.
-/
namespace MatchgateWidth
noncomputable section
open scoped symmDiff

private theorem empty_xor {n : ℕ} (S : Finset (Fin n)) : ∅ ∆ S = S := bot_symmDiff S
private theorem xor_empty {n : ℕ} (S : Finset (Fin n)) : S ∆ ∅ = S := symmDiff_bot S

variable {R : Type*} [CommRing R] {r t : ℕ}

/-- The ordinary row space, retaining the actual Boolean output coordinates. -/
def orderedRowSpace (P : Matrix (BooleanInput r) (BooleanInput t) R) :
    Submodule R (BooleanTable t R) := Submodule.span R (Set.range P.row)

theorem row_mem_orderedRowSpace (P : Matrix (BooleanInput r) (BooleanInput t) R)
    (x : BooleanInput r) : P.row x ∈ orderedRowSpace P :=
  Submodule.subset_span ⟨x, rfl⟩

/-- Pinning every input leaves an actual pure output signature. The reversal
in the definition of an ordered matrix is explicitly undone. -/
theorem OrderedMatchgateMatrix.row
    {P : Matrix (BooleanInput r) (BooleanInput t) R}
    (hP : OrderedMatchgateMatrix P) (x : BooleanInput r) :
    BooleanMatchgateIdentities (P.row x) := by
  classical
  let e : Fin t ↪ Fin (r + t) := Fin.natAddEmb r
  have he : StrictMono e := by intro i j h; exact (Fin.natAdd_lt_natAdd_iff r).mpr h
  have h := ((orderedMatchgateMatrix_iff P).mp hP).ordered_pin e he
    (blockJoin (booleanSubsetEquiv r x) ∅)
  have hh : MatchgateIdentities (fun S =>
      P x ((booleanSubsetEquiv t).symm (reversePortSubset S))) := by
    have heq (S : Finset (Fin t)) :
        S.map e ∆ blockJoin (booleanSubsetEquiv r x) ∅ =
          blockJoin (booleanSubsetEquiv r x) S := by
      have hmap : S.map e = blockJoin (∅ : Finset (Fin r)) S := by
        simp [e, blockJoin]
      rw [hmap, blockJoin_symmDiff]
      simp only [empty_xor, xor_empty]
    simpa only [heq, orderedMatrixSubsetSignature_blockJoin,
      Equiv.symm_apply_apply] using h
  have hh' := hh.reverse
  simpa only [BooleanMatchgateIdentities, reversePortSubset_reversePortSubset,
    Matrix.row_apply] using hh'

/-- Scalar multiples of pure Boolean signatures remain pure. -/
theorem BooleanMatchgateIdentities.smul {u : BooleanTable t R}
    (hu : BooleanMatchgateIdentities u) (c : R) :
    BooleanMatchgateIdentities (c • u) := hu.const_mul c

variable {K : Type*} [Field K]

/-- The Gaussian chart can be taken at any specified nonzero matrix entry. -/
theorem OrderedMatchgateMatrix.exists_gaussian_chart_at
    {P : Matrix (BooleanInput r) (BooleanInput t) K}
    (hP : OrderedMatchgateMatrix P) (p : BooleanInput r) (q : BooleanInput t)
    (hpq : P p q ≠ 0) :
    ∃ (A : Matrix (Fin r) (Fin r) K) (B : Matrix (Fin r) (Fin t) K)
      (D : Matrix (Fin t) (Fin t) K),
      (∀ i j, A i j = -A j i) ∧ (∀ i j, D i j = -D j i) ∧
      (∀ i, A i i = 0) ∧ (∀ i, D i i = 0) ∧
      ∀ x y, P x y = P p q * gaussianOrderedMatrix A B D
        (pfaffianXor p x) (pfaffianXor q y) := by
  let pivot := matrixBoundaryWord p q
  let F : SubsetSignature (r+t) K := fun S =>
    orderedMatrixSignature P ((booleanSubsetEquiv (r+t)).symm S)
  have hF : MatchgateIdentities F := hP
  have hp : F (booleanSubsetEquiv (r+t) pivot) ≠ 0 := by
    simpa only [F, Equiv.symm_apply_apply, pivot,
      orderedMatrixSignature_boundaryWord] using hpq
  let a := mgiChartParameters (subsetPivot F (booleanSubsetEquiv (r+t) pivot))
  have ha (z : BooleanInput (r+t)) :
      orderedMatrixSignature P z = pfaffianPivotChart pivot (fun _ => 0) a z := by
    simpa only [F, Equiv.symm_apply_apply, a] using hF.eq_pfaffianPivotChart pivot hp z
  have hc : a none = P p q := by
    simp only [a, mgiChartParameters, subsetPivot, empty_xor, F,
      Equiv.symm_apply_apply, pivot, orderedMatrixSignature_boundaryWord]
  let M := pfaffianChartMatrix a
  have hM : ∀ i j, M i j = -M j i := fun i j => pfaffianChartMatrix_skew a j i
  refine ⟨boundaryInputBlock M, boundaryCrossBlock M, boundaryOutputBlock M,
    (fun i j => hM _ _), (fun i j => hM _ _),
    (fun i => pfaffianChartMatrix_diag a _),
    (fun i => pfaffianChartMatrix_diag a _), ?_⟩
  intro x y
  have h := ha (matrixBoundaryWord x y)
  rw [orderedMatrixSignature_boundaryWord] at h
  rw [gaussian_boundary_value M hM, h]
  simp only [pfaffianPivotChart, Fin.val_zero, pow_zero, one_mul,
    pfaffianChart, hc]
  congr 1
  change pfaffianList M _ = pfaffianList M _
  congr 1
  change (booleanSubsetEquiv (r+t) (pfaffianXor pivot (matrixBoundaryWord x y))).sort _ = _
  rw [matrixBoundaryWord_xor]
  simp [pivot, matrixBoundaryWord]


/-- Output parity, expressed without selecting a chart. -/
def booleanParity (z : BooleanInput t) : ℕ := (booleanSubsetEquiv t z).card % 2

theorem booleanParity_lt_two (z : BooleanInput t) : booleanParity z < 2 :=
  Nat.mod_lt _ (by decide)

theorem booleanParity_xor (p z : BooleanInput t) :
    booleanParity (pfaffianXor p z) = (booleanParity p + booleanParity z) % 2 := by
  classical
  unfold booleanParity
  rw [booleanSubsetEquiv_xor]
  let A := booleanSubsetEquiv t p
  let B := booleanSubsetEquiv t z
  have hA := Finset.card_sdiff_add_card_inter A B
  have hB := Finset.card_sdiff_add_card_inter B A
  rw [Finset.inter_comm B A] at hB
  have hd : Disjoint (A \ B) (B \ A) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    exact (Finset.mem_sdiff.mp hi).2 (Finset.mem_sdiff.mp hj).1
  change (A ∆ B).card % 2 = (A.card % 2 + B.card % 2) % 2
  rw [Finset.symmDiff_def, Finset.card_union_of_disjoint hd]
  omega

@[simp] theorem booleanParity_zero : booleanParity (fun _ : Fin t => 0) = 0 := by
  simp [booleanParity]

/-- A Boolean word selecting exactly one mode. -/
def singletonWord (i : Fin t) : BooleanInput t := (booleanSubsetEquiv t).symm {i}

@[simp] theorem booleanSubsetEquiv_singletonWord (i : Fin t) :
    booleanSubsetEquiv t (singletonWord i) = {i} := Equiv.apply_symm_apply _ _

@[simp] theorem booleanParity_singletonWord (i : Fin t) :
    booleanParity (singletonWord i) = 1 := by simp [booleanParity]

theorem gaussianOrderedMatrix_odd
    (A : Matrix (Fin r) (Fin r) K) (B : Matrix (Fin r) (Fin t) K)
    (D : Matrix (Fin t) (Fin t) K) (x : BooleanInput r) (y : BooleanInput t)
    (hodd : (booleanParity x + booleanParity y) % 2 = 1) :
    gaussianOrderedMatrix A B D x y = 0 := by
  apply pfaffianList_odd
  simp only [List.length_append, List.length_map, List.length_reverse,
    gaussianSubsetList_length]
  simpa [booleanParity, Nat.add_mod] using hodd

@[simp] theorem gaussianOrderedMatrix_zero_zero
    (A : Matrix (Fin r) (Fin r) K) (B : Matrix (Fin r) (Fin t) K)
    (D : Matrix (Fin t) (Fin t) K) :
    gaussianOrderedMatrix A B D (fun _ => 0) (fun _ => 0) = 1 := by
  simp [gaussianOrderedMatrix, gaussianFullPlanarPfaffianMatrix,
    gaussianSubsetList_eq_sort, gaussianFullPfaffian]

@[simp] theorem gaussianOrderedMatrix_singleton_zero
    (A : Matrix (Fin r) (Fin r) K) (B : Matrix (Fin r) (Fin t) K)
    (D : Matrix (Fin t) (Fin t) K) (i : Fin r) :
    gaussianOrderedMatrix A B D (singletonWord i) (fun _ => 0) = 0 := by
  exact gaussianOrderedMatrix_odd A B D _ _ (by simp)

@[simp] theorem gaussianOrderedMatrix_singleton_singleton
    (A : Matrix (Fin r) (Fin r) K) (B : Matrix (Fin r) (Fin t) K)
    (D : Matrix (Fin t) (Fin t) K) (i : Fin r) (j : Fin t) :
    gaussianOrderedMatrix A B D (singletonWord i) (singletonWord j) = B i j := by
  simp [gaussianOrderedMatrix, gaussianFullPlanarPfaffianMatrix,
    gaussianSubsetList_eq_sort, gaussianFullPfaffian, gaussianFullMatrix]

/-- A rank-two row space is spanned by any two rows with a triangular nonzero
coordinate minor. -/
theorem orderedRowSpace_eq_span_pair_of_rank_two
    (P : Matrix (BooleanInput r) (BooleanInput t) K) (hP : P.rank = 2)
    (x₀ x₁ : BooleanInput r) (y₀ y₁ : BooleanInput t)
    (h00 : P x₀ y₀ ≠ 0) (h10 : P x₁ y₀ = 0) (h11 : P x₁ y₁ ≠ 0) :
    orderedRowSpace P = Submodule.span K ({P.row x₀, P.row x₁} : Set (BooleanTable t K)) := by
  let v : Fin 2 → BooleanTable t K := ![P.row x₀, P.row x₁]
  have hv : LinearIndependent K v := by
    rw [linearIndependent_fin2]
    constructor
    · intro hz
      exact h11 (congrFun hz y₁)
    · intro a ha
      have h := congrFun ha y₀
      change a * P x₁ y₀ = P x₀ y₀ at h
      rw [h10, mul_zero] at h
      exact h00 h.symm
  have hvset : Set.range v = {P.row x₀, P.row x₁} := by
    ext z
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp [v]
    · rintro (rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
  symm
  apply Submodule.eq_of_le_of_finrank_eq
  · apply Submodule.span_le.mpr
    rintro z (rfl | rfl) <;> exact row_mem_orderedRowSpace P _
  · rw [← hvset, finrank_span_eq_card hv]
    change 2 = Module.finrank K (Submodule.span K (Set.range P.row))
    rw [← Matrix.rank_eq_finrank_span_row, hP]

variable [CharZero K]

/-- The two parity lines of a rank-two MGI matrix are spanned by actual
pinned rows. This proves the needed rank-two canonical-form consequence. -/
theorem OrderedMatchgateMatrix.rank_two_pinned_basis
    {P : Matrix (BooleanInput r) (BooleanInput t) K}
    (hP : OrderedMatchgateMatrix P) (hr : P.rank = 2) :
    ∃ (x₀ x₁ : BooleanInput r) (k : ℕ), k < 2 ∧
      P.row x₀ ≠ 0 ∧ P.row x₁ ≠ 0 ∧
      (∀ y, booleanParity y ≠ k → P x₀ y = 0) ∧
      (∀ y, booleanParity y = k → P x₁ y = 0) ∧
      orderedRowSpace P = Submodule.span K ({P.row x₀, P.row x₁} : Set (BooleanTable t K)) := by
  classical
  obtain ⟨p, q, c, A, B, D, hA, hD, _, _, heq⟩ := hP.exists_gaussian_chart
  have hPeq : P = c • (gaussianOrderedMatrix A B D).submatrix
      (booleanXorEquiv p) (booleanXorEquiv q) := by
    ext x y
    exact heq x y
  have hc : c ≠ 0 := by
    intro hz
    rw [hPeq, hz, zero_smul, Matrix.rank_zero] at hr
    norm_num at hr
  have hGr : (gaussianOrderedMatrix A B D).rank = 2 := by
    rwa [hPeq, rank_scaled_xor _ p q hc] at hr
  have hB : B ≠ 0 := by
    intro hz
    rw [gaussianOrderedMatrix_rank A B D hA hD, hz, Matrix.rank_zero] at hGr
    norm_num at hGr
  obtain ⟨i, j, hij⟩ : ∃ i j, B i j ≠ 0 := by
    by_contra h
    push Not at h
    exact hB (by ext i j; exact h i j)
  let x₁ := pfaffianXor p (singletonWord i)
  let y₁ := pfaffianXor q (singletonWord j)
  have h00 : P p q = c := by rw [heq]; simp
  have h10 : P x₁ q = 0 := by rw [heq]; simp [x₁]
  have h11 : P x₁ y₁ = c * B i j := by rw [heq]; simp [x₁, y₁]
  refine ⟨p, x₁, booleanParity q, booleanParity_lt_two q, ?_, ?_, ?_, ?_, ?_⟩
  · intro hz
    exact hc (h00.symm.trans (congrFun hz q))
  · intro hz
    exact mul_ne_zero hc hij (h11.symm.trans (congrFun hz y₁))
  · intro y hy
    rw [heq]
    have ho : (booleanParity (pfaffianXor p p) + booleanParity (pfaffianXor q y)) % 2 = 1 := by
      simp only [pfaffianXor_self, booleanParity_zero, zero_add, booleanParity_xor]
      have := booleanParity_lt_two q
      have := booleanParity_lt_two y
      omega
    rw [gaussianOrderedMatrix_odd A B D _ _ ho, mul_zero]
  · intro y hy
    rw [heq]
    have ho : (booleanParity (pfaffianXor p x₁) + booleanParity (pfaffianXor q y)) % 2 = 1 := by
      simp only [x₁, pfaffianXor_involutive, booleanParity_singletonWord, booleanParity_xor, hy]
      have := booleanParity_lt_two q
      omega
    rw [gaussianOrderedMatrix_odd A B D _ _ ho, mul_zero]
  · exact orderedRowSpace_eq_span_pair_of_rank_two P hr p x₁ q y₁
      (h00 ▸ hc) h10 (h11 ▸ mul_ne_zero hc hij)


/-- Projection onto one of the two literal output-parity classes. -/
def outputParityProjection (k : ℕ) : BooleanTable t K →ₗ[K] BooleanTable t K where
  toFun u y := if booleanParity y = k then u y else 0
  map_add' u v := by ext y; simp only [Pi.add_apply]; split_ifs <;> simp
  map_smul' a u := by ext y; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; split_ifs <;> simp

omit [CharZero K] in
theorem outputParityProjection_add (u : BooleanTable t K) :
    outputParityProjection 0 u + outputParityProjection 1 u = u := by
  ext y
  have hy := booleanParity_lt_two y
  by_cases h : booleanParity y = 0
  · simp [outputParityProjection, h]
  · have h' : booleanParity y = 1 := by omega
    simp [outputParityProjection, h']

/-- Every parity component of a rank-two row-space vector is a scalar
multiple of an actual pinned input row. -/
theorem OrderedMatchgateMatrix.rank_two_parityProjection_is_row
    {P : Matrix (BooleanInput r) (BooleanInput t) K}
    (hP : OrderedMatchgateMatrix P) (hr : P.rank = 2)
    (k : ℕ) (hk : k < 2) (u : BooleanTable t K) (hu : u ∈ orderedRowSpace P) :
    ∃ (x : BooleanInput r) (a : K), outputParityProjection k u = a • P.row x := by
  obtain ⟨x₀, x₁, b, hb, _, _, h₀, h₁, hspan⟩ := hP.rank_two_pinned_basis hr
  rw [hspan] at hu
  obtain ⟨a₀, a₁, rfl⟩ := Submodule.mem_span_pair.mp hu
  by_cases hkb : k = b
  · refine ⟨x₀, a₀, ?_⟩
    ext y
    by_cases hy : booleanParity y = b
    · simp [outputParityProjection, hkb, hy, h₁ y hy]
    · simp [outputParityProjection, hkb, hy, h₀ y hy]
  · refine ⟨x₁, a₁, ?_⟩
    ext y
    by_cases hy : booleanParity y = b
    · have hyk : booleanParity y ≠ k := by omega
      simp [outputParityProjection, hyk, h₁ y hy]
    · have hyk : booleanParity y = k := by have := booleanParity_lt_two y; omega
      simp [outputParityProjection, hyk, h₀ y hy]

/-- Rank-two row spaces are parity-invariant, and their homogeneous members
are pure; both facts follow from actual pinned rows rather than an assumed
spinor normal form. -/
theorem OrderedMatchgateMatrix.rank_two_parityProjection
    {P : Matrix (BooleanInput r) (BooleanInput t) K}
    (hP : OrderedMatchgateMatrix P) (hr : P.rank = 2)
    (k : ℕ) (hk : k < 2) (u : BooleanTable t K) (hu : u ∈ orderedRowSpace P) :
    outputParityProjection k u ∈ orderedRowSpace P ∧
      BooleanMatchgateIdentities (outputParityProjection k u) := by
  obtain ⟨x, a, h⟩ := hP.rank_two_parityProjection_is_row hr k hk u hu
  rw [h]
  exact ⟨Submodule.smul_mem _ a (row_mem_orderedRowSpace P x), (hP.row x).smul a⟩

/-- A nonzero intersection of rank-two ordered MGI row spaces contains a
nonzero homogeneous pure vector. Distinctness is not needed for this step. -/
theorem exists_pure_common_row_of_rank_two
    {s : ℕ} {P : Matrix (BooleanInput r) (BooleanInput t) K}
    {Q : Matrix (BooleanInput s) (BooleanInput t) K}
    (hP : OrderedMatchgateMatrix P) (hQ : OrderedMatchgateMatrix Q)
    (hrP : P.rank = 2) (hrQ : Q.rank = 2)
    (hmeet : orderedRowSpace P ⊓ orderedRowSpace Q ≠ ⊥) :
    ∃ u : BooleanTable t K, u ≠ 0 ∧ BooleanMatchgateIdentities u ∧
      u ∈ orderedRowSpace P ∧ u ∈ orderedRowSpace Q ∧
      ∃ k < 2, outputParityProjection k u = u := by
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hmeet
  obtain ⟨k, hk, hkv⟩ : ∃ k < 2, outputParityProjection k v ≠ 0 := by
    by_cases h : outputParityProjection 0 v = 0
    · refine ⟨1, by decide, ?_⟩
      intro h'
      have he := outputParityProjection_add v
      rw [h, h', zero_add] at he
      exact hv0 he.symm
    · exact ⟨0, by decide, h⟩
  have hp := hP.rank_two_parityProjection hrP k hk v hv.1
  have hq := hQ.rank_two_parityProjection hrQ k hk v hv.2
  refine ⟨outputParityProjection k v, hkv, hp.2, hp.1, hq.1, k, hk, ?_⟩
  ext y
  by_cases hy : booleanParity y = k <;> simp [outputParityProjection, hy]

/-- If the vacuum belongs to a rank-two ordered MGI row space, one actual
pinned row is a nonzero multiple of the vacuum. -/
theorem OrderedMatchgateMatrix.rank_two_vacuum_pinned_row
    {P : Matrix (BooleanInput r) (BooleanInput t) K}
    (hP : OrderedMatchgateMatrix P) (hr : P.rank = 2)
    (hv : (fun z : BooleanInput t => if (fun _ => 0) = z then (1 : K) else 0) ∈
      orderedRowSpace P) :
    ∃ x : BooleanInput r, P x (fun _ => 0) ≠ 0 ∧
      ∀ y, P x y = P x (fun _ => 0) * (if (fun _ => 0) = y then 1 else 0) := by
  classical
  let v : BooleanTable t K := fun z => if (fun _ => 0) = z then 1 else 0
  have hp : outputParityProjection 0 v = v := by
    ext y
    by_cases hy : (fun _ : Fin t => (0 : Fin 2)) = y
    · subst y; simp [outputParityProjection, v]
    · simp [outputParityProjection, v, hy]
  obtain ⟨x, a, ha⟩ := hP.rank_two_parityProjection_is_row hr 0 (by decide) v hv
  rw [hp] at ha
  have ha0 : 1 = a * P x (fun _ => 0) := by simpa [v] using congrFun ha (fun _ => 0)
  have hx : P x (fun _ => 0) ≠ 0 := by intro hz; simp [hz] at ha0
  have ha' : a ≠ 0 := by intro hz; simp [hz] at ha0
  refine ⟨x, hx, ?_⟩
  intro y
  have h := congrFun ha y
  change v y = a * P x y at h
  apply mul_left_cancel₀ ha'
  calc
    a * P x y = v y := h.symm
    _ = (a * P x (fun _ => 0)) * v y := by rw [← ha0, one_mul]
    _ = a * (P x (fun _ => 0) * (if (fun _ => 0) = y then 1 else 0)) := by
      dsimp [v]; ring


/-- The vacuum output vector. -/
def outputVacuum : BooleanTable t K := fun z => if (fun _ => 0) = z then 1 else 0

/-- Embed a one-particle coefficient vector in Boolean signature coordinates. -/
def singletonLift : (Fin t → K) →ₗ[K] BooleanTable t K where
  toFun b y := if (booleanSubsetEquiv t y).card = 1 then ∑ j ∈ booleanSubsetEquiv t y, b j else 0
  map_add' b c := by
    ext y
    simp only [Pi.add_apply]
    split_ifs <;> simp [Finset.sum_add_distrib]
  map_smul' a b := by
    ext y
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> simp [Finset.mul_sum]

omit [CharZero K] in
@[simp] theorem singletonLift_singletonWord (b : Fin t → K) (j : Fin t) :
    singletonLift b (singletonWord j) = b j := by simp [singletonLift]

omit [CharZero K] in
@[simp] theorem singletonLift_zero_word (b : Fin t → K) :
    singletonLift b (fun _ => 0) = 0 := by simp [singletonLift]

omit [CharZero K] in
theorem singletonLift_injective : Function.Injective (singletonLift (K := K) (t := t)) := by
  intro b c h
  funext j
  simpa using congrFun h (singletonWord j)

omit [CharZero K] in
/-- A Gaussian singleton input row with no output quadratic block consists
exactly of its degree-one cross coefficients. -/
theorem gaussianOrderedMatrix_singleton_row
    (A : Matrix (Fin r) (Fin r) K) (B : Matrix (Fin r) (Fin t) K) (i : Fin r) :
    (gaussianOrderedMatrix A B 0).row (singletonWord i) = singletonLift (B i) := by
  ext y
  by_cases hy : (booleanSubsetEquiv t y).card = 1
  · obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hy
    have hword : y = singletonWord j := (booleanSubsetEquiv t).injective (by simpa using hj)
    subst y
    simp
  · have hA : gaussianOrderedMatrix A B 0 (singletonWord i) y =
        gaussianCrossPfaffian B [i] (gaussianSubsetList (booleanSubsetEquiv t y)).reverse := by
      simp only [gaussianOrderedMatrix, Matrix.submatrix_apply,
        gaussianFullPlanarPfaffianMatrix, gaussianFullPfaffian_output_zero,
        booleanSubsetEquiv_singletonWord, gaussianSubsetList_eq_sort, Finset.sort_singleton]
      have hnil : gaussianInputPfaffian A B [] = gaussianInputPfaffian 0 B [] := by
        ext ys
        cases ys <;> simp
      rw [← gaussianInputPfaffian_zero]
      simp [gaussianInputPfaffian_cons, hnil]
    rw [Matrix.row_apply, hA,
      gaussianCrossPfaffian_eq_zero_of_length_ne B [i] _ (by simpa using Ne.symm hy)]
    simp [singletonLift, hy]

omit [CharZero K] in
/-- The empty input row with no output couplings is exactly the vacuum. -/
theorem gaussianOrderedMatrix_vacuum
    (A : Matrix (Fin r) (Fin r) K) (B : Matrix (Fin r) (Fin t) K) :
    (gaussianOrderedMatrix A B 0).row (fun _ => 0) = outputVacuum := by
  ext y
  by_cases hy : (fun _ : Fin t => (0 : Fin 2)) = y
  · subst y; simp [outputVacuum]
  · have hS : booleanSubsetEquiv t y ≠ ∅ := by
      intro hz
      apply hy
      apply (booleanSubsetEquiv t).injective
      simpa using hz.symm
    have hlist : gaussianSubsetList (booleanSubsetEquiv t y) ≠ [] := by
      intro hz
      apply hS
      have := congrArg List.length hz
      simpa using this
    simp only [gaussianOrderedMatrix, Matrix.row_apply, Matrix.submatrix_apply,
      booleanSubsetEquiv_zero, gaussianFullPlanarPfaffianMatrix,
      gaussianSubsetList_eq_sort, Finset.sort_empty, gaussianFullPfaffian_nil]
    have hr : ((booleanSubsetEquiv t y).sort (· ≤ ·)).reverse ≠ [] := by
      simpa [gaussianSubsetList_eq_sort] using hlist
    cases he : ((booleanSubsetEquiv t y).sort (· ≤ ·)).reverse with
    | nil => exact (hr he).elim
    | cons a xs =>
      rw [pfaffianList_isolated_first (0 : Matrix (Fin t) (Fin t) K) a xs (by simp)]
      simp [outputVacuum, hy]

omit [CharZero K] in
/-- Two-mode vacuum coefficients directly recover the output quadratic block. -/
theorem gaussianOrderedMatrix_zero_pair
    (A : Matrix (Fin r) (Fin r) K) (B : Matrix (Fin r) (Fin t) K)
    (D : Matrix (Fin t) (Fin t) K) (i j : Fin t) (hij : i < j) :
    gaussianOrderedMatrix A B D (fun _ => 0) ((booleanSubsetEquiv t).symm {i,j}) = D j i := by
  have hs : ({i,j} : Finset (Fin t)).sort (· ≤ ·) = [i,j] := by
    rw [Finset.sort_insert (· ≤ ·) (by simpa using le_of_lt hij) (by simpa using ne_of_lt hij)]
    simp
  simp [gaussianOrderedMatrix, gaussianFullPlanarPfaffianMatrix, gaussianSubsetList_eq_sort,
    hs, gaussianFullPfaffian_nil]

/-- If a Gaussian vacuum row is the vacuum, its output quadratic block is
zero. This reads actual pair coefficients, rather than assuming a chart form. -/
theorem gaussianOrderedMatrix_output_zero_of_vacuum
    (A : Matrix (Fin r) (Fin r) K) (B : Matrix (Fin r) (Fin t) K)
    (D : Matrix (Fin t) (Fin t) K) (hD : ∀ i j, D i j = -D j i)
    (hv : (gaussianOrderedMatrix A B D).row (fun _ => 0) = outputVacuum) : D = 0 := by
  ext i j
  rcases lt_trichotomy i j with hij | hij | hij
  · have hy : (fun _ : Fin t => (0 : Fin 2)) ≠ (booleanSubsetEquiv t).symm {i,j} := by
      intro hz
      have := congrArg (booleanSubsetEquiv t) hz
      simp only [booleanSubsetEquiv_zero, Equiv.apply_symm_apply] at this
      have hc := congrArg Finset.card this
      simp [ne_of_lt hij] at hc
    have h := congrFun hv ((booleanSubsetEquiv t).symm {i,j})
    rw [Matrix.row_apply, gaussianOrderedMatrix_zero_pair A B D i j hij] at h
    simp [outputVacuum, hy] at h
    simpa [h] using hD i j
  · subst j
    exact skew_diagonal_eq_zero D hD i
  · have hy : (fun _ : Fin t => (0 : Fin 2)) ≠ (booleanSubsetEquiv t).symm {j,i} := by
      intro hz
      have := congrArg (booleanSubsetEquiv t) hz
      simp only [booleanSubsetEquiv_zero, Equiv.apply_symm_apply] at this
      have hc := congrArg Finset.card this
      simp [ne_of_lt hij] at hc
    have h := congrFun hv ((booleanSubsetEquiv t).symm {j,i})
    rw [Matrix.row_apply, gaussianOrderedMatrix_zero_pair A B D j i hij] at h
    simpa [outputVacuum, hy] using h

omit [CharZero K] in
/-- Multiplying both generators by a common nonzero scalar preserves their
span. -/
theorem span_pair_smul (u v : BooleanTable t K) {c : K} (hc : c ≠ 0) :
    Submodule.span K ({c • u, c • v} : Set (BooleanTable t K)) =
      Submodule.span K ({u, v} : Set (BooleanTable t K)) := by
  apply Submodule.span_eq_span
  · rintro z (rfl | rfl) <;> exact Submodule.smul_mem _ c (Submodule.subset_span (by simp))
  · intro z hz
    rcases Set.mem_insert_iff.mp hz with hz | hz
    · rw [hz]
      have h := Submodule.smul_mem (Submodule.span K ({c • u, c • v} : Set (BooleanTable t K)))
        c⁻¹ (Submodule.subset_span (by simp : c • u ∈ ({c • u, c • v} : Set (BooleanTable t K))))
      simpa [smul_smul, hc] using h
    · rw [Set.mem_singleton_iff.mp hz]
      have h := Submodule.smul_mem (Submodule.span K ({c • u, c • v} : Set (BooleanTable t K)))
        c⁻¹ (Submodule.subset_span (by simp : c • v ∈ ({c • u, c • v} : Set (BooleanTable t K))))
      simpa [smul_smul, hc] using h

/-- A rank-two ordered MGI row space containing the vacuum is exactly the
span of the vacuum and a nonzero one-particle vector. -/
theorem OrderedMatchgateMatrix.rank_two_vacuum_normal_form
    {P : Matrix (BooleanInput r) (BooleanInput t) K}
    (hP : OrderedMatchgateMatrix P) (hr : P.rank = 2)
    (hv : outputVacuum ∈ orderedRowSpace P) :
    ∃ b : Fin t → K, b ≠ 0 ∧
      orderedRowSpace P = Submodule.span K ({outputVacuum, singletonLift b} : Set (BooleanTable t K)) := by
  classical
  obtain ⟨p, hc, hp⟩ := hP.rank_two_vacuum_pinned_row hr hv
  obtain ⟨A, B, D, hA, hD, _, _, heq⟩ := hP.exists_gaussian_chart_at p (fun _ => 0) hc
  have hD0 : D = 0 := by
    apply gaussianOrderedMatrix_output_zero_of_vacuum A B D hD
    ext y
    apply mul_left_cancel₀ hc
    have h := heq p y
    simpa only [pfaffianXor_self, pfaffianXor_zero, Matrix.row_apply, hp y,
      outputVacuum] using h.symm
  subst D
  have hPeq : P = P p (fun _ => 0) • (gaussianOrderedMatrix A B 0).submatrix
      (booleanXorEquiv p) (booleanXorEquiv (fun _ => 0)) := by
    ext x y
    exact heq x y
  have hB : B ≠ 0 := by
    intro hz
    rw [hPeq, rank_scaled_xor _ _ _ hc, gaussianOrderedMatrix_rank A B 0 hA (by simp),
      hz, Matrix.rank_zero] at hr
    norm_num at hr
  obtain ⟨i, j, hij⟩ : ∃ i j, B i j ≠ 0 := by
    by_contra h
    push Not at h
    exact hB (by ext i j; exact h i j)
  let x₁ := pfaffianXor p (singletonWord i)
  have hp₀ : P.row p = P p (fun _ => 0) • outputVacuum := by
    ext y
    exact hp y
  have hp₁ : P.row x₁ = P p (fun _ => 0) • singletonLift (B i) := by
    ext y
    rw [Matrix.row_apply, heq]
    simp only [x₁, pfaffianXor_involutive, pfaffianXor_zero, Pi.smul_apply, smul_eq_mul]
    congr 1
    exact congrFun (gaussianOrderedMatrix_singleton_row A B i) y
  have h11 : P x₁ (singletonWord j) = P p (fun _ => 0) * B i j := by
    simpa using congrFun hp₁ (singletonWord j)
  have hspan := orderedRowSpace_eq_span_pair_of_rank_two P hr p x₁ (fun _ => 0)
    (singletonWord j) hc (by simpa using congrFun hp₁ (fun _ => 0))
    (h11 ▸ mul_ne_zero hc hij)
  refine ⟨B i, ?_, ?_⟩
  · intro hz
    exact hij (congrFun hz j)
  · rw [hspan, hp₀, hp₁, span_pair_smul _ _ hc]


omit [CharZero K] in
/-- Right multiplication maps the ordinary row space by ordinary row-vector
multiplication, in the same output coordinate order. -/
theorem orderedRowSpace_mul {s : ℕ}
    (P : Matrix (BooleanInput r) (BooleanInput t) K)
    (Q : Matrix (BooleanInput t) (BooleanInput s) K) :
    orderedRowSpace (P * Q) = (orderedRowSpace P).map Q.vecMulLinear := by
  unfold orderedRowSpace
  rw [Submodule.map_span]
  congr 1
  ext v
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨P.row x, ⟨x, rfl⟩, rfl⟩
  · rintro ⟨u, ⟨x, rfl⟩, rfl⟩
    exact ⟨x, rfl⟩

omit [CharZero K] in
/-- An invertible output change preserves matrix rank. -/
theorem rank_mul_of_right_inverse
    (P : Matrix (BooleanInput r) (BooleanInput t) K)
    (C E : Matrix (BooleanInput t) (BooleanInput t) K) (hCE : C * E = 1) :
    (P * C).rank = P.rank := by
  apply le_antisymm (Matrix.rank_mul_le_left P C)
  have h := Matrix.rank_mul_le_left (P * C) E
  simpa only [Matrix.mul_assoc, hCE, Matrix.mul_one] using h

omit [CharZero K] in
/-- Equal row spaces after an invertible output transformation were already
equal before that transformation. -/
theorem orderedRowSpace_eq_of_mul_eq {s : ℕ}
    (P : Matrix (BooleanInput r) (BooleanInput t) K)
    (Q : Matrix (BooleanInput s) (BooleanInput t) K)
    (C E : Matrix (BooleanInput t) (BooleanInput t) K) (hCE : C * E = 1)
    (heq : orderedRowSpace (P * C) = orderedRowSpace (Q * C)) :
    orderedRowSpace P = orderedRowSpace Q := by
  have h := congrArg (fun U : Submodule K (BooleanTable t K) => U.map E.vecMulLinear) heq
  simpa only [← orderedRowSpace_mul, Matrix.mul_assoc, hCE, Matrix.mul_one] using h

/-- Two distinct rank-two MGI row spaces through the vacuum are contained in
the four-dimensional Gaussian generated by their two degree-one directions. -/
theorem exists_rank_four_hull_of_vacuum
    {s : ℕ} {P : Matrix (BooleanInput r) (BooleanInput t) K}
    {Q : Matrix (BooleanInput s) (BooleanInput t) K}
    (hP : OrderedMatchgateMatrix P) (hQ : OrderedMatchgateMatrix Q)
    (hrP : P.rank = 2) (hrQ : Q.rank = 2)
    (hne : orderedRowSpace P ≠ orderedRowSpace Q)
    (hvP : outputVacuum ∈ orderedRowSpace P) (hvQ : outputVacuum ∈ orderedRowSpace Q) :
    ∃ H : Matrix (BooleanInput 2) (BooleanInput t) K,
      OrderedMatchgateMatrix H ∧ H.rank = 4 ∧
      orderedRowSpace P ⊔ orderedRowSpace Q ≤ orderedRowSpace H := by
  classical
  obtain ⟨b₁, hb₁, hR₁⟩ := hP.rank_two_vacuum_normal_form hrP hvP
  obtain ⟨b₂, hb₂, hR₂⟩ := hQ.rank_two_vacuum_normal_form hrQ hvQ
  let B : Matrix (Fin 2) (Fin t) K := ![b₁, b₂]
  have hli : LinearIndependent K B.row := by
    rw [linearIndependent_fin2]
    refine ⟨hb₂, ?_⟩
    intro a ha
    change a • b₂ = b₁ at ha
    have hlift : a • singletonLift b₂ = singletonLift b₁ := by
      simpa only [map_smul] using congrArg (singletonLift (K := K)) ha
    have hle : orderedRowSpace P ≤ orderedRowSpace Q := by
      rw [hR₁, hR₂]
      apply Submodule.span_le.mpr
      rintro v (rfl | rfl)
      · exact Submodule.subset_span (by simp)
      · rw [← hlift]
        exact Submodule.smul_mem _ a (Submodule.subset_span (by simp))
    apply hne
    apply Submodule.eq_of_le_of_finrank_eq hle
    change Module.finrank K (Submodule.span K (Set.range P.row)) =
      Module.finrank K (Submodule.span K (Set.range Q.row))
    rw [← Matrix.rank_eq_finrank_span_row, ← Matrix.rank_eq_finrank_span_row, hrP, hrQ]
  have hBr : B.rank = 2 := by
    rw [Matrix.rank_eq_finrank_span_row, finrank_span_eq_card hli, Fintype.card_fin]
  let H := gaussianOrderedMatrix 0 B 0
  have hH : OrderedMatchgateMatrix H :=
    gaussianOrderedMatrix_isMatchgate 0 B 0 (by simp) (by simp) (by simp) (by simp)
  have hrH : H.rank = 4 := by
    rw [gaussianOrderedMatrix_rank 0 B 0 (by simp) (by simp), hBr]
    norm_num
  have hvH : outputVacuum ∈ orderedRowSpace H := by
    rw [← gaussianOrderedMatrix_vacuum (0 : Matrix (Fin 2) (Fin 2) K) B]
    exact row_mem_orderedRowSpace H (fun _ => 0)
  have hbH (i : Fin 2) : singletonLift (B i) ∈ orderedRowSpace H := by
    rw [← gaussianOrderedMatrix_singleton_row (0 : Matrix (Fin 2) (Fin 2) K) B i]
    exact row_mem_orderedRowSpace H (singletonWord i)
  refine ⟨H, hH, hrH, sup_le ?_ ?_⟩
  · rw [hR₁]
    apply Submodule.span_le.mpr
    rintro v (rfl | rfl)
    · exact hvH
    · exact hbH 0
  · rw [hR₂]
    apply Submodule.span_le.mpr
    rintro v (rfl | rfl)
    · exact hvH
    · exact hbH 1

/-- **Algebraic rank-two Gaussian hull.** Two distinct two-dimensional row
spaces of literal ordered MGI matrices with nonzero intersection lie in the
row space of a rank-four, two-input literal ordered MGI matrix.

The proof derives the common homogeneous pure ray and its actual pinned-row
representative, normalizes it using a proved invertible ordered MGI matrix,
and constructs the hull from two independent degree-one directions. A planar
graph realization statement requires the separate realization correspondence. -/
theorem exists_rank_two_gaussian_hull
    {s : ℕ} {P : Matrix (BooleanInput r) (BooleanInput t) K}
    {Q : Matrix (BooleanInput s) (BooleanInput t) K}
    (hP : OrderedMatchgateMatrix P) (hQ : OrderedMatchgateMatrix Q)
    (hrP : P.rank = 2) (hrQ : Q.rank = 2)
    (hne : orderedRowSpace P ≠ orderedRowSpace Q)
    (hmeet : orderedRowSpace P ⊓ orderedRowSpace Q ≠ ⊥) :
    ∃ H : Matrix (BooleanInput 2) (BooleanInput t) K,
      OrderedMatchgateMatrix H ∧ H.rank = 4 ∧
      orderedRowSpace P ⊔ orderedRowSpace Q ≤ orderedRowSpace H := by
  obtain ⟨u, hu0, hu, huP, huQ, _⟩ :=
    exists_pure_common_row_of_rank_two hP hQ hrP hrQ hmeet
  obtain ⟨C, E, hC, hE, hCE, hEC, huC⟩ :=
    exists_orderedMatchgate_vacuum_normalization u hu hu0
  have hvP : outputVacuum ∈ orderedRowSpace (P * C) := by
    rw [orderedRowSpace_mul]
    exact ⟨u, huP, huC⟩
  have hvQ : outputVacuum ∈ orderedRowSpace (Q * C) := by
    rw [orderedRowSpace_mul]
    exact ⟨u, huQ, huC⟩
  have hne' : orderedRowSpace (P * C) ≠ orderedRowSpace (Q * C) := by
    intro h
    exact hne (orderedRowSpace_eq_of_mul_eq P Q C E hCE h)
  have hrP' : (P * C).rank = 2 := (rank_mul_of_right_inverse P C E hCE).trans hrP
  have hrQ' : (Q * C).rank = 2 := (rank_mul_of_right_inverse Q C E hCE).trans hrQ
  obtain ⟨H, hH, hrH, hle⟩ := exists_rank_four_hull_of_vacuum
    (hP.mul hC) (hQ.mul hC) hrP' hrQ' hne' hvP hvQ
  refine ⟨H * E, hH.mul hE, (rank_mul_of_right_inverse H E C hEC).trans hrH,
    sup_le ?_ ?_⟩
  · have h := Submodule.map_mono (f := E.vecMulLinear) (le_sup_left.trans hle)
    simpa only [← orderedRowSpace_mul, Matrix.mul_assoc, hCE, Matrix.mul_one] using h
  · have h := Submodule.map_mono (f := E.vecMulLinear) (le_sup_right.trans hle)
    simpa only [← orderedRowSpace_mul, Matrix.mul_assoc, hCE, Matrix.mul_one] using h

end
end MatchgateWidth
