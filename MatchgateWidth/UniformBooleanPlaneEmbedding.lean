import MatchgateWidth.RankTwoGaussianHull
import MatchgateWidth.CoverCompressionAlgebra

/-! # Uniform Boolean coordinates on a rank-two ordered MGI plane

The encoder and decoder are chosen from the plane alone. Every arity uses
those same matrices, and reconstruction is an equality of actual coefficients.
-/
namespace MatchgateWidth
noncomputable section

variable {K : Type*} [Field K] [CharZero K]

/-- A rank-two ordered MGI plane is the exact row space of a full-row-rank
one-input ordered MGI matrix. No specified normal form is assumed. -/
theorem OrderedMatchgateMatrix.exists_one_input_rowSpace {r t : ℕ}
    {P : Matrix (BooleanInput r) (BooleanInput t) K}
    (hP : OrderedMatchgateMatrix P) (hr : P.rank = 2) :
    ∃ Q : Matrix (BooleanInput 1) (BooleanInput t) K,
      OrderedMatchgateMatrix Q ∧ Q.rank = 2 ∧ orderedRowSpace Q = orderedRowSpace P := by
  classical
  obtain ⟨x₀, x₁, k, hk, hx₀, hx₁, h₀, h₁, hspan⟩ := hP.rank_two_pinned_basis hr
  obtain ⟨C, E, hC, hE, hCE, hEC, huC⟩ :=
    exists_orderedMatchgate_vacuum_normalization (P.row x₀) (hP.row x₀) hx₀
  have hv : outputVacuum ∈ orderedRowSpace (P * C) := by
    rw [orderedRowSpace_mul]
    exact ⟨P.row x₀, row_mem_orderedRowSpace P x₀, huC⟩
  have hr' : (P * C).rank = 2 := (rank_mul_of_right_inverse P C E hCE).trans hr
  obtain ⟨b, hb, hform⟩ := (hP.mul hC).rank_two_vacuum_normal_form hr' hv
  let B : Matrix (Fin 1) (Fin t) K := fun _ => b
  have hB : B.rank = 1 := by
    rw [Matrix.rank_eq_finrank_span_row]
    change Module.finrank K (Submodule.span K (Set.range (fun _ : Fin 1 => b))) = 1
    rw [Set.range_const]
    exact finrank_span_singleton hb
  let Q₀ := gaussianOrderedMatrix 0 B 0
  have hQ₀ : OrderedMatchgateMatrix Q₀ :=
    gaussianOrderedMatrix_isMatchgate 0 B 0 (by simp) (by simp) (by simp) (by simp)
  have hr₀ : Q₀.rank = 2 := by
    rw [gaussianOrderedMatrix_rank 0 B 0 (by simp) (by simp), hB]
    norm_num
  obtain ⟨j, hj⟩ : ∃ j, b j ≠ 0 := by
    by_contra h
    push Not at h
    exact hb (funext h)
  have hspace : orderedRowSpace Q₀ = orderedRowSpace (P * C) := by
    rw [hform]
    have h := orderedRowSpace_eq_span_pair_of_rank_two Q₀ hr₀
      (fun _ => 0) (singletonWord 0) (fun _ => 0) (singletonWord j)
      (by simp [Q₀]) (by simp [Q₀]) (by change gaussianOrderedMatrix 0 B 0 (singletonWord 0) (singletonWord j) ≠ 0; rw [gaussianOrderedMatrix_singleton_singleton]; exact hj)
    rw [h, gaussianOrderedMatrix_vacuum, gaussianOrderedMatrix_singleton_row]
  refine ⟨Q₀ * E, hQ₀.mul hE,
    (rank_mul_of_right_inverse Q₀ E C hEC).trans hr₀, ?_⟩
  rw [orderedRowSpace_mul, hspace, ← orderedRowSpace_mul, Matrix.mul_assoc, hCE, Matrix.mul_one]


/-- A one-wire Boolean word is one of the two literal endpoint words. -/
theorem booleanInput_one_cases (x : BooleanInput 1) :
    x = (fun _ => 0) ∨ x = (fun _ => 1) := by
  have h : x 0 = 0 ∨ x 0 = 1 := by
    have hx := (x 0).isLt
    omega
  rcases h with h | h
  · left
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    simpa [hi] using h
  · right
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    simpa [hi] using h

/-- The two fixed endpoint rows of a full-rank one-input encoder have opposite
literal output parity. No tensor or tensor arity is used to select these rows. -/
theorem OrderedMatchgateMatrix.one_input_endpoint_parity {t : ℕ}
    {Q : Matrix (BooleanInput 1) (BooleanInput t) K}
    (hQ : OrderedMatchgateMatrix Q) (hr : Q.rank = 2) :
    ∃ k < 2, Q.row (fun _ => 0) ≠ 0 ∧ Q.row (fun _ => 1) ≠ 0 ∧
      (∀ y, booleanParity y ≠ k → Q (fun _ => 0) y = 0) ∧
      (∀ y, booleanParity y = k → Q (fun _ => 1) y = 0) := by
  obtain ⟨x₀, x₁, k, hk, h₀, h₁, hp₀, hp₁, hspan⟩ := hQ.rank_two_pinned_basis hr
  have hne : x₀ ≠ x₁ := by
    intro he
    apply h₀
    funext y
    by_cases hy : booleanParity y = k
    · simpa [he] using hp₁ y hy
    · exact hp₀ y hy
  rcases booleanInput_one_cases x₀ with h0 | h0 <;>
    rcases booleanInput_one_cases x₁ with h1 | h1
  · exact (hne (h0.trans h1.symm)).elim
  · subst x₀
    subst x₁
    exact ⟨k, hk, h₀, h₁, hp₀, hp₁⟩
  · subst x₀
    subst x₁
    refine ⟨1-k, by omega, h₁, h₀, ?_, ?_⟩
    · intro y hy
      apply hp₁
      have := booleanParity_lt_two y
      omega
    · intro y hy
      apply hp₀
      omega
  · exact (hne (h0.trans h1.symm)).elim

omit [CharZero K] in
/-- The two endpoint rows span precisely the encoder's ordinary row space. -/
theorem orderedRowSpace_one_input {t : ℕ}
    (Q : Matrix (BooleanInput 1) (BooleanInput t) K) :
    orderedRowSpace Q = Submodule.span K
      ({Q.row (fun _ => 0), Q.row (fun _ => 1)} : Set (BooleanTable t K)) := by
  unfold orderedRowSpace
  congr 1
  ext u
  constructor
  · rintro ⟨x, rfl⟩
    rcases booleanInput_one_cases x with rfl | rfl <;> simp
  · rintro (rfl | rfl)
    · exact ⟨fun _ => 0, rfl⟩
    · exact ⟨fun _ => 1, rfl⟩


omit [CharZero K] in
/-- Full row rank makes the two literal endpoint vectors a linearly independent
pair. Together with orderedRowSpace_one_input this is the actual fixed basis. -/
theorem linearIndependent_one_input_endpoints {t : ℕ}
    (Q : Matrix (BooleanInput 1) (BooleanInput t) K) (hr : Q.rank = 2) :
    LinearIndependent K (![Q.row (fun _ => 0), Q.row (fun _ => 1)] : Fin 2 → BooleanTable t K) := by
  have heq : Set.range (![Q.row (fun _ => 0), Q.row (fun _ => 1)] : Fin 2 → BooleanTable t K) =
      ({Q.row (fun _ => 0), Q.row (fun _ => 1)} : Set (BooleanTable t K)) := by
    ext u
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · rintro (rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
  rw [linearIndependent_iff_card_eq_finrank_span, heq]
  change 2 = Module.finrank K (Submodule.span K
    ({Q.row (fun _ => 0), Q.row (fun _ => 1)} : Set (BooleanTable t K)))
  rw [← orderedRowSpace_one_input]
  change 2 = Module.finrank K (Submodule.span K (Set.range Q.row))
  rw [← Matrix.rank_eq_finrank_span_row, hr]

section TensorFactorization
variable {I A B : Type*} [Fintype I] [DecidableEq I] [Fintype A] [DecidableEq A] [Fintype B]

/-- The actual coefficient action of a separately chosen matrix at each port. -/
def heterogeneousLeftTransform (M : I → Matrix B B K) (F : (I → B) → K) : (I → B) → K :=
  fun x => ∑ y, F y * ∏ i, M i (y i) (x i)

omit [CharZero K] in
/-- Splitting one matrix attachment off the complete coordinate sum. -/
theorem heterogeneousLeftTransform_split (M : I → Matrix B B K)
    (F : (I → B) → K) (j : I) (x : I → B) :
    heterogeneousLeftTransform M F x =
      ∑ a : {i : I // i ≠ j} → B,
        (∑ d, F (insertBoundaryCoordinate j d a) * M j d (x j)) *
          ∏ i : {i : I // i ≠ j}, M i (a i) (x i) := by
  classical
  unfold heterogeneousLeftTransform
  rw [sum_eq_selected_sum_complement j, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro d _
  rw [prod_eq_selected_mul_complement j]
  simp only [insertBoundaryCoordinate_same]
  have heq : (∏ i : {i : I // i ≠ j}, M i (insertBoundaryCoordinate j d a i) (x i)) =
      ∏ i : {i : I // i ≠ j}, M i (a i) (x i) := by
    apply Finset.prod_congr rfl
    intro i _
    rw [insertBoundaryCoordinate_ne j d a i i.property]
  rw [heq]
  ring

omit [CharZero K] in
/-- If every one-port slice is fixed by a matrix, its complete tensor power
fixes the tensor. This is a coefficient theorem, including zero ports. -/
theorem leftTransform_eq_self_of_slices (E : Matrix B B K) (F : (I → B) → K)
    (hfix : ∀ (j : I) (a : {i : I // i ≠ j} → B),
      Matrix.vecMul (fun d => F (insertBoundaryCoordinate j d a)) E =
        (fun d => F (insertBoundaryCoordinate j d a))) :
    leftTransform E F = F := by
  classical
  have hpartial (s : Finset I) :
      heterogeneousLeftTransform (fun i => if i ∈ s then E else 1) F = F := by
    induction s using Finset.induction_on with
    | empty =>
      change leftTransform (1 : Matrix B B K) F = F
      rw [leftTransform_eq_tensorPowerMatrix_transpose_mulVecLin, tensorPowerMatrix_one,
        Matrix.transpose_one]
      exact Matrix.one_mulVec F
    | @insert j s hj ih =>
      apply Eq.trans _ ih
      funext x
      rw [heterogeneousLeftTransform_split _ _ j, heterogeneousLeftTransform_split _ _ j]
      apply Finset.sum_congr rfl
      intro a _
      congr 1
      · simp only [Finset.mem_insert_self, ite_true, hj, ite_false]
        change Matrix.vecMul (fun d => F (insertBoundaryCoordinate j d a)) E (x j) =
          Matrix.vecMul (fun d => F (insertBoundaryCoordinate j d a)) 1 (x j)
        rw [hfix, Matrix.vecMul_one]
      · apply Finset.prod_congr rfl
        intro i _
        have hi : i.val ≠ j := i.property
        simp only [Finset.mem_insert, hi, false_or]
  have h := hpartial Finset.univ
  simp only [Finset.mem_univ, ite_true] at h
  exact h

omit [CharZero K] in
/-- Every column of a port flattening is literally in its column support. -/
theorem portFlatten_slice_mem (F : (I → B) → K) (j : I)
    (a : {i : I // i ≠ j} → B) :
    (fun d => F (insertBoundaryCoordinate j d a)) ∈ columnSupport (portFlatten F j) := by
  classical
  refine ⟨Pi.single a 1, ?_⟩
  change Matrix.mulVec (portFlatten F j) (Pi.single a 1) = _
  rw [Matrix.mulVec_single_one]
  rfl

omit [CharZero K] in
/-- A fixed right decoder is a left inverse on the encoder's entire row space. -/
theorem vecMul_decoder_encoder (Q : Matrix A B K) (D : Matrix B A K)
    (hQD : Q * D = 1) (u : B → K)
    (hu : u ∈ Submodule.span K (Set.range Q.row)) :
    Matrix.vecMul u (D * Q) = u := by
  classical
  induction hu using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨a, rfl⟩ := hu
    funext b
    change (Q * (D * Q)) a b = Q a b
    rw [← Matrix.mul_assoc, hQD, Matrix.one_mul]
  | zero => simp
  | add x y hx hy ihx ihy => simp [Matrix.add_vecMul, ihx, ihy]
  | smul c x hx ih => simp [Matrix.smul_vecMul, ih]

omit [CharZero K] in
/-- Exact simultaneous factorization through a fixed encoder, from containment
of every actual block support. The decoder is independent of both arity and tensor. -/
theorem leftTransform_decoder_reconstruct (Q : Matrix A B K) (D : Matrix B A K)
    (hQD : Q * D = 1) (F : (I → B) → K)
    (hsupport : ∀ j, columnSupport (portFlatten F j) ≤
      Submodule.span K (Set.range Q.row)) :
    leftTransform Q (leftTransform D F) = F := by
  rw [leftTransform_compose]
  apply leftTransform_eq_self_of_slices
  intro j a
  exact vecMul_decoder_encoder Q D hQD _ (hsupport j (portFlatten_slice_mem F j a))


omit [CharZero K] in
/-- Exact coefficient extraction for a tensor already written in the encoder
basis. This gives uniqueness with the same decoder at every arity. -/
theorem leftTransform_decoder_extract (Q : Matrix A B K) (D : Matrix B A K)
    (hQD : Q * D = 1) (G : (I → A) → K) :
    leftTransform D (leftTransform Q G) = G := by
  classical
  rw [leftTransform_compose, hQD, leftTransform_eq_tensorPowerMatrix_transpose_mulVecLin]
  have he : tensorPowerMatrix (P := I) (1 : Matrix A A K) = 1 := by
    convert tensorPowerMatrix_one (P := I) (D := A) (K := K)
  rw [he, Matrix.transpose_one]
  exact Matrix.one_mulVec G

end TensorFactorization


omit [CharZero K] in
/-- Attaching one fixed decoder at every block both preserves the MGI and
reconstructs the original tensor exactly when every block support is covered. -/
theorem ordered_plane_decode_reconstruct {r t : ℕ}
    (Q : Matrix (BooleanInput r) (BooleanInput t) K)
    (D : Matrix (BooleanInput t) (BooleanInput r) K)
    (hD : OrderedMatchgateMatrix D) (hQD : Q * D = 1)
    (k : ℕ) (T : BooleanTable (k*t) K) (hT : BooleanMatchgateIdentities T)
    (hsupport : ∀ j, columnSupport
      (portFlatten (fun x => T (flattenBooleanBlocks x)) j) ≤ orderedRowSpace Q) :
    BooleanMatchgateIdentities (blockwiseTransform D.transpose k T) ∧
      leftBooleanLift Q k (fun x => blockwiseTransform D.transpose k T (flattenBooleanBlocks x)) = T := by
  refine ⟨hD.transpose.blockwiseTransform k hT, ?_⟩
  let F : (Fin k → BooleanInput t) → K := fun x => T (flattenBooleanBlocks x)
  have heq : (fun x : Fin k → BooleanInput r =>
      blockwiseTransform D.transpose k T (flattenBooleanBlocks x)) = leftTransform D F := by
    funext x
    unfold blockwiseTransform
    change rightTransform D.transpose F
      ((booleanBlocksEquiv k r).symm ((booleanBlocksEquiv k r) x)) = _
    rw [Equiv.symm_apply_apply, rightTransform_transpose]
  rw [heq]
  have hr := leftTransform_decoder_reconstruct Q D hQD F hsupport
  funext z
  change leftTransform Q (leftTransform D F) ((booleanBlocksEquiv k t).symm z) = T z
  rw [hr]
  exact congrArg T ((booleanBlocksEquiv k t).apply_symm_apply z)


/-- The literal k-wire coefficient tensor in a one-input encoder's basis. -/
def booleanPlanePullback {t : ℕ} (D : Matrix (BooleanInput t) (BooleanInput 1) K)
    (k : ℕ) (T : BooleanTable (k*t) K) : BooleanTable k K :=
  fun z => leftTransform D (fun y => T (flattenBooleanBlocks y)) (fun i _ => z i)

omit [CharZero K] in
/-- One-input block decoding has exactly k surviving Boolean wires, in their
inherited order. The displayed cast changes only the equal arity k*1=k. -/
theorem booleanPlanePullback_eq_cast {t : ℕ}
    (D : Matrix (BooleanInput t) (BooleanInput 1) K) (k : ℕ)
    (T : BooleanTable (k*t) K) :
    booleanPlanePullback D k T =
      castBooleanTable (Nat.mul_one k) (blockwiseTransform D.transpose k T) := by
  funext z
  unfold booleanPlanePullback castBooleanTable blockwiseTransform
  rw [rightTransform_transpose]
  congr 1
  funext i j
  apply congrArg z
  apply Fin.ext
  have hj : j = 0 := Subsingleton.elim _ _
  simp [hj, finProdFinEquiv]

omit [CharZero K] in
/-- The exact coefficient pullback of an MGI tensor is an MGI signature on
k Boolean wires, using the fixed decoder D. -/
theorem OrderedMatchgateMatrix.booleanPlanePullback {t : ℕ}
    {D : Matrix (BooleanInput t) (BooleanInput 1) K}
    (hD : OrderedMatchgateMatrix D) (k : ℕ)
    {T : BooleanTable (k*t) K} (hT : BooleanMatchgateIdentities T) :
    BooleanMatchgateIdentities (MatchgateWidth.booleanPlanePullback D k T) := by
  rw [booleanPlanePullback_eq_cast]
  exact (hD.transpose.blockwiseTransform k hT).cast (Nat.mul_one k)

omit [CharZero K] in
/-- Evaluating one-wire block coordinates is the actual decoder coefficient sum. -/
theorem booleanPlanePullback_blocks {t : ℕ}
    (D : Matrix (BooleanInput t) (BooleanInput 1) K) (k : ℕ)
    (T : BooleanTable (k*t) K) :
    (fun x : Fin k → BooleanInput 1 => booleanPlanePullback D k T (fun i => x i 0)) =
      leftTransform D (fun y => T (flattenBooleanBlocks y)) := by
  funext x
  unfold booleanPlanePullback
  congr 1
  funext i j
  exact congrArg (x i) (Subsingleton.elim 0 j)

omit [CharZero K] in
/-- Literal k-wire coefficients reconstruct any tensor supported in the fixed
plane, with no rescaling, permutation, or arity-dependent basis choice. -/
theorem booleanPlanePullback_reconstruct {t : ℕ}
    (Q : Matrix (BooleanInput 1) (BooleanInput t) K)
    (D : Matrix (BooleanInput t) (BooleanInput 1) K) (hQD : Q * D = 1)
    (k : ℕ) (T : BooleanTable (k*t) K)
    (hsupport : ∀ j, columnSupport
      (portFlatten (fun x => T (flattenBooleanBlocks x)) j) ≤ orderedRowSpace Q) :
    leftBooleanLift Q k (fun x => booleanPlanePullback D k T (fun i => x i 0)) = T := by
  rw [booleanPlanePullback_blocks]
  have hr := leftTransform_decoder_reconstruct Q D hQD
    (fun y => T (flattenBooleanBlocks y)) hsupport
  funext z
  unfold leftBooleanLift
  rw [hr]
  exact congrArg T ((booleanBlocksEquiv k t).apply_symm_apply z)


omit [CharZero K] in
/-- Every prescribed coefficient tensor is recovered exactly from its lift in
the fixed basis; therefore the pulled-back coefficients are unique. -/
theorem booleanPlanePullback_leftBooleanLift {t : ℕ}
    (Q : Matrix (BooleanInput 1) (BooleanInput t) K)
    (D : Matrix (BooleanInput t) (BooleanInput 1) K) (hQD : Q * D = 1)
    (k : ℕ) (H : BooleanTable k K) :
    booleanPlanePullback D k (leftBooleanLift Q k (fun x => H (fun i => x i 0))) = H := by
  have hflat : (fun y : Fin k → BooleanInput t =>
      leftBooleanLift Q k (fun x => H (fun i => x i 0)) (flattenBooleanBlocks y)) =
      leftTransform Q (fun x => H (fun i => x i 0)) := by
    funext y
    unfold leftBooleanLift
    change leftTransform Q (fun x => H (fun i => x i 0))
      ((booleanBlocksEquiv k t).symm ((booleanBlocksEquiv k t) y)) = _
    rw [Equiv.symm_apply_apply]
  funext z
  unfold booleanPlanePullback
  rw [hflat, leftTransform_decoder_extract Q D hQD]

omit [CharZero K] in
/-- If any all-arity tensor written in this fixed basis satisfies the literal
MGI, its very same coefficient tensor satisfies the Boolean MGI. -/
theorem booleanMatchgateIdentities_of_plane_lift {t : ℕ}
    (Q : Matrix (BooleanInput 1) (BooleanInput t) K)
    (D : Matrix (BooleanInput t) (BooleanInput 1) K)
    (hD : OrderedMatchgateMatrix D) (hQD : Q * D = 1)
    (k : ℕ) (H : BooleanTable k K)
    (hT : BooleanMatchgateIdentities (leftBooleanLift Q k (fun x => H (fun i => x i 0)))) :
    BooleanMatchgateIdentities H := by
  rw [← booleanPlanePullback_leftBooleanLift Q D hQD k H]
  exact hD.booleanPlanePullback k hT

/-- **Uniform Boolean-plane embedding (algebraic Lemma 10.8).**
A rank-two literal ordered MGI row space has a single full-rank one-input
encoder, an exact ordered MGI decoder, and two nonzero opposite-parity
endpoint basis vectors. The same encoder and decoder work simultaneously for
every arity and every MGI tensor whose actual block supports lie in the plane.
The forward reconstruction is equality of the complete coefficient sums. -/
theorem exists_uniform_boolean_plane_embedding {r t : ℕ}
    {P : Matrix (BooleanInput r) (BooleanInput t) K}
    (hP : OrderedMatchgateMatrix P) (hr : P.rank = 2) :
    ∃ (Q : Matrix (BooleanInput 1) (BooleanInput t) K)
      (D : Matrix (BooleanInput t) (BooleanInput 1) K) (b : ℕ),
      OrderedMatchgateMatrix Q ∧ OrderedMatchgateMatrix D ∧ Q * D = 1 ∧
      Q.rank = 2 ∧ orderedRowSpace Q = orderedRowSpace P ∧ b < 2 ∧
      Q.row (fun _ => 0) ≠ 0 ∧ Q.row (fun _ => 1) ≠ 0 ∧
      (∀ y, booleanParity y ≠ b → Q (fun _ => 0) y = 0) ∧
      (∀ y, booleanParity y = b → Q (fun _ => 1) y = 0) ∧
      (∀ k (T : BooleanTable (k*t) K), BooleanMatchgateIdentities T →
        (∀ j, columnSupport (portFlatten (fun x => T (flattenBooleanBlocks x)) j) ≤
          orderedRowSpace P) →
        BooleanMatchgateIdentities (blockwiseTransform D.transpose k T) ∧
        leftBooleanLift Q k (fun x => blockwiseTransform D.transpose k T (flattenBooleanBlocks x)) = T) := by
  obtain ⟨Q, hQ, hrQ, hspace⟩ := hP.exists_one_input_rowSpace hr
  obtain ⟨D, hD, hQD⟩ := hQ.exists_rightInverse (by simpa using hrQ)
  obtain ⟨b, hb, h₀, h₁, hp₀, hp₁⟩ := hQ.one_input_endpoint_parity hrQ
  refine ⟨Q, D, b, hQ, hD, hQD, hrQ, hspace, hb, h₀, h₁, hp₀, hp₁, ?_⟩
  intro k T hT hsupport
  apply ordered_plane_decode_reconstruct Q D hD hQD k T hT
  simpa only [hspace] using hsupport


/-- Source-labelled Boolean plane coordinates: the fixed endpoint indexed by
zero is even and the fixed endpoint indexed by one is odd. If the initial
encoder reverses those labels, a single active-input XOR corrects them before
the encoder and decoder are fixed. -/
theorem exists_even_odd_boolean_plane_encoder {r t : ℕ}
    {P : Matrix (BooleanInput r) (BooleanInput t) K}
    (hP : OrderedMatchgateMatrix P) (hr : P.rank = 2) :
    ∃ (Q : Matrix (BooleanInput 1) (BooleanInput t) K)
      (D : Matrix (BooleanInput t) (BooleanInput 1) K),
      OrderedMatchgateMatrix Q ∧ OrderedMatchgateMatrix D ∧ Q * D = 1 ∧
      Q.rank = 2 ∧ orderedRowSpace Q = orderedRowSpace P ∧
      Q.row (fun _ => 0) ≠ 0 ∧ Q.row (fun _ => 1) ≠ 0 ∧
      (∀ y, booleanParity y ≠ 0 → Q (fun _ => 0) y = 0) ∧
      (∀ y, booleanParity y = 0 → Q (fun _ => 1) y = 0) := by
  obtain ⟨Q, hQ, hrQ, hspace⟩ := hP.exists_one_input_rowSpace hr
  obtain ⟨b, hb, h₀, h₁, hp₀, hp₁⟩ := hQ.one_input_endpoint_parity hrQ
  by_cases hb0 : b = 0
  · obtain ⟨D, hD, hQD⟩ := hQ.exists_rightInverse (by simpa using hrQ)
    exact ⟨Q, D, hQ, hD, hQD, hrQ, hspace, h₀, h₁, hb0 ▸ hp₀, hb0 ▸ hp₁⟩
  · have hb1 : b = 1 := by omega
    subst b
    let Q' : Matrix (BooleanInput 1) (BooleanInput t) K :=
      Q.submatrix (booleanXorEquiv (fun _ => 1)) (Equiv.refl _)
    have hQ' : OrderedMatchgateMatrix Q' := hQ.inputXor (fun _ => 1)
    have hrQ' : Q'.rank = 2 :=
      (Matrix.rank_submatrix Q (booleanXorEquiv (fun _ => 1)) (Equiv.refl _)).trans hrQ
    have hspace' : orderedRowSpace Q' = orderedRowSpace Q := by
      unfold orderedRowSpace
      congr 1
      change Set.range (Q.row ∘ booleanXorEquiv (fun _ => 1)) = Set.range Q.row
      exact (booleanXorEquiv (fun _ => 1)).surjective.range_comp Q.row
    have hrow0 : Q'.row (fun _ => 0) = Q.row (fun _ => 1) := by
      ext y
      change Q (pfaffianXor (fun _ => 1) (fun _ => 0)) y = Q (fun _ => 1) y
      congr 1
    have hrow1 : Q'.row (fun _ => 1) = Q.row (fun _ => 0) := by
      ext y
      change Q (pfaffianXor (fun _ => 1) (fun _ => 1)) y = Q (fun _ => 0) y
      rw [pfaffianXor_self]
    obtain ⟨D, hD, hQD⟩ := hQ'.exists_rightInverse (by simpa using hrQ')
    refine ⟨Q', D, hQ', hD, hQD, hrQ', hspace'.trans hspace,
      hrow0.symm ▸ h₁, hrow1.symm ▸ h₀, ?_, ?_⟩
    · intro y hy
      have hy1 : booleanParity y = 1 := by have := booleanParity_lt_two y; omega
      change Q'.row (fun _ => 0) y = 0
      rw [hrow0]
      exact hp₁ y hy1
    · intro y hy
      change Q'.row (fun _ => 1) y = 0
      rw [hrow1]
      exact hp₀ y (by omega)

end
end MatchgateWidth
