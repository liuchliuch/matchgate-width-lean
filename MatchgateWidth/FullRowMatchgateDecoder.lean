import MatchgateWidth.GaussianDecoder
import MatchgateWidth.GaussianMatrixCharts
import MatchgateWidth.PureVacuumNormalization

/-!
# Full-row-rank ordered matchgate decoders

Over characteristic-zero fields, a full-row-rank matrix satisfying the literal
ordered matchgate identities has a right inverse satisfying the same literal
identities.  The proof derives a Gaussian chart, selects a nonsingular output
mode cube, and uses proved ordered composition and inverse closure.  It does
not assume a matchgate canonical form or a decoder as a hypothesis.

This is the algebraic MGI statement underlying source Lemma 10.4.  An assertion
about graph-realized exact signatures also requires the separately audited
MGI-to-planar-realization correspondence.
-/
namespace MatchgateWidth
noncomputable section
variable {R : Type*} [CommRing R] {r t : ℕ}

/-- Independent input/output XORs are the two blocks of one boundary pivot. -/
theorem OrderedMatchgateMatrix.xor
    {P : Matrix (BooleanInput r) (BooleanInput t) R}
    (hP : OrderedMatchgateMatrix P) (p : BooleanInput r) (q : BooleanInput t) :
    OrderedMatchgateMatrix (P.submatrix (booleanXorEquiv p) (booleanXorEquiv q)) := by
  have h := hP.pivot (matrixBoundaryWord p q)
  have heq : (fun z => orderedMatrixSignature P (pfaffianXor (matrixBoundaryWord p q) z)) =
      orderedMatrixSignature (P.submatrix (booleanXorEquiv p) (booleanXorEquiv q)) := by
    funext z
    unfold orderedMatrixSignature
    congr 1
    · funext i
      simp [booleanXorEquiv, pfaffianXor, matrixBoundaryWord]
    · funext j
      simp [booleanXorEquiv, pfaffianXor, matrixBoundaryWord]
  change BooleanMatchgateIdentities _
  rw [heq] at h
  exact h

/-- Input XOR preserves the ordered matchgate matrix class. -/
theorem OrderedMatchgateMatrix.inputXor
    {P : Matrix (BooleanInput r) (BooleanInput t) R}
    (hP : OrderedMatchgateMatrix P) (p : BooleanInput r) :
    OrderedMatchgateMatrix (fun x y => P (pfaffianXor p x) y) := by
  have h := hP.xor p (fun _ => 0)
  have heq : P.submatrix (booleanXorEquiv p) (booleanXorEquiv (fun _ => 0)) =
      (fun x y => P (pfaffianXor p x) y) := by
    ext x y
    simp [booleanXorEquiv]
  rw [heq] at h
  exact h

variable {K : Type*} [Field K]

/-- Independent XORs and a nonzero scalar preserve ordinary matrix rank. -/
theorem rank_scaled_xor (P : Matrix (BooleanInput r) (BooleanInput t) K)
    (p : BooleanInput r) (q : BooleanInput t) {c : K} (hc : c ≠ 0) :
    (c • P.submatrix (booleanXorEquiv p) (booleanXorEquiv q)).rank = P.rank := by
  rw [Matrix.rank_smul_of_mem_nonZeroDivisors _ (mem_nonZeroDivisors_of_ne_zero hc),
    Matrix.rank_submatrix]

/-- Decoder transport under the actual independent Boolean pivots and scale. -/
theorem exists_ordered_rightInverse_scaled_xor
    {P : Matrix (BooleanInput r) (BooleanInput t) K}
    {N : Matrix (BooleanInput t) (BooleanInput r) K}
    (hN : OrderedMatchgateMatrix N) (hPN : P * N = 1)
    (p : BooleanInput r) (q : BooleanInput t) {c : K} (hc : c ≠ 0) :
    ∃ E : Matrix (BooleanInput t) (BooleanInput r) K,
      OrderedMatchgateMatrix E ∧
      (c • P.submatrix (booleanXorEquiv p) (booleanXorEquiv q)) * E = 1 := by
  refine ⟨c⁻¹ • N.submatrix (booleanXorEquiv q) (booleanXorEquiv p),
    (hN.xor q p).smul c⁻¹, ?_⟩
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hc, one_smul,
    Matrix.submatrix_mul_equiv, hPN, Matrix.submatrix_one_equiv]

variable [CharZero K]

/-- Full-row-rank exact ordered MGI matrices have exact ordered MGI right
inverses. Includes zero input width, rectangular output width, arbitrary parity,
and arbitrary nonzero chart pivots. -/
theorem OrderedMatchgateMatrix.exists_rightInverse
    {P : Matrix (BooleanInput r) (BooleanInput t) K}
    (hP : OrderedMatchgateMatrix P) (hfull : P.rank = 2 ^ r) :
    ∃ N : Matrix (BooleanInput t) (BooleanInput r) K,
      OrderedMatchgateMatrix N ∧ P * N = 1 := by
  obtain ⟨p, q, c, A, B, D, hA, hD, _, _, heq⟩ := hP.exists_gaussian_chart
  have hP_eq : P = c • (gaussianOrderedMatrix A B D).submatrix
      (booleanXorEquiv p) (booleanXorEquiv q) := by
    ext x y
    exact heq x y
  have hc : c ≠ 0 := by
    intro hz
    rw [hP_eq, hz, zero_smul, Matrix.rank_zero] at hfull
    exact (Nat.ne_of_gt (Nat.two_pow_pos r)) hfull.symm
  have hG : (gaussianOrderedMatrix A B D).rank = 2 ^ r := by
    rwa [hP_eq, rank_scaled_xor _ p q hc] at hfull
  obtain ⟨N, hN, hGN⟩ := gaussianOrderedMatrix_exists_rightInverse A B D hA hD hG
  rw [hP_eq]
  exact exists_ordered_rightInverse_scaled_xor hN hGN p q hc

/-- The same decoder theorem phrased using the number of Boolean rows. -/
theorem OrderedMatchgateMatrix.exists_rightInverse_of_fullRowRank
    {P : Matrix (BooleanInput r) (BooleanInput t) K}
    (hP : OrderedMatchgateMatrix P) (hfull : P.rank = Fintype.card (BooleanInput r)) :
    ∃ N : Matrix (BooleanInput t) (BooleanInput r) K,
      OrderedMatchgateMatrix N ∧ P * N = 1 := by
  apply hP.exists_rightInverse
  simpa [BooleanInput] using hfull

end
end MatchgateWidth
