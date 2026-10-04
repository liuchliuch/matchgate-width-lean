import MatchgateWidth.MGIBlockContraction
import MatchgateWidth.MGIReversal

/-!
# Matrix multiplication with the exact planar boundary order

A matrix has increasing inputs followed by reversed outputs. Its intermediate
indices therefore occur in opposite physical orders in the two factors. The
proof below transfers the simultaneous toggles in the two summed intermediate
words. Reversing their sorted difference is exactly the sign which cancels the
two retained-block identities. No arbitrary same-order contraction is used.
-/

namespace MatchgateWidth
open scoped symmDiff

variable {R : Type*} [CommRing R]

private def matrixAlt {α : Type*} (w : α → R) : List α → R
  | [] => 0
  | a :: xs => -w a - matrixAlt w xs

private theorem matrixAlt_eq {α : Type*} (w : α → R) (xs : List α) :
    matrixAlt w xs = ∑ j : Fin xs.length, (-1 : R) ^ (j.val + 1) * w xs[j] := by
  induction xs with
  | nil => simp [matrixAlt]
  | cons a xs ih =>
    simp only [matrixAlt, ih, List.length_cons, Fin.sum_univ_succ,
      Fin.val_zero, zero_add, pow_one, neg_one_mul, Fin.val_succ]
    rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    simp [pow_succ]

private theorem matrixAlt_append {α : Type*} (w : α → R) (xs ys : List α) :
    matrixAlt w (xs ++ ys) = matrixAlt w xs + (-1 : R) ^ xs.length * matrixAlt w ys := by
  induction xs with
  | nil => simp [matrixAlt]
  | cons a xs ih => simp only [List.cons_append, matrixAlt, List.length_cons, ih, pow_succ]; ring

private theorem matrixAlt_map {α β : Type*} (w : β → R) (f : α → β) (xs : List α) :
    matrixAlt w (xs.map f) = matrixAlt (fun a => w (f a)) xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [matrixAlt, ih]

private theorem matrixAlt_reverse {α : Type*} (w : α → R) (xs : List α) :
    matrixAlt w xs.reverse = (-1 : R) ^ (xs.length + 1) * matrixAlt w xs := by
  induction xs with
  | nil => simp [matrixAlt]
  | cons a xs ih =>
    rw [List.reverse_cons, matrixAlt_append, ih]
    simp only [matrixAlt, List.length_cons, List.length_reverse, sub_zero, pow_succ]
    ring

private theorem matrix_mgi_alt {n : ℕ} (F G : SubsetSignature n R)
    (A B : Finset (Fin n)) :
    mgiBilinear F G A B =
      matrixAlt (fun i => F (A ∆ {i}) * G (B ∆ {i})) ((A ∆ B).sort (· ≤ ·)) := by
  classical
  rw [matrixAlt_eq]
  unfold mgiBilinear
  simp only [mul_assoc]
  calc
    _ = ∑ i ∈ A ∆ B, (-1 : R) ^ (((A ∆ B).sort (· ≤ ·)).idxOf i + 1) *
      (F (A ∆ {i}) * G (B ∆ {i})) := by simp [mgiCoeff]
    _ = _ := by
      symm
      apply Finset.sum_bij (fun j _ => ((A ∆ B).sort (· ≤ ·))[j])
      · intro j _
        exact (Finset.mem_sort (· ≤ ·)).mp (List.getElem_mem j.isLt)
      · intro i _ j _ h
        exact Fin.ext ((Finset.sort_nodup _ _).getElem_inj_iff.mp h)
      · intro i hi
        have hm : i ∈ (A ∆ B).sort (· ≤ ·) := (Finset.mem_sort (· ≤ ·)).mpr hi
        refine ⟨⟨_, List.idxOf_lt_length_iff.mpr hm⟩, Finset.mem_univ _, ?_⟩
        simp
      · intro j _
        simp only [Fin.getElem_fin, (Finset.sort_nodup _ _).idxOf_getElem]

private theorem matrix_sum_alt {n : ℕ} (G : SubsetSignature n R)
    (A B : Finset (Fin n)) (xs : List (Fin n)) :
    matchgateSum G A B xs = matrixAlt (fun i => G (A ∆ {i}) * G (B ∆ {i})) xs := by
  rw [matrixAlt_eq]
  unfold matchgateSum
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem matrix_mgi_self {n : ℕ} {G : SubsetSignature n R}
    (hG : MatchgateIdentities G) (A B : Finset (Fin n)) : mgiBilinear G G A B = 0 := by
  rw [matrix_mgi_alt, ← matrix_sum_alt]
  exact hG A B

private theorem matrix_block_split {r s : ℕ} (Q : SubsetSignature (r + s) R)
    (X Z : Finset (Fin r)) (A B : Finset (Fin s)) :
    mgiBilinear Q Q (blockJoin X A) (blockJoin Z B) =
      mgiBilinear (fun W => Q (blockJoin W A)) (fun W => Q (blockJoin W B)) X Z +
      (-1 : R) ^ (X ∆ Z).card *
      mgiBilinear (fun W => Q (blockJoin X W)) (fun W => Q (blockJoin Z W)) A B := by
  rw [matrix_mgi_alt, blockJoin_symmDiff, sort_blocks]
  simp only [firstBlock_blockJoin, secondBlock_blockJoin, matrixAlt_append,
    matrixAlt_map, List.length_map, Finset.length_sort, blockJoin_flip_left,
    blockJoin_flip_right, matrix_mgi_alt]

private theorem matrix_bilinear_reverse {n : ℕ} (F G : SubsetSignature n R)
    (A B : Finset (Fin n)) :
    mgiBilinear F G (reversePortSubset A) (reversePortSubset B) =
      (-1 : R) ^ ((A ∆ B).card + 1) *
        mgiBilinear (fun X => F (reversePortSubset X))
          (fun X => G (reversePortSubset X)) A B := by
  rw [matrix_mgi_alt, ← reversePortSubset_symmDiff, sort_reversePortSubset,
    matrixAlt_reverse, matrixAlt_map]
  simp only [List.length_map, Finset.length_sort, matrix_mgi_alt,
    reversePortSubset_symmDiff, reversePortSubset_singleton]

private theorem matrix_blockJoin_blocks {r s : ℕ} (S : Finset (Fin (r + s))) :
    blockJoin (firstBlock S) (secondBlock S) = S := by
  ext i
  induction i using Fin.addCases with
  | left i => simp only [← mem_firstBlock, firstBlock_blockJoin]
  | right i => simp only [← mem_secondBlock, secondBlock_blockJoin]

private theorem matrix_sign_square (n : ℕ) : (-1 : R) ^ n * (-1 : R) ^ n = 1 := by
  rw [← mul_pow]
  simp

private theorem matrix_sum_rotate {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (f : α → β → γ → R) :
    (∑ a, ∑ b, ∑ c, f a b c) = ∑ c, ∑ a, ∑ b, f a b c := by
  classical
  calc
    _ = ∑ a, ∑ c, ∑ b, f a b c := by
      apply Finset.sum_congr rfl
      intro a _
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm

private def matrixXorEquiv {r : ℕ} (i : Fin r) : Finset (Fin r) ≃ Finset (Fin r) where
  toFun X := X ∆ {i}
  invFun X := X ∆ {i}
  left_inv _ := symmDiff_symmDiff_cancel_right _ _
  right_inv _ := symmDiff_symmDiff_cancel_right _ _

private theorem matrix_xor_common {r : ℕ} (X Z P : Finset (Fin r)) :
    (X ∆ P) ∆ (Z ∆ P) = X ∆ Z := by
  rw [symmDiff_symmDiff_symmDiff_comm, symmDiff_self, symmDiff_bot]

private theorem matrix_toggle_transfer {r : ℕ}
    (c : Finset (Fin r) → Fin r → R) (F G U V : SubsetSignature r R) :
    (∑ X, ∑ Z, ∑ i, c (X ∆ Z) i * F X * G Z * U (X ∆ {i}) * V (Z ∆ {i})) =
      ∑ X, ∑ Z, ∑ i, c (X ∆ Z) i * F (X ∆ {i}) * G (Z ∆ {i}) * U X * V Z := by
  classical
  conv_lhs => rw [matrix_sum_rotate]
  conv_rhs => rw [matrix_sum_rotate]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_equiv (matrixXorEquiv i)
  · simp
  · intro X _
    apply Finset.sum_equiv (matrixXorEquiv i)
    · simp
    · intro Z _
      simp only [matrixXorEquiv, Equiv.coe_fn_mk, matrix_xor_common,
        symmDiff_symmDiff_cancel_right]

/-- Contraction of opposite physical orders, retaining both exterior blocks. -/
def orderedBlockContraction {r t s : ℕ}
    (P : SubsetSignature (r + t) R) (Q : SubsetSignature (t + s) R) :
    SubsetSignature (r + s) R := fun S =>
  ∑ X, P (blockJoin (firstBlock S) (reversePortSubset X)) * Q (blockJoin X (secondBlock S))

@[simp] theorem orderedBlockContraction_blockJoin {r t s : ℕ}
    (P : SubsetSignature (r + t) R) (Q : SubsetSignature (t + s) R)
    (A : Finset (Fin r)) (B : Finset (Fin s)) :
    orderedBlockContraction P Q (blockJoin A B) =
      ∑ X, P (blockJoin A (reversePortSubset X)) * Q (blockJoin X B) := by
  simp [orderedBlockContraction]

private theorem matrix_bilinear_sum {n t : ℕ}
    (P Q : Finset (Fin t) → SubsetSignature n R)
    (A B : Finset (Fin n)) :
    mgiBilinear (fun W => ∑ X, P X W) (fun W => ∑ X, Q X W) A B =
      ∑ X, ∑ Z, mgiBilinear (P X) (Q Z) A B := by
  classical
  unfold mgiBilinear
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [← matrix_sum_rotate, Finset.sum_comm]

private theorem matrix_bilinear_mul {n : ℕ} (F G : SubsetSignature n R)
    (a b : R) (A B : Finset (Fin n)) :
    mgiBilinear (fun W => F W * a) (fun W => G W * b) A B =
      mgiBilinear F G A B * a * b := by
  unfold mgiBilinear
  simp only [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Exact retained-block closure, with reversal on the joined block. -/
theorem MatchgateIdentities.orderedBlockContraction {r t s : ℕ}
    {P : SubsetSignature (r + t) R} {Q : SubsetSignature (t + s) R}
    (hP : MatchgateIdentities P) (hQ : MatchgateIdentities Q) :
    MatchgateIdentities (MatchgateWidth.orderedBlockContraction P Q) := by
  classical
  intro U V
  rw [matrix_sum_alt, ← matrix_mgi_alt]
  rw [← matrix_blockJoin_blocks U, ← matrix_blockJoin_blocks V]
  generalize firstBlock U = A
  generalize firstBlock V = C
  generalize secondBlock U = B
  generalize secondBlock V = D
  rw [matrix_block_split]
  simp only [orderedBlockContraction_blockJoin, matrix_bilinear_sum, matrix_bilinear_mul]
  have hp (X Z : Finset (Fin t)) := matrix_mgi_self hP
    (blockJoin A (reversePortSubset X)) (blockJoin C (reversePortSubset Z))
  simp only [matrix_block_split, matrix_bilinear_reverse] at hp
  have hq (X Z : Finset (Fin t)) := matrix_mgi_self hQ (blockJoin X B) (blockJoin Z D)
  simp only [matrix_block_split] at hq
  have hpleft (X Z : Finset (Fin t)) :
      mgiBilinear (fun W => P (blockJoin W (reversePortSubset X)))
        (fun W => P (blockJoin W (reversePortSubset Z))) A C =
      (-1 : R) ^ (A ∆ C).card * (-1 : R) ^ (X ∆ Z).card *
        mgiBilinear (fun W => P (blockJoin A (reversePortSubset W)))
          (fun W => P (blockJoin C (reversePortSubset W))) X Z := by
    have h := hp X Z
    simp only [pow_succ] at h
    linear_combination h
  have hqright (X Z : Finset (Fin t)) :
      mgiBilinear (fun W => Q (blockJoin X W)) (fun W => Q (blockJoin Z W)) B D =
      -((-1 : R) ^ (X ∆ Z).card *
        mgiBilinear (fun W => Q (blockJoin W B)) (fun W => Q (blockJoin W D)) X Z) := by
    have h := congrArg (fun z : R => (-1 : R) ^ (X ∆ Z).card * z) (hq X Z)
    simp only [mul_add, ← mul_assoc, matrix_sign_square, one_mul, mul_zero] at h
    linear_combination h
  have hr (X Z : Finset (Fin t)) :
      mgiBilinear
        (fun W => P (blockJoin A (reversePortSubset X)) * Q (blockJoin X W))
        (fun W => P (blockJoin C (reversePortSubset Z)) * Q (blockJoin Z W)) B D =
      P (blockJoin A (reversePortSubset X)) * P (blockJoin C (reversePortSubset Z)) *
        mgiBilinear (fun W => Q (blockJoin X W)) (fun W => Q (blockJoin Z W)) B D := by
    unfold mgiBilinear
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp_rw [hpleft, hr, hqright]
  have ht := matrix_toggle_transfer
    (fun E i => (-1 : R) ^ E.card * mgiCoeff E i)
    (fun X => P (blockJoin A (reversePortSubset X)))
    (fun X => P (blockJoin C (reversePortSubset X)))
    (fun X => Q (blockJoin X B)) (fun X => Q (blockJoin X D))
  have he :
      (∑ X, ∑ Z, (-1 : R) ^ (X ∆ Z).card *
        mgiBilinear (fun W => P (blockJoin A (reversePortSubset W)))
          (fun W => P (blockJoin C (reversePortSubset W))) X Z *
        Q (blockJoin X B) * Q (blockJoin Z D)) =
      ∑ X, ∑ Z, P (blockJoin A (reversePortSubset X)) *
        P (blockJoin C (reversePortSubset Z)) * ((-1 : R) ^ (X ∆ Z).card *
          mgiBilinear (fun W => Q (blockJoin W B)) (fun W => Q (blockJoin W D)) X Z) := by
    simp only [mgiBilinear, Finset.mul_sum, Finset.sum_mul]
    convert ht.symm using 1 <;>
      apply Finset.sum_congr rfl <;> intro X _ <;>
      apply Finset.sum_congr rfl <;> intro Z _ <;>
      apply Finset.sum_congr rfl <;> intro i _ <;> ring
  calc
    _ = (-1 : R) ^ (A ∆ C).card *
        ((∑ X, ∑ Z, (-1 : R) ^ (X ∆ Z).card *
          mgiBilinear (fun W => P (blockJoin A (reversePortSubset W)))
            (fun W => P (blockJoin C (reversePortSubset W))) X Z *
          Q (blockJoin X B) * Q (blockJoin Z D)) -
        (∑ X, ∑ Z, P (blockJoin A (reversePortSubset X)) *
          P (blockJoin C (reversePortSubset Z)) * ((-1 : R) ^ (X ∆ Z).card *
            mgiBilinear (fun W => Q (blockJoin W B)) (fun W => Q (blockJoin W D)) X Z))) := by
      simp only [sub_eq_add_neg, mul_add, Finset.mul_sum, mul_neg, ← Finset.sum_neg_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro X _
      apply Finset.sum_congr rfl
      intro Z _
      ring
    _ = 0 := by rw [he, sub_self, mul_zero]

/-- The noncrossing equality tensor with reversed output boundary order. -/
def orderedEqualitySignature (n : ℕ) : SubsetSignature (n + n) R := fun S =>
  if firstBlock S = reversePortSubset (secondBlock S) then 1 else 0

@[simp] theorem orderedEqualitySignature_blockJoin {n : ℕ}
    (A B : Finset (Fin n)) :
    orderedEqualitySignature (R := R) n (blockJoin A B) =
      if A = reversePortSubset B then 1 else 0 := by
  simp [orderedEqualitySignature]

private theorem matrix_delta_cancel {n : ℕ} (A B C D : Finset (Fin n)) :
    mgiBilinear (fun W => if W = B then (1 : R) else 0)
      (fun W => if W = D then (1 : R) else 0) A C +
    (-1 : R) ^ (A ∆ C).card * (-1 : R) ^ ((B ∆ D).card + 1) *
      mgiBilinear (fun W => if A = W then (1 : R) else 0)
        (fun W => if C = W then (1 : R) else 0) B D = 0 := by
  classical
  unfold mgiBilinear
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro i _
  have hA : A ∆ {i} = B ↔ A = B ∆ {i} := by
    constructor
    · intro h; rw [← h]; simp
    · intro h; rw [h]; simp
  have hC : C ∆ {i} = D ↔ C = D ∆ {i} := by
    constructor
    · intro h; rw [← h]; simp
    · intro h; rw [h]; simp
  by_cases ha : A = B ∆ {i}
  · by_cases hc : C = D ∆ {i}
    · subst A C
      simp only [matrix_xor_common, symmDiff_symmDiff_cancel_right, ite_true, mul_one,
        pow_succ, ← mul_assoc, matrix_sign_square]
      ring
    · simp [hC, ha, hc]
  · simp [hA, hC, ha]

/-- The identity wire tensor satisfies the literal identities at every width,
including width zero. -/
theorem orderedEqualitySignature_matchgateIdentities (n : ℕ) :
    MatchgateIdentities (orderedEqualitySignature (R := R) n) := by
  intro U V
  rw [matrix_sum_alt, ← matrix_mgi_alt]
  have h (A B C D : Finset (Fin n)) :
      mgiBilinear (orderedEqualitySignature (R := R) n) (orderedEqualitySignature n)
        (blockJoin A (reversePortSubset B)) (blockJoin C (reversePortSubset D)) = 0 := by
    rw [matrix_block_split, matrix_bilinear_reverse]
    simp only [orderedEqualitySignature_blockJoin, reversePortSubset_reversePortSubset]
    simpa only [mul_assoc] using matrix_delta_cancel (R := R) A B C D
  simpa only [reversePortSubset_reversePortSubset, matrix_blockJoin_blocks] using
    h (firstBlock U) (reversePortSubset (secondBlock U))
      (firstBlock V) (reversePortSubset (secondBlock V))

/-- Read a matrix in boundary order: inputs increase, while output port `j`
appears at physical position `r + j.rev`. -/
def orderedMatrixSignature {r t : ℕ}
    (P : Matrix (BooleanInput r) (BooleanInput t) R) : BooleanTable (r + t) R :=
  fun z => P (fun i => z (Fin.castAdd t i)) (fun j => z (Fin.natAdd r j.rev))

/-- Literal MGI locus of matrices in the increasing-input, reversed-output
boundary convention. -/
def OrderedMatchgateMatrix {r t : ℕ}
    (P : Matrix (BooleanInput r) (BooleanInput t) R) : Prop :=
  BooleanMatchgateIdentities (orderedMatrixSignature P)

/-- Subset-coordinate form of the matrix boundary convention. -/
def orderedMatrixSubsetSignature {r t : ℕ}
    (P : Matrix (BooleanInput r) (BooleanInput t) R) : SubsetSignature (r + t) R :=
  fun S => P ((booleanSubsetEquiv r).symm (firstBlock S))
    ((booleanSubsetEquiv t).symm (reversePortSubset (secondBlock S)))

omit [CommRing R] in
@[simp] theorem orderedMatrixSignature_subset {r t : ℕ}
    (P : Matrix (BooleanInput r) (BooleanInput t) R) (S : Finset (Fin (r + t))) :
    orderedMatrixSignature P ((booleanSubsetEquiv (r + t)).symm S) =
      orderedMatrixSubsetSignature P S := by
  unfold orderedMatrixSignature orderedMatrixSubsetSignature
  congr 1
  · funext i
    simp [booleanSubsetEquiv]
  · funext i
    simp [booleanSubsetEquiv]

theorem orderedMatchgateMatrix_iff {r t : ℕ}
    (P : Matrix (BooleanInput r) (BooleanInput t) R) :
    OrderedMatchgateMatrix P ↔ MatchgateIdentities (orderedMatrixSubsetSignature P) := by
  simp only [OrderedMatchgateMatrix, BooleanMatchgateIdentities, orderedMatrixSignature_subset]

omit [CommRing R] in
@[simp] theorem orderedMatrixSubsetSignature_blockJoin {r t : ℕ}
    (P : Matrix (BooleanInput r) (BooleanInput t) R)
    (A : Finset (Fin r)) (B : Finset (Fin t)) :
    orderedMatrixSubsetSignature P (blockJoin A B) =
      P ((booleanSubsetEquiv r).symm A) ((booleanSubsetEquiv t).symm (reversePortSubset B)) := by
  simp [orderedMatrixSubsetSignature]

/-- The algebraic contraction above is precisely ordinary matrix multiplication,
with neither a sign twist nor a permutation of the surviving indices. -/
theorem orderedMatrixSubsetSignature_mul {r t s : ℕ}
    (P : Matrix (BooleanInput r) (BooleanInput t) R)
    (Q : Matrix (BooleanInput t) (BooleanInput s) R) :
    orderedMatrixSubsetSignature (P * Q) =
      orderedBlockContraction (orderedMatrixSubsetSignature P) (orderedMatrixSubsetSignature Q) := by
  classical
  funext S
  simp only [orderedMatrixSubsetSignature, Matrix.mul_apply, orderedBlockContraction,
    firstBlock_blockJoin, secondBlock_blockJoin, reversePortSubset_reversePortSubset]
  exact ((booleanSubsetEquiv t).symm.sum_comp
    (fun x => P ((booleanSubsetEquiv r).symm (firstBlock S)) x *
      Q x ((booleanSubsetEquiv s).symm (reversePortSubset (secondBlock S))))).symm

/-- Ordinary multiplication closes the literal MGI matrix locus exactly in the
opposite physical order on the identified ports. -/
theorem OrderedMatchgateMatrix.mul {r t s : ℕ}
    {P : Matrix (BooleanInput r) (BooleanInput t) R}
    {Q : Matrix (BooleanInput t) (BooleanInput s) R}
    (hP : OrderedMatchgateMatrix P) (hQ : OrderedMatchgateMatrix Q) :
    OrderedMatchgateMatrix (P * Q) := by
  rw [orderedMatchgateMatrix_iff, orderedMatrixSubsetSignature_mul]
  exact ((orderedMatchgateMatrix_iff P).mp hP).orderedBlockContraction
    ((orderedMatchgateMatrix_iff Q).mp hQ)

@[simp] theorem orderedMatrixSubsetSignature_one (n : ℕ) :
    orderedMatrixSubsetSignature (1 : Matrix (BooleanInput n) (BooleanInput n) R) =
      orderedEqualitySignature n := by
  classical
  funext S
  simp only [orderedMatrixSubsetSignature, Matrix.one_apply, Equiv.apply_eq_iff_eq,
    orderedEqualitySignature]

/-- Identity matrices belong to the ordered matchgate class at every width. -/
theorem OrderedMatchgateMatrix.one (n : ℕ) :
    OrderedMatchgateMatrix (1 : Matrix (BooleanInput n) (BooleanInput n) R) := by
  rw [orderedMatchgateMatrix_iff, orderedMatrixSubsetSignature_one]
  exact orderedEqualitySignature_matchgateIdentities n

/-- Every natural power, including the zeroth, remains in the literal ordered
matchgate locus. -/
theorem OrderedMatchgateMatrix.pow {n : ℕ}
    {P : Matrix (BooleanInput n) (BooleanInput n) R}
    (hP : OrderedMatchgateMatrix P) (k : ℕ) : OrderedMatchgateMatrix (P ^ k) := by
  induction k with
  | zero => simpa only [pow_zero] using OrderedMatchgateMatrix.one (R := R) n
  | succ k ih => simpa only [pow_succ] using ih.mul hP

end MatchgateWidth
