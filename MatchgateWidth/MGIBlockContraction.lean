import MatchgateWidth.MGIOperations

/-!
# Whole-leaf contraction in the exact boundary order

The entire first signature is contracted against the initial block of the
second. No signature with an additional retained block is covered by this
operation. The proof transfers the literal alternating identities across a
finite double sum by simultaneously flipping the two contracted words.
-/

namespace MatchgateWidth
open scoped symmDiff

variable {R : Type*} [CommRing R]

/-- Join two Boolean subsets in consecutive port order. -/
def blockJoin {r s : ℕ} (X : Finset (Fin r)) (Y : Finset (Fin s)) :
    Finset (Fin (r + s)) :=
  X.map (Fin.castAddEmb s) ∪ Y.map (Fin.natAddEmb r)

@[simp] theorem firstBlock_blockJoin {r s : ℕ}
    (X : Finset (Fin r)) (Y : Finset (Fin s)) : firstBlock (blockJoin X Y) = X := by
  ext i
  simp only [mem_firstBlock, blockJoin, Finset.mem_union, Finset.mem_map]
  constructor
  · rintro (⟨j, hj, he⟩ | ⟨j, hj, he⟩)
    · have hji : j = i := (Fin.castAddEmb s).injective he
      simpa only [hji] using hj
    · have he := congrArg Fin.val he
      change r + j.val = i.val at he
      omega
  · exact fun hi => Or.inl ⟨i, hi, rfl⟩

@[simp] theorem secondBlock_blockJoin {r s : ℕ}
    (X : Finset (Fin r)) (Y : Finset (Fin s)) : secondBlock (blockJoin X Y) = Y := by
  ext i
  simp only [mem_secondBlock, blockJoin, Finset.mem_union, Finset.mem_map]
  constructor
  · rintro (⟨j, hj, he⟩ | ⟨j, hj, he⟩)
    · have he := congrArg Fin.val he
      change j.val = r + i.val at he
      omega
    · have hji : j = i := (Fin.natAddEmb r).injective he
      simpa only [hji] using hj
  · exact fun hi => Or.inr ⟨i, hi, rfl⟩

private theorem block_ext {r s : ℕ} {U V : Finset (Fin (r + s))}
    (h₁ : firstBlock U = firstBlock V) (h₂ : secondBlock U = secondBlock V) : U = V := by
  ext i
  induction i using Fin.addCases with
  | left i => simpa only [← mem_firstBlock] using Finset.ext_iff.mp h₁ i
  | right i => simpa only [← mem_secondBlock] using Finset.ext_iff.mp h₂ i

@[simp] theorem blockJoin_symmDiff {r s : ℕ}
    (X Z : Finset (Fin r)) (A B : Finset (Fin s)) :
    blockJoin X A ∆ blockJoin Z B = blockJoin (X ∆ Z) (A ∆ B) := by
  apply block_ext <;> simp

@[simp] theorem blockJoin_flip_left {r s : ℕ}
    (X : Finset (Fin r)) (A : Finset (Fin s)) (i : Fin r) :
    blockJoin X A ∆ {Fin.castAdd s i} = blockJoin (X ∆ {i}) A := by
  apply block_ext <;> simp

@[simp] theorem blockJoin_flip_right {r s : ℕ}
    (X : Finset (Fin r)) (A : Finset (Fin s)) (i : Fin s) :
    blockJoin X A ∆ {Fin.natAdd r i} = blockJoin X (A ∆ {i}) := by
  apply block_ext <;> simp

private def altSum {α : Type*} (w : α → R) : List α → R
  | [] => 0
  | a :: xs => -w a - altSum w xs

private theorem altSum_eq {α : Type*} (w : α → R) (xs : List α) :
    altSum w xs = ∑ j : Fin xs.length, (-1 : R) ^ (j.val + 1) * w xs[j] := by
  induction xs with
  | nil => simp [altSum]
  | cons a xs ih =>
    simp only [altSum, ih, List.length_cons, Fin.sum_univ_succ,
      Fin.val_zero, zero_add, pow_one, neg_one_mul, Fin.val_succ]
    rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    simp [pow_succ]

private theorem altSum_append {α : Type*} (w : α → R) (xs ys : List α) :
    altSum w (xs ++ ys) = altSum w xs + (-1 : R) ^ xs.length * altSum w ys := by
  induction xs with
  | nil => simp [altSum]
  | cons a xs ih => simp only [List.cons_append, altSum, List.length_cons, ih, pow_succ]; ring

private theorem altSum_map {α β : Type*} (w : β → R) (f : α → β) (xs : List α) :
    altSum w (xs.map f) = altSum (fun a => w (f a)) xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [altSum, ih]

private theorem matchgateSum_alt {s : ℕ} (G : SubsetSignature s R)
    (A B : Finset (Fin s)) (xs : List (Fin s)) :
    matchgateSum G A B xs = altSum (fun i => G (A ∆ {i}) * G (B ∆ {i})) xs := by
  rw [altSum_eq]
  unfold matchgateSum
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The coefficient of a port in its sorted symmetric-difference list. -/
def mgiCoeff {n : ℕ} (D : Finset (Fin n)) (i : Fin n) : R :=
  if i ∈ D then (-1 : R) ^ ((D.sort (· ≤ ·)).idxOf i + 1) else 0

private theorem altSum_sort {n : ℕ} (w : Fin n → R) (D : Finset (Fin n)) :
    altSum w (D.sort (· ≤ ·)) = ∑ i, mgiCoeff D i * w i := by
  classical
  rw [altSum_eq]
  symm
  calc
    ∑ i, mgiCoeff D i * w i = ∑ i ∈ D, (-1 : R) ^ ((D.sort (· ≤ ·)).idxOf i + 1) * w i := by
      simp [mgiCoeff]
    _ = ∑ j : Fin (D.sort (· ≤ ·)).length, (-1 : R) ^ (j.val + 1) * w (D.sort (· ≤ ·))[j] := by
      symm
      apply Finset.sum_bij (fun j _ => (D.sort (· ≤ ·))[j])
      · intro j _
        exact (Finset.mem_sort (· ≤ ·)).mp (List.getElem_mem j.isLt)
      · intro i _ j _ h
        exact Fin.ext ((Finset.sort_nodup _ _).getElem_inj_iff.mp h)
      · intro i hi
        have hm : i ∈ D.sort (· ≤ ·) := (Finset.mem_sort (· ≤ ·)).mpr hi
        refine ⟨⟨(D.sort (· ≤ ·)).idxOf i, List.idxOf_lt_length_iff.mpr hm⟩, Finset.mem_univ _, ?_⟩
        simp
      · intro j _
        simp only [Fin.getElem_fin, (Finset.sort_nodup _ _).idxOf_getElem]

/-- Bilinear form with the literal MGI coefficients. -/
def mgiBilinear {n : ℕ} (F G : SubsetSignature n R)
    (A B : Finset (Fin n)) : R :=
  ∑ i, mgiCoeff (A ∆ B) i * F (A ∆ {i}) * G (B ∆ {i})

private theorem mgiBilinear_alt {n : ℕ} (F G : SubsetSignature n R)
    (A B : Finset (Fin n)) : mgiBilinear F G A B =
      altSum (fun i => F (A ∆ {i}) * G (B ∆ {i})) ((A ∆ B).sort (· ≤ ·)) := by
  rw [altSum_sort]
  simp only [mgiBilinear, mul_assoc]

private theorem mgiBilinear_self {n : ℕ} {G : SubsetSignature n R}
    (hG : MatchgateIdentities G) (A B : Finset (Fin n)) : mgiBilinear G G A B = 0 := by
  rw [mgiBilinear_alt, ← matchgateSum_alt]
  exact hG A B

/-- Split the second signature's identity at the contracted boundary block.
The suffix is shifted by exactly the size of the prefix difference. -/
private theorem mgi_block_split {r s : ℕ} {Q : SubsetSignature (r + s) R}
    (hQ : MatchgateIdentities Q) (X Z : Finset (Fin r)) (A B : Finset (Fin s)) :
    mgiBilinear (fun W => Q (blockJoin W A)) (fun W => Q (blockJoin W B)) X Z +
      (-1 : R) ^ (X ∆ Z).card *
      mgiBilinear (fun W => Q (blockJoin X W)) (fun W => Q (blockJoin Z W)) A B = 0 := by
  have h := hQ (blockJoin X A) (blockJoin Z B)
  rw [matchgateSum_alt, blockJoin_symmDiff, sort_blocks] at h
  simp only [firstBlock_blockJoin, secondBlock_blockJoin, altSum_append,
    altSum_map, List.length_map, Finset.length_sort, blockJoin_flip_left,
    blockJoin_flip_right] at h
  simpa only [mgiBilinear_alt] using h

private def xorEquiv {r : ℕ} (i : Fin r) : Finset (Fin r) ≃ Finset (Fin r) where
  toFun X := X ∆ {i}
  invFun X := X ∆ {i}
  left_inv _ := symmDiff_symmDiff_cancel_right _ _
  right_inv _ := symmDiff_symmDiff_cancel_right _ _

private theorem xor_common {r : ℕ} (X Z P : Finset (Fin r)) :
    (X ∆ P) ∆ (Z ∆ P) = X ∆ Z := by
  rw [symmDiff_symmDiff_symmDiff_comm, symmDiff_self, symmDiff_bot]

/-- Transfer a toggle between the two factors of a double contraction. The
coefficient is permitted to depend on the difference, which is unchanged by
simultaneously toggling both contracted words. -/
private theorem toggle_transfer {r : ℕ}
    (c : Finset (Fin r) → Fin r → R) (g U V : SubsetSignature r R) (i : Fin r) :
    (∑ X, ∑ Z, c (X ∆ Z) i * g X * g Z * U (X ∆ {i}) * V (Z ∆ {i})) =
      ∑ X, ∑ Z, c (X ∆ Z) i * g (X ∆ {i}) * g (Z ∆ {i}) * U X * V Z := by
  classical
  apply Finset.sum_equiv (xorEquiv i)
  · simp
  · intro X _
    apply Finset.sum_equiv (xorEquiv i)
    · simp
    · intro Z _
      simp only [xorEquiv, Equiv.coe_fn_mk, xor_common, symmDiff_symmDiff_cancel_right]

private theorem sum_rotate {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (f : α → β → γ → R) :
    (∑ a, ∑ b, ∑ c, f a b c) = ∑ c, ∑ a, ∑ b, f a b c := by
  classical
  calc
    _ = ∑ a, ∑ c, ∑ b, f a b c := by
      apply Finset.sum_congr rfl
      intro a _
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm

private theorem toggle_transfer_sum {r : ℕ}
    (c : Finset (Fin r) → Fin r → R) (g U V : SubsetSignature r R) :
    (∑ X, ∑ Z, ∑ i, c (X ∆ Z) i * g X * g Z * U (X ∆ {i}) * V (Z ∆ {i})) =
      ∑ X, ∑ Z, ∑ i, c (X ∆ Z) i * g (X ∆ {i}) * g (Z ∆ {i}) * U X * V Z := by
  classical
  calc
    _ = ∑ i, ∑ X, ∑ Z, c (X ∆ Z) i * g X * g Z * U (X ∆ {i}) * V (Z ∆ {i}) := sum_rotate _
    _ = ∑ i, ∑ X, ∑ Z, c (X ∆ Z) i * g (X ∆ {i}) * g (Z ∆ {i}) * U X * V Z := by
      apply Finset.sum_congr rfl
      intro i _
      exact toggle_transfer c g U V i
    _ = _ := (sum_rotate _).symm

/-- Contract an entire leaf against the first consecutive block of `Q`.
The remaining ports of `Q` retain their original order. -/
def unaryBlockContraction {r s : ℕ} (g : SubsetSignature r R)
    (Q : SubsetSignature (r + s) R) : SubsetSignature s R :=
  fun A => ∑ X, g X * Q (blockJoin X A)

private theorem contraction_bilinear {r s : ℕ} (g : SubsetSignature r R)
    (Q : SubsetSignature (r + s) R) (A B : Finset (Fin s)) :
    mgiBilinear (unaryBlockContraction g Q) (unaryBlockContraction g Q) A B =
      ∑ X, ∑ Z, g X * g Z *
        mgiBilinear (fun W => Q (blockJoin X W)) (fun W => Q (blockJoin Z W)) A B := by
  classical
  unfold mgiBilinear unaryBlockContraction
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [← sum_rotate, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro X _
  apply Finset.sum_congr rfl
  intro Z _
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem sign_square (n : ℕ) : (-1 : R) ^ n * (-1 : R) ^ n = 1 := by
  rw [← mul_pow]
  simp

/-- Whole-leaf contraction preserves the literal MGI, including either empty
block. This is proved directly from both identities, with no graphical
realization and no same-order two-retained-block closure assumption. -/
theorem MatchgateIdentities.unaryBlockContraction {r s : ℕ}
    {g : SubsetSignature r R} {Q : SubsetSignature (r + s) R}
    (hg : MatchgateIdentities g) (hQ : MatchgateIdentities Q) :
    MatchgateIdentities (MatchgateWidth.unaryBlockContraction g Q) := by
  classical
  intro A B
  rw [matchgateSum_alt, ← mgiBilinear_alt, contraction_bilinear]
  have hsplit (X Z : Finset (Fin r)) :
      mgiBilinear (fun W => Q (blockJoin X W)) (fun W => Q (blockJoin Z W)) A B =
        -((-1 : R) ^ (X ∆ Z).card *
          mgiBilinear (fun W => Q (blockJoin W A)) (fun W => Q (blockJoin W B)) X Z) := by
    have h := mgi_block_split hQ X Z A B
    have hs := sign_square (R := R) (X ∆ Z).card
    have h' := congrArg (fun z : R => (-1 : R) ^ (X ∆ Z).card * z) h
    simp only [mul_add, ← mul_assoc, hs, one_mul, mul_zero] at h'
    linear_combination h' 
  simp_rw [hsplit]
  have ht := toggle_transfer_sum
    (fun D i => (-1 : R) ^ D.card * mgiCoeff D i) g
    (fun X => Q (blockJoin X A)) (fun X => Q (blockJoin X B))
  have hz : (∑ X, ∑ Z, ∑ i,
      ((-1 : R) ^ (X ∆ Z).card * mgiCoeff (X ∆ Z) i) *
        g X * g Z * Q (blockJoin (X ∆ {i}) A) * Q (blockJoin (Z ∆ {i}) B)) = 0 := by
    rw [ht]
    apply Finset.sum_eq_zero
    intro X _
    apply Finset.sum_eq_zero
    intro Z _
    calc
      _ = (-1 : R) ^ (X ∆ Z).card * mgiBilinear g g X Z *
          Q (blockJoin X A) * Q (blockJoin Z B) := by
        simp only [mgiBilinear, Finset.mul_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = 0 := by rw [mgiBilinear_self hg, mul_zero, zero_mul, zero_mul]
  calc
    _ = -(∑ X, ∑ Z, ∑ i,
      ((-1 : R) ^ (X ∆ Z).card * mgiCoeff (X ∆ Z) i) *
        g X * g Z * Q (blockJoin (X ∆ {i}) A) * Q (blockJoin (Z ∆ {i}) B)) := by
      simp_rw [mgiBilinear, mul_neg, Finset.mul_sum]
      simp only [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro X _
      apply Finset.sum_congr rfl
      intro Z _
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = 0 := by rw [hz, neg_zero]

@[simp] theorem booleanSubsetEquiv_symm_blockJoin {r s : ℕ}
    (X : Finset (Fin r)) (A : Finset (Fin s)) :
    (booleanSubsetEquiv (r + s)).symm (blockJoin X A) =
      Fin.append ((booleanSubsetEquiv r).symm X) ((booleanSubsetEquiv s).symm A) := by
  funext i
  induction i using Fin.addCases with
  | left i =>
    rw [Fin.append_left]
    change (if Fin.castAdd s i ∈ blockJoin X A then 1 else 0) = (if i ∈ X then 1 else 0)
    simp only [← mem_firstBlock, firstBlock_blockJoin]
  | right i =>
    rw [Fin.append_right]
    change (if Fin.natAdd r i ∈ blockJoin X A then 1 else 0) = (if i ∈ A then 1 else 0)
    simp only [← mem_secondBlock, secondBlock_blockJoin]

/-- The exact Boolean-coordinate form of whole-leaf contraction used for an
ordered unary block in the Section 9 star. There is no reversal in the
resulting formula: both leaf and right-hand tensor use the same word `x`. -/
theorem BooleanMatchgateIdentities.unaryBlockContraction {r s : ℕ}
    {g : BooleanTable r R} {Q : BooleanTable (r + s) R}
    (hg : BooleanMatchgateIdentities g) (hQ : BooleanMatchgateIdentities Q) :
    BooleanMatchgateIdentities (fun y => ∑ x : BooleanInput r, g x * Q (Fin.append x y)) := by
  classical
  have h := MatchgateIdentities.unaryBlockContraction hg hQ
  have heq : MatchgateWidth.unaryBlockContraction
      (fun X => g ((booleanSubsetEquiv r).symm X))
      (fun S => Q ((booleanSubsetEquiv (r + s)).symm S)) =
      (fun A => ∑ x : BooleanInput r, g x * Q (Fin.append x ((booleanSubsetEquiv s).symm A))) := by
    funext A
    simp only [MatchgateWidth.unaryBlockContraction, booleanSubsetEquiv_symm_blockJoin]
    exact (booleanSubsetEquiv r).symm.sum_comp
      (fun x => g x * Q (Fin.append x ((booleanSubsetEquiv s).symm A)))
  rw [heq] at h
  exact h

/-- The empty contracted block contributes precisely the unique leaf scalar. -/
@[simp] theorem unaryBlockContraction_zero_left {s : ℕ}
    (g : SubsetSignature 0 R) (Q : SubsetSignature (0 + s) R) (A : Finset (Fin s)) :
    unaryBlockContraction g Q A = g ∅ * Q (blockJoin ∅ A) := by
  classical
  have hd : (default : Finset (Fin 0)) = ∅ := Subsingleton.elim _ _
  simp [unaryBlockContraction, hd]

/-- No surviving ports: the operation is exactly the ordinary scalar pairing. -/
theorem unaryBlockContraction_zero_right {r : ℕ}
    (g : SubsetSignature r R) (Q : SubsetSignature (r + 0) R) :
    unaryBlockContraction g Q ∅ = ∑ X, g X * Q (blockJoin X ∅) := rfl

end MatchgateWidth
