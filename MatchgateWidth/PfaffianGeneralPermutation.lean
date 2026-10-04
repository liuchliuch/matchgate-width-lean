import MatchgateWidth.PfaffianPermutation
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Data.List.OfFn
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# The full coordinate-permutation law for Pfaffians

The adjacent-coordinate law extends to arbitrary finite permutations, with the
ordinary permutation sign. The matrix version identifies that sign with the
determinant of the coordinate permutation matrix.
-/

namespace MatchgateWidth

variable {R ι : Type*} [CommRing R]

private theorem pfaffianList_ofFn_swap_adjacent (A : Matrix ι ι R)
    (hskew : ∀ x y, A x y = -A y x) {n : ℕ} (i : Fin n)
    (f : Fin (n + 1) → ι) (pre : List ι) :
    pfaffianList A (pre ++ List.ofFn (f ∘ Equiv.swap i.castSucc i.succ)) =
      -pfaffianList A (pre ++ List.ofFn f) := by
  induction n generalizing pre with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun i => ?_) i
    · have hlist : List.ofFn (f ∘ Equiv.swap (0 : Fin (n + 2)) 1) =
          f 1 :: f 0 :: List.ofFn (fun j : Fin n => f j.succ.succ) := by
        rw [List.ofFn_succ, List.ofFn_succ]
        simp only [Function.comp_apply, Equiv.swap_apply_left,
          Fin.succ_zero_eq_one, Equiv.swap_apply_right]
        congr 2
      simpa only [Fin.castSucc_zero, Fin.succ_zero_eq_one, hlist,
        List.ofFn_succ] using
        pfaffianList_swap_adjacent A hskew (f 1) (f 0) pre
          (List.ofFn (fun j : Fin n => f j.succ.succ))
    · have hfun : (fun j : Fin (n + 1) =>
            f (Equiv.swap i.succ.castSucc i.succ.succ j.succ)) =
          (fun j => f j.succ) ∘ Equiv.swap i.castSucc i.succ := by
        funext j
        congr 1
        simpa only [Fin.castSucc_succ, Function.comp_apply] using
          (Function.Injective.map_swap (Fin.succ_injective _) i.castSucc i.succ j).symm
      have hzero : Equiv.swap i.succ.castSucc i.succ.succ (0 : Fin (n + 2)) = 0 := by
        apply Equiv.swap_apply_of_ne_of_ne <;> (intro h; have := congrArg Fin.val h; simp at this)
      simpa only [List.ofFn_succ, Function.comp_apply, hzero, hfun,
        List.append_assoc, List.cons_append, List.nil_append] using
        ih i (fun j => f j.succ) (pre ++ [f 0])

/-- Any coordinate permutation multiplies the ordered Pfaffian by its sign.
The coordinate function need not be injective, and the matrix order need not be even. -/
theorem pfaffianList_ofFn_comp_perm (A : Matrix ι ι R)
    (hskew : ∀ x y, A x y = -A y x) {n : ℕ}
    (σ : Equiv.Perm (Fin n)) (f : Fin n → ι) :
    pfaffianList A (List.ofFn (f ∘ σ)) =
      (Equiv.Perm.sign σ : ℤ) * pfaffianList A (List.ofFn f) := by
  cases n with
  | zero =>
    have : σ = 1 := Subsingleton.elim _ _
    simp [this]
  | succ n =>
    have hmem : σ ∈ Submonoid.closure
        (Set.range fun i : Fin n => Equiv.swap i.castSucc i.succ) := by
      rw [Equiv.Perm.mclosure_swap_castSucc_succ]
      trivial
    induction hmem using Submonoid.closure_induction generalizing f with
    | mem σ hσ =>
      obtain ⟨i, rfl⟩ := hσ
      have hne : i.castSucc ≠ i.succ := by
        intro h
        have := congrArg Fin.val h
        simp only [Fin.val_castSucc, Fin.val_succ] at this
        omega
      simpa [Equiv.Perm.sign_swap hne] using
        pfaffianList_ofFn_swap_adjacent A hskew i f []
    | one => simp
    | mul σ τ hσ hτ ihσ ihτ =>
      calc
        _ = pfaffianList A (List.ofFn ((f ∘ σ) ∘ τ)) := rfl
        _ = (Equiv.Perm.sign τ : ℤ) *
            pfaffianList A (List.ofFn (f ∘ σ)) := ihτ _
        _ = (Equiv.Perm.sign τ : ℤ) *
            ((Equiv.Perm.sign σ : ℤ) * pfaffianList A (List.ofFn f)) := by rw [ihσ]
        _ = _ := by simp only [Equiv.Perm.sign_mul, Units.val_mul, Int.cast_mul]; ring

/-- Simultaneous reindexing of rows and columns obeys the full sign law. -/
theorem pfaffianList_reindex_perm {n : ℕ} (A : Matrix (Fin n) (Fin n) R)
    (hskew : ∀ x y, A x y = -A y x) (σ : Equiv.Perm (Fin n)) :
    pfaffianList (A.submatrix σ σ) (List.ofFn id) =
      (Equiv.Perm.sign σ : ℤ) * pfaffianList A (List.ofFn id) := by
  change pfaffianList (fun x y => A (σ x) (σ y)) _ = _
  rw [← pfaffianList_map, List.map_ofFn]
  simpa only [Function.comp_id, Function.id_comp] using
    pfaffianList_ofFn_comp_perm A hskew σ id

/-- The permutation matrix with a `1` in row `i`, column `σ i`. -/
def coordinatePermutationMatrix {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    Matrix (Fin n) (Fin n) R := (1 : Matrix (Fin n) (Fin n) R).submatrix σ id

/-- The determinant of the coordinate permutation matrix is its permutation sign. -/
theorem det_coordinatePermutationMatrix {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    (coordinatePermutationMatrix (R := R) σ).det = (Equiv.Perm.sign σ : ℤ) := by
  simp [coordinatePermutationMatrix, Matrix.det_permute]

/-- A coordinate permutation matrix conjugates by pulling back both indices. -/
theorem coordinatePermutationMatrix_mul_transpose {n : ℕ}
    (A : Matrix (Fin n) (Fin n) R) (σ : Equiv.Perm (Fin n)) :
    coordinatePermutationMatrix σ * A * (coordinatePermutationMatrix σ).transpose =
      A.submatrix σ σ := by
  simp only [coordinatePermutationMatrix, Matrix.transpose_submatrix, Matrix.transpose_one]
  have hl := Matrix.one_submatrix_mul (α := R) σ (Equiv.refl (Fin n)) A
  simp only [Equiv.coe_refl, Equiv.refl_symm, Function.id_comp] at hl
  rw [hl]
  have hr := Matrix.mul_submatrix_one (α := R) (Equiv.refl (Fin n)) σ
    (A.submatrix σ id)
  simpa only [Equiv.coe_refl, Equiv.refl_symm, Function.id_comp,
    Function.comp_id, Matrix.submatrix_submatrix] using hr

/-- The paper's full permutation-matrix Pfaffian identity, with the ordinary
matrix determinant as its sign factor. -/
theorem pfaffianList_permMatrix_conjugate {n : ℕ}
    (A : Matrix (Fin n) (Fin n) R) (hskew : ∀ x y, A x y = -A y x)
    (σ : Equiv.Perm (Fin n)) :
    pfaffianList (coordinatePermutationMatrix σ * A *
      (coordinatePermutationMatrix σ).transpose) (List.ofFn id) =
      (coordinatePermutationMatrix (R := R) σ).det * pfaffianList A (List.ofFn id) := by
  rw [coordinatePermutationMatrix_mul_transpose, det_coordinatePermutationMatrix]
  exact pfaffianList_reindex_perm A hskew σ

/-- The number of inverted pairs in the one-line notation for a permutation. -/
def permutationInversions {n : ℕ} (σ : Equiv.Perm (Fin n)) : ℕ :=
  ∑ i : Fin n, ((Finset.Ioi i).filter (fun j => σ j < σ i)).card

/-- The ordinary permutation sign is the parity of the inversion count. -/
theorem permutationSign_eq_negOne_pow {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    Equiv.Perm.sign σ = (-1 : ℤˣ) ^ permutationInversions σ := by
  rw [Equiv.Perm.sign_eq_prod_prod_Ioi]
  unfold permutationInversions
  rw [← Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_congr rfl
  intro i _
  have hfilter : (Finset.Ioi i).filter (fun j => ¬σ i < σ j) =
      (Finset.Ioi i).filter (fun j => σ j < σ i) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_Ioi]
    constructor
    · rintro ⟨hij, h⟩
      exact ⟨hij, (le_of_not_gt h).lt_of_ne (fun he => hij.ne (σ.injective he.symm))⟩
    · rintro ⟨hij, h⟩
      exact ⟨hij, not_lt_of_gt h⟩
  simp only [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const,
    hfilter]

/-- The inversion-sign formula after casting into any commutative ring. -/
theorem permutationSign_cast_eq_negOne_pow {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    ((Equiv.Perm.sign σ : ℤ) : R) = (-1 : R) ^ permutationInversions σ := by
  rw [permutationSign_eq_negOne_pow]
  simp

private theorem pfaffianList_move_across (A : Matrix ι ι R)
    (hskew : ∀ x y, A x y = -A y x) (a : ι) (xs pre suf : List ι) :
    pfaffianList A (pre ++ a :: (xs ++ suf)) =
      (-1 : R) ^ xs.length * pfaffianList A (pre ++ xs ++ a :: suf) := by
  induction xs generalizing pre with
  | nil => simp
  | cons b xs ih =>
    simp only [List.cons_append, List.length_cons]
    rw [pfaffianList_swap_adjacent A hskew a b pre (xs ++ suf)]
    have h := ih (pre ++ [b])
    simp only [List.append_assoc, List.cons_append, List.nil_append] at h
    rw [h, pow_succ]
    simp only [List.append_assoc, List.cons_append]
    ring

/-- Swapping consecutive coordinate chunks of lengths `p` and `q` contributes
exactly the sign `(-1)^(p*q)`, including arbitrary fixed surrounding coordinates. -/
theorem pfaffianList_swap_chunks (A : Matrix ι ι R)
    (hskew : ∀ x y, A x y = -A y x) (xs ys pre suf : List ι) :
    pfaffianList A (pre ++ xs ++ ys ++ suf) =
      (-1 : R) ^ (xs.length * ys.length) *
        pfaffianList A (pre ++ ys ++ xs ++ suf) := by
  induction xs generalizing pre with
  | nil => simp
  | cons a xs ih =>
    have h := ih (pre ++ [a])
    simp only [List.append_assoc, List.cons_append, List.nil_append] at h ⊢
    rw [h, pfaffianList_move_across A hskew a ys pre (xs ++ suf)]
    simp only [List.length_cons, Nat.add_mul, one_mul, pow_add,
      List.append_assoc]
    ring

/-- Interchanging two even coordinate chunks introduces no sign. -/
theorem pfaffianList_swap_even_chunks (A : Matrix ι ι R)
    (hskew : ∀ x y, A x y = -A y x) (xs ys pre suf : List ι)
    (hxs : Even xs.length) (_hys : Even ys.length) :
    pfaffianList A (pre ++ xs ++ ys ++ suf) =
      pfaffianList A (pre ++ ys ++ xs ++ suf) := by
  rw [pfaffianList_swap_chunks A hskew]
  rw [(hxs.mul_right ys.length).neg_one_pow, one_mul]

/-- Arbitrarily permuting even-sized coordinate chunks preserves the Pfaffian.
No block-diagonal assumption is made: all cross-couplings are allowed. -/
theorem pfaffianList_even_chunks_perm (A : Matrix ι ι R)
    (hskew : ∀ x y, A x y = -A y x)
    {xs ys : List (List ι)} (hperm : xs.Perm ys)
    (heven : ∀ x ∈ xs, Even x.length) (pre suf : List ι) :
    pfaffianList A (pre ++ xs.flatten ++ suf) =
      pfaffianList A (pre ++ ys.flatten ++ suf) := by
  induction hperm generalizing pre with
  | nil => rfl
  | @cons x xs ys hperm ih =>
    simpa only [List.flatten_cons, List.append_assoc] using
      ih (fun y hy => heven y (by simp [hy])) (pre ++ x)
  | swap x y xs =>
    simpa only [List.flatten_cons, List.append_assoc] using
      pfaffianList_swap_even_chunks A hskew y x pre (xs.flatten ++ suf)
        (heven y (by simp)) (heven x (by simp))
  | @trans xs ys zs h₁ h₂ ih₁ ih₂ =>
    exact (ih₁ heven pre).trans
      (ih₂ (fun y hy => heven y (h₁.mem_iff.mpr hy)) pre)

end MatchgateWidth
