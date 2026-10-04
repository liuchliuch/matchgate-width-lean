import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.Ring

/-!
# Ordered Pfaffian expansion

The recursive expansion is along the first row in the supplied order.
It implements the convention in Section 4.3 and the four-mode control
calculation in Proposition 8.1 of arXiv:2610.00079v1. The connection with
planar matchgate realization is not assumed here; it is constructed in the
subsequent circuit and disk realization modules.
-/

namespace MatchgateWidth

variable {R ι : Type*} [CommRing R]

/-- Pfaffian of an ordered principal submatrix, expanded at its first index. -/
def pfaffianList (A : Matrix ι ι R) : List ι → R
  | [] => 1
  | a :: xs => ∑ j : Fin xs.length,
      (-1 : R) ^ j.val * A a xs[j] * pfaffianList A (xs.eraseIdx j.val)
termination_by xs => xs.length
decreasing_by
  exact Nat.lt_succ_of_le (List.length_eraseIdx_le ..)

@[simp] theorem pfaffianList_nil (A : Matrix ι ι R) : pfaffianList A [] = 1 :=
  pfaffianList.eq_1 A

@[simp] theorem pfaffianList_singleton (A : Matrix ι ι R) (a : ι) :
    pfaffianList A [a] = 0 := by
  rw [pfaffianList]
  simp

@[simp] theorem pfaffianList_pair (A : Matrix ι ι R) (a b : ι) :
    pfaffianList A [a,b] = A a b := by
  rw [pfaffianList]
  simp

/-- The standard four-mode formula with the fixed external order. -/
theorem pfaffianList_four (A : Matrix ι ι R) (a b c d : ι) :
    pfaffianList A [a,b,c,d] =
      A a b * A c d - A a c * A b d + A a d * A b c := by
  rw [pfaffianList]
  simp [Fin.sum_univ_succ, List.eraseIdx]
  ring

/-- Four-mode control calculation in Proposition 8.1, without a realization claim. -/
theorem control_pfaffian (A : Matrix ι ι R) (p q a b : ι) (α β : R)
    (hab : A a b = 1) (hpq : A p q = α) (hpa : A p a = 1)
    (hqb : A q b = α - β) (hpb : A p b = 0) :
    pfaffianList A [p,q,a,b] = β := by
  rw [pfaffianList_four, hab, hpq, hpa, hqb, hpb]
  ring

/-- Odd-order principal Pfaffians vanish, including singleton indices. -/
theorem pfaffianList_odd (A : Matrix ι ι R) (xs : List ι)
    (hodd : xs.length % 2 = 1) : pfaffianList A xs = 0 := by
  induction xs using (measure List.length).wf.induction with
  | _ xs ih =>
    cases xs with
    | nil => simp at hodd
    | cons a ys =>
      rw [pfaffianList]
      apply Finset.sum_eq_zero
      intro j _
      have hj : j.val < ys.length := j.isLt
      have hlen : (ys.eraseIdx j.val).length = ys.length - 1 := by
        simp [List.length_eraseIdx, hj]
      have hlt : (ys.eraseIdx j.val).length < (a :: ys).length := by
        simp only [List.length_cons]
        omega
      have hmod : (ys.eraseIdx j.val).length % 2 = 1 := by
        simp only [List.length_cons] at hodd
        omega
      rw [ih (ys.eraseIdx j.val) hlt hmod]
      simp

/-- An isolated first mode makes every nonempty coordinate vanish. -/
theorem pfaffianList_isolated_first (A : Matrix ι ι R) (a : ι) (xs : List ι)
    (h : ∀ j : Fin xs.length, A a xs[j] = 0) :
    pfaffianList A (a :: xs) = 0 := by
  rw [pfaffianList]
  apply Finset.sum_eq_zero
  intro j _
  rw [h j]
  simp

end MatchgateWidth
