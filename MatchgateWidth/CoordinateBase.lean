import MatchgateWidth.StarContraction
import MatchgateWidth.TransformedSupport

/-!
# Coordinate-code bases

Exact full-row-rank and restriction properties of the qutrit coordinate base
in Section 8. These results hold for any injective finite code. They do not
assert that the transformed tensors have a planar matchgate realization.
-/

namespace MatchgateWidth

noncomputable section
open scoped Classical

variable {K D B P : Type*} [Field K]
variable [Fintype D] [Fintype B] [Fintype P]

/-- A code assigns a distinct coordinate basis row to each domain state. -/
def coordinateBase (code : D → B) : Matrix D B K := by
  classical
  exact fun d b => if b = code d then 1 else 0

/-- The transpose is an exact right decoder when codewords are distinct. -/
theorem coordinateBase_mul_transpose (code : D → B) (hcode : Function.Injective code) :
    coordinateBase (K := K) code * (coordinateBase (K := K) code).transpose = 1 := by
  classical
  ext d e
  simp [Matrix.mul_apply, Matrix.transpose_apply, coordinateBase, hcode.eq_iff, Matrix.one_apply, eq_comm]

/-- Distinct codewords make the base have full row rank. -/
theorem coordinateBase_rank (code : D → B) (hcode : Function.Injective code) :
    (coordinateBase (K := K) code).rank = Fintype.card D := by
  classical
  have hl := Matrix.rank_mul_le_left (coordinateBase (K := K) code)
    (coordinateBase (K := K) code).transpose
  rw [coordinateBase_mul_transpose code hcode, Matrix.rank_one] at hl
  exact le_antisymm (coordinateBase code).rank_le_card_height hl

/-- Right transformation by a coordinate base is literal codeword restriction. -/
theorem rightTransform_coordinateBase (code : D → B) (Q : (P → B) → K) (x : P → D) :
    rightTransform (coordinateBase code) Q x = Q (fun i => code (x i)) := by
  classical
  exact starContract_coordinatePins Q (fun i => code (x i))

/-- A domain unary coordinate pin transforms to the corresponding Boolean code pin. -/
theorem unaryTransform_coordinateBase_pin (code : D → B) (d : D) :
    unaryTransform (coordinateBase (K := K) code)
      (@coordinatePin K D _ (Classical.decEq D) d) =
      @coordinatePin K B _ (Classical.decEq B) (code d) := by
  classical
  funext b
  unfold unaryTransform
  simp only [coordinatePin, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]
  rfl

/-- A tensor coordinate pin transforms to its exact tuple of codewords. -/
theorem leftTransform_coordinateBase_pin (code : D → B) (x : P → D) :
    leftTransform (coordinateBase (K := K) code)
      (@coordinatePin K (P → D) _ (Classical.decEq _) x) =
      @coordinatePin K (P → B) _ (Classical.decEq _) (fun i => code (x i)) := by
  classical
  funext y
  simp only [leftTransform, coordinatePin, coordinateBase]
  simp only [ite_mul, zero_mul, one_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  by_cases h : y = fun i => code (x i)
  · subst y
    simp
  · rw [ite_eq_right h]
    obtain ⟨i, hi⟩ : ∃ i, y i ≠ code (x i) := by
      by_contra hn
      apply h
      funext i
      exact not_ne_iff.mp (not_exists.mp hn i)
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

end
end MatchgateWidth
