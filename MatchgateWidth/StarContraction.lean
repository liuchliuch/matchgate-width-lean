import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
# Exact star contraction under a common base

This is the coordinate algebra in equation (star-extraction), Section 9 of
arXiv:2610.00079v1. It is valid over arbitrary finite domains and without
rank hypotheses on the base. Matchgate closure and equivalence of planar
labelled languages are separate, not assumed as conclusions here.
-/

namespace MatchgateWidth

noncomputable section

variable {K P D B : Type*} [CommSemiring K]
variable [Fintype P] [Fintype D] [Fintype B]

/-- The multilinear non-Hermitian contraction from Section 4.6. -/
def starContract (Q : (P → B) → K) (g : P → B → K) : K :=
  by classical exact ∑ x : P → B, Q x * ∏ i, g i (x i)

/-- Right-hand tensor transformation by the same base at every ordered port. -/
def rightTransform (M : D → B → K) (Q : (P → B) → K) (x : P → D) : K :=
  by classical exact ∑ y : P → B, Q y * ∏ i, M (x i) (y i)

/-- Transformation of a unary left label. -/
def unaryTransform (M : D → B → K) (g : D → K) (y : B) : K :=
  ∑ d, g d * M d y

/-- Exact evaluation of a closed labelled star survives insertion of a common base.
No inverse, rank assumption, or equality of the original and competing domains
is required. This is an algebraic identity, not a matchgate-realization axiom. -/
theorem starContract_rightTransform (M : D → B → K) (Q : (P → B) → K)
    (g : P → D → K) :
    starContract (rightTransform M Q) g =
      starContract Q (fun i => unaryTransform M (g i)) := by
  classical
  unfold starContract rightTransform unaryTransform
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  rw [Fintype.prod_sum]
  simp_rw [Finset.mul_sum, Finset.prod_mul_distrib]
  apply Finset.sum_congr rfl
  intro x _
  ring

/-- The coordinate pin at a domain value. -/
def coordinatePin [DecidableEq B] (b : B) (x : B) : K := if x = b then 1 else 0

/-- Labelled unary pins recover an exact coordinate, with no scalar ambiguity. -/
theorem starContract_coordinatePins (Q : (P → B) → K) (x : P → B) :
    starContract Q (fun i => @coordinatePin K B _ (Classical.decEq B) (x i)) = Q x := by
  classical
  unfold starContract
  rw [Finset.sum_eq_single x]
  · simp [coordinatePin]
  · intro y _ hne
    have hi : ∃ i, y i ≠ x i := by
      by_contra h
      apply hne
      funext i
      exact not_ne_iff.mp (not_exists.mp h i)
    obtain ⟨i, hi⟩ := hi
    have hz : (∏ j, coordinatePin (x j) (y j) : K) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (by simp [coordinatePin, hi])
    rw [hz, mul_zero]
  · simp

/-- Empty Boolean blocks have one word; contraction then has the scalar formula. -/
theorem starContract_singleton_alphabet [Unique B]
    (Q : (P → B) → K) (g : P → B → K) :
    starContract Q g = Q (fun _ => default) * ∏ i, g i default := by
  classical
  simp [starContract]

end
end MatchgateWidth
