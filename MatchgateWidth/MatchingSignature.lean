import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic

/-!
# Finite weighted deletion signatures

Graph semantics for Section 4.3 of arXiv:2610.00079v1. Edge identities are
retained, so parallel edges are allowed. Planar embedding and outer-face
order are separate structures still to be developed. Nothing in this file
identifies arbitrary graph signatures with planar matchgates.
-/

namespace MatchgateWidth

noncomputable section

variable {V E K : Type*} [Fintype V] [Fintype E] [CommSemiring K]

/-- A finite weighted loopless graph with explicit edge identities. -/
structure WeightedGraph (V E K : Type*) where
  left : E → V
  right : E → V
  loopless : ∀ e, left e ≠ right e
  weight : E → K

/-- Incidences of a selected edge family at a vertex. -/
def matchingDegree (G : WeightedGraph V E K) (m : Finset E) (v : V) : ℕ := by
  classical
  exact ∑ e ∈ m, ((if G.left e = v then 1 else 0) +
    (if G.right e = v then 1 else 0))

/-- The selected edges match exactly the active vertices. This directly encodes
perfect matching after deletion of the complementary vertex set. -/
def MatchesExactly (G : WeightedGraph V E K) (active : Finset V) (m : Finset E) : Prop :=
  by classical exact ∀ v, matchingDegree G m v = if v ∈ active then 1 else 0

/-- Every selected edge contributes two incidences. -/
theorem sum_matchingDegree (G : WeightedGraph V E K) (m : Finset E) :
    ∑ v, matchingDegree G m v = 2 * m.card := by
  classical
  unfold matchingDegree
  rw [Finset.sum_comm]
  simp [Finset.sum_add_distrib, mul_comm]

/-- Every perfect matching covers an even number of active vertices. -/
theorem matchesExactly_even_card (G : WeightedGraph V E K)
    (active : Finset V) (m : Finset E) (h : MatchesExactly G active m) :
    Even active.card := by
  classical
  have hs := sum_matchingDegree G m
  unfold MatchesExactly at h
  simp_rw [h] at hs
  have hc : active.card = 2 * m.card := by simpa using hs
  exact ⟨m.card, by omega⟩

/-- The weighted perfect matching sum; an empty sum is zero and an empty product one. -/
def weightedPerfectMatch (G : WeightedGraph V E K) (active : Finset V) : K := by
  classical
  exact ∑ m : Finset E, if MatchesExactly G active m then ∏ e ∈ m, G.weight e else 0

/-- With an odd number of vertices every matching summand vanishes. -/
theorem weightedPerfectMatch_odd (G : WeightedGraph V E K) (active : Finset V)
    (hodd : active.card % 2 = 1) : weightedPerfectMatch G active = 0 := by
  classical
  unfold weightedPerfectMatch
  apply Finset.sum_eq_zero
  intro m _
  split_ifs with hm
  · rcases matchesExactly_even_card G active m hm with ⟨a, ha⟩
    omega
  · rfl

/-- The empty active vertex set has exactly the empty matching. -/
theorem matchesExactly_empty_iff (G : WeightedGraph V E K) (m : Finset E) :
    MatchesExactly G ∅ m ↔ m = ∅ := by
  classical
  constructor
  · intro h
    have hs := sum_matchingDegree G m
    unfold MatchesExactly at h
    simp_rw [h] at hs
    simp at hs
    exact hs
  · rintro rfl
    intro v
    simp [matchingDegree]

/-- The empty graph contributes the empty product, equal to one. -/
theorem weightedPerfectMatch_empty (G : WeightedGraph V E K) :
    weightedPerfectMatch G ∅ = 1 := by
  classical
  unfold weightedPerfectMatch
  simp [matchesExactly_empty_iff]

/-- Active vertices under the fixed deletion-bit convention. -/
def deletionActive {s : ℕ} (ext : Fin s → V) (x : Fin s → Bool) : Finset V := by
  classical
  exact Finset.univ.filter (fun v => ¬ ∃ i, x i = true ∧ ext i = v)

/-- The graph's Boolean signature is the weighted matching sum after deletion. -/
def deletionSignature {s : ℕ} (G : WeightedGraph V E K) (ext : Fin s → V)
    (x : Fin s → Bool) : K := weightedPerfectMatch G (deletionActive ext x)

/-- Reversing both the external enumeration and the argument cancels exactly.
This is the graph-coordinate part of Lemma 4.1; the planar reflection bridge
is not asserted in this module. -/
theorem deletionActive_reverse {s : ℕ} (ext : Fin s → V) (x : Fin s → Bool) :
    deletionActive (fun i => ext i.rev) x = deletionActive ext (fun i => x i.rev) := by
  classical
  ext v
  simp only [deletionActive, Finset.mem_filter, Finset.mem_univ, true_and]
  apply not_congr
  constructor
  · rintro ⟨i, hi, he⟩
    exact ⟨i.rev, by simpa using hi, he⟩
  · rintro ⟨i, hi, he⟩
    exact ⟨i.rev, hi, by simpa using he⟩

theorem deletionSignature_reverse {s : ℕ} (G : WeightedGraph V E K)
    (ext : Fin s → V) (x : Fin s → Bool) :
    deletionSignature G (fun i => ext i.rev) x =
      deletionSignature G ext (fun i => x i.rev) := by
  unfold deletionSignature
  rw [deletionActive_reverse]

end
end MatchgateWidth
