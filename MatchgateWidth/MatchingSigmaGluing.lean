import MatchgateWidth.MatchingGluing
import Mathlib.Data.Finset.Sigma
import Mathlib.Algebra.BigOperators.Group.Finset.Pi

/-! # Actual matching sums of finite dependent disjoint graph families -/
namespace MatchgateWidth
noncomputable section
open scoped Classical
set_option maxHeartbeats 600000

variable {I : Type*} {V E : I → Type*} {K : Type*}
variable [Fintype I] [∀ i, Fintype (V i)] [∀ i, Fintype (E i)] [CommSemiring K]

/-- Every local graph retains its own disjoint vertex and edge identities. -/
def sigmaGraph (G : ∀ i, WeightedGraph (V i) (E i) K) : WeightedGraph (Sigma V) (Sigma E) K where
  left e := ⟨e.1,(G e.1).left e.2⟩
  right e := ⟨e.1,(G e.1).right e.2⟩
  loopless := by rintro ⟨i,e⟩ he; exact (G i).loopless e (eq_of_heq (Sigma.mk.inj he).2)
  weight e := (G e.1).weight e.2

/-- A global selected edge subset is exactly one selected subset per component. -/
def sigmaFinsetEquiv : Finset (Sigma E) ≃ ((i : I) → Finset (E i)) where
  toFun s i := Finset.univ.filter (fun e => (⟨i,e⟩ : Sigma E) ∈ s)
  invFun m := Finset.univ.sigma m
  left_inv s := by ext ⟨i,e⟩; simp
  right_inv m := by funext i; ext e; simp

/-- Degrees are computed componentwise in the literal disjoint family. -/
theorem matchingDegree_sigmaGraph (G : ∀ i, WeightedGraph (V i) (E i) K)
    (m : (i : I) → Finset (E i)) (i : I) (v : V i) :
    matchingDegree (sigmaGraph G) (Finset.univ.sigma m) ⟨i,v⟩ = matchingDegree (G i) (m i) v := by
  classical
  unfold matchingDegree
  rw [Finset.sum_sigma]
  rw [Finset.sum_eq_single i]
  · simp [sigmaGraph]
  · intro j hj hji
    apply Finset.sum_eq_zero
    intro e he
    have hl : (⟨j,(G j).left e⟩ : Sigma V) ≠ ⟨i,v⟩ := fun h => hji (congrArg Sigma.fst h)
    have hr : (⟨j,(G j).right e⟩ : Sigma V) ≠ ⟨i,v⟩ := fun h => hji (congrArg Sigma.fst h)
    simp [sigmaGraph,hl,hr]
  · simp

/-- Matching exactly the active global vertices is equivalent to matching
exactly the active vertices of each component. -/
theorem matchesExactly_sigmaGraph (G : ∀ i, WeightedGraph (V i) (E i) K)
    (active : (i : I) → Finset (V i)) (m : (i : I) → Finset (E i)) :
    MatchesExactly (sigmaGraph G) (Finset.univ.sigma active) (Finset.univ.sigma m) ↔
      ∀ i, MatchesExactly (G i) (active i) (m i) := by
  simp only [MatchesExactly, Sigma.forall, matchingDegree_sigmaGraph, Finset.mem_sigma,
    Finset.mem_univ, true_and]

/-- The product of selected weights has the same component factorization. -/
theorem matchingWeight_sigmaGraph (G : ∀ i, WeightedGraph (V i) (E i) K)
    (m : (i : I) → Finset (E i)) :
    (∏ e ∈ Finset.univ.sigma m, (sigmaGraph G).weight e) =
      ∏ i, ∏ e ∈ m i, (G i).weight e := by
  simp only [Finset.prod_sigma, sigmaGraph]

/-- Full dependent disjoint-union matching-sum factorization, including empty
families, zero-vertex components, and arbitrary active vertex deletions. -/
theorem weightedPerfectMatch_sigmaGraph (G : ∀ i, WeightedGraph (V i) (E i) K)
    (active : (i : I) → Finset (V i)) :
    weightedPerfectMatch (sigmaGraph G) (Finset.univ.sigma active) =
      ∏ i, weightedPerfectMatch (G i) (active i) := by
  classical
  unfold weightedPerfectMatch
  rw [← (sigmaFinsetEquiv (E := E)).symm.sum_comp]
  simp only [sigmaFinsetEquiv, Equiv.coe_fn_symm_mk,
    matchesExactly_sigmaGraph, matchingWeight_sigmaGraph]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro m hm
  by_cases h : ∀ i, MatchesExactly (G i) (active i) (m i)
  · simp [h]
  · rw [ite_eq_right h]
    symm
    push Not at h
    obtain ⟨i,hi⟩ := h
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [hi]

end
end MatchgateWidth
