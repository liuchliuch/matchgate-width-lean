import MatchgateWidth.PolygonalRibbonPaths
import MatchgateWidth.PolygonalTransverseSections
import MatchgateWidth.SeparatedSegmentCarriers

/-! # Parallel simple wires along any finite simple polygon

Original segment simplicity is the only nonintersection input. Transverse
sections, nonadjacent open carriers, a uniform positive width, all lane paths,
and their global pairwise disjointness are derived. Prescribed open obstacle-
avoiding sets continue to contain every shifted wire segment.
-/
namespace MatchgateWidth
noncomputable section

/-- Every finite simple polygon has positive transverse route data inside
arbitrary preassigned open neighborhoods of its original segments. -/
theorem simplePolygon_exists_transverseRoute {n : ℕ} (p : Fin (n+1) → ℂ)
    (hne : ∀ i : Fin n, p i.castSucc ≠ p i.succ)
    (hadj : ∀ i j : Fin n, i.val + 1 = j.val →
      segment ℝ (p i.castSucc) (p i.succ) ∩ segment ℝ (p j.castSucc) (p j.succ) ⊆ {p i.succ})
    (hdis : ∀ i j : Fin n, i.val + 1 < j.val →
      Disjoint (segment ℝ (p i.castSucc) (p i.succ)) (segment ℝ (p j.castSucc) (p j.succ)))
    (O : Fin n → Set ℂ) (hO : ∀ i, IsOpen (O i))
    (hcenter : ∀ i, Set.range (straightArc (p i.castSucc) (p i.succ)) ⊆ O i) :
    ∃ R : TransversePolygonalRoute n, R.vertex = p ∧ ∀ i, R.carrier i ⊆ O i := by
  obtain ⟨w,hstart,hend⟩ := exists_positive_polygonal_sections p hne hadj
  obtain ⟨R,hp,hw,hRO⟩ := exists_transversePolygonalRoute p w O hO hcenter
    (fun i j hij => by
      rw [range_straightArc, range_straightArc]
      rcases hij with hij | hji
      · exact hdis i j hij
      · exact (hdis j i hji).symm) hstart hend
  exact ⟨R,hp,hRO⟩

/-- **Actual finite parallel-wire existence.** A simple polygonal route admits
any finite number of pairwise-disjoint continuous simple polygonal wire paths.
All endpoints are explicit ordered shifts of the original endpoint sections;
all segments remain in the prescribed open carriers. No routing, simplicity,
or disjointness conclusion is assumed of the output wires. -/
theorem simplePolygon_exists_parallel_paths {n : ℕ} (hn : 0 < n)
    (p : Fin (n+1) → ℂ)
    (hne : ∀ i : Fin n, p i.castSucc ≠ p i.succ)
    (hadj : ∀ i j : Fin n, i.val + 1 = j.val →
      segment ℝ (p i.castSucc) (p i.succ) ∩ segment ℝ (p j.castSucc) (p j.succ) ⊆ {p i.succ})
    (hdis : ∀ i j : Fin n, i.val + 1 < j.val →
      Disjoint (segment ℝ (p i.castSucc) (p i.succ)) (segment ℝ (p j.castSucc) (p j.succ)))
    (O : Fin n → Set ℂ) (hO : ∀ i, IsOpen (O i))
    (hcenter : ∀ i, Set.range (straightArc (p i.castSucc) (p i.succ)) ⊆ O i)
    (k : ℕ) :
    ∃ (R : TransversePolygonalRoute n) (_ : R.vertex = p),
      (∀ i, R.carrier i ⊆ O i) ∧
      ∃ (ε : ℝ) (_ : 0 < ε), R.Width ε ∧
      ∃ q : (i : Fin k) → Path
        (R.laneVertex (TransversePolygonalRoute.laneOffset ε k i) 0)
        (R.laneVertex (TransversePolygonalRoute.laneOffset ε k i) (Fin.last n)),
      (∀ i, Function.Injective (q i) ∧ IsPolygonalPath (q i) ∧
        Set.range (q i) = R.laneSupport (TransversePolygonalRoute.laneOffset ε k i)) ∧
      Pairwise (fun i j => Disjoint (Set.range (q i)) (Set.range (q j))) := by
  obtain ⟨R,hp,hRO⟩ := simplePolygon_exists_transverseRoute p hne hadj hdis O hO hcenter
  exact ⟨R,hp,hRO,R.exists_parallel_paths hn k⟩

end
end MatchgateWidth
