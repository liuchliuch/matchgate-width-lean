import MatchgateWidth.PolygonalRibbonAssembly
import MatchgateWidth.IndexedPolygonalRouting

/-! # Continuous simple paths for finite parallel ribbon lanes

The previously proved segment and corner geometry is concatenated into actual
injective continuous paths. Their full images are exactly the constructed
polygonal lane supports, so different wire paths are disjoint globally.
-/
namespace MatchgateWidth
noncomputable section

/-- The repository's elementary straight arc is the standard bundled segment
with exactly the same linear parameter, and has the full closed segment image. -/
theorem range_straightArc (p q : ℂ) : Set.range (straightArc p q) = segment ℝ p q := by
  have h : straightArc p q = (Path.segment p q : unitInterval → ℂ) := by
    funext t
    simp [straightArc, Path.segment_apply, AffineMap.lineMap_apply_module]
  rw [h, Path.range_segment]

namespace TransversePolygonalRoute
variable {n : ℕ} (R : TransversePolygonalRoute n)

/-- The original polygon vertices displaced along their actual sections. -/
def laneVertex (δ : ℝ) (i : Fin (n+1)) : ℂ :=
  ribbonSection (R.vertex i) (R.transverse i) δ

@[simp] theorem edge_zero (δ : ℝ) (i : Fin n) : R.edge δ i 0 = R.laneVertex δ i.castSucc :=
  ribbonArc_zero _ _ _ _ _

@[simp] theorem edge_one (δ : ℝ) (i : Fin n) : R.edge δ i 1 = R.laneVertex δ i.succ :=
  ribbonArc_one _ _ _ _ _

theorem edge_range (δ : ℝ) (i : Fin n) : Set.range (R.edge δ i) =
    segment ℝ (R.laneVertex δ i.castSucc) (R.laneVertex δ i.succ) :=
  range_straightArc _ _

/-- Every permitted lane has nonzero polygonal edges. -/
theorem lane_edge_ne {ε δ : ℝ} (hε : R.Width ε) (hδ : |δ| < ε) (i : Fin n) :
    R.laneVertex δ i.castSucc ≠ R.laneVertex δ i.succ := by
  intro h
  have he : R.edge δ i 0 = R.edge δ i 1 := by simpa only [R.edge_zero, R.edge_one] using h
  have hz : (0 : unitInterval) = 1 := R.edge_injective hε hδ i he
  exact zero_ne_one hz

/-- Consecutive edges of one wire intersect only at their actual shared
shifted polygon vertex. -/
theorem lane_adjacent_inter {ε δ : ℝ} (hε : R.Width ε) (hδ : |δ| < ε)
    (i j : Fin n) (hij : i.val+1=j.val) :
    segment ℝ (R.laneVertex δ i.castSucc) (R.laneVertex δ i.succ) ∩
      segment ℝ (R.laneVertex δ j.castSucc) (R.laneVertex δ j.succ) ⊆
        {R.laneVertex δ i.succ} := by
  intro z hz
  rw [← R.edge_range δ i, ← R.edge_range δ j] at hz
  obtain ⟨s,hs⟩ := hz.1
  obtain ⟨t,ht⟩ := hz.2
  have hst := (R.adjacent_eq_iff hε hδ hδ i j hij s t).mp (hs.trans ht.symm)
  have hzv : z = R.laneVertex δ i.succ := by rw [← hs, hst.1, R.edge_one]
  exact hzv

/-- Actual injective continuous path for one lane, with exact endpoints and
exact geometric image, obtained by finite segment concatenation. -/
theorem exists_lane_path (hn : 0 < n) {ε δ : ℝ} (hε : R.Width ε) (hδ : |δ| < ε) :
    ∃ p : Path (R.laneVertex δ 0) (R.laneVertex δ (Fin.last n)),
      Function.Injective p ∧ IsPolygonalPath p ∧ Set.range p = R.laneSupport δ := by
  obtain ⟨p,hp,hpoly,hrange⟩ := exists_injective_polygonal_path_of_indexed hn
    (R.laneVertex δ) (R.lane_edge_ne hε hδ) (R.lane_adjacent_inter hε hδ)
    (fun i j hij => by
      rw [← R.edge_range, ← R.edge_range]
      exact R.nonadjacent_disjoint hε hδ hδ i j (Or.inl hij))
  refine ⟨p,hp,hpoly,?_⟩
  rw [hrange]
  simp only [laneSupport, R.edge_range]

/-- Any finite number of wires can be routed as actual pairwise-disjoint
simple polygonal paths through the entire route, with explicitly increasing
signed positions at both endpoint sections. -/
theorem exists_parallel_paths (hn : 0 < n) (k : ℕ) :
    ∃ (ε : ℝ) (_ : 0 < ε), R.Width ε ∧
      ∃ p : (i : Fin k) → Path
        (R.laneVertex (laneOffset ε k i) 0)
        (R.laneVertex (laneOffset ε k i) (Fin.last n)),
      (∀ i, Function.Injective (p i) ∧ IsPolygonalPath (p i) ∧
        Set.range (p i) = R.laneSupport (laneOffset ε k i)) ∧
      Pairwise (fun i j => Disjoint (Set.range (p i)) (Set.range (p j))) := by
  classical
  obtain ⟨ε,hε,hwidth,hdis⟩ := R.exists_finite_parallel_bundle k
  have hex (i : Fin k) := R.exists_lane_path hn hwidth (laneOffset_bounds hε i).2
  choose p hp using hex
  refine ⟨ε,hε,hwidth,p,hp,?_⟩
  intro i j hij
  rw [(hp i).2.2, (hp j).2.2]
  exact hdis hij

end TransversePolygonalRoute
end
end MatchgateWidth
