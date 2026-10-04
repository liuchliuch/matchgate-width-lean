import MatchgateWidth.IndexedPolygonalRouting

namespace MatchgateWidth
noncomputable section
open Set

namespace IndexedSimplePolygonalRoute
variable {U : Set ℂ} {x y : ℂ} (r : IndexedSimplePolygonalRoute U x y)

/-- The first edge, available because routes are nontrivial. -/
def firstEdge : Fin r.edgeCount := ⟨0, r.positive⟩
/-- The last edge of a nontrivial route. -/
def lastEdge : Fin r.edgeCount := ⟨r.edgeCount - 1, by have := r.positive; omega⟩

@[simp] theorem firstEdge_val : r.firstEdge.val = 0 := rfl
@[simp] theorem lastEdge_val : r.lastEdge.val = r.edgeCount - 1 := rfl

@[simp] theorem firstEdge_castSucc : r.firstEdge.castSucc = 0 := rfl
@[simp] theorem lastEdge_succ : r.lastEdge.succ = Fin.last r.edgeCount := by
  apply Fin.ext
  simp only [Fin.val_succ, lastEdge_val, Fin.val_last]
  have := r.positive
  omega

/-- The source belongs to exactly the first closed edge of a simple route. -/
theorem source_mem_segment_iff_index_zero (i : Fin r.edgeCount) :
    x ∈ segment ℝ (r.vertex i.castSucc) (r.vertex i.succ) ↔ i.val = 0 := by
  have hx : x ∈ segment ℝ (r.vertex r.firstEdge.castSucc)
      (r.vertex r.firstEdge.succ) := by
    simpa only [r.firstEdge_castSucc, r.source] using
      left_mem_segment ℝ (r.vertex r.firstEdge.castSucc) (r.vertex r.firstEdge.succ)
  constructor
  · intro hi
    by_contra hn
    by_cases h1 : i.val = 1
    · have he := r.adjacent r.firstEdge i (by simpa using h1.symm) ⟨hx, hi⟩
      have he' : x = r.vertex r.firstEdge.succ := Set.mem_singleton_iff.mp he
      exact r.nonzero r.firstEdge (by simpa only [r.firstEdge_castSucc, r.source] using he')
    · exact Set.disjoint_left.mp (r.nonadjacent r.firstEdge i (by simp; omega)) hx hi
  · intro hi
    have he : i = r.firstEdge := Fin.ext hi
    simpa only [he] using hx

/-- The target belongs to exactly the last closed edge of a simple route. -/
theorem target_mem_segment_iff_last (i : Fin r.edgeCount) :
    y ∈ segment ℝ (r.vertex i.castSucc) (r.vertex i.succ) ↔
      i.val+1 = r.edgeCount := by
  have hy : y ∈ segment ℝ (r.vertex r.lastEdge.castSucc)
      (r.vertex r.lastEdge.succ) := by
    simpa only [r.lastEdge_succ, r.target] using
      right_mem_segment ℝ (r.vertex r.lastEdge.castSucc) (r.vertex r.lastEdge.succ)
  constructor
  · intro hi
    by_contra hn
    by_cases h1 : i.val+1 = r.lastEdge.val
    · have he := r.adjacent i r.lastEdge h1 ⟨hi, hy⟩
      have he' : y = r.vertex i.succ := Set.mem_singleton_iff.mp he
      have heq : i.succ = r.lastEdge.castSucc := Fin.ext h1
      exact r.nonzero r.lastEdge (by simpa only [heq, r.lastEdge_succ, r.target] using he'.symm)
    · have hlt : i.val+1 < r.lastEdge.val := by
        have := i.isLt
        simp only [lastEdge_val] at *
        omega
      exact Set.disjoint_left.mp (r.nonadjacent i r.lastEdge hlt) hi hy
  · intro hi
    have he : i = r.lastEdge := Fin.ext (by simp only [lastEdge_val]; omega)
    simpa only [he] using hy

/-- Replace only the two endpoint vertices. -/
def trimmedVertex (a b : ℂ) (i : Fin (r.edgeCount+1)) : ℂ :=
  if i.val = 0 then a else if i.val = r.edgeCount then b else r.vertex i

@[simp] theorem trimmedVertex_zero (a b : ℂ) : r.trimmedVertex a b 0 = a := by
  simp [trimmedVertex]
@[simp] theorem trimmedVertex_last (a b : ℂ) :
    r.trimmedVertex a b (Fin.last r.edgeCount) = b := by
  have hn := r.positive
  simp [trimmedVertex, Nat.ne_of_gt hn]

theorem trimmedVertex_interior (a b : ℂ) (i : Fin (r.edgeCount+1))
    (h0 : 0 < i.val) (hn : i.val < r.edgeCount) :
    r.trimmedVertex a b i = r.vertex i := by
  simp [trimmedVertex, Nat.ne_of_gt h0, Nat.ne_of_lt hn]

@[simp] theorem trimmedVertex_castSucc (a b : ℂ) (i : Fin r.edgeCount) :
    r.trimmedVertex a b i.castSucc = if i.val = 0 then a else r.vertex i.castSucc := by
  simp [trimmedVertex, Nat.ne_of_lt i.isLt]
@[simp] theorem trimmedVertex_succ (a b : ℂ) (i : Fin r.edgeCount) :
    r.trimmedVertex a b i.succ =
      if i.val+1 = r.edgeCount then b else r.vertex i.succ := by
  simp [trimmedVertex]

/-- Endpoint replacement inside the end edges shrinks every edge individually. -/
theorem trimmed_segment_subset (a b : ℂ)
    (ha : a ∈ segment ℝ (r.vertex r.firstEdge.castSucc) (r.vertex r.firstEdge.succ))
    (hb : b ∈ segment ℝ (r.vertex r.lastEdge.castSucc) (r.vertex r.lastEdge.succ))
    (i : Fin r.edgeCount) :
    segment ℝ (r.trimmedVertex a b i.castSucc) (r.trimmedVertex a b i.succ) ⊆
      segment ℝ (r.vertex i.castSucc) (r.vertex i.succ) := by
  have hleft : r.trimmedVertex a b i.castSucc ∈
      segment ℝ (r.vertex i.castSucc) (r.vertex i.succ) := by
    rw [r.trimmedVertex_castSucc]
    split_ifs with hi
    · have he : i = r.firstEdge := Fin.ext hi
      simpa [he] using ha
    · exact left_mem_segment _ _ _
  have hright : r.trimmedVertex a b i.succ ∈
      segment ℝ (r.vertex i.castSucc) (r.vertex i.succ) := by
    rw [r.trimmedVertex_succ]
    split_ifs with hi
    · have he : i = r.lastEdge := Fin.ext (by simp only [lastEdge_val]; omega)
      simpa [he] using hb
    · exact right_mem_segment _ _ _
  exact (convex_segment (𝕜 := ℝ) _ _).segment_subset hleft hright

/-- Trimming creates no new adjacent-edge intersection, even for two edges. -/
theorem trimmed_adjacent (a b : ℂ)
    (ha : a ∈ segment ℝ (r.vertex r.firstEdge.castSucc) (r.vertex r.firstEdge.succ))
    (hb : b ∈ segment ℝ (r.vertex r.lastEdge.castSucc) (r.vertex r.lastEdge.succ))
    (i j : Fin r.edgeCount) (hij : i.val+1=j.val) :
    segment ℝ (r.trimmedVertex a b i.castSucc) (r.trimmedVertex a b i.succ) ∩
      segment ℝ (r.trimmedVertex a b j.castSucc) (r.trimmedVertex a b j.succ) ⊆
        {r.trimmedVertex a b i.succ} := by
  have hi : i.val+1 < r.edgeCount := by rw [hij]; exact j.isLt
  intro z hz
  have hz' := r.adjacent i j hij
    ⟨r.trimmed_segment_subset a b ha hb i hz.1,
      r.trimmed_segment_subset a b ha hb j hz.2⟩
  simpa only [r.trimmedVertex_interior a b i.succ (by simp) hi] using hz' 

/-- Trimming preserves all nonadjacent-edge disjointness certificates. -/
theorem trimmed_nonadjacent (a b : ℂ)
    (ha : a ∈ segment ℝ (r.vertex r.firstEdge.castSucc) (r.vertex r.firstEdge.succ))
    (hb : b ∈ segment ℝ (r.vertex r.lastEdge.castSucc) (r.vertex r.lastEdge.succ))
    (i j : Fin r.edgeCount) (hij : i.val+1<j.val) :
    Disjoint
      (segment ℝ (r.trimmedVertex a b i.castSucc) (r.trimmedVertex a b i.succ))
      (segment ℝ (r.trimmedVertex a b j.castSucc) (r.trimmedVertex a b j.succ)) :=
  (r.nonadjacent i j hij).mono (r.trimmed_segment_subset a b ha hb i)
    (r.trimmed_segment_subset a b ha hb j)

/-- Strict cuts leave every edge nondegenerate; a one-edge route additionally
requires that its two cut points be distinct. -/
theorem trimmed_nonzero (a b : ℂ)
    (ha : a ∈ openSegment ℝ (r.vertex r.firstEdge.castSucc) (r.vertex r.firstEdge.succ))
    (hb : b ∈ openSegment ℝ (r.vertex r.lastEdge.castSucc) (r.vertex r.lastEdge.succ))
    (hab : r.edgeCount = 1 → a ≠ b) (i : Fin r.edgeCount) :
    r.trimmedVertex a b i.castSucc ≠ r.trimmedVertex a b i.succ := by
  rw [r.trimmedVertex_castSucc, r.trimmedVertex_succ]
  split_ifs with h0 hn hn
  · exact hab (by omega)
  · have he : i = r.firstEdge := Fin.ext h0
    subst i
    intro heq
    rw [heq] at ha
    exact r.nonzero r.firstEdge (right_mem_openSegment_iff.mp ha)
  · have he : i = r.lastEdge := Fin.ext (by simp only [lastEdge_val]; omega)
    subst i
    intro heq
    rw [← heq] at hb
    exact r.nonzero r.lastEdge (left_mem_openSegment_iff.mp hb)
  · exact r.nonzero i

/-- Exact finite geometric trimming, retaining the edge count and all interior
vertices. The extra premise is needed only in the single-edge case. -/
def trimEndpoints (a b : ℂ)
    (ha : a ∈ openSegment ℝ (r.vertex r.firstEdge.castSucc) (r.vertex r.firstEdge.succ))
    (hb : b ∈ openSegment ℝ (r.vertex r.lastEdge.castSucc) (r.vertex r.lastEdge.succ))
    (hab : r.edgeCount = 1 → a ≠ b) : IndexedSimplePolygonalRoute U a b where
  edgeCount := r.edgeCount
  positive := r.positive
  vertex := r.trimmedVertex a b
  source := r.trimmedVertex_zero a b
  target := r.trimmedVertex_last a b
  segment_subset i := (r.trimmed_segment_subset a b
    (openSegment_subset_segment _ _ _ ha) (openSegment_subset_segment _ _ _ hb) i).trans
      (r.segment_subset i)
  nonzero := r.trimmed_nonzero a b ha hb hab
  adjacent := r.trimmed_adjacent a b (openSegment_subset_segment _ _ _ ha)
    (openSegment_subset_segment _ _ _ hb)
  nonadjacent := r.trimmed_nonadjacent a b (openSegment_subset_segment _ _ _ ha)
    (openSegment_subset_segment _ _ _ hb)

/-- With at least two edges, the two strict endpoint cuts are independent. -/
def trimEndpointsOfTwoLE (hn : 2 ≤ r.edgeCount) (a b : ℂ)
    (ha : a ∈ openSegment ℝ (r.vertex r.firstEdge.castSucc) (r.vertex r.firstEdge.succ))
    (hb : b ∈ openSegment ℝ (r.vertex r.lastEdge.castSucc) (r.vertex r.lastEdge.succ)) :
    IndexedSimplePolygonalRoute U a b :=
  r.trimEndpoints a b ha hb (by omega)

/-- The trimmed route retains precisely the original interior vertices. -/
theorem trimEndpoints_vertex_interior (a b : ℂ)
    (ha : a ∈ openSegment ℝ (r.vertex r.firstEdge.castSucc) (r.vertex r.firstEdge.succ))
    (hb : b ∈ openSegment ℝ (r.vertex r.lastEdge.castSucc) (r.vertex r.lastEdge.succ))
    (hab : r.edgeCount = 1 → a ≠ b) (i : Fin (r.edgeCount+1))
    (h0 : 0 < i.val) (hn : i.val < r.edgeCount) :
    (r.trimEndpoints a b ha hb hab).vertex i = r.vertex i :=
  r.trimmedVertex_interior a b i h0 hn

/-- Trimming only removes points from the original polygonal trace. -/
theorem trimEndpoints_trace_subset (a b : ℂ)
    (ha : a ∈ openSegment ℝ (r.vertex r.firstEdge.castSucc) (r.vertex r.firstEdge.succ))
    (hb : b ∈ openSegment ℝ (r.vertex r.lastEdge.castSucc) (r.vertex r.lastEdge.succ))
    (hab : r.edgeCount = 1 → a ≠ b) :
    polygonalTrace (List.ofFn (r.trimEndpoints a b ha hb hab).vertex) ⊆
      polygonalTrace (List.ofFn r.vertex) := by
  rw [polygonalTrace_ofFn (r.trimEndpoints a b ha hb hab).positive,
    polygonalTrace_ofFn r.positive]
  exact Set.iUnion_mono fun i => r.trimmed_segment_subset a b
    (openSegment_subset_segment _ _ _ ha) (openSegment_subset_segment _ _ _ hb) i

/-- For a single edge, two strictly ordered affine parameters give exact,
nondegenerate endpoint trimming. -/
def trimSingleEdge (hn : r.edgeCount = 1) (α β : ℝ)
    (hα : 0 < α) (hαβ : α < β) (hβ : β < 1) :
    IndexedSimplePolygonalRoute U (AffineMap.lineMap x y α) (AffineMap.lineMap x y β) := by
  have hfirst : r.vertex r.firstEdge.succ = y := by
    have he : r.firstEdge.succ = Fin.last r.edgeCount := by
      apply Fin.ext
      simp only [Fin.val_succ, firstEdge_val, Fin.val_last, hn]
    rw [he, r.target]
  have hlast : r.vertex r.lastEdge.castSucc = x := by
    have he : r.lastEdge.castSucc = 0 := by
      apply Fin.ext
      simp only [Fin.val_castSucc, lastEdge_val, hn, Nat.sub_self, Fin.val_zero]
    rw [he, r.source]
  have hxy : x ≠ y := by
    simpa only [r.firstEdge_castSucc, r.source, hfirst] using r.nonzero r.firstEdge
  refine r.trimEndpoints (AffineMap.lineMap x y α) (AffineMap.lineMap x y β) ?_ ?_ ?_
  · simpa only [r.firstEdge_castSucc, r.source, hfirst] using
      lineMap_mem_openSegment ℝ x y (show α ∈ Ioo (0 : ℝ) 1 from ⟨hα, hαβ.trans hβ⟩)
  · simpa only [hlast, r.lastEdge_succ, r.target] using
      lineMap_mem_openSegment ℝ x y (show β ∈ Ioo (0 : ℝ) 1 from ⟨hα.trans hαβ, hβ⟩)
  · intro _
    exact (AffineMap.lineMap_injective ℝ hxy).ne hαβ.ne

end IndexedSimplePolygonalRoute
end
end MatchgateWidth
