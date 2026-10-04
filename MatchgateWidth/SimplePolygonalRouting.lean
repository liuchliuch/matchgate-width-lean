import MatchgateWidth.PolygonalRouting
import Mathlib.Tactic.Module
import Mathlib.Tactic.LinearCombination

/-! # Loop erasure for finite polygonal routes
A shortest vertex list has nonzero edges, and two of its closed edges meet
only when consecutive, at their common endpoint. -/
namespace MatchgateWidth
noncomputable section
open Set

/-- A minimal polygonal vertex list, with its endpoints kept fixed. -/
def MinimalPolygonalList (U : Set ℂ) (l : List ℂ) : Prop :=
  l.IsChain (fun a b => segment ℝ a b ⊆ U) ∧
  ∀ m : List ℂ, m.head? = l.head? → m.getLast? = l.getLast? →
    m.IsChain (fun a b => segment ℝ a b ⊆ U) → l.length ≤ m.length

private theorem head_splice (p q r : List ℂ) (a b : ℂ) :
    (p ++ a :: q ++ b :: r).head? = (p ++ a :: b :: r).head? := by
  cases p <;> simp

private theorem last_splice (p q r : List ℂ) (a b : ℂ) :
    (p ++ a :: q ++ b :: r).getLast? = (p ++ a :: b :: r).getLast? := by
  simp only [List.getLast?_append_cons, List.getLast?_cons_cons]

/-- Any nontrivial overlap of segments with a common endpoint permits deleting
the corner: one of the outer endpoints belongs to the other segment. -/
theorem mem_segment_or_mem_segment_of_overlap {a b c z : ℂ}
    (hz₁ : z ∈ segment ℝ a b) (hz₂ : z ∈ segment ℝ b c) (hzb : z ≠ b) :
    a ∈ segment ℝ b c ∨ c ∈ segment ℝ a b := by
  rw [segment_symm] at hz₁
  obtain ⟨t, ht, heqt⟩ := (show z ∈ AffineMap.lineMap b a '' Icc (0 : ℝ) 1 by
    simpa only [← segment_eq_image_lineMap] using hz₁)
  obtain ⟨s, hs, heqs⟩ := (show z ∈ AffineMap.lineMap b c '' Icc (0 : ℝ) 1 by
    simpa only [← segment_eq_image_lineMap] using hz₂)
  have ht0 : t ≠ 0 := by intro h; subst t; simp at heqt; exact hzb heqt.symm
  have hs0 : s ≠ 0 := by intro h; subst s; simp at heqs; exact hzb heqs.symm
  have htpos : 0 < t := lt_of_le_of_ne ht.1 ht0.symm
  have hspos : 0 < s := lt_of_le_of_ne hs.1 hs0.symm
  have heq : t • (a - b) = s • (c - b) := by
    simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add] at heqt heqs
    linear_combination (norm := module) heqt - heqs
  rcases le_total s t with hst | hts
  · left
    refine ⟨1-s/t,s/t,sub_nonneg.mpr ((div_le_one htpos).mpr hst),
      div_nonneg hs.1 ht.1,by ring,?_⟩
    have hd : (s/t) • (c-b) = a-b := by
      calc
        (s/t) • (c-b) = t⁻¹ • (s • (c-b)) := by rw [smul_smul]; congr 1; field_simp
        _ = t⁻¹ • (t • (a-b)) := by rw [heq]
        _ = a-b := inv_smul_smul₀ ht0 _
    linear_combination (norm := module) hd
  · right
    rw [segment_symm]
    refine ⟨1-t/s,t/s,sub_nonneg.mpr ((div_le_one hspos).mpr hts),
      div_nonneg ht.1 hs.1,by ring,?_⟩
    have hd : (t/s) • (a-b) = c-b := by
      calc
        (t/s) • (a-b) = s⁻¹ • (t • (a-b)) := by rw [smul_smul]; congr 1; field_simp
        _ = s⁻¹ • (s • (c-b)) := by rw [heq]
        _ = c-b := inv_smul_smul₀ hs0 _
    linear_combination (norm := module) hd

private theorem chain_splice {R : ℂ → ℂ → Prop} {p q r s : List ℂ} {a b : ℂ}
    (h : (p ++ a :: q ++ b :: r).IsChain R)
    (hm : (a :: s ++ [b]).IsChain R) :
    (p ++ a :: s ++ b :: r).IsChain R := by
  have hp : (p ++ [a]).IsChain R := by
    exact ((List.isChain_split (l₁ := p) (c := a) (l₂ := q ++ b :: r)).mp
      (by simpa only [List.append_assoc, List.cons_append] using h)).1
  have hr : (b :: r).IsChain R := (List.isChain_split.mp h).2
  apply List.isChain_split.mpr
  refine ⟨?_,hr⟩
  have hh := (List.isChain_split.mpr ⟨hp,hm⟩ :
    (p ++ a :: (s ++ [b])).IsChain R)
  simpa only [List.append_assoc, List.cons_append] using hh

/-- Replacing the interior of a subroute cannot decrease the number of vertices. -/
theorem MinimalPolygonalList.splice_le {U : Set ℂ} {l : List ℂ}
    (hl : MinimalPolygonalList U l) {p q r : List ℂ} {a b : ℂ}
    (heq : l = p ++ a :: q ++ b :: r) (s : List ℂ)
    (hs : (a :: s ++ [b]).IsChain (fun a b => segment ℝ a b ⊆ U)) :
    q.length ≤ s.length := by
  subst l
  have hh := hl.2 (p ++ a :: s ++ b :: r)
    ((head_splice p s r a b).trans (head_splice p q r a b).symm)
    ((last_splice p s r a b).trans (last_splice p q r a b).symm)
    (chain_splice hl.1 hs)
  simp only [List.length_append, List.length_cons] at hh
  omega

/-- No vertex of a shortest route is repeated. -/
theorem MinimalPolygonalList.no_repeat {U : Set ℂ} {l : List ℂ}
    (hl : MinimalPolygonalList U l) {p q r : List ℂ} {a : ℂ}
    (heq : l = p ++ a :: q ++ a :: r) : False := by
  subst l
  have hp : (p ++ [a]).IsChain (fun a b => segment ℝ a b ⊆ U) := by
    exact ((List.isChain_split (l₁ := p) (c := a) (l₂ := q ++ a :: r)).mp
      (by simpa only [List.append_assoc, List.cons_append] using hl.1)).1
  have hr : (a :: r).IsChain (fun a b => segment ℝ a b ⊆ U) :=
    (List.isChain_split.mp hl.1).2
  have hh := hl.2 (p ++ a :: r) (by cases p <;> simp)
    (by simp only [List.getLast?_append_cons])
    (List.isChain_split.mpr ⟨hp,hr⟩)
  simp only [List.length_append, List.length_cons] at hh
  omega

/-- Every edge of a shortest polygonal route is nondegenerate. -/
theorem MinimalPolygonalList.nonzero_edges {U : Set ℂ} {l : List ℂ}
    (hl : MinimalPolygonalList U l) : l.IsChain (· ≠ ·) := by
  apply List.isChain_iff_forall_rel_of_append_cons_cons.mpr
  intro a b p r heq hab
  subst b
  exact hl.no_repeat (q := []) (by simpa using heq)

/-- Consecutive edges of a shortest route meet only at their shared endpoint. -/
theorem MinimalPolygonalList.adjacent_inter {U : Set ℂ} {l : List ℂ}
    (hl : MinimalPolygonalList U l) {p r : List ℂ} {a b c : ℂ}
    (heq : l = p ++ a :: b :: c :: r) :
    segment ℝ a b ∩ segment ℝ b c ⊆ {b} := by
  intro z hz
  by_contra hzb
  have hzne : z ≠ b := by simpa only [Set.mem_singleton_iff] using hzb
  have hab : segment ℝ a b ⊆ U :=
    List.isChain_iff_forall_rel_of_append_cons_cons.mp hl.1 heq
  have hbc : segment ℝ b c ⊆ U :=
    List.isChain_iff_forall_rel_of_append_cons_cons.mp hl.1
      (l₁ := p ++ [a]) (l₂ := r) (by simpa using heq)
  have hac : segment ℝ a c ⊆ U := by
    rcases mem_segment_or_mem_segment_of_overlap hz.1 hz.2 hzne with ha | hc
    · exact ((convex_segment b c).segment_subset ha (right_mem_segment ℝ b c)).trans hbc
    · exact ((convex_segment a b).segment_subset (left_mem_segment ℝ a b) hc).trans hab
  have hh := hl.splice_le (p := p) (q := [b]) (r := r) (a := a) (b := c)
    (by simpa using heq) [] (by simpa using hac)
  simp at hh

/-- Nonconsecutive closed edges of a shortest route are disjoint. -/
theorem MinimalPolygonalList.nonadjacent_disjoint {U : Set ℂ} {l : List ℂ}
    (hl : MinimalPolygonalList U l) {p q r : List ℂ} {a b c d : ℂ}
    (heq : l = p ++ a :: b :: q ++ c :: d :: r) :
    Disjoint (segment ℝ a b) (segment ℝ c d) := by
  apply Set.disjoint_left.mpr
  intro z hz₁ hz₂
  have hab : segment ℝ a b ⊆ U :=
    List.isChain_iff_forall_rel_of_append_cons_cons.mp hl.1
      (l₁ := p) (l₂ := q ++ c :: d :: r) (by simpa using heq)
  have hcd : segment ℝ c d ⊆ U :=
    List.isChain_iff_forall_rel_of_append_cons_cons.mp hl.1
      (l₁ := p ++ a :: b :: q) (l₂ := r) (by simpa [List.append_assoc] using heq)
  have haz : segment ℝ a z ⊆ U :=
    ((convex_segment a b).segment_subset (left_mem_segment ℝ a b) hz₁).trans hab
  have hzd : segment ℝ z d ⊆ U :=
    ((convex_segment c d).segment_subset hz₂ (right_mem_segment ℝ c d)).trans hcd
  have hh := hl.splice_le (p := p) (q := b :: q ++ [c]) (r := r) (a := a) (b := d)
    (by simpa [List.append_assoc] using heq) [z] (by simp [haz,hzd])
  simp only [List.length_cons, List.length_append, List.length_nil] at hh
  omega

/-- An explicit finite simple polygonal chain: nonzero edges, only the common
endpoint at a corner, and no intersections between nonconsecutive edges. -/
structure SimplePolygonalList (l : List ℂ) : Prop where
  nonzero_edges : l.IsChain (· ≠ ·)
  adjacent_inter : ∀ (p r : List ℂ) (a b c : ℂ), l = p ++ a :: b :: c :: r →
    segment ℝ a b ∩ segment ℝ b c ⊆ {b}
  nonadjacent_disjoint : ∀ (p q r : List ℂ) (a b c d : ℂ),
    l = p ++ a :: b :: q ++ c :: d :: r →
      Disjoint (segment ℝ a b) (segment ℝ c d)

theorem MinimalPolygonalList.simple {U : Set ℂ} {l : List ℂ}
    (hl : MinimalPolygonalList U l) : SimplePolygonalList l :=
  ⟨hl.nonzero_edges, fun _ _ _ _ _ h => hl.adjacent_inter h,
    fun _ _ _ _ _ _ _ h => hl.nonadjacent_disjoint h⟩

/-- Polygonal reachability admits a finite simple polygonal vertex list with
the original endpoints and all its closed edges in the original carrier. -/
theorem PolygonallyJoinedIn.exists_simple_list {U : Set ℂ} {x y : ℂ}
    (h : PolygonallyJoinedIn U x y) :
    ∃ l : List ℂ, l.head? = some x ∧ l.getLast? = some y ∧
      l.IsChain (fun a b => segment ℝ a b ⊆ U) ∧ SimplePolygonalList l := by
  obtain ⟨l,hx,hy,hc,hm⟩ := h.exists_minimal_list
  have hmin : MinimalPolygonalList U l :=
    ⟨hc,fun m hm₀ hm₁ hmc => hm m (hm₀.trans hx) (hm₁.trans hy) hmc⟩
  exact ⟨l,hx,hy,hc,hmin.simple⟩

/-- A corner whose two segments meet only at the corner cannot reverse its
unit tangent. This is the nonzero tangent-bisector condition used in ribbons. -/
theorem norm_smul_add_norm_smul_ne_zero_of_corner {p q r : ℂ}
    (hpq : p ≠ q) (hqr : q ≠ r)
    (hint : segment ℝ p q ∩ segment ℝ q r ⊆ {q}) :
    ‖r-q‖ • (q-p) + ‖q-p‖ • (r-q) ≠ 0 := by
  intro hzero
  let A := ‖q-p‖
  let B := ‖r-q‖
  have hA : 0 < A := norm_pos_iff.mpr (sub_ne_zero.mpr hpq.symm)
  have hB : 0 < B := norm_pos_iff.mpr (sub_ne_zero.mpr hqr.symm)
  have hS : 0 < A+B := add_pos hA hB
  let z : ℂ := (1-B/(A+B)) • q + (B/(A+B)) • p
  have hz₁ : z ∈ segment ℝ p q := by
    rw [segment_symm]
    refine ⟨1-B/(A+B), B/(A+B),?_,div_nonneg hB.le hS.le,by ring,rfl⟩
    exact sub_nonneg.mpr ((div_le_one hS).mpr (by linarith))
  have hrel : (B/(A+B)) • (q-p) + (A/(A+B)) • (r-q) = 0 := by
    change B • (q-p) + A • (r-q) = 0 at hzero
    have hh := congrArg (fun v : ℂ => (A+B)⁻¹ • v) hzero
    rw [smul_add,smul_smul,smul_smul,smul_zero] at hh
    simpa only [div_eq_mul_inv,mul_comm] using hh
  have hzeq : (1-A/(A+B)) • q + (A/(A+B)) • r = z := by
    change (1-A/(A+B)) • q + (A/(A+B)) • r =
      (1-B/(A+B)) • q + (B/(A+B)) • p
    linear_combination (norm := module) hrel
  have hz₂ : z ∈ segment ℝ q r := by
    refine ⟨1-A/(A+B),A/(A+B),?_,div_nonneg hA.le hS.le,by ring,hzeq⟩
    exact sub_nonneg.mpr ((div_le_one hS).mpr (by linarith))
  have hzq : z = q := hint ⟨hz₁,hz₂⟩
  have hnz : (B/(A+B)) • (p-q) = 0 := by
    change (1-B/(A+B)) • q + (B/(A+B)) • p = q at hzq
    linear_combination (norm := module) hzq
  exact (smul_ne_zero (ne_of_gt (div_pos hB hS)) (sub_ne_zero.mpr hpq)) hnz

/-- Every interior vertex of a simple list has a nonzero tangent bisector. -/
theorem SimplePolygonalList.nonbacktracking {l : List ℂ} (hl : SimplePolygonalList l)
    {s t : List ℂ} {p q r : ℂ} (heq : l = s ++ p :: q :: r :: t) :
    ‖r-q‖ • (q-p) + ‖q-p‖ • (r-q) ≠ 0 := by
  apply norm_smul_add_norm_smul_ne_zero_of_corner
  · exact List.isChain_iff_forall_rel_of_append_cons_cons.mp hl.nonzero_edges heq
  · exact List.isChain_iff_forall_rel_of_append_cons_cons.mp hl.nonzero_edges
      (l₁ := s ++ [p]) (l₂ := t) (by simpa using heq)
  · exact hl.adjacent_inter s t p q r heq

end
end MatchgateWidth
