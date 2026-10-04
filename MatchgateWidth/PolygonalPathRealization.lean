import MatchgateWidth.SimplePolygonalRouting
import Mathlib.Analysis.Convex.PathConnected

/-! # Realizing simple polygonal lists by injective paths -/
namespace MatchgateWidth
noncomputable section
open Set unitInterval

/-- A path assembled from finitely many affine straight-segment paths. -/
inductive IsPolygonalPath : {x y : ℂ} → Path x y → Prop
  | segment (x y : ℂ) : IsPolygonalPath (Path.segment x y)
  | trans {x y z : ℂ} {p : Path x y} {q : Path y z} :
      IsPolygonalPath p → IsPolygonalPath q → IsPolygonalPath (p.trans q)

/-- Concatenating simple arcs that meet only at their common endpoint gives
another simple arc, with the usual piecewise-affine time parametrization. -/
theorem Path.injective_trans_of_inter {x y z : ℂ} {p : Path x y} {q : Path y z}
    (hp : Function.Injective p) (hq : Function.Injective q)
    (hint : Set.range p ∩ Set.range q ⊆ {y}) : Function.Injective (p.trans q) := by
  intro s t heq
  rw [Path.trans_apply,Path.trans_apply] at heq
  split_ifs at heq with hs ht ht
  · have hst := congrArg Subtype.val (hp heq)
    apply Subtype.ext
    dsimp at hst
    linarith
  · have hpy : p ⟨2*s,(mul_pos_mem_iff zero_lt_two).2 ⟨s.2.1,hs⟩⟩ = y :=
      hint ⟨⟨_,rfl⟩,⟨_,heq.symm⟩⟩
    have hqt : q ⟨2*t-1,two_mul_sub_one_mem_iff.2 ⟨(not_le.1 ht).le,t.2.2⟩⟩ = y :=
      heq.symm.trans hpy
    have ht0 := congrArg Subtype.val (hq (hqt.trans q.source.symm))
    dsimp at ht0
    exfalso
    linarith
  · have hpy : p ⟨2*t,(mul_pos_mem_iff zero_lt_two).2 ⟨t.2.1,ht⟩⟩ = y :=
      hint ⟨⟨_,rfl⟩,⟨_,heq⟩⟩
    have hqs : q ⟨2*s-1,two_mul_sub_one_mem_iff.2 ⟨(not_le.1 hs).le,s.2.2⟩⟩ = y :=
      heq.trans hpy
    have hs0 := congrArg Subtype.val (hq (hqs.trans q.source.symm))
    dsimp at hs0
    exfalso
    linarith
  · have hst := congrArg Subtype.val (hq heq)
    apply Subtype.ext
    dsimp at hst
    linarith

/-- The geometric trace of a vertex list, including singleton lists. -/
def polygonalTrace : List ℂ → Set ℂ
  | [] => ∅
  | [a] => {a}
  | a :: b :: l => segment ℝ a b ∪ polygonalTrace (b :: l)

/-- Every point of a nontrivial trace belongs to one of its closed edges. -/
theorem mem_polygonalTrace_iff {a b z : ℂ} {l : List ℂ} :
    z ∈ polygonalTrace (a :: b :: l) ↔
      ∃ (p r : List ℂ) (c d : ℂ), a :: b :: l = p ++ c :: d :: r ∧
        z ∈ segment ℝ c d := by
  constructor
  · intro hz
    induction l generalizing a b with
    | nil =>
      refine ⟨[],[],a,b,rfl,?_⟩
      rcases hz with hz | hz
      · exact hz
      · have heq : z = b := hz
        exact heq ▸ right_mem_segment ℝ a z
    | cons c l ih =>
      rcases hz with hz | hz
      · exact ⟨[],c::l,a,b,rfl,hz⟩
      · obtain ⟨p,r,d,e,heq,hz⟩ := ih hz
        exact ⟨a::p,r,d,e,by simpa using congrArg (List.cons a) heq,hz⟩
  · rintro ⟨p,r,c,d,heq,hz⟩
    have hall : ∀ (p r : List ℂ) (c d z : ℂ), z ∈ segment ℝ c d →
        z ∈ polygonalTrace (p ++ c :: d :: r) := by
      intro p r c d z hz
      induction p with
      | nil => exact Or.inl hz
      | cons e p ih =>
        cases p with
        | nil => exact Or.inr ih
        | cons f p => exact Or.inr ih
    exact heq ▸ hall p r c d z hz

/-- Removing the first vertex preserves simplicity. -/
theorem SimplePolygonalList.tail {a : ℂ} {l : List ℂ}
    (h : SimplePolygonalList (a::l)) : SimplePolygonalList l := by
  refine ⟨h.nonzero_edges.tail,?_,?_⟩
  · intro p r b c d heq
    exact h.adjacent_inter (a::p) r b c d (by simpa using congrArg (List.cons a) heq)
  · intro p q r b c d e heq
    exact h.nonadjacent_disjoint (a::p) q r b c d e
      (by simpa using congrArg (List.cons a) heq)

/-- The first edge meets the remainder of a simple trace only at its endpoint. -/
theorem SimplePolygonalList.first_inter_trace {a b : ℂ} {l : List ℂ}
    (h : SimplePolygonalList (a::b::l)) :
    segment ℝ a b ∩ polygonalTrace (b::l) ⊆ {b} := by
  intro z hz
  cases l with
  | nil => exact hz.2
  | cons c l =>
    obtain ⟨p,r,d,e,heq,hzedge⟩ := mem_polygonalTrace_iff.mp hz.2
    cases p with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at heq
      obtain ⟨rfl,rfl,rfl⟩ := heq
      exact h.adjacent_inter [] l a b c rfl ⟨hz.1,hzedge⟩
    | cons f p =>
      simp only [List.cons_append, List.cons.injEq] at heq
      obtain ⟨rfl,heq⟩ := heq
      exact (Set.disjoint_left.mp (h.nonadjacent_disjoint [] p r a b d e
        (by simpa using congrArg (fun t => a :: b :: t) heq)) hz.1 hzedge).elim

/-- Realization of a simple finite vertex list by an injective path assembled
from its straight segments. The image is exactly the polygonal trace. -/
theorem SimplePolygonalList.exists_injective_path {a b : ℂ} {l : List ℂ}
    (h : SimplePolygonalList (a::b::l)) {y : ℂ}
    (hy : (a::b::l).getLast? = some y) :
    ∃ p : Path a y, Function.Injective p ∧ IsPolygonalPath p ∧
      Set.range p = polygonalTrace (a::b::l) := by
  induction l generalizing a b with
  | nil =>
    have hby : b = y := by simpa using hy
    subst y
    refine ⟨Path.segment a b,Path.segment_injective_of_ne h.nonzero_edges.rel,
      IsPolygonalPath.segment a b,?_⟩
    rw [Path.range_segment]
    dsimp [polygonalTrace]
    exact (Set.union_eq_left.mpr (by simpa using right_mem_segment ℝ a b)).symm
  | cons c l ih =>
    obtain ⟨p,hp,hpoly,hrange⟩ := ih h.tail (by simpa using hy)
    refine ⟨(Path.segment a b).trans p,?_,.trans (.segment a b) hpoly,?_⟩
    · apply Path.injective_trans_of_inter
        (Path.segment_injective_of_ne h.nonzero_edges.rel) hp
      rw [Path.range_segment,hrange]
      exact h.first_inter_trace
    · rw [Path.trans_range,Path.range_segment,hrange]
      rfl

/-- Any finite straight-segment walk with distinct endpoints can be replaced
by a genuinely injective piecewise-linear path in the same carrier. -/
theorem PolygonallyJoinedIn.exists_injective_polygonal_path {U : Set ℂ} {x y : ℂ}
    (h : PolygonallyJoinedIn U x y) (hne : x ≠ y) :
    ∃ p : Path x y, Function.Injective p ∧ IsPolygonalPath p ∧ Set.range p ⊆ U := by
  obtain ⟨l,hx,hy,hchain,hsimple⟩ := h.exists_simple_list
  cases l with
  | nil => simp at hx
  | cons a l =>
    have hax : a = x := by simpa using hx
    subst a
    cases l with
    | nil =>
      have hxy : x = y := by simpa using hy
      exact (hne hxy).elim
    | cons b l =>
      obtain ⟨p,hp,hpoly,hrange⟩ := hsimple.exists_injective_path hy
      refine ⟨p,hp,hpoly,?_⟩
      rw [hrange]
      intro z hz
      obtain ⟨r,s,c,d,heq,hz⟩ := mem_polygonalTrace_iff.mp hz
      exact List.isChain_iff_forall_rel_of_append_cons_cons.mp hchain heq hz

/-- Continuous routes in open subsets of the plane admit injective finite
piecewise-linear routes with precisely their original, distinct endpoints. -/
theorem Path.exists_injective_polygonal_path {U : Set ℂ} (hU : IsOpen U) {x y : ℂ}
    (p : Path x y) (hp : Set.range p ⊆ U) (hne : x ≠ y) :
    ∃ q : Path x y, Function.Injective q ∧ IsPolygonalPath q ∧ Set.range q ⊆ U :=
  (Path.polygonallyJoinedIn hU p hp).exists_injective_polygonal_path hne

/-- Finite families of disjoint arcs can simultaneously be replaced by simple
polygonal arcs inside their prescribed open carriers. -/
theorem finite_disjoint_injective_polygonal_routes {ι : Type*} [Finite ι]
    (a b : ι → ℂ) (hne : ∀ i, a i ≠ b i) (p : ∀ i, Path (a i) (b i))
    (hdis : Pairwise (fun i j => Disjoint (Set.range (p i)) (Set.range (p j))))
    (O : ι → Set ℂ) (hO : ∀ i, IsOpen (O i)) (hp : ∀ i, Set.range (p i) ⊆ O i) :
    ∃ q : ∀ i, Path (a i) (b i),
      (∀ i, Function.Injective (q i) ∧ IsPolygonalPath (q i) ∧ Set.range (q i) ⊆ O i) ∧
      Pairwise (fun i j => Disjoint (Set.range (q i)) (Set.range (q j))) := by
  obtain ⟨U,hU,hUO,hdU,hpoly⟩ := finite_disjoint_polygonal_routes a b p hdis O hO hp
  choose q hq using fun i => (hpoly i).exists_injective_polygonal_path (hne i)
  exact ⟨q,fun i => ⟨(hq i).1,(hq i).2.1,(hq i).2.2.trans (hUO i)⟩,
    fun i j hij => (hdU hij).mono (hq i).2.2 (hq j).2.2⟩

end
end MatchgateWidth
