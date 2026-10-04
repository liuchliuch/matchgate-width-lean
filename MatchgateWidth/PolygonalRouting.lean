import Mathlib.Data.List.Chain
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Topology.Connected.PathConnected

/-! # Finite straight-segment routing inside open path neighborhoods
This supplies finite polygonal walks. Simplicity and thickened disjoint strips
are separate obligations; neither is encoded as an assumed matchgate property.
-/
namespace MatchgateWidth
noncomputable section
open Set Metric

/-- A finite chain of actual closed straight segments staying in an open carrier. -/
def PolygonallyJoinedIn (U : Set ℂ) (x y : ℂ) : Prop :=
  Relation.ReflTransGen (fun a b => segment ℝ a b ⊆ U) x y

theorem PolygonallyJoinedIn.mem {U : Set ℂ} {x y : ℂ}
    (h : PolygonallyJoinedIn U x y) (hx : x ∈ U) : y ∈ U := by
  induction h with
  | refl => exact hx
  | @tail b c hbc hseg ih => exact hseg (right_mem_segment ℝ b c)

/-- Polygonal reachability is open inside an open Euclidean carrier. -/
theorem polygonal_reachable_isOpen {U : Set ℂ} (hU : IsOpen U) {x : ℂ} (hx : x ∈ U) :
    IsOpen {y | PolygonallyJoinedIn U x y} := by
  apply Metric.isOpen_iff.mpr
  intro y hy
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp hU y (hy.mem hx)
  refine ⟨ε,hε,?_⟩
  intro z hz
  exact hy.tail (((convex_ball y ε).segment_subset (mem_ball_self hε) hz).trans hball)

/-- The other polygonal components are open as well. -/
theorem polygonal_unreachable_isOpen {U : Set ℂ} (hU : IsOpen U) (x : ℂ) :
    IsOpen {y | y ∈ U ∧ ¬ PolygonallyJoinedIn U x y} := by
  apply Metric.isOpen_iff.mpr
  intro y hy
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp hU y hy.1
  refine ⟨ε,hε,?_⟩
  intro z hz
  refine ⟨hball hz,?_⟩
  intro hxz
  exact hy.2 (hxz.tail (((convex_ball y ε).segment_subset hz (mem_ball_self hε)).trans hball))

/-- Every continuous path in an open carrier has a finite straight-segment
route with exactly the same endpoints and still wholly inside that carrier. -/
theorem Path.polygonallyJoinedIn {U : Set ℂ} (hU : IsOpen U) {x y : ℂ}
    (p : Path x y) (hp : Set.range p ⊆ U) : PolygonallyJoinedIn U x y := by
  have hx : x ∈ U := hp ⟨0,p.source⟩
  let R : Set ℂ := {z | PolygonallyJoinedIn U x z}
  let N : Set ℂ := {z | z ∈ U ∧ ¬ PolygonallyJoinedIn U x z}
  have hR : IsOpen R := polygonal_reachable_isOpen hU hx
  have hN : IsOpen N := polygonal_unreachable_isOpen hU x
  have hdis : Disjoint R N := Set.disjoint_left.mpr (by intro z hz hn; exact hn.2 hz)
  have hcover : Set.range p ⊆ R ∪ N := by
    intro z hz
    by_cases hr : PolygonallyJoinedIn U x z
    · exact Or.inl hr
    · exact Or.inr ⟨hp hz,hr⟩
  have hstart : (Set.range p ∩ R).Nonempty :=
    ⟨x,⟨0,p.source⟩,Relation.ReflTransGen.refl⟩
  have hconn : IsPreconnected (Set.range p) := isPreconnected_range p.continuous
  exact hconn.subset_left_of_subset_union hR hN hdis hcover hstart ⟨1,p.target⟩

/-- Finite disjoint compact arc carriers admit simultaneous disjoint open
neighborhoods inside any preassigned open obstacle-avoiding carriers. -/
theorem finite_compact_disjoint_open_neighborhoods {ι : Type*} [Finite ι]
    (S O : ι → Set ℂ) (hS : ∀ i, IsCompact (S i))
    (hdis : Pairwise (fun i j => Disjoint (S i) (S j)))
    (hO : ∀ i, IsOpen (O i)) (hSO : ∀ i, S i ⊆ O i) :
    ∃ U : ι → Set ℂ, (∀ i, IsOpen (U i)) ∧ (∀ i, S i ⊆ U i) ∧
      (∀ i, U i ⊆ O i) ∧ Pairwise (fun i j => Disjoint (U i) (U j)) := by
  classical
  have hex (i j : ι) : ∃ δ : ℝ, 0 < δ ∧
      (i ≠ j → Disjoint (thickening δ (S i)) (thickening δ (S j))) := by
    by_cases hij : i=j
    · exact ⟨1,by norm_num,fun h => (h hij).elim⟩
    · obtain ⟨δ,hδ,hd⟩ := (hdis hij).exists_thickenings (hS i) (hS j).isClosed
      exact ⟨δ,hδ,fun _ => hd⟩
  choose δ hδ hd using hex
  let U : ι → Set ℂ := fun i => O i ∩
    ⋂ j, (thickening (δ i j) (S i) ∩ thickening (δ j i) (S i))
  refine ⟨U,?_,?_,?_,?_⟩
  · intro i
    exact (hO i).inter (isOpen_iInter_of_finite fun j => isOpen_thickening.inter isOpen_thickening)
  · intro i x hx
    exact ⟨hSO i hx,mem_iInter.mpr fun j =>
      ⟨self_subset_thickening (hδ i j) (S i) hx,
       self_subset_thickening (hδ j i) (S i) hx⟩⟩
  · intro i x hx
    exact hx.1
  · intro i j hij
    exact (hd i j hij).mono
      (fun x hx => (mem_iInter.mp hx.2 j).1)
      (fun x hx => (mem_iInter.mp hx.2 i).2)

/-- Simultaneous finite polygonal walks can be selected in pairwise-disjoint
carriers around disjoint continuous arcs. This makes no simplicity claim yet. -/
theorem finite_disjoint_polygonal_routes {ι : Type*} [Finite ι]
    (a b : ι → ℂ) (p : ∀ i, Path (a i) (b i))
    (hdis : Pairwise (fun i j => Disjoint (Set.range (p i)) (Set.range (p j))))
    (O : ι → Set ℂ) (hO : ∀ i, IsOpen (O i)) (hp : ∀ i, Set.range (p i) ⊆ O i) :
    ∃ U : ι → Set ℂ, (∀ i, IsOpen (U i)) ∧ (∀ i, U i ⊆ O i) ∧
      Pairwise (fun i j => Disjoint (U i) (U j)) ∧
      ∀ i, PolygonallyJoinedIn (U i) (a i) (b i) := by
  obtain ⟨U,hU,hpU,hUO,hdU⟩ := finite_compact_disjoint_open_neighborhoods
    (fun i => Set.range (p i)) O (fun i => isCompact_range (p i).continuous) hdis hO hp
  exact ⟨U,hU,hUO,hdU,fun i => MatchgateWidth.Path.polygonallyJoinedIn (hU i) (p i) (hpU i)⟩

/-- The segment chain has an explicit finite list of geometric vertices. -/
theorem PolygonallyJoinedIn.exists_list {U : Set ℂ} {x y : ℂ}
    (h : PolygonallyJoinedIn U x y) :
    ∃ l : List ℂ, l.head? = some x ∧ l.getLast? = some y ∧
      l.IsChain (fun a b => segment ℝ a b ⊆ U) := by
  induction h with
  | refl => exact ⟨[x],rfl,rfl,by simp⟩
  | @tail b c hbc hseg ih =>
    obtain ⟨l,hfirst,hlast,hchain⟩ := ih
    have hne : l ≠ [] := by intro hz; simp [hz] at hfirst
    refine ⟨l++[c],?_,by simp,?_⟩
    · simpa only [List.head?_append_of_ne_nil l hne] using hfirst
    · apply hchain.append (by simp)
      intro u hu v hv
      have hu' : u=b := by
        have hh : b=u := by simpa [hlast] using hu
        exact hh.symm
      have hv' : v=c := by
        have hh : c=v := by simpa using hv
        exact hh.symm
      simpa only [hu',hv'] using hseg

/-- Among all finite straight-segment routes with the prescribed endpoints,
a minimum-length vertex list exists. This is the starting point for geometric
loop erasure; no claim of simple embedded arcs is made by this lemma alone. -/
theorem PolygonallyJoinedIn.exists_minimal_list {U : Set ℂ} {x y : ℂ}
    (h : PolygonallyJoinedIn U x y) :
    ∃ l : List ℂ, l.head? = some x ∧ l.getLast? = some y ∧
      l.IsChain (fun a b => segment ℝ a b ⊆ U) ∧
      ∀ m : List ℂ, m.head? = some x → m.getLast? = some y →
        m.IsChain (fun a b => segment ℝ a b ⊆ U) → l.length ≤ m.length := by
  classical
  let Good := fun l : List ℂ => l.head?=some x ∧ l.getLast?=some y ∧
    l.IsChain (fun a b => segment ℝ a b ⊆ U)
  have hex : ∃ n, ∃ l : List ℂ, Good l ∧ l.length=n := by
    obtain ⟨l,hl⟩ := h.exists_list
    exact ⟨l.length,l,hl,rfl⟩
  obtain ⟨l,hl,hn⟩ := Nat.find_spec hex
  refine ⟨l,hl.1,hl.2.1,hl.2.2,?_⟩
  intro m hm0 hm1 hmc
  rw [hn]
  exact Nat.find_min' hex ⟨m,⟨hm0,hm1,hmc⟩,rfl⟩

end
end MatchgateWidth
