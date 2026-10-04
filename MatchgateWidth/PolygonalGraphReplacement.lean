import MatchgateWidth.IndexedPolygonalRouting
import MatchgateWidth.CompactRoutingSeparation
import MatchgateWidth.DiskBoundaryNoncrossing

/-! # Same-graph polygonal replacement with retained radial endpoint rays
The middle of each original edge is replaced in an open carrier disjoint from
all other middle carriers and all other retained endpoint segments. Loop erasure
is performed within the union of each edge's own two radial stems and carrier.
-/
namespace MatchgateWidth
noncomputable section
open Set Metric

private theorem compact_segment (x y : ℂ) : IsCompact (segment ℝ x y) := by
  rw [← Path.range_segment]
  exact isCompact_range (Path.segment x y).continuous

/-- Restriction to a subinterval, with an affine, non-stationary parametrization. -/
def Path.affineSubpath {x y : ℂ} (p : Path x y) (a b : unitInterval) :
    Path (p a) (p b) where
  toFun t := p ⟨(1-(t:ℝ))*(a:ℝ)+(t:ℝ)*(b:ℝ),by
    constructor
    · nlinarith [t.2.1,t.2.2,a.2.1,b.2.1]
    · have := a.2.2; have := b.2.2
      nlinarith [t.2.1,t.2.2]⟩
  continuous_toFun := p.continuous.comp (by fun_prop)
  source' := by simp
  target' := by simp

theorem Path.affineSubpath_range_subset {x y : ℂ} (p : Path x y)
    {a b : unitInterval} (hab : a ≤ b) :
    Set.range (Path.affineSubpath p a b) ⊆ p '' Icc a b := by
  rintro z ⟨t,rfl⟩
  refine ⟨_,⟨?_,?_⟩,rfl⟩
  · change (a:ℝ) ≤ (1-(t:ℝ))*(a:ℝ)+(t:ℝ)*(b:ℝ)
    have hh : (a:ℝ) ≤ b := hab
    nlinarith [t.2.1,t.2.2]
  · change (1-(t:ℝ))*(a:ℝ)+(t:ℝ)*(b:ℝ) ≤ (b:ℝ)
    have hh : (a:ℝ) ≤ b := hab
    nlinarith [t.2.1,t.2.2]

/-- Every point on a straight initial germ already lies on the original arc. -/
theorem segment_subset_initial_image {x y : ℂ} (p : Path x y)
    (a : unitInterval) (V : ℂ)
    (hg : ∀ t : unitInterval, t ≤ a → p t = x+(t:ℝ)•V) :
    segment ℝ x (p a) ⊆ p '' Icc 0 a := by
  intro z hz
  rw [hg a le_rfl,segment_eq_image_lineMap] at hz
  obtain ⟨t,ht,rfl⟩ := hz
  let u : unitInterval := ⟨t*(a:ℝ),by
    constructor
    · exact mul_nonneg ht.1 a.2.1
    · nlinarith [ht.2,a.2.2,a.2.1]⟩
  have hua : u ≤ a := by change t*(a:ℝ) ≤ a; nlinarith [ht.2,a.2.1]
  refine ⟨u,⟨u.2.1,hua⟩,?_⟩
  rw [hg u hua,AffineMap.lineMap_apply_module]
  change x+(t*(a:ℝ))•V = (1-t)•x+t•(x+(a:ℝ)•V)
  module

namespace PlanarDrawing
variable {V E : Type*} {s : ℕ} {G : WeightedGraph V E ℂ} {ext : Fin s → V}

/-- An interior point of one edge avoids the entire image of another edge. -/
theorem interior_ne_other_edge (D : PlanarDrawing G ext) {e f : E} (hef : e ≠ f)
    (t u : unitInterval) (ht0 : 0<t) (ht1 : t<1) : D.edge e t ≠ D.edge f u := by
  by_cases hu0 : u=0
  · subst u
    rw [D.edge_left]
    exact D.interior_avoids_vertices e t ht0 ht1 _
  by_cases hu1 : u=1
  · subst u
    rw [D.edge_right]
    exact D.interior_avoids_vertices e t ht0 ht1 _
  exact D.interiors_disjoint e f hef t u ht0 ht1
    (lt_of_le_of_ne u.2.1 (Ne.symm hu0)) (lt_of_le_of_ne u.2.2 hu1)

/-- Any common point of two different edges is an original graph vertex. -/
theorem common_edge_point_vertex (D : PlanarDrawing G ext) {e f : E} (hef : e ≠ f)
    {z : ℂ} (he : z ∈ Set.range (D.edge e)) (hf : z ∈ Set.range (D.edge f)) :
    z ∈ Set.range D.vertex := by
  obtain ⟨t,rfl⟩ := he
  obtain ⟨u,hu⟩ := hf
  by_cases ht0 : t=0
  · subst t
    exact ⟨G.left e,(D.edge_left e).symm⟩
  by_cases ht1 : t=1
  · subst t
    exact ⟨G.right e,(D.edge_right e).symm⟩
  exact (D.interior_ne_other_edge hef t u
    (lt_of_le_of_ne t.2.1 (Ne.symm ht0)) (lt_of_le_of_ne t.2.2 ht1) hu.symm).elim

/-- A compact middle subarc stays away from all vertices. -/
theorem middle_avoids_vertices (D : PlanarDrawing G ext) (e : E)
    {a b : unitInterval} (ha : 0<a) (hb : b<1) :
    Disjoint (D.edge e '' Icc a b) (Set.range D.vertex) := by
  apply Set.disjoint_left.mpr
  rintro z ⟨t,ht,rfl⟩ ⟨v,hv⟩
  exact D.interior_avoids_vertices e t (ha.trans_le ht.1) (ht.2.trans_lt hb) v hv.symm

/-- Distinct compact middle subarcs are disjoint, including parallel edges. -/
theorem middles_disjoint (D : PlanarDrawing G ext)
    (a b : E → unitInterval) (ha : ∀ e, 0<a e) (hb : ∀ e, b e<1) :
    Pairwise (fun e f => Disjoint (D.edge e '' Icc (a e) (b e))
      (D.edge f '' Icc (a f) (b f))) := by
  intro e f hef
  apply Set.disjoint_left.mpr
  rintro z ⟨t,ht,rfl⟩ ⟨u,hu,heq⟩
  exact D.interior_ne_other_edge hef t u ((ha e).trans_le ht.1)
    (ht.2.trans_lt (hb e)) heq.symm

/-- Central edge neighborhoods can be simultaneously separated from every
other edge's retained compact stems and from positive balls at all vertices. -/
theorem middle_open_carriers [Finite V] [Finite E] (D : PlanarDrawing G ext)
    (a b : E → unitInterval) (ha : ∀ e, 0<a e) (hb : ∀ e, b e<1)
    (hint : ∀ e t, 0<t → t<1 → ‖D.edge e t‖<1)
    (S : E → Set ℂ) (hS : ∀ e, IsCompact (S e))
    (hSD : ∀ e, S e ⊆ Set.range (D.edge e)) :
    ∃ (δ : V → ℝ) (U : E → Set ℂ), (∀ v, 0<δ v) ∧
      (∀ e, IsOpen (U e)) ∧ (∀ e, D.edge e '' Icc (a e) (b e) ⊆ U e) ∧
      (∀ e z, z∈U e → ‖z‖<1 ∧ ∀ v, δ v < dist z (D.vertex v)) ∧
      Pairwise (fun e f => Disjoint (U e) (U f)) ∧
      (∀ e f, e≠f → Disjoint (U e) (S f)) := by
  classical
  let K : E → Set ℂ := fun e => D.edge e '' Icc (a e) (b e)
  have hK : ∀ e, IsCompact (K e) := fun e =>
    isClosed_Icc.isCompact.image (D.edge_continuous e)
  have hvK : ∀ v e, D.vertex v ∉ K e := by
    intro v e hv
    exact Set.disjoint_left.mp (D.middle_avoids_vertices e (ha e) (hb e)) hv ⟨v,rfl⟩
  choose ρ hρ hρK using fun v =>
    finite_compact_obstacles_avoid_ball K hK (D.vertex v) (hvK v)
  let T : E → Set ℂ := fun e => ⋃ f, if e=f then ∅ else S f
  have hT : ∀ e, IsCompact (T e) := by
    intro e
    apply isCompact_iUnion
    intro f
    by_cases hef : e=f <;> simp only [hef,ite_true,ite_false]
    · exact isCompact_empty
    · exact hS f
  let O : E → Set ℂ := fun e =>
    {z | ‖z‖<1} ∩ (⋂ v, {z | ρ v / 2 < dist z (D.vertex v)}) ∩ (T e)ᶜ
  have hO : ∀ e, IsOpen (O e) := by
    intro e
    exact ((isOpen_lt continuous_norm continuous_const).inter
      (isOpen_iInter_of_finite fun v => isOpen_lt continuous_const
        (continuous_id.dist continuous_const))).inter (hT e).isClosed.isOpen_compl
  have hKO : ∀ e, K e ⊆ O e := by
    intro e z hz
    obtain ⟨t,ht,rfl⟩ := hz
    refine ⟨⟨hint e t ((ha e).trans_le ht.1) (ht.2.trans_lt (hb e)),?_⟩,?_⟩
    · apply Set.mem_iInter.mpr
      intro v
      have hd := hρK v e (D.edge e t) ⟨t,ht,rfl⟩
      change ρ v / 2 < dist (D.edge e t) (D.vertex v)
      linarith [hρ v]
    · intro hz
      obtain ⟨f,hf⟩ := Set.mem_iUnion.mp hz
      by_cases hef : e=f
      · simp [hef] at hf
      · have hfS : D.edge e t ∈ S f := by simpa [hef] using hf
        obtain ⟨u,hu⟩ := hSD f hfS
        exact D.interior_ne_other_edge hef t u ((ha e).trans_le ht.1)
          (ht.2.trans_lt (hb e)) hu.symm
  obtain ⟨U,hU,hKU,hUO,hdis⟩ := finite_compact_disjoint_open_neighborhoods K O hK
    (D.middles_disjoint a b ha hb) hO hKO
  refine ⟨fun v => ρ v/2,U,fun v => div_pos (hρ v) (by norm_num),hU,hKU,?_,hdis,?_⟩
  · intro e z hz
    have hh := hUO e hz
    exact ⟨hh.1.1,fun v => Set.mem_iInter.mp hh.1.2 v⟩
  · intro e f hef
    apply Set.disjoint_left.mpr
    intro z hze hzf
    exact (hUO e hze).2 (Set.mem_iUnion.mpr ⟨f,by simpa [hef] using hzf⟩)

/-- Polygonal replacement data on the original graph, retaining the two
original endpoint rays locally. All drawing properties are conclusions. -/
structure PolygonalStemReplacement (D : PlanarDrawing G ext) (a b : E → unitInterval) where
  path : ∀ e, Path (D.vertex (G.left e)) (D.vertex (G.right e))
  injective : ∀ e, Function.Injective (path e)
  polygonal : ∀ e, IsPolygonalPath (path e)
  in_disk : ∀ e t, ‖path e t‖≤1
  interior_in_disk : ∀ e t, 0<t → t<1 → ‖path e t‖<1
  avoids_vertices : ∀ e t, 0<t → t<1 → ∀ v, path e t ≠ D.vertex v
  disjoint : ∀ e f, e≠f → ∀ t u, 0<t → t<1 → 0<u → u<1 → path e t ≠ path f u
  source_ray : ∀ e, ∃ ε : ℝ, 0<ε ∧ ∀ z∈Set.range (path e),
    dist z (D.vertex (G.left e))<ε → z∈segment ℝ (D.vertex (G.left e)) (D.edge e (a e))
  target_ray : ∀ e, ∃ ε : ℝ, 0<ε ∧ ∀ z∈Set.range (path e),
    dist z (D.vertex (G.right e))<ε → z∈segment ℝ (D.vertex (G.right e)) (D.edge e (b e))

/-- The actual replacement drawing keeps every original vertex and boundary
angle, so the abstract graph and marked boundary labels are literally fixed. -/
def PolygonalStemReplacement.drawing {D : PlanarDrawing G ext} {a b : E → unitInterval}
    (R : D.PolygonalStemReplacement a b) : PlanarDrawing G ext where
  vertex := D.vertex
  vertex_injective := D.vertex_injective
  vertex_in_disk := D.vertex_in_disk
  edge := fun e => R.path e
  edge_continuous := fun e => (R.path e).continuous
  edge_injective := R.injective
  edge_left := fun e => (R.path e).source
  edge_right := fun e => (R.path e).target
  edge_in_disk := R.in_disk
  interior_avoids_vertices := R.avoids_vertices
  interiors_disjoint := R.disjoint
  external_injective := D.external_injective
  angle := D.angle
  angle_pos := D.angle_pos
  angle_lt_one := D.angle_lt_one
  angle_strictMono := D.angle_strictMono
  external_vertex := D.external_vertex

/-- Simultaneously replace all middle arcs, then erase loops within each edge's
own stems and carrier. No simplicity or crossing-free output is assumed. -/
theorem exists_polygonal_stem_replacement [Finite V] [Finite E] (D : PlanarDrawing G ext)
    (a b : E → unitInterval) (ha : ∀ e, 0<a e) (hab : ∀ e, a e<b e) (hb : ∀ e, b e<1)
    (hint : ∀ e t, 0<t → t<1 → ‖D.edge e t‖<1)
    (hL : ∀ e, segment ℝ (D.vertex (G.left e)) (D.edge e (a e)) ⊆ D.edge e '' Icc 0 (a e))
    (hR : ∀ e, segment ℝ (D.edge e (b e)) (D.vertex (G.right e)) ⊆ D.edge e '' Icc (b e) 1) :
    Nonempty (D.PolygonalStemReplacement a b) := by
  classical
  let L : E → Set ℂ := fun e => segment ℝ (D.vertex (G.left e)) (D.edge e (a e))
  let R : E → Set ℂ := fun e => segment ℝ (D.edge e (b e)) (D.vertex (G.right e))
  let S : E → Set ℂ := fun e => L e ∪ R e
  have hS : ∀ e, IsCompact (S e) := fun e => (compact_segment _ _).union (compact_segment _ _)
  have hSD : ∀ e, S e ⊆ Set.range (D.edge e) := by
    intro e z hz
    rcases hz with hz | hz
    · exact Set.image_subset_range _ _ (hL e hz)
    · exact Set.image_subset_range _ _ (hR e hz)
  obtain ⟨δ,U,hδ,hU,hKU,hUb,hUU,hUS⟩ := D.middle_open_carriers a b ha hb hint S hS hSD
  let W : E → Set ℂ := fun e => S e ∪ U e
  have hwalk : ∀ e, PolygonallyJoinedIn (W e) (D.vertex (G.left e)) (D.vertex (G.right e)) := by
    intro e
    have hc : PolygonallyJoinedIn (U e) (D.edge e (a e)) (D.edge e (b e)) :=
      Path.polygonallyJoinedIn (hU e) (Path.affineSubpath (D.edgePath e) (a e) (b e))
        ((Path.affineSubpath_range_subset (D.edgePath e) (hab e).le).trans (hKU e))
    have hcW : PolygonallyJoinedIn (W e) (D.edge e (a e)) (D.edge e (b e)) := by
      exact Relation.ReflTransGen.mono
        (r := fun x y => segment ℝ x y ⊆ U e)
        (p := fun x y => segment ℝ x y ⊆ W e)
        (fun u v hseg z hz => Or.inr (hseg hz)) _ _ hc
    exact ((Relation.ReflTransGen.single (fun z hz => Or.inl (Or.inl hz))).trans hcW).tail
      (fun z hz => Or.inl (Or.inr hz))
  choose q hqi hqp hqW using fun e => (hwalk e).exists_injective_polygonal_path
    (fun he => G.loopless e (D.vertex_injective he))
  have hqavoid : ∀ e t, 0<t → t<1 → ∀ v, q e t ≠ D.vertex v := by
    intro e t ht0 ht1 v heq
    rcases hqW e ⟨t,rfl⟩ with hz | hz
    · obtain ⟨u,hu⟩ := hSD e hz
      by_cases hu0 : u=0
      · subst u
        have htx : q e t = q e 0 := hu.symm.trans (D.edge_left e) |>.trans (q e).source.symm
        exact (ne_of_gt ht0) (hqi e htx)
      by_cases hu1 : u=1
      · subst u
        have hty : q e t = q e 1 := hu.symm.trans (D.edge_right e) |>.trans (q e).target.symm
        exact (ne_of_lt ht1) (hqi e hty)
      exact D.interior_avoids_vertices e u (lt_of_le_of_ne u.2.1 (Ne.symm hu0))
        (lt_of_le_of_ne u.2.2 hu1) v (hu.trans heq)
    · have hd := (hUb e (q e t) hz).2 v
      rw [heq,dist_self] at hd
      exact (not_lt_of_ge (hδ v).le) hd
  have hqinterior : ∀ e t, 0<t → t<1 → ‖q e t‖<1 := by
    intro e t ht0 ht1
    rcases hqW e ⟨t,rfl⟩ with hz | hz
    · obtain ⟨u,hu⟩ := hSD e hz
      have hu0 : u≠0 := by
        intro hu0
        subst u
        exact hqavoid e t ht0 ht1 (G.left e) (hu.symm.trans (D.edge_left e))
      have hu1 : u≠1 := by
        intro hu1
        subst u
        exact hqavoid e t ht0 ht1 (G.right e) (hu.symm.trans (D.edge_right e))
      rw [← hu]
      exact hint e u (lt_of_le_of_ne u.2.1 hu0.symm) (lt_of_le_of_ne u.2.2 hu1)
    · exact (hUb e _ hz).1
  refine ⟨⟨q,hqi,hqp,?_,hqinterior,hqavoid,?_,?_,?_⟩⟩
  · intro e t
    rcases hqW e ⟨t,rfl⟩ with hz | hz
    · obtain ⟨u,hu⟩ := hSD e hz
      rw [← hu]
      exact D.edge_in_disk e u
    · exact (hUb e _ hz).1.le
  · intro e f hef t u ht0 ht1 hu0 hu1 heq
    have he := hqW e ⟨t,rfl⟩
    have hf := hqW f ⟨u,heq.symm⟩
    rcases he with he | he <;> rcases hf with hf | hf
    · obtain ⟨v,hv⟩ := D.common_edge_point_vertex hef (hSD e he) (hSD f hf)
      exact hqavoid e t ht0 ht1 v hv.symm
    · exact Set.disjoint_left.mp (hUS f e hef.symm) hf he
    · exact Set.disjoint_left.mp (hUS e f hef) he hf
    · exact Set.disjoint_left.mp (hUU hef) he hf
  · intro e
    have hxR : D.vertex (G.left e) ∉ R e := by
      intro hx
      obtain ⟨t,ht,heq⟩ := hR e hx
      have ht0 : t=0 := D.edge_injective e (heq.trans (D.edge_left e).symm)
      subst t
      exact (not_le_of_gt ((ha e).trans (hab e))) ht.1
    obtain ⟨ε,hε,he⟩ := finite_compact_obstacles_avoid_ball (fun _ : Unit => R e)
      (fun _ => compact_segment _ _) (D.vertex (G.left e)) (fun _ => hxR)
    refine ⟨min ε (δ (G.left e)),lt_min hε (hδ _),?_⟩
    intro z hz hzd
    rcases hqW e hz with (hz | hz) | hz
    · exact hz
    · exact (not_lt_of_ge (he () z hz) (hzd.trans_le (min_le_left _ _))).elim
    · exact (not_lt_of_ge ((hUb e z hz).2 (G.left e)).le
        (hzd.trans_le (min_le_right _ _))).elim
  · intro e
    have hyL : D.vertex (G.right e) ∉ L e := by
      intro hy
      obtain ⟨t,ht,heq⟩ := hL e hy
      have ht1 : t=1 := D.edge_injective e (heq.trans (D.edge_right e).symm)
      subst t
      exact (not_le_of_gt ((hab e).trans (hb e))) ht.2
    obtain ⟨ε,hε,he⟩ := finite_compact_obstacles_avoid_ball (fun _ : Unit => L e)
      (fun _ => compact_segment _ _) (D.vertex (G.right e)) (fun _ => hyL)
    refine ⟨min ε (δ (G.right e)),lt_min hε (hδ _),?_⟩
    intro z hz hzd
    rcases hqW e hz with (hz | hz) | hz
    · exact (not_lt_of_ge (he () z hz) (hzd.trans_le (min_le_left _ _))).elim
    · change z ∈ segment ℝ (D.edge e (b e)) (D.vertex (G.right e)) at hz
      rwa [segment_symm]
    · exact (not_lt_of_ge ((hUb e z hz).2 (G.right e)).le
        (hzd.trans_le (min_le_right _ _))).elim

end PlanarDrawing
end
end MatchgateWidth
