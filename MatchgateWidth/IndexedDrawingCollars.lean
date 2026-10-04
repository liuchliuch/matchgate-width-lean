import MatchgateWidth.PolygonalDrawingRoutes
import MatchgateWidth.IndexedPolygonalRadialTrimming
import MatchgateWidth.PolygonalCollarGeometry

/-! # Derived common round collars for finite indexed drawing routes -/
namespace MatchgateWidth
noncomputable section
open Set Metric

private theorem polygonalPath_cast {x y x' y' : ℂ} {p : Path x y}
    (hp : IsPolygonalPath p) (hx : x'=x) (hy : y'=y) : IsPolygonalPath (p.cast hx hy) := by
  subst x' y'
  simpa using hp
namespace PlanarDrawing
variable {V E : Type*} {s : ℕ} {G : WeightedGraph V E ℂ} {ext : Fin s → V}

/-- A segment is incident with an original vertex only when it is the first
segment at that edge's source, or the last segment at its target. -/
def IndexedRoutes.EndIncident {D : PlanarDrawing G ext} (R : D.IndexedRoutes)
    (v : V) (e : E) (i : Fin (R e).edgeCount) : Prop :=
  (G.left e=v ∧ i.val=0) ∨ (G.right e=v ∧ i.val+1=(R e).edgeCount)

theorem IndexedRoutes.nonincident_avoids_vertex {D : PlanarDrawing G ext}
    (R : D.IndexedRoutes) (v : V) (e : E) (i : Fin (R e).edgeCount)
    (hi : ¬R.EndIncident v e i) :
    D.vertex v ∉ segment ℝ ((R e).vertex i.castSucc) ((R e).vertex i.succ) := by
  intro hz
  obtain ⟨t,ht⟩ := (R e).segment_subset i hz
  by_cases ht0 : t=0
  · subst t
    have hv : G.left e=v := D.vertex_injective ((D.edge_left e).symm.trans ht)
    have hii := ((R e).source_mem_segment_iff_index_zero i).mp (by simpa only [hv] using hz)
    exact hi (Or.inl ⟨hv,hii⟩)
  by_cases ht1 : t=1
  · subst t
    have hv : G.right e=v := D.vertex_injective ((D.edge_right e).symm.trans ht)
    have hii := ((R e).target_mem_segment_iff_last i).mp (by simpa only [hv] using hz)
    exact hi (Or.inr ⟨hv,hii⟩)
  exact D.interior_avoids_vertices e t (lt_of_le_of_ne t.2.1 (Ne.symm ht0))
    (lt_of_le_of_ne t.2.2 ht1) v ht

/-- A positive common collar radius with ample room for nested radial cuts.
Every relevant separation is derived from the actual finite drawing. -/
theorem IndexedRoutes.exists_collar_radius [Finite V] [Finite E]
    {D : PlanarDrawing G ext} (R : D.IndexedRoutes) :
    ∃ r : ℝ, 0<r ∧ r<1/16 ∧
      Pairwise (fun v w => Disjoint (closedBall (D.vertex v) (4*r))
        (closedBall (D.vertex w) (4*r))) ∧
      (∀ e, 16*r < ‖(R e).vertex (R e).firstEdge.succ - D.vertex (G.left e)‖ ∧
        16*r < ‖D.vertex (G.right e) - (R e).vertex (R e).lastEdge.castSucc‖) ∧
      (∀ v e (i : Fin (R e).edgeCount), ¬R.EndIncident v e i →
        ∀ z∈segment ℝ ((R e).vertex i.castSucc) ((R e).vertex i.succ),
          4*r < dist z (D.vertex v)) := by
  classical
  let J := Σ e : E, Fin (R e).edgeCount
  let K : J → Set ℂ := fun j => segment ℝ ((R j.1).vertex j.2.castSucc) ((R j.1).vertex j.2.succ)
  have hK : ∀ j, IsCompact (K j) := by
    intro j
    rw [show K j = Set.range (Path.segment ((R j.1).vertex j.2.castSucc)
      ((R j.1).vertex j.2.succ)) by rw [Path.range_segment]]
    exact isCompact_range (Path.segment _ _).continuous
  obtain ⟨ro,hro,hroK⟩ := finite_vertex_obstacle_radius D.vertex K hK
    (fun v j => R.EndIncident v j.1 j.2)
    (fun v j hj => R.nonincident_avoids_vertex v j.1 j.2 hj)
  obtain ⟨rv,hrv,hrvdis⟩ := finite_points_disjoint_closedBalls D.vertex D.vertex_injective
  let len : E → ℝ := fun e => min
    ‖(R e).vertex (R e).firstEdge.succ - D.vertex (G.left e)‖
    ‖D.vertex (G.right e) - (R e).vertex (R e).lastEdge.castSucc‖
  have hlen : ∀ e, 0<len e := by
    intro e
    apply lt_min
    · apply norm_pos_iff.mpr
      apply sub_ne_zero.mpr
      have hh := (R e).nonzero (R e).firstEdge
      simpa only [(R e).firstEdge_castSucc,(R e).source] using hh.symm
    · apply norm_pos_iff.mpr
      apply sub_ne_zero.mpr
      have hh := (R e).nonzero (R e).lastEdge
      simpa only [(R e).lastEdge_succ,(R e).target] using hh.symm
  obtain ⟨rl,hrl,hrlL⟩ := finite_positive_lower_bound len hlen
  let ε : ℝ := min 1 (min rv (min ro rl))
  have hε : 0<ε := lt_min (by norm_num) (lt_min hrv (lt_min hro hrl))
  have hε1 : ε≤1 := min_le_left _ _
  have hεv : ε≤rv := (min_le_right _ _).trans (min_le_left _ _)
  have hεo : ε≤ro := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hεl : ε≤rl := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨ε/32,div_pos hε (by norm_num),by linarith,?_,?_,?_⟩
  · intro v w hvw
    apply (hrvdis hvw).mono (closedBall_subset_closedBall (by linarith))
      (closedBall_subset_closedBall (by linarith))
  · intro e
    have hh := hrlL e
    have hfirst : rl≤‖(R e).vertex (R e).firstEdge.succ-D.vertex (G.left e)‖ :=
      hh.trans (min_le_left _ _)
    have hlast : rl≤‖D.vertex (G.right e)-(R e).vertex (R e).lastEdge.castSucc‖ :=
      hh.trans (min_le_right _ _)
    constructor <;> linarith
  · intro v e i hi z hz
    have hh := hroK v ⟨e,i⟩ hi z hz
    linarith

/-- Derived geometric room for all edge cuts and all local vertex insertions. -/
structure IndexedRoutes.Collars {D : PlanarDrawing G ext} (R : D.IndexedRoutes) where
  radius : ℝ
  positive : 0<radius
  small : radius<1/16
  disks_disjoint : Pairwise (fun v w => Disjoint (closedBall (D.vertex v) (4*radius))
    (closedBall (D.vertex w) (4*radius)))
  lengths : ∀ e, 16*radius < ‖(R e).vertex (R e).firstEdge.succ-D.vertex (G.left e)‖ ∧
    16*radius < ‖D.vertex (G.right e)-(R e).vertex (R e).lastEdge.castSucc‖
  separation : ∀ v e (i : Fin (R e).edgeCount), ¬R.EndIncident v e i →
    ∀ z∈segment ℝ ((R e).vertex i.castSucc) ((R e).vertex i.succ),
      4*radius < dist z (D.vertex v)

theorem IndexedRoutes.exists_collars [Finite V] [Finite E]
    {D : PlanarDrawing G ext} (R : D.IndexedRoutes) : Nonempty R.Collars := by
  obtain ⟨r,hr,hs,hd,hl,hsep⟩ := R.exists_collar_radius
  exact ⟨⟨r,hr,hs,hd,hl,hsep⟩⟩

namespace IndexedRoutes.Collars
variable {D : PlanarDrawing G ext} {R : D.IndexedRoutes} (C : R.Collars)

private theorem cut_first_bound {δ : ℝ} (hδ : δ≤4*C.radius) (e : E) :
    3*δ < ‖(R e).vertex (R e).firstEdge.succ-(R e).vertex (R e).firstEdge.castSucc‖ := by
  simp only [(R e).firstEdge_castSucc,(R e).source]
  have hh := (C.lengths e).1
  linarith [C.positive]

private theorem cut_last_bound {δ : ℝ} (hδ : δ≤4*C.radius) (e : E) :
    3*δ < ‖(R e).vertex (R e).lastEdge.succ-(R e).vertex (R e).lastEdge.castSucc‖ := by
  simp only [(R e).lastEdge_succ,(R e).target]
  have hh := (C.lengths e).2
  linarith [C.positive]

/-- The actual indexed corridor obtained by cutting both endpoint segments
at any positive radius at most four times the common base radius. -/
def trimRoute (δ : ℝ) (hδ : 0<δ) (hδmax : δ≤4*C.radius) (e : E) :
    IndexedSimplePolygonalRoute (Set.range (D.edge e))
      ((R e).radialSourceCut δ) ((R e).radialTargetCut δ) :=
  (R e).trimAtRadius δ hδ (C.cut_first_bound hδmax e) (C.cut_last_bound hδmax e)

/-- Every trimmed corridor, including its endpoints, avoids every open vertex
disk at its exact cut radius. The one-segment case is included. -/
theorem trimRoute_segment_outside (δ : ℝ) (hδ : 0<δ) (hδmax : δ≤4*C.radius)
    (v : V) (e : E) (i : Fin (R e).edgeCount)
    {z : ℂ} (hz : z∈segment ℝ ((C.trimRoute δ hδ hδmax e).vertex i.castSucc)
      ((C.trimRoute δ hδ hδmax e).vertex i.succ)) : δ≤dist z (D.vertex v) := by
  by_cases hi : R.EndIncident v e i
  · rcases hi with ⟨hv,hi⟩ | ⟨hv,hi⟩
    · have hii : i=(R e).firstEdge := Fin.ext hi
      subst i
      subst v
      exact (R e).trimAtRadius_first_segment_outside δ hδ
        (C.cut_first_bound hδmax e) (C.cut_last_bound hδmax e) z hz
    · have hii : i=(R e).lastEdge := Fin.ext (by simp only [IndexedSimplePolygonalRoute.lastEdge_val]; omega)
      subst i
      subst v
      exact (R e).trimAtRadius_last_segment_outside δ hδ
        (C.cut_first_bound hδmax e) (C.cut_last_bound hδmax e) z hz
  · have hzo := (R e).trimAtRadius_segment_subset δ hδ
      (C.cut_first_bound hδmax e) (C.cut_last_bound hδmax e) i hz
    exact hδmax.trans (C.separation v e i hi z hzo).le

/-- The compact geometric support of a derived central corridor. -/
def support (δ : ℝ) (hδ : 0<δ) (hδmax : δ≤4*C.radius) (e : E) : Set ℂ :=
  ⋃ i : Fin (R e).edgeCount, segment ℝ ((C.trimRoute δ hδ hδmax e).vertex i.castSucc)
    ((C.trimRoute δ hδ hδmax e).vertex i.succ)

theorem support_compact (δ : ℝ) (hδ : 0<δ) (hδmax : δ≤4*C.radius) (e : E) :
    IsCompact (C.support δ hδ hδmax e) := by
  apply isCompact_iUnion
  intro i
  rw [← Path.range_segment]
  exact isCompact_range (Path.segment _ _).continuous

theorem support_subset_old (δ : ℝ) (hδ : 0<δ) (hδmax : δ≤4*C.radius) (e : E) :
    C.support δ hδ hδmax e ⊆ Set.range (D.edge e) := by
  intro z hz
  obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hz
  exact (C.trimRoute δ hδ hδmax e).segment_subset i hi

theorem support_outside (δ : ℝ) (hδ : 0<δ) (hδmax : δ≤4*C.radius)
    (v : V) (e : E) {z : ℂ} (hz : z∈C.support δ hδ hδmax e) :
    δ≤dist z (D.vertex v) := by
  obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hz
  exact C.trimRoute_segment_outside δ hδ hδmax v e i hi

/-- Different source edges have genuinely disjoint compact corridors. -/
theorem supports_disjoint (δ : ℝ) (hδ : 0<δ) (hδmax : δ≤4*C.radius) :
    Pairwise (fun e f => Disjoint (C.support δ hδ hδmax e) (C.support δ hδ hδmax f)) := by
  intro e f hef
  apply Set.disjoint_left.mpr
  intro z hze hzf
  obtain ⟨v,hv⟩ := D.common_edge_point_vertex hef
    (C.support_subset_old δ hδ hδmax e hze) (C.support_subset_old δ hδ hδmax f hzf)
  have hh := C.support_outside δ hδ hδmax v e hze
  rw [← hv,dist_self] at hh
  exact (not_le_of_gt hδ) hh

/-- Primitive vertex disks fit strictly inside the unit disk, with room to
spare, whenever the normalized primitive center has norm at most one half. -/
theorem vertex_disk_inside {v : V} (hv : ‖D.vertex v‖≤1/2)
    {z : ℂ} (hz : z∈closedBall (D.vertex v) (4*C.radius)) : ‖z‖<1 := by
  have hz' : dist z (D.vertex v)≤4*C.radius := hz
  have hn : ‖z‖≤dist z (D.vertex v)+‖D.vertex v‖ := by
    simpa only [dist_eq_norm,add_comm] using norm_le_insert' z (D.vertex v)
  linarith [C.small]

/-- All central support points are genuine interior points of the old edge. -/
theorem support_inside_disk (hint : ∀ e t, 0<t → t<1 → ‖D.edge e t‖<1)
    (δ : ℝ) (hδ : 0<δ) (hδmax : δ≤4*C.radius) (e : E)
    {z : ℂ} (hz : z∈C.support δ hδ hδmax e) : ‖z‖<1 := by
  obtain ⟨t,ht⟩ := C.support_subset_old δ hδ hδmax e hz
  have ht0 : t≠0 := by
    intro hh
    subst t
    have hh := C.support_outside δ hδ hδmax (G.left e) e hz
    rw [← ht,D.edge_left,dist_self] at hh
    exact (not_le_of_gt hδ) hh
  have ht1 : t≠1 := by
    intro hh
    subst t
    have hh := C.support_outside δ hδ hδmax (G.right e) e hz
    rw [← ht,D.edge_right,dist_self] at hh
    exact (not_le_of_gt hδ) hh
  rw [← ht]
  exact hint e t (lt_of_le_of_ne t.2.1 ht0.symm) (lt_of_le_of_ne t.2.2 ht1)

/-- The compact corridors admit disjoint open neighborhoods staying in the
unit disk and outside every smaller closed vertex collar. No carrier existence
or no-reentry hypothesis is assumed. -/
theorem open_carriers [Finite V] [Finite E]
    (hint : ∀ e t, 0<t → t<1 → ‖D.edge e t‖<1)
    (δ : ℝ) (hδ : 0<δ) (hδmax : δ≤4*C.radius) (γ : ℝ) (hγ : γ<δ) :
    ∃ U : E → Set ℂ, (∀ e, IsOpen (U e)) ∧
      (∀ e, C.support δ hδ hδmax e ⊆ U e) ∧
      Pairwise (fun e f => Disjoint (U e) (U f)) ∧
      (∀ e z, z∈U e → ‖z‖<1 ∧ ∀ v, γ<dist z (D.vertex v)) := by
  let O : E → Set ℂ := fun _ => {z | ‖z‖<1} ∩ ⋂ v, {z | γ<dist z (D.vertex v)}
  have hO : ∀ e, IsOpen (O e) := fun _ =>
    (isOpen_lt continuous_norm continuous_const).inter
      (isOpen_iInter_of_finite fun _ => isOpen_lt continuous_const (continuous_id.dist continuous_const))
  have hSO : ∀ e, C.support δ hδ hδmax e ⊆ O e := by
    intro e z hz
    exact ⟨C.support_inside_disk hint δ hδ hδmax e hz,
      Set.mem_iInter.mpr fun v => hγ.trans_le (C.support_outside δ hδ hδmax v e hz)⟩
  obtain ⟨U,hU,hSU,hUO,hd⟩ := finite_compact_disjoint_open_neighborhoods
    (C.support δ hδ hδmax) O (C.support_compact δ hδ hδmax)
    (C.supports_disjoint δ hδ hδmax) hO hSO
  exact ⟨U,hU,hSU,hd,fun e z hz => ⟨(hUO e hz).1,fun v => Set.mem_iInter.mp (hUO e hz).2 v⟩⟩

/-- Realize all derived corridors as actual simple polygonal paths with their
exact finite segment supports. -/
theorem exists_paths (δ : ℝ) (hδ : 0<δ) (hδmax : δ≤4*C.radius) :
    ∃ p : ∀ e, Path ((R e).radialSourceCut δ) ((R e).radialTargetCut δ),
      (∀ e, Function.Injective (p e) ∧ IsPolygonalPath (p e) ∧
        Set.range (p e)=C.support δ hδ hδmax e) ∧
      Pairwise (fun e f => Disjoint (Set.range (p e)) (Set.range (p f))) := by
  have hex e := exists_injective_polygonal_path_of_indexed
    (C.trimRoute δ hδ hδmax e).positive (C.trimRoute δ hδ hδmax e).vertex
    (C.trimRoute δ hδ hδmax e).nonzero (C.trimRoute δ hδ hδmax e).adjacent
    (C.trimRoute δ hδ hδmax e).nonadjacent
  have hex' : ∀ e, ∃ p : Path ((R e).radialSourceCut δ) ((R e).radialTargetCut δ),
      Function.Injective p ∧ IsPolygonalPath p ∧ Set.range p=C.support δ hδ hδmax e := by
    intro e
    obtain ⟨p,hp,hpoly,hrange⟩ := hex e
    refine ⟨p.cast (C.trimRoute δ hδ hδmax e).source.symm
      (C.trimRoute δ hδ hδmax e).target.symm,hp,
      polygonalPath_cast hpoly _ _,hrange⟩
  choose p hp using hex'
  refine ⟨p,hp,?_⟩
  intro e f hef
  rw [(hp e).2.2,(hp f).2.2]
  exact C.supports_disjoint δ hδ hδmax hef

/-- The only contacts between a central corridor and a vertex's exact closed
collar are its designated cut endpoints, when that vertex is incident. -/
theorem support_closedBall_contact (δ : ℝ) (hδ : 0<δ) (hδmax : δ≤4*C.radius)
    (v : V) (e : E) :
    C.support δ hδ hδmax e ∩ closedBall (D.vertex v) δ ⊆
      {z | (G.left e=v ∧ z=(R e).radialSourceCut δ) ∨
        (G.right e=v ∧ z=(R e).radialTargetCut δ)} := by
  intro z hz
  obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hz.1
  by_cases hinc : R.EndIncident v e i
  · rcases hinc with ⟨hv,hii⟩ | ⟨hv,hii⟩
    · have hie : i=(R e).firstEdge := Fin.ext hii
      subst i
      have hc := (R e).trimAtRadius_first_segment_closedBall_contact δ hδ
        (C.cut_first_bound hδmax e) (C.cut_last_bound hδmax e)
        ⟨hi,by simpa only [hv] using hz.2⟩
      exact Or.inl ⟨hv,hc⟩
    · have hie : i=(R e).lastEdge := Fin.ext (by simp only [IndexedSimplePolygonalRoute.lastEdge_val]; omega)
      subst i
      have hc := (R e).trimAtRadius_last_segment_closedBall_contact δ hδ
        (C.cut_first_bound hδmax e) (C.cut_last_bound hδmax e)
        ⟨hi,by simpa only [hv] using hz.2⟩
      exact Or.inr ⟨hv,hc⟩
  · have hzo := (R e).trimAtRadius_segment_subset δ hδ
      (C.cut_first_bound hδmax e) (C.cut_last_bound hδmax e) i hi
    have hsep := C.separation v e i hinc z hzo
    have hdist : dist z (D.vertex v)≤δ := hz.2
    exact (not_lt_of_ge (hdist.trans hδmax) hsep).elim

theorem support_source_closedBall_contact (δ : ℝ) (hδ : 0<δ) (hδmax : δ≤4*C.radius)
    (e : E) : C.support δ hδ hδmax e ∩ closedBall (D.vertex (G.left e)) δ ⊆
      {(R e).radialSourceCut δ} := by
  intro z hz
  rcases C.support_closedBall_contact δ hδ hδmax (G.left e) e hz with hz | hz
  · exact hz.2
  · exact (G.loopless e hz.1.symm).elim

theorem support_target_closedBall_contact (δ : ℝ) (hδ : 0<δ) (hδmax : δ≤4*C.radius)
    (e : E) : C.support δ hδ hδmax e ∩ closedBall (D.vertex (G.right e)) δ ⊆
      {(R e).radialTargetCut δ} := by
  intro z hz
  rcases C.support_closedBall_contact δ hδ hδmax (G.right e) e hz with hz | hz
  · exact (G.loopless e hz.1).elim
  · exact hz.2

end IndexedRoutes.Collars
end PlanarDrawing
end
end MatchgateWidth
