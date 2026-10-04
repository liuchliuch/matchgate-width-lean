import MatchgateWidth.OrderedAllLeftGadget
import MatchgateWidth.DiskExteriorAccess
import MatchgateWidth.PolygonalPathRealization

/-! # Same-graph boundary collars for ordered all-left gadgets

Each degree-one boundary terminal is moved radially from the unit circle to
radius two. Its original incident arc is concatenated with that radial segment.
Rescaling by one half restores the unit disk and puts all primitive vertices
strictly inside it. No vertices, edges, incidences, or marked orders are changed.
-/
namespace MatchgateWidth
noncomputable section
open Set

namespace PlanarDrawing
variable {V E : Type*} {G : WeightedGraph V E ℂ} {s : ℕ} {ext : Fin s → V}

/-- Any occurrence of a vertex on an edge is one of its two endpoints. -/
theorem edge_eq_vertex_iff (D : PlanarDrawing G ext) (e : E)
    (t : unitInterval) (v : V) :
    D.edge e t = D.vertex v ↔
      (t = 0 ∧ G.left e = v) ∨ (t = 1 ∧ G.right e = v) := by
  constructor
  · intro h
    by_cases h0 : t = 0
    · subst t
      exact Or.inl ⟨rfl,D.vertex_injective ((D.edge_left e).symm.trans h)⟩
    by_cases h1 : t = 1
    · subst t
      exact Or.inr ⟨rfl,D.vertex_injective ((D.edge_right e).symm.trans h)⟩
    exact (D.interior_avoids_vertices e t (lt_of_le_of_ne t.2.1 (Ne.symm h0))
      (lt_of_le_of_ne t.2.2 h1) v h).elim
  · rintro (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩)
    · exact D.edge_left e
    · exact D.edge_right e

/-- The exterior radial segment is simple. -/
theorem radialAccess_injective (D : PlanarDrawing G ext) (p : Fin s) :
    Function.Injective (D.radialAccess p) := by
  intro t u h
  have hn := congrArg norm h
  rw [D.norm_radialAccess,D.norm_radialAccess] at hn
  exact Subtype.ext (by linarith)

end PlanarDrawing

namespace AllLeftGadget
variable {S : LabelledShape} {a b c n : ℕ} {I : AllLeftGadget S a b c n}
namespace OrderedPlanar
variable (P : I.OrderedPlanar)

/-- Degree one makes the old boundary point unique to its own edge. -/
theorem edge_eq_boundary_iff (e : Fin c ⊕ Fin n) (t : unitInterval) (p : Fin n) :
    P.drawing.edge e t = P.drawing.vertex (Sum.inr p) ↔ e = Sum.inr p ∧ t = 1 := by
  rw [P.drawing.edge_eq_vertex_iff]
  cases e <;> simp [AllLeftGadget.graph, and_comm]

/-- The unscaled moved vertex placement. -/
def extendedVertex : ((Fin a ⊕ Fin b) ⊕ Fin n) → ℂ
  | Sum.inl v => P.drawing.vertex (Sum.inl v)
  | Sum.inr p => 2 * P.drawing.vertex (Sum.inr p)

/-- The actual concatenated boundary arc before rescaling. -/
def extendedBoundaryPath (p : Fin n) :
    Path (P.drawing.vertex (I.graph.left (Sum.inr p)))
      (2 * P.drawing.vertex (Sum.inr p)) :=
  (P.drawing.edgePath (Sum.inr p)).trans
    ((P.drawing.radialAccess p).cast rfl (by rw [P.drawing.external_vertex]))

@[simp] theorem extendedBoundaryPath_range (p : Fin n) :
    Set.range (P.extendedBoundaryPath p) =
      Set.range (P.drawing.edge (Sum.inr p)) ∪ Set.range (P.drawing.radialAccess p) := by
  rw [extendedBoundaryPath,Path.trans_range]
  rfl

theorem extendedBoundaryPath_injective (p : Fin n) :
    Function.Injective (P.extendedBoundaryPath p) := by
  apply Path.injective_trans_of_inter (P.drawing.edge_injective _) (P.drawing.radialAccess_injective p)
  rintro z ⟨⟨t,rfl⟩,⟨u,hu⟩⟩
  have hn := congrArg norm hu
  change ‖P.drawing.radialAccess p u‖ = ‖P.drawing.edge (Sum.inr p) t‖ at hn
  rw [P.drawing.norm_radialAccess] at hn
  have hu0 : u = 0 := Subtype.ext (by change (u : ℝ) = 0; linarith [P.drawing.edge_in_disk (Sum.inr p) t,u.2.1])
  subst u
  simpa [PlanarDrawing.edgePath] using hu.symm

/-- Original internal arcs and extended dangling arcs, on exactly the same edges. -/
def extendedEdge : (Fin c ⊕ Fin n) → unitInterval → ℂ
  | Sum.inl e => P.drawing.edge (Sum.inl e)
  | Sum.inr p => P.extendedBoundaryPath p

@[simp] theorem extendedEdge_left (e : Fin c ⊕ Fin n) :
    P.extendedEdge e 0 = P.extendedVertex (I.graph.left e) := by
  cases e with
  | inl e => exact P.drawing.edge_left _
  | inr p => exact (P.extendedBoundaryPath p).source

@[simp] theorem extendedEdge_right (e : Fin c ⊕ Fin n) :
    P.extendedEdge e 1 = P.extendedVertex (I.graph.right e) := by
  cases e with
  | inl e => exact P.drawing.edge_right _
  | inr p => exact (P.extendedBoundaryPath p).target

theorem extendedEdge_continuous (e : Fin c ⊕ Fin n) : Continuous (P.extendedEdge e) := by
  cases e with
  | inl e => exact P.drawing.edge_continuous _
  | inr p => exact (P.extendedBoundaryPath p).continuous

theorem extendedEdge_injective (e : Fin c ⊕ Fin n) : Function.Injective (P.extendedEdge e) := by
  cases e with
  | inl e => exact P.drawing.edge_injective _
  | inr p => exact P.extendedBoundaryPath_injective p

/-- Every new point comes from an old edge, or its own boundary extension. -/
theorem extendedEdge_cases (e : Fin c ⊕ Fin n) (t : unitInterval) :
    (∃ u, P.extendedEdge e t = P.drawing.edge e u) ∨
    ∃ p u, e = Sum.inr p ∧ P.extendedEdge e t = P.drawing.radialAccess p u := by
  cases e with
  | inl e => exact Or.inl ⟨t,rfl⟩
  | inr p =>
    have h : P.extendedEdge (Sum.inr p) t ∈ Set.range (P.extendedBoundaryPath p) := ⟨t,rfl⟩
    rw [P.extendedBoundaryPath_range] at h
    rcases h with ⟨u,hu⟩ | ⟨u,hu⟩
    · exact Or.inl ⟨u,hu.symm⟩
    · exact Or.inr ⟨p,u,rfl,hu.symm⟩

/-- A radial extension meets an original edge only at its own old terminal. -/
theorem radialAccess_eq_edge_iff (p : Fin n) (u : unitInterval)
    (e : Fin c ⊕ Fin n) (t : unitInterval) :
    P.drawing.radialAccess p u = P.drawing.edge e t ↔
      u = 0 ∧ e = Sum.inr p ∧ t = 1 := by
  constructor
  · intro h
    have hn := congrArg norm h
    rw [P.drawing.norm_radialAccess] at hn
    have hu : u = 0 := Subtype.ext (by
      change (u : ℝ) = 0
      linarith [P.drawing.edge_in_disk e t,u.2.1])
    subst u
    refine ⟨rfl,?_⟩
    exact (P.edge_eq_boundary_iff e t p).mp (by simpa using h.symm)
  · rintro ⟨rfl,rfl,rfl⟩
    simpa [AllLeftGadget.graph] using (P.drawing.edge_right (Sum.inr p)).symm

/-- Radial extensions avoid every primitive vertex, even if the original
primitive vertex happened to lie on the unit circle. -/
theorem radialAccess_ne_primitive (p : Fin n) (t : unitInterval)
    (v : Fin a ⊕ Fin b) :
    P.drawing.radialAccess p t ≠ P.drawing.vertex (Sum.inl v) := by
  intro h
  have hn := congrArg norm h
  rw [P.drawing.norm_radialAccess] at hn
  have ht : t = 0 := Subtype.ext (by
    change (t : ℝ) = 0
    linarith [P.drawing.vertex_in_disk (Sum.inl v),t.2.1])
  subst t
  have he : (Sum.inr p : (Fin a ⊕ Fin b) ⊕ Fin n) = Sum.inl v :=
    P.drawing.vertex_injective (by simpa using h)
  exact Sum.inr_ne_inl he

@[simp] theorem norm_extendedVertex_boundary (p : Fin n) :
    ‖P.extendedVertex (Sum.inr p)‖ = 2 := by
  simp [extendedVertex,P.drawing.external_on_circle]

theorem extendedVertex_injective : Function.Injective P.extendedVertex := by
  intro v w h
  cases v with
  | inl v =>
    cases w with
    | inl w => exact P.drawing.vertex_injective h
    | inr p =>
      have hn := congrArg norm h
      rw [P.norm_extendedVertex_boundary] at hn
      exact (by have hb := P.drawing.vertex_in_disk (Sum.inl v); change ‖P.drawing.vertex (Sum.inl v)‖ = 2 at hn; linarith : False).elim
  | inr p =>
    cases w with
    | inl w =>
      have hn := congrArg norm h
      rw [P.norm_extendedVertex_boundary] at hn
      exact (by have hb := P.drawing.vertex_in_disk (Sum.inl w); change 2 = ‖P.drawing.vertex (Sum.inl w)‖ at hn; linarith : False).elim
    | inr q => exact P.drawing.vertex_injective (mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0) h)

theorem extendedVertex_bound (v : (Fin a ⊕ Fin b) ⊕ Fin n) :
    ‖P.extendedVertex v‖ ≤ 2 := by
  cases v with
  | inl v => exact (P.drawing.vertex_in_disk _).trans (by norm_num)
  | inr p => exact (P.norm_extendedVertex_boundary p).le

theorem extendedEdge_bound (e : Fin c ⊕ Fin n) (t : unitInterval) :
    ‖P.extendedEdge e t‖ ≤ 2 := by
  rcases P.extendedEdge_cases e t with ⟨u,hu⟩ | ⟨p,u,he,hu⟩
  · rw [hu]
    exact (P.drawing.edge_in_disk e u).trans (by norm_num)
  · rw [hu,P.drawing.norm_radialAccess]
    linarith [u.2.2]

/-- Every vertex met by an extended edge is still one of its two endpoints. -/
theorem extendedEdge_eq_vertex_incident (e : Fin c ⊕ Fin n) (t : unitInterval)
    (v : (Fin a ⊕ Fin b) ⊕ Fin n)
    (h : P.extendedEdge e t = P.extendedVertex v) :
    I.graph.left e = v ∨ I.graph.right e = v := by
  rcases P.extendedEdge_cases e t with ⟨u,hu⟩ | ⟨p,u,rfl,hu⟩
  · cases v with
    | inl v =>
      have hv : P.drawing.edge e u = P.drawing.vertex (Sum.inl v) := hu.symm.trans h
      rcases (P.drawing.edge_eq_vertex_iff e u _).mp hv with ⟨_,hh⟩ | ⟨_,hh⟩
      · exact Or.inl hh
      · exact Or.inr hh
    | inr p =>
      have hn := congrArg norm (hu.symm.trans h)
      rw [P.norm_extendedVertex_boundary] at hn
      have hb := P.drawing.edge_in_disk e u
      exact (by linarith : False).elim
  · cases v with
    | inl v => exact (P.radialAccess_ne_primitive p u v (hu.symm.trans h)).elim
    | inr q =>
      have hn := congrArg norm (hu.symm.trans h)
      rw [P.drawing.norm_radialAccess,P.norm_extendedVertex_boundary] at hn
      have hu1 : u = 1 := Subtype.ext (by change (u : ℝ) = 1; linarith)
      subst u
      have hq : (Sum.inr p : (Fin a ⊕ Fin b) ⊕ Fin n) = Sum.inr q :=
        P.drawing.vertex_injective (mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0)
          (by simpa [extendedVertex,P.drawing.external_vertex] using hu.symm.trans h))
      exact Or.inr hq

theorem extendedEdge_interior_avoids_vertices (e : Fin c ⊕ Fin n)
    (t : unitInterval) (ht0 : 0 < t) (ht1 : t < 1)
    (v : (Fin a ⊕ Fin b) ⊕ Fin n) :
    P.extendedEdge e t ≠ P.extendedVertex v := by
  intro h
  rcases P.extendedEdge_eq_vertex_incident e t v h with hv | hv
  · have ht := P.extendedEdge_injective e (h.trans (hv ▸ (P.extendedEdge_left e).symm))
    exact (ne_of_gt ht0) ht
  · have ht := P.extendedEdge_injective e (h.trans (hv ▸ (P.extendedEdge_right e).symm))
    exact (ne_of_lt ht1) ht

/-- The new dangling portions are disjoint from every other new or old arc. -/
theorem extendedEdge_interiors_disjoint (e f : Fin c ⊕ Fin n) (hef : e ≠ f)
    (t u : unitInterval) (ht0 : 0 < t) (ht1 : t < 1) (_hu0 : 0 < u) (_hu1 : u < 1) :
    P.extendedEdge e t ≠ P.extendedEdge f u := by
  intro h
  rcases P.extendedEdge_cases e t with ⟨s,hs⟩ | ⟨p,s,he,hs⟩
  · rcases P.extendedEdge_cases f u with ⟨r,hr⟩ | ⟨q,r,hf,hr⟩
    · have heq : P.drawing.edge e s = P.drawing.edge f r := hs.symm.trans (h.trans hr)
      have hno (v : (Fin a ⊕ Fin b) ⊕ Fin n)
          (hv : P.drawing.edge e s = P.drawing.vertex v) : False := by
        cases v with
        | inl v => exact P.extendedEdge_interior_avoids_vertices e t ht0 ht1 (Sum.inl v) (hs.trans hv)
        | inr p =>
          have he := (P.edge_eq_boundary_iff e s p).mp hv
          have hf := (P.edge_eq_boundary_iff f r p).mp (heq.symm.trans hv)
          exact hef (he.1.trans hf.1.symm)
      by_cases hs0 : s = 0
      · exact hno _ (hs0 ▸ P.drawing.edge_left e)
      by_cases hs1 : s = 1
      · exact hno _ (hs1 ▸ P.drawing.edge_right e)
      by_cases hr0 : r = 0
      · exact hno _ (heq.trans (hr0 ▸ P.drawing.edge_left f))
      by_cases hr1 : r = 1
      · exact hno _ (heq.trans (hr1 ▸ P.drawing.edge_right f))
      exact P.drawing.interiors_disjoint e f hef s r
        (lt_of_le_of_ne s.2.1 (Ne.symm hs0)) (lt_of_le_of_ne s.2.2 hs1)
        (lt_of_le_of_ne r.2.1 (Ne.symm hr0)) (lt_of_le_of_ne r.2.2 hr1) heq
    · have heq := hr.symm.trans (h.symm.trans hs)
      exact hef (((P.radialAccess_eq_edge_iff q r e s).mp heq).2.1.trans hf.symm)
  · rcases P.extendedEdge_cases f u with ⟨r,hr⟩ | ⟨q,r,hf,hr⟩
    · have heq := hs.symm.trans (h.trans hr)
      exact hef (he.trans ((P.radialAccess_eq_edge_iff p s f r).mp heq).2.1.symm)
    · have hpq : p ≠ q := fun hpq => hef (he.trans (hpq ▸ hf.symm))
      exact Set.disjoint_left.mp (P.drawing.radialAccess_disjoint hpq)
        ⟨s,rfl⟩ ⟨r,hr.symm.trans (h.symm.trans hs)⟩

/-- The normalized drawing has exactly the original abstract graph and exact
original marked external angles. -/
def boundaryCollarDrawing : PlanarDrawing I.graph
    (Sum.inr : Fin n → (Fin a ⊕ Fin b) ⊕ Fin n) where
  vertex := fun v => (1 / 2 : ℂ) * P.extendedVertex v
  vertex_injective := fun _ _ h => P.extendedVertex_injective
    (mul_left_cancel₀ (by norm_num : (1 / 2 : ℂ) ≠ 0) h)
  vertex_in_disk := by
    intro v
    rw [norm_mul]
    norm_num
    linarith [P.extendedVertex_bound v]
  edge := fun e t => (1 / 2 : ℂ) * P.extendedEdge e t
  edge_continuous := fun e => continuous_const.mul (P.extendedEdge_continuous e)
  edge_injective := fun e _ _ h => P.extendedEdge_injective e
    (mul_left_cancel₀ (by norm_num : (1 / 2 : ℂ) ≠ 0) h)
  edge_left := fun e => congrArg ((1 / 2 : ℂ) * ·) (P.extendedEdge_left e)
  edge_right := fun e => congrArg ((1 / 2 : ℂ) * ·) (P.extendedEdge_right e)
  edge_in_disk := by
    intro e t
    rw [norm_mul]
    norm_num
    linarith [P.extendedEdge_bound e t]
  interior_avoids_vertices := fun e t h0 h1 v h =>
    P.extendedEdge_interior_avoids_vertices e t h0 h1 v
      (mul_left_cancel₀ (by norm_num : (1 / 2 : ℂ) ≠ 0) h)
  interiors_disjoint := fun e f hef t u ht0 ht1 hu0 hu1 h =>
    P.extendedEdge_interiors_disjoint e f hef t u ht0 ht1 hu0 hu1
      (mul_left_cancel₀ (by norm_num : (1 / 2 : ℂ) ≠ 0) h)
  external_injective := Sum.inr_injective
  angle := P.drawing.angle
  angle_pos := P.drawing.angle_pos
  angle_lt_one := P.drawing.angle_lt_one
  angle_strictMono := P.drawing.angle_strictMono
  external_vertex := by
    intro p
    change (1 / 2 : ℂ) * (2 * P.drawing.vertex (Sum.inr p)) = _
    rw [← mul_assoc]
    norm_num
    exact P.drawing.external_vertex p

@[simp] theorem boundaryCollarDrawing_angle (p : Fin n) :
    P.boundaryCollarDrawing.angle p = P.drawing.angle p := rfl

@[simp] theorem boundaryCollarDrawing_primitive (v : Fin a ⊕ Fin b) :
    P.boundaryCollarDrawing.vertex (Sum.inl v) =
      (1 / 2 : ℂ) * P.drawing.vertex (Sum.inl v) := rfl

/-- All primitive vertices are uniformly inside the half-radius disk. -/
theorem boundaryCollarDrawing_primitive_bound (v : Fin a ⊕ Fin b) :
    ‖P.boundaryCollarDrawing.vertex (Sum.inl v)‖ ≤ 1 / 2 := by
  rw [P.boundaryCollarDrawing_primitive,norm_mul]
  norm_num
  linarith [P.drawing.vertex_in_disk (Sum.inl v)]

theorem boundaryCollarDrawing_primitive_interior (v : Fin a ⊕ Fin b) :
    ‖P.boundaryCollarDrawing.vertex (Sum.inl v)‖ < 1 :=
  (P.boundaryCollarDrawing_primitive_bound v).trans_lt (by norm_num)

/-- An internal edge is simply rescaled, without reparametrization. -/
@[simp] theorem boundaryCollarDrawing_internal (e : Fin c) (t : unitInterval) :
    P.boundaryCollarDrawing.edge (Sum.inl e) t =
      (1 / 2 : ℂ) * P.drawing.edge (Sum.inl e) t := rfl

/-- The first half of a dangling edge follows its original arc at double speed. -/
theorem extendedEdge_boundary_initial (p : Fin n) (t : unitInterval)
    (ht : (t : ℝ) ≤ 1 / 2) :
    P.extendedEdge (Sum.inr p) t = P.drawing.edge (Sum.inr p)
      ⟨2 * (t : ℝ),by constructor <;> linarith [t.2.1]⟩ := by
  change (P.extendedBoundaryPath p) t = _
  rw [extendedBoundaryPath,Path.trans_apply,dite_eq_left ht]
  rfl

/-- Its second half is an exact radial outer collar. -/
theorem boundaryCollarDrawing_radial_tail (p : Fin n) (t : unitInterval)
    (ht : 1 / 2 ≤ (t : ℝ)) :
    P.boundaryCollarDrawing.edge (Sum.inr p) t =
      ((t : ℝ) : ℂ) * boundaryPoint (P.drawing.angle p) := by
  change (1 / 2 : ℂ) * P.extendedBoundaryPath p t = _
  rw [extendedBoundaryPath,Path.trans_apply]
  split_ifs with hh
  · have hteq : (t : ℝ) = 1 / 2 := le_antisymm hh ht
    have h1 : (⟨2 * (t : ℝ),by constructor <;> linarith [t.2.1]⟩ : unitInterval) = 1 :=
      Subtype.ext (by change 2 * (t : ℝ) = 1; linarith)
    rw [h1]
    change (1 / 2 : ℂ) * P.drawing.edge (Sum.inr p) 1 = _
    rw [P.drawing.edge_right]
    change (1 / 2 : ℂ) * P.drawing.vertex (Sum.inr p) = _
    rw [P.drawing.external_vertex,hteq]
    norm_num
  · change (1 / 2 : ℂ) *
        ((((1 + (2 * (t : ℝ) - 1)) : ℝ) : ℂ) * P.drawing.vertex (Sum.inr p)) = _
    rw [P.drawing.external_vertex]
    push_cast
    ring

/-- Every internal arc remains in the half-radius disk. -/
theorem boundaryCollarDrawing_internal_bound (e : Fin c) (t : unitInterval) :
    ‖P.boundaryCollarDrawing.edge (Sum.inl e) t‖ ≤ 1 / 2 := by
  rw [P.boundaryCollarDrawing_internal,norm_mul]
  norm_num
  linarith [P.drawing.edge_in_disk (Sum.inl e) t]

/-- The original part of every boundary edge remains in the half-radius disk. -/
theorem boundaryCollarDrawing_initial_bound (p : Fin n) (t : unitInterval)
    (ht : (t : ℝ) ≤ 1 / 2) :
    ‖P.boundaryCollarDrawing.edge (Sum.inr p) t‖ ≤ 1 / 2 := by
  change ‖(1 / 2 : ℂ) * P.extendedEdge (Sum.inr p) t‖ ≤ 1 / 2
  rw [P.extendedEdge_boundary_initial p t ht,norm_mul]
  norm_num
  linarith [P.drawing.edge_in_disk (Sum.inr p)
    ⟨2 * (t : ℝ),by constructor <;> linarith [t.2.1]⟩]

/-- No edge interior touches the outer circle after collar normalization. -/
theorem boundaryCollarDrawing_edge_interior (e : Fin c ⊕ Fin n)
    (t : unitInterval) (_ht0 : 0 < t) (ht1 : t < 1) :
    ‖P.boundaryCollarDrawing.edge e t‖ < 1 := by
  cases e with
  | inl e => exact (P.boundaryCollarDrawing_internal_bound e t).trans_lt (by norm_num)
  | inr p =>
    by_cases ht : (t : ℝ) ≤ 1 / 2
    · exact (P.boundaryCollarDrawing_initial_bound p t ht).trans_lt (by norm_num)
    · rw [P.boundaryCollarDrawing_radial_tail p t (le_of_not_ge ht)]
      simpa [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg t.2.1] using ht1

/-- Boundary terminals have an explicit inward radial germ on the reversed arc. -/
theorem boundaryCollarDrawing_boundary_reverse_germ (p : Fin n) (t : unitInterval)
    (ht : (t : ℝ) ≤ 1 / 2) :
    P.boundaryCollarDrawing.edge (Sum.inr p) (LabelledInstance.reverseParameter t) =
      boundaryPoint (P.drawing.angle p) + (t : ℝ) • (-boundaryPoint (P.drawing.angle p)) := by
  rw [P.boundaryCollarDrawing_radial_tail p (LabelledInstance.reverseParameter t)
    (by change 1 / 2 ≤ 1 - (t : ℝ); linarith)]
  simp only [LabelledInstance.reverseParameter,Complex.real_smul]
  push_cast
  ring

/-- Local left speeds compensate precisely for the doubled parametrization of
boundary edges. The marked square-angle coordinates themselves are unchanged. -/
def boundaryCollarLeftOrder (v : Fin a) : LabelledInstance.PositivePortOrder
    (P.boundaryCollarDrawing.vertex (Sum.inl (Sum.inl v)))
    (fun i t => P.boundaryCollarDrawing.edge (I.leftIncidence ⟨v,i⟩) t) where
  rotation := (1 / 2 : ℂ) * (P.leftOrder v).rotation
  rotation_ne_zero := mul_ne_zero (by norm_num) (P.leftOrder v).rotation_ne_zero
  time := (P.leftOrder v).time
  time_strictMono := (P.leftOrder v).time_strictMono
  time_range := (P.leftOrder v).time_range
  speed := fun i => Sum.elim (fun _ => (P.leftOrder v).speed i)
    (fun _ => 2 * (P.leftOrder v).speed i) (I.leftIncidence ⟨v,i⟩)
  speed_pos := by
    intro i
    cases I.leftIncidence ⟨v,i⟩ with
    | inl e => exact (P.leftOrder v).speed_pos i
    | inr p => exact mul_pos (by norm_num) ((P.leftOrder v).speed_pos i)
  radius := ⟨((P.leftOrder v).radius : ℝ) / 2, by
    constructor <;> linarith [(P.leftOrder v).radius.2.1,(P.leftOrder v).radius.2.2]⟩
  radius_pos := by
    change 0 < ((P.leftOrder v).radius : ℝ) / 2
    exact div_pos (P.leftOrder v).radius_pos (by norm_num)
  germ := by
    intro i t ht
    change (t : ℝ) ≤ ((P.leftOrder v).radius : ℝ) / 2 at ht
    have htold : t ≤ (P.leftOrder v).radius := by
      change (t : ℝ) ≤ ((P.leftOrder v).radius : ℝ)
      linarith [(P.leftOrder v).radius.2.1]
    have hthalf : (t : ℝ) ≤ 1 / 2 := by linarith [(P.leftOrder v).radius.2.2]
    cases he : I.leftIncidence ⟨v,i⟩ with
    | inl e =>
      have hg := (P.leftOrder v).germ i t htold
      rw [he] at hg
      rw [P.boundaryCollarDrawing_internal,hg,P.boundaryCollarDrawing_primitive]
      simp only [Sum.elim_inl,Complex.real_smul]
      ring
    | inr p =>
      let u : unitInterval := ⟨2 * (t : ℝ),by constructor <;> linarith [t.2.1]⟩
      have hu : u ≤ (P.leftOrder v).radius := by
        change 2 * (t : ℝ) ≤ ((P.leftOrder v).radius : ℝ)
        linarith
      have hg := (P.leftOrder v).germ i u hu
      rw [he] at hg
      change (1 / 2 : ℂ) * P.extendedEdge (Sum.inr p) t = _
      rw [P.extendedEdge_boundary_initial p t hthalf]
      change (1 / 2 : ℂ) * P.drawing.edge (Sum.inr p) u = _
      rw [hg,P.boundaryCollarDrawing_primitive]
      simp only [Sum.elim_inr,Complex.real_smul]
      dsimp [u]
      push_cast
      ring

/-- Right incidences are all internal, so their radial germs merely rescale. -/
def boundaryCollarRightOrder (v : Fin b) : LabelledInstance.PositivePortOrder
    (P.boundaryCollarDrawing.vertex (Sum.inl (Sum.inr v)))
    (fun i t => P.boundaryCollarDrawing.edge (Sum.inl (I.rightIncidence ⟨v,i⟩))
      (LabelledInstance.reverseParameter t)) where
  rotation := (1 / 2 : ℂ) * (P.rightOrder v).rotation
  rotation_ne_zero := mul_ne_zero (by norm_num) (P.rightOrder v).rotation_ne_zero
  time := (P.rightOrder v).time
  time_strictMono := (P.rightOrder v).time_strictMono
  time_range := (P.rightOrder v).time_range
  speed := (P.rightOrder v).speed
  speed_pos := (P.rightOrder v).speed_pos
  radius := (P.rightOrder v).radius
  radius_pos := (P.rightOrder v).radius_pos
  germ := by
    intro i t ht
    rw [P.boundaryCollarDrawing_internal,(P.rightOrder v).germ i t ht,
      P.boundaryCollarDrawing_primitive]
    simp only [Complex.real_smul]
    ring

/-- Actual collar normalization preserving every port index and marked order. -/
def boundaryCollarOrderedPlanar : I.OrderedPlanar where
  drawing := P.boundaryCollarDrawing
  leftOrder := P.boundaryCollarLeftOrder
  rightOrder := P.boundaryCollarRightOrder

@[simp] theorem boundaryCollarOrderedPlanar_left_time (v : Fin a) :
    (P.boundaryCollarOrderedPlanar.leftOrder v).time = (P.leftOrder v).time := rfl

@[simp] theorem boundaryCollarOrderedPlanar_right_time (v : Fin b) :
    (P.boundaryCollarOrderedPlanar.rightOrder v).time = (P.rightOrder v).time := rfl

/-- Extract the actual initial radial germ of each edge from its unique left
incidence, without changing the incidence index. -/
theorem edge_initial_germ (e : Fin c ⊕ Fin n) :
    ∃ τ : unitInterval, 0 < τ ∧ ∃ w : ℂ, ∀ t : unitInterval, t ≤ τ →
      P.drawing.edge e t = P.drawing.vertex (I.graph.left e) + (t : ℝ) • w := by
  let q := I.leftIncidence.symm e
  let O := P.leftOrder q.1
  refine ⟨O.radius,O.radius_pos,O.speed q.2 • (O.rotation * twoCenterSquare (O.time q.2)),?_⟩
  intro t ht
  have hg := O.germ q.2 t ht
  have he : I.leftIncidence ⟨q.1,q.2⟩ = e := I.leftIncidence.apply_symm_apply e
  rw [he] at hg
  exact hg

/-- Initial germs of the normalized drawing are genuine edge-by-edge data. -/
theorem boundaryCollarDrawing_initial_germ (e : Fin c ⊕ Fin n) :
    ∃ τ : unitInterval, 0 < τ ∧ ∃ w : ℂ, ∀ t : unitInterval, t ≤ τ →
      P.boundaryCollarDrawing.edge e t =
        P.boundaryCollarDrawing.vertex (I.graph.left e) + (t : ℝ) • w :=
  P.boundaryCollarOrderedPlanar.edge_initial_germ e

/-- Every reversed terminal arc has an actual positive radial germ, including
the newly straightened boundary ends. -/
theorem boundaryCollarDrawing_terminal_germ (e : Fin c ⊕ Fin n) :
    ∃ τ : unitInterval, 0 < τ ∧ ∃ w : ℂ, ∀ t : unitInterval, t ≤ τ →
      P.boundaryCollarDrawing.edge e (LabelledInstance.reverseParameter t) =
        P.boundaryCollarDrawing.vertex (I.graph.right e) + (t : ℝ) • w := by
  cases e with
  | inl e =>
    let q := I.rightIncidence.symm e
    let O := P.boundaryCollarOrderedPlanar.rightOrder q.1
    refine ⟨O.radius,O.radius_pos,O.speed q.2 • (O.rotation * twoCenterSquare (O.time q.2)),?_⟩
    intro t ht
    have hg := O.germ q.2 t ht
    have he : I.rightIncidence ⟨q.1,q.2⟩ = e := I.rightIncidence.apply_symm_apply e
    rw [he] at hg
    exact hg
  | inr p =>
    refine ⟨⟨1 / 2,by constructor <;> norm_num⟩,by change (0 : ℝ) < 1 / 2; norm_num,
      -boundaryPoint (P.drawing.angle p),?_⟩
    intro t ht
    change P.boundaryCollarDrawing.edge (Sum.inr p) (LabelledInstance.reverseParameter t) =
      P.boundaryCollarDrawing.vertex (Sum.inr p) + _
    rw [P.boundaryCollarDrawing.external_vertex]
    exact P.boundaryCollarDrawing_boundary_reverse_germ p t ht

/-- Every ordered all-left gadget has a genuine same-graph collar-normalized
drawing, with no extra existence or matchgate premise. -/
theorem exists_boundary_collar : ∃ Q : I.OrderedPlanar,
    (∀ v : Fin a ⊕ Fin b, ‖Q.drawing.vertex (Sum.inl v)‖ ≤ 1 / 2) ∧
    Q.drawing.angle = P.drawing.angle ∧
    (∀ v, (Q.leftOrder v).time = (P.leftOrder v).time) ∧
    (∀ v, (Q.rightOrder v).time = (P.rightOrder v).time) ∧
    (∀ p (t : unitInterval), 1 / 2 ≤ (t : ℝ) →
      Q.drawing.edge (Sum.inr p) t = ((t : ℝ) : ℂ) * boundaryPoint (Q.drawing.angle p)) := by
  exact ⟨P.boundaryCollarOrderedPlanar,P.boundaryCollarDrawing_primitive_bound,rfl,
    fun _ => rfl,fun _ => rfl,P.boundaryCollarDrawing_radial_tail⟩

end OrderedPlanar
end AllLeftGadget
end
end MatchgateWidth
