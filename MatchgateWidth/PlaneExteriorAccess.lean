import MatchgateWidth.DiskBoundaryNoncrossing

/-!
# Necessity for plane drawings with ordered exterior access

The original graph and its matching sum are unchanged. A crossing-free plane
drawing with disjoint access arcs to a surrounding circle has noncrossing
boundary endpoint paths, and hence satisfies all matchgate identities.

This is an explicit geometric witness interface. The existence of such access
arcs from an independent formal notion of ordered outer-face incidence is a
separate theorem and is not assumed or asserted here.
-/

namespace MatchgateWidth
noncomputable section
open Classical
open scoped symmDiff

/-- An ordinary crossing-free plane drawing by continuous simple edge arcs,
without a disk constraint or distinguished boundary vertices. -/
structure PlaneDrawing {V E : Type*} (G : WeightedGraph V E ℂ) where
  vertex : V → ℂ
  vertex_injective : Function.Injective vertex
  edge : E → unitInterval → ℂ
  edge_continuous : ∀ e, Continuous (edge e)
  edge_injective : ∀ e, Function.Injective (edge e)
  edge_left : ∀ e, edge e 0 = vertex (G.left e)
  edge_right : ∀ e, edge e 1 = vertex (G.right e)
  interior_avoids_vertices : ∀ e t, 0 < t → t < 1 → ∀ v, edge e t ≠ vertex v
  interiors_disjoint : ∀ e f, e ≠ f → ∀ t u,
    0 < t → t < 1 → 0 < u → u < 1 → edge e t ≠ edge f u

/-- Ordered access to a surrounding circle from the prescribed external
vertices. Access arcs are genuinely disjoint and meet the graph only at their
own initial endpoint. Their existence is data, not inferred from informal
outer-face terminology. -/
structure OrderedExteriorAccess {V E : Type*} {G : WeightedGraph V E ℂ}
    (P : PlaneDrawing G) {s : ℕ} (ext : Fin s → V) where
  external_injective : Function.Injective ext
  radius : ℝ
  radius_pos : 0 < radius
  vertex_bound : ∀ v, ‖P.vertex v‖ ≤ radius
  edge_bound : ∀ e t, ‖P.edge e t‖ ≤ radius
  angle : Fin s → ℝ
  angle_pos : ∀ i, 0 < angle i
  angle_lt_one : ∀ i, angle i < 1
  angle_strictMono : StrictMono angle
  access : ∀ i, Path (P.vertex (ext i)) ((radius : ℂ) * boundaryPoint (angle i))
  access_bound : ∀ i t, ‖access i t‖ ≤ radius
  access_disjoint : ∀ i j, i ≠ j → Disjoint (Set.range (access i)) (Set.range (access j))
  access_meets_edge_only_at_start : ∀ i t e u, access i t = P.edge e u → t = 0

namespace OrderedExteriorAccess
variable {V E : Type*} {G : WeightedGraph V E ℂ} {P : PlaneDrawing G}
    {s r : ℕ} {ext : Fin s → V}

/-- Uniform scaling by the inverse surrounding radius. -/
def scale (A : OrderedExteriorAccess P ext) (z : ℂ) : ℂ := (A.radius : ℂ)⁻¹ * z

theorem scale_injective (A : OrderedExteriorAccess P ext) : Function.Injective A.scale :=
  mul_right_injective₀ (inv_ne_zero (Complex.ofReal_ne_zero.mpr A.radius_pos.ne'))

theorem scale_continuous (A : OrderedExteriorAccess P ext) : Continuous A.scale :=
  continuous_const.mul continuous_id

theorem norm_scale_le_one (A : OrderedExteriorAccess P ext) {z : ℂ}
    (hz : ‖z‖ ≤ A.radius) : ‖A.scale z‖ ≤ 1 := by
  calc
    ‖A.scale z‖ = A.radius⁻¹ * ‖z‖ := by
      simp [scale, abs_of_pos A.radius_pos]
    _ ≤ A.radius⁻¹ * A.radius := mul_le_mul_of_nonneg_left hz (inv_nonneg.mpr A.radius_pos.le)
    _ = 1 := inv_mul_cancel₀ A.radius_pos.ne'

/-- The original graph scaled into the unit disk, temporarily with no external
vertices. This reuses the graph-path realization theorems without pretending
that the original external vertices themselves lie on the surrounding circle. -/
def graphDrawing (A : OrderedExteriorAccess P ext) :
    PlanarDrawing G (Fin.elim0 : Fin 0 → V) where
  vertex := fun v => A.scale (P.vertex v)
  vertex_injective := A.scale_injective.comp P.vertex_injective
  vertex_in_disk := fun v => A.norm_scale_le_one (A.vertex_bound v)
  edge := fun e t => A.scale (P.edge e t)
  edge_continuous := fun e => A.scale_continuous.comp (P.edge_continuous e)
  edge_injective := fun e => A.scale_injective.comp (P.edge_injective e)
  edge_left := fun e => congrArg A.scale (P.edge_left e)
  edge_right := fun e => congrArg A.scale (P.edge_right e)
  edge_in_disk := fun e t => A.norm_scale_le_one (A.edge_bound e t)
  interior_avoids_vertices := fun e t ht₀ ht₁ v h =>
    P.interior_avoids_vertices e t ht₀ ht₁ v (A.scale_injective h)
  interiors_disjoint := fun e f hef t u ht₀ ht₁ hu₀ hu₁ h =>
    P.interiors_disjoint e f hef t u ht₀ ht₁ hu₀ hu₁ (A.scale_injective h)
  external_injective := Function.injective_of_subsingleton _
  angle := Fin.elim0
  angle_pos := fun i => i.elim0
  angle_lt_one := fun i => i.elim0
  angle_strictMono := by intro i; exact i.elim0
  external_vertex := fun i => i.elim0

/-- The access path scaled to the unit circle. -/
def normalizedAccess (A : OrderedExteriorAccess P ext) (i : Fin s) :
    Path (A.graphDrawing.vertex (ext i)) (boundaryPoint (A.angle i)) :=
  ((A.access i).map A.scale_continuous).cast rfl (by
    change boundaryPoint (A.angle i) = (A.radius : ℂ)⁻¹ *
      ((A.radius : ℂ) * boundaryPoint (A.angle i))
    rw [← mul_assoc, inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr A.radius_pos.ne'), one_mul])

@[simp] theorem normalizedAccess_apply (A : OrderedExteriorAccess P ext) (i : Fin s)
    (t : unitInterval) : A.normalizedAccess i t = A.scale (A.access i t) := rfl

theorem normalizedAccess_in_disk (A : OrderedExteriorAccess P ext) (i : Fin s)
    (t : unitInterval) : ‖A.normalizedAccess i t‖ ≤ 1 :=
  A.norm_scale_le_one (A.access_bound i t)

theorem normalizedAccess_disjoint (A : OrderedExteriorAccess P ext) {i j : Fin s}
    (hij : i ≠ j) : Disjoint (Set.range (A.normalizedAccess i))
      (Set.range (A.normalizedAccess j)) := by
  apply Set.disjoint_left.mpr
  rintro z ⟨u, rfl⟩ ⟨v, hv⟩
  exact Set.disjoint_left.mp (A.access_disjoint i j hij) ⟨u, rfl⟩
    ⟨v, A.scale_injective hv⟩

/-- An access arc is disjoint from a graph path which omits its root vertex. -/
theorem pathSupport_disjoint_normalizedAccess (A : OrderedExteriorAccess P ext)
    (q : SimpleEdgePath G r) (i : Fin s) (hi : ext i ∉ q.vertexSet) :
    Disjoint (A.graphDrawing.pathSupport q) (Set.range (A.normalizedAccess i)) := by
  apply Set.disjoint_left.mpr
  rintro z ⟨e, he, u, hu⟩ ⟨t, ht⟩
  have heq : A.access i t = P.edge e u := A.scale_injective (ht.trans hu.symm)
  have ht₀ := A.access_meets_edge_only_at_start i t e u heq
  subst t
  rw [Path.source] at ht
  have hinc := A.graphDrawing.vertex_incident_of_mem_edge (hu.trans ht.symm)
  exact hi (q.vertex_mem_of_incident_edge he hinc)

/-- Ordered disjoint exterior access forces the original graph's actual overlay
endpoint paths to be noncrossing. The graph and external vertex map are not
altered; only their continuous path realizations are extended to the circle. -/
theorem boundaryPathNoncrossing (A : OrderedExteriorAccess P ext) :
    BoundaryPathNoncrossing G ext := by
  intro m n hm hn a b c d p p' hp hp' hab hbc hcd
  obtain ⟨r, q, hs, ht, _, he, hend⟩ := hp
  obtain ⟨t, q', hs', ht', _, he', hend'⟩ := hp'
  have hd : Disjoint q.vertexSet q'.vertexSet :=
    q.vertexSet_disjoint_of_endpoint_paths q' hm hn he he' hend
      (hend' _ (Or.inl rfl))
      (by rw [hs, hs']; exact fun h => (ne_of_gt hab) (A.external_injective h))
      (by rw [ht, hs']; exact fun h => (ne_of_lt hbc) (A.external_injective h))
  have hqa : ext a ∈ q.vertexSet :=
    Finset.mem_image.mpr ⟨0, Finset.mem_univ _, hs⟩
  have hqc : ext c ∈ q.vertexSet :=
    Finset.mem_image.mpr ⟨Fin.last (r + 1), Finset.mem_univ _, ht⟩
  have hqb : ext b ∈ q'.vertexSet :=
    Finset.mem_image.mpr ⟨0, Finset.mem_univ _, hs'⟩
  have hqd : ext d ∈ q'.vertexSet :=
    Finset.mem_image.mpr ⟨Fin.last (t + 1), Finset.mem_univ _, ht'⟩
  have hna : ext a ∉ q'.vertexSet := fun h => Finset.disjoint_left.mp hd hqa h
  have hnc : ext c ∉ q'.vertexSet := fun h => Finset.disjoint_left.mp hd hqc h
  have hnb : ext b ∉ q.vertexSet := fun h => Finset.disjoint_left.mp hd h hqb
  have hnd : ext d ∉ q.vertexSet := fun h => Finset.disjoint_left.mp hd h hqd
  have hj := A.graphDrawing.joinedIn_pathSupport q
  have hj' := A.graphDrawing.joinedIn_pathSupport q'
  rw [hs, ht] at hj
  rw [hs', ht'] at hj'
  obtain ⟨γ, hγ⟩ := hj
  obtain ⟨δ, hδ⟩ := hj'
  have hγsub : Set.range γ ⊆ A.graphDrawing.pathSupport q := by
    rintro z ⟨u, rfl⟩; exact hγ u
  have hδsub : Set.range δ ⊆ A.graphDrawing.pathSupport q' := by
    rintro z ⟨u, rfl⟩; exact hδ u
  have hγδ : Disjoint (Set.range γ) (Set.range δ) :=
    (A.graphDrawing.pathSupport_disjoint q q' hd).mono hγsub hδsub
  have hγb : Disjoint (Set.range γ) (Set.range (A.normalizedAccess b)) :=
    (A.pathSupport_disjoint_normalizedAccess q b hnb).mono_left hγsub
  have hγd : Disjoint (Set.range γ) (Set.range (A.normalizedAccess d)) :=
    (A.pathSupport_disjoint_normalizedAccess q d hnd).mono_left hγsub
  have haδ : Disjoint (Set.range (A.normalizedAccess a)) (Set.range δ) :=
    (A.pathSupport_disjoint_normalizedAccess q' a hna).symm.mono_right hδsub
  have hcδ : Disjoint (Set.range (A.normalizedAccess c)) (Set.range δ) :=
    (A.pathSupport_disjoint_normalizedAccess q' c hnc).symm.mono_right hδsub
  have hab' := A.normalizedAccess_disjoint (ne_of_lt hab)
  have had' := A.normalizedAccess_disjoint (ne_of_lt (hab.trans (hbc.trans hcd)))
  have hcb' := A.normalizedAccess_disjoint (ne_of_gt hbc)
  have hcd' := A.normalizedAccess_disjoint (ne_of_lt hcd)
  let γ' := ((A.normalizedAccess a).symm.trans γ).trans (A.normalizedAccess c)
  let δ' := ((A.normalizedAccess b).symm.trans δ).trans (A.normalizedAccess d)
  have hext : Disjoint (Set.range γ') (Set.range δ') := by
    simp only [γ', δ', Path.trans_range, Path.symm_range,
      Set.disjoint_union_left, Set.disjoint_union_right]
    tauto
  have hγ' : ∀ u, ‖γ' u‖ ≤ 1 := by
    intro u
    have hu : γ' u ∈ Set.range γ' := Set.mem_range_self u
    simp only [γ', Path.trans_range, Path.symm_range, Set.mem_union, Set.mem_range] at hu
    rcases hu with (⟨v, hv⟩ | ⟨v, hv⟩) | ⟨v, hv⟩
    · rw [← hv]; exact A.normalizedAccess_in_disk a v
    · rw [← hv]; exact A.graphDrawing.pathSupport_in_disk q (hγ v)
    · rw [← hv]; exact A.normalizedAccess_in_disk c v
  have hδ' : ∀ u, ‖δ' u‖ ≤ 1 := by
    intro u
    have hu : δ' u ∈ Set.range δ' := Set.mem_range_self u
    simp only [δ', Path.trans_range, Path.symm_range, Set.mem_union, Set.mem_range] at hu
    rcases hu with (⟨v, hv⟩ | ⟨v, hv⟩) | ⟨v, hv⟩
    · rw [← hv]; exact A.normalizedAccess_in_disk b v
    · rw [← hv]; exact A.graphDrawing.pathSupport_in_disk q' (hδ v)
    · rw [← hv]; exact A.normalizedAccess_in_disk d v
  obtain ⟨u, v, huv⟩ := diskPathCrossing (A.angle a) (A.angle b) (A.angle c) (A.angle d)
    (A.angle_pos a) (A.angle_strictMono hab) (A.angle_strictMono hbc)
    (A.angle_strictMono hcd) (A.angle_lt_one d) γ' δ' hγ' hδ'
  exact Set.disjoint_left.mp hext ⟨u, rfl⟩ ⟨v, huv.symm⟩

/-- All matchgate identities for the original plane graph's finite-subset
signature, assuming the explicit geometric exterior-access witness. -/
theorem deletionSubsetSignature_matchgateIdentities [Fintype V] [Fintype E]
    (A : OrderedExteriorAccess P ext) : MatchgateIdentities (deletionSubsetSignature G ext) :=
  MatchgateWidth.deletionSubsetSignature_matchgateIdentities G ext A.external_injective
    A.boundaryPathNoncrossing

/-- The corresponding theorem for the original Boolean deletion signature.
No pendant graph, substituted signature, or assumed graph MGI is used. -/
theorem deletionSignature_matchgateIdentities [Fintype V] [Fintype E]
    (A : OrderedExteriorAccess P ext) :
    MatchgateIdentities (fun S => deletionSignature G ext (fun i => decide (i ∈ S))) :=
  MatchgateWidth.deletionSignature_matchgateIdentities G ext A.external_injective
    A.boundaryPathNoncrossing

end OrderedExteriorAccess
end
end MatchgateWidth
