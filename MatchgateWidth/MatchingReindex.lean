import MatchgateWidth.PlanarDrawing

/-! # Finite graph enumeration preserves exact weighted deletion signatures -/
namespace MatchgateWidth
noncomputable section
variable {V E V' E' K : Type*} [Fintype V] [Fintype E] [Fintype V'] [Fintype E']
  [CommSemiring K]

/-- Pull a graph back along bijective vertex and edge enumerations. -/
def WeightedGraph.reindex (G : WeightedGraph V E K) (v : V' ≃ V) (e : E' ≃ E) :
    WeightedGraph V' E' K where
  left a := v.symm (G.left (e a))
  right a := v.symm (G.right (e a))
  loopless a := fun h => G.loopless (e a) (v.symm.injective h)
  weight a := G.weight (e a)

theorem matchingDegree_reindex (G : WeightedGraph V E K) (v : V' ≃ V) (e : E' ≃ E)
    (m : Finset E') (x : V') :
    matchingDegree (G.reindex v e) m x = matchingDegree G (e.finsetCongr m) (v x) := by
  classical
  simp [matchingDegree, WeightedGraph.reindex, Equiv.finsetCongr_apply, Equiv.symm_apply_eq]

theorem matchesExactly_reindex (G : WeightedGraph V E K) (v : V' ≃ V) (e : E' ≃ E)
    (a : Finset V') (m : Finset E') :
    MatchesExactly (G.reindex v e) a m ↔ MatchesExactly G (v.finsetCongr a) (e.finsetCongr m) := by
  classical
  simp only [MatchesExactly, matchingDegree_reindex]
  constructor
  · intro h x
    obtain ⟨y, rfl⟩ := v.surjective x
    simpa [Equiv.finsetCongr_apply] using h y
  · intro h x
    simpa [Equiv.finsetCongr_apply] using h (v x)

theorem weightedPerfectMatch_reindex (G : WeightedGraph V E K) (v : V' ≃ V) (e : E' ≃ E)
    (a : Finset V') :
    weightedPerfectMatch (G.reindex v e) a = weightedPerfectMatch G (v.finsetCongr a) := by
  classical
  unfold weightedPerfectMatch
  rw [← e.finsetCongr.sum_comp]
  apply Finset.sum_congr rfl
  intro m _
  rw [matchesExactly_reindex]
  simp [WeightedGraph.reindex, Equiv.finsetCongr_apply]
  rfl

theorem deletionActive_reindex {s : ℕ} (v : V' ≃ V) (ext : Fin s → V) (x : Fin s → Bool) :
    v.finsetCongr (deletionActive (fun i => v.symm (ext i)) x) = deletionActive ext x := by
  classical
  ext z
  simp [Equiv.finsetCongr_apply, deletionActive]

theorem deletionSignature_reindex {s : ℕ} (G : WeightedGraph V E K)
    (v : V' ≃ V) (e : E' ≃ E) (ext : Fin s → V) (x : Fin s → Bool) :
    deletionSignature (G.reindex v e) (fun i => v.symm (ext i)) x = deletionSignature G ext x := by
  unfold deletionSignature
  rw [weightedPerfectMatch_reindex, deletionActive_reindex]

/-- Relabeling transports the actual continuous ordered drawing. -/
def PlanarDrawing.reindex {s : ℕ} {G : WeightedGraph V E ℂ} {ext : Fin s → V}
    (D : PlanarDrawing G ext) (v : V' ≃ V) (e : E' ≃ E) :
    PlanarDrawing (G.reindex v e) (fun i => v.symm (ext i)) where
  vertex := D.vertex ∘ v
  vertex_injective := D.vertex_injective.comp v.injective
  vertex_in_disk x := D.vertex_in_disk (v x)
  edge a := D.edge (e a)
  edge_continuous a := D.edge_continuous (e a)
  edge_injective a := D.edge_injective (e a)
  edge_left a := by simpa [WeightedGraph.reindex] using D.edge_left (e a)
  edge_right a := by simpa [WeightedGraph.reindex] using D.edge_right (e a)
  edge_in_disk a t := D.edge_in_disk (e a) t
  interior_avoids_vertices a t h0 h1 x := D.interior_avoids_vertices (e a) t h0 h1 (v x)
  interiors_disjoint a b hab t u ht0 ht1 hu0 hu1 :=
    D.interiors_disjoint (e a) (e b) (fun h => hab (e.injective h)) t u ht0 ht1 hu0 hu1
  external_injective := v.symm.injective.comp D.external_injective
  angle := D.angle
  angle_pos := D.angle_pos
  angle_lt_one := D.angle_lt_one
  angle_strictMono := D.angle_strictMono
  external_vertex i := by simpa using D.external_vertex i

/-- A genuine drawing of any finite typed graph supplies the canonical finite
vertex/edge enumeration required by DiskRealizable, preserving every coefficient. -/
theorem diskRealizable_of_finite_drawing {s : ℕ} (G : WeightedGraph V E ℂ)
    (ext : Fin s → V) (D : PlanarDrawing G ext) :
    DiskRealizable (deletionSignature G ext) := by
  let v := (Fintype.equivFin V).symm
  let e := (Fintype.equivFin E).symm
  refine ⟨Fintype.card V, Fintype.card E, G.reindex v e,
    (fun i => v.symm (ext i)), ⟨D.reindex v e⟩, ?_⟩
  intro x
  exact (deletionSignature_reindex G v e ext x).symm

end
end MatchgateWidth
