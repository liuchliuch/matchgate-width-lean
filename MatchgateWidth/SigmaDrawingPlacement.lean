import MatchgateWidth.LocalDrawingPlacement
import MatchgateWidth.MatchingSigmaGluing
import MatchgateWidth.CompactRoutingSeparation

/-! # Simultaneous disjoint placement of a finite family of matchgate graphs -/
namespace MatchgateWidth
noncomputable section

namespace PlaneDrawing
variable {I : Type*} {V E : I → Type*} {G : ∀ i, WeightedGraph (V i) (E i) ℂ}

structure FamilyCarriers (P : ∀ i, PlaneDrawing (G i)) where
  carrier : I → Set ℂ
  disjoint : Pairwise (fun i j => Disjoint (carrier i) (carrier j))
  vertex_mem : ∀ i v, (P i).vertex v ∈ carrier i
  edge_mem : ∀ i e t, (P i).edge e t ∈ carrier i

/-- The full dependent disjoint union is drawn using the literal component
coordinates, with every cross-component nonintersection derived from carriers. -/
def sigmaDrawing (P : ∀ i, PlaneDrawing (G i)) (C : FamilyCarriers P) :
    PlaneDrawing (sigmaGraph G) where
  vertex := fun v => (P v.1).vertex v.2
  vertex_injective := by
    rintro ⟨i,v⟩ ⟨j,w⟩ h
    change (P i).vertex v = (P j).vertex w at h
    by_cases hij : i=j
    · subst j
      exact congrArg (Sigma.mk i) ((P i).vertex_injective h)
    · exact (Set.disjoint_left.mp (C.disjoint hij) (C.vertex_mem i v)
        (h.symm ▸ C.vertex_mem j w)).elim
  edge := fun e t => (P e.1).edge e.2 t
  edge_continuous := fun e => (P e.1).edge_continuous e.2
  edge_injective := fun e => (P e.1).edge_injective e.2
  edge_left := fun e => (P e.1).edge_left e.2
  edge_right := fun e => (P e.1).edge_right e.2
  interior_avoids_vertices := by
    rintro ⟨i,e⟩ t ht0 ht1 ⟨j,v⟩ h
    by_cases hij : i=j
    · subst j
      exact (P i).interior_avoids_vertices e t ht0 ht1 v h
    · exact Set.disjoint_left.mp (C.disjoint hij) (C.edge_mem i e t)
        (h.symm ▸ C.vertex_mem j v)
  interiors_disjoint := by
    rintro ⟨i,e⟩ ⟨j,f⟩ hef t u ht0 ht1 hu0 hu1 h
    by_cases hij : i=j
    · subst j
      exact (P i).interiors_disjoint e f (fun he => hef (congrArg (Sigma.mk i) he))
        t u ht0 ht1 hu0 hu1 h
    · exact Set.disjoint_left.mp (C.disjoint hij) (C.edge_mem i e t)
        (h.symm ▸ C.edge_mem j f u)

end PlaneDrawing

/-- Finite distinct centers admit one common positive closed-disk radius,
including the empty and one-center cases. -/
theorem finite_distinct_closedBall_disjoint {I : Type*} [Finite I]
    (c : I → ℂ) (hc : Function.Injective c) :
    ∃ ε : ℝ, 0 < ε ∧ Pairwise (fun i j =>
      Disjoint (Metric.closedBall (c i) ε) (Metric.closedBall (c j) ε)) := by
  classical
  let d : I×I → ℝ := fun p => if p.1=p.2 then 1 else dist (c p.1) (c p.2)/3
  have hd : ∀ p, 0<d p := by
    rintro ⟨i,j⟩
    by_cases hij : i=j
    · simp [d,hij]
    · simp only [d,ite_eq_right hij]
      exact div_pos (dist_pos.mpr (fun h => hij (hc h))) (by norm_num)
  obtain ⟨ε,hε,he⟩ := finite_positive_lower_bound d hd
  refine ⟨ε,hε,?_⟩
  intro i j hij
  apply Set.disjoint_left.mpr
  intro z hzi hzj
  have hi : dist z (c i) ≤ ε := hzi
  have hj : dist z (c j) ≤ ε := hzj
  have hdist := dist_triangle_left (c i) (c j) z
  have hbound := he (i,j)
  simp only [d,ite_eq_right hij] at hbound
  nlinarith

end
end MatchgateWidth
