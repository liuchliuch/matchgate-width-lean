import MatchgateWidth.AllLeftGeometricLanes
import MatchgateWidth.CompactRoutingSeparation

/-! # One simultaneous physical ribbon family for all source edges

All route-specific width choices are made before the single global parameter.
The resulting paths use the exact internal/exposed lane reindexing, with all
within-edge and cross-edge nonintersection conclusions proved.
-/
namespace MatchgateWidth
noncomputable section
namespace TransversePolygonalRoute
variable {m : ℕ} (R : TransversePolygonalRoute m)

theorem Width.mono {ε η : ℝ} (h : R.Width ε) (hle : η ≤ ε) : R.Width η :=
  fun δ hδ => h δ (hδ.trans_le hle)

theorem laneSupport_subset_carriers {ε δ : ℝ} (h : R.Width ε) (hδ : |δ| < ε) :
    R.laneSupport δ ⊆ ⋃ i, R.carrier i := by
  intro z hz
  obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hz
  exact Set.mem_iUnion.mpr ⟨i,(h δ hδ i).2.2 hi⟩

end TransversePolygonalRoute
namespace AllLeftGadget
variable {c n t : ℕ}

/-- Real finite ribbons, already constructed from the source polygonal traces,
admit one global width and a pairwise-disjoint physical wire path family for
every smaller positive width. Empty edge and lane types are included. -/
theorem exists_uniform_physical_ribbon_family
    (m : Fin c ⊕ Fin n → ℕ) (R : ∀ e, TransversePolygonalRoute (m e))
    (hm : ∀ e, 0 < m e)
    (hcross : Pairwise (fun e f => Disjoint (⋃ i, (R e).carrier i) (⋃ j, (R f).carrier j))) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε, 0 < ε → ε ≤ ε₀ →
      (∀ e, (R e).Width ε) ∧
      ∃ q : (e : Fin c ⊕ Fin n) → (k : Fin t) →
        Path ((R e).laneVertex (physicalLaneOffset ε e k) 0)
          ((R e).laneVertex (physicalLaneOffset ε e k) (Fin.last (m e))),
      (∀ e k, Function.Injective (q e k) ∧ IsPolygonalPath (q e k) ∧
        Set.range (q e k) = (R e).laneSupport (physicalLaneOffset ε e k)) ∧
      Pairwise (fun x y : (Fin c ⊕ Fin n) × Fin t =>
        Disjoint (Set.range (q x.1 x.2)) (Set.range (q y.1 y.2))) := by
  classical
  choose η hη hwidth using fun e => (R e).exists_width
  obtain ⟨ε₀,hε₀,hsmall⟩ := finite_positive_lower_bound η hη
  refine ⟨ε₀,hε₀,?_⟩
  intro ε hε hεle
  have hW (e : Fin c ⊕ Fin n) : (R e).Width ε :=
    TransversePolygonalRoute.Width.mono (R e) (hwidth e) (hεle.trans (hsmall e))
  have hex (e : Fin c ⊕ Fin n) := exists_physical_lane_paths (t := t) (R e) (hm e) hε (hW e) e
  choose q hq hd using hex
  refine ⟨hW,q,hq,?_⟩
  rintro ⟨e,k⟩ ⟨f,l⟩ hne
  by_cases hef : e = f
  · subst f
    exact hd e (fun hkl => hne (Prod.ext rfl hkl))
  · rw [(hq e k).2.2,(hq f l).2.2]
    exact (hcross hef).mono
      ((R e).laneSupport_subset_carriers (hW e) (physicalLaneOffset_bounds hε e k).2)
      ((R f).laneSupport_subset_carriers (hW f) (physicalLaneOffset_bounds hε f l).2)

end AllLeftGadget
end
end MatchgateWidth
