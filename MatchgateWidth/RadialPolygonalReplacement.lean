import MatchgateWidth.PolygonalGraphReplacement
import MatchgateWidth.PolygonalEndpointGerms

/-! # Polygonal replacement preserves every positive radial endpoint germ -/
namespace MatchgateWidth
noncomputable section
open Set
namespace PlanarDrawing
variable {V E : Type*} {s : ℕ} {G : WeightedGraph V E ℂ} {ext : Fin s → V}

/-- Same-graph polygonal replacement together with exact preservation of each
original radial direction, allowing only a positive speed change. -/
structure RadialPolygonalReplacement (D : PlanarDrawing G ext) where
  initialCut : E → unitInterval
  terminalCut : E → unitInterval
  stem : D.PolygonalStemReplacement initialCut terminalCut
  source_germ : ∀ e (τ : unitInterval), 0<τ → ∀ v : ℂ,
    (∀ t : unitInterval, t≤τ → D.edge e t = D.vertex (G.left e)+(t:ℝ)•v) →
    ∃ κ : ℝ, 0<κ ∧ ∃ ρ : unitInterval, 0<ρ ∧
      ∀ t : unitInterval, t≤ρ → stem.path e t = D.vertex (G.left e)+(t:ℝ)•(κ•v)
  target_germ : ∀ e (τ : unitInterval), 0<τ → ∀ v : ℂ,
    (∀ t : unitInterval, t≤τ → (D.edgePath e).symm t = D.vertex (G.right e)+(t:ℝ)•v) →
    ∃ κ : ℝ, 0<κ ∧ ∃ ρ : unitInterval, 0<ρ ∧
      ∀ t : unitInterval, t≤ρ → (stem.path e).symm t = D.vertex (G.right e)+(t:ℝ)•(κ•v)

abbrev RadialPolygonalReplacement.drawing {D : PlanarDrawing G ext}
    (R : D.RadialPolygonalReplacement) := R.stem.drawing

/-- Radial endpoint germs and strict interior edge containment suffice for a
same-graph simple polygonal drawing preserving all original endpoint directions. -/
theorem exists_radial_polygonal_replacement [Finite V] [Finite E] (D : PlanarDrawing G ext)
    (hint : ∀ e t, 0<t → t<1 → ‖D.edge e t‖<1)
    (hgL : ∀ e, ∃ τ : unitInterval, 0<τ ∧ ∃ v : ℂ,
      ∀ t : unitInterval, t≤τ → D.edge e t = D.vertex (G.left e)+(t:ℝ)•v)
    (hgR : ∀ e, ∃ τ : unitInterval, 0<τ ∧ ∃ v : ℂ,
      ∀ t : unitInterval, t≤τ → (D.edgePath e).symm t = D.vertex (G.right e)+(t:ℝ)•v) :
    Nonempty D.RadialPolygonalReplacement := by
  classical
  choose τL hτL vL hvL using hgL
  choose τR hτR vR hvR using hgR
  let quarter : unitInterval := ⟨1/4,by norm_num⟩
  let a : E → unitInterval := fun e => min (τL e) quarter
  let c : E → unitInterval := fun e => min (τR e) quarter
  let b : E → unitInterval := fun e => unitInterval.symm (c e)
  have ha : ∀ e, 0<a e := fun e => lt_min (hτL e) (by change (0:ℝ)<1/4; norm_num)
  have hc : ∀ e, 0<c e := fun e => lt_min (hτR e) (by change (0:ℝ)<1/4; norm_num)
  have haτ : ∀ e, a e≤τL e := fun e => min_le_left _ _
  have hcτ : ∀ e, c e≤τR e := fun e => min_le_left _ _
  have hab : ∀ e, a e<b e := by
    intro e
    have haQ : a e≤quarter := min_le_right _ _
    have hcQ : c e≤quarter := min_le_right _ _
    change (a e:ℝ)<1-(c e:ℝ)
    change (a e:ℝ)≤1/4 at haQ
    change (c e:ℝ)≤1/4 at hcQ
    linarith
  have hb : ∀ e, b e<1 := by
    intro e
    change 1-(c e:ℝ)<1
    have hh : 0<(c e:ℝ) := hc e
    linarith
  have hL : ∀ e, segment ℝ (D.vertex (G.left e)) (D.edge e (a e)) ⊆
      D.edge e '' Icc 0 (a e) := by
    intro e
    exact segment_subset_initial_image (D.edgePath e) (a e) (vL e)
      (fun t ht => hvL e t (ht.trans (haτ e)))
  have hR : ∀ e, segment ℝ (D.edge e (b e)) (D.vertex (G.right e)) ⊆
      D.edge e '' Icc (b e) 1 := by
    intro e z hz
    have hseg := segment_subset_initial_image (D.edgePath e).symm (c e) (vR e)
      (fun t ht => hvR e t (ht.trans (hcτ e)))
    have hz' : z ∈ segment ℝ (D.vertex (G.right e)) ((D.edgePath e).symm (c e)) := by
      change z ∈ segment ℝ (D.vertex (G.right e)) (D.edge e (b e))
      rwa [segment_symm]
    obtain ⟨t,ht,heq⟩ := hseg hz'
    refine ⟨unitInterval.symm t,⟨?_,(unitInterval.symm t).2.2⟩,heq⟩
    change 1-(c e:ℝ)≤1-(t:ℝ)
    have hh : (t:ℝ)≤c e := ht.2
    linarith
  obtain ⟨R⟩ := D.exists_polygonal_stem_replacement a b ha hab hb hint hL hR
  have hnewL : ∀ e, ∃ κ : ℝ, 0<κ ∧ ∃ ρ : unitInterval, 0<ρ ∧
      ∀ t : unitInterval, t≤ρ → R.path e t = D.vertex (G.left e)+(t:ℝ)•(κ•vL e) := by
    intro e
    have hloc := R.source_ray e
    rw [hvL e (a e) (haτ e)] at hloc
    obtain ⟨κ,hκ,ρ,hρ,hg⟩ := (R.polygonal e).exists_positive_source_germ (R.injective e) hloc
    refine ⟨κ*(a e:ℝ),mul_pos hκ (ha e),ρ,hρ,?_⟩
    intro t ht
    simpa only [smul_smul] using hg t ht
  have hnewR : ∀ e, ∃ κ : ℝ, 0<κ ∧ ∃ ρ : unitInterval, 0<ρ ∧
      ∀ t : unitInterval, t≤ρ → (R.path e).symm t = D.vertex (G.right e)+(t:ℝ)•(κ•vR e) := by
    intro e
    have hloc := R.target_ray e
    have hcut : D.edge e (b e) = D.vertex (G.right e)+(c e:ℝ)•vR e :=
      hvR e (c e) (hcτ e)
    rw [hcut] at hloc
    obtain ⟨κ,hκ,ρ,hρ,hg⟩ := (R.polygonal e).exists_positive_target_germ (R.injective e) hloc
    refine ⟨κ*(c e:ℝ),mul_pos hκ (hc e),ρ,hρ,?_⟩
    intro t ht
    simpa only [smul_smul] using hg t ht
  refine ⟨⟨a,b,R,?_,?_⟩⟩
  · intro e τ hτ v hg
    have hvel : vL e=v := source_germ_velocity_unique (hτL e) hτ (hvL e) hg
    simpa only [hvel] using hnewL e
  · intro e τ hτ v hg
    have hvel : vR e=v := source_germ_velocity_unique (hτR e) hτ (hvR e) hg
    simpa only [hvel] using hnewR e

end PlanarDrawing
end
end MatchgateWidth
