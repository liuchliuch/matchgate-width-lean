import MatchgateWidth.DisjointDiskBridgeAssembly
import MatchgateWidth.StrongExteriorAccess

/-! # Strong exterior access for an actually assembled bridge graph
Local carrier avoidance and corridor disjointness imply all graph-edge and
isolated-vertex avoidance conditions. No output signature identity is assumed.
-/
namespace MatchgateWidth
noncomputable section
namespace PlaneDrawing
variable {V W E F B : Type*} {G : WeightedGraph V E ℂ} {H : WeightedGraph W F ℂ}

/-- Assemble the strong global external-order witness from actual boundary
paths and the concrete bridge drawing. -/
def bridgeStrongExteriorAccess
    (P : PlaneDrawing G) (Q : PlaneDrawing H) (C : DisjointCarriers P Q)
    (extL : B → V) (extR : B → W) (R : BridgeRouting P Q C extL extR)
    {s : ℕ} (ext : Fin s → V) (hext : Function.Injective ext)
    (ρ : ℝ) (hρ : 0<ρ) (θ : Fin s → ℝ)
    (hθ0 : ∀ i, 0<θ i) (hθ1 : ∀ i, θ i<1) (hθ : StrictMono θ)
    (A : ∀ i, Path (P.vertex (ext i)) ((ρ:ℂ)*boundaryPoint (θ i)))
    (hAi : ∀ i, Function.Injective (A i))
    (hAd : Pairwise (fun i j => Disjoint (Set.range (A i)) (Set.range (A j))))
    (hAL : ∀ i, Set.range (A i) ∩ C.left ⊆ {P.vertex (ext i)})
    (hAR : ∀ i, Disjoint (Set.range (A i)) C.right)
    (hAB : ∀ i b, Disjoint (Set.range (A i)) (Set.range (R.arc b)))
    (hPv : ∀ v, ‖P.vertex v‖ ≤ ρ) (hQv : ∀ v, ‖Q.vertex v‖ ≤ ρ)
    (hPe : ∀ e t, ‖P.edge e t‖ ≤ ρ) (hQe : ∀ e t, ‖Q.edge e t‖ ≤ ρ)
    (hRe : ∀ b t, ‖R.arc b t‖ ≤ ρ) (hAb : ∀ i t, ‖A i t‖ ≤ ρ) :
    StrongOrderedExteriorAccess (P.bridge Q C extL extR R) (fun i => Sum.inl (ext i)) where
  external_injective := Sum.inl_injective.comp hext
  radius := ρ
  radius_pos := hρ
  vertex_bound := by rintro (v|w); exact hPv v; exact hQv w
  edge_bound := by rintro ((e|f)|b) t; exact hPe e t; exact hQe f t; exact hRe b t
  angle := θ
  angle_pos := hθ0
  angle_lt_one := hθ1
  angle_strictMono := hθ
  access := A
  access_bound := hAb
  access_disjoint := hAd
  access_injective := hAi
  access_meets_edge_only_at_start := by
    rintro i t ((e|f)|b) u h
    · change A i t = P.edge e u at h
      have he : A i t = P.vertex (ext i) := hAL i ⟨⟨t,rfl⟩,h.symm ▸ C.left_edge e u⟩
      exact hAi i (he.trans (A i).source.symm)
    · change A i t = Q.edge f u at h
      exact (Set.disjoint_left.mp (hAR i) ⟨t,rfl⟩ (h.symm ▸ C.right_edge f u)).elim
    · change A i t = R.arc b u at h
      exact (Set.disjoint_left.mp (hAB i b) ⟨t,rfl⟩ ⟨u,h.symm⟩).elim
  access_meets_vertex_only_at_start := by
    rintro i t (v|w) h
    · change A i t = P.vertex v at h
      have he : A i t = P.vertex (ext i) := hAL i ⟨⟨t,rfl⟩,h.symm ▸ C.left_vertex v⟩
      have ht : t=0 := hAi i (he.trans (A i).source.symm)
      exact ⟨ht,congrArg Sum.inl (P.vertex_injective (h.symm.trans he))⟩
    · change A i t = Q.vertex w at h
      exact (Set.disjoint_left.mp (hAR i) ⟨t,rfl⟩ (h.symm ▸ C.right_vertex w)).elim

end PlaneDrawing
end
end MatchgateWidth
