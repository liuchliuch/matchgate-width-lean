import MatchgateWidth.SigmaDrawingPlacement
import MatchgateWidth.DisjointDiskBridgeAssembly
import MatchgateWidth.MatchingFamilySubstitution

/-! # Actual plane drawings of dependent disjoint matchgate families

The geometric constructor uses the same `sigmaGraph` and `bridgeGraph`
identities as the independently proved matching-sum factorization. Local
vertices and edges retain their component identities and original parameters.
-/
namespace MatchgateWidth
noncomputable section

namespace PlaneDrawing
variable {I : Type*} {V E : I → Type*}
variable {G : ∀ i, WeightedGraph (V i) (E i) ℂ}

/-- The full family is contained in the union of its local carriers. -/
theorem sigma_vertex_mem (P : ∀ i, PlaneDrawing (G i)) (C : FamilyCarriers P) (v : Sigma V) :
    (sigmaDrawing P C).vertex v ∈ ⋃ i, C.carrier i :=
  Set.mem_iUnion.mpr ⟨v.1,C.vertex_mem v.1 v.2⟩

theorem sigma_edge_mem (P : ∀ i, PlaneDrawing (G i)) (C : FamilyCarriers P)
    (e : Sigma E) (t : unitInterval) :
    (sigmaDrawing P C).edge e t ∈ ⋃ i, C.carrier i :=
  Set.mem_iUnion.mpr ⟨e.1,C.edge_mem e.1 e.2 t⟩

/-- Pairwise separated local carrier disks on the left and right give the
exact two-family carrier interface required by bridge assembly. -/
def bipartiteCarriers {J : Type*} {W F : J → Type*}
    {H : ∀ j, WeightedGraph (W j) (F j) ℂ}
    (P : ∀ i, PlaneDrawing (G i)) (Q : ∀ j, PlaneDrawing (H j))
    (C : FamilyCarriers P) (D : FamilyCarriers Q)
    (hcross : ∀ i j, Disjoint (C.carrier i) (D.carrier j)) :
    DisjointCarriers (sigmaDrawing P C) (sigmaDrawing Q D) where
  left := ⋃ i, C.carrier i
  right := ⋃ j, D.carrier j
  disjoint := by
    apply Set.disjoint_left.mpr
    intro z hz hz'
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hz
    obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hz'
    exact Set.disjoint_left.mp (hcross i j) hi hj
  left_vertex := sigma_vertex_mem P C
  right_vertex := sigma_vertex_mem Q D
  left_edge := sigma_edge_mem P C
  right_edge := sigma_edge_mem Q D

/-- Substitute an actual graph family on each side and add independently
constructed physical wire paths. The resulting graph is literally the graph
used by `deletionSignature_substitutedFamilyGraph`, not a proxy signature. -/
def substitutedFamilies {J B : Type*} {W F : J → Type*}
    {H : ∀ j, WeightedGraph (W j) (F j) ℂ}
    {arityL : I → ℕ} {arityR : J → ℕ}
    (P : ∀ i, PlaneDrawing (G i)) (Q : ∀ j, PlaneDrawing (H j))
    (C : FamilyCarriers P) (D : FamilyCarriers Q)
    (hcross : ∀ i j, Disjoint (C.carrier i) (D.carrier j))
    (extL : ∀ i, Fin (arityL i) → V i) (extR : ∀ j, Fin (arityR j) → W j)
    (portL : B → Σ i, Fin (arityL i)) (portR : B → Σ j, Fin (arityR j))
    (routes : BridgeRouting (sigmaDrawing P C) (sigmaDrawing Q D) (bipartiteCarriers P Q C D hcross)
      (sigmaExternal extL ∘ portL) (sigmaExternal extR ∘ portR)) :
    PlaneDrawing (substitutedFamilyGraph G H extL extR portL portR) :=
  (sigmaDrawing P C).bridge (sigmaDrawing Q D) (bipartiteCarriers P Q C D hcross)
    (sigmaExternal extL ∘ portL) (sigmaExternal extR ∘ portR) routes

end PlaneDrawing
end
end MatchgateWidth
