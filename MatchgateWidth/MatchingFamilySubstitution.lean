import MatchgateWidth.MatchingSigmaGluing

/-!
# Finite family substitution is exactly a deletion-signature tensor network

Actual disjoint local matching graphs are joined by distinct unit-weight bridge
edges. Only graph identities and prescribed port matchings occur; no output MGI
or planar closure is assumed. Planar routing can be supplied independently.
-/
namespace MatchgateWidth
noncomputable section
open scoped Classical
set_option maxHeartbeats 600000

/-- Embed every local external vertex in its own graph component. -/
def sigmaExternal {I : Type*} {V : I → Type*} {arity : I → ℕ}
    (ext : (i : I) → Fin (arity i) → V i) : (Σ i, Fin (arity i)) → Sigma V :=
  fun q => ⟨q.1,ext q.1 q.2⟩

theorem sigmaExternal_injective {I : Type*} {V : I → Type*} {arity : I → ℕ}
    (ext : (i : I) → Fin (arity i) → V i)
    (h : ∀ i, Function.Injective (ext i)) : Function.Injective (sigmaExternal ext) := by
  rintro ⟨i,k⟩ ⟨j,l⟩ he
  have hij : i = j := congrArg Sigma.fst he
  subst j
  exact Sigma.mk.inj_iff.mpr ⟨rfl, heq_of_eq (h i (eq_of_heq (Sigma.mk.inj he).2))⟩

/-- Deleting a finite global port set is exactly deleting its componentwise
Boolean masks. This holds even for empty or nullary graph components. -/
theorem sigma_delete_ports {I : Type*} {V : I → Type*} {arity : I → ℕ}
    [Fintype I] [∀ i, Fintype (V i)]
    [DecidableEq (Sigma V)] [DecidableEq (Σ i, Fin (arity i))]
    (ext : (i : I) → Fin (arity i) → V i) (d : Finset (Σ i, Fin (arity i))) :
    Finset.univ \ d.image (sigmaExternal ext) =
      Finset.univ.sigma (fun i => deletionActive (ext i) (fun k => decide ((⟨i,k⟩ : Σ i, Fin (arity i)) ∈ d))) := by
  classical
  ext ⟨i,v⟩
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_image,
    Finset.mem_sigma, deletionActive, Finset.mem_filter, decide_eq_true_eq]
  apply not_congr
  constructor
  · rintro ⟨⟨j,k⟩,hjk,he⟩
    have hji : j = i := congrArg Sigma.fst he
    subst j
    exact ⟨k,hjk,eq_of_heq (Sigma.mk.inj he).2⟩
  · rintro ⟨k,hk,he⟩
    exact ⟨⟨i,k⟩,hk,congrArg (Sigma.mk i) he⟩

/-- Explicit physical graph obtained by substituting local graphs on both
sides and adding the prescribed internal unit bridges. -/
def substitutedFamilyGraph {I J B : Type*} {VL EL : I → Type*} {VR ER : J → Type*}
    {aL : I → ℕ} {aR : J → ℕ} {K : Type*} [CommSemiring K]
    (Gleft : ∀ i, WeightedGraph (VL i) (EL i) K)
    (Gright : ∀ j, WeightedGraph (VR j) (ER j) K)
    (extL : ∀ i, Fin (aL i) → VL i) (extR : ∀ j, Fin (aR j) → VR j)
    (portL : B → Σ i, Fin (aL i)) (portR : B → Σ j, Fin (aR j)) :=
  bridgeGraph (sigmaGraph Gleft) (sigmaGraph Gright)
    (sigmaExternal extL ∘ portL) (sigmaExternal extR ∘ portR)

/-- Whole substituted graph identity, with arbitrary prescribed external
boundary order. The local Boolean masks are derived from actual selected
bridges and the actual requested boundary deletions. -/
theorem deletionSignature_substitutedFamilyGraph
    {I J B : Type*} {VL EL : I → Type*} {VR ER : J → Type*}
    {aL : I → ℕ} {aR : J → ℕ} {s : ℕ} {K : Type*} [CommSemiring K]
    [Fintype I] [Fintype J] [Fintype B]
    [∀ i, Fintype (VL i)] [∀ i, Fintype (EL i)]
    [∀ j, Fintype (VR j)] [∀ j, Fintype (ER j)]
    [DecidableEq (Σ i, Fin (aL i))] [DecidableEq (Σ j, Fin (aR j))]
    (Gleft : ∀ i, WeightedGraph (VL i) (EL i) K)
    (Gright : ∀ j, WeightedGraph (VR j) (ER j) K)
    (extL : ∀ i, Fin (aL i) → VL i) (extR : ∀ j, Fin (aR j) → VR j)
    (hL : ∀ i, Function.Injective (extL i)) (hR : ∀ j, Function.Injective (extR j))
    (portL : B → Σ i, Fin (aL i)) (portR : B → Σ j, Fin (aR j))
    (hinjL : Function.Injective portL) (hinjR : Function.Injective portR)
    (boundary : Fin s → Σ i, Fin (aL i))
    (hdisjoint : ∀ b q, portL b ≠ boundary q) (z : Fin s → Bool) :
    deletionSignature (substitutedFamilyGraph Gleft Gright extL extR portL portR)
      (fun q => Sum.inl (sigmaExternal extL (boundary q))) z =
    ∑ b : Finset B,
      (∏ i, deletionSignature (Gleft i) (extL i)
        (fun k => decide ((⟨i,k⟩ : Σ i, Fin (aL i)) ∈
          (bridgeBitsEquiv (Fin s) z).image boundary ∪ b.image portL))) *
      ∏ j, deletionSignature (Gright j) (extR j)
        (fun k => decide ((⟨j,k⟩ : Σ j, Fin (aR j)) ∈ b.image portR)) := by
  classical
  letI : DecidableEq (Sigma VL) := Classical.decEq _
  letI : DecidableEq (Sigma VR) := Classical.decEq _
  let d := (bridgeBitsEquiv (Fin s) z).image boundary
  let l := sigmaExternal extL
  let r := sigmaExternal extR
  have hli : Function.Injective l := sigmaExternal_injective extL hL
  have hri : Function.Injective r := sigmaExternal_injective extR hR
  have hactive : deletionActive (fun q => Sum.inl (l (boundary q))) z =
      (Finset.univ \ d.image l).disjSum (Finset.univ : Finset (Sigma VR)) := by
    ext v
    cases v with
    | inl v => simp [deletionActive,d,bridgeBitsEquiv,l]
    | inr v => simp [deletionActive]
  have hbridgeL (b : B) : l (portL b) ∈ Finset.univ \ d.image l := by
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_image]
    rintro ⟨p,hp,he⟩
    have hpe := hli he
    subst p
    obtain ⟨q,hq,hqb⟩ := Finset.mem_image.mp hp
    exact hdisjoint b q hqb.symm
  unfold deletionSignature substitutedFamilyGraph
  rw [hactive, weightedPerfectMatch_bridge_active (sigmaGraph Gleft) (sigmaGraph Gright)
    (l ∘ portL) (r ∘ portR) (hli.comp hinjL) (hri.comp hinjR)
    _ _ hbridgeL (fun _ => Finset.mem_univ _)]
  apply Finset.sum_congr rfl
  intro b hb
  have hleft : (Finset.univ \ d.image l) \ b.image (l ∘ portL) =
      Finset.univ \ (d ∪ b.image portL).image l := by
    simp only [Finset.image_union, Finset.image_image]
    ext v
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_union, not_or]
  have hright : (Finset.univ : Finset (Sigma VR)) \ b.image (r ∘ portR) =
      Finset.univ \ (b.image portR).image r := by rw [Finset.image_image]
  rw [hleft, hright]
  change weightedPerfectMatch (sigmaGraph Gleft) (Finset.univ \ (d ∪ b.image portL).image (sigmaExternal extL)) *
    weightedPerfectMatch (sigmaGraph Gright) (Finset.univ \ (b.image portR).image (sigmaExternal extR)) = _
  rw [sigma_delete_ports extL, sigma_delete_ports extR,
    weightedPerfectMatch_sigmaGraph, weightedPerfectMatch_sigmaGraph]

end
end MatchgateWidth
