import MatchgateWidth.UniformBooleanPlaneEmbedding
import MatchgateWidth.PivotCircuitRealization

/-! # Constructive disk realizations of uniformly decoded Boolean cores

The decoder is the one fixed by the algebraic plane embedding theorem. These
corollaries synthesize actual disk graphs for its coefficients at every arity;
they do not assume a source planar-embedding characterization.
-/
namespace MatchgateWidth
noncomputable section

/-- A fixed ordered decoder produces a genuinely disk-realizable k-wire core,
including k=0 and the zero tensor. -/
theorem booleanPlanePullback_diskRealizable {t : ℕ}
    {D : Matrix (BooleanInput t) (BooleanInput 1) ℂ}
    (hD : OrderedMatchgateMatrix D) (k : ℕ)
    {T : BooleanTable (k*t) ℂ} (hT : BooleanMatchgateIdentities T) :
    DiskRealizable (fun z => booleanPlanePullback D k T ((booleanWordEquiv k).symm z)) :=
  (hD.booleanPlanePullback k hT).diskRealizable

/-- The uniform coefficient core has an actual finite graph with an ordered
disk drawing and exactly equal deletion coefficients. -/
theorem booleanPlanePullback_diskWitness {t : ℕ}
    {D : Matrix (BooleanInput t) (BooleanInput 1) ℂ}
    (hD : OrderedMatchgateMatrix D) (k : ℕ)
    {T : BooleanTable (k*t) ℂ} (hT : BooleanMatchgateIdentities T) :
    ∃ (v e : ℕ) (G : WeightedGraph (Fin v) (Fin e) ℂ) (ext : Fin k → Fin v),
      Nonempty (PlanarDrawing G ext) ∧
      ∀ z, deletionSignature G ext z = booleanPlanePullback D k T ((booleanWordEquiv k).symm z) := by
  obtain ⟨v, e, G, ext, hd, _, hs⟩ :=
    (hD.booleanPlanePullback k hT).diskWitness_map_all (RingHom.id ℂ)
  exact ⟨v, e, G, ext, hd, hs⟩

end
end MatchgateWidth
