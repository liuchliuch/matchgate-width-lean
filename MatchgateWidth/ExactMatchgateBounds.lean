import MatchgateWidth.StrongExteriorAccess
import MatchgateWidth.TranscendenceBounds
import MatchgateWidth.AlgebraicObstruction
import MatchgateWidth.MGIReversal

/-! # Source matchgate bounds under the explicit global exterior-star order -/
namespace MatchgateWidth
noncomputable section
open Algebra

/-- Lemma 4.1, including arity zero. -/
theorem ExactMatchgate.reverse {s : ℕ} {G : BooleanTable s ℂ} (hG : ExactMatchgate G) :
    ExactMatchgate (fun x => G (fun i => x i.rev)) :=
  (BooleanMatchgateIdentities.reverse hG.matchgateIdentities).exactMatchgate

/-- Lemma 4.2: a literal MGI table over any complex subfield has an actual
ordered planar deletion realization whose every edge weight lies in that field. -/
theorem field_preserving_matchgate_realization {s : ℕ} (K : Subfield ℂ)
    (G : BooleanTable s K) (hG : BooleanMatchgateIdentities G) :
    ∃ (v e : ℕ) (H : WeightedGraph (Fin v) (Fin e) ℂ) (ext : Fin s → Fin v),
      Nonempty (PlanarDrawing H ext) ∧ (∀ a, H.weight a ∈ K) ∧
      ∀ y, deletionSignature H ext y = (G ((booleanWordEquiv s).symm y) : ℂ) := by
  obtain ⟨v,e,H,ext,hd,hw,hval⟩ := hG.diskWitness_map_all K.subtype
  refine ⟨v,e,H,ext,hd,?_,hval⟩
  intro a
  obtain ⟨q,hq⟩ := hw a
  rw [hq]
  exact q.property

/-- Lemma 5.1 for the actual geometrically realized matchgate signature. -/
theorem ExactMatchgate.trdeg_coordinateField_le {s : ℕ} {G : BooleanTable s ℂ}
    (hG : ExactMatchgate G) : trdeg ℚ (coordinateField G) ≤ delta s :=
  hG.matchgateIdentities.trdeg_coordinateField_le

/-- Proposition 5.2 for every finite sampler alphabet, with zero wire widths
and arbitrary complex graph weights included. Empty/zero-arity cases are harmless
stronger extensions of the source's q≥1 and k≥1 hypotheses. -/
theorem exact_sampled_star_coordinateField_bound {L : Type} [Fintype L] {k r : ℕ}
    {Q : BooleanTable (k*r) ℂ} {g : L → BooleanTable r ℂ}
    (hQ : ExactMatchgate Q) (hg : ∀ l, ExactMatchgate (g l)) :
    trdeg ℚ (coordinateField (sampledAlphabetStar Q g)) ≤
      (Fintype.card L * delta r + delta (k*r) : ℕ) :=
  trdeg_sampledAlphabetStar_coordinateField_le hQ.matchgateIdentities
    (fun l => (hg l).matchgateIdentities)

/-- Proposition 6.4: one positive integer table obstructs every narrower exact
complex-weight graph star, and has all Boolean mode flattenings of rank two. -/
theorem exists_positive_integer_exact_obstruction (k : ℕ) (hk : 2 ≤ k) :
    ∃ a : BooleanTable k ℕ, (∀ z, 0 < a z) ∧
      (∀ (r : ℕ) (g : Fin 2 → BooleanTable r ℂ) (Q : BooleanTable (k*r) ℂ),
        (∀ b, ExactMatchgate (g b)) → ExactMatchgate Q →
        (∀ z, (a z : ℂ) = starContract (fun x => Q (flattenBooleanBlocks x)) (fun i => g (z i))) →
        2^k ≤ 2*delta r + delta (k*r)) ∧
      ∀ i : Fin k, (oneVsRestFlattening (fun z => (a z : ℂ)) i).rank = 2 := by
  obtain ⟨a,ha,hbudget,hrank⟩ := exists_positive_integer_MGI_obstruction k hk
  refine ⟨a,ha,?_,hrank⟩
  intro r g Q hg hQ hrep
  exact hbudget r ⟨g,Q,(fun b => (hg b).matchgateIdentities),hQ.matchgateIdentities,hrep⟩

end
end MatchgateWidth
