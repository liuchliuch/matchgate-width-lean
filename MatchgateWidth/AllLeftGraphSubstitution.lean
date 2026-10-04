import MatchgateWidth.AllLeftWirePorts
import MatchgateWidth.MatchingFamilySubstitution
import MatchgateWidth.InternalBlockCorrection

/-! # Actual all-left local-graph substitution and exact network semantics -/
namespace MatchgateWidth
noncomputable section
open scoped Classical
set_option maxHeartbeats 600000

/-- Finite local matching graphs with literal ordered external vertices. No
output matchgate identity is included in this graph-algebra data. -/
structure LocalMatchingGraphFamily (J : Type*) (arity : J → ℕ) where
  vertices : J → ℕ
  edges : J → ℕ
  graph : ∀ j, WeightedGraph (Fin (vertices j)) (Fin (edges j)) ℂ
  external : ∀ j, Fin (arity j) → Fin (vertices j)
  external_injective : ∀ j, Function.Injective (external j)

namespace LocalMatchingGraphFamily
variable {J : Type*} {arity : J → ℕ}
def signature (F : LocalMatchingGraphFamily J arity) (j : J) : (Fin (arity j) → Bool) → ℂ :=
  deletionSignature (F.graph j) (F.external j)
/-- Exact equality to the requested local coefficients in `Fin 2` coordinates. -/
def Realizes (F : LocalMatchingGraphFamily J arity)
    (T : (j : J) → BooleanTable (arity j) ℂ) : Prop :=
  ∀ j z, F.signature j ((booleanWordEquiv (arity j)) z) = T j z

/-- Independent genuine ordered disk drawings of all local graphs. -/
def DiskDrawn (F : LocalMatchingGraphFamily J arity) : Prop :=
  ∀ j, Nonempty (PlanarDrawing (F.graph j) (F.external j))

/-- Exact tensors provide actual finite local graphs and exact signature
identities, not just a collection of MGI predicates. -/
theorem exists_of_exact (T : (j : J) → BooleanTable (arity j) ℂ)
    (hT : ∀ j, ExactMatchgate (T j)) :
    ∃ F : LocalMatchingGraphFamily J arity, F.DiskDrawn ∧ F.Realizes T := by
  have hw (j : J) := (exactMatchgate_iff_booleanDiskRealizable _).mp (hT j)
  choose nv ne G ext hdraw hval using hw
  let F : LocalMatchingGraphFamily J arity := {
    vertices := nv
    edges := ne
    graph := G
    external := ext
    external_injective := fun j => (Classical.choice (hdraw j)).external_injective }
  refine ⟨F,hdraw,?_⟩
  intro j z
  have hh := hval j ((booleanWordEquiv (arity j)) z)
  change deletionSignature (G j) (ext j) ((booleanWordEquiv (arity j)) z) = T j z
  simpa only [Equiv.symm_apply_apply] using hh.symm

end LocalMatchingGraphFamily

namespace AllLeftGadget
variable {S : LabelledShape} {a b c n t : ℕ} (I : AllLeftGadget S a b c n)

/-- Local family graph data, indexed by the actual primitive occurrences. -/
abbrev LeftMatchingFamily := LocalMatchingGraphFamily (Fin a) (fun v => S.leftArity (I.leftLabel v)*t)
abbrev RightMatchingFamily := LocalMatchingGraphFamily (Fin b) (fun v => S.rightArity (I.rightLabel v)*t)

/-- Substitute disjoint local graphs and add one unit bridge per original
internal Boolean wire, with the proved opposite-position left endpoint. -/
def substitutionGraph (L : I.LeftMatchingFamily (t := t)) (R : I.RightMatchingFamily (t := t)) :=
  substitutedFamilyGraph L.graph R.graph L.external R.external I.internalLeftWire I.internalRightWire

/-- The original ordered external boundary, with its unchanged inherited local
left endpoint at every scalar wire. -/
def substitutionExternal (L : I.LeftMatchingFamily (t := t)) (R : I.RightMatchingFamily (t := t))
    (q : Fin (n*t)) : (Σ v, Fin (L.vertices v)) ⊕ (Σ v, Fin (R.vertices v)) :=
  Sum.inl (sigmaExternal L.external (I.boundaryLeftWire q))

theorem substitutionExternal_injective (L : I.LeftMatchingFamily (t := t)) (R : I.RightMatchingFamily (t := t)) :
    Function.Injective (I.substitutionExternal L R) :=
  Sum.inl_injective.comp ((sigmaExternal_injective L.external L.external_injective).comp
    I.boundaryLeftWire_injective)

/-- The deletion signature of the complete substituted finite graph is exactly
its local-signature network. All local masks are the actual opposite-position
wire indices, and all subset/bit assignments are summed exactly once. -/
theorem substitution_signature (L : I.LeftMatchingFamily (t := t)) (R : I.RightMatchingFamily (t := t))
    (z : Fin (n*t) → Bool) :
    deletionSignature (I.substitutionGraph L R) (I.substitutionExternal L R) z =
      ∑ x : Fin (c*t) → Bool,
        (∏ v, L.signature v (fun k => I.leftWireBits x z ⟨v,k⟩)) *
        ∏ v, R.signature v (fun k => I.rightWireBits x ⟨v,k⟩) := by
  classical
  have hh := deletionSignature_substitutedFamilyGraph L.graph R.graph L.external R.external
    L.external_injective R.external_injective I.internalLeftWire I.internalRightWire
    I.internalLeftWire_injective I.internalRightWire_injective I.boundaryLeftWire
    I.internal_boundary_wire_disjoint z
  change deletionSignature (I.substitutionGraph L R) (I.substitutionExternal L R) z = _ at hh
  rw [hh, ← (bridgeBitsEquiv (Fin (c*t))).sum_comp]
  apply Finset.sum_congr (by ext; simp)
  intro x hx
  simp_rw [I.leftWireBits_eq_selected, I.rightWireBits_eq_selected]
  rfl

/-- Boolean coding preserves every physical left endpoint index: internal
positions are reversed and exposed positions are unchanged. -/
theorem leftWireBits_booleanWord (x : Fin c → BooleanInput t) (z : Fin n → BooleanInput t)
    (v : Fin a) :
    (fun k => I.leftWireBits ((booleanWordEquiv (c*t)) (flattenBooleanBlocks x))
      ((booleanWordEquiv (n*t)) (flattenBooleanBlocks z)) ⟨v,k⟩) =
    (booleanWordEquiv (S.leftArity (I.leftLabel v)*t))
      (flattenBooleanBlocks (I.physicalLeftWords x z v)) := by
  funext h
  obtain ⟨⟨i,k⟩,rfl⟩ := finProdFinEquiv.surjective h
  rw [I.leftWireBits_local]
  cases he : I.leftIncidence ⟨v,i⟩ <;>
    simp [booleanWordEquiv, flattenBooleanBlocks, physicalLeftWords, reverseBlockWord, he]

theorem rightWireBits_booleanWord (x : Fin c → BooleanInput t) (v : Fin b) :
    (fun k => I.rightWireBits ((booleanWordEquiv (c*t)) (flattenBooleanBlocks x)) ⟨v,k⟩) =
    (booleanWordEquiv (S.rightArity (I.rightLabel v)*t))
      (flattenBooleanBlocks (fun i => x (I.rightIncidence ⟨v,i⟩))) := by
  funext h
  obtain ⟨⟨i,k⟩,rfl⟩ := finProdFinEquiv.surjective h
  rw [I.rightWireBits_local]
  simp [booleanWordEquiv, flattenBooleanBlocks]

/-- Full substituted-graph semantics in the presentation's own Boolean word
coordinates, with corrected left locals and inherited external order. -/
theorem substitution_signature_eq_physical_network
    (L : I.LeftMatchingFamily (t := t)) (R : I.RightMatchingFamily (t := t))
    (F : (v : Fin a) → BooleanTable (S.leftArity (I.leftLabel v)*t) ℂ)
    (H : (l : S.RightLabel) → BooleanTable (S.rightArity l*t) ℂ)
    (hL : L.Realizes F) (hR : R.Realizes (fun v => H (I.rightLabel v)))
    (z : Fin n → BooleanInput t) :
    deletionSignature (I.substitutionGraph L R) (I.substitutionExternal L R)
      ((booleanWordEquiv (n*t)) (flattenBooleanBlocks z)) =
        I.internalPhysicalNetwork F H z := by
  rw [I.substitution_signature]
  let e := (booleanBlocksEquiv c t).trans (booleanWordEquiv (c*t))
  rw [← e.sum_comp]
  unfold internalPhysicalNetwork
  apply Finset.sum_congr (by ext; simp)
  intro x hx
  change (∏ v, L.signature v (fun k => I.leftWireBits
    ((booleanWordEquiv (c*t)) (flattenBooleanBlocks x))
    ((booleanWordEquiv (n*t)) (flattenBooleanBlocks z)) ⟨v,k⟩)) *
    (∏ v, R.signature v (fun k => I.rightWireBits
      ((booleanWordEquiv (c*t)) (flattenBooleanBlocks x)) ⟨v,k⟩)) = _
  simp_rw [I.leftWireBits_booleanWord, I.rightWireBits_booleanWord]
  exact congrArg₂ (· * ·) (Finset.prod_congr rfl (fun v _ => hL v _))
    (Finset.prod_congr rfl (fun v _ => hR v _))

/-- Every valid qutrit presentation supplies the exact local graphs used in
its corrected physical substitution. The only later obligation is geometrically
routing this specific finite assembled graph in its specified outer order. -/
theorem exists_corrected_local_graphs
    (p : LabelledCommonPresentation S (Fin 3) t) (hM : p.baseMatrix.rank = 3) :
    ∃ (L : I.LeftMatchingFamily (t := t)) (R : I.RightMatchingFamily (t := t)),
      L.DiskDrawn ∧ R.DiskDrawn ∧
      L.Realizes (I.correctedLeftTensor
        (fun l => leftBooleanLift p.baseMatrix (S.leftArity l) (p.left l))) ∧
      R.Realizes (fun v => p.rightPreimage (I.rightLabel v)) ∧
      ∀ z : BooleanInput (n*t),
        deletionSignature (I.substitutionGraph L R) (I.substitutionExternal L R)
          ((booleanWordEquiv (n*t)) z) = leftBooleanLift p.baseMatrix n (I.value p.language) z := by
  obtain ⟨L,hLd,hL⟩ := LocalMatchingGraphFamily.exists_of_exact
    (I.correctedLeftTensor (fun l => leftBooleanLift p.baseMatrix (S.leftArity l) (p.left l)))
    (I.correctedLeftTensor_exact p hM)
  obtain ⟨R,hRd,hR⟩ := LocalMatchingGraphFamily.exists_of_exact
    (fun v => p.rightPreimage (I.rightLabel v))
    (fun v => (exactMatchgate_iff_booleanDiskRealizable _).mpr (p.validRight (I.rightLabel v)))
  refine ⟨L,R,hLd,hRd,hL,hR,?_⟩
  intro z
  have hh := I.substitution_signature_eq_physical_network L R _ p.rightPreimage hL hR
    ((booleanBlocksEquiv n t).symm z)
  have hz : flattenBooleanBlocks ((booleanBlocksEquiv n t).symm z) = z :=
    (booleanBlocksEquiv n t).apply_symm_apply z
  rw [hz, I.internalPhysicalNetwork_presentation_eq_lift] at hh
  exact hh

end AllLeftGadget
end
end MatchgateWidth
