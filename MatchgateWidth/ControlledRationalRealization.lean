import MatchgateWidth.AlgebraicQutritLanguage
import MatchgateWidth.ScaledCircuitRealization

/-! # Actual rational planar realization of the controlled right preimage -/
namespace MatchgateWidth
noncomputable section

/-- The rational coefficient field as an actual complex subfield. -/
def rationalComplexField : Subfield ℂ := (Rat.castHom ℂ).fieldRange

theorem rationalComplexField_mem (q : ℚ) : (q : ℂ) ∈ rationalComplexField :=
  (Rat.castHom ℂ).mem_fieldRange_self q

/-- Field-preserving graph realization in the exact supplied boundary-list order. -/
theorem rational_orderedPfaffian_diskWitness {I : Type*}
    (xs : List I) (hnodup : xs.Nodup) (hall : ∀ i, i ∈ xs) (hlen : 0 < xs.length)
    (A : Matrix I I ℚ) (hA : ∀ i j, A i j = -A j i) (hdiag : ∀ i, A i i = 0)
    (c : ℚ) :
    ∃ (v e : ℕ) (G : WeightedGraph (Fin v) (Fin e) ℂ) (ext : Fin xs.length → Fin v),
      Nonempty (PlanarDrawing G ext) ∧ (∀ a, ∃ q : ℚ, G.weight a = q) ∧
      ∀ z : BooleanInput xs.length,
        deletionSignature G ext (booleanWordEquiv xs.length z) =
          ((c * pfaffianList A (xs.filter (orderedBooleanAssignment xs hnodup hall z)) : ℚ) : ℂ) := by
  let B := A.submatrix xs.get xs.get
  let M : Matrix (Fin xs.length) (Fin xs.length) ℂ := fun i j => (B i j : ℂ)
  have hm : ∀ i j, M i j = -M j i := by
    intro i j
    simpa [M, B] using congrArg (fun q : ℚ => (q : ℂ)) (hA (xs.get i) (xs.get j))
  have hm0 : ∀ i, M i i = 0 := by
    intro i
    simpa [M, B] using congrArg (fun q : ℚ => (q : ℂ)) (hdiag (xs.get i))
  obtain ⟨v,e,G,ext,hd,hw,hg⟩ := scaledPrincipalPfaffian_diskWitness
    (c : ℂ) M hlen hm hm0 rationalComplexField (rationalComplexField_mem c)
    (fun i j _ => rationalComplexField_mem (B i j))
  refine ⟨v,e,G,ext,hd,?_,?_⟩
  · intro a
    obtain ⟨q,hq⟩ := (RingHom.mem_fieldRange).mp (hw a)
    exact ⟨q,hq.symm⟩
  · intro z
    rw [hg]
    have hb : bridgeBitsEquiv _ (booleanWordEquiv xs.length z) = booleanSubsetEquiv _ z := by
      ext i
      simp [bridgeBitsEquiv, booleanWordEquiv, booleanSubsetEquiv]
    rw [hb]
    have hp : principalPfaffian M (booleanSubsetEquiv _ z) =
        ((principalPfaffian B (booleanSubsetEquiv _ z) : ℚ) : ℂ) :=
      pfaffianList_map_ringHom (Rat.castHom ℂ) B _
    rw [hp, orderedPfaffianSignature_eq xs hnodup hall A c z]
    push_cast
    rfl

/-- The actual canonical controlled right signature has a rational-edge disk
realization at its full ordered Boolean arity. -/
theorem controlledBooleanPreimage_rational_diskWitness {k : ℕ}
    (f : BooleanTable k ℚ) (hf : ∀ x, f x ≠ 0) (j : Fin k) :
    ∃ (v e : ℕ) (G : WeightedGraph (Fin v) (Fin e) ℂ)
      (ext : Fin (controlledPhysicalOrder k).length → Fin v),
      Nonempty (PlanarDrawing G ext) ∧ (∀ a, ∃ q : ℚ, G.weight a = q) ∧
      ∀ z, deletionSignature G ext (booleanWordEquiv _ z) =
        ((controlledBooleanPreimage f hf j z : ℚ) : ℂ) := by
  have hn : 0 < (controlledPhysicalOrder k).length := by
    rw [controlledPhysicalOrder_length]
    positivity
  exact rational_orderedPfaffian_diskWitness
    (controlledPhysicalOrder k) (controlledPhysicalOrder_nodup k)
    mem_controlledPhysicalOrder hn
    (controlledPhysicalMatrix (booleanSubsetTable f) (fun _ => hf _) j)
    (controlledPhysicalMatrix_skew _ _ _) (controlledPhysicalMatrix_diag _ _ _)
    (booleanSubsetTable f ∅)

end
end MatchgateWidth
