import MatchgateWidth.BlockInterpolationPositions
import MatchgateWidth.ScaledCircuitRealization

/-! # Theorem 7.1: exact field-preserving block-Pfaffian interpolation

The arity is explicitly proved to be k * 2^k. Repetition is witnessed as the
literal list of boundary bits in order; the graph is a genuine finite weighted
graph with a continuous ordered disk drawing and all weights in the given field.
-/
namespace MatchgateWidth
noncomputable section

/-- Actual repeated Boolean boundary assignment in the fixed positional order. -/
def interpolationRepeatedBoundary {k : ℕ} (x : Fin k → Bool) :
    Fin (interpolationBoundaryOrder k).length → Bool :=
  fun i => decide (interpolationRepetitionBits x i = 1)

theorem interpolationRepeatedBoundary_word {k : ℕ} (x : Fin k → Bool) :
    List.ofFn (interpolationRepeatedBoundary x) = booleanRepetitionWord x :=
  interpolationRepetitionBits_word x

/-- All clauses of the block-interpolation construction, including the graph
witness, coefficient field, exact scalar and exact ordered repeated inputs. -/
theorem blockPfaffian_interpolation (K : Subfield ℂ) (k : ℕ) (hk : 1 ≤ k)
    (f : Finset (Fin k) → K) (hf : ∀ S, f S ≠ 0) :
    (interpolationBoundaryOrder k).length = k * 2 ^ k ∧
    ∃ (A : Matrix (Fin (interpolationBoundaryOrder k).length)
        (Fin (interpolationBoundaryOrder k).length) K)
      (v e : ℕ) (G : WeightedGraph (Fin v) (Fin e) ℂ)
      (ext : Fin (interpolationBoundaryOrder k).length → Fin v),
      A = interpolationPositionMatrix f hf ∧
      (∀ i j, A i j = -A j i) ∧ (∀ i, A i i = 0) ∧
      principalPfaffian A ∅ = 1 ∧
      Nonempty (PlanarDrawing G ext) ∧ (∀ a, G.weight a ∈ K) ∧
      (∀ y, deletionSignature G ext y = (f ∅ : ℂ) *
        principalPfaffian (fun i j => (A i j : ℂ)) (bridgeBitsEquiv _ y)) ∧
      (∀ y, deletionSignature G ext y ∈ K) ∧
      (∀ x : Fin k → Bool,
        List.ofFn (interpolationRepeatedBoundary x) = booleanRepetitionWord x ∧
        principalPfaffian A (booleanSubsetEquiv _ (interpolationRepetitionBits x)) =
          f (Finset.univ.filter fun i => x i) / f ∅ ∧
        deletionSignature G ext (interpolationRepeatedBoundary x) =
          (f (Finset.univ.filter fun i => x i) : ℂ)) := by
  refine ⟨interpolationBoundaryOrder_length k, ?_⟩
  let A := interpolationPositionMatrix f hf
  let M : Matrix (Fin (interpolationBoundaryOrder k).length)
      (Fin (interpolationBoundaryOrder k).length) ℂ := fun i j => (A i j : ℂ)
  have hn : 0 < (interpolationBoundaryOrder k).length := by
    rw [interpolationBoundaryOrder_length]
    exact Nat.mul_pos (by omega) (pow_pos (by decide) k)
  have ha : ∀ i j, A i j = -A j i := interpolationPositionMatrix_skew f hf
  have ha0 : ∀ i, A i i = 0 := interpolationPositionMatrix_diag f hf
  have hm : ∀ i j, M i j = -M j i := by
    intro i j
    exact congrArg (fun z : K => (z : ℂ)) (ha i j)
  have hm0 : ∀ i, M i i = 0 := by
    intro i
    exact congrArg (fun z : K => (z : ℂ)) (ha0 i)
  obtain ⟨v,e,G,ext,hdraw,hw,hsig⟩ := scaledPrincipalPfaffian_diskWitness
    (f ∅ : ℂ) M hn hm hm0 K (f ∅).property (fun i j _ => (A i j).property)
  have hmap (S) : principalPfaffian M S = ((principalPfaffian A S : K) : ℂ) :=
    pfaffianList_map_ringHom K.subtype A _
  refine ⟨A,v,e,G,ext,rfl,ha,ha0,by simp [principalPfaffian],hdraw,hw,hsig,?_,?_⟩
  · intro y
    rw [hsig, hmap]
    exact K.mul_mem (f ∅).property (principalPfaffian A _).property
  · intro x
    refine ⟨interpolationRepeatedBoundary_word x, interpolationPositionMatrix_repetition f hf x, ?_⟩
    have hb : bridgeBitsEquiv _ (interpolationRepeatedBoundary x) =
        booleanSubsetEquiv _ (interpolationRepetitionBits x) := by
      ext i
      simp [bridgeBitsEquiv, booleanSubsetEquiv, interpolationRepeatedBoundary]
    rw [hsig, hb, hmap, interpolationPositionMatrix_repetition f hf x]
    change ((f ∅ * (f (Finset.univ.filter fun i => x i) / f ∅) : K) : ℂ) = _
    congr 1
    exact mul_div_cancel₀ _ (hf ∅)

end
end MatchgateWidth
