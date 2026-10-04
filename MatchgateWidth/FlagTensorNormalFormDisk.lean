import MatchgateWidth.FlagTensorNormalForm
import MatchgateWidth.PivotCircuitRealization

/-! # Actual disk witnesses for flag-normal-form cores

The incoming tensor is assumed to satisfy the literal ordered MGI. The core
produced by rank-one stripping is then realized by a concrete weighted graph
with an ordered disk drawing. No converse graph-to-MGI axiom is assumed.
-/
namespace MatchgateWidth
noncomputable section

variable {D : Type*} [Fintype D]

/-- The reconstructed flag core has an actual finite weighted graph and disk
drawing, with exactly the claimed Boolean deletion coefficients. -/
theorem fullRank_flag_normal_form_diskWitness {m n t : ℕ}
    (M : Matrix D (BooleanInput t) ℂ)
    (hM : Function.Injective M.transpose.mulVecLin)
    (E : Matrix (BooleanInput 1) D ℂ)
    (C : Matrix (BooleanInput t) (BooleanInput 1) ℂ)
    (hC : OrderedMatchgateMatrix C) (hEC : (E*M)*C = 1)
    (i : Fin m ↪ Fin n) (hi : StrictMono i)
    (T : (Fin n → D) → ℂ)
    (hT : BooleanMatchgateIdentities (leftBooleanLift M n T))
    (hplane : ∀ j, columnSupport (portFlatten T (i j)) ≤
      Submodule.span ℂ (Set.range E.row))
    (q : Fin n → D → ℂ)
    (hq : ∀ j, j ∉ Set.range i →
      columnSupport (portFlatten T j) ≤ Submodule.span ℂ {q j})
    (hqne : ∀ j, j ∉ Set.range i → q j ≠ 0) :
    ∃ (h : BooleanTable m ℂ) (v e : ℕ)
      (G : WeightedGraph (Fin v) (Fin e) ℂ) (ext : Fin m → Fin v),
      BooleanMatchgateIdentities h ∧ T = flagTensor E i q h ∧
      Nonempty (PlanarDrawing G ext) ∧
      ∀ z, deletionSignature G ext z = h ((booleanWordEquiv m).symm z) := by
  obtain ⟨h, hmg, hfac⟩ := fullRank_flag_normal_form M hM E C hC hEC i hi T hT hplane q hq hqne
  obtain ⟨v, e, G, ext, hd, _, hs⟩ := hmg.diskWitness_map_all (RingHom.id ℂ)
  exact ⟨h, v, e, G, ext, hmg, hfac, hd, hs⟩

end
end MatchgateWidth
