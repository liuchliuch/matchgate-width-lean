import MatchgateWidth.AlgebraicObstruction
import MatchgateWidth.ControlledPfaffian

/-!
# The assembled rank and support conclusion of Proposition 8.2

We select a positive natural-number table whose Boolean flattenings have rank
exactly two over `ℂ`, then carry out the actual canonical Pfaffian construction
over `ℂ`. Thus this theorem does not assume rank preservation from `ℚ` to `ℂ`.
The right tensor is the literal `rightTransform` of the constructed physical
signature, and its coordinate formula follows from the proved Pfaffian identity.

The preserved obstruction concerns the algebraic MGI-star representation locus.
No planar realization, planar width obstruction, or validity claim from
Proposition 8.1 is assumed or concluded here.
-/

namespace MatchgateWidth
noncomputable section
open scoped Classical

/-- The zero-one plane is literally the span of the indicated basis vectors. -/
theorem qutritCoordinatePlane_two_eq_span {K : Type*} [Field K] :
    qutritCoordinatePlane (K := K) 2 =
      Submodule.span K ({Pi.single 0 (1 : K), Pi.single 1 (1 : K)} :
        Set (Fin 3 → K)) := by
  apply le_antisymm
  · intro v hv
    apply Submodule.mem_span_pair.mpr
    refine ⟨v 0, v 1, ?_⟩
    have hv' : v 2 = 0 := hv
    ext i
    fin_cases i <;> simp [hv']
  · apply Submodule.span_le.mpr
    intro v hv
    rcases hv with rfl | hv
    · simp
    · obtain rfl := Set.mem_singleton_iff.mp hv
      simp

/-- The zero-two plane is literally the span of the indicated basis vectors. -/
theorem qutritCoordinatePlane_one_eq_span {K : Type*} [Field K] :
    qutritCoordinatePlane (K := K) 1 =
      Submodule.span K ({Pi.single 0 (1 : K), Pi.single 2 (1 : K)} :
        Set (Fin 3 → K)) := by
  apply le_antisymm
  · intro v hv
    apply Submodule.mem_span_pair.mpr
    refine ⟨v 0, v 2, ?_⟩
    have hv' : v 1 = 0 := hv
    ext i
    fin_cases i <;> simp [hv']
  · apply Submodule.span_le.mpr
    intro v hv
    rcases hv with rfl | hv
    · simp
    · obtain rfl := Set.mem_singleton_iff.mp hv
      simp

/-- The actual complex right tensor obtained from positive natural data. -/
def positiveControlledRightTensor {k : ℕ} (a : BooleanTable k ℕ)
    (ha : ∀ x, 0 < a x) (j : Fin k) :
    (ControlledQutritPort k → Fin 3) → ℂ :=
  rightTransform (controlledCoordinateBase k)
    (controlledPhysicalSignature (booleanSubsetTable (fun x => (a x : ℂ)))
      (fun _S => Nat.cast_ne_zero.mpr (Nat.ne_of_gt (ha _))) j)

/-- This is an identity for the constructed Pfaffian tensor, not a hypothesis. -/
theorem positiveControlledRightTensor_eq {k : ℕ} (a : BooleanTable k ℕ)
    (ha : ∀ x, 0 < a x) (j : Fin k) :
    positiveControlledRightTensor a ha j = controlledQutrit (fun x => (a x : ℂ)) j := by
  exact controlledPhysicalSignature_boolean_rightTransform (fun x => (a x : ℂ))
    (fun x => Nat.cast_ne_zero.mpr (Nat.ne_of_gt (ha x))) j

/-- Proposition 8.2's complete rank and support package, for every `k ≥ 2`
and designated hard port. All input nonvanishing and rank facts are obtained
from the proved positive-integer table selection. The left family consists of
all three pins and `X01`; right support-essentiality uses `R` alone. -/
theorem exists_controlled_ranks_and_support_proposition (k : ℕ) (hk : 2 ≤ k)
    (j : Fin k) :
    ∃ (a : BooleanTable k ℕ) (ha : ∀ x, 0 < a x),
      let R := positiveControlledRightTensor a ha j
      (∀ r, HasMGIStarRepresentation k r (fun x => (a x : ℂ)) → 2 ^ k ≤ D k r) ∧
      (∀ i : Fin k, (oneVsRestFlattening (fun x => (a x : ℂ)) i).rank = 2) ∧
      R = controlledQutrit (fun x => (a x : ℂ)) j ∧
      (∀ r : Fin 3, ∀ p : Fin 1,
        (portFlatten (qutritPinTensor (K := ℂ) r) p).rank = 1) ∧
      (∀ l : Fin 2, (portFlatten (qutritNeqTensor (K := ℂ)) l).rank = 2) ∧
      (∀ p : ControlledQutritPort k, (portFlatten R p).rank = 2) ∧
      (∀ l : Fin 2, columnSupport (portFlatten R (Sum.inl l)) =
        Submodule.span ℂ ({Pi.single 0 (1 : ℂ), Pi.single 1 (1 : ℂ)} :
          Set (Fin 3 → ℂ))) ∧
      (∀ i : Fin k, columnSupport (portFlatten R (Sum.inr i)) =
        Submodule.span ℂ ({Pi.single 0 (1 : ℂ), Pi.single 2 (1 : ℂ)} :
          Set (Fin 3 → ℂ))) ∧
      ((⨆ r : Fin 3, columnSupport (portFlatten (qutritPinTensor (K := ℂ) r) 0)) ⊔
        (⨆ l : Fin 2, columnSupport (portFlatten (qutritNeqTensor (K := ℂ)) l)) = ⊤) ∧
      (⨆ p : ControlledQutritPort k, columnSupport (portFlatten R p)) = ⊤ := by
  obtain ⟨a, ha, hbudget, hrank⟩ := exists_positive_integer_MGI_obstruction k hk
  have hnonzero : ∀ x, (a x : ℂ) ≠ 0 :=
    fun x => Nat.cast_ne_zero.mpr (Nat.ne_of_gt (ha x))
  refine ⟨a, ha, ?_⟩
  dsimp only
  rw [positiveControlledRightTensor_eq]
  refine ⟨hbudget, hrank, rfl, ?_, qutritNeq_rank, ?_, ?_, ?_,
    qutritPins_and_neq_support_essential, ?_⟩
  · intro r p
    fin_cases p
    exact qutritPin_rank r
  · exact controlledQutrit_all_port_ranks _ j (hnonzero _) hrank
  · intro l
    rw [controlledQutrit_link_support _ j (hnonzero _) l,
      qutritCoordinatePlane_two_eq_span]
  · intro i
    rw [controlledQutrit_hard_support _ j i (hrank i),
      qutritCoordinatePlane_one_eq_span]
  · exact controlledQutrit_support_essential _ j (hnonzero _) (hrank j)

end
end MatchgateWidth
