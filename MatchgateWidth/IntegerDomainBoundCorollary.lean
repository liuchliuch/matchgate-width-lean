import MatchgateWidth.IntegerSourceWidth
import MatchgateWidth.ControlledLabelledRanks
import MatchgateWidth.RationalControlledLabelledPresentation

/-! # Corollary 3.2 with the universal presentation quantifiers

There is no domain-cardinality bound even after restricting the displayed
presentation to rational coefficients. Every competing exact presentation
still has arbitrary complex weights and an arbitrary nonempty finite domain.
The source instance class is a parameter independent of tensor values.
-/
namespace MatchgateWidth
noncomputable section
open scoped Classical
set_option maxHeartbeats 800000

/-- The induced domain language, on both sides, has integer coordinates,
positive arities, and no full-rank port. -/
def IntegerPositiveDeficient {S : LabelledShape} {E : Type} [Fintype E]
    (F : LabelledLanguage S E) : Prop :=
  (∀ l x, ∃ z : ℤ, F.left l x = z) ∧
  (∀ l x, ∃ z : ℤ, F.right l x = z) ∧
  (∀ l, 0 < S.leftArity l) ∧ (∀ l, 0 < S.rightArity l) ∧
  (∀ l p, (portFlatten (F.left l) p).rank < Fintype.card E) ∧
  (∀ l p, (portFlatten (F.right l) p).rank < Fintype.card E)

theorem integerControlledLanguage_qualifies (k : ℕ) (hk : 2 ≤ k) :
    IntegerPositiveDeficient (integerControlledLanguage k hk) := by
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · intro l x
    cases l with
    | inl r =>
      simp only [integerControlledLanguage, controlledLabelledLanguage, coordinatePin]
      split_ifs
      · exact ⟨1,by simp⟩
      · exact ⟨0,by simp⟩
    | inr u =>
      exact controlledLanguageTensor_integer (integerHardTableIn ℂ k)
        (integerHardTableIn_integer ℂ k) (integerControlPort k hk) .neq x
  · intro l x
    exact controlledQutrit_integer_coordinates (integerHardTableIn ℂ k)
      (integerHardTableIn_integer ℂ k) (integerControlPort k hk) _
  · intro l
    cases l <;> norm_num [starLanguageShape]
  · intro l
    change 0 < k + 2
    omega
  · intro l p
    cases l with
    | inl r =>
      have hp : p = 0 := Subsingleton.elim _ _
      subst p
      have h := qutritPin_rank (K := ℂ) r
      have he : (integerControlledLanguage k hk).left (Sum.inl r) = qutritPinTensor r := by
        funext x
        simp [integerControlledLanguage, controlledLabelledLanguage, coordinatePin, qutritPinTensor, eq_comm]
      rw [he]
      simpa only [Matrix.rank, Matrix.range_mulVecLin] using (show
        (portFlatten (qutritPinTensor (K := ℂ) r) 0).rank < Fintype.card (Fin 3) by rw [h]; decide)
    | inr u =>
      change (portFlatten (qutritNeqTensor (K := ℂ)) p).rank < 3
      rw [qutritNeq_rank]
      decide
  · intro l p
    change (portFlatten (orderedControlledQutrit (integerHardTableIn ℂ k)
      (integerControlPort k hk)) p).rank < 3
    rw [orderedControlledQutrit_port_rank _ (integerHardTableIn_ne_zero ℂ k) _
      (integerHardTable_ranks k hk)]
    decide

/-- The chosen integer language is exactly the language induced by this
rational-coefficient valid presentation. -/
def integerRationalPresentation (k : ℕ) (hk : 2 ≤ k) :
    LabelledCommonPresentation (starLanguageShape (k + 2)) (Fin 3) (2 ^ k + 3) :=
  rationalControlledLabelledPresentation (integerHardTableIn ℚ k)
    (integerHardTableIn_ne_zero ℚ k) (integerControlPort k hk)

theorem integerRationalPresentation_language (k : ℕ) (hk : 2 ≤ k) :
    (integerRationalPresentation k hk).language = integerControlledLanguage k hk := by
  rw [integerRationalPresentation, rationalControlledLabelledPresentation_language]
  have he : (fun x => ((integerHardTableIn ℚ k x : ℚ) : ℂ)) = integerHardTableIn ℂ k := by
    funext x
    simp [integerHardTableIn]
  rw [he]
  rfl

theorem integerRationalPresentation_rational (k : ℕ) (hk : 2 ≤ k) :
    RationalCoefficientPresentation (integerRationalPresentation k hk) :=
  rationalControlledLabelledPresentation_rational _ _ _

/-- Corollary 3.2. A purported bound cannot supply even one equivalent
presentation below the bound, which is equivalent to bounding the minimum.
The displayed input is rational, but this restriction is absent from the
competing `HasExactCommonWidthOn` quantifier. -/
theorem no_universal_domain_width_bound_even_rational
    (C : ∀ S : LabelledShape, LabelledInstanceClass S)
    (hC : ∀ S, ContainsOrderedPlanar (C S)) :
    ¬ ∃ h : ℕ → ℕ,
      ∀ (S : LabelledShape) (E : Type) (_ : Fintype E) (_ : Nonempty E)
        (r : ℕ) (p : LabelledCommonPresentation S E r),
      RationalCoefficientPresentation p → IntegerPositiveDeficient p.language →
      ∃ s, HasExactCommonWidthOn (C S) p.language s ∧ s ≤ h (Fintype.card E) := by
  rintro ⟨h,hh⟩
  let k := 4 * h 3 + 8
  have hk : 2 ≤ k := by omega
  obtain ⟨s,hs,hsmall⟩ := hh (starLanguageShape (k + 2)) (Fin 3) inferInstance inferInstance
    (2 ^ k + 3) (integerRationalPresentation k hk)
    (integerRationalPresentation_rational k hk)
    (by rw [integerRationalPresentation_language]; exact integerControlledLanguage_qualifies k hk)
  rw [integerRationalPresentation_language] at hs
  have hb := integer_main_width_budget k hk (hs.restrict (hC _))
  have hm := D_mono_width k (show s ≤ h 3 by simpa using hsmall)
  have hx := budget_lt_two_pow_at_explicit_arity (h 3)
  change D k (h 3) < 2 ^ k at hx
  omega

/-- Removing the rational restriction can only strengthen the impossible
universal bound. -/
theorem no_universal_domain_width_bound
    (C : ∀ S : LabelledShape, LabelledInstanceClass S)
    (hC : ∀ S, ContainsOrderedPlanar (C S)) :
    ¬ ∃ h : ℕ → ℕ,
      ∀ (S : LabelledShape) (E : Type) (_ : Fintype E) (_ : Nonempty E)
        (r : ℕ) (p : LabelledCommonPresentation S E r),
      IntegerPositiveDeficient p.language →
      ∃ s, HasExactCommonWidthOn (C S) p.language s ∧ s ≤ h (Fintype.card E) := by
  rintro ⟨h,hh⟩
  apply no_universal_domain_width_bound_even_rational C hC
  exact ⟨h,fun S E _ _ r p _ hp => hh S E inferInstance inferInstance r p hp⟩

end
end MatchgateWidth
