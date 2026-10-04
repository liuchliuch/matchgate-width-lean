import MatchgateWidth.IntegerDomainBoundCorollary
import MatchgateWidth.ControlledRationalRealization

/-! # Rational coefficients give actual rational-edge common presentations

This uses the previously proved field-preserving graph realization theorem;
no new geometric characterization or embedding normalization is assumed.
-/
namespace MatchgateWidth
noncomputable section
open scoped Classical

/-- Actual ordered finite rational-edge disk graph for this Boolean tensor. -/
def RationalEdgeDiskRealizable {n : ℕ} (f : BooleanTable n ℂ) : Prop :=
  ∃ (v e : ℕ) (G : WeightedGraph (Fin v) (Fin e) ℂ) (ext : Fin n → Fin v),
    Nonempty (PlanarDrawing G ext) ∧ (∀ a, ∃ q : ℚ, G.weight a = q) ∧
    ∀ y, deletionSignature G ext y = f ((booleanWordEquiv n).symm y)

theorem BooleanDiskRealizable.rational_edges {n : ℕ} {f : BooleanTable n ℂ}
    (hf : BooleanDiskRealizable f) (hq : ∀ z, f z ∈ rationalComplexField) :
    RationalEdgeDiskRealizable f := by
  obtain ⟨v,e,G,ext,hd,hw,hs⟩ := hf.field_preserving rationalComplexField hq
  refine ⟨v,e,G,ext,hd,?_,hs⟩
  intro a
  obtain ⟨q,hq⟩ := (RingHom.mem_fieldRange).mp (hw a)
  exact ⟨q,hq.symm⟩

/-- Both sides of the same displayed common presentation have actual graphs
with rational edge weights and the prescribed original Boolean port order. -/
def RationalGraphPresentation {S : LabelledShape} {E : Type} [Fintype E]
    {r : ℕ} (p : LabelledCommonPresentation S E r) : Prop :=
  (∀ l, RationalEdgeDiskRealizable
    (fun z => leftTransform p.base (p.left l) (fun i t => z (finProdFinEquiv (i,t))))) ∧
  (∀ l, RationalEdgeDiskRealizable (p.rightPreimage l))

/-- Source rational coefficients faithfully imply rational edge realizations
for the full displayed presentation, including zero/nullary components. -/
theorem RationalCoefficientPresentation.rational_graphs {S : LabelledShape} {E : Type}
    [Fintype E] {r : ℕ} {p : LabelledCommonPresentation S E r}
    (hp : RationalCoefficientPresentation p) : RationalGraphPresentation p := by
  have hbase (d : E) (z : BooleanInput r) : p.base d z ∈ rationalComplexField := by
    obtain ⟨q,hq⟩ := hp.1 d z
    rw [hq]
    exact rationalComplexField_mem q
  have hleft (l : S.LeftLabel) (x : Fin (S.leftArity l) → E) :
      p.left l x ∈ rationalComplexField := by
    obtain ⟨q,hq⟩ := hp.2.1 l x
    rw [hq]
    exact rationalComplexField_mem q
  refine ⟨?_,?_⟩
  · intro l
    apply (p.validLeft l).rational_edges
    intro z
    unfold leftTransform
    apply rationalComplexField.sum_mem
    intro x hx
    apply rationalComplexField.mul_mem (hleft l x)
    apply rationalComplexField.prod_mem
    intro i hi
    exact hbase _ _
  · intro l
    apply (p.validRight l).rational_edges
    intro z
    obtain ⟨q,hq⟩ := hp.2.2 l z
    rw [hq]
    exact rationalComplexField_mem q

theorem integerRationalPresentation_rational_graphs (k : ℕ) (hk : 2 ≤ k) :
    RationalGraphPresentation (integerRationalPresentation k hk) :=
  (integerRationalPresentation_rational k hk).rational_graphs

/-- Corollary 3.2 with rational-edge graphs explicitly required of the displayed
input; arbitrary complex competing presentations remain admissible. -/
theorem no_universal_domain_bound_even_rational_graphs
    (C : ∀ S : LabelledShape, LabelledInstanceClass S)
    (hC : ∀ S, ContainsOrderedPlanar (C S)) :
    ¬ ∃ h : ℕ → ℕ,
      ∀ (S : LabelledShape) (E : Type) (_ : Fintype E) (_ : Nonempty E)
        (r : ℕ) (p : LabelledCommonPresentation S E r),
      RationalCoefficientPresentation p → RationalGraphPresentation p →
      IntegerPositiveDeficient p.language →
      ∃ s, HasExactCommonWidthOn (C S) p.language s ∧ s ≤ h (Fintype.card E) := by
  rintro ⟨h,hh⟩
  apply no_universal_domain_width_bound_even_rational C hC
  exact ⟨h,fun S E _ _ r p hq hi => hh S E inferInstance inferInstance r p hq
    hq.rational_graphs hi⟩

end
end MatchgateWidth
