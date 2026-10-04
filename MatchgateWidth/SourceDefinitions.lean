import MatchgateWidth.LabelledInstanceClasses
import MatchgateWidth.SourceSupportTrichotomy

/-! # Explicit source-definition interfaces
The class parameter retains actual incidence, marked port order and labels.
It does not authorize a change of graph or normalization of partition values.
-/
namespace MatchgateWidth
noncomputable section
open scoped Classical

/-- Definition 2.1 in the chosen ordered-planar representative model is exactly
the instance-class definition specialized to its actual geometric predicate. -/
theorem exactlyLabelledEquivalent_iff_on {S T : LabelledShape} {D E : Type}
    [Fintype D] [Fintype E] (F : LabelledLanguage S D) (G : LabelledLanguage T E) :
    ExactlyLabelledEquivalent F G ↔ ExactlyLabelledEquivalentOn
      (fun _ _ _ I => Nonempty I.OrderedPlanar) F G := Iff.rfl

/-- Definition 2.2 for any chosen full instance class, with nonemptiness made
explicit rather than an assumed minimizing presentation. -/
def minimumExactCommonWidthOn {S : LabelledShape} {D : Type} [Fintype D]
    (C : LabelledInstanceClass S) (F : LabelledLanguage S D)
    (h : ∃ r, HasExactCommonWidthOn C F r) : ℕ := Nat.find h

theorem minimumExactCommonWidthOn_spec {S : LabelledShape} {D : Type} [Fintype D]
    (C : LabelledInstanceClass S) (F : LabelledLanguage S D)
    (h : ∃ r, HasExactCommonWidthOn C F r) :
    HasExactCommonWidthOn C F (minimumExactCommonWidthOn C F h) := Nat.find_spec h

theorem minimumExactCommonWidthOn_le {S : LabelledShape} {D : Type} [Fintype D]
    (C : LabelledInstanceClass S) (F : LabelledLanguage S D)
    (h : ∃ r, HasExactCommonWidthOn C F r) {r : ℕ}
    (hr : HasExactCommonWidthOn C F r) : minimumExactCommonWidthOn C F h ≤ r :=
  Nat.find_min' h hr

namespace LabelledCommonPresentation
variable {S : LabelledShape} {D : Type} [Fintype D] {t : ℕ}

/-- Every valid displayed presentation supplies a finite-width witness on
any instance class, using the same domain, labels, graph and exact values. -/
theorem hasExactCommonWidthOn [Nonempty D] (p : LabelledCommonPresentation S D t)
    (C : LabelledInstanceClass S) : HasExactCommonWidthOn C p.language t :=
  ⟨D,inferInstance,inferInstance,S,p,ExactlyLabelledEquivalentOn.refl C _⟩

theorem finiteWidthOn [Nonempty D] (p : LabelledCommonPresentation S D t)
    (C : LabelledInstanceClass S) : ∃ r, HasExactCommonWidthOn C p.language r :=
  ⟨t,p.hasExactCommonWidthOn C⟩

/-- Definition 4.4 uses literal left/right transforms and exact ordered graph
signatures under the one common base. -/
theorem exactValidity (p : LabelledCommonPresentation S D t) :
    (∀ l, ExactMatchgate (fun z => leftTransform p.base (p.left l)
      (fun i j => z (finProdFinEquiv (i,j))))) ∧
    (∀ l, ExactMatchgate (p.rightPreimage l)) :=
  ⟨fun l => (p.validLeft l).matchgateIdentities.exactMatchgate,
   fun l => (p.validRight l).matchgateIdentities.exactMatchgate⟩

end LabelledCommonPresentation

/-- Conversely the displayed source validity conditions build the presentation
record; no rank, support, normalization or coefficient-field hypothesis is added. -/
def presentationOfExact {S : LabelledShape} {D : Type} [Fintype D] {t : ℕ}
    (M : D → BooleanInput t → ℂ)
    (F : (l : S.LeftLabel) → (Fin (S.leftArity l) → D) → ℂ)
    (H : (l : S.RightLabel) → BooleanTable (S.rightArity l*t) ℂ)
    (hF : ∀ l, ExactMatchgate (fun z => leftTransform M (F l)
      (fun i j => z (finProdFinEquiv (i,j)))))
    (hH : ∀ l, ExactMatchgate (H l)) : LabelledCommonPresentation S D t where
  base := M
  left := F
  rightPreimage := H
  validLeft l := (hF l).matchgateIdentities.diskRealizable
  validRight l := (hH l).matchgateIdentities.diskRealizable

/-- Definition 4.5 is literally the realized support-set flag, with the two
parity rays pulled back through the displayed base. -/
theorem allLeftMonomialFlag_iff {S : LabelledShape} {t : ℕ}
    (p : LabelledCommonPresentation S (Fin 3) t)
    (P L : Submodule ℂ (Fin 3 → ℂ)) :
    AllLeftMonomialFlag p P L ↔
      P ∈ allLeftRealizedSupports p.language 2 ∧
      L ∈ allLeftRealizedSupports p.language 1 ∧ ¬L≤P ∧
      allLeftRealizedSupports p.language 2 = {P} ∧
      allLeftRealizedSupports p.language 1 ⊆
        {primitiveParityEndpoint p.baseMatrix P 0,primitiveParityEndpoint p.baseMatrix P 1,L} :=
  Iff.rfl

/-- The connection-prime definition uses only the actual support closure,
its spanning property and absence of a monomial flag. -/
theorem allLeftConnectionPrime_iff {S : LabelledShape} {t : ℕ}
    (p : LabelledCommonPresentation S (Fin 3) t) :
    AllLeftConnectionPrime p ↔
      sSup (allLeftRealizedSupports p.language 1 ∪ allLeftRealizedSupports p.language 2)=⊤ ∧
      (allLeftRealizedSupports p.language 2).Nonempty ∧
      ¬∃ P L, AllLeftMonomialFlag p P L := Iff.rfl

end
end MatchgateWidth
