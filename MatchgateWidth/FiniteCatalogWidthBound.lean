import MatchgateWidth.LabelledInstances
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Card

/-!
# Finite coefficient catalogs have a finite maximum exact width

This is the elementary, non-effective observation in the bounded-arity open
questions: after fixing the domain size, arity bound, total label bound, and a
finite coefficient alphabet, there are finitely many canonically named labelled
languages. Consequently, the minimum admitted widths have a finite maximum.

The admissibility predicate is arbitrary: it may use the full source instance
class, without identifying that class with the geometric model in this project.
The specialization to `HasExactCommonWidth` uses that model literally. Neither
result supplies a decision procedure, a computable bound, nor a structural bound
without the coefficient restriction. The explicit rational alphabet includes
all rationals whose reduced numerator magnitude and positive denominator are at
most `2^B`, hence covers the usual stricter B-bit convention as well.
-/
namespace MatchgateWidth
noncomputable section
open scoped Classical

/-- Canonically named bipartite shapes: two initial segments of natural numbers,
with at most `m` labels in total and every arity at most `a`. Zero arities and
empty label sets are allowed; equal tensors at different labels remain distinct.
-/
abbrev FiniteCatalogShape (a m : ℕ) :=
  {s : Σ l : Fin (m + 1), Σ r : Fin (m + 1),
    (Fin l.val → Fin (a + 1)) × (Fin r.val → Fin (a + 1)) //
    s.1.val + s.2.1.val ≤ m}

namespace FiniteCatalogShape
variable {a m : ℕ}

def toLabelledShape (s : FiniteCatalogShape a m) : LabelledShape where
  LeftLabel := Fin s.val.1.val
  RightLabel := Fin s.val.2.1.val
  leftFinite := inferInstance
  rightFinite := inferInstance
  leftArity l := (s.val.2.2.1 l).val
  rightArity l := (s.val.2.2.2 l).val

theorem label_count_le (s : FiniteCatalogShape a m) :
    Fintype.card s.toLabelledShape.LeftLabel +
      Fintype.card s.toLabelledShape.RightLabel ≤ m := by
  change Fintype.card (Fin s.val.1.val) + Fintype.card (Fin s.val.2.1.val) ≤ m
  simpa only [Fintype.card_fin] using s.property

theorem left_arity_le (s : FiniteCatalogShape a m)
    (l : s.toLabelledShape.LeftLabel) : s.toLabelledShape.leftArity l ≤ a :=
  Nat.le_of_lt_succ (s.val.2.2.1 l).isLt

theorem right_arity_le (s : FiniteCatalogShape a m)
    (l : s.toLabelledShape.RightLabel) : s.toLabelledShape.rightArity l ≤ a :=
  Nat.le_of_lt_succ (s.val.2.2.2 l).isLt

/-- Every bounded shape has a representative with these canonical label names.
The equivalence preserves each port's index, not just its cyclic order. -/
def ofShape (S : LabelledShape)
    (hcount : Fintype.card S.LeftLabel + Fintype.card S.RightLabel ≤ m)
    (hleft : ∀ l, S.leftArity l ≤ a) (hright : ∀ l, S.rightArity l ≤ a) :
    FiniteCatalogShape a m :=
  ⟨⟨⟨Fintype.card S.LeftLabel, by omega⟩,
      ⟨Fintype.card S.RightLabel, by omega⟩,
      (fun l => ⟨S.leftArity ((Fintype.equivFin S.LeftLabel).symm l),
        Nat.lt_succ_of_le (hleft _)⟩),
      (fun l => ⟨S.rightArity ((Fintype.equivFin S.RightLabel).symm l),
        Nat.lt_succ_of_le (hright _)⟩)⟩, hcount⟩

def ofShapeEquiv (S : LabelledShape)
    (hcount : Fintype.card S.LeftLabel + Fintype.card S.RightLabel ≤ m)
    (hleft : ∀ l, S.leftArity l ≤ a) (hright : ∀ l, S.rightArity l ≤ a) :
    LabelledShapeEquiv (ofShape S hcount hleft hright).toLabelledShape S where
  left := (Fintype.equivFin S.LeftLabel).symm
  right := (Fintype.equivFin S.RightLabel).symm
  leftArity _ := rfl
  rightArity _ := rfl

end FiniteCatalogShape

/-- All coefficient tables for one canonical shape over the `q`-element domain.
A coefficient alphabet may have redundant codes; injectivity is unnecessary. -/
abbrev FiniteCatalogTables (q : ℕ) {a m : ℕ} (s : FiniteCatalogShape a m)
    (A : Type) :=
  ((l : s.toLabelledShape.LeftLabel) →
    (Fin (s.toLabelledShape.leftArity l) → Fin q) → A) ×
  ((l : s.toLabelledShape.RightLabel) →
    (Fin (s.toLabelledShape.rightArity l) → Fin q) → A)

/-- The finite catalog simultaneously includes every bounded shape and every
ordered tensor table on that shape, including repeated labels/tensors. -/
abbrev FiniteLanguageCatalog (q a m : ℕ) (A : Type) :=
  Σ s : FiniteCatalogShape a m, FiniteCatalogTables q s A

instance finiteCatalogTablesFintype (q : ℕ) {a m : ℕ}
    (s : FiniteCatalogShape a m) (A : Type) [Fintype A] :
    Fintype (FiniteCatalogTables q s A) := by
  unfold FiniteCatalogTables FiniteCatalogShape.toLabelledShape
  infer_instance

/-- Finiteness comes from finite dependent sums and finite function spaces. -/
theorem finiteLanguageCatalog_finite (q a m : ℕ) (A : Type) [Fintype A] :
    Finite (FiniteLanguageCatalog q a m A) := inferInstance

namespace FiniteLanguageCatalog
variable {q a m : ℕ} {A : Type}

/-- Interpret coefficient codes as actual complex signature entries. -/
def language (c : FiniteLanguageCatalog q a m A) (coefficient : A → ℂ) :
    LabelledLanguage c.1.toLabelledShape (Fin q) where
  left l x := coefficient (c.2.1 l x)
  right l x := coefficient (c.2.2 l x)

/-- The actual interpreted languages form a finite set, even when decoding has
collisions. The sigma records the shape as well as every labelled tensor. -/
theorem finite_languages [Fintype A] (coefficient : A → ℂ) :
    (Set.range (fun c : FiniteLanguageCatalog q a m A =>
      (⟨c.1.toLabelledShape, c.language coefficient⟩ :
        Σ S : LabelledShape, LabelledLanguage S (Fin q)))).Finite :=
  Set.finite_range _

/-- Every table whose entries lie in the alphabet is included in the catalog. -/
theorem covers_language (s : FiniteCatalogShape a m) (coefficient : A → ℂ)
    (F : LabelledLanguage s.toLabelledShape (Fin q))
    (hleft : ∀ l x, ∃ v, coefficient v = F.left l x)
    (hright : ∀ l x, ∃ v, coefficient v = F.right l x) :
    ∃ t : FiniteCatalogTables q s A,
      language (⟨s, t⟩ : FiniteLanguageCatalog q a m A) coefficient = F := by
  refine ⟨⟨fun l x => Classical.choose (hleft l x),
    fun l x => Classical.choose (hright l x)⟩, ?_⟩
  cases F
  unfold language
  congr 1 <;> funext l x
  · exact Classical.choose_spec (hleft l x)
  · exact Classical.choose_spec (hright l x)

end FiniteLanguageCatalog

/-- The admitted members of a finite catalog, for any exact-width criterion.
In particular, no decidability of admission is assumed. -/
abbrev AdmittedFiniteCatalog {C : Type} (W : C → ℕ → Prop) :=
  {c : C // ∃ r, W c r}

/-- The maximum of the actual minimum admitted widths, or zero when there are
no admitted members. This uses classical choice/decidability noncomputably. -/
def finiteCatalogWidthMaximum {C : Type} [Fintype C] (W : C → ℕ → Prop) : ℕ :=
  Finset.univ.sup (fun c : AdmittedFiniteCatalog W => Nat.find c.property)

theorem finiteCatalog_minimum_le_maximum {C : Type} [Fintype C]
    (W : C → ℕ → Prop) (c : C) (h : ∃ r, W c r) :
    Nat.find h ≤ finiteCatalogWidthMaximum W := by
  exact Finset.le_sup (s := Finset.univ)
    (f := fun c : AdmittedFiniteCatalog W => Nat.find c.property)
    (b := ⟨c, h⟩) (Finset.mem_univ _)

/-- A uniform finite upper bound on some valid width for every admitted member.
The statement applies unchanged to stronger source-level exactness notions. -/
theorem finiteCatalog_admitted_width_bound {C : Type} [Fintype C]
    (W : C → ℕ → Prop) :
    ∃ H : ℕ, ∀ c, (∃ r, W c r) → ∃ r, r ≤ H ∧ W c r := by
  refine ⟨finiteCatalogWidthMaximum W, fun c hc => ?_⟩
  exact ⟨Nat.find hc, finiteCatalog_minimum_le_maximum W c hc, Nat.find_spec hc⟩

/-- If any member is admitted, the maximum is the exact minimum of an admitted
member, rather than merely an arbitrary upper bound. -/
theorem finiteCatalog_maximum_attained {C : Type} [Fintype C]
    (W : C → ℕ → Prop) (hne : ∃ c r, W c r) :
    ∃ (c : C) (h : ∃ r, W c r),
      finiteCatalogWidthMaximum W = Nat.find h := by
  obtain ⟨c, r, hr⟩ := hne
  have hfin : (Finset.univ : Finset (AdmittedFiniteCatalog W)).Nonempty :=
    ⟨⟨c, r, hr⟩, Finset.mem_univ _⟩
  obtain ⟨d, _, hd⟩ := Finset.exists_mem_eq_sup Finset.univ hfin
    (fun e : AdmittedFiniteCatalog W => Nat.find e.property)
  exact ⟨d.val, d.property, hd⟩

/-- In particular, the exact common widths of all realizable finite-alphabet
languages with fixed `q,a,m` have one finite upper bound. -/
theorem finite_alphabet_exact_width_bound (q a m : ℕ) (A : Type) [Fintype A]
    (coefficient : A → ℂ) :
    ∃ H : ℕ, ∀ (c : FiniteLanguageCatalog q a m A)
      (h : ∃ r, HasExactCommonWidth (c.language coefficient) r),
      minimumExactCommonWidth (c.language coefficient) h ≤ H := by
  refine ⟨finiteCatalogWidthMaximum
    (fun c : FiniteLanguageCatalog q a m A => HasExactCommonWidth (c.language coefficient)), ?_⟩
  intro c h
  exact finiteCatalog_minimum_le_maximum
    (fun c : FiniteLanguageCatalog q a m A => HasExactCommonWidth (c.language coefficient)) c h

/-- An equivalent formulation directly for all actual complex-valued tensor
families with entries in the finite alphabet; users need not provide codes. -/
theorem finite_alphabet_language_exact_width_bound (q a m : ℕ)
    (A : Type) [Fintype A] (coefficient : A → ℂ) :
    ∃ H : ℕ, ∀ (s : FiniteCatalogShape a m)
      (F : LabelledLanguage s.toLabelledShape (Fin q)),
      (∀ l x, ∃ v, coefficient v = F.left l x) →
      (∀ l x, ∃ v, coefficient v = F.right l x) →
      ∀ h : ∃ r, HasExactCommonWidth F r, minimumExactCommonWidth F h ≤ H := by
  obtain ⟨H, hH⟩ := finite_alphabet_exact_width_bound q a m A coefficient
  refine ⟨H, ?_⟩
  intro s F hleft hright h
  obtain ⟨t, ht⟩ := FiniteLanguageCatalog.covers_language s coefficient F hleft hright
  have hc : ∃ r, HasExactCommonWidth
      (FiniteLanguageCatalog.language ⟨s, t⟩ coefficient) r := by
    simpa only [ht] using h
  have hb := hH ⟨s, t⟩ hc
  simpa only [ht] using hb

/-- A concrete finite signed integer alphabet; the inclusive endpoints are a
harmless over-approximation of the usual B-bit magnitude convention. -/
def integerCoefficientAlphabet (B : ℕ) : Finset ℤ :=
  Finset.Icc (-((2 ^ B : ℕ) : ℤ)) ((2 ^ B : ℕ) : ℤ)

theorem integer_mem_coefficientAlphabet {B : ℕ} (z : ℤ)
    (h : z.natAbs ≤ 2 ^ B) : z ∈ integerCoefficientAlphabet B := by
  have habs : |z| ≤ ((2 ^ B : ℕ) : ℤ) := by
    rw [← Int.natCast_natAbs]
    exact_mod_cast h
  exact Finset.mem_Icc.mpr (abs_le.mp habs)

/-- Integer B-bit inputs are a direct instance of the same finite-alphabet
argument. No decision procedure for admitting a presentation is used. -/
theorem bitbounded_integer_exact_width_bound (q a m B : ℕ) :
    ∃ H : ℕ, ∀ (c : FiniteLanguageCatalog q a m
      {z : ℤ // z ∈ integerCoefficientAlphabet B})
      (h : ∃ r, HasExactCommonWidth (c.language (fun v => (v.val : ℂ))) r),
      minimumExactCommonWidth (c.language (fun v => (v.val : ℂ))) h ≤ H :=
  finite_alphabet_exact_width_bound q a m _ _

/-- Rational codes have a signed bounded numerator and a positive denominator
from `1` through `2^B`; nonreduced codes are deliberately permitted. -/
abbrev RationalCoefficientCode (B : ℕ) :=
  {z : ℤ // z ∈ integerCoefficientAlphabet B} × Fin (2 ^ B)

def rationalCoefficientValue {B : ℕ} (c : RationalCoefficientCode B) : ℚ :=
  (c.1.val : ℚ) / ((c.2.val + 1 : ℕ) : ℚ)

def rationalCoefficientAlphabet (B : ℕ) : Finset ℚ :=
  Finset.univ.image (rationalCoefficientValue (B := B))

theorem rationalCoefficientAlphabet_finite (B : ℕ) :
    (↑(rationalCoefficientAlphabet B) : Set ℚ).Finite :=
  (rationalCoefficientAlphabet B).finite_toSet

/-- Explicit coverage of the numerator/denominator interpretation of bit bound.
No representation-theoretic decidability assumption enters this finiteness. -/
theorem rational_mem_coefficientAlphabet {B : ℕ} (x : ℚ)
    (hneg : -((2 ^ B : ℕ) : ℤ) ≤ x.num)
    (hpos : x.num ≤ ((2 ^ B : ℕ) : ℤ)) (hden : x.den ≤ 2 ^ B) :
    x ∈ rationalCoefficientAlphabet B := by
  let n : {z : ℤ // z ∈ integerCoefficientAlphabet B} :=
    ⟨x.num, Finset.mem_Icc.mpr ⟨hneg, hpos⟩⟩
  let d : Fin (2 ^ B) := ⟨x.den - 1, by have := x.den_pos; omega⟩
  refine Finset.mem_image.mpr ⟨(n, d), Finset.mem_univ _, ?_⟩
  have hd : d.val + 1 = x.den := by dsimp [d]; have := x.den_pos; omega
  simp only [rationalCoefficientValue, n, hd, Rat.num_div_den]

/-- The preceding interval condition follows from a reduced-numerator
magnitude bound. Standard bit-length ≤ B gives even the strict bound `< 2^B`. -/
theorem rational_mem_coefficientAlphabet_of_natAbs_le {B : ℕ} (x : ℚ)
    (hnum : x.num.natAbs ≤ 2 ^ B) (hden : x.den ≤ 2 ^ B) :
    x ∈ rationalCoefficientAlphabet B := by
  have hmem := integer_mem_coefficientAlphabet x.num hnum
  obtain ⟨hneg, hpos⟩ := Finset.mem_Icc.mp hmem
  exact rational_mem_coefficientAlphabet x hneg hpos hden

/-- The claimed four-parameter finite bound, with bounded rational coefficient
codes. Every reduced B-bit rational is among these codes by the preceding
coverage lemma. This assertion intentionally says nothing about computability. -/
theorem bitbounded_rational_exact_width_bound (q a m B : ℕ) :
    ∃ H : ℕ, ∀ (c : FiniteLanguageCatalog q a m (RationalCoefficientCode B))
      (h : ∃ r, HasExactCommonWidth
        (c.language (fun v => (rationalCoefficientValue v : ℂ))) r),
      minimumExactCommonWidth
        (c.language (fun v => (rationalCoefficientValue v : ℂ))) h ≤ H :=
  finite_alphabet_exact_width_bound q a m (RationalCoefficientCode B) _

end
end MatchgateWidth
