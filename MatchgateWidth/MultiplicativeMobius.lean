import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.GroupWithZero.Units.Basic

/-!
# Multiplicative decomposition of a nonvanishing table

This file formalizes the multiplicative Möbius step in Theorem 7.1 of
arXiv:2610.00079v1 (equations `multiplicative-mobius` and
`mobius-product-identity`).  Multipliers are constructed by well-founded
recursion on strict inclusion, rather than supplied as an assumption.
-/

namespace MatchgateWidth

open scoped BigOperators

noncomputable section

variable {α G : Type*} [DecidableEq α] [CommGroup G]

/-- The nonempty subsets of a finite set, including the set itself when nonempty. -/
def nonemptySubsets (S : Finset α) : Finset (Finset α) := S.powerset.erase ∅

@[simp] theorem mem_nonemptySubsets {S U : Finset α} :
    U ∈ nonemptySubsets S ↔ U ≠ ∅ ∧ U ⊆ S := by
  simp [nonemptySubsets, Finset.mem_powerset]

/-- The nonempty proper subsets used in the recursive denominator. -/
def properNonemptySubsets (S : Finset α) : Finset (Finset α) :=
  (nonemptySubsets S).erase S

@[simp] theorem mem_properNonemptySubsets {S U : Finset α} :
    U ∈ properNonemptySubsets S ↔ U ≠ ∅ ∧ U ⊂ S := by
  simp only [properNonemptySubsets, Finset.mem_erase, mem_nonemptySubsets,
    Finset.ssubset_iff_subset_ne]
  tauto

lemma properNonemptySubsets_ssubset {S U : Finset α}
    (hU : U ∈ properNonemptySubsets S) : U ⊂ S := by
  obtain ⟨hne, hU⟩ := Finset.mem_erase.mp hU
  have hsub : U ⊆ S := Finset.mem_powerset.mp (Finset.mem_erase.mp hU).2
  exact Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩

/-- Multiplicative Möbius coefficients, constructed recursively over strict subsets. -/
def multiplicativeMobius (f : Finset α → G) (S : Finset α) : G :=
  S.strongInductionOn fun S rec =>
    (f S / f ∅) /
      ∏ U ∈ (properNonemptySubsets S).attach,
        rec U.val (properNonemptySubsets_ssubset U.property)

/-- The actual constructed coefficients satisfy the source's recursive formula. -/
theorem multiplicativeMobius_eq (f : Finset α → G) (S : Finset α) :
    multiplicativeMobius f S =
      (f S / f ∅) / ∏ U ∈ properNonemptySubsets S, multiplicativeMobius f U := by
  unfold multiplicativeMobius
  rw [Finset.strongInductionOn_eq]
  exact congrArg (fun z : G => (f S / f ∅) / z)
    (Finset.prod_attach (properNonemptySubsets S) (multiplicativeMobius f))

/-- The product of all nonempty-subset multipliers recovers the normalized table. -/
theorem prod_multiplicativeMobius (f : Finset α → G) (T : Finset α) :
    (∏ S ∈ nonemptySubsets T, multiplicativeMobius f S) = f T / f ∅ := by
  by_cases hT : T = ∅
  · subst T
    simp [nonemptySubsets]
  · have hmem : T ∈ nonemptySubsets T := by
      exact Finset.mem_erase.mpr ⟨hT, Finset.mem_powerset.mpr (Finset.Subset.refl _)⟩
    rw [← Finset.mul_prod_erase (nonemptySubsets T) (multiplicativeMobius f) hmem]
    rw [multiplicativeMobius_eq]
    exact div_mul_cancel _ _

/-- Every group-valued table admits the multiplicative decomposition. -/
theorem exists_multiplicative_decomposition (f : Finset α → G) :
    ∃ y : Finset α → G,
      ∀ T : Finset α, (∏ S ∈ nonemptySubsets T, y S) = f T / f ∅ :=
  ⟨multiplicativeMobius f, prod_multiplicativeMobius f⟩


variable {K : Type*} [CommGroupWithZero K]

/-- A nowhere-zero table, viewed as a table with values in the unit group. -/
def unitTable (f : Finset α → K) (hf : ∀ S, f S ≠ 0) : Finset α → Kˣ :=
  fun S => Units.mk0 (f S) (hf S)

/-- Constructed nonzero multipliers for a nowhere-zero table over a field, or more
    generally over any commutative group with zero. -/
def nonzeroMultiplicativeMobius (f : Finset α → K) (hf : ∀ S, f S ≠ 0)
    (S : Finset α) : K :=
  (↑(multiplicativeMobius (unitTable f hf) S) : K)

/-- Every constructed multiplier is nonzero, including the harmless empty index. -/
theorem nonzeroMultiplicativeMobius_ne_zero (f : Finset α → K)
    (hf : ∀ S, f S ≠ 0) (S : Finset α) :
    nonzeroMultiplicativeMobius f hf S ≠ 0 :=
  (multiplicativeMobius (unitTable f hf) S).ne_zero

/-- The unit-group construction has exactly the recursive formula in the paper. -/
theorem nonzeroMultiplicativeMobius_eq (f : Finset α → K)
    (hf : ∀ S, f S ≠ 0) (S : Finset α) :
    nonzeroMultiplicativeMobius f hf S =
      (f S / f ∅) / ∏ U ∈ properNonemptySubsets S,
        nonzeroMultiplicativeMobius f hf U := by
  have h := congrArg (fun u : Kˣ => (u : K))
    (multiplicativeMobius_eq (unitTable f hf) S)
  simpa [nonzeroMultiplicativeMobius, unitTable] using h

/-- The nonzero multipliers obey precisely the multiplicative Möbius product identity. -/
theorem prod_nonzeroMultiplicativeMobius (f : Finset α → K)
    (hf : ∀ S, f S ≠ 0) (T : Finset α) :
    (∏ S ∈ nonemptySubsets T, nonzeroMultiplicativeMobius f hf S) = f T / f ∅ := by
  have h := congrArg (fun u : Kˣ => (u : K))
    (prod_multiplicativeMobius (unitTable f hf) T)
  simpa [nonzeroMultiplicativeMobius, unitTable] using h

/-- Existence without an assumed decomposition: the table itself is the only input. -/
theorem exists_nonzero_multiplicative_decomposition (f : Finset α → K)
    (hf : ∀ S, f S ≠ 0) :
    ∃ y : Finset α → K, (∀ S, y S ≠ 0) ∧
      ∀ T, (∏ S ∈ nonemptySubsets T, y S) = f T / f ∅ :=
  ⟨nonzeroMultiplicativeMobius f hf,
    nonzeroMultiplicativeMobius_ne_zero f hf,
    prod_nonzeroMultiplicativeMobius f hf⟩


/-- The source's finite-indexed table statement, including `k = 0` and `T = ∅`.
    No field, characteristic, or algebraic-closure hypothesis is needed for this step. -/
theorem exists_fin_nonzero_multipliers (k : ℕ) (f : Finset (Fin k) → K)
    (hf : ∀ T, f T ≠ 0) :
    ∃ y : Finset (Fin k) → K, (∀ S, S ≠ ∅ → y S ≠ 0) ∧
      ∀ T, (∏ S ∈ T.powerset.erase ∅, y S) = f T / f ∅ := by
  obtain ⟨y, hy, hprod⟩ := exists_nonzero_multiplicative_decomposition f hf
  exact ⟨y, fun S _ => hy S, hprod⟩

end

end MatchgateWidth
