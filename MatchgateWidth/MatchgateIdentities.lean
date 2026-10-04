import MatchgateWidth.PfaffianCharts
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# Matchgate identities and their nonzero-pivot Pfaffian consequence

The identities are the alternating Grassmann–Plücker sums, indexed by the
increasing symmetric difference of two subsets of the ordered external ports.
No assertion that a planar graph satisfies these identities is made here.
-/

namespace MatchgateWidth

open scoped symmDiff

/-- Subset coordinates for a signature on `s` Boolean ports. -/
abbrev SubsetSignature (s : ℕ) (R : Type*) := Finset (Fin s) → R

/-- The alternating MGI expression for an explicitly ordered difference list. -/
def matchgateSum {s : ℕ} {R : Type*} [CommRing R]
    (G : SubsetSignature s R) (α β : Finset (Fin s)) (p : List (Fin s)) : R :=
  ∑ j : Fin p.length, (-1 : R) ^ (j.val + 1) *
    G (α ∆ {p[j]}) * G (β ∆ {p[j]})

/-- The exact matchgate identities. The first summand has sign `-1`; changing
all signs would give the equivalent conventional indexing from one. -/
def MatchgateIdentities {s : ℕ} {R : Type*} [CommRing R]
    (G : SubsetSignature s R) : Prop :=
  ∀ α β : Finset (Fin s), matchgateSum G α β ((α ∆ β).sort (· ≤ ·)) = 0

/-- Common XOR by a pivot subset. -/
def subsetPivot {s : ℕ} {R : Type*} (G : SubsetSignature s R)
    (pivot : Finset (Fin s)) : SubsetSignature s R := fun S => G (S ∆ pivot)

private theorem symmDiff_common {s : ℕ} (A B C : Finset (Fin s)) :
    (A ∆ C) ∆ (B ∆ C) = A ∆ B := by
  ext i
  simp only [Finset.mem_symmDiff]
  tauto

private theorem symmDiff_swap_right {s : ℕ} (A B C : Finset (Fin s)) :
    (A ∆ B) ∆ C = (A ∆ C) ∆ B := by
  ext i
  simp only [Finset.mem_symmDiff]
  tauto

/-- The full identities, not merely their recursion consequence, are invariant
under applying the same Boolean XOR pivot to every coordinate. -/
theorem MatchgateIdentities.subsetPivot {s : ℕ} {R : Type*} [CommRing R]
    {G : SubsetSignature s R} (hG : MatchgateIdentities G)
    (pivot : Finset (Fin s)) : MatchgateIdentities (MatchgateWidth.subsetPivot G pivot) := by
  intro α β
  have h := hG (α ∆ pivot) (β ∆ pivot)
  rw [symmDiff_common] at h
  simpa only [matchgateSum, MatchgateWidth.subsetPivot, symmDiff_swap_right] using h

private theorem toFinset_xor_get {s : ℕ} (xs : List (Fin s)) (hxs : xs.Nodup)
    (j : Fin xs.length) : xs.toFinset ∆ {xs[j]} = (xs.eraseIdx j.val).toFinset := by
  rw [← hxs.erase_getElem j.val j.isLt]
  ext i
  have hj : xs[j] ∈ xs := List.getElem_mem j.isLt
  simp only [Finset.mem_symmDiff, List.mem_toFinset, Finset.mem_singleton,
    hxs.mem_erase_iff]
  constructor
  · rintro (⟨hi, hne⟩ | ⟨rfl, hn⟩)
    · exact ⟨hne, hi⟩
    · exact (hn hj).elim
  · rintro ⟨hne, hi⟩
    exact Or.inl ⟨hi, hne⟩

/-- First-coordinate expansion obtained by specializing the actual MGI to
`α = {a}` and `β = xs.toFinset`. -/
theorem MatchgateIdentities.first_expansion {s : ℕ} {R : Type*} [CommRing R]
    {G : SubsetSignature s R} (hG : MatchgateIdentities G)
    (a : Fin s) (xs : List (Fin s)) (hs : (a :: xs).SortedLT) :
    G ∅ * G (a :: xs).toFinset =
      ∑ j : Fin xs.length, (-1 : R) ^ j.val * G {a, xs[j]} *
        G (xs.eraseIdx j.val).toFinset := by
  have hn := hs.nodup
  have ha : a ∉ xs := (List.nodup_cons.mp hn).1
  have hx : xs.Nodup := (List.nodup_cons.mp hn).2
  have hdiff : ({a} : Finset (Fin s)) ∆ xs.toFinset = (a :: xs).toFinset := by
    ext i
    simp only [Finset.mem_symmDiff, Finset.mem_singleton, List.toFinset_cons,
      Finset.mem_insert, List.mem_toFinset]
    constructor
    · tauto
    · rintro (rfl | hi)
      · exact Or.inl ⟨rfl, ha⟩
      · exact Or.inr ⟨hi, fun he => ha (he ▸ hi)⟩
  have hsort : (({a} : Finset (Fin s)) ∆ xs.toFinset).sort (· ≤ ·) = a :: xs := by
    rw [hdiff]
    exact (List.toFinset_sort _ hn).mpr hs.sortedLE.pairwise
  have h := hG {a} xs.toFinset
  rw [hsort] at h
  unfold matchgateSum at h
  simp only [List.length_cons, Fin.sum_univ_succ] at h
  change (-1 : R) ^ 1 * G ({a} ∆ {a}) * G (xs.toFinset ∆ {a}) +
    (∑ j : Fin xs.length, (-1 : R) ^ (j.val + 1 + 1) *
      G ({a} ∆ {xs[j]}) * G (xs.toFinset ∆ {xs[j]})) = 0 at h
  simp only [symmDiff_self, pow_one] at h
  have hfirst : xs.toFinset ∆ {a} = (a :: xs).toFinset := by
    rw [symmDiff_comm, hdiff]
  rw [hfirst] at h
  have hrest : (∑ j : Fin xs.length, (-1 : R) ^ (j.val + 1 + 1) *
      G ({a} ∆ {xs[j]}) * G (xs.toFinset ∆ {xs[j]})) =
      ∑ j : Fin xs.length, (-1 : R) ^ j.val * G {a, xs[j]} *
        G (xs.eraseIdx j.val).toFinset := by
    apply Finset.sum_congr rfl
    intro j _
    have hj : a ≠ xs[j] := fun he => ha (he ▸ List.getElem_mem j.isLt)
    have hp : ({a} : Finset (Fin s)) ∆ {xs[j]} = {a, xs[j]} := by
      ext i
      simp only [Finset.mem_symmDiff, Finset.mem_singleton, Finset.mem_insert]
      grind
    rw [hp, toFinset_xor_get xs hx j]
    simp [pow_succ]
  rw [hrest] at h
  linear_combination -h

/-- Uniqueness from the MGI recurrence: a nonzero empty coordinate and the
normalized pair coordinates determine every coordinate. Only the upper entries
of `A` are used in increasing order. -/
theorem MatchgateIdentities.eq_scale_pfaffianList {s : ℕ} {R : Type*}
    [CommRing R] [NoZeroDivisors R] {G : SubsetSignature s R}
    (hG : MatchgateIdentities G) (h0 : G ∅ ≠ 0) (A : Matrix (Fin s) (Fin s) R)
    (hA : ∀ a b : Fin s, a < b → G {a, b} = G ∅ * A a b)
    (xs : List (Fin s)) (hs : xs.SortedLT) :
    G xs.toFinset = G ∅ * pfaffianList A xs := by
  induction xs using (measure List.length).wf.induction with
  | _ xs ih =>
    cases xs with
    | nil => simp
    | cons a xs =>
      apply mul_left_cancel₀ h0
      rw [hG.first_expansion a xs hs, pfaffianList, Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      have hlt : (xs.eraseIdx j.val).length < (a :: xs).length := by
        have := List.length_eraseIdx_le xs j.val
        simp only [List.length_cons]
        omega
      have hs' : (xs.eraseIdx j.val).SortedLT :=
        ((List.sortedLT_cons.mp hs).2.pairwise.sublist (List.eraseIdx_sublist xs j.val)).sortedLT
      rw [ih (xs.eraseIdx j.val) hlt hs',
        hA a xs[j] ((List.sortedLT_cons.mp hs).1 _ (List.getElem_mem j.isLt))]
      ring

/-- The actual coordinates of the normalized skew matrix on a nonzero-empty
MGI chart. The `none` parameter records the unnormalized scale. -/
def mgiChartParameters {s : ℕ} {K : Type*} [Field K]
    (G : SubsetSignature s K) : PfaffianChartParameter s → K
  | none => G ∅
  | some p => G {p.val.1, p.val.2} / G ∅

/-- The normalized Pfaffian representation of an MGI signature at an empty
coordinate pivot. -/
theorem MatchgateIdentities.eq_pfaffian_chart_on_list {s : ℕ} {K : Type*} [Field K]
    {G : SubsetSignature s K} (hG : MatchgateIdentities G) (h0 : G ∅ ≠ 0)
    (xs : List (Fin s)) (hs : xs.SortedLT) :
    G xs.toFinset = G ∅ * pfaffianList (pfaffianChartMatrix (mgiChartParameters G)) xs := by
  apply hG.eq_scale_pfaffianList h0 _ ?_ xs hs
  intro a b hab
  rw [pfaffianChartMatrix_upper _ a b hab]
  simp only [mgiChartParameters]
  field_simp

/-- In particular, the identities force parity on every nonzero-empty chart. -/
theorem MatchgateIdentities.odd_eq_zero {s : ℕ} {K : Type*} [Field K]
    {G : SubsetSignature s K} (hG : MatchgateIdentities G) (h0 : G ∅ ≠ 0)
    (S : Finset (Fin s)) (hodd : S.card % 2 = 1) : G S = 0 := by
  have h := hG.eq_pfaffian_chart_on_list h0 (S.sort (· ≤ ·)) (Finset.sortedLT_sort S)
  rw [Finset.sort_toFinset] at h
  rw [h, pfaffianList_odd]
  · exact mul_zero _
  · simpa using hodd

/-- Boolean words and subsets are explicit interchangeable coordinate systems. -/
def booleanSubsetEquiv (s : ℕ) : BooleanInput s ≃ Finset (Fin s) where
  toFun z := Finset.univ.filter fun i => z i = 1
  invFun S i := if i ∈ S then 1 else 0
  left_inv z := by
    funext i
    generalize hz : z i = b
    fin_cases b <;> simp [hz]
  right_inv S := by
    ext i
    simp

@[simp] theorem mem_booleanSubsetEquiv {s : ℕ} (z : BooleanInput s) (i : Fin s) :
    i ∈ booleanSubsetEquiv s z ↔ z i = 1 := by
  simp [booleanSubsetEquiv]

@[simp] theorem booleanSubsetEquiv_zero (s : ℕ) :
    booleanSubsetEquiv s (fun _ => 0) = ∅ := by
  ext i
  simp

/-- The explicit coordinate equivalence takes pointwise Boolean XOR to finite
symmetric difference. -/
theorem booleanSubsetEquiv_xor {s : ℕ} (pivot z : BooleanInput s) :
    booleanSubsetEquiv s (pfaffianXor pivot z) =
      booleanSubsetEquiv s pivot ∆ booleanSubsetEquiv s z := by
  ext i
  simp only [mem_booleanSubsetEquiv, Finset.mem_symmDiff]
  generalize hp : pivot i = p
  generalize hz : z i = b
  fin_cases p <;> fin_cases b <;> simp [pfaffianXor, hp, hz]

/-- In Boolean coordinates the derived representation is exactly the
polynomial Pfaffian chart defined in `PfaffianCharts`. -/
theorem MatchgateIdentities.eq_pfaffianChart {s : ℕ} {K : Type*} [Field K]
    {G : SubsetSignature s K} (hG : MatchgateIdentities G) (h0 : G ∅ ≠ 0)
    (z : BooleanInput s) :
    G (booleanSubsetEquiv s z) = pfaffianChart (mgiChartParameters G) z := by
  have h := hG.eq_pfaffian_chart_on_list h0
    (pfaffianSelectedPorts z) (pfaffianSelectedPorts_sorted z)
  simpa [pfaffianSelectedPorts, pfaffianChart, booleanSubsetEquiv,
    mgiChartParameters] using h

/-- Every nonzero coordinate supplies a genuine pivot chart, with all chart
signs equal to zero for the common-XOR convention. -/
theorem MatchgateIdentities.eq_pfaffianPivotChart {s : ℕ} {K : Type*} [Field K]
    {G : SubsetSignature s K} (hG : MatchgateIdentities G)
    (pivot : BooleanInput s) (hp : G (booleanSubsetEquiv s pivot) ≠ 0)
    (z : BooleanInput s) :
    G (booleanSubsetEquiv s z) = pfaffianPivotChart pivot (fun _ => 0)
      (mgiChartParameters (MatchgateWidth.subsetPivot G (booleanSubsetEquiv s pivot))) z := by
  have hH := hG.subsetPivot (booleanSubsetEquiv s pivot)
  have h0 : MatchgateWidth.subsetPivot G (booleanSubsetEquiv s pivot) ∅ ≠ 0 := by
    change G (⊥ ∆ booleanSubsetEquiv s pivot) ≠ 0
    simpa only [bot_symmDiff] using hp
  have h := hH.eq_pfaffianChart h0 (pfaffianXor pivot z)
  rw [booleanSubsetEquiv_xor] at h
  simpa [MatchgateWidth.subsetPivot, symmDiff_symmDiff_self', pfaffianPivotChart] using h

/-- The MGI locus is covered by the finite family of the actual Pfaffian
polynomial charts. The zero signature is included, with zero scale. -/
theorem MatchgateIdentities.exists_pfaffianPivotChart {s : ℕ} {K : Type*} [Field K]
    {G : SubsetSignature s K} (hG : MatchgateIdentities G) :
    ∃ (pivot : BooleanInput s) (a : PfaffianChartParameter s → K),
      ∀ z, G (booleanSubsetEquiv s z) = pfaffianPivotChart pivot (fun _ => 0) a z := by
  classical
  by_cases hzero : ∀ S, G S = 0
  · refine ⟨fun _ => 0, fun _ => 0, ?_⟩
    intro z
    rw [hzero]
    simp [pfaffianPivotChart, pfaffianChart]
  · push Not at hzero
    obtain ⟨S, hS⟩ := hzero
    let pivot := (booleanSubsetEquiv s).symm S
    have hp : G (booleanSubsetEquiv s pivot) ≠ 0 := by simpa [pivot] using hS
    exact ⟨pivot, mgiChartParameters (MatchgateWidth.subsetPivot G (booleanSubsetEquiv s pivot)),
      hG.eq_pfaffianPivotChart pivot hp⟩

/-- The exact MGI predicate on the project's existing Boolean coordinate type. -/
def BooleanMatchgateIdentities {s : ℕ} {R : Type*} [CommRing R]
    (f : BooleanTable s R) : Prop :=
  MatchgateIdentities (fun S => f ((booleanSubsetEquiv s).symm S))

/-- Boolean MGI signatures therefore have one scale plus `choose s 2`
continuous parameters in one of finitely many XOR pivot charts. -/
theorem BooleanMatchgateIdentities.exists_pfaffianPivotChart {s : ℕ} {K : Type*}
    [Field K] {f : BooleanTable s K} (hf : BooleanMatchgateIdentities f) :
    ∃ (pivot : BooleanInput s) (a : PfaffianChartParameter s → K),
      f = pfaffianPivotChart pivot (fun _ => 0) a := by
  obtain ⟨pivot, a, h⟩ := MatchgateIdentities.exists_pfaffianPivotChart hf
  refine ⟨pivot, a, ?_⟩
  funext z
  simpa using h z

/-- Explicit polynomial coverage of the full Boolean MGI locus, including the
zero signature. These are the integer coordinate polynomials, evaluated in the
field of values, on exactly `1 + s.choose 2` parameters. -/
theorem BooleanMatchgateIdentities.exists_integer_polynomial_parameters
    {s : ℕ} {K : Type*} [Field K] {f : BooleanTable s K}
    (hf : BooleanMatchgateIdentities f) :
    ∃ (pivot : BooleanInput s) (a : PfaffianChartParameter s → K),
      ∀ z, f z = MvPolynomial.eval₂ (Int.castRingHom K) a
        (pfaffianPivotChartPolynomial s ℤ pivot (fun _ => 0) z) := by
  obtain ⟨pivot, a, ha⟩ := hf.exists_pfaffianPivotChart
  refine ⟨pivot, a, ?_⟩
  intro z
  rw [ha, eval₂_pfaffianPivotChartPolynomial]

end MatchgateWidth
