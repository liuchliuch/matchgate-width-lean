import MatchgateWidth.PositiveGrid
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.RingTheory.AlgebraicIndependent.Defs

/-!
# Boolean flattening minors

This file formalizes the one-versus-rest rank arguments in Propositions 6.2
and 6.4 of arXiv:2610.00079v1. Coordinates are indexed by `Fin k`; after
removing the selected port, the remaining coordinates retain their order.
For every `k ≥ 2`, the two constant assignments provide distinct columns.
Their symbolic determinant is nonzero, and a nonzero evaluation certifies
rank exactly two. Positive-grid avoidance therefore gives a positive-integer
Boolean table whose flattenings have rank two at every port.

The matchgate obstruction in Proposition 6.4 is not asserted here.
-/

namespace MatchgateWidth

/-- The Boolean inputs of an arity-`k` table. -/
abbrev BooleanInput (k : ℕ) := Fin k → Fin 2

/-- A Boolean table with values in `R`. -/
abbrev BooleanTable (k : ℕ) (R : Type*) := BooleanInput k → R

/-- Insert the selected port into the ordered tuple of other coordinates.
The successor case uses `Fin.insertNth`, whose other positions are enumerated
in order by `Fin.succAbove`. -/
def insertPort {k : ℕ} (i : Fin k) (b : Fin 2)
    (u : BooleanInput (k - 1)) : BooleanInput k :=
  match k with
  | 0 => Fin.elim0 i
  | _n + 1 => i.insertNth b u

@[simp]
theorem insertPort_self {k : ℕ} (i : Fin k) (b : Fin 2)
    (u : BooleanInput (k - 1)) : insertPort i b u i = b := by
  cases k with
  | zero => exact Fin.elim0 i
  | succ n => simp [insertPort]

@[simp]
theorem insertPort_inj {k : ℕ} {i : Fin k} {b c : Fin 2}
    {u v : BooleanInput (k - 1)} :
    insertPort i b u = insertPort i c v ↔ b = c ∧ u = v := by
  cases k with
  | zero => exact Fin.elim0 i
  | succ n => simp [insertPort]

/-- The ordered one-versus-rest flattening at port `i` has exactly two rows. -/
def oneVsRestFlattening {k : ℕ} {R : Type*} (f : BooleanTable k R) (i : Fin k) :
    Matrix (Fin 2) (BooleanInput (k - 1)) R :=
  fun b u => f (insertPort i b u)

/-- For arity at least two, the two constant assignments to the other ports
are distinct, uniformly for every selected port. -/
theorem constant_rest_assignments_ne {k : ℕ} (hk : 2 ≤ k) :
    (fun _ : Fin (k - 1) => (0 : Fin 2)) ≠ (fun _ => (1 : Fin 2)) := by
  intro h
  have h0 : 0 < k - 1 := by omega
  have heq := congr_fun h ⟨0, h0⟩
  exact Fin.zero_ne_one heq

/-- The two assignments used by the paper exist for every `k ≥ 2`. -/
theorem exists_distinct_rest_assignments {k : ℕ} (hk : 2 ≤ k) :
    ∃ u v : BooleanInput (k - 1), u ≠ v :=
  ⟨fun _ => 0, fun _ => 1, constant_rest_assignments_ne hk⟩

/-- The four entries of a two-column minor are genuinely different table
coordinates whenever the two assignments to the other ports are distinct. -/
theorem minor_coordinates_injective {k : ℕ} (i : Fin k)
    {u v : BooleanInput (k - 1)} (huv : u ≠ v) :
    Function.Injective (fun p : Fin 2 × Fin 2 => insertPort i p.1 (![u, v] p.2)) := by
  rintro ⟨b, s⟩ ⟨c, t⟩ h
  obtain ⟨hp, hq⟩ := insertPort_inj.mp h
  apply Prod.ext hp
  fin_cases s <;> fin_cases t <;> simp_all

/-- A symbolic two-by-two determinant in the Boolean table coordinates. -/
noncomputable def booleanMinor {k : ℕ} (R : Type*) [CommRing R] (i : Fin k)
    (u v : BooleanInput (k - 1)) : MvPolynomial (BooleanInput k) R :=
  MvPolynomial.X (insertPort i 0 u) * MvPolynomial.X (insertPort i 1 v) -
    MvPolynomial.X (insertPort i 0 v) * MvPolynomial.X (insertPort i 1 u)

/-- The symbolic minor is nonzero: evaluating its diagonal variables at one
and its off-diagonal variables at zero gives one. -/
theorem booleanMinor_ne_zero {k : ℕ} {R : Type*} [CommRing R] [Nontrivial R]
    (i : Fin k) {u v : BooleanInput (k - 1)} (huv : u ≠ v) :
    booleanMinor R i u v ≠ 0 := by
  classical
  intro hz
  let a : BooleanInput k → R := fun z =>
    if z = insertPort i 0 u ∨ z = insertPort i 1 v then 1 else 0
  have h := congrArg (MvPolynomial.eval a) hz
  simp [booleanMinor, a, insertPort_inj, huv, Ne.symm huv] at h

/-- Evaluation of the symbolic minor is the ordinary determinant of the
specified two-column submatrix of the corresponding flattening. -/
theorem eval_booleanMinor {k : ℕ} {R : Type*} [CommRing R]
    (f : BooleanTable k R) (i : Fin k) (u v : BooleanInput (k - 1)) :
    MvPolynomial.eval f (booleanMinor R i u v) =
      ((oneVsRestFlattening f i).submatrix id ![u, v]).det := by
  simp [booleanMinor, Matrix.det_fin_two, Matrix.submatrix, oneVsRestFlattening]

/-- The same determinant identity after changing coefficient rings. This is
needed for rational defining equations evaluated on complex tables. -/
theorem eval₂_booleanMinor {k : ℕ} {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (f : BooleanTable k S) (i : Fin k)
    (u v : BooleanInput (k - 1)) :
    MvPolynomial.eval₂ φ f (booleanMinor R i u v) =
      ((oneVsRestFlattening f i).submatrix id ![u, v]).det := by
  change (MvPolynomial.eval₂Hom φ f) (booleanMinor R i u v) = _
  rw [booleanMinor, map_sub, map_mul, map_mul]
  simp [Matrix.det_fin_two, Matrix.submatrix, oneVsRestFlattening]

/-- A nonvanishing evaluated minor gives lower rank two; the two-row shape
supplies the matching upper bound. -/
theorem rank_oneVsRestFlattening_eq_two_of_minor_ne_zero
    {k : ℕ} {R : Type*} [Field R] (f : BooleanTable k R) (i : Fin k)
    (u v : BooleanInput (k - 1))
    (h : MvPolynomial.eval f (booleanMinor R i u v) ≠ 0) :
    (oneVsRestFlattening f i).rank = 2 := by
  have hdet : ((oneVsRestFlattening f i).submatrix id ![u, v]).det ≠ 0 := by
    rwa [← eval_booleanMinor]
  have hlower := Matrix.rank_submatrix_le (oneVsRestFlattening f i) id ![u, v]
  rw [Matrix.rank_of_det_ne_zero hdet, Fintype.card_fin] at hlower
  exact le_antisymm (by simpa using (oneVsRestFlattening f i).rank_le_card_height) hlower

/-- The rank certificate is valid even when the minor polynomial and table
have different coefficient rings. -/
theorem rank_oneVsRestFlattening_eq_two_of_eval₂_minor_ne_zero
    {k : ℕ} {R S : Type*} [CommRing R] [Field S]
    (φ : R →+* S) (f : BooleanTable k S) (i : Fin k)
    (u v : BooleanInput (k - 1))
    (h : MvPolynomial.eval₂ φ f (booleanMinor R i u v) ≠ 0) :
    (oneVsRestFlattening f i).rank = 2 := by
  apply rank_oneVsRestFlattening_eq_two_of_minor_ne_zero f i u v
  rwa [eval_booleanMinor, ← eval₂_booleanMinor φ]

/-- The flattening conclusion of Proposition 6.2 follows from algebraic
independence of the complete table. Establishing that independence for the
paper's explicit transcendental entries is a separate input. -/
theorem algebraicIndependent_table_all_flattenings_rank_two
    {k : ℕ} {R S : Type*} [CommRing R] [Nontrivial R] [Field S] [Algebra R S]
    (hk : 2 ≤ k) (f : BooleanTable k S) (hf : AlgebraicIndependent R f) :
    ∀ i : Fin k, (oneVsRestFlattening f i).rank = 2 := by
  obtain ⟨u, v, huv⟩ := exists_distinct_rest_assignments hk
  intro i
  apply rank_oneVsRestFlattening_eq_two_of_eval₂_minor_ne_zero (algebraMap R S) f i u v
  intro hz
  apply booleanMinor_ne_zero (R := R) i huv
  apply hf.eq_zero_of_aeval_eq_zero
  simpa only [MvPolynomial.aeval_def] using hz

/-- The finite positive-grid argument yields one positive-integer Boolean
table simultaneously having rank two at every port. This is the flattening
conclusion of Proposition 6.4, without its separate matchgate obstruction. -/
theorem exists_positive_integer_table_all_flattenings_rank_two
    (k : ℕ) (hk : 2 ≤ k) :
    ∃ a : BooleanTable k ℕ, (∀ z, 0 < a z) ∧
      ∀ i : Fin k,
        (oneVsRestFlattening (fun z => (a z : ℂ)) i).rank = 2 := by
  let u : BooleanInput (k - 1) := fun _ => 0
  let v : BooleanInput (k - 1) := fun _ => 1
  have huv : u ≠ v := constant_rest_assignments_ne hk
  obtain ⟨a, ha, hminor⟩ := exists_positive_nat_forall_eval_ne_zero_fintype
    (fun i : Fin k => booleanMinor ℂ i u v) (fun i => booleanMinor_ne_zero i huv)
  exact ⟨a, ha, fun i => rank_oneVsRestFlattening_eq_two_of_minor_ne_zero
    (fun z => (a z : ℂ)) i u v (hminor i)⟩

/-- The complete finite-avoidance and full-flattening-rank layer of
Proposition 6.4. Given any finite family of proper rational-defined loci in
complex Boolean table space, a positive-integer table avoids all of them and
has rank two at every port. Proving that the matchgate images lie in such
proper loci remains an independent geometric obligation. -/
theorem exists_positive_integer_table_avoiding_loci_all_flattenings_rank_two
    {ι : Type*} (k : ℕ) (hk : 2 ≤ k)
    (s : Finset ι) (P : ι → Set (MvPolynomial (BooleanInput k) ℚ))
    (hproper : ∀ j ∈ s,
      polynomialZeroLocus (Rat.castHom ℂ) (P j) ≠ Set.univ) :
    ∃ a : BooleanTable k ℕ, (∀ z, 0 < a z) ∧
      (∀ j ∈ s, (fun z => (a z : ℂ)) ∉
        polynomialZeroLocus (Rat.castHom ℂ) (P j)) ∧
      ∀ i : Fin k,
        (oneVsRestFlattening (fun z => (a z : ℂ)) i).rank = 2 := by
  let u : BooleanInput (k - 1) := fun _ => 0
  let v : BooleanInput (k - 1) := fun _ => 1
  have huv : u ≠ v := constant_rest_assignments_ne hk
  obtain ⟨a, ha, hloci, hminor⟩ :=
    positive_integer_table_avoids_rational_zeroLoci_and_minors s P hproper
      Finset.univ (fun i : Fin k => booleanMinor ℚ i u v)
      (fun i _ => booleanMinor_ne_zero i huv)
  exact ⟨a, ha, hloci, fun i =>
    rank_oneVsRestFlattening_eq_two_of_eval₂_minor_ne_zero (Rat.castHom ℂ)
      (fun z => (a z : ℂ)) i u v (hminor i (Finset.mem_univ i))⟩

end MatchgateWidth
