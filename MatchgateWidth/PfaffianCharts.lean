import MatchgateWidth.BooleanMinors
import MatchgateWidth.PfaffianBlocks
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Prod

/-!
# Polynomial coordinates for ordered principal-Pfaffian charts

An arity-`s` chart has one scale parameter and one parameter for each strict
upper-triangular entry. Its Boolean coordinates are the scale times the
principal Pfaffian in the increasing order of the selected ports. The actual
coordinate polynomials work over every commutative coefficient ring, including
at zero scale and arity zero. Optional pivot/sign charts only reindex and sign
these coordinates. No identification with matchgate signatures or planar
realization theorem is asserted here.
-/

namespace MatchgateWidth

/-- A strict upper-triangular position, counted once. -/
abbrev PfaffianUpperPair (s : ℕ) := {p : Fin s × Fin s // p.1 < p.2}

/-- `none` is the scale; `some (i,j)` is the upper-triangular entry `Aᵢⱼ`. -/
abbrev PfaffianChartParameter (s : ℕ) := Option (PfaffianUpperPair s)

@[simp] theorem card_pfaffianUpperPair (s : ℕ) :
    Fintype.card (PfaffianUpperPair s) = s.choose 2 := by
  rw [Fintype.card_subtype]
  simpa using (Fintype.card_product_filter_lt (α := Fin s))

/-- The parameter count is exact, also for arities zero and one. -/
@[simp] theorem card_pfaffianChartParameter (s : ℕ) :
    Fintype.card (PfaffianChartParameter s) = 1 + s.choose 2 := by
  simp [PfaffianChartParameter, Nat.add_comm]

/-- The matrix with the specified strict upper entries, their negatives below
the diagonal, and zero diagonal. The scale parameter is not used here. -/
def pfaffianChartMatrix {s : ℕ} {R : Type*} [CommRing R]
    (a : PfaffianChartParameter s → R) : Matrix (Fin s) (Fin s) R :=
  fun i j => if h : i < j then a (some ⟨(i, j), h⟩)
    else if h : j < i then -a (some ⟨(j, i), h⟩) else 0

@[simp] theorem pfaffianChartMatrix_diag {s : ℕ} {R : Type*} [CommRing R]
    (a : PfaffianChartParameter s → R) (i : Fin s) :
    pfaffianChartMatrix a i i = 0 := by
  simp [pfaffianChartMatrix]

@[simp] theorem pfaffianChartMatrix_upper {s : ℕ} {R : Type*} [CommRing R]
    (a : PfaffianChartParameter s → R) (i j : Fin s) (h : i < j) :
    pfaffianChartMatrix a i j = a (some ⟨(i,j), h⟩) := by
  simp [pfaffianChartMatrix, h]

theorem pfaffianChartMatrix_skew {s : ℕ} {R : Type*} [CommRing R]
    (a : PfaffianChartParameter s → R) (i j : Fin s) :
    pfaffianChartMatrix a j i = -pfaffianChartMatrix a i j := by
  rcases lt_trichotomy i j with h | h | h
  · simp [pfaffianChartMatrix, h, not_lt_of_gt h]
  · subst j; simp
  · simp [pfaffianChartMatrix, h, not_lt_of_gt h]

/-- Ports selected by the Boolean word, listed in increasing external order. -/
def pfaffianSelectedPorts {s : ℕ} (z : BooleanInput s) : List (Fin s) :=
  (Finset.univ.filter fun i => z i = 1).sort (· ≤ ·)

@[simp] theorem mem_pfaffianSelectedPorts {s : ℕ} (z : BooleanInput s) (i : Fin s) :
    i ∈ pfaffianSelectedPorts z ↔ z i = 1 := by
  simp [pfaffianSelectedPorts]

theorem pfaffianSelectedPorts_nodup {s : ℕ} (z : BooleanInput s) :
    (pfaffianSelectedPorts z).Nodup := Finset.sort_nodup ..

theorem pfaffianSelectedPorts_sorted {s : ℕ} (z : BooleanInput s) :
    (pfaffianSelectedPorts z).SortedLT := Finset.sortedLT_sort ..

@[simp] theorem pfaffianSelectedPorts_zero (s : ℕ) :
    pfaffianSelectedPorts (fun _ : Fin s => (0 : Fin 2)) = [] := by
  simp [pfaffianSelectedPorts]

@[simp] theorem pfaffianSelectedPorts_arity_zero (z : BooleanInput 0) :
    pfaffianSelectedPorts z = [] := by
  simp [pfaffianSelectedPorts]

/-- A scaled ordered principal-Pfaffian signature. -/
def pfaffianChart {s : ℕ} {R : Type*} [CommRing R]
    (a : PfaffianChartParameter s → R) : BooleanTable s R :=
  fun z => a none * pfaffianList (pfaffianChartMatrix a) (pfaffianSelectedPorts z)

@[simp] theorem pfaffianChart_zero_word {s : ℕ} {R : Type*} [CommRing R]
    (a : PfaffianChartParameter s → R) :
    pfaffianChart a (fun _ => 0) = a none := by
  simp [pfaffianChart]

@[simp] theorem pfaffianChart_arity_zero {R : Type*} [CommRing R]
    (a : PfaffianChartParameter 0 → R) (z : BooleanInput 0) :
    pfaffianChart a z = a none := by
  simp [pfaffianChart]

theorem pfaffianChart_zero_scale {s : ℕ} {R : Type*} [CommRing R]
    (a : PfaffianChartParameter s → R) (ha : a none = 0) :
    pfaffianChart a = 0 := by
  funext z
  simp [pfaffianChart, ha]

theorem pfaffianChart_odd {s : ℕ} {R : Type*} [CommRing R]
    (a : PfaffianChartParameter s → R) (z : BooleanInput s)
    (hz : (pfaffianSelectedPorts z).length % 2 = 1) :
    pfaffianChart a z = 0 := by
  simp [pfaffianChart, pfaffianList_odd _ _ hz]

/-- Actual multivariate coordinate polynomials: substitute the variable matrix
into the ordered Pfaffian recursion and multiply by the scale variable. -/
noncomputable def pfaffianChartPolynomial (s : ℕ) (R : Type*) [CommRing R]
    (z : BooleanInput s) : MvPolynomial (PfaffianChartParameter s) R :=
  pfaffianChart (MvPolynomial.X : PfaffianChartParameter s →
    MvPolynomial (PfaffianChartParameter s) R) z

/-- Construction of the skew matrix commutes with every coefficient map. -/
theorem pfaffianChartMatrix_map {s : ℕ} {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (a : PfaffianChartParameter s → R) :
    (fun i j => f (pfaffianChartMatrix a i j)) =
      pfaffianChartMatrix (fun t => f (a t)) := by
  funext i j
  by_cases hij : i < j
  · simp [pfaffianChartMatrix, hij]
  · by_cases hji : j < i <;> simp [pfaffianChartMatrix, hij, hji]

/-- The entire chart commutes with ring homomorphisms. -/
theorem pfaffianChart_map {s : ℕ} {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (a : PfaffianChartParameter s → R) (z : BooleanInput s) :
    f (pfaffianChart a z) = pfaffianChart (fun t => f (a t)) z := by
  rw [pfaffianChart, map_mul, ← pfaffianList_map_ringHom, pfaffianChartMatrix_map]
  rfl

/-- Evaluation of every coordinate polynomial equals the chart coordinate.
The coefficient ring can be `ℤ` or `ℚ`, with values in any receiving ring. -/
theorem eval₂_pfaffianChartPolynomial {s : ℕ} {R S : Type*}
    [CommRing R] [CommRing S] (f : R →+* S)
    (a : PfaffianChartParameter s → S) (z : BooleanInput s) :
    MvPolynomial.eval₂ f a (pfaffianChartPolynomial s R z) = pfaffianChart a z := by
  change (MvPolynomial.eval₂Hom f a) (pfaffianChartPolynomial s R z) = _
  unfold pfaffianChartPolynomial
  rw [pfaffianChart_map]
  simp

@[simp] theorem eval_pfaffianChartPolynomial {s : ℕ} {R : Type*} [CommRing R]
    (a : PfaffianChartParameter s → R) (z : BooleanInput s) :
    MvPolynomial.eval a (pfaffianChartPolynomial s R z) = pfaffianChart a z :=
  eval₂_pfaffianChartPolynomial (RingHom.id R) a z

/-- Pointwise XOR, expressed without coercing the existing `Fin 2` words. -/
def pfaffianXor {s : ℕ} (pivot z : BooleanInput s) : BooleanInput s :=
  fun i => if pivot i = z i then 0 else 1

@[simp] theorem pfaffianXor_self {s : ℕ} (pivot : BooleanInput s) :
    pfaffianXor pivot pivot = fun _ => 0 := by
  funext i
  simp [pfaffianXor]

@[simp] theorem pfaffianXor_zero {s : ℕ} (z : BooleanInput s) :
    pfaffianXor (fun _ => 0) z = z := by
  funext i
  have hi := (z i).isLt
  dsimp [pfaffianXor]
  split_ifs with h
  · exact h
  · apply Fin.ext
    simp only [Fin.val_one]
    have hn : (z i).val ≠ 0 := by
      intro hz
      apply h
      exact (Fin.ext hz).symm
    omega

@[simp] theorem pfaffianXor_involutive {s : ℕ} (pivot z : BooleanInput s) :
    pfaffianXor pivot (pfaffianXor pivot z) = z := by
  funext i
  generalize hp : pivot i = p
  generalize hz : z i = b
  fin_cases p <;> fin_cases b <;> simp [pfaffianXor, hp, hz]

/-- A fixed pivot and fixed coordinate signs form another polynomial chart.
The sign word is chart data, not an additional continuous parameter. -/
def pfaffianPivotChart {s : ℕ} {R : Type*} [CommRing R]
    (pivot : BooleanInput s) (signs : BooleanInput s → Fin 2)
    (a : PfaffianChartParameter s → R) : BooleanTable s R :=
  fun z => (-1 : R) ^ (signs z).val * pfaffianChart a (pfaffianXor pivot z)

/-- The polynomial signature for a fixed pivot and fixed signs. -/
noncomputable def pfaffianPivotChartPolynomial (s : ℕ) (R : Type*) [CommRing R]
    (pivot : BooleanInput s) (signs : BooleanInput s → Fin 2)
    (z : BooleanInput s) : MvPolynomial (PfaffianChartParameter s) R :=
  (-1) ^ (signs z).val * pfaffianChartPolynomial s R (pfaffianXor pivot z)

/-- Pivoting and fixed signs do not change the number of variables or prevent
an integral/rational polynomial parameterization. -/
theorem eval₂_pfaffianPivotChartPolynomial {s : ℕ} {R S : Type*}
    [CommRing R] [CommRing S] (f : R →+* S)
    (pivot : BooleanInput s) (signs : BooleanInput s → Fin 2)
    (a : PfaffianChartParameter s → S) (z : BooleanInput s) :
    MvPolynomial.eval₂ f a (pfaffianPivotChartPolynomial s R pivot signs z) =
      pfaffianPivotChart pivot signs a z := by
  change (MvPolynomial.eval₂Hom f a)
    (pfaffianPivotChartPolynomial s R pivot signs z) = _
  rw [pfaffianPivotChartPolynomial, map_mul, map_pow, map_neg, map_one]
  change (-1 : S) ^ (signs z).val *
    MvPolynomial.eval₂ f a (pfaffianChartPolynomial s R (pfaffianXor pivot z)) = _
  rw [eval₂_pfaffianChartPolynomial]
  rfl

@[simp] theorem pfaffianPivotChart_pivot {s : ℕ} {R : Type*} [CommRing R]
    (pivot : BooleanInput s) (signs : BooleanInput s → Fin 2)
    (a : PfaffianChartParameter s → R) :
    pfaffianPivotChart pivot signs a pivot = (-1 : R) ^ (signs pivot).val * a none := by
  simp [pfaffianPivotChart]

theorem pfaffianPivotChart_zero_scale {s : ℕ} {R : Type*} [CommRing R]
    (pivot : BooleanInput s) (signs : BooleanInput s → Fin 2)
    (a : PfaffianChartParameter s → R) (ha : a none = 0) :
    pfaffianPivotChart pivot signs a = 0 := by
  funext z
  simp [pfaffianPivotChart, pfaffianChart_zero_scale a ha]

/-- Every coordinate of every fixed signed pivot chart is represented by an
integer polynomial on exactly one scale plus the strict upper-triangular
parameters. This has no nonzero-scale or positive-arity side condition. -/
theorem exists_integer_pfaffianPivotChart_polynomials (s : ℕ)
    (pivot : BooleanInput s) (signs : BooleanInput s → Fin 2) :
    ∃ P : BooleanInput s → MvPolynomial (PfaffianChartParameter s) ℤ,
      ∀ (R : Type*) [CommRing R] (a : PfaffianChartParameter s → R) (z : BooleanInput s),
        MvPolynomial.eval₂ (Int.castRingHom R) a (P z) =
          pfaffianPivotChart pivot signs a z := by
  exact ⟨pfaffianPivotChartPolynomial s ℤ pivot signs,
    fun R _ a z => eval₂_pfaffianPivotChartPolynomial (Int.castRingHom R)
      pivot signs a z⟩

end MatchgateWidth
