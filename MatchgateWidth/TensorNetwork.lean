import MatchgateWidth.Support
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Boundary support of finite tensor networks

A network is given by finite vertices, finite local port sets, and an incidence
map from local ports to internal edges or boundary ports. Its value is the
actual sum over internal edge labels of the product of the vertex tensors.
The boundary-support theorem applies whenever the exposed boundary port has
one incidence. In particular it applies to every planar gadget of Lemma 10.1
of arXiv:2610.00079v1: forgetting its embedding gives this finite network.
Neither planarity nor matchgate identities are needed for this algebraic fact.
-/

namespace MatchgateWidth

noncomputable section

open scoped Classical

variable {K V E P D : Type*} {I : V → Type*}

/-- Fill one distinguished port, keeping the remaining port coordinates. -/
def insertBoundaryCoordinate {J : Type*} (j : J) (d : D) (a : {i : J // i ≠ j} → D) : J → D :=
  fun i => if h : i = j then d else a ⟨i, h⟩

@[simp] theorem insertBoundaryCoordinate_same {J : Type*} (j : J) (d : D)
    (a : {i : J // i ≠ j} → D) : insertBoundaryCoordinate j d a j = d := by
  classical
  simp [insertBoundaryCoordinate]

@[simp] theorem insertBoundaryCoordinate_ne {J : Type*} (j : J) (d : D)
    (a : {i : J // i ≠ j} → D) (i : J) (h : i ≠ j) :
    insertBoundaryCoordinate j d a i = a ⟨i, h⟩ := by
  classical
  simp [insertBoundaryCoordinate, h]

variable [Field K] [Fintype V] [Fintype E] [Fintype P] [Fintype D]
variable [∀ v, Fintype (I v)]

/-- The tensor-network coordinate sum; an edge label is shared by all its incidences. -/
def networkValue (inc : ∀ v, I v → E ⊕ P)
    (T : ∀ v, (I v → D) → K) (b : P → D) : K :=
  ∑ e : E → D, ∏ v, T v (fun i => Sum.elim e b (inc v i))

/-- Flatten a tensor along one port, with all other port labels indexing columns. -/
def portFlatten {J : Type*} (T : (J → D) → K) (j : J) :
    Matrix D ({i : J // i ≠ j} → D) K :=
  fun d a => T (insertBoundaryCoordinate j d a)

/-- Labels of nonselected ports at the distinguished vertex in the residual network. -/
def residualPortLabels (inc : ∀ v, I v → E ⊕ P) (v₀ : V) (i₀ : I v₀)
    (p : P) (d₀ : D) (e : E → D) (b : {q : P // q ≠ p} → D) :
    {i : I v₀ // i ≠ i₀} → D :=
  fun i => Sum.elim e (insertBoundaryCoordinate p d₀ b) (inc v₀ i)

/-- Product of all vertex factors other than the distinguished primitive. -/
def residualWeight (inc : ∀ v, I v → E ⊕ P)
    (T : ∀ v, (I v → D) → K) (v₀ : V) (p : P) (d₀ : D)
    (e : E → D) (b : {q : P // q ≠ p} → D) : K := by
  classical
  exact ∏ v ∈ Finset.univ.erase v₀,
    T v (fun i => Sum.elim e (insertBoundaryCoordinate p d₀ b) (inc v i))

omit [Fintype E] [Fintype P] [Fintype D] in
/-- Changing an exposed boundary label leaves every other wire value unchanged. -/
theorem wireValue_insertBoundaryCoordinate_eq (p : P) (d d₀ : D)
    (e : E → D) (b : {q : P // q ≠ p} → D)
    (w : E ⊕ P) (hw : w ≠ Sum.inr p) :
    Sum.elim e (insertBoundaryCoordinate p d b) w = Sum.elim e (insertBoundaryCoordinate p d₀ b) w := by
  classical
  cases w with
  | inl a => rfl
  | inr q =>
    have hq : q ≠ p := fun h => hw (congrArg Sum.inr h)
    simp [insertBoundaryCoordinate, hq]

omit [Fintype P] [∀ v, Fintype (I v)] in
/-- Exact factorization at a uniquely incident boundary port, directly from the
sum/product semantics. The two uniqueness assumptions separate the other ports
of the selected vertex from ports of all other vertices. -/
theorem networkValue_factor_boundary (inc : ∀ v, I v → E ⊕ P)
    (T : ∀ v, (I v → D) → K) (v₀ : V) (i₀ : I v₀) (p : P)
    (hincident : inc v₀ i₀ = Sum.inr p)
    (hselected : ∀ i, inc v₀ i = Sum.inr p → i = i₀)
    (hother : ∀ v, v ≠ v₀ → ∀ i, inc v i ≠ Sum.inr p)
    (d d₀ : D) (b : {q : P // q ≠ p} → D) :
    networkValue inc T (insertBoundaryCoordinate p d b) =
      ∑ e : E → D,
        portFlatten (T v₀) i₀ d (residualPortLabels inc v₀ i₀ p d₀ e b) *
        residualWeight inc T v₀ p d₀ e b := by
  classical
  unfold networkValue
  apply Finset.sum_congr rfl
  intro e _
  have hlocal : (fun i => Sum.elim e (insertBoundaryCoordinate p d b) (inc v₀ i)) =
      insertBoundaryCoordinate i₀ d (residualPortLabels inc v₀ i₀ p d₀ e b) := by
    funext i
    by_cases hi : i = i₀
    · subst i
      simp [hincident]
    · rw [insertBoundaryCoordinate_ne _ _ _ _ hi]
      exact wireValue_insertBoundaryCoordinate_eq p d d₀ e b (inc v₀ i)
        (fun h => hi (hselected i h))
  rw [← Finset.mul_prod_erase Finset.univ
    (fun v => T v (fun i => Sum.elim e (insertBoundaryCoordinate p d b) (inc v i)))
    (Finset.mem_univ v₀)]
  rw [hlocal]
  congr 1
  unfold residualWeight
  apply Finset.prod_congr rfl
  intro v hv
  congr 1
  funext i
  exact wireValue_insertBoundaryCoordinate_eq p d d₀ e b (inc v i)
    (hother v (Finset.mem_erase.mp hv).1 i)

/-- Explicit residual contraction matrix. Each internal edge assignment contributes
its residual vertex product to the column indexed by its selected-vertex labels. -/
def boundaryResidual (inc : ∀ v, I v → E ⊕ P)
    (T : ∀ v, (I v → D) → K) (v₀ : V) (i₀ : I v₀) (p : P) (d₀ : D) :
    Matrix ({i : I v₀ // i ≠ i₀} → D) ({q : P // q ≠ p} → D) K :=
  fun a b => ∑ e : E → D,
    if residualPortLabels inc v₀ i₀ p d₀ e b = a
    then residualWeight inc T v₀ p d₀ e b else 0

omit [Fintype P] in
/-- The actual network boundary flattening is the primitive flattening times an
explicitly computed residual matrix, proved from incidence and coordinate sums. -/
theorem portFlatten_networkValue_eq_mul (inc : ∀ v, I v → E ⊕ P)
    (T : ∀ v, (I v → D) → K) (v₀ : V) (i₀ : I v₀) (p : P)
    (hincident : inc v₀ i₀ = Sum.inr p)
    (hselected : ∀ i, inc v₀ i = Sum.inr p → i = i₀)
    (hother : ∀ v, v ≠ v₀ → ∀ i, inc v i ≠ Sum.inr p) (d₀ : D) :
    portFlatten (networkValue inc T) p =
      portFlatten (T v₀) i₀ * boundaryResidual inc T v₀ i₀ p d₀ := by
  classical
  funext d b
  rw [Matrix.mul_apply]
  change networkValue inc T (insertBoundaryCoordinate p d b) = _
  rw [networkValue_factor_boundary inc T v₀ i₀ p hincident hselected hother d d₀ b]
  unfold boundaryResidual
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  symm
  rw [Finset.sum_eq_single (residualPortLabels inc v₀ i₀ p d₀ e b)]
  · simp
  · intro a _ ha
    simp [Ne.symm ha]
  · simp

/-- **Boundary-support monotonicity (Lemma 10.1).** If a boundary port is incident
only to a single port of one primitive tensor, its support in the contracted
finite network is contained in the primitive port support. All internal labels,
vertex factors and incidence constraints are represented in `networkValue`.
This includes arbitrary planar tensor gadgets and does not need planarity. -/
theorem network_boundary_support_le (inc : ∀ v, I v → E ⊕ P)
    (T : ∀ v, (I v → D) → K) (v₀ : V) (i₀ : I v₀) (p : P)
    (hincident : inc v₀ i₀ = Sum.inr p)
    (hselected : ∀ i, inc v₀ i = Sum.inr p → i = i₀)
    (hother : ∀ v, v ≠ v₀ → ∀ i, inc v i ≠ Sum.inr p) :
    columnSupport (portFlatten (networkValue inc T) p) ≤
      columnSupport (portFlatten (T v₀) i₀) := by
  classical
  cases isEmpty_or_nonempty D with
  | inl h =>
    have := h
    intro x _
    have hx : x = 0 := Subsingleton.elim _ _
    rw [hx]
    exact Submodule.zero_mem _
  | inr h =>
    have := h
    rw [portFlatten_networkValue_eq_mul inc T v₀ i₀ p hincident hselected hother
      (Classical.choice h)]
    exact columnSupport_mul_le _ _

/-- The same boundary-support theorem with unique incidence expressed directly
on the disjoint union of all vertex ports. This is the usual dangling-edge
condition in a finite graph or planar gadget. Internal edges may be restricted
to two incidences without changing the theorem or its proof. -/
theorem network_boundary_support_le_of_unique_incidence
    (inc : ∀ v, I v → E ⊕ P) (T : ∀ v, (I v → D) → K)
    (v₀ : V) (i₀ : I v₀) (p : P)
    (hincident : inc v₀ i₀ = Sum.inr p)
    (hunique : ∀ v i, inc v i = Sum.inr p →
      (⟨v, i⟩ : Sigma I) = ⟨v₀, i₀⟩) :
    columnSupport (portFlatten (networkValue inc T) p) ≤
      columnSupport (portFlatten (T v₀) i₀) := by
  apply network_boundary_support_le inc T v₀ i₀ p hincident
  · intro i hi
    exact eq_of_heq (Sigma.mk.inj (hunique v₀ i hi)).2
  · intro v hv i hi
    exact hv (Sigma.mk.inj (hunique v i hi)).1

end
end MatchgateWidth
