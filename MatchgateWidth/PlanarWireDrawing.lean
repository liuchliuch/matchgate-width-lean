import MatchgateWidth.PlanarDrawing
import MatchgateWidth.MatchingGluing
import MatchgateWidth.ElementaryPlanarGates
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# Explicit compositional strip drawings

These are actual continuous simple-arc drawings, with all nonintersection
conditions checked. A width `n` strip has `-1/2 < x < n-1/2` and `0 ≤ y ≤ 1`.
Its input ports occur at `(i,1)` and output ports at `(i,0)`. Parallel
composition translates the right graph by the left width. Serial composition
places the first graph in the upper third, the second in the lower third,
and inserts vertical, unit-weight bridge edges in the middle third.

This is a strong constructive circuit convention, not a normalization theorem
for arbitrary plane embeddings. Reading top ports left-to-right and then
bottom ports right-to-left is the clockwise physical boundary order.

Output-only states additionally have an explicit exponential embedding into
the closed disk. Their bottom outputs acquire strictly increasing angles,
so `StateDrawing.toDisk` supplies the existing `PlanarDrawing` structure.
The graph kernel and state-composition theorem use the actual matching sum.
-/

namespace MatchgateWidth
noncomputable section

/-- A genuine drawing in the plane, before any bounding region is chosen. -/
structure PlaneArcDrawing {V E : Type*} (G : WeightedGraph V E ℂ) where
  vertex : V → ℂ
  vertex_injective : Function.Injective vertex
  edge : E → unitInterval → ℂ
  edge_continuous : ∀ e, Continuous (edge e)
  edge_injective : ∀ e, Function.Injective (edge e)
  edge_left : ∀ e, edge e 0 = vertex (G.left e)
  edge_right : ∀ e, edge e 1 = vertex (G.right e)
  interior_avoids_vertices : ∀ e t, 0 < t → t < 1 → ∀ v, edge e t ≠ vertex v
  interiors_disjoint : ∀ e f, e ≠ f → ∀ t u,
    0 < t → t < 1 → 0 < u → u < 1 → edge e t ≠ edge f u

namespace PlaneArcDrawing
variable {V E : Type*} {G : WeightedGraph V E ℂ}

/-- Forget the disk bound and marked external enumeration. -/
def ofDisk {s : ℕ} {ext : Fin s → V} (D : PlanarDrawing G ext) : PlaneArcDrawing G where
  vertex := D.vertex
  vertex_injective := D.vertex_injective
  edge := D.edge
  edge_continuous := D.edge_continuous
  edge_injective := D.edge_injective
  edge_left := D.edge_left
  edge_right := D.edge_right
  interior_avoids_vertices := D.interior_avoids_vertices
  interiors_disjoint := D.interiors_disjoint

/-- Transport through a continuous injective map of the plane. -/
def map (D : PlaneArcDrawing G) (φ : ℂ → ℂ) (hc : Continuous φ)
    (hi : Function.Injective φ) : PlaneArcDrawing G where
  vertex := φ ∘ D.vertex
  vertex_injective := hi.comp D.vertex_injective
  edge := fun e => φ ∘ D.edge e
  edge_continuous := fun e => hc.comp (D.edge_continuous e)
  edge_injective := fun e => hi.comp (D.edge_injective e)
  edge_left := fun e => congrArg φ (D.edge_left e)
  edge_right := fun e => congrArg φ (D.edge_right e)
  interior_avoids_vertices := fun e t ht₀ ht₁ v h =>
    D.interior_avoids_vertices e t ht₀ ht₁ v (hi h)
  interiors_disjoint := fun e f hef t u ht₀ ht₁ hu₀ hu₁ h =>
    D.interiors_disjoint e f hef t u ht₀ ht₁ hu₀ hu₁ (hi h)

end PlaneArcDrawing

/-- Independent affine changes of horizontal and vertical coordinates. -/
def wireAffine (sx sy tx ty : ℝ) (z : ℂ) : ℂ :=
  ⟨sx * z.re + tx, sy * z.im + ty⟩

@[simp] theorem wireAffine_re (sx sy tx ty : ℝ) (z : ℂ) :
    (wireAffine sx sy tx ty z).re = sx * z.re + tx := rfl
@[simp] theorem wireAffine_im (sx sy tx ty : ℝ) (z : ℂ) :
    (wireAffine sx sy tx ty z).im = sy * z.im + ty := rfl

theorem continuous_wireAffine (sx sy tx ty : ℝ) : Continuous (wireAffine sx sy tx ty) := by
  change Continuous (Complex.equivRealProdCLM.symm ∘
    fun z : ℂ => (sx * z.re + tx, sy * z.im + ty))
  exact Complex.equivRealProdCLM.symm.continuous.comp (by fun_prop)

theorem wireAffine_injective {sx sy tx ty : ℝ} (hx : sx ≠ 0) (hy : sy ≠ 0) :
    Function.Injective (wireAffine sx sy tx ty) := by
  intro z w h
  apply Complex.ext
  · have h' := congrArg Complex.re h
    simpa only [wireAffine_re, add_left_inj, mul_right_inj' hx] using h'
  · have h' := congrArg Complex.im h
    simpa only [wireAffine_im, add_left_inj, mul_right_inj' hy] using h'

/-- A crossing-free drawing confined to the closed-height, open-width strip. -/
structure StripDrawing {V E : Type*} (G : WeightedGraph V E ℂ) (n : ℕ)
    extends PlaneArcDrawing G where
  vertex_x_lower : ∀ v, -(1 / 2 : ℝ) < (vertex v).re
  vertex_x_upper : ∀ v, (vertex v).re < (n : ℝ) - 1 / 2
  vertex_y_lower : ∀ v, 0 ≤ (vertex v).im
  vertex_y_upper : ∀ v, (vertex v).im ≤ 1
  edge_x_lower : ∀ e t, -(1 / 2 : ℝ) < (edge e t).re
  edge_x_upper : ∀ e t, (edge e t).re < (n : ℝ) - 1 / 2
  edge_y_lower : ∀ e t, 0 ≤ (edge e t).im
  edge_y_upper : ∀ e t, (edge e t).im ≤ 1

/-- All wires use the same horizontal coordinate on both interfaces. -/
structure WireDrawing {V E : Type*} {n : ℕ} (G : WeightedGraph V E ℂ)
    (input output : Fin n → V) extends StripDrawing G n where
  input_vertex : ∀ i, vertex (input i) = ⟨(i.val : ℝ), 1⟩
  output_vertex : ∀ i, vertex (output i) = ⟨(i.val : ℝ), 0⟩

namespace StripDrawing
variable {V W E F : Type*} {n m : ℕ}
variable {G : WeightedGraph V E ℂ} {H : WeightedGraph W F ℂ}

/-- Genuine parallel composition: the right drawing is translated by `n`. -/
def parallel (D : StripDrawing G n) (Q : StripDrawing H m) :
    StripDrawing (disjointUnionGraph G H) (n + m) where
  vertex := Sum.elim D.vertex (fun v => wireAffine 1 1 n 0 (Q.vertex v))
  vertex_injective := by
    rintro (v | v) (w | w) h
    · exact congrArg Sum.inl (D.vertex_injective h)
    · have h' := congrArg Complex.re h
      dsimp at h'
      linarith [D.vertex_x_upper v, Q.vertex_x_lower w]
    · have h' := congrArg Complex.re h
      dsimp at h'
      linarith [Q.vertex_x_lower v, D.vertex_x_upper w]
    · exact congrArg Sum.inr (Q.vertex_injective
        (wireAffine_injective (by norm_num) (by norm_num) h))
  edge := Sum.elim D.edge (fun e t => wireAffine 1 1 n 0 (Q.edge e t))
  edge_continuous := by
    rintro (e | e)
    · exact D.edge_continuous e
    · exact (continuous_wireAffine 1 1 n 0).comp (Q.edge_continuous e)
  edge_injective := by
    rintro (e | e)
    · exact D.edge_injective e
    · exact (wireAffine_injective (by norm_num) (by norm_num)).comp (Q.edge_injective e)
  edge_left := by
    rintro (e | e)
    · exact D.edge_left e
    · exact congrArg (wireAffine 1 1 n 0) (Q.edge_left e)
  edge_right := by
    rintro (e | e)
    · exact D.edge_right e
    · exact congrArg (wireAffine 1 1 n 0) (Q.edge_right e)
  interior_avoids_vertices := by
    rintro (e | e) t ht₀ ht₁ (v | v) h
    · exact D.interior_avoids_vertices e t ht₀ ht₁ v h
    · have h' := congrArg Complex.re h
      dsimp at h'
      linarith [D.edge_x_upper e t, Q.vertex_x_lower v]
    · have h' := congrArg Complex.re h
      dsimp at h'
      linarith [Q.edge_x_lower e t, D.vertex_x_upper v]
    · exact Q.interior_avoids_vertices e t ht₀ ht₁ v
        (wireAffine_injective (by norm_num) (by norm_num) h)
  interiors_disjoint := by
    rintro (e | e) (f | f) hef t u ht₀ ht₁ hu₀ hu₁ h
    · exact D.interiors_disjoint e f (fun h => hef (congrArg Sum.inl h))
        t u ht₀ ht₁ hu₀ hu₁ h
    · have h' := congrArg Complex.re h
      dsimp at h'
      linarith [D.edge_x_upper e t, Q.edge_x_lower f u]
    · have h' := congrArg Complex.re h
      dsimp at h'
      linarith [Q.edge_x_lower e t, D.edge_x_upper f u]
    · exact Q.interiors_disjoint e f (fun h => hef (congrArg Sum.inr h))
        t u ht₀ ht₁ hu₀ hu₁ (wireAffine_injective (by norm_num) (by norm_num) h)
  vertex_x_lower := by
    rintro (v | v)
    · exact D.vertex_x_lower v
    · dsimp
      linarith [Q.vertex_x_lower v, (show (0 : ℝ) ≤ n by positivity)]
  vertex_x_upper := by
    rintro (v | v)
    · dsimp
      push_cast
      linarith [D.vertex_x_upper v, (show (0 : ℝ) ≤ m by positivity)]
    · dsimp
      push_cast
      linarith [Q.vertex_x_upper v]
  vertex_y_lower := by
    rintro (v | v)
    · exact D.vertex_y_lower v
    · simpa using Q.vertex_y_lower v
  vertex_y_upper := by
    rintro (v | v)
    · exact D.vertex_y_upper v
    · simpa using Q.vertex_y_upper v
  edge_x_lower := by
    rintro (e | e) t
    · exact D.edge_x_lower e t
    · dsimp
      linarith [Q.edge_x_lower e t, (show (0 : ℝ) ≤ n by positivity)]
  edge_x_upper := by
    rintro (e | e) t
    · dsimp
      push_cast
      linarith [D.edge_x_upper e t, (show (0 : ℝ) ≤ m by positivity)]
    · dsimp
      push_cast
      linarith [Q.edge_x_upper e t]
  edge_y_lower := by
    rintro (e | e) t
    · exact D.edge_y_lower e t
    · simpa using Q.edge_y_lower e t
  edge_y_upper := by
    rintro (e | e) t
    · exact D.edge_y_upper e t
    · simpa using Q.edge_y_upper e t

end StripDrawing

namespace WireDrawing
variable {V W E F : Type*} {n m : ℕ}
variable {G : WeightedGraph V E ℂ} {H : WeightedGraph W F ℂ}
variable {input output : Fin n → V} {input' output' : Fin m → W}

theorem input_injective (D : WireDrawing G input output) : Function.Injective input := by
  intro i j h
  have h' := congrArg (fun v => (D.vertex v).re) h
  rw [D.input_vertex, D.input_vertex] at h'
  change (i.val : ℝ) = (j.val : ℝ) at h'
  exact Fin.ext (by exact_mod_cast h')

theorem output_injective (D : WireDrawing G input output) : Function.Injective output := by
  intro i j h
  have h' := congrArg (fun v => (D.vertex v).re) h
  rw [D.output_vertex, D.output_vertex] at h'
  change (i.val : ℝ) = (j.val : ℝ) at h'
  exact Fin.ext (by exact_mod_cast h')

theorem input_ne_output (D : WireDrawing G input output) (i j : Fin n) :
    input i ≠ output j := by
  intro h
  have h' := congrArg (fun v => (D.vertex v).im) h
  rw [D.input_vertex, D.output_vertex] at h'
  norm_num at h'

/-- The lower interface is reversed in the physical cyclic enumeration. -/
def boundaryOrder (input output : Fin n → V) : Fin (n + n) → V :=
  Fin.addCases input (fun i => output i.rev)

theorem boundaryOrder_injective (D : WireDrawing G input output) :
    Function.Injective (boundaryOrder input output) := by
  intro i j h
  induction i using Fin.addCases with
  | left i =>
    induction j using Fin.addCases with
    | left j => exact congrArg (Fin.castAdd n) (D.input_injective (by simpa only [boundaryOrder, Fin.addCases_left, Fin.addCases_right] using h))
    | right j => exact (D.input_ne_output i j.rev (by simpa only [boundaryOrder, Fin.addCases_left, Fin.addCases_right] using h)).elim
  | right i =>
    induction j using Fin.addCases with
    | left j => exact (D.input_ne_output j i.rev (by simpa only [boundaryOrder, Fin.addCases_left, Fin.addCases_right] using h.symm)).elim
    | right j =>
      exact congrArg (Fin.natAdd n) (Fin.rev_injective (D.output_injective (by simpa only [boundaryOrder, Fin.addCases_left, Fin.addCases_right] using h)))

/-- Concatenate same-height interfaces, shifting the right wire numbers. -/
def parallelPorts (f : Fin n → V) (g : Fin m → W) : Fin (n + m) → V ⊕ W :=
  Fin.addCases (fun i => Sum.inl (f i)) (fun i => Sum.inr (g i))

/-- Place two equal-height wire gates side by side. -/
def parallel (D : WireDrawing G input output) (Q : WireDrawing H input' output') :
    WireDrawing (disjointUnionGraph G H)
      (parallelPorts input input') (parallelPorts output output') where
  toStripDrawing := D.toStripDrawing.parallel Q.toStripDrawing
  input_vertex := by
    intro i
    induction i using Fin.addCases with
    | left i => simpa [parallelPorts, StripDrawing.parallel] using D.input_vertex i
    | right i => simp [parallelPorts, StripDrawing.parallel, Q.input_vertex, wireAffine, Nat.cast_add, add_comm]
  output_vertex := by
    intro i
    induction i using Fin.addCases with
    | left i => simpa [parallelPorts, StripDrawing.parallel] using D.output_vertex i
    | right i => simp [parallelPorts, StripDrawing.parallel, Q.output_vertex, wireAffine, Nat.cast_add, add_comm]

end WireDrawing

/-- Compress into the upper third, keeping the horizontal wire coordinates. -/
def wireUpper : ℂ → ℂ := wireAffine 1 (1/3) 0 (2/3)
/-- Compress into the lower third. -/
def wireLower : ℂ → ℂ := wireAffine 1 (1/3) 0 0
/-- The explicit vertical connecting arc, directed from top to bottom. -/
def wireBridge {n : ℕ} (i : Fin n) (t : unitInterval) : ℂ :=
  ⟨(i.val : ℝ), (2 - (t : ℝ)) / 3⟩

theorem wireUpper_injective : Function.Injective wireUpper :=
  wireAffine_injective (by norm_num) (by norm_num)
theorem wireLower_injective : Function.Injective wireLower :=
  wireAffine_injective (by norm_num) (by norm_num)
theorem continuous_wireUpper : Continuous wireUpper := continuous_wireAffine _ _ _ _
theorem continuous_wireLower : Continuous wireLower := continuous_wireAffine _ _ _ _
theorem continuous_wireBridge {n : ℕ} (i : Fin n) : Continuous (wireBridge i) := by
  change Continuous (Complex.equivRealProdCLM.symm ∘
    fun t : unitInterval => ((i.val : ℝ), (2 - (t : ℝ)) / 3))
  exact Complex.equivRealProdCLM.symm.continuous.comp (by fun_prop)

theorem wireBridge_injective {n : ℕ} (i : Fin n) : Function.Injective (wireBridge i) := by
  intro t u h
  apply Subtype.ext
  have h' := congrArg Complex.im h
  dsimp [wireBridge] at h'
  linarith

namespace StripDrawing
variable {V W E F : Type*} {n : ℕ}
variable {G : WeightedGraph V E ℂ} {H : WeightedGraph W F ℂ}

/-- Serial composition of the underlying strip drawings. Only the interfaces
being joined are required, so this also supports states with no upper ports. -/
def serial (D : StripDrawing G n) (Q : StripDrawing H n)
    (output : Fin n → V) (input : Fin n → W)
    (houtput : ∀ i, D.vertex (output i) = ⟨(i.val : ℝ), 0⟩)
    (hinput : ∀ i, Q.vertex (input i) = ⟨(i.val : ℝ), 1⟩) :
    StripDrawing (bridgeGraph G H output input) n where
  vertex := Sum.elim (fun v => wireUpper (D.vertex v)) (fun w => wireLower (Q.vertex w))
  vertex_injective := by
    rintro (v | v) (w | w) h
    · exact congrArg Sum.inl (D.vertex_injective (wireUpper_injective h))
    · have h' := congrArg Complex.im h
      dsimp [wireUpper, wireLower, wireAffine] at h'
      linarith [D.vertex_y_lower v, Q.vertex_y_upper w]
    · have h' := congrArg Complex.im h
      dsimp [wireUpper, wireLower, wireAffine] at h'
      linarith [Q.vertex_y_upper v, D.vertex_y_lower w]
    · exact congrArg Sum.inr (Q.vertex_injective (wireLower_injective h))
  edge := Sum.elim
    (Sum.elim (fun e t => wireUpper (D.edge e t)) (fun f t => wireLower (Q.edge f t)))
    wireBridge
  edge_continuous := by
    rintro ((e | f) | i)
    · exact continuous_wireUpper.comp (D.edge_continuous e)
    · exact continuous_wireLower.comp (Q.edge_continuous f)
    · exact continuous_wireBridge i
  edge_injective := by
    rintro ((e | f) | i)
    · exact wireUpper_injective.comp (D.edge_injective e)
    · exact wireLower_injective.comp (Q.edge_injective f)
    · exact wireBridge_injective i
  edge_left := by
    rintro ((e | f) | i)
    · exact congrArg wireUpper (D.edge_left e)
    · exact congrArg wireLower (Q.edge_left f)
    · simp [bridgeGraph, wireBridge, wireUpper, wireAffine, houtput]
  edge_right := by
    rintro ((e | f) | i)
    · exact congrArg wireUpper (D.edge_right e)
    · exact congrArg wireLower (Q.edge_right f)
    · norm_num [bridgeGraph, wireBridge, wireLower, wireAffine, hinput]
  interior_avoids_vertices := by
    rintro ((e | f) | i) t ht₀ ht₁ (v | w) h
    · exact D.interior_avoids_vertices e t ht₀ ht₁ v (wireUpper_injective h)
    · have h' := congrArg Complex.im h
      dsimp [wireUpper, wireLower, wireAffine] at h'
      linarith [D.edge_y_lower e t, Q.vertex_y_upper w]
    · have h' := congrArg Complex.im h
      dsimp [wireUpper, wireLower, wireAffine] at h'
      linarith [Q.edge_y_upper f t, D.vertex_y_lower v]
    · exact Q.interior_avoids_vertices f t ht₀ ht₁ w (wireLower_injective h)
    · have h' := congrArg Complex.im h
      have ht : 0 < (t : ℝ) := ht₀
      dsimp [wireBridge, wireUpper, wireAffine] at h'
      linarith [D.vertex_y_lower v]
    · have h' := congrArg Complex.im h
      have ht : (t : ℝ) < 1 := ht₁
      dsimp [wireBridge, wireLower, wireAffine] at h'
      linarith [Q.vertex_y_upper w]
  interiors_disjoint := by
    rintro ((e | e) | i) ((f | f) | j) hef t u ht₀ ht₁ hu₀ hu₁ h
    · exact D.interiors_disjoint e f (fun h => hef (congrArg (Sum.inl ∘ Sum.inl) h))
        t u ht₀ ht₁ hu₀ hu₁ (wireUpper_injective h)
    · have h' := congrArg Complex.im h
      dsimp [wireUpper, wireLower, wireAffine] at h'
      linarith [D.edge_y_lower e t, Q.edge_y_upper f u]
    · have h' := congrArg Complex.im h
      have hu : 0 < (u : ℝ) := hu₀
      dsimp [wireBridge, wireUpper, wireAffine] at h'
      linarith [D.edge_y_lower e t]
    · have h' := congrArg Complex.im h
      dsimp [wireUpper, wireLower, wireAffine] at h'
      linarith [Q.edge_y_upper e t, D.edge_y_lower f u]
    · exact Q.interiors_disjoint e f (fun h => hef (congrArg (Sum.inl ∘ Sum.inr) h))
        t u ht₀ ht₁ hu₀ hu₁ (wireLower_injective h)
    · have h' := congrArg Complex.im h
      have hu : (u : ℝ) < 1 := hu₁
      dsimp [wireBridge, wireLower, wireAffine] at h'
      linarith [Q.edge_y_upper e t]
    · have h' := congrArg Complex.im h
      have ht : 0 < (t : ℝ) := ht₀
      dsimp [wireBridge, wireUpper, wireAffine] at h'
      linarith [D.edge_y_lower f u]
    · have h' := congrArg Complex.im h
      have ht : (t : ℝ) < 1 := ht₁
      dsimp [wireBridge, wireLower, wireAffine] at h'
      linarith [Q.edge_y_upper f u]
    · have h' := congrArg Complex.re h
      dsimp [wireBridge] at h'
      have hij : i = j := Fin.ext (by exact_mod_cast h')
      exact hef (congrArg Sum.inr hij)
  vertex_x_lower := by
    rintro (v | w)
    · simpa [wireUpper, wireAffine] using D.vertex_x_lower v
    · simpa [wireLower, wireAffine] using Q.vertex_x_lower w
  vertex_x_upper := by
    rintro (v | w)
    · simpa [wireUpper, wireAffine] using D.vertex_x_upper v
    · simpa [wireLower, wireAffine] using Q.vertex_x_upper w
  vertex_y_lower := by
    rintro (v | w)
    · dsimp [wireUpper, wireAffine]
      linarith [D.vertex_y_lower v]
    · dsimp [wireLower, wireAffine]
      linarith [Q.vertex_y_lower w]
  vertex_y_upper := by
    rintro (v | w)
    · dsimp [wireUpper, wireAffine]
      linarith [D.vertex_y_upper v]
    · dsimp [wireLower, wireAffine]
      linarith [Q.vertex_y_upper w]
  edge_x_lower := by
    rintro ((e | f) | i) t
    · simpa [wireUpper, wireAffine] using D.edge_x_lower e t
    · simpa [wireLower, wireAffine] using Q.edge_x_lower f t
    · dsimp [wireBridge]
      have hi : (0 : ℝ) ≤ i.val := by positivity
      linarith
  edge_x_upper := by
    rintro ((e | f) | i) t
    · simpa [wireUpper, wireAffine] using D.edge_x_upper e t
    · simpa [wireLower, wireAffine] using Q.edge_x_upper f t
    · dsimp [wireBridge]
      have hi : (i.val : ℝ) + 1 ≤ n := by exact_mod_cast i.isLt
      linarith
  edge_y_lower := by
    rintro ((e | f) | i) t
    · dsimp [wireUpper, wireAffine]
      linarith [D.edge_y_lower e t]
    · dsimp [wireLower, wireAffine]
      linarith [Q.edge_y_lower f t]
    · dsimp [wireBridge]
      linarith [t.property.2]
  edge_y_upper := by
    rintro ((e | f) | i) t
    · dsimp [wireUpper, wireAffine]
      linarith [D.edge_y_upper e t]
    · dsimp [wireLower, wireAffine]
      linarith [Q.edge_y_upper f t]
    · dsimp [wireBridge]
      linarith [t.property.1]

end StripDrawing

namespace WireDrawing
variable {V W E F : Type*} {n : ℕ}
variable {G : WeightedGraph V E ℂ} {H : WeightedGraph W F ℂ}
variable {input output : Fin n → V} {input' output' : Fin n → W}

/-- Equal-width gates compose by actual bridge-edge gluing, with every new
edge and every possible intersection checked by the strip construction. -/
def serial (D : WireDrawing G input output) (Q : WireDrawing H input' output') :
    WireDrawing (bridgeGraph G H output input')
      (fun i => Sum.inl (input i)) (fun i => Sum.inr (output' i)) where
  toStripDrawing := D.toStripDrawing.serial Q.toStripDrawing output input'
    D.output_vertex Q.input_vertex
  input_vertex := by
    intro i
    change wireUpper (D.vertex (input i)) = _
    rw [D.input_vertex]
    norm_num [wireUpper, wireAffine]
  output_vertex := by
    intro i
    change wireLower (Q.vertex (output' i)) = _
    rw [Q.output_vertex]
    norm_num [wireLower, wireAffine]

end WireDrawing

/-- A circuit state has only its ordered bottom output interface. -/
structure StateDrawing {V E : Type*} {n : ℕ} (G : WeightedGraph V E ℂ)
    (output : Fin n → V) extends StripDrawing G n where
  output_vertex : ∀ i, vertex (output i) = ⟨(i.val : ℝ), 0⟩

namespace StateDrawing
variable {V W E F : Type*} {n : ℕ}
variable {G : WeightedGraph V E ℂ} {H : WeightedGraph W F ℂ}
variable {output : Fin n → V} {input' output' : Fin n → W}

/-- Apply a gate below a state without creating a fictitious upper interface. -/
def applyGate (D : StateDrawing G output) (Q : WireDrawing H input' output') :
    StateDrawing (bridgeGraph G H output input') (fun i => Sum.inr (output' i)) where
  toStripDrawing := D.toStripDrawing.serial Q.toStripDrawing output input'
    D.output_vertex Q.input_vertex
  output_vertex := by
    intro i
    change wireLower (Q.vertex (output' i)) = _
    rw [Q.output_vertex]
    norm_num [wireLower, wireAffine]

end StateDrawing

namespace StateDrawing
variable {V W E F : Type*} {n m : ℕ}
variable {G : WeightedGraph V E ℂ} {H : WeightedGraph W F ℂ}
variable {output : Fin n → V} {output' : Fin m → W}

/-- Tensor states by actual disjoint union and horizontal translation. -/
def parallel (D : StateDrawing G output) (Q : StateDrawing H output') :
    StateDrawing (disjointUnionGraph G H) (WireDrawing.parallelPorts output output') where
  toStripDrawing := D.toStripDrawing.parallel Q.toStripDrawing
  output_vertex := by
    intro i
    induction i using Fin.addCases with
    | left i => simpa [WireDrawing.parallelPorts, StripDrawing.parallel] using D.output_vertex i
    | right i => simp [WireDrawing.parallelPorts, StripDrawing.parallel,
        Q.output_vertex, wireAffine, Nat.cast_add, add_comm]

end StateDrawing

/-- An affine change of coordinates preserves straight parameterized arcs. -/
theorem wireAffine_straightArc (sx sy tx ty : ℝ) (p q : ℂ) (t : unitInterval) :
    wireAffine sx sy tx ty (straightArc p q t) =
      straightArc (wireAffine sx sy tx ty p) (wireAffine sx sy tx ty q) t := by
  apply Complex.ext <;> simp [wireAffine, straightArc] <;> ring

namespace StripDrawing
variable {V E : Type*} {G : WeightedGraph V E ℂ}

/-- Straight arcs inherit strip bounds from their endpoints. This helper only
supplies bounds; crossing-freeness still comes from the actual plane drawing. -/
def ofStraight (D : PlaneArcDrawing G) (n : ℕ)
    (hstraight : ∀ e t, D.edge e t = straightArc (D.vertex (G.left e)) (D.vertex (G.right e)) t)
    (hxl : ∀ v, -(1/2 : ℝ) < (D.vertex v).re)
    (hxu : ∀ v, (D.vertex v).re < (n : ℝ) - 1/2)
    (hyl : ∀ v, 0 ≤ (D.vertex v).im)
    (hyu : ∀ v, (D.vertex v).im ≤ 1) : StripDrawing G n where
  toPlaneArcDrawing := D
  vertex_x_lower := hxl
  vertex_x_upper := hxu
  vertex_y_lower := hyl
  vertex_y_upper := hyu
  edge_x_lower := by
    intro e t
    rw [hstraight]
    have h := convex_Ioo (𝕜 := ℝ) (-(1/2 : ℝ)) ((n : ℝ) - 1/2)
      ⟨hxl (G.left e), hxu (G.left e)⟩ ⟨hxl (G.right e), hxu (G.right e)⟩
      (sub_nonneg.mpr t.property.2) t.property.1 (sub_add_cancel 1 (t : ℝ))
    simpa [straightArc] using h.1
  edge_x_upper := by
    intro e t
    rw [hstraight]
    have h := convex_Ioo (𝕜 := ℝ) (-(1/2 : ℝ)) ((n : ℝ) - 1/2)
      ⟨hxl (G.left e), hxu (G.left e)⟩ ⟨hxl (G.right e), hxu (G.right e)⟩
      (sub_nonneg.mpr t.property.2) t.property.1 (sub_add_cancel 1 (t : ℝ))
    simpa [straightArc] using h.2
  edge_y_lower := by
    intro e t
    rw [hstraight]
    have h := convex_Icc (𝕜 := ℝ) (0 : ℝ) 1
      ⟨hyl (G.left e), hyu (G.left e)⟩ ⟨hyl (G.right e), hyu (G.right e)⟩
      (sub_nonneg.mpr t.property.2) t.property.1 (sub_add_cancel 1 (t : ℝ))
    simpa [straightArc] using h.1
  edge_y_upper := by
    intro e t
    rw [hstraight]
    have h := convex_Icc (𝕜 := ℝ) (0 : ℝ) 1
      ⟨hyl (G.left e), hyu (G.left e)⟩ ⟨hyl (G.right e), hyu (G.right e)⟩
      (sub_nonneg.mpr t.property.2) t.property.1 (sub_add_cancel 1 (t : ℝ))
    simpa [straightArc] using h.2
end StripDrawing

/-- Explicit affine conversion from the elementary inscribed square to the
two-wire strip. It reverses horizontal direction to retain the gate tables. -/
def squareToWire : ℂ → ℂ :=
  wireAffine (-(1 / (2 * squareScale))) (1 / (2 * squareScale)) (1/2) (1/2)

theorem continuous_squareToWire : Continuous squareToWire := continuous_wireAffine _ _ _ _
theorem squareToWire_injective : Function.Injective squareToWire :=
  wireAffine_injective (neg_ne_zero.mpr (by have := squareScale_pos; positivity))
    (by have := squareScale_pos; positivity)

@[simp] theorem squareToWire_squarePoint (x y : ℝ) :
    squareToWire (squarePoint x y) = ⟨(1-x)/2, (1+y)/2⟩ := by
  have hs : squareScale ≠ 0 := ne_of_gt squareScale_pos
  apply Complex.ext <;> dsimp [squareToWire, wireAffine, squarePoint] <;>
    field_simp <;> ring

theorem squareToWire_straightArc (p q : ℂ) (t : unitInterval) :
    squareToWire (straightArc p q t) = straightArc (squareToWire p) (squareToWire q) t :=
  wireAffine_straightArc _ _ _ _ _ _ _

/-- The top two physical ports of each two-wire elementary gadget. -/
def twoWireInput : Fin 2 → Fin 4 := ![0, 1]
/-- The bottom ports in wire order, reversing their cyclic enumeration. -/
def twoWireOutput : Fin 2 → Fin 4 := ![3, 2]

/-- Pair creation in the compositional strip convention, obtained by the
explicit affine map from its checked disk drawing. -/
def pairCreationWireDrawing (z : ℂ) :
    WireDrawing (pairCreationGraph z) twoWireInput twoWireOutput where
  toStripDrawing := StripDrawing.ofStraight
    ((PlaneArcDrawing.ofDisk (pairCreationDrawing z)).map squareToWire
      continuous_squareToWire squareToWire_injective) 2
    (fun e t => squareToWire_straightArc _ _ t)
    (by intro v; fin_cases v <;>
        norm_num [PlaneArcDrawing.map, PlaneArcDrawing.ofDisk, pairCreationDrawing, squareCorners])
    (by intro v; fin_cases v <;>
        norm_num [PlaneArcDrawing.map, PlaneArcDrawing.ofDisk, pairCreationDrawing, squareCorners])
    (by intro v; fin_cases v <;>
        norm_num [PlaneArcDrawing.map, PlaneArcDrawing.ofDisk, pairCreationDrawing, squareCorners])
    (by intro v; fin_cases v <;>
        norm_num [PlaneArcDrawing.map, PlaneArcDrawing.ofDisk, pairCreationDrawing, squareCorners])
  input_vertex := by
    intro i
    fin_cases i <;> norm_num [StripDrawing.ofStraight, PlaneArcDrawing.map,
      PlaneArcDrawing.ofDisk, pairCreationDrawing, squareCorners, twoWireInput]
  output_vertex := by
    intro i
    fin_cases i <;> norm_num [StripDrawing.ofStraight, PlaneArcDrawing.map,
      PlaneArcDrawing.ofDisk, pairCreationDrawing, squareCorners, twoWireOutput]

/-- Signed adjacent swap in exactly the same two-wire convention. -/
def crossoverWireDrawing : WireDrawing (crossoverGraphOver ℂ)
    (fun i => crossoverExternal (twoWireInput i))
    (fun i => crossoverExternal (twoWireOutput i)) where
  toStripDrawing := StripDrawing.ofStraight
    ((PlaneArcDrawing.ofDisk crossoverDiskDrawing).map squareToWire
      continuous_squareToWire squareToWire_injective) 2
    (fun e t => squareToWire_straightArc _ _ t)
    (by intro v; fin_cases v <;>
        norm_num [PlaneArcDrawing.map, PlaneArcDrawing.ofDisk, crossoverDiskDrawing, crossoverDiskVertices])
    (by intro v; fin_cases v <;>
        norm_num [PlaneArcDrawing.map, PlaneArcDrawing.ofDisk, crossoverDiskDrawing, crossoverDiskVertices])
    (by intro v; fin_cases v <;>
        norm_num [PlaneArcDrawing.map, PlaneArcDrawing.ofDisk, crossoverDiskDrawing, crossoverDiskVertices])
    (by intro v; fin_cases v <;>
        norm_num [PlaneArcDrawing.map, PlaneArcDrawing.ofDisk, crossoverDiskDrawing, crossoverDiskVertices])
  input_vertex := by
    intro i
    fin_cases i <;> norm_num [StripDrawing.ofStraight, PlaneArcDrawing.map,
      PlaneArcDrawing.ofDisk, crossoverDiskDrawing, crossoverDiskVertices, crossoverExternal, twoWireInput]
  output_vertex := by
    intro i
    fin_cases i <;> norm_num [StripDrawing.ofStraight, PlaneArcDrawing.map,
      PlaneArcDrawing.ofDisk, crossoverDiskDrawing, crossoverDiskVertices, crossoverExternal, twoWireOutput]


/-- A one-wire identity is a single vertical unit-weight edge. -/
def identityWireDrawing : WireDrawing (pinZeroGraph ℂ)
    (fun _ => 0 : Fin 1 → Fin 2) (fun _ => 1 : Fin 1 → Fin 2) := by
  let D : PlaneArcDrawing (pinZeroGraph ℂ) := {
    vertex := fun v => ⟨0, 1 - (v.val : ℝ)⟩
    vertex_injective := by
      intro v w h
      apply Fin.ext
      have h' := congrArg Complex.im h
      dsimp at h'
      exact_mod_cast (by linarith : (v.val : ℝ) = (w.val : ℝ))
    edge := fun _ t => ⟨0, 1 - (t : ℝ)⟩
    edge_continuous := by
      intro e
      change Continuous (Complex.equivRealProdCLM.symm ∘
        fun t : unitInterval => ((0 : ℝ), 1 - (t : ℝ)))
      exact Complex.equivRealProdCLM.symm.continuous.comp (by fun_prop)
    edge_injective := by
      intro e t u h
      apply Subtype.ext
      have h' := congrArg Complex.im h
      dsimp at h'
      linarith
    edge_left := by intro e; simp [pinZeroGraph]
    edge_right := by intro e; simp [pinZeroGraph]
    interior_avoids_vertices := by
      intro e t ht₀ ht₁ v h
      have ht0 : 0 < (t : ℝ) := ht₀
      have ht1 : (t : ℝ) < 1 := ht₁
      have h' := congrArg Complex.im h
      fin_cases v <;> norm_num at h' <;> first | exact (ne_of_gt ht₀) h' | linarith
    interiors_disjoint := by
      intro e f hef
      exact (hef (Subsingleton.elim _ _)).elim }
  refine {
    toStripDrawing := StripDrawing.ofStraight D 1 ?_ ?_ ?_ ?_ ?_
    input_vertex := ?_
    output_vertex := ?_ }
  · intro e t
    apply Complex.ext <;> simp [D, straightArc, pinZeroGraph]
  · intro v; norm_num [D]
  · intro v; norm_num [D]
  · intro v; fin_cases v <;> norm_num [D]
  · intro v; fin_cases v <;> norm_num [D]
  · intro i; fin_cases i; norm_num [StripDrawing.ofStraight, D]
  · intro i; fin_cases i; norm_num [StripDrawing.ofStraight, D]

/-- Explicit square-to-state conversion; the marked upper-right square point
becomes the sole bottom output, and the center becomes a strict interior point. -/
def squareToPin : ℂ → ℂ :=
  wireAffine (-(1 / (4 * squareScale))) (-(1 / (2 * squareScale))) (1/4) (1/2)

theorem continuous_squareToPin : Continuous squareToPin := continuous_wireAffine _ _ _ _
theorem squareToPin_injective : Function.Injective squareToPin :=
  wireAffine_injective (neg_ne_zero.mpr (by have := squareScale_pos; positivity))
    (neg_ne_zero.mpr (by have := squareScale_pos; positivity))

@[simp] theorem squareToPin_squarePoint (x y : ℝ) :
    squareToPin (squarePoint x y) = ⟨(1-x)/4, (1-y)/2⟩ := by
  have hs : squareScale ≠ 0 := ne_of_gt squareScale_pos
  apply Complex.ext <;> dsimp [squareToPin, wireAffine, squarePoint] <;>
    field_simp <;> ring

/-- The vacuum bit has a bottom-only state drawing, with an internal leaf. -/
def pinZeroStateDrawing : StateDrawing (pinZeroGraph ℂ) (fun _ => 0 : Fin 1 → Fin 2) where
  toStripDrawing := StripDrawing.ofStraight
    ((PlaneArcDrawing.ofDisk pinZeroDrawing).map squareToPin
      continuous_squareToPin squareToPin_injective) 1
    (fun e t => wireAffine_straightArc _ _ _ _ _ _ t)
    (by intro v; fin_cases v <;>
        norm_num [PlaneArcDrawing.map, PlaneArcDrawing.ofDisk, pinZeroDrawing, pinZeroVertices])
    (by intro v; fin_cases v <;>
        norm_num [PlaneArcDrawing.map, PlaneArcDrawing.ofDisk, pinZeroDrawing, pinZeroVertices])
    (by intro v; fin_cases v <;>
        norm_num [PlaneArcDrawing.map, PlaneArcDrawing.ofDisk, pinZeroDrawing, pinZeroVertices])
    (by intro v; fin_cases v <;>
        norm_num [PlaneArcDrawing.map, PlaneArcDrawing.ofDisk, pinZeroDrawing, pinZeroVertices])
  output_vertex := by
    intro i
    fin_cases i; norm_num [StripDrawing.ofStraight, PlaneArcDrawing.map,
      PlaneArcDrawing.ofDisk, pinZeroDrawing, pinZeroVertices]

/-- The occupied bit has a bottom-only state drawing with no edges. -/
def pinOneStateDrawing : StateDrawing (pinOneGraph ℂ) id where
  toStripDrawing := StripDrawing.ofStraight
    ((PlaneArcDrawing.ofDisk pinOneDrawing).map squareToPin
      continuous_squareToPin squareToPin_injective) 1
    (fun e => e.elim0)
    (by intro v; norm_num [PlaneArcDrawing.map, PlaneArcDrawing.ofDisk, pinOneDrawing])
    (by intro v; norm_num [PlaneArcDrawing.map, PlaneArcDrawing.ofDisk, pinOneDrawing])
    (by intro v; norm_num [PlaneArcDrawing.map, PlaneArcDrawing.ofDisk, pinOneDrawing])
    (by intro v; norm_num [PlaneArcDrawing.map, PlaneArcDrawing.ofDisk, pinOneDrawing])
  output_vertex := by
    intro i
    fin_cases i; norm_num [StripDrawing.ofStraight, PlaneArcDrawing.map,
      PlaneArcDrawing.ofDisk, pinOneDrawing]


/-- The transfer kernel deletes input and output vertices according to their
wire bits, while retaining all internal vertices. -/
def wireKernel {V E K : Type*} [Fintype V] [Fintype E] [CommSemiring K]
    {n : ℕ} (G : WeightedGraph V E K) (input output : Fin n → V)
    (a b : Fin n → Bool) : K := by
  classical
  exact weightedPerfectMatch G (deletionActive input a ∩ deletionActive output b)

/-- Physical cyclic boundary bits reverse the bottom interface. -/
def wireBoundaryBits {n : ℕ} (a b : Fin n → Bool) : Fin (n + n) → Bool :=
  Fin.addCases a (fun i => b i.rev)

/-- The internal transfer-kernel convention agrees exactly with the reversed
physical bottom boundary, without a sign or a bit complement. -/
theorem wireKernel_eq_deletionSignature {V E K : Type*}
    [Fintype V] [Fintype E] [CommSemiring K] {n : ℕ}
    (G : WeightedGraph V E K) (input output : Fin n → V) (a b : Fin n → Bool) :
    wireKernel G input output a b =
      deletionSignature G (WireDrawing.boundaryOrder input output) (wireBoundaryBits a b) := by
  classical
  unfold wireKernel deletionSignature
  congr 1
  ext v
  simp only [deletionActive, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨ha, hb⟩ ⟨i, hi, hv⟩
    induction i using Fin.addCases with
    | left i =>
      exact ha ⟨i, by simpa only [wireBoundaryBits, Fin.addCases_left] using hi,
        by simpa only [WireDrawing.boundaryOrder, Fin.addCases_left] using hv⟩
    | right i =>
      exact hb ⟨i.rev, by simpa only [wireBoundaryBits, Fin.addCases_right] using hi,
        by simpa only [WireDrawing.boundaryOrder, Fin.addCases_right] using hv⟩
  · intro h
    constructor
    · rintro ⟨i, hi, hv⟩
      apply h
      exact ⟨Fin.castAdd n i, by simpa only [wireBoundaryBits, Fin.addCases_left] using hi,
        by simpa only [WireDrawing.boundaryOrder, Fin.addCases_left] using hv⟩
    · rintro ⟨i, hi, hv⟩
      apply h
      exact ⟨Fin.natAdd n i.rev,
        by simpa only [wireBoundaryBits, Fin.addCases_right, Fin.rev_rev] using hi,
        by simpa only [WireDrawing.boundaryOrder, Fin.addCases_right, Fin.rev_rev] using hv⟩

namespace StateDrawing
variable {V W E F : Type*} {n : ℕ}
variable {G : WeightedGraph V E ℂ} {H : WeightedGraph W F ℂ}
variable {output : Fin n → V} {input' output' : Fin n → W}

theorem output_injective (D : StateDrawing G output) : Function.Injective output := by
  intro i j h
  have h' := congrArg (fun v => (D.vertex v).re) h
  rw [D.output_vertex, D.output_vertex] at h'
  change (i.val : ℝ) = (j.val : ℝ) at h'
  exact Fin.ext (by exact_mod_cast h')

/-- The actual bridge-glued state drawing realizes ordinary transfer-kernel
contraction. This links the geometric constructor to the finite matching sum. -/
theorem applyGate_deletionSignature [Fintype V] [Fintype W] [Fintype E] [Fintype F]
    (D : StateDrawing G output) (Q : WireDrawing H input' output') (b : Fin n → Bool) :
    deletionSignature (bridgeGraph G H output input') (fun i => Sum.inr (output' i)) b =
      ∑ a : Fin n → Bool, deletionSignature G output a * wireKernel H input' output' a b := by
  classical
  have hactive : deletionActive (fun i => Sum.inr (output' i) : Fin n → V ⊕ W) b =
      Finset.univ.disjSum (deletionActive output' b) := by
    ext v
    cases v <;> simp [deletionActive]
  have hinput : ∀ i, input' i ∈ deletionActive output' b := by
    intro i
    simp only [deletionActive, Finset.mem_filter, Finset.mem_univ, true_and]
    rintro ⟨j, _, h⟩
    exact Q.input_ne_output i j h.symm
  rw [deletionSignature, hactive, weightedPerfectMatch_bridge_active G H output input'
    D.output_injective Q.input_injective Finset.univ (deletionActive output' b)
    (fun _ => Finset.mem_univ _) hinput, ← (bridgeBitsEquiv (Fin n)).sum_comp]
  apply Finset.sum_congr rfl
  intro a _
  have hl : Finset.univ \ (bridgeBitsEquiv (Fin n) a).image output = deletionActive output a :=
    bridgeRemaining_bits output a
  have hr : deletionActive output' b \ (bridgeBitsEquiv (Fin n) a).image input' =
      deletionActive input' a ∩ deletionActive output' b := by
    ext v
    simp [deletionActive, bridgeBitsEquiv, and_comm]
  rw [hl, hr]
  rfl

end StateDrawing

/-- Elementary pair creation keeps exactly the matrix convention used by the
finite circuit synthesis theorem. -/
theorem pairCreation_wireKernel (z : ℂ) (a b : Fin 2 → Bool) :
    wireKernel (pairCreationGraph z) twoWireInput twoWireOutput a b = pairCreationMatrix z a b := by
  rw [wireKernel_eq_deletionSignature]
  have he : WireDrawing.boundaryOrder twoWireInput twoWireOutput = id := by
    ext i
    fin_cases i <;> rfl
  have hb : wireBoundaryBits a b = ![a 0, a 1, b 1, b 0] := by
    ext i
    fin_cases i <;> rfl
  rw [he, hb]
  rfl

/-- The signed swap has the same input/output table after affine conversion. -/
theorem crossover_wireKernel (a b : Fin 2 → Bool) :
    wireKernel (crossoverGraphOver ℂ)
      (fun i => crossoverExternal (twoWireInput i))
      (fun i => crossoverExternal (twoWireOutput i)) a b = crossoverMatrix a b := by
  rw [wireKernel_eq_deletionSignature]
  have he : WireDrawing.boundaryOrder
      (fun i => crossoverExternal (twoWireInput i))
      (fun i => crossoverExternal (twoWireOutput i)) = crossoverExternal := by
    ext i
    fin_cases i <;> rfl
  have hb : wireBoundaryBits a b = ![a 0, a 1, b 1, b 0] := by
    ext i
    fin_cases i <;> rfl
  rw [he, hb]
  rfl

/-- A single straight unit wire has the exact identity transfer kernel. -/
theorem identity_wireKernel (a b : Fin 1 → Bool) :
    wireKernel (pinZeroGraph ℂ) (fun _ => 0 : Fin 1 → Fin 2) (fun _ => 1 : Fin 1 → Fin 2)
      a b = if a = b then 1 else 0 := by
  classical
  have ha : a = fun _ => a 0 := by ext i; fin_cases i; rfl
  have hb : b = fun _ => b 0 := by ext i; fin_cases i; rfl
  have hu : (Finset.univ : Finset (Finset (Fin 1))) = {∅, {0}} := by decide
  rw [ha, hb]
  generalize a 0 = a₀
  generalize b 0 = b₀
  cases a₀ <;> cases b₀ <;>
    simp +decide [wireKernel, weightedPerfectMatch, hu, MatchesExactly,
      matchingDegree, pinZeroGraph, deletionActive, Fin.forall_fin_succ]


/-- The empty graph supplies the empty-width identity and vacuum. -/
def emptyWireGraph : WeightedGraph (Fin 0) (Fin 0) ℂ where
  left := Fin.elim0
  right := Fin.elim0
  loopless := fun e => e.elim0
  weight := Fin.elim0

def emptyStripDrawing : StripDrawing emptyWireGraph 0 where
  vertex := Fin.elim0
  vertex_injective := by intro v; exact v.elim0
  edge := Fin.elim0
  edge_continuous := fun e => e.elim0
  edge_injective := fun e => e.elim0
  edge_left := fun e => e.elim0
  edge_right := fun e => e.elim0
  interior_avoids_vertices := fun e => e.elim0
  interiors_disjoint := fun e => e.elim0
  vertex_x_lower := fun v => v.elim0
  vertex_x_upper := fun v => v.elim0
  vertex_y_lower := fun v => v.elim0
  vertex_y_upper := fun v => v.elim0
  edge_x_lower := fun e => e.elim0
  edge_x_upper := fun e => e.elim0
  edge_y_lower := fun e => e.elim0
  edge_y_upper := fun e => e.elim0

def emptyWireDrawing : WireDrawing emptyWireGraph Fin.elim0 Fin.elim0 where
  toStripDrawing := emptyStripDrawing
  input_vertex := fun i => i.elim0
  output_vertex := fun i => i.elim0

def emptyStateDrawing : StateDrawing emptyWireGraph Fin.elim0 where
  toStripDrawing := emptyStripDrawing
  output_vertex := fun i => i.elim0

@[simp] theorem emptyWireGraph_deletionSignature (x : Fin 0 → Bool) :
    deletionSignature emptyWireGraph Fin.elim0 x = 1 := by
  have ha : deletionActive (Fin.elim0 : Fin 0 → Fin 0) x = ∅ := by
    ext v
    exact v.elim0
  rw [deletionSignature, ha, weightedPerfectMatch_empty]

@[simp] theorem emptyWireGraph_wireKernel (a b : Fin 0 → Bool) :
    wireKernel emptyWireGraph Fin.elim0 Fin.elim0 a b = 1 := by
  classical
  have ha : deletionActive (Fin.elim0 : Fin 0 → Fin 0) a ∩ deletionActive Fin.elim0 b = ∅ := by
    ext v
    exact v.elim0
  unfold wireKernel
  convert weightedPerfectMatch_empty emptyWireGraph using 1
  congr 1

/-- An exponential embedding of a state strip into the unit disk. -/
def stateDiskMap (n : ℕ) (z : ℂ) : ℂ :=
  Complex.exp ⟨-z.im, Real.pi * (z.re + 1) / ((n : ℝ) + 1)⟩

theorem continuous_stateDiskMap (n : ℕ) : Continuous (stateDiskMap n) := by
  change Continuous (Complex.exp ∘ Complex.equivRealProdCLM.symm ∘
    fun z : ℂ => (-z.im, Real.pi * (z.re + 1) / ((n : ℝ) + 1)))
  exact Complex.continuous_exp.comp (Complex.equivRealProdCLM.symm.continuous.comp (by fun_prop))

private theorem stateDiskMap_phase_bounds (n : ℕ) (z : ℂ)
    (hl : -(1/2 : ℝ) < z.re) (hu : z.re < (n : ℝ) - 1/2) :
    0 < Real.pi * (z.re + 1) / ((n : ℝ) + 1) ∧
      Real.pi * (z.re + 1) / ((n : ℝ) + 1) < Real.pi := by
  have hd : (0 : ℝ) < n + 1 := by positivity
  constructor
  · have hz : 0 < z.re + 1 := by linarith
    positivity
  · apply (div_lt_iff₀ hd).mpr
    nlinarith [Real.pi_pos]

/-- Injectivity is proved on the actual strip, not assumed globally for exp. -/
theorem stateDiskMap_injective (n : ℕ) {z w : ℂ}
    (hzl : -(1/2 : ℝ) < z.re) (hzu : z.re < (n : ℝ) - 1/2)
    (hwl : -(1/2 : ℝ) < w.re) (hwu : w.re < (n : ℝ) - 1/2)
    (h : stateDiskMap n z = stateDiskMap n w) : z = w := by
  have hz := stateDiskMap_phase_bounds n z hzl hzu
  have hw := stateDiskMap_phase_bounds n w hwl hwu
  have he := Complex.exp_inj_of_neg_pi_lt_of_le_pi
    (by dsimp; linarith [Real.pi_pos, hz.1]) (by exact le_of_lt hz.2)
    (by dsimp; linarith [Real.pi_pos, hw.1]) (by exact le_of_lt hw.2) h
  have hI := congrArg Complex.im he
  have hR := congrArg Complex.re he
  apply Complex.ext
  · dsimp at hI
    have hd : (n : ℝ) + 1 ≠ 0 := by positivity
    have hp : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
    exact add_right_cancel ((mul_left_cancel₀ hp) ((div_left_inj' hd).mp hI))
  · dsimp at hR
    linarith

theorem stateDiskMap_in_disk (n : ℕ) {z : ℂ} (hy : 0 ≤ z.im) :
    ‖stateDiskMap n z‖ ≤ 1 := by
  rw [stateDiskMap, Complex.norm_exp]
  change Real.exp (-z.im) ≤ 1
  exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr hy)

@[simp] theorem stateDiskMap_output (n : ℕ) (i : Fin n) :
    stateDiskMap n ⟨(i.val : ℝ), 0⟩ =
      boundaryPoint (((i.val : ℝ) + 1) / (2 * ((n : ℝ) + 1))) := by
  unfold stateDiskMap boundaryPoint circleMap
  simp only [neg_zero]
  change Complex.exp ⟨0, Real.pi * ((i.val : ℝ) + 1) / ((n : ℝ) + 1)⟩ =
    0 + (1 : ℂ) * Complex.exp
      (((2 * Real.pi * (((i.val : ℝ) + 1) / (2 * ((n : ℝ) + 1))) : ℝ) : ℂ) * Complex.I)
  rw [zero_add, one_mul]
  apply congrArg Complex.exp
  apply Complex.ext
  · simp only [Complex.mul_re, Complex.ofReal_re, Complex.I_re, mul_zero,
      Complex.ofReal_im, Complex.I_im, zero_mul, sub_zero]
  · simp only [Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one,
      Complex.ofReal_im, Complex.I_re, mul_zero, add_zero]
    field_simp

namespace StateDrawing
variable {V E : Type*} {n : ℕ} {G : WeightedGraph V E ℂ} {output : Fin n → V}

/-- Every constructed state strip has an explicit ordered disk drawing. The
exponential map places its outputs at increasing positive boundary angles. -/
def toDisk (D : StateDrawing G output) : PlanarDrawing G output where
  vertex := stateDiskMap n ∘ D.vertex
  vertex_injective := by
    intro v w h
    exact D.vertex_injective (stateDiskMap_injective n (D.vertex_x_lower v)
      (D.vertex_x_upper v) (D.vertex_x_lower w) (D.vertex_x_upper w) h)
  vertex_in_disk := fun v => stateDiskMap_in_disk n (D.vertex_y_lower v)
  edge := fun e => stateDiskMap n ∘ D.edge e
  edge_continuous := fun e => (continuous_stateDiskMap n).comp (D.edge_continuous e)
  edge_injective := by
    intro e t u h
    exact D.edge_injective e (stateDiskMap_injective n (D.edge_x_lower e t)
      (D.edge_x_upper e t) (D.edge_x_lower e u) (D.edge_x_upper e u) h)
  edge_left := fun e => congrArg (stateDiskMap n) (D.edge_left e)
  edge_right := fun e => congrArg (stateDiskMap n) (D.edge_right e)
  edge_in_disk := fun e t => stateDiskMap_in_disk n (D.edge_y_lower e t)
  interior_avoids_vertices := fun e t ht₀ ht₁ v h =>
    D.interior_avoids_vertices e t ht₀ ht₁ v (stateDiskMap_injective n
      (D.edge_x_lower e t) (D.edge_x_upper e t) (D.vertex_x_lower v) (D.vertex_x_upper v) h)
  interiors_disjoint := fun e f hef t u ht₀ ht₁ hu₀ hu₁ h =>
    D.interiors_disjoint e f hef t u ht₀ ht₁ hu₀ hu₁ (stateDiskMap_injective n
      (D.edge_x_lower e t) (D.edge_x_upper e t) (D.edge_x_lower f u) (D.edge_x_upper f u) h)
  external_injective := D.output_injective
  angle := fun i => ((i.val : ℝ) + 1) / (2 * ((n : ℝ) + 1))
  angle_pos := by intro i; positivity
  angle_lt_one := by
    intro i
    apply (div_lt_one (by positivity : (0 : ℝ) < 2 * ((n : ℝ) + 1))).mpr
    have hi : (i.val : ℝ) < n := by exact_mod_cast i.isLt
    have hn : (0 : ℝ) ≤ n := by positivity
    linarith
  angle_strictMono := by
    intro i j hij
    apply (div_lt_div_iff_of_pos_right (by positivity : (0 : ℝ) < 2 * ((n : ℝ) + 1))).mpr
    have hval : (i.val : ℝ) < (j.val : ℝ) := by exact_mod_cast hij
    linarith
  external_vertex := by intro i; simp [D.output_vertex]

end StateDrawing
end
end MatchgateWidth
