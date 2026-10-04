import MatchgateWidth.MatchingSignature
import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
import Mathlib.Topology.UnitInterval
import Mathlib.Data.Fin.Rev

/-!
# Geometric disk drawings and reflection reversal

A drawing here has arbitrary continuous simple edge arcs, not necessarily
straight segments. Distinct edge interiors are disjoint, and no edge interior
meets any vertex. Vertex locations and all edge images lie in the closed unit
disk. Distinct external vertices lie on its boundary, with strictly increasing
angles specifying the counterclockwise order and a marked first vertex.

Complex conjugation is an actual reflection of these drawings. It leaves the
weighted graph unchanged and reverses the boundary order. The exact matching
signature, with its deletion convention, is therefore reversed as well.

`DiskRealizable` quantifies over finite graphs with these geometric witnesses.
`IsDiskMatchgateSignature` is the same exact model. An explicit single-edge
drawing proves the paper's nullary convention MG₀ = ℂ, including zero. Neither
definition assumes a reflection-closure axiom.

This is a standard disk-drawing presentation of the external-order notion.
It is not a formal equivalence with an independently defined rotation-system
or arbitrary plane-embedding/outer-face model. In particular, normalization of
such a model into a closed disk with the marked external order has not been
proved here. The underlying `WeightedGraph` is loopless. The source does not
explicitly specify whether loops are admitted; loops cannot contribute to
perfect matchings, but an elimination/reindexing bridge for a separate
loop-admitting model is not proved here. No graph class is silently identified
with all planar graphs.
-/

namespace MatchgateWidth

noncomputable section

open scoped ComplexConjugate

/-- A point of the unit circle, with angle measured in complete turns. -/
def boundaryPoint (a : ℝ) : ℂ := circleMap 0 1 (2 * Real.pi * a)

@[simp] theorem norm_boundaryPoint (a : ℝ) : ‖boundaryPoint a‖ = 1 := by
  simp [boundaryPoint]

/-- Conjugation reverses the angular coordinate around the circle. -/
theorem conj_boundaryPoint (a : ℝ) :
    conj (boundaryPoint a) = boundaryPoint (1 - a) := by
  unfold boundaryPoint
  rw [conj_circleMap_zero]
  have h : 2 * Real.pi * (1 - a) = -(2 * Real.pi * a) + 2 * Real.pi := by ring
  rw [h, periodic_circleMap 0 1]

/-- A genuine crossing-free drawing in a closed disk, with a prescribed
counterclockwise external order. All edges are arbitrary simple continuous
arcs on `[0,1]`, so this does not restrict to straight-line planar graphs. -/
structure PlanarDrawing {V E : Type*} {s : ℕ}
    (G : WeightedGraph V E ℂ) (ext : Fin s → V) where
  vertex : V → ℂ
  vertex_injective : Function.Injective vertex
  vertex_in_disk : ∀ v, ‖vertex v‖ ≤ 1
  edge : E → unitInterval → ℂ
  edge_continuous : ∀ e, Continuous (edge e)
  edge_injective : ∀ e, Function.Injective (edge e)
  edge_left : ∀ e, edge e 0 = vertex (G.left e)
  edge_right : ∀ e, edge e 1 = vertex (G.right e)
  edge_in_disk : ∀ e t, ‖edge e t‖ ≤ 1
  interior_avoids_vertices : ∀ e t, 0 < t → t < 1 → ∀ v, edge e t ≠ vertex v
  interiors_disjoint : ∀ e f, e ≠ f → ∀ t u,
    0 < t → t < 1 → 0 < u → u < 1 → edge e t ≠ edge f u
  external_injective : Function.Injective ext
  angle : Fin s → ℝ
  angle_pos : ∀ i, 0 < angle i
  angle_lt_one : ∀ i, angle i < 1
  angle_strictMono : StrictMono angle
  external_vertex : ∀ i, vertex (ext i) = boundaryPoint (angle i)

namespace PlanarDrawing

variable {V E : Type*} {s : ℕ} {G : WeightedGraph V E ℂ} {ext : Fin s → V}

/-- Reflect every vertex and edge in the real axis, and mark the old last
external vertex as the new first. No weight or edge incidence changes. -/
def reflect (D : PlanarDrawing G ext) : PlanarDrawing G (fun i => ext i.rev) where
  vertex := fun v => conj (D.vertex v)
  vertex_injective := star_injective.comp D.vertex_injective
  vertex_in_disk := fun v => by simpa using D.vertex_in_disk v
  edge := fun e t => conj (D.edge e t)
  edge_continuous := fun e => Complex.continuous_conj.comp (D.edge_continuous e)
  edge_injective := fun e => star_injective.comp (D.edge_injective e)
  edge_left := fun e => congrArg conj (D.edge_left e)
  edge_right := fun e => congrArg conj (D.edge_right e)
  edge_in_disk := fun e t => by simpa using D.edge_in_disk e t
  interior_avoids_vertices := fun e t ht₀ ht₁ v h =>
    D.interior_avoids_vertices e t ht₀ ht₁ v (star_injective h)
  interiors_disjoint := fun e f hef t u ht₀ ht₁ hu₀ hu₁ h =>
    D.interiors_disjoint e f hef t u ht₀ ht₁ hu₀ hu₁ (star_injective h)
  external_injective := D.external_injective.comp Fin.rev_injective
  angle := fun i => 1 - D.angle i.rev
  angle_pos := fun i => by linarith [D.angle_lt_one i.rev]
  angle_lt_one := fun i => by linarith [D.angle_pos i.rev]
  angle_strictMono := by
    intro i j hij
    have h := D.angle_strictMono (Fin.rev_lt_rev.mpr hij)
    linarith
  external_vertex := fun i => by rw [D.external_vertex, conj_boundaryPoint]

@[simp] theorem reflect_vertex (D : PlanarDrawing G ext) (v : V) :
    D.reflect.vertex v = conj (D.vertex v) := rfl

@[simp] theorem reflect_edge (D : PlanarDrawing G ext) (e : E) (t : unitInterval) :
    D.reflect.edge e t = conj (D.edge e t) := rfl

@[simp] theorem reflect_angle (D : PlanarDrawing G ext) (i : Fin s) :
    D.reflect.angle i = 1 - D.angle i.rev := rfl

/-- In particular, each external location lies on the unit circle. -/
theorem external_on_circle (D : PlanarDrawing G ext) (i : Fin s) :
    ‖D.vertex (ext i)‖ = 1 := by rw [D.external_vertex]; simp

end PlanarDrawing

/-- Exact realization by a finite weighted graph with an actual crossing-free
ordered disk drawing. Finite vertex and edge sets are canonically enumerated;
edge identities allow parallel edges, and no straightness assumption is made. -/
def DiskRealizable {s : ℕ} (f : (Fin s → Bool) → ℂ) : Prop :=
  ∃ (n m : ℕ) (G : WeightedGraph (Fin n) (Fin m) ℂ) (ext : Fin s → Fin n),
    Nonempty (PlanarDrawing G ext) ∧ ∀ x, f x = deletionSignature G ext x

/-- Reverse all boundary bits in their fixed linear enumeration. -/
def reverseSignature {s : ℕ} (f : (Fin s → Bool) → ℂ) : (Fin s → Bool) → ℂ :=
  fun x => f (fun i => x i.rev)

@[simp] theorem reverseSignature_reverseSignature {s : ℕ}
    (f : (Fin s → Bool) → ℂ) : reverseSignature (reverseSignature f) = f := by
  funext x
  simp [reverseSignature]

/-- Geometric reflection reversal for exact disk-drawn matching signatures. -/
theorem DiskRealizable.reverse {s : ℕ} {f : (Fin s → Bool) → ℂ}
    (hf : DiskRealizable f) : DiskRealizable (reverseSignature f) := by
  rcases hf with ⟨n, m, G, ext, ⟨D⟩, hf⟩
  refine ⟨n, m, G, (fun i => ext i.rev), ⟨D.reflect⟩, ?_⟩
  intro x
  exact (hf (fun i => x i.rev)).trans (deletionSignature_reverse G ext x).symm

/-- A single internal edge of a prescribed scalar weight. -/
def scalarEdgeGraph (c : ℂ) : WeightedGraph (Fin 2) (Fin 1) ℂ where
  left := fun _ => 0
  right := fun _ => 1
  loopless := by intro e; decide
  weight := fun _ => c

/-- The unique perfect matching has exactly the prescribed edge weight. -/
theorem scalarEdgeGraph_perfectMatch (c : ℂ) : weightedPerfectMatch (scalarEdgeGraph c) Finset.univ = c := by
  classical
  have hu : (Finset.univ : Finset (Finset (Fin 1))) = {∅, {0}} := by
    decide
  unfold weightedPerfectMatch
  rw [hu]
  simp [MatchesExactly, matchingDegree, scalarEdgeGraph, Fin.forall_fin_succ]

/-- Draw the two vertices at ±1/2 and the sole edge as the connecting segment.
Only this scalar realization is straight-line; general drawings remain arbitrary arcs. -/
def scalarEdgeDrawing (c : ℂ) : PlanarDrawing (scalarEdgeGraph c) (Fin.elim0 : Fin 0 → Fin 2) where
  vertex := fun v => ((v.val : ℝ) - 1 / 2 : ℝ)
  vertex_injective := by
    intro v w h
    apply Fin.ext
    have h' := congrArg Complex.re h
    simp only [Complex.ofReal_re] at h'
    exact_mod_cast (sub_left_injective h')
  vertex_in_disk := by
    intro v
    fin_cases v <;> norm_num
  edge := fun _ t => ((t : ℝ) - 1 / 2 : ℝ)
  edge_continuous := by
    intro e
    exact Complex.continuous_ofReal.comp (continuous_subtype_val.sub continuous_const)
  edge_injective := by
    intro e t u h
    apply Subtype.ext
    have h' := congrArg Complex.re h
    simp only [Complex.ofReal_re] at h'
    linarith
  edge_left := by intro e; simp [scalarEdgeGraph]
  edge_right := by intro e; simp [scalarEdgeGraph]
  edge_in_disk := by
    intro e t
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith [t.property.1, t.property.2]
  interior_avoids_vertices := by
    intro e t ht₀ ht₁ v h
    have h' := congrArg Complex.re h
    simp only [Complex.ofReal_re] at h'
    fin_cases v
    · norm_num at h'
      exact (ne_of_gt ht₀) (Subtype.ext (by simpa using h'))
    · norm_num at h'
      have h1 : t = 1 := Subtype.ext (by dsimp; linarith)
      exact (ne_of_lt ht₁) h1
  interiors_disjoint := by
    intro e f hef
    exact (hef (Subsingleton.elim e f)).elim
  external_injective := Function.injective_of_subsingleton _
  angle := Fin.elim0
  angle_pos := fun i => i.elim0
  angle_lt_one := fun i => i.elim0
  angle_strictMono := by intro i; exact i.elim0
  external_vertex := fun i => i.elim0

/-- Every nullary tensor is exactly realized by a single internal weighted edge.
Thus the geometric existential itself, without an extra closure convention,
has the paper's nullary space MG₀ = ℂ. -/
theorem diskRealizable_zero (f : (Fin 0 → Bool) → ℂ) : DiskRealizable f := by
  let x₀ : Fin 0 → Bool := Fin.elim0
  refine ⟨2, 1, scalarEdgeGraph (f x₀), Fin.elim0, ⟨scalarEdgeDrawing (f x₀)⟩, ?_⟩
  intro x
  have hx : x = x₀ := Subsingleton.elim _ _
  have ha : deletionActive (Fin.elim0 : Fin 0 → Fin 2) x = Finset.univ := by
    ext v
    simp [deletionActive]
  rw [deletionSignature, ha, scalarEdgeGraph_perfectMatch, hx]

/-- Exact disk-drawn matchgate signatures, with no separately assumed algebraic
or reflection-closure axioms. Nullary realization is established above. -/
def IsDiskMatchgateSignature {s : ℕ} (f : (Fin s → Bool) → ℂ) : Prop :=
  DiskRealizable f

/-- Every nullary tensor is allowed, as required by the paper's MG₀ = ℂ convention. -/
theorem isDiskMatchgateSignature_zero (f : (Fin 0 → Bool) → ℂ) :
    IsDiskMatchgateSignature f := diskRealizable_zero f

/-- Membership is exactly geometric disk realizability, at every arity. -/
theorem isDiskMatchgateSignature_iff {s : ℕ}
    (f : (Fin s → Bool) → ℂ) : IsDiskMatchgateSignature f ↔ DiskRealizable f := Iff.rfl

/-- Lemma 4.1 in the explicit geometric disk model, including nullary signatures.
The proof constructs a reflected drawing and uses the actual matching sum. -/
theorem reflection_reversal {s : ℕ} {f : (Fin s → Bool) → ℂ}
    (hf : IsDiskMatchgateSignature f) :
    IsDiskMatchgateSignature (reverseSignature f) := hf.reverse

end
end MatchgateWidth
