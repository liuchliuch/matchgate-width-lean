import MatchgateWidth.OrderedAllLeftGadget
import MatchgateWidth.SquareDiskDrawing

/-! # Literal one-vertex all-left gadgets

The one-vertex gadget has the original left label, every original port exposed,
and exactly its original tensor as boundary value. Explicit radial disk drawings
below cover arities zero, one, and two, enough for the coordinate pins and X01.
-/
namespace MatchgateWidth
noncomputable section
open scoped Classical
local instance (priority := 2000) primitiveGadgetFinDecidableEq (m : ℕ) : DecidableEq (Fin m) := Classical.decEq _

namespace AllLeftGadget
variable {S : LabelledShape}

/-- No internal edges or right vertices: all ports of this literal primitive
are exposed in precisely their original order. -/
def primitive (l : S.LeftLabel) : AllLeftGadget S 1 0 0 (S.leftArity l) where
  leftLabel _ := l
  rightLabel := Fin.elim0
  leftIncidence := {
    toFun q := Sum.inr q.2
    invFun := Sum.elim Fin.elim0 (fun i => ⟨0,i⟩)
    left_inv := by rintro ⟨v,i⟩; have hv : v = 0 := Subsingleton.elim _ _; subst v; rfl
    right_inv := by rintro (i | i); exact i.elim0; rfl }
  rightIncidence := {
    toFun q := q.1.elim0
    invFun := Fin.elim0
    left_inv q := q.1.elim0
    right_inv i := i.elim0 }

@[simp] theorem primitive_value {D : Type} [Fintype D]
    (F : LabelledLanguage S D) (l : S.LeftLabel) :
    (primitive l).value F = F.left l := by
  classical
  funext z
  rw [value_eq]
  simp [primitive]
  rfl

/-- The unique primitive is connected even when its arity is zero. -/
theorem primitive_connected (l : S.LeftLabel) : (primitive l).Connected := by
  refine ⟨⟨Sum.inl 0⟩, ?_⟩
  intro u v
  have h : u = v := by
    cases u with
    | inl u =>
      cases v with
      | inl v => exact congrArg Sum.inl (Subsingleton.elim _ _)
      | inr v => exact v.elim0
    | inr u => exact u.elim0
  subst v
  exact Relation.ReflTransGen.refl

/-- A radial star configuration records actual circle endpoints and their
positive square-germ order, independently of any tensor or matching identity. -/
structure RadialPortConfiguration (n : ℕ) where
  point : Fin n → ℂ
  norm_point : ∀ i, ‖point i‖ = 1
  point_injective : Function.Injective point
  angle : Fin n → ℝ
  angle_pos : ∀ i, 0 < angle i
  angle_lt_one : ∀ i, angle i < 1
  angle_strictMono : StrictMono angle
  point_eq_boundary : ∀ i, point i = boundaryPoint (angle i)
  time : Fin n → ℝ
  time_strictMono : StrictMono time
  time_range : ∀ i, 0 ≤ time i ∧ time i < 4
  speed : Fin n → ℝ
  speed_pos : ∀ i, 0 < speed i
  point_eq_square : ∀ i, point i = speed i • twoCenterSquare (time i)

namespace RadialPortConfiguration
variable {n : ℕ} (C : RadialPortConfiguration n)

def vertex : (Fin 1 ⊕ Fin 0) ⊕ Fin n → ℂ := Sum.elim (fun _ => 0) C.point

def edge : Fin 0 ⊕ Fin n → unitInterval → ℂ :=
  Sum.elim Fin.elim0 (fun i t => (t : ℝ) • C.point i)

theorem vertex_injective : Function.Injective C.vertex := by
  rintro (v | i) (w | j) h
  · have hw : v = w := by
      cases v with
      | inl v =>
        cases w with
        | inl w => exact congrArg Sum.inl (Subsingleton.elim _ _)
        | inr w => exact w.elim0
      | inr v => exact v.elim0
    exact congrArg Sum.inl hw
  · have hn := congrArg norm h
    norm_num only [vertex, Sum.elim_inl, Sum.elim_inr, norm_zero, C.norm_point] at hn
  · have hn := congrArg norm h
    norm_num only [vertex, Sum.elim_inl, Sum.elim_inr, norm_zero, C.norm_point] at hn
  · exact congrArg Sum.inr (C.point_injective h)

theorem norm_edge (i : Fin n) (t : unitInterval) :
    ‖C.edge (Sum.inr i) t‖ = t := by
  simp [edge,  C.norm_point, Real.norm_eq_abs, abs_of_nonneg t.property.1]

theorem edge_injective (e : Fin 0 ⊕ Fin n) : Function.Injective (C.edge e) := by
  cases e with
  | inl e => exact e.elim0
  | inr i =>
    intro t u h
    exact Subtype.ext (by simpa only [C.norm_edge] using congrArg norm h)

theorem interior_avoids (e : Fin 0 ⊕ Fin n) (t : unitInterval)
    (ht0 : 0 < t) (ht1 : t < 1) (v : (Fin 1 ⊕ Fin 0) ⊕ Fin n) :
    C.edge e t ≠ C.vertex v := by
  cases e with
  | inl e => exact e.elim0
  | inr i =>
    intro h
    have hn := congrArg norm h
    cases v with
    | inl v =>
      have hz : (t : ℝ) = 0 := by simpa only [C.norm_edge, vertex, Sum.elim_inl, norm_zero] using hn
      exact (ne_of_gt ht0) (Subtype.ext hz)
    | inr j =>
      have ho : (t : ℝ) = 1 := by simpa only [C.norm_edge, vertex, Sum.elim_inr, C.norm_point] using hn
      exact (ne_of_lt ht1) (Subtype.ext ho)

theorem interiors_disjoint (e f : Fin 0 ⊕ Fin n) (hef : e ≠ f)
    (t u : unitInterval) (ht0 : 0 < t) (_ht1 : t < 1)
    (_hu0 : 0 < u) (_hu1 : u < 1) : C.edge e t ≠ C.edge f u := by
  cases e with
  | inl e => exact e.elim0
  | inr i =>
    cases f with
    | inl f => exact f.elim0
    | inr j =>
      intro h
      have htu : t = u := Subtype.ext (by simpa only [C.norm_edge] using congrArg norm h)
      subst u
      have hp : C.point i = C.point j := (smul_right_inj (show (t : ℝ) ≠ 0 from ne_of_gt ht0)).mp h
      exact hef (congrArg Sum.inr (C.point_injective hp))

end RadialPortConfiguration

/-- Assemble the literal primitive with its independently specified radial
circle configuration; this is a complete actual disk drawing. -/
def primitiveDrawing (l : S.LeftLabel) (C : RadialPortConfiguration (S.leftArity l)) :
    PlanarDrawing (primitive l).graph
      (Sum.inr : Fin (S.leftArity l) → (Fin 1 ⊕ Fin 0) ⊕ Fin (S.leftArity l)) where
  vertex := C.vertex
  vertex_injective := C.vertex_injective
  vertex_in_disk := by rintro (v | i); simp [RadialPortConfiguration.vertex]; exact (C.norm_point i).le
  edge := C.edge
  edge_continuous := by rintro (e | i); exact e.elim0; dsimp [RadialPortConfiguration.edge]; fun_prop
  edge_injective := C.edge_injective
  edge_left := by rintro (e | i); exact e.elim0; simp [RadialPortConfiguration.edge, RadialPortConfiguration.vertex, graph, primitive]
  edge_right := by rintro (e | i); exact e.elim0; simp [RadialPortConfiguration.edge, RadialPortConfiguration.vertex, graph, primitive]
  edge_in_disk := by rintro (e | i) t; exact e.elim0; rw [C.norm_edge]; exact t.property.2
  interior_avoids_vertices := C.interior_avoids
  interiors_disjoint := C.interiors_disjoint
  external_injective := Sum.inr_injective
  angle := C.angle
  angle_pos := C.angle_pos
  angle_lt_one := C.angle_lt_one
  angle_strictMono := C.angle_strictMono
  external_vertex := C.point_eq_boundary

/-- The radial primitive preserves its marked first port and every local
argument position, including the positive orientation. -/
def primitiveOrderedPlanar (l : S.LeftLabel) (C : RadialPortConfiguration (S.leftArity l)) :
    (primitive l).OrderedPlanar where
  drawing := primitiveDrawing l C
  leftOrder _ := {
    rotation := 1
    rotation_ne_zero := one_ne_zero
    time := C.time
    time_strictMono := C.time_strictMono
    time_range := C.time_range
    speed := C.speed
    speed_pos := C.speed_pos
    radius := 1
    radius_pos := by norm_num
    germ := by
      intro i t _
      change Fin (S.leftArity l) at i
      change (t : ℝ) • C.point i = 0 + (t : ℝ) • (C.speed i • (1 * twoCenterSquare (C.time i)))
      rw [zero_add, one_mul, C.point_eq_square] }
  rightOrder v := v.elim0

/-- Two positive radial directions at the upper inscribed-square corners. -/
def binaryRadialPortConfiguration : RadialPortConfiguration 2 where
  point := ![squarePoint 1 1, squarePoint (-1) 1]
  norm_point := by
    intro i
    fin_cases i
    · change ‖squarePoint 1 1‖ = 1
      rw [squarePoint_one_one]; exact norm_boundaryPoint _
    · change ‖squarePoint (-1) 1‖ = 1
      rw [squarePoint_neg_one_one]; exact norm_boundaryPoint _
  point_injective := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [squarePoint_inj]
    all_goals norm_num at h
  angle := ![1/8, 3/8]
  angle_pos := by intro i; fin_cases i <;> norm_num
  angle_lt_one := by intro i; fin_cases i <;> norm_num
  angle_strictMono := by intro i j hij; fin_cases i <;> fin_cases j <;> norm_num at *
  point_eq_boundary := by
    intro i
    fin_cases i
    · exact squarePoint_one_one
    · exact squarePoint_neg_one_one
  time := ![1,2]
  time_strictMono := by intro i j hij; fin_cases i <;> fin_cases j <;> norm_num at *
  time_range := by intro i; fin_cases i <;> norm_num
  speed := fun _ => squareScale
  speed_pos := fun _ => squareScale_pos
  point_eq_square := by
    intro i
    fin_cases i <;> apply Complex.ext <;> norm_num [squarePoint, twoCenterSquare]

/-- Restrict the explicit binary radial configuration to an initial segment;
this covers nullary and unary labels without changing the first port. -/
def smallRadialPortConfiguration (n : ℕ) (hn : n ≤ 2) : RadialPortConfiguration n where
  point i := binaryRadialPortConfiguration.point (Fin.castLE hn i)
  norm_point i := binaryRadialPortConfiguration.norm_point _
  point_injective := by
    intro i j h
    exact Fin.ext (congrArg (fun i : Fin 2 => i.val) (binaryRadialPortConfiguration.point_injective h))
  angle i := binaryRadialPortConfiguration.angle (Fin.castLE hn i)
  angle_pos i := binaryRadialPortConfiguration.angle_pos _
  angle_lt_one i := binaryRadialPortConfiguration.angle_lt_one _
  angle_strictMono := by
    intro i j hij
    apply binaryRadialPortConfiguration.angle_strictMono
    exact hij
  point_eq_boundary i := binaryRadialPortConfiguration.point_eq_boundary _
  time i := binaryRadialPortConfiguration.time (Fin.castLE hn i)
  time_strictMono := by
    intro i j hij
    apply binaryRadialPortConfiguration.time_strictMono
    exact hij
  time_range i := binaryRadialPortConfiguration.time_range _
  speed i := binaryRadialPortConfiguration.speed (Fin.castLE hn i)
  speed_pos i := binaryRadialPortConfiguration.speed_pos _
  point_eq_square i := binaryRadialPortConfiguration.point_eq_square _

/-- Actual ordered planar primitive inclusion for all nullary, unary, and
binary left labels, including the controlled family's pins and X01. -/
theorem primitive_orderedPlanar_of_arity_le_two (l : S.LeftLabel)
    (hl : S.leftArity l ≤ 2) : Nonempty (primitive l).OrderedPlanar :=
  ⟨primitiveOrderedPlanar l (smallRadialPortConfiguration _ hl)⟩

end AllLeftGadget
end
end MatchgateWidth
