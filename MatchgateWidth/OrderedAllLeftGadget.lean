import MatchgateWidth.LabelledInstances
import MatchgateWidth.TransformedSupport
import Mathlib.Algebra.BigOperators.Group.Finset.Pi

/-!
# Actual finite ordered all-left gadgets

The incidence bijections enforce exactly one incidence on each side of every
internal edge and exactly one left incidence on every dangling edge. Geometric
planarity and local port orders are independent data, not consequences of a
signature identity. The value is the actual finite tensor-network sum.

This module supplies the source gadget domain for boundary-support statements.
It does not assume that substituting many-wire matchgates produces an ordered
planar drawing, and does not put the desired matchgate identity in the gadget
definition.
-/
namespace MatchgateWidth
noncomputable section
open scoped Classical
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 200000
local instance (priority := 2000) orderedGadgetFinDecidableEq (m : ℕ) : DecidableEq (Fin m) := Classical.decEq _

/-- A finite labelled bipartite gadget whose dangling edges all meet left
vertices. Each boundary position is already fixed by `Fin n`. -/
structure AllLeftGadget (S : LabelledShape) (a b c n : ℕ) where
  leftLabel : Fin a → S.LeftLabel
  rightLabel : Fin b → S.RightLabel
  leftIncidence : (Σ v : Fin a, Fin (S.leftArity (leftLabel v))) ≃ (Fin c ⊕ Fin n)
  rightIncidence : (Σ v : Fin b, Fin (S.rightArity (rightLabel v))) ≃ Fin c

namespace AllLeftGadget
variable {S : LabelledShape} {a b c n : ℕ}

/-- Local ports at both sorts of primitive vertices. -/
abbrev Ports (I : AllLeftGadget S a b c n) : Fin a ⊕ Fin b → Type
  | Sum.inl v => Fin (S.leftArity (I.leftLabel v))
  | Sum.inr v => Fin (S.rightArity (I.rightLabel v))

instance (I : AllLeftGadget S a b c n) (v : Fin a ⊕ Fin b) : Fintype (I.Ports v) := by
  cases v <;> dsimp [Ports] <;> exact inferInstance

/-- Literal local incidence with an internal edge or boundary position. -/
def incidence (I : AllLeftGadget S a b c n) :
    (v : Fin a ⊕ Fin b) → I.Ports v → Fin c ⊕ Fin n
  | Sum.inl v, i => I.leftIncidence ⟨v,i⟩
  | Sum.inr v, i => Sum.inl (I.rightIncidence ⟨v,i⟩)

/-- Every boundary edge has its actual unique left endpoint. -/
def boundaryVertex (I : AllLeftGadget S a b c n) (p : Fin n) : Fin a :=
  (I.leftIncidence.symm (Sum.inr p)).1

def boundaryPort (I : AllLeftGadget S a b c n) (p : Fin n) :
    I.Ports (Sum.inl (I.boundaryVertex p)) :=
  (I.leftIncidence.symm (Sum.inr p)).2

@[simp] theorem incidence_boundary (I : AllLeftGadget S a b c n) (p : Fin n) :
    I.incidence (Sum.inl (I.boundaryVertex p)) (I.boundaryPort p) = Sum.inr p :=
  I.leftIncidence.apply_symm_apply _

/-- There is no hidden extra incidence at a dangling boundary position. -/
theorem boundary_unique (I : AllLeftGadget S a b c n) (p : Fin n)
    (v : Fin a ⊕ Fin b) (i : I.Ports v) (hi : I.incidence v i = Sum.inr p) :
    (⟨v,i⟩ : Sigma I.Ports) = ⟨Sum.inl (I.boundaryVertex p),I.boundaryPort p⟩ := by
  cases v with
  | inl v =>
    have h : (⟨v,i⟩ : Σ v : Fin a, Fin (S.leftArity (I.leftLabel v))) =
        I.leftIncidence.symm (Sum.inr p) := I.leftIncidence.injective
      (hi.trans (I.leftIncidence.apply_symm_apply _).symm)
    exact congrArg (fun q : Σ v : Fin a, Fin (S.leftArity (I.leftLabel v)) =>
      (⟨Sum.inl q.1,q.2⟩ : Sigma I.Ports)) h
  | inr v => exact (Sum.inl_ne_inr hi).elim

/-- Tensor at each primitive vertex, preserving its declared argument order. -/
def tensors {D : Type} (I : AllLeftGadget S a b c n) (F : LabelledLanguage S D) :
    (v : Fin a ⊕ Fin b) → (I.Ports v → D) → ℂ
  | Sum.inl v => F.left (I.leftLabel v)
  | Sum.inr v => F.right (I.rightLabel v)

/-- The boundary tensor is the actual finite contraction, with no linear-span
closure or algebraic realizability certificate added. -/
def value {D : Type} [Fintype D] (I : AllLeftGadget S a b c n)
    (F : LabelledLanguage S D) : (Fin n → D) → ℂ :=
  networkValue I.incidence (I.tensors F)

/-- An explicit coordinate formula for the gadget boundary tensor. -/
theorem value_eq {D : Type} [Fintype D] (I : AllLeftGadget S a b c n)
    (F : LabelledLanguage S D) (z : Fin n → D) :
    I.value F z = ∑ x : Fin c → D,
      (∏ v, F.left (I.leftLabel v)
        (fun i => Sum.elim x z (I.leftIncidence ⟨v,i⟩))) *
      ∏ v, F.right (I.rightLabel v) (fun i => x (I.rightIncidence ⟨v,i⟩)) := by
  classical
  simp only [value, networkValue, Fintype.prod_sum_type, tensors, incidence, Sum.elim_inl]
  all_goals congr <;> exact Subsingleton.elim _ _

/-- The exact underlying graph, with an extra degree-one terminal at each
boundary edge. Weights are irrelevant to tensor-network semantics. -/
def graph (I : AllLeftGadget S a b c n) :
    WeightedGraph ((Fin a ⊕ Fin b) ⊕ Fin n) (Fin c ⊕ Fin n) ℂ where
  left e := Sum.inl (Sum.inl (I.leftIncidence.symm e).1)
  right := Sum.elim (fun e => Sum.inl (Sum.inr (I.rightIncidence.symm e).1)) Sum.inr
  loopless := by rintro (e | p) <;> simp
  weight _ := 1

/-- Source connectedness ignores dangling half-edges. Empty graphs are not
called connected. No geometric or matchgate assertion enters this predicate. -/
def Connected (I : AllLeftGadget S a b c n) : Prop :=
  Nonempty (Fin a ⊕ Fin b) ∧ ∀ u v : Fin a ⊕ Fin b,
    Relation.ReflTransGen (fun x y => ∃ e : Fin c,
      (x = Sum.inl (I.leftIncidence.symm (Sum.inl e)).1 ∧
       y = Sum.inr (I.rightIncidence.symm e).1) ∨
      (y = Sum.inl (I.leftIncidence.symm (Sum.inl e)).1 ∧
       x = Sum.inr (I.rightIncidence.symm e).1)) u v

/-- An actual disk embedding and exact positive local order. The inherited
boundary order is the strictly increasing marked order in `PlanarDrawing`. -/
structure OrderedPlanar (I : AllLeftGadget S a b c n) where
  drawing : PlanarDrawing I.graph (Sum.inr : Fin n → (Fin a ⊕ Fin b) ⊕ Fin n)
  leftOrder : ∀ v, LabelledInstance.PositivePortOrder
    (drawing.vertex (Sum.inl (Sum.inl v)))
    (fun i t => drawing.edge (I.leftIncidence ⟨v,i⟩) t)
  rightOrder : ∀ v, LabelledInstance.PositivePortOrder
    (drawing.vertex (Sum.inl (Sum.inr v)))
    (fun i t => drawing.edge (Sum.inl (I.rightIncidence ⟨v,i⟩))
      (LabelledInstance.reverseParameter t))

/-- Boundary-support monotonicity for every actual all-left gadget, at its
literal primitive left endpoint. This uses no embedding normalization. -/
theorem boundary_support_le {D : Type} [Fintype D]
    (I : AllLeftGadget S a b c n) (F : LabelledLanguage S D) (p : Fin n) :
    columnSupport (portFlatten (I.value F) p) ≤
      columnSupport (portFlatten (F.left (I.leftLabel (I.boundaryVertex p)))
        (I.boundaryPort p)) := by
  classical
  exact network_boundary_support_le_of_unique_incidence I.incidence (I.tensors F)
    (Sum.inl (I.boundaryVertex p)) (I.boundaryPort p) p
    (I.incidence_boundary p) (I.boundary_unique p)

end AllLeftGadget
end
end MatchgateWidth
