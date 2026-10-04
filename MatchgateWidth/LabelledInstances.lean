import MatchgateWidth.ExactStarLowerBound
import MatchgateWidth.TwoCenterDrawing
import MatchgateWidth.DiskMatchgateCharacterization

/-!
# Finite labelled ordered planar instances

A closed instance has two finite vertex sets and two incidence bijections onto
one finite edge set. Its value is the actual sum over all edge assignments.
Labels carry arities, including zero. Relabelling changes only labels, never
vertices, edges, incidence, the marked first port, or port order.

The geometric model below allows arbitrary continuous simple arcs away from
vertices, and requires locally radial germs at vertices. Its increasing square
parameters specify the positive cyclic order with a marked first port. This is
a precise geometric model of finite ordered planar instances, not a theorem
normalizing all topological plane embeddings into this regularity convention.
That normalization/source-model bridge is deliberately not asserted here.
-/
namespace MatchgateWidth
noncomputable section
open scoped Classical

/-- The finite left and right label sets, with their declared arities. -/
structure LabelledShape where
  LeftLabel : Type
  RightLabel : Type
  leftFinite : Fintype LeftLabel
  rightFinite : Fintype RightLabel
  leftArity : LeftLabel → ℕ
  rightArity : RightLabel → ℕ

attribute [instance] LabelledShape.leftFinite LabelledShape.rightFinite

/-- A labelled complex language; distinct labels may carry identical tensors. -/
structure LabelledLanguage (S : LabelledShape) (D : Type) where
  left : (l : S.LeftLabel) → (Fin (S.leftArity l) → D) → ℂ
  right : (l : S.RightLabel) → (Fin (S.rightArity l) → D) → ℂ

/-- A bipartite multigraph with one incidence on each side of each edge.
`Fin (arity label)` is the linearized cyclic order, marked at zero if nonempty. -/
structure LabelledInstance (S : LabelledShape) (a b c : ℕ) where
  leftLabel : Fin a → S.LeftLabel
  rightLabel : Fin b → S.RightLabel
  leftIncidence : (Σ v : Fin a, Fin (S.leftArity (leftLabel v))) ≃ Fin c
  rightIncidence : (Σ v : Fin b, Fin (S.rightArity (rightLabel v))) ≃ Fin c

namespace LabelledInstance
variable {S : LabelledShape} {a b c : ℕ}

/-- Forget labels but retain the same edge identities and endpoints. -/
def graph (I : LabelledInstance S a b c) : WeightedGraph (Fin a ⊕ Fin b) (Fin c) ℂ where
  left e := Sum.inl (I.leftIncidence.symm e).1
  right e := Sum.inr (I.rightIncidence.symm e).1
  loopless := by intro e; simp
  weight _ := 1

/-- The full Holant partition sum, with no conjugation or normalization. -/
def value {D : Type} [Fintype D] (I : LabelledInstance S a b c)
    (F : LabelledLanguage S D) : ℂ := by
  classical
  exact ∑ x : Fin c → D,
    (∏ v, F.left (I.leftLabel v) (fun i => x (I.leftIncidence ⟨v,i⟩))) *
    (∏ v, F.right (I.rightLabel v) (fun i => x (I.rightIncidence ⟨v,i⟩)))

/-- Parameter reversal changes only the direction in which an arc is traversed. -/
def reverseParameter (t : unitInterval) : unitInterval :=
  ⟨1 - t, by constructor <;> linarith [t.property.1, t.property.2]⟩

/-- Genuine local positive port order. The rotation is multiplication by a
nonzero complex scalar, hence cannot reflect the plane. Different speeds allow
unequal lengths of incident edges. Only a positive initial germ is prescribed. -/
structure PositivePortOrder {n : ℕ} (vertex : ℂ)
    (arc : Fin n → unitInterval → ℂ) where
  rotation : ℂ
  rotation_ne_zero : rotation ≠ 0
  time : Fin n → ℝ
  time_strictMono : StrictMono time
  time_range : ∀ i, 0 ≤ time i ∧ time i < 4
  speed : Fin n → ℝ
  speed_pos : ∀ i, 0 < speed i
  radius : unitInterval
  radius_pos : 0 < radius
  germ : ∀ i t, t ≤ radius → arc i t = vertex +
    (t : ℝ) • (speed i • (rotation * twoCenterSquare (time i)))

/-- The incidence bijections are used directly in the local order witnesses,
so no independent port permutation can be hidden in the planar certificate. -/
structure OrderedPlanar (I : LabelledInstance S a b c) where
  drawing : PlaneArcDrawing I.graph
  leftOrder : ∀ v, PositivePortOrder (drawing.vertex (Sum.inl v))
    (fun i t => drawing.edge (I.leftIncidence ⟨v,i⟩) t)
  rightOrder : ∀ v, PositivePortOrder (drawing.vertex (Sum.inr v))
    (fun i t => drawing.edge (I.rightIncidence ⟨v,i⟩) (reverseParameter t))

end LabelledInstance

/-- Bijections of the two label sets preserving every declared arity. -/
structure LabelledShapeEquiv (S T : LabelledShape) where
  left : S.LeftLabel ≃ T.LeftLabel
  right : S.RightLabel ≃ T.RightLabel
  leftArity : ∀ l, T.leftArity (left l) = S.leftArity l
  rightArity : ∀ l, T.rightArity (right l) = S.rightArity l

namespace LabelledShapeEquiv
variable {S T : LabelledShape}

/-- Pull tensors back to the original labels. `Fin.cast` preserves every index
value: this is an arity equality cast, not a cyclic shift or permutation. -/
def pullback {D : Type} (e : LabelledShapeEquiv S T)
    (F : LabelledLanguage T D) : LabelledLanguage S D where
  left l x := F.left (e.left l) (fun i => x (Fin.cast (e.leftArity l) i))
  right l x := F.right (e.right l) (fun i => x (Fin.cast (e.rightArity l) i))

/-- Identity relabelling. -/
def refl (S : LabelledShape) : LabelledShapeEquiv S S where
  left := Equiv.refl _
  right := Equiv.refl _
  leftArity _ := rfl
  rightArity _ := rfl

@[simp] theorem pullback_refl {D : Type} (F : LabelledLanguage S D) :
    (refl S).pullback F = F := by cases F; rfl
end LabelledShapeEquiv

/-- Exact labelled equivalence quantifies over all finite ordered planar
instances in the geometric model above. The two sides evaluate the very same
instance; the original drawing and incidence bijections are never replaced. -/
def ExactlyLabelledEquivalent {S T : LabelledShape} {D E : Type}
    [Fintype D] [Fintype E] (F : LabelledLanguage S D) (G : LabelledLanguage T E) : Prop :=
  ∃ e : LabelledShapeEquiv S T, ∀ (a b c : ℕ) (I : LabelledInstance S a b c),
    Nonempty I.OrderedPlanar → I.value F = I.value (e.pullback G)

theorem ExactlyLabelledEquivalent.refl {S : LabelledShape} {D : Type}
    [Fintype D] (F : LabelledLanguage S D) : ExactlyLabelledEquivalent F F := by
  refine ⟨LabelledShapeEquiv.refl S, ?_⟩
  intro a b c I hI
  simp

/-- A valid common width presentation, using exact disk-defined graph
matchgates for every component, not an assumed MGI or rank condition. -/
structure LabelledCommonPresentation (S : LabelledShape) (E : Type)
    [Fintype E] (r : ℕ) where
  base : E → BooleanInput r → ℂ
  left : (l : S.LeftLabel) → (Fin (S.leftArity l) → E) → ℂ
  rightPreimage : (l : S.RightLabel) → BooleanTable (S.rightArity l * r) ℂ
  validLeft : ∀ l, BooleanDiskRealizable
    (fun z => leftTransform base (left l) (fun i t => z (finProdFinEquiv (i,t))))
  validRight : ∀ l, BooleanDiskRealizable (rightPreimage l)

namespace LabelledCommonPresentation
variable {S : LabelledShape} {E : Type} [Fintype E] {r : ℕ}

/-- The presentation's induced language on its own arbitrary finite domain. -/
def language (p : LabelledCommonPresentation S E r) : LabelledLanguage S E where
  left := p.left
  right l := rightTransform p.base (fun x => p.rightPreimage l (flattenBooleanBlocks x))
/-- Arity equality transports the flattened left transform without changing
one wire index or block order. -/
theorem leftTransform_cast_arity {n m r : ℕ} {E : Type} [Fintype E]
    (h : n = m) (N : E → BooleanInput r → ℂ) (F : (Fin n → E) → ℂ) :
    (fun z : BooleanInput (m * r) => leftTransform N
      (fun x : Fin m → E => F (fun i => x (Fin.cast h i)))
      (fun i t => z (finProdFinEquiv (i,t)))) =
    castBooleanTable (congrArg (fun a => a * r) h)
      (fun z => leftTransform N F (fun i t => z (finProdFinEquiv (i,t)))) := by
  cases h
  rfl

theorem leftTransform_one_block {E : Type} [Fintype E] {r : ℕ}
    (N : E → BooleanInput r → ℂ) (F : (Fin 1 → E) → ℂ) :
    castBooleanTable (one_mul r)
      (fun z => leftTransform N F (fun i t => z (finProdFinEquiv (i,t)))) =
    unaryTransform N (fun d => F (fun _ => d)) := by
  funext z
  unfold castBooleanTable leftTransform unaryTransform
  apply Fintype.sum_equiv (Equiv.funUnique (Fin 1) E)
  intro x
  simp only [Fintype.prod_unique, Fin.default_eq_zero, Equiv.funUnique_apply]
  congr 2
  · funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    rfl


/-- The corresponding right transform is equally insensitive to an equality
cast; this statement contains no permutation invariance claim. -/
theorem rightTransform_cast_arity {n m r : ℕ} {E : Type} [Fintype E]
    (h : n = m) (N : E → BooleanInput r → ℂ) (Q : BooleanTable (n * r) ℂ) :
    rightTransform N (fun x : Fin m → BooleanInput r =>
      castBooleanTable (congrArg (fun a => a * r) h) Q (flattenBooleanBlocks x)) =
    (fun x : Fin m → E => rightTransform N (fun x => Q (flattenBooleanBlocks x))
      (fun i => x (Fin.cast h i))) := by
  cases h
  rfl

/-- Arity-preserving label bijections transport an entire valid presentation.
Exact graph realizability is retained via the proved disk characterization. -/
def pullback {T : LabelledShape} (p : LabelledCommonPresentation T E r)
    (e : LabelledShapeEquiv S T) : LabelledCommonPresentation S E r where
  base := p.base
  left := (e.pullback p.language).left
  rightPreimage l := castBooleanTable (congrArg (fun a => a * r) (e.rightArity l))
    (p.rightPreimage (e.right l))
  validLeft l := by
    change BooleanDiskRealizable
      (fun z => leftTransform p.base
        (fun x => p.left (e.left l) (fun i => x (Fin.cast (e.leftArity l) i)))
        (fun i t => z (finProdFinEquiv (i,t))))
    rw [leftTransform_cast_arity]
    exact ((p.validLeft (e.left l)).matchgateIdentities.cast _).diskRealizable
  validRight l := ((p.validRight (e.right l)).matchgateIdentities.cast _).diskRealizable

theorem pullback_language {T : LabelledShape} (p : LabelledCommonPresentation T E r)
    (e : LabelledShapeEquiv S T) : (p.pullback e).language = e.pullback p.language := by
  unfold language pullback LabelledShapeEquiv.pullback
  congr 1
  funext l
  exact rightTransform_cast_arity (e.rightArity l) p.base (p.rightPreimage (e.right l))

end LabelledCommonPresentation

/-- The admissible widths include zero, and range over all finite nonempty
competing domains and finite arity-preserving labelled families. -/
def HasExactCommonWidth {S : LabelledShape} {D : Type} [Fintype D]
    (F : LabelledLanguage S D) (r : ℕ) : Prop :=
  ∃ (E : Type) (_ : Fintype E) (_ : Nonempty E) (T : LabelledShape)
    (p : LabelledCommonPresentation T E r), ExactlyLabelledEquivalent F p.language

/-- The minimum in this precise instance model, on languages admitting a valid
equivalent presentation. Identification with the source's unrestricted embedding
model would additionally require the stated normalization bridge. -/
def minimumExactCommonWidth {S : LabelledShape} {D : Type} [Fintype D]
    (F : LabelledLanguage S D) (h : ∃ r, HasExactCommonWidth F r) : ℕ := Nat.find h

theorem minimumExactCommonWidth_spec {S : LabelledShape} {D : Type} [Fintype D]
    (F : LabelledLanguage S D) (h : ∃ r, HasExactCommonWidth F r) :
    HasExactCommonWidth F (minimumExactCommonWidth F h) := Nat.find_spec h

theorem minimumExactCommonWidth_le {S : LabelledShape} {D : Type} [Fintype D]
    (F : LabelledLanguage S D) (h : ∃ r, HasExactCommonWidth F r)
    {r : ℕ} (hr : HasExactCommonWidth F r) : minimumExactCommonWidth F h ≤ r :=
  Nat.find_min' h hr

end
end MatchgateWidth
