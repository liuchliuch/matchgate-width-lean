import MatchgateWidth.LabelledInstances
import MatchgateWidth.ControlledQutrit

/-! Concrete two-link closed stars as actual labelled ordered planar instances. -/
namespace MatchgateWidth
noncomputable section
open scoped Classical

/-- Three unary pins, one binary label, and one right label of declared arity n. -/
abbrev starLanguageShape (n : ℕ) : LabelledShape where
  LeftLabel := Fin 3 ⊕ Fin 1
  RightLabel := Fin 1
  leftFinite := inferInstance
  rightFinite := inferInstance
  leftArity := fun l => match l with | .inl _ => 1 | .inr _ => 2
  rightArity := fun _ => n

/-- Every leaf is unary; every edge joins its own leaf to the sole center. -/
abbrev labelledStar (n : ℕ) (labels : Fin n → Fin 3) :
    LabelledInstance (starLanguageShape n) n 1 n where
  leftLabel i := Sum.inl (labels i)
  rightLabel _ := 0
  leftIncidence := {
    toFun := fun p => p.1
    invFun := fun i => ⟨i,0⟩
    left_inv := by rintro ⟨i,p⟩; have hp : p = 0 := Subsingleton.elim _ _; subst p; rfl
    right_inv := fun _ => rfl }
  rightIncidence := {
    toFun := fun p => p.2
    invFun := fun i => ⟨0,i⟩
    left_inv := by rintro ⟨v,i⟩; have hv : v = 0 := Subsingleton.elim _ _; subst v; rfl
    right_inv := fun _ => rfl }

/-- This instance's partition sum is precisely the ordinary star contraction. -/
theorem labelledStar_value {D : Type} [Fintype D] (n : ℕ) (labels : Fin n → Fin 3)
    (F : LabelledLanguage (starLanguageShape n) D) :
    (labelledStar n labels).value F =
      starContract (F.right 0) (fun i d => F.left (Sum.inl (labels i)) (fun _ => d)) := by
  simp only [LabelledInstance.value, starContract, labelledStar, Fintype.prod_unique, Equiv.coe_fn_mk]
  apply Finset.sum_congr (by ext; simp)
  intro x _
  exact mul_comm _ _

/-- Distinct fan rays lie on the east edge of the positive square. -/
def starHeight {n : ℕ} (i : Fin n) : ℝ := i.val / (n + 1)
def starRay {n : ℕ} (i : Fin n) : ℂ := ⟨1,starHeight i⟩
def starTime {n : ℕ} (i : Fin n) : ℝ := (1 + starHeight i) / 2

theorem starHeight_bounds {n : ℕ} (i : Fin n) : 0 ≤ starHeight i ∧ starHeight i < 1 := by
  have hn : (0 : ℝ) < n + 1 := by positivity
  have hi : (i.val : ℝ) < n := by exact_mod_cast i.isLt
  refine ⟨by unfold starHeight; positivity, ?_⟩
  exact (div_lt_one hn).mpr (by linarith)

theorem starHeight_strictMono {n : ℕ} : StrictMono (starHeight (n := n)) := by
  intro i j hij
  have hn : (0 : ℝ) < n + 1 := by positivity
  apply (div_lt_div_iff_of_pos_right hn).mpr
  exact_mod_cast hij

theorem starTime_strictMono {n : ℕ} : StrictMono (starTime (n := n)) := by
  intro i j hij
  dsimp [starTime]
  linarith [starHeight_strictMono hij]

theorem starTime_range {n : ℕ} (i : Fin n) : 0 ≤ starTime i ∧ starTime i < 4 := by
  dsimp [starTime]
  constructor <;> linarith [(starHeight_bounds i).1, (starHeight_bounds i).2]

theorem starRay_square {n : ℕ} (i : Fin n) : starRay i = twoCenterSquare (starTime i) := by
  have hi : starTime i ≤ 1 := by dsimp [starTime]; linarith [(starHeight_bounds i).2]
  rw [twoCenterSquare, ite_eq_left hi]
  apply Complex.ext
  · rfl
  · dsimp [starRay, starTime]; ring

def starVertex {n : ℕ} : Fin n ⊕ Fin 1 → ℂ := Sum.elim starRay (fun _ => 0)
def starEdge {n : ℕ} (i : Fin n) (t : unitInterval) : ℂ := (1 - (t : ℝ)) • starRay i

theorem starVertex_injective {n : ℕ} : Function.Injective (starVertex (n := n)) := by
  rintro (i | i) (j | j) h
  · have hh := congrArg Complex.im h
    exact congrArg Sum.inl (starHeight_strictMono.injective hh)
  · have hh := congrArg Complex.re h
    simp [starVertex, starRay] at hh
  · have hh := congrArg Complex.re h
    simp [starVertex, starRay] at hh
  · exact congrArg Sum.inr (Subsingleton.elim _ _)

theorem starEdge_injective {n : ℕ} (i : Fin n) : Function.Injective (starEdge i) := by
  intro t u h
  have hh := congrArg Complex.re h
  apply Subtype.ext
  simpa [starEdge, starRay] using hh

theorem starEdge_avoids {n : ℕ} (i : Fin n) (t : unitInterval)
    (ht0 : 0 < t) (ht1 : t < 1) (v : Fin n ⊕ Fin 1) :
    starEdge i t ≠ starVertex v := by
  intro h
  have hh := congrArg Complex.re h
  cases v <;> simp [starEdge, starVertex, starRay] at hh
  · exact (ne_of_gt ht0) hh
  · have : (t : ℝ) = 1 := by linarith
    exact (ne_of_lt ht1) (Subtype.ext this)

theorem starEdge_disjoint {n : ℕ} (i j : Fin n) (hij : i ≠ j)
    (t u : unitInterval) (_ht0 : 0 < t) (_ht1 : t < 1)
    (_hu0 : 0 < u) (hu1 : u < 1) : starEdge i t ≠ starEdge j u := by
  intro h
  have hr := congrArg Complex.re h
  have hi := congrArg Complex.im h
  simp [starEdge, starRay] at hr hi
  have htu : (t : ℝ) = u := by linarith
  rw [htu] at hi
  have hpos : (1 - (u : ℝ)) ≠ 0 := by have hu : (u : ℝ) < 1 := hu1; linarith
  exact hij (starHeight_strictMono.injective (mul_left_cancel₀ hpos hi))

def labelledStarDrawing (n : ℕ) (labels : Fin n → Fin 3) :
    PlaneArcDrawing (labelledStar n labels).graph where
  vertex := starVertex
  vertex_injective := starVertex_injective
  edge := starEdge
  edge_continuous := by intro i; unfold starEdge; fun_prop
  edge_injective := starEdge_injective
  edge_left := by intro i; simp [starEdge, starVertex, LabelledInstance.graph, labelledStar]
  edge_right := by intro i; simp [starEdge, starVertex, LabelledInstance.graph, labelledStar]
  interior_avoids_vertices := starEdge_avoids
  interiors_disjoint := starEdge_disjoint

/-- The center's marked order is exactly 0,1,...,n-1; no reflection is used. -/
def labelledStarPlanar (n : ℕ) (labels : Fin n → Fin 3) :
    (labelledStar n labels).OrderedPlanar where
  drawing := labelledStarDrawing n labels
  leftOrder v := {
    rotation := -1
    rotation_ne_zero := by norm_num
    time := fun _ => starTime v
    time_strictMono := by intro i j hij; have : i = j := Subsingleton.elim _ _; subst j; exact (lt_irrefl _ hij).elim
    time_range := fun _ => starTime_range v
    speed := fun _ => 1
    speed_pos := fun _ => by norm_num
    radius := 1
    radius_pos := by norm_num
    germ := by
      intro i t ht
      change (1 - (t : ℝ)) • starRay v = starRay v +
        (t : ℝ) • ((1 : ℝ) • ((-1 : ℂ) * twoCenterSquare (starTime v)))
      rw [← starRay_square]
      simp
      ring }
  rightOrder v := {
    rotation := 1
    rotation_ne_zero := by norm_num
    time := starTime
    time_strictMono := starTime_strictMono
    time_range := starTime_range
    speed := fun _ => 1
    speed_pos := fun _ => by norm_num
    radius := 1
    radius_pos := by norm_num
    germ := by
      intro i t ht
      change (1 - (LabelledInstance.reverseParameter t : ℝ)) • starRay i =
        0 + (t : ℝ) • ((1 : ℝ) • ((1 : ℂ) * twoCenterSquare (starTime i)))
      simp [LabelledInstance.reverseParameter, ← starRay_square] }

/-- Exact equivalence yields equality of these particular stars by applying
its all-planar-instance quantifier to the constructed geometric certificate. -/
theorem ExactlyLabelledEquivalent.labelledStar {n : ℕ} {T : LabelledShape}
    {D E : Type} [Fintype D] [Fintype E]
    {F : LabelledLanguage (starLanguageShape n) D} {G : LabelledLanguage T E}
    (h : ExactlyLabelledEquivalent F G) :
    ∃ e : LabelledShapeEquiv (starLanguageShape n) T, ∀ labels : Fin n → Fin 3,
      starContract (F.right 0) (fun i d => F.left (Sum.inl (labels i)) (fun _ => d)) =
        starContract ((e.pullback G).right 0)
          (fun i d => (e.pullback G).left (Sum.inl (labels i)) (fun _ => d)) := by
  obtain ⟨e,he⟩ := h
  refine ⟨e, fun labels => ?_⟩
  have hs := he n 1 n (MatchgateWidth.labelledStar n labels) ⟨labelledStarPlanar n labels⟩
  simpa only [labelledStar_value] using hs

/-- Two fixed zero link labels, followed by the ordered hard labels 0 or 2. -/
def closedStarLabelSequence {k : ℕ} (z : BooleanInput k) : Fin (k + 2) → Fin 3 :=
  Fin.cons 0 (Fin.cons 0 (fun i => hardStarLabel (z i)))

/-- The complete controlled qutrit tensor in the source's linear port order. -/
def orderedControlledQutrit {k : ℕ} (f : BooleanTable k ℂ) (j : Fin k)
    (x : Fin (k + 2) → Fin 3) : ℂ :=
  controlledQutrit f j (Sum.elim (fun l => if l = 0 then x 0 else x 1)
    (fun i => x i.succ.succ))

/-- All five source labels, with no deletion of the unused binary label. -/
def controlledLabelledLanguage {k : ℕ} (f : BooleanTable k ℂ) (j : Fin k) :
    LabelledLanguage (starLanguageShape (k + 2)) (Fin 3) where
  left l := match l with
    | .inl b => fun x => @coordinatePin ℂ (Fin 3) _ (Classical.decEq _) b (x 0)
    | .inr _ => qutritNeqTensor
  right _ := orderedControlledQutrit f j

theorem orderedControlledQutrit_closed {k : ℕ} (f : BooleanTable k ℂ)
    (j : Fin k) (z : BooleanInput k) :
    orderedControlledQutrit f j (closedStarLabelSequence z) = f z := by
  change controlledQutrit f j _ = f z
  have he : (Sum.elim
      (fun l : Fin 2 => if l = 0 then closedStarLabelSequence z 0
        else closedStarLabelSequence z 1)
      (fun i => closedStarLabelSequence z i.succ.succ)) =
      controlledQutritAssignment 0 0 z := by
    funext p
    cases p with
    | inl l => fin_cases l <;> simp [closedStarLabelSequence, controlledQutritAssignment]
    | inr i => simp [closedStarLabelSequence, controlledQutritAssignment,
        hardStarLabel, hardQutritLabel]
  rw [he, controlledQutrit_00]

/-- The source instance's value is exactly f(z), by summing genuine coordinate
pins in the finite partition function. This is not an observational premise. -/
theorem controlledLabelledStar_value {k : ℕ} (f : BooleanTable k ℂ)
    (j : Fin k) (z : BooleanInput k) :
    (labelledStar (k + 2) (closedStarLabelSequence z)).value
      (controlledLabelledLanguage f j) = f z := by
  rw [labelledStar_value]
  change starContract (orderedControlledQutrit f j)
    (fun i => @coordinatePin ℂ (Fin 3) _ (Classical.decEq _)
      (closedStarLabelSequence z i)) = f z
  exact (starContract_coordinatePins (orderedControlledQutrit f j)
    (closedStarLabelSequence z)).trans (orderedControlledQutrit_closed f j z)

/-- The two-link star evaluations follow from the full exact-equivalence
quantifier and the explicit planar/order witnesses. The competing domain and
its label tensors are unrestricted finite data. -/
theorem exactEquivalence_closedStarValues {k : ℕ} {T : LabelledShape}
    {E : Type} [Fintype E] (f : BooleanTable k ℂ) (j : Fin k)
    (G : LabelledLanguage T E)
    (h : ExactlyLabelledEquivalent (controlledLabelledLanguage f j) G) :
    ∃ e : LabelledShapeEquiv (starLanguageShape (k + 2)) T, ∀ z,
      f z = starContract ((e.pullback G).right 0)
        (closedStarLeaves (fun b d => (e.pullback G).left (Sum.inl b) (fun _ => d)) z) := by
  obtain ⟨e,he⟩ := h
  refine ⟨e, fun z => ?_⟩
  have hs := he (k + 2) 1 (k + 2)
    (labelledStar (k + 2) (closedStarLabelSequence z))
    ⟨labelledStarPlanar (k + 2) (closedStarLabelSequence z)⟩
  rw [controlledLabelledStar_value, labelledStar_value] at hs
  convert hs using 2
  funext i d
  induction i using Fin.cases with
  | zero => rfl
  | succ i =>
    induction i using Fin.cases with
    | zero => rfl
    | succ i => rfl

end
end MatchgateWidth
