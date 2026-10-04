import MatchgateWidth.PlanarWireDrawing
import MatchgateWidth.ControlledQutrit

/-! An explicit straight-segment embedding of the cross-paired two-center
network. The local and outer orders are certified by square-boundary ray
parameters, avoiding any assumption of planarity. -/
namespace MatchgateWidth
noncomputable section
open scoped Classical
variable {k : ℕ}

abbrev TwoCenterDrawingVertex (k : ℕ) := Fin 2 ⊕ (Fin 2 ⊕ (Fin 2 × Fin k))
abbrev TwoCenterDrawingEdge (k : ℕ) := Fin 2 × ControlledQutritPort k

/-- The left fan descends along the left boundary, the right fan is its half-turn. -/
def twoCenterHeight (i : Fin k) : ℝ := 1 - 2 * ((i.val + 1 : ℝ) / (k + 1))

theorem twoCenterHeight_bounds (i : Fin k) : -1 < twoCenterHeight i ∧ twoCenterHeight i < 1 := by
  have hk : (0 : ℝ) < k + 1 := by positivity
  have hi : (i.val : ℝ) < k := by exact_mod_cast i.isLt
  have hp : 0 < ((i.val + 1 : ℝ) / (k + 1)) := by positivity
  have hl : ((i.val + 1 : ℝ) / (k + 1)) < 1 := (div_lt_one hk).mpr (by linarith)
  constructor <;> dsimp [twoCenterHeight] <;> linarith

theorem twoCenterHeight_strictAnti : StrictAnti (twoCenterHeight (k := k)) := by
  intro i j hij
  have hk : (0 : ℝ) < k + 1 := by positivity
  have hi : (i.val : ℝ) < j.val := by exact_mod_cast hij
  have hd : ((i.val + 1 : ℝ) / (k + 1)) < ((j.val + 1 : ℝ) / (k + 1)) :=
    (div_lt_div_iff_of_pos_right hk).mpr (by linarith)
  dsimp [twoCenterHeight]
  linarith

def twoCenterDrawingGraph (k : ℕ) :
    WeightedGraph (TwoCenterDrawingVertex k) (TwoCenterDrawingEdge k) ℂ where
  left e := Sum.inl e.1
  right e := match e.2 with
    | Sum.inl l => Sum.inr (Sum.inl (if e.1 = l then 1 else 0))
    | Sum.inr i => Sum.inr (Sum.inr (e.1, i))
  loopless := by rintro ⟨c, l | i⟩ <;> simp
  weight _ := 1

def twoCenterVertexPoint : TwoCenterDrawingVertex k → ℂ
  | Sum.inl c => if c = 0 then ⟨-1,0⟩ else ⟨1,0⟩
  | Sum.inr (Sum.inl x) => if x = 0 then ⟨0,1⟩ else ⟨0,-1⟩
  | Sum.inr (Sum.inr (c,i)) => if c = 0 then ⟨-2,twoCenterHeight i⟩
      else ⟨2,-twoCenterHeight i⟩

/-- The ordered rays around the left center, starting with the lower link. -/
def twoCenterRay : ControlledQutritPort k → ℂ
  | Sum.inl l => if l = 0 then ⟨1,-1⟩ else ⟨1,1⟩
  | Sum.inr i => ⟨-1,twoCenterHeight i⟩

/-- Both centers use the same rays up to a half-turn, never reflection. -/
def twoCenterEdgeArc (e : TwoCenterDrawingEdge k) (t : unitInterval) : ℂ :=
  if e.1 = 0 then (⟨-1,0⟩ : ℂ) + (t : ℝ) • twoCenterRay e.2
  else (⟨1,0⟩ : ℂ) - (t : ℝ) • twoCenterRay e.2

theorem twoCenterVertexPoint_injective :
    Function.Injective (twoCenterVertexPoint (k := k)) := by
  rintro (c | x | ⟨c,i⟩) (d | y | ⟨d,j⟩) h
  all_goals try fin_cases c
  all_goals try fin_cases d
  all_goals try fin_cases x
  all_goals try fin_cases y
  all_goals norm_num [twoCenterVertexPoint, Complex.ext_iff] at h
  all_goals simp only [Sum.inr.injEq, Prod.mk.injEq, true_and]
  all_goals exact twoCenterHeight_strictAnti.injective h

theorem twoCenterEdgeArc_endpoints (e : TwoCenterDrawingEdge k) :
    twoCenterEdgeArc e 0 = twoCenterVertexPoint ((twoCenterDrawingGraph k).left e) ∧
      twoCenterEdgeArc e 1 = twoCenterVertexPoint ((twoCenterDrawingGraph k).right e) := by
  rcases e with ⟨c,l | i⟩
  · fin_cases c <;> fin_cases l <;>
      simp [twoCenterEdgeArc, twoCenterRay, twoCenterVertexPoint, twoCenterDrawingGraph,
        Complex.ext_iff]
  · fin_cases c <;>
      simp [twoCenterEdgeArc, twoCenterRay, twoCenterVertexPoint, twoCenterDrawingGraph,
        Complex.ext_iff] <;> norm_num

theorem twoCenterEdgeArc_injective (e : TwoCenterDrawingEdge k) :
    Function.Injective (twoCenterEdgeArc e) := by
  intro t u h
  have hr := congrArg Complex.re h
  apply Subtype.ext
  rcases e with ⟨c,l | i⟩
  · fin_cases c <;> fin_cases l <;> simp [twoCenterEdgeArc, twoCenterRay] at hr <;> linarith
  · fin_cases c <;> simp [twoCenterEdgeArc, twoCenterRay] at hr <;> linarith

theorem twoCenterEdgeArc_avoids_vertices (e : TwoCenterDrawingEdge k)
    (t : unitInterval) (ht₀ : 0 < t) (ht₁ : t < 1) (v : TwoCenterDrawingVertex k) :
    twoCenterEdgeArc e t ≠ twoCenterVertexPoint v := by
  intro h
  have hr := congrArg Complex.re h
  have hi := congrArg Complex.im h
  have ht0 : (0 : ℝ) < t := ht₀
  have ht1 : (t : ℝ) < 1 := ht₁
  rcases e with ⟨c,l | i⟩ <;> rcases v with d | x | ⟨d,j⟩
  all_goals fin_cases c
  all_goals first | fin_cases l | skip
  all_goals first | fin_cases d | fin_cases x
  all_goals simp [twoCenterEdgeArc, twoCenterRay, twoCenterVertexPoint] at hr hi
  all_goals try { exact (ne_of_gt ht₀) hr }
  all_goals linarith

theorem twoCenterEdgeArc_disjoint (e f : TwoCenterDrawingEdge k) (hef : e ≠ f)
    (t u : unitInterval) (ht₀ : 0 < t) (ht₁ : t < 1) (hu₀ : 0 < u) (hu₁ : u < 1) :
    twoCenterEdgeArc e t ≠ twoCenterEdgeArc f u := by
  intro h
  have hr := congrArg Complex.re h
  have hi := congrArg Complex.im h
  have ht0 : (0 : ℝ) < t := ht₀
  have ht1 : (t : ℝ) < 1 := ht₁
  have hu0 : (0 : ℝ) < u := hu₀
  have hu1 : (u : ℝ) < 1 := hu₁
  rcases e with ⟨c,l | i⟩ <;> rcases f with ⟨d,m | j⟩
  all_goals fin_cases c <;> fin_cases d
  all_goals first | fin_cases l | skip
  all_goals first | fin_cases m | skip
  all_goals simp [twoCenterEdgeArc, twoCenterRay] at hr hi
  all_goals try { exact hef rfl }
  all_goals try linarith
  all_goals
    have htu : (t : ℝ) = u := by linarith
    rw [htu] at hi
    have hh : twoCenterHeight i = twoCenterHeight j := by nlinarith
    have hij := twoCenterHeight_strictAnti.injective hh
    subst j
    exact hef rfl

/-- Crossing-freeness is proved from the coordinates of every vertex and edge. -/
def twoCenterPlaneDrawing (k : ℕ) : PlaneArcDrawing (twoCenterDrawingGraph k) where
  vertex := twoCenterVertexPoint
  vertex_injective := twoCenterVertexPoint_injective
  edge := twoCenterEdgeArc
  edge_continuous := by
    intro e
    unfold twoCenterEdgeArc
    split_ifs <;> fun_prop
  edge_injective := twoCenterEdgeArc_injective
  edge_left e := (twoCenterEdgeArc_endpoints e).1
  edge_right e := (twoCenterEdgeArc_endpoints e).2
  interior_avoids_vertices := twoCenterEdgeArc_avoids_vertices
  interiors_disjoint := twoCenterEdgeArc_disjoint

/-- Counterclockwise parametrization of a square, starting at its southeast
corner. The last point repeats the first and there are no other repetitions. -/
def twoCenterSquare (r : ℝ) : ℂ :=
  if r ≤ 1 then ⟨1, 2*r-1⟩ else if r ≤ 2 then ⟨3-2*r,1⟩
  else if r ≤ 3 then ⟨-1,5-2*r⟩ else ⟨2*r-7,-1⟩

private theorem continuous_complexMk (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun r => (⟨f r,g r⟩ : ℂ)) := by
  change Continuous (Complex.equivRealProdCLM.symm ∘ (fun r => (f r,g r)))
  exact Complex.equivRealProdCLM.symm.continuous.comp (hf.prodMk hg)

theorem twoCenterSquare_continuous : Continuous twoCenterSquare := by
  unfold twoCenterSquare
  apply continuous_if_le continuous_id continuous_const
  · apply Continuous.continuousOn; apply continuous_complexMk <;> fun_prop
  · apply Continuous.continuousOn
    apply continuous_if_le continuous_id continuous_const
    · apply Continuous.continuousOn; apply continuous_complexMk <;> fun_prop
    · apply Continuous.continuousOn
      apply continuous_if_le continuous_id continuous_const
      · apply Continuous.continuousOn; apply continuous_complexMk <;> fun_prop
      · apply Continuous.continuousOn; apply continuous_complexMk <;> fun_prop
      · intro r hr; change r = 3 at hr; subst r; norm_num
    · intro r hr; change r = 2 at hr; subst r; norm_num
  · intro r hr; change r = 1 at hr; subst r; norm_num

theorem twoCenterSquare_simple : Set.InjOn twoCenterSquare (Set.Ico 0 4) := by
  intro r hr s hs h
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp only [twoCenterSquare] at hre him
  split_ifs at hre him <;> dsimp at hre him <;> rcases hr with ⟨hr0,hr4⟩ <;>
    rcases hs with ⟨hs0,hs4⟩ <;> linarith

@[simp] theorem twoCenterSquare_closed : twoCenterSquare 0 = twoCenterSquare 4 := by
  norm_num [twoCenterSquare, Complex.ext_iff]

/-- The standard link-then-hard local order. -/
def twoCenterOrderedPort : Fin (2+k) → ControlledQutritPort k :=
  Fin.addCases Sum.inl Sum.inr

/-- Successive local square-perimeter parameters: 0, 1, then values in (2,3). -/
def twoCenterLocalTime : Fin (2+k) → ℝ :=
  Fin.addCases (fun l => l.val) (fun i => 2 + (1-twoCenterHeight i)/2)

theorem twoCenterLocalTime_strictMono : StrictMono (twoCenterLocalTime (k := k)) := by
  intro i j hij
  induction i using Fin.addCases with
  | left i =>
    induction j using Fin.addCases with
    | left j =>
      simp only [twoCenterLocalTime, Fin.addCases_left]
      exact_mod_cast hij
    | right j =>
      simp only [twoCenterLocalTime, Fin.addCases_left, Fin.addCases_right]
      have hi : (i.val : ℝ) < 2 := by exact_mod_cast i.isLt
      linarith [(twoCenterHeight_bounds j).2]
  | right i =>
    induction j using Fin.addCases with
    | left j => have := j.isLt; simp only [Fin.lt_def, Fin.val_natAdd, Fin.val_castAdd] at hij; omega
    | right j =>
      simp only [twoCenterLocalTime, Fin.addCases_right]
      have hi : i < j := by simp only [Fin.lt_def, Fin.val_natAdd] at hij ⊢; omega
      linarith [twoCenterHeight_strictAnti hi]

theorem twoCenterLocalTime_bounds (i : Fin (2+k)) :
    0 ≤ twoCenterLocalTime i ∧ twoCenterLocalTime i < 4 := by
  induction i using Fin.addCases with
  | left i => fin_cases i <;> norm_num [twoCenterLocalTime]
  | right i =>
    simp only [twoCenterLocalTime, Fin.addCases_right]
    constructor <;> linarith [(twoCenterHeight_bounds i).1, (twoCenterHeight_bounds i).2]

/-- The empty interior corner is between the two adjacent links. All hard
ports lie strictly in the complementary square sector. -/
theorem twoCenter_local_sectors :
    twoCenterLocalTime (Fin.castAdd k (0 : Fin 2)) = 0 ∧
    twoCenterLocalTime (Fin.castAdd k (1 : Fin 2)) = 1 ∧
    ∀ i : Fin k, 2 < twoCenterLocalTime (Fin.natAdd 2 i) ∧
      twoCenterLocalTime (Fin.natAdd 2 i) < 3 := by
  refine ⟨by simp [twoCenterLocalTime], by simp [twoCenterLocalTime], ?_⟩
  intro i
  simp only [twoCenterLocalTime, Fin.addCases_right]
  constructor <;> linarith [(twoCenterHeight_bounds i).1, (twoCenterHeight_bounds i).2]

/-- Both halves of the upper path have positive height, and both halves of
the lower path have negative height away from the center. -/
theorem twoCenter_paths_above_below (t : unitInterval) (ht : 0 < t) :
    0 < (twoCenterEdgeArc (k := k) (0,Sum.inl 1) t).im ∧
    0 < (twoCenterEdgeArc (k := k) (1,Sum.inl 0) t).im ∧
    (twoCenterEdgeArc (k := k) (0,Sum.inl 0) t).im < 0 ∧
    (twoCenterEdgeArc (k := k) (1,Sum.inl 1) t).im < 0 := by
  have ht' : (0 : ℝ) < t := ht
  simpa [twoCenterEdgeArc, twoCenterRay] using ht'

theorem twoCenterRay_order (i : Fin (2+k)) :
    twoCenterRay (twoCenterOrderedPort i) = twoCenterSquare (twoCenterLocalTime i) := by
  induction i using Fin.addCases with
  | left i => fin_cases i <;> norm_num [twoCenterOrderedPort, twoCenterLocalTime,
      twoCenterRay, twoCenterSquare, Complex.ext_iff]
  | right i =>
    have h₁ : ¬ 2 + (1-twoCenterHeight i)/2 ≤ 1 := by linarith [(twoCenterHeight_bounds i).2]
    have h₂ : ¬ 2 + (1-twoCenterHeight i)/2 ≤ 2 := by linarith [(twoCenterHeight_bounds i).2]
    have h₃ : 2 + (1-twoCenterHeight i)/2 ≤ 3 := by linarith [(twoCenterHeight_bounds i).1]
    simp [twoCenterOrderedPort, twoCenterLocalTime, twoCenterRay, twoCenterSquare,
      h₁, h₂, h₃, Complex.ext_iff]
    ring

/-- At the right center the square is rotated by π, which preserves its
counterclockwise direction and its marked link-then-hard enumeration. -/
theorem twoCenterEdgeArc_local_order (c : Fin 2) (i : Fin (2+k)) (t : unitInterval) :
    twoCenterEdgeArc (c,twoCenterOrderedPort i) t =
      twoCenterVertexPoint (k := k) (Sum.inl c) +
        (t : ℝ) • (if c = 0 then twoCenterSquare (twoCenterLocalTime i)
          else -twoCenterSquare (twoCenterLocalTime i)) := by
  fin_cases c <;> simp [twoCenterEdgeArc, twoCenterVertexPoint, twoCenterRay_order, sub_eq_add_neg]

/-- An enclosing square. It starts at the upper left and travels down the left
side, then up the right side, in the positive orientation. -/
def twoCenterOuterSquare (r : ℝ) : ℂ := -(2 : ℂ) * twoCenterSquare r

def twoCenterOrderedBoundary : Fin (k+k) → TwoCenterDrawingVertex k :=
  Fin.addCases (fun i => Sum.inr (Sum.inr (0,i))) (fun i => Sum.inr (Sum.inr (1,i)))

def twoCenterBoundaryTime : Fin (k+k) → ℝ :=
  Fin.addCases (fun i => (2-twoCenterHeight i)/4) (fun i => 2+(2-twoCenterHeight i)/4)

theorem twoCenterBoundaryTime_strictMono : StrictMono (twoCenterBoundaryTime (k := k)) := by
  intro i j hij
  induction i using Fin.addCases with
  | left i =>
    induction j using Fin.addCases with
    | left j =>
      simp only [twoCenterBoundaryTime, Fin.addCases_left]
      have hi : i < j := by simp only [Fin.lt_def,  Fin.val_castAdd] at hij ⊢; omega
      linarith [twoCenterHeight_strictAnti hi]
    | right j =>
      simp only [twoCenterBoundaryTime, Fin.addCases_left, Fin.addCases_right]
      linarith [(twoCenterHeight_bounds i).1, (twoCenterHeight_bounds j).2]
  | right i =>
    induction j using Fin.addCases with
    | left j => have := j.isLt; simp only [Fin.lt_def, Fin.val_natAdd, Fin.val_castAdd] at hij; omega
    | right j =>
      simp only [twoCenterBoundaryTime, Fin.addCases_right]
      have hi : i < j := by simp only [Fin.lt_def, Fin.val_natAdd] at hij ⊢; omega
      linarith [twoCenterHeight_strictAnti hi]

theorem twoCenterBoundaryTime_bounds (i : Fin (k+k)) :
    0 < twoCenterBoundaryTime i ∧ twoCenterBoundaryTime i < 4 := by
  induction i using Fin.addCases <;> simp only [twoCenterBoundaryTime, Fin.addCases_left,
    Fin.addCases_right] <;> constructor <;>
    linarith [(twoCenterHeight_bounds ‹Fin k›).1, (twoCenterHeight_bounds ‹Fin k›).2]

/-- The full marked external enumeration is exactly h₁ᴸ,…,hₖᴸ,h₁ᴿ,…,hₖᴿ. -/
theorem twoCenterBoundary_order (i : Fin (k+k)) :
    twoCenterVertexPoint (twoCenterOrderedBoundary i) =
      twoCenterOuterSquare (twoCenterBoundaryTime i) := by
  induction i using Fin.addCases with
  | left i =>
    have hh : (2-twoCenterHeight i)/4 ≤ 1 := by linarith [(twoCenterHeight_bounds i).1]
    simp only [twoCenterOrderedBoundary, twoCenterBoundaryTime, Fin.addCases_left]
    simp [twoCenterOuterSquare, twoCenterVertexPoint, twoCenterSquare, hh, Complex.ext_iff]
    ring
  | right i =>
    have h₁ : ¬ 2+(2-twoCenterHeight i)/4 ≤ 1 := by linarith [(twoCenterHeight_bounds i).2]
    have h₂ : ¬ 2+(2-twoCenterHeight i)/4 ≤ 2 := by linarith [(twoCenterHeight_bounds i).2]
    have h₃ : 2+(2-twoCenterHeight i)/4 ≤ 3 := by linarith [(twoCenterHeight_bounds i).1]
    simp only [twoCenterOrderedBoundary, twoCenterBoundaryTime, Fin.addCases_right]
    simp [twoCenterOuterSquare, twoCenterVertexPoint, twoCenterSquare, h₁, h₂, h₃, Complex.ext_iff]
    ring

/-- All nonboundary vertices lie strictly inside the enclosing square. -/
theorem twoCenter_nonboundary_inside (v : Fin 2 ⊕ Fin 2) :
    |(twoCenterVertexPoint (k := k) (Sum.elim Sum.inl (fun x => Sum.inr (Sum.inl x)) v)).re| < 2 ∧
    |(twoCenterVertexPoint (k := k) (Sum.elim Sum.inl (fun x => Sum.inr (Sum.inl x)) v)).im| < 2 := by
  rcases v with c | x <;> (first | fin_cases c | fin_cases x) <;>
    norm_num [twoCenterVertexPoint]

/-- Every edge interior stays strictly inside the enclosing square, so its
marked hard leaves are genuinely external to the four-cycle. -/
theorem twoCenter_edges_inside (e : TwoCenterDrawingEdge k) (t : unitInterval)
    (ht₀ : 0 < t) (ht₁ : t < 1) :
    |(twoCenterEdgeArc e t).re| < 2 ∧ |(twoCenterEdgeArc e t).im| < 2 := by
  have ht0 : (0 : ℝ) < t := ht₀
  have ht1 : (t : ℝ) < 1 := ht₁
  rcases e with ⟨c,l | i⟩
  · fin_cases c <;> fin_cases l <;> simp [twoCenterEdgeArc, twoCenterRay, abs_lt] <;>
      constructor <;> constructor <;> linarith
  · have hb := twoCenterHeight_bounds i
    have ha : |(t : ℝ) * twoCenterHeight i| < 2 := by
      rw [abs_lt]; constructor <;> nlinarith [hb.1, hb.2]
    have hprod : |(t : ℝ)| * |twoCenterHeight i| < 2 := by simpa [abs_mul] using ha
    fin_cases c <;> simp [twoCenterEdgeArc, twoCenterRay, hprod] <;>
      rw [abs_lt] <;> constructor <;> linarith


/-- The four oriented corner cross-products are positive. In particular the
local square and its half-turn have the same positive cyclic orientation. -/
theorem twoCenterSquare_positive_orientation (i : Fin 4) :
    (twoCenterSquare i.val).re * (twoCenterSquare ((i+1 : Fin 4).val)).im -
      (twoCenterSquare i.val).im * (twoCenterSquare ((i+1 : Fin 4).val)).re = 2 := by
  fin_cases i <;> norm_num [twoCenterSquare]

theorem twoCenterOuterSquare_continuous : Continuous twoCenterOuterSquare :=
  continuous_const.mul twoCenterSquare_continuous

theorem twoCenterOuterSquare_simple : Set.InjOn twoCenterOuterSquare (Set.Ico 0 4) := by
  intro r hr s hs h
  apply twoCenterSquare_simple hr hs
  exact mul_left_cancel₀ (by norm_num : -(2 : ℂ) ≠ 0) h

@[simp] theorem twoCenterOuterSquare_closed : twoCenterOuterSquare 0 = twoCenterOuterSquare 4 := by
  unfold twoCenterOuterSquare
  rw [twoCenterSquare_closed]

/-- Undirected adjacency of the actual drawing graph, including hard leaves. -/
def twoCenterGraphAdjacent (v w : TwoCenterDrawingVertex k) : Prop :=
  ∃ e : TwoCenterDrawingEdge k,
    ((twoCenterDrawingGraph k).left e = v ∧ (twoCenterDrawingGraph k).right e = w) ∨
    ((twoCenterDrawingGraph k).right e = v ∧ (twoCenterDrawingGraph k).left e = w)

/-- The drawing graph is connected: every vertex has an explicit finite path
from the left center. -/
theorem twoCenterDrawing_reachable (v : TwoCenterDrawingVertex k) :
    Relation.ReflTransGen twoCenterGraphAdjacent (Sum.inl 0) v := by
  have hupper : Relation.ReflTransGen (twoCenterGraphAdjacent (k := k))
      (Sum.inl 0) (Sum.inr (Sum.inl 0)) :=
    .single ⟨(0,Sum.inl 1), Or.inl (by simp [twoCenterDrawingGraph])⟩
  have hlower : Relation.ReflTransGen (twoCenterGraphAdjacent (k := k))
      (Sum.inl 0) (Sum.inr (Sum.inl 1)) :=
    .single ⟨(0,Sum.inl 0), Or.inl (by simp [twoCenterDrawingGraph])⟩
  have hright : Relation.ReflTransGen (twoCenterGraphAdjacent (k := k))
      (Sum.inl 0) (Sum.inl 1) :=
    hupper.trans (.single ⟨(1,Sum.inl 0), Or.inr (by simp [twoCenterDrawingGraph])⟩)
  rcases v with c | x | ⟨c,i⟩
  · fin_cases c
    · exact .refl
    · exact hright
  · fin_cases x
    · exact hupper
    · exact hlower
  · have hc : Relation.ReflTransGen (twoCenterGraphAdjacent (k := k))
        (Sum.inl 0) (Sum.inl c) := by
      fin_cases c
      · exact .refl
      · exact hright
    exact hc.trans (.single ⟨(c,Sum.inr i), Or.inl (by simp [twoCenterDrawingGraph])⟩)

/-- A checkable ordered planar witness: simple continuous edge arcs, local
port order at each center, and a marked simple enclosing boundary curve. -/
structure TwoCenterPlanarCertificate (k : ℕ) where
  drawing : PlaneArcDrawing (twoCenterDrawingGraph k)
  local_order : ∀ (c : Fin 2) (i : Fin (2+k)) (t : unitInterval),
    drawing.edge (c,twoCenterOrderedPort i) t = drawing.vertex (Sum.inl c) +
      (t : ℝ) • (if c = 0 then twoCenterSquare (twoCenterLocalTime i)
        else -twoCenterSquare (twoCenterLocalTime i))
  local_strictMono : StrictMono (twoCenterLocalTime (k := k))
  local_range : ∀ i : Fin (2+k), 0 ≤ twoCenterLocalTime i ∧ twoCenterLocalTime i < 4
  boundary_order : ∀ i, drawing.vertex (twoCenterOrderedBoundary i) =
    twoCenterOuterSquare (twoCenterBoundaryTime i)
  boundary_strictMono : StrictMono (twoCenterBoundaryTime (k := k))
  boundary_range : ∀ i : Fin (k+k), 0 < twoCenterBoundaryTime i ∧ twoCenterBoundaryTime i < 4
  internal_interior : ∀ v : Fin 2 ⊕ Fin 2,
    |(drawing.vertex (Sum.elim Sum.inl (fun x => Sum.inr (Sum.inl x)) v)).re| < 2 ∧
    |(drawing.vertex (Sum.elim Sum.inl (fun x => Sum.inr (Sum.inl x)) v)).im| < 2
  edge_interior : ∀ e t, 0 < t → t < 1 →
    |(drawing.edge e t).re| < 2 ∧ |(drawing.edge e t).im| < 2

/-- The prescribed rotations and external order are realized, rather than
postulated as planarity hypotheses. -/
def twoCenterPlanarCertificate (k : ℕ) : TwoCenterPlanarCertificate k where
  drawing := twoCenterPlaneDrawing k
  local_order := twoCenterEdgeArc_local_order
  local_strictMono := twoCenterLocalTime_strictMono
  local_range := twoCenterLocalTime_bounds
  boundary_order := twoCenterBoundary_order
  boundary_strictMono := twoCenterBoundaryTime_strictMono
  boundary_range := twoCenterBoundaryTime_bounds
  internal_interior := twoCenter_nonboundary_inside
  edge_interior := twoCenter_edges_inside

end
end MatchgateWidth
