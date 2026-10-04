import MatchgateWidth.PolygonalPathRealization
import MatchgateWidth.DisjointDiskBridgeAssembly

/-! # Actual assembly of local connectors and middle ribbon wires

The three independently constructed geometric stages are concatenated into
simple disjoint wire paths. Stage-wise carrier separation and endpoint-only
meetings prove all bridge-routing obligations. These hypotheses concern the
local constructions, never a desired graph signature or output MGI.
-/
namespace MatchgateWidth
noncomputable section

/-- Left/outgoing connector, middle ribbon, and right/outgoing connector.
The last connector is traversed backwards by the assembled wire. -/
structure ThreePieceRouting {B : Type*} (x a b y : B → ℂ) where
  left : ∀ i, Path (x i) (a i)
  middle : ∀ i, Path (a i) (b i)
  right : ∀ i, Path (y i) (b i)
  left_simple : ∀ i, Function.Injective (left i)
  middle_simple : ∀ i, Function.Injective (middle i)
  right_simple : ∀ i, Function.Injective (right i)
  left_middle_join : ∀ i, Set.range (left i) ∩ Set.range (middle i) ⊆ {a i}
  middle_right_join : ∀ i, Set.range (middle i) ∩ Set.range (right i) ⊆ {b i}
  left_disjoint : Pairwise (fun i j => Disjoint (Set.range (left i)) (Set.range (left j)))
  middle_disjoint : Pairwise (fun i j => Disjoint (Set.range (middle i)) (Set.range (middle j)))
  right_disjoint : Pairwise (fun i j => Disjoint (Set.range (right i)) (Set.range (right j)))
  left_middle_off : ∀ i j, i ≠ j → Disjoint (Set.range (left i)) (Set.range (middle j))
  left_right : ∀ i j, Disjoint (Set.range (left i)) (Set.range (right j))
  middle_right_off : ∀ i j, i ≠ j → Disjoint (Set.range (middle i)) (Set.range (right j))

namespace ThreePieceRouting
variable {B : Type*} {x a b y : B → ℂ} (T : ThreePieceRouting x a b y)

/-- Actual composed path, with exactly the two required matching-graph endpoints. -/
def wirePath (i : B) : Path (x i) (y i) :=
  (T.left i).trans ((T.middle i).trans (T.right i).symm)

theorem wirePath_range (i : B) : Set.range (T.wirePath i) =
    Set.range (T.left i) ∪ (Set.range (T.middle i) ∪ Set.range (T.right i)) := by
  simp only [wirePath,Path.trans_range,Path.symm_range]

/-- Endpoint-only local joins produce a globally simple three-piece wire. -/
theorem wirePath_injective (i : B) : Function.Injective (T.wirePath i) := by
  have hr : Function.Injective (T.right i).symm :=
    (T.right_simple i).comp unitInterval.symm_bijective.injective
  have hm : Function.Injective ((T.middle i).trans (T.right i).symm) := by
    apply Path.injective_trans_of_inter (T.middle_simple i) hr
    simpa only [Path.symm_range] using T.middle_right_join i
  apply Path.injective_trans_of_inter (T.left_simple i) hm
  intro z hz
  rw [Path.trans_range,Path.symm_range] at hz
  rcases hz.2 with hm | hr
  · exact T.left_middle_join i ⟨hz.1,hm⟩
  · exact (Set.disjoint_left.mp (T.left_right i i) hz.1 hr).elim

/-- Stage separation prevents crossings between any two complete assembled wires. -/
theorem wirePaths_disjoint : Pairwise (fun i j =>
    Disjoint (Set.range (T.wirePath i)) (Set.range (T.wirePath j))) := by
  intro i j hij
  have hLL := T.left_disjoint hij
  have hMM := T.middle_disjoint hij
  have hRR := T.right_disjoint hij
  have hLM := T.left_middle_off i j hij
  have hML := (T.left_middle_off j i hij.symm).symm
  have hLR := T.left_right i j
  have hRL := (T.left_right j i).symm
  have hMR := T.middle_right_off i j hij
  have hRM := (T.middle_right_off j i hij.symm).symm
  simp only [T.wirePath_range,Set.disjoint_union_left,Set.disjoint_union_right]
  tauto

/-- The local stage carrier facts supplied by round insertion disks, annular
connectors, and obstacle-avoiding middle ribbon corridors. -/
structure CarrierAvoidance (L R : Set ℂ) : Prop where
  left_meets_left : ∀ i, Set.range (T.left i) ∩ L ⊆ {x i}
  left_avoids_right : ∀ i, Disjoint (Set.range (T.left i)) R
  middle_avoids_left : ∀ i, Disjoint (Set.range (T.middle i)) L
  middle_avoids_right : ∀ i, Disjoint (Set.range (T.middle i)) R
  right_avoids_left : ∀ i, Disjoint (Set.range (T.right i)) L
  right_meets_right : ∀ i, Set.range (T.right i) ∩ R ⊆ {y i}

theorem wirePath_meets_left {L R : Set ℂ} (C : T.CarrierAvoidance L R)
    (i : B) : Set.range (T.wirePath i) ∩ L ⊆ {x i} := by
  intro z hz
  rw [T.wirePath_range] at hz
  rcases hz.1 with hl | hm | hr
  · exact C.left_meets_left i ⟨hl,hz.2⟩
  · exact (Set.disjoint_left.mp (C.middle_avoids_left i) hm hz.2).elim
  · exact (Set.disjoint_left.mp (C.right_avoids_left i) hr hz.2).elim

theorem wirePath_meets_right {L R : Set ℂ} (C : T.CarrierAvoidance L R)
    (i : B) : Set.range (T.wirePath i) ∩ R ⊆ {y i} := by
  intro z hz
  rw [T.wirePath_range] at hz
  rcases hz.1 with hl | hm | hr
  · exact (Set.disjoint_left.mp (C.left_avoids_right i) hl hz.2).elim
  · exact (Set.disjoint_left.mp (C.middle_avoids_right i) hm hz.2).elim
  · exact C.right_meets_right i ⟨hr,hz.2⟩

/-- Construct the actual bridge-routing witness used by `PlaneDrawing.bridge`
from the local three-stage geometry. No whole-bridge drawing is assumed. -/
def toBridgeRouting {V W E F : Type*}
    {G : WeightedGraph V E ℂ} {H : WeightedGraph W F ℂ}
    (P : PlaneDrawing G) (Q : PlaneDrawing H) (C : PlaneDrawing.DisjointCarriers P Q)
    (extL : B → V) (extR : B → W)
    {a b : B → ℂ}
    (T : ThreePieceRouting (fun i => P.vertex (extL i)) a b (fun i => Q.vertex (extR i)))
    (hC : T.CarrierAvoidance C.left C.right) :
    PlaneDrawing.BridgeRouting P Q C extL extR where
  arc := T.wirePath
  simple := T.wirePath_injective
  outside_left := by
    intro i t ht0 _ ht
    have he : T.wirePath i t = P.vertex (extL i) :=
      T.wirePath_meets_left hC i ⟨⟨t,rfl⟩,ht⟩
    have hz : t = 0 := T.wirePath_injective i (he.trans (T.wirePath i).source.symm)
    exact (ne_of_gt ht0) hz
  outside_right := by
    intro i t _ ht1 ht
    have he : T.wirePath i t = Q.vertex (extR i) :=
      T.wirePath_meets_right hC i ⟨⟨t,rfl⟩,ht⟩
    have hz : t = 1 := T.wirePath_injective i (he.trans (T.wirePath i).target.symm)
    exact (ne_of_lt ht1) hz
  disjoint_interiors := by
    intro i j hij t u _ _ _ _ he
    exact Set.disjoint_left.mp (T.wirePaths_disjoint hij) ⟨t,rfl⟩ ⟨u,he.symm⟩

end ThreePieceRouting
end
end MatchgateWidth
