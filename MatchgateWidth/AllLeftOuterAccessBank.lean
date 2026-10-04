import MatchgateWidth.AllLeftCapCoordinates
import MatchgateWidth.AllLeftScaffoldEndpointAreas

/-! # Derived global ordered radial access for every exterior scalar block

The frame is exactly one and the marked source boundary angle list is used
verbatim. For one common sufficiently small width, every true shifted boundary
cap has an actual simple radial path to the common circle of radius two.
-/
namespace MatchgateWidth
noncomputable section
open Filter Topology
namespace AllLeftGadget.TransverseScaffold
variable {S : LabelledShape} {a b c n t : ℕ} {I : AllLeftGadget S a b c n}
    (K : I.TransverseScaffold)

theorem cutRadius_lt_one : K.cutRadius < 1 := by
  dsimp only [cutRadius]
  linarith [K.collars.small]

/-- The actual global frame and original angle list of the unperturbed cuts. -/
def boundaryAngles : OrderedRayAngles (fun p : Fin n =>
    ((1-K.cutRadius:ℝ):ℂ)*boundaryPoint (K.ordered.drawing.angle p)) :=
  globalOrderedRayAngles K.ordered.drawing.angle (fun _ => 1-K.cutRadius)
    K.ordered.drawing.angle_strictMono K.ordered.drawing.angle_pos
    K.ordered.drawing.angle_lt_one (fun _ => sub_pos.mpr K.cutRadius_lt_one)

def boundaryTransverse (p : Fin n) : ℂ :=
  (K.route (Sum.inr p)).transverse (Fin.last (K.indexed (Sum.inr p)).edgeCount)

def boundaryCoefficients (_K : I.TransverseScaffold) (_p : Fin n) (k : Fin t) : ℝ :=
  TransversePolygonalRoute.laneOffset 1 t k

/-- The exact inherited-order endpoint of every physical boundary lane. -/
def boundaryCap (ε : ℝ) (q : Fin (n*t)) : ℂ :=
  let p := (finProdFinEquiv.symm q).1
  let k := (finProdFinEquiv.symm q).2
  (K.route (Sum.inr p)).laneVertex (physicalLaneOffset ε (Sum.inr p : Fin c ⊕ Fin n) k)
    (Fin.last (K.indexed (Sum.inr p)).edgeCount)

theorem boundaryCap_eq_blockEndpoint (ε : ℝ) (q : Fin (n*t)) :
    K.boundaryCap ε q = K.boundaryAngles.blockEndpoint
      K.boundaryTransverse K.boundaryCoefficients ε q := by
  obtain ⟨⟨p,k⟩,rfl⟩ := finProdFinEquiv.surjective q
  simp only [boundaryCap,Equiv.symm_apply_apply,physicalLaneOffset,geometricLane,leftWirePosition,
    Sum.elim_inr,TransversePolygonalRoute.laneVertex,ribbonSection,Complex.real_smul,
    K.boundary_target,OrderedRayAngles.blockEndpoint,boundaryCoefficients,mul_laneOffset_one,
    boundaryTransverse]

theorem boundary_signed_lane_order (p : Fin n) (j l : Fin t) (hjl : j < l) :
    0 < (K.boundaryCoefficients p l-K.boundaryCoefficients p j) *
      orientedArea (((1-K.cutRadius:ℝ):ℂ)*boundaryPoint (K.ordered.drawing.angle p))
        (K.boundaryTransverse p) :=
  mul_pos (sub_pos.mpr (TransversePolygonalRoute.laneOffset_strictMono (by norm_num : (0:ℝ)<1) t hjl))
    (K.boundary_area_positive p)

/-- Concrete outer-tail bank, built from the exact physical cap coordinates. -/
structure OuterAccessBank (ε : ℝ) where
  angle : Fin (n*t) → ℝ
  angle_pos : ∀ q, 0 < angle q
  angle_lt_one : ∀ q, angle q < 1
  angle_strictMono : StrictMono angle
  path : ∀ q, Path (K.boundaryCap ε q) ((2:ℂ)*boundaryPoint (angle q))
  simple : ∀ q, Function.Injective (path q)
  disjoint : Pairwise (fun q s => Disjoint (Set.range (path q)) (Set.range (path s)))
  bound : ∀ q u, ‖path q u‖ ≤ 2
  norm_lower : ∀ q u, ‖K.boundaryCap ε q‖ ≤ ‖path q u‖
  radius : Fin (n*t) → ℝ
  radius_pos : ∀ q, 0 < radius q
  radius_gt_three_quarters : ∀ q, (3:ℝ)/4 < radius q
  radius_lt_two : ∀ q, radius q < 2
  cap_eq : ∀ q, K.boundaryCap ε q = (radius q:ℂ)*boundaryPoint (angle q)
  formula : ∀ q u, path q u =
    ((affineBlend (radius q) 2 u:ℝ):ℂ)*boundaryPoint (angle q)

/-- The global ordered boundary angles and actual radial tails exist for all
sufficiently small positive common widths, with no external-order premise. -/
theorem exists_uniform_outer_access (t : ℕ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε, 0 < ε → ε < ε₀ →
      Nonempty (K.OuterAccessBank (t := t) ε) := by
  have hbase (p : Fin n) :
      ‖((1-K.cutRadius:ℝ):ℂ)*boundaryPoint (K.ordered.drawing.angle p)‖ < 2 := by
    rw [norm_mul,norm_boundaryPoint,mul_one,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos (sub_pos.mpr K.cutRadius_lt_one)]
    linarith [K.cutRadius_pos]
  obtain ⟨ε₀,hε₀,hsmall⟩ := K.boundaryAngles.exists_outer_block_endpoints rfl
    K.boundaryTransverse (K.boundaryCoefficients (t := t)) K.boundary_signed_lane_order 2 hbase
  have hlower : ∀ᶠ ε in 𝓝 (0:ℝ), ∀ q : Fin (n*t),
      (3:ℝ)/4 < ‖K.boundaryAngles.blockEndpoint K.boundaryTransverse K.boundaryCoefficients ε q‖ := by
    rw [Filter.eventually_all]
    intro q
    have hc : ContinuousAt (fun ε : ℝ =>
        ‖K.boundaryAngles.blockEndpoint K.boundaryTransverse K.boundaryCoefficients ε q‖) 0 := by
      unfold OrderedRayAngles.blockEndpoint
      fun_prop
    apply continuousAt_const.eventually_lt hc
    simp only [OrderedRayAngles.blockEndpoint,zero_mul,Complex.ofReal_zero,add_zero]
    rw [norm_mul,norm_boundaryPoint,mul_one,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos (sub_pos.mpr K.cutRadius_lt_one)]
    dsimp only [cutRadius]
    linarith [K.collars.small]
  obtain ⟨η,hη,hηball⟩ := Metric.mem_nhds_iff.mp hlower
  refine ⟨min ε₀ η,lt_min hε₀ hη,?_⟩
  intro ε hε hεlt
  obtain ⟨B,hBrot,hBrad⟩ := hsmall ε hε (hεlt.trans_le (min_le_left _ _))
  have hBlo (q : Fin (n*t)) : (3:ℝ)/4 < B.radius q := by
    rw [← B.norm_point_of_rotation_one hBrot]
    apply hηball
    simpa only [Metric.mem_ball,dist_zero_right,Real.norm_eq_abs,abs_of_pos hε] using
      hεlt.trans_le (min_le_right ε₀ η)
  let path (q : Fin (n*t)) := (B.outerPath hBrot 2 q).cast (K.boundaryCap_eq_blockEndpoint ε q) rfl
  refine ⟨{
    angle := B.angle
    angle_pos := B.angle_pos
    angle_lt_one := B.angle_lt_one
    angle_strictMono := B.angle_strictMono
    path := path
    simple := B.outerPath_injective hBrot hBrad
    disjoint := B.outerPaths_disjoint hBrot (by norm_num)
    bound := fun q u => (B.outerPath_norm_bounds hBrot hBrad q u).2
    norm_lower := ?_
    radius := B.radius
    radius_pos := B.radius_pos
    radius_gt_three_quarters := hBlo
    radius_lt_two := hBrad
    cap_eq := ?_
    formula := fun q u => B.outerPath_apply hBrot 2 q u }⟩
  · intro q u
    change ‖K.boundaryCap ε q‖ ≤ ‖B.outerPath hBrot 2 q u‖
    rw [K.boundaryCap_eq_blockEndpoint,B.norm_point_of_rotation_one hBrot]
    exact (B.outerPath_norm_bounds hBrot hBrad q u).1
  · intro q
    rw [K.boundaryCap_eq_blockEndpoint,B.point_eq,hBrot,one_mul]

end AllLeftGadget.TransverseScaffold
end
end MatchgateWidth
