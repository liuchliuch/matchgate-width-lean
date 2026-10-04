import MatchgateWidth.AllLeftWirePorts
import MatchgateWidth.PolygonalRibbonPaths
import MatchgateWidth.TransversePortAngles

/-! # Source wire indices and actual geometric ribbon lanes

Source edges are oriented from their left occurrence to a right occurrence or
an exterior terminal. Internal semantic wire `k` uses geometric lane `k.rev`;
external semantic wire `k` uses lane `k`. These equations are proved against the
literal scalar endpoint maps of the substituted matching graph.
-/
namespace MatchgateWidth
noncomputable section
namespace AllLeftGadget
variable {S : LabelledShape} {a b c n t : ℕ} (I : AllLeftGadget S a b c n)

/-- Index in the increasing geometric lane family, as distinct from the
semantic bit position at the right occurrence or external boundary. -/
def geometricLane (e : Fin c ⊕ Fin n) (k : Fin t) : Fin t :=
  leftWirePosition e k

@[simp] theorem geometricLane_internal (e : Fin c) (k : Fin t) :
    geometricLane (Sum.inl e : Fin c ⊕ Fin n) k = k.rev := rfl

@[simp] theorem geometricLane_boundary (p : Fin n) (k : Fin t) :
    geometricLane (Sum.inr p : Fin c ⊕ Fin n) k = k := rfl

@[simp] theorem geometricLane_twice (e : Fin c ⊕ Fin n) (k : Fin t) :
    geometricLane e (geometricLane e k) = k := leftWirePosition_twice e k

theorem geometricLane_injective (e : Fin c ⊕ Fin n) :
    Function.Injective (geometricLane (t := t) e) := by
  intro k l h
  simpa using congrArg (geometricLane e) h

/-- Every left scalar port, including exposed ports, has its unchanged local
position in the increasing geometric family. The semantic internal reversal
cancels the physical lane reversal exactly once. -/
theorem geometricLane_left_local (v : Fin a)
    (i : Fin (S.leftArity (I.leftLabel v))) (k : Fin t) :
    geometricLane (I.leftWireEquiv.symm ⟨v,finProdFinEquiv (i,k)⟩).1
      (I.leftWireEquiv.symm ⟨v,finProdFinEquiv (i,k)⟩).2 = k := by
  rw [I.leftWireEquiv_symm_local]
  exact leftWirePosition_twice _ _

/-- Explicit endpoint equation for an internal physical corridor. -/
theorem internalLeftWire_eq_geometricLane (e : Fin c) (k : Fin t) :
    I.internalLeftWire (finProdFinEquiv (e,k)) =
      ⟨(I.leftIncidence.symm (Sum.inl e)).1,
        finProdFinEquiv ((I.leftIncidence.symm (Sum.inl e)).2,
          geometricLane (Sum.inl e : Fin c ⊕ Fin n) k)⟩ := by
  simp [internalLeftWire,leftWireEquiv,leftWireTwist,geometricLane]

/-- At the right end the semantic position is unchanged, even though its
geometric lane is decreasing in the outward local orientation. -/
theorem internalRightWire_eq_local_position (e : Fin c) (k : Fin t) :
    I.internalRightWire (finProdFinEquiv (e,k)) =
      ⟨(I.rightIncidence.symm e).1,
        finProdFinEquiv ((I.rightIncidence.symm e).2,k)⟩ := by
  simp [internalRightWire,rightWireEquiv]

/-- The external boundary block uses increasing geometric and local indices. -/
theorem boundaryLeftWire_eq_geometricLane (p : Fin n) (k : Fin t) :
    I.boundaryLeftWire (finProdFinEquiv (p,k)) =
      ⟨(I.leftIncidence.symm (Sum.inr p)).1,
        finProdFinEquiv ((I.leftIncidence.symm (Sum.inr p)).2,k)⟩ := by
  simp [boundaryLeftWire,leftWireEquiv,leftWireTwist,leftWirePosition]

/-- One uniform-width family of actual physical offsets, in semantic indices. -/
def physicalLaneOffset (ε : ℝ) (e : Fin c ⊕ Fin n) (k : Fin t) : ℝ :=
  TransversePolygonalRoute.laneOffset ε t (geometricLane e k)

theorem physicalLaneOffset_injective {ε : ℝ} (hε : 0 < ε) (e : Fin c ⊕ Fin n) :
    Function.Injective (physicalLaneOffset (t := t) ε e) :=
  (TransversePolygonalRoute.laneOffset_strictMono hε t).injective.comp
    (geometricLane_injective e)

theorem physicalLaneOffset_bounds {ε : ℝ} (hε : 0 < ε) (e : Fin c ⊕ Fin n) (k : Fin t) :
    0 < physicalLaneOffset ε e k ∧ |physicalLaneOffset ε e k| < ε :=
  TransversePolygonalRoute.laneOffset_bounds hε _

theorem physicalLaneOffset_internal_strictAnti {ε : ℝ} (hε : 0 < ε) (e : Fin c) :
    StrictAnti (physicalLaneOffset (t := t) ε (Sum.inl e : Fin c ⊕ Fin n)) := by
  intro k l hkl
  apply TransversePolygonalRoute.laneOffset_strictMono hε t
  change l.rev < k.rev
  exact Fin.rev_lt_rev.mpr hkl

theorem physicalLaneOffset_boundary_strictMono {ε : ℝ} (hε : 0 < ε) (p : Fin n) :
    StrictMono (physicalLaneOffset (t := t) ε (Sum.inr p : Fin c ⊕ Fin n)) :=
  TransversePolygonalRoute.laneOffset_strictMono hε t

/-- Actual local left offsets are increasing in their own original port order. -/
theorem physicalLaneOffset_left_local (ε : ℝ) (v : Fin a)
    (i : Fin (S.leftArity (I.leftLabel v))) (k : Fin t) :
    physicalLaneOffset ε (I.leftWireEquiv.symm ⟨v,finProdFinEquiv (i,k)⟩).1
      (I.leftWireEquiv.symm ⟨v,finProdFinEquiv (i,k)⟩).2 =
        TransversePolygonalRoute.laneOffset ε t k := by
  unfold physicalLaneOffset
  rw [I.geometricLane_left_local]

/-- Reindexing the genuinely constructed geometric paths gives the physical
corridor family with exactly the source endpoint convention. Simplicity and
full path images are retained; distinct semantic positions remain disjoint. -/
theorem exists_physical_lane_paths {m : ℕ} (R : TransversePolygonalRoute m)
    (hm : 0 < m) {ε : ℝ} (hε : 0 < ε) (hwidth : R.Width ε)
    (e : Fin c ⊕ Fin n) :
    ∃ q : (k : Fin t) → Path
      (R.laneVertex (physicalLaneOffset ε e k) 0)
      (R.laneVertex (physicalLaneOffset ε e k) (Fin.last m)),
      (∀ k, Function.Injective (q k) ∧ IsPolygonalPath (q k) ∧
        Set.range (q k) = R.laneSupport (physicalLaneOffset ε e k)) ∧
      Pairwise (fun k l => Disjoint (Set.range (q k)) (Set.range (q l))) := by
  classical
  have hex (k : Fin t) := R.exists_lane_path hm hwidth
    (physicalLaneOffset_bounds hε e k).2
  choose q hq using hex
  refine ⟨q,hq,?_⟩
  intro k l hkl
  rw [(hq k).2.2,(hq l).2.2]
  exact R.lanes_disjoint hwidth (physicalLaneOffset_bounds hε e k).2
    (physicalLaneOffset_bounds hε e l).2
    (fun he => hkl (physicalLaneOffset_injective hε e he))

end AllLeftGadget
end
end MatchgateWidth
