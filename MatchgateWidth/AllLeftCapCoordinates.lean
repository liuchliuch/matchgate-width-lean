import MatchgateWidth.AllLeftTransverseScaffold

/-! # Exact occurrence-to-corridor cap coordinates

The local block endpoint formulas and the global physical ribbon endpoint
formulas agree on the nose. Internal left reversal, unchanged right position,
and unchanged external position are all checked separately.
-/
namespace MatchgateWidth
noncomputable section
namespace AllLeftGadget.TransverseScaffold
variable {S : LabelledShape} {a b c n t : ℕ} {I : AllLeftGadget S a b c n}
    (K : I.TransverseScaffold)

/-- The outgoing section at each original left port. -/
def leftTransverse (v : Fin a) (i : Fin (S.leftArity (I.leftLabel v))) : ℂ :=
  (K.route (I.leftIncidence ⟨v,i⟩)).transverse 0

/-- The incoming section at each original right port. -/
def rightTransverse (v : Fin b) (i : Fin (S.rightArity (I.rightLabel v))) : ℂ :=
  (K.route (Sum.inl (I.rightIncidence ⟨v,i⟩))).transverse
    (Fin.last (K.indexed (Sum.inl (I.rightIncidence ⟨v,i⟩))).edgeCount)

/-- Increasing local left positions before the occurrence-specific semantic twist. -/
def leftCoefficients (_K : I.TransverseScaffold) (v : Fin a) (_i : Fin (S.leftArity (I.leftLabel v))) (k : Fin t) : ℝ :=
  TransversePolygonalRoute.laneOffset 1 t k

/-- Right local positions use decreasing geometric lanes. -/
def rightCoefficients (_K : I.TransverseScaffold) (v : Fin b) (_i : Fin (S.rightArity (I.rightLabel v))) (k : Fin t) : ℝ :=
  TransversePolygonalRoute.laneOffset 1 t k.rev

theorem mul_laneOffset_one (ε : ℝ) (k : Fin t) :
    ε * TransversePolygonalRoute.laneOffset 1 t k =
      TransversePolygonalRoute.laneOffset ε t k := by
  simp [TransversePolygonalRoute.laneOffset]

/-- Actual absolute cap point indexed by a local left scalar port. -/
def leftCap (ε : ℝ) (q : Σ v : Fin a, Fin (S.leftArity (I.leftLabel v)*t)) : ℂ :=
  let w := I.leftWireEquiv.symm q
  (K.route w.1).laneVertex (physicalLaneOffset ε w.1 w.2) ⟨0,Nat.zero_lt_succ _⟩

/-- Actual absolute cap point indexed by a local right scalar port. -/
def rightCap (ε : ℝ) (q : Σ v : Fin b, Fin (S.rightArity (I.rightLabel v)*t)) : ℂ :=
  let w := I.rightWireEquiv.symm q
  (K.route (Sum.inl w.1)).laneVertex (physicalLaneOffset ε (Sum.inl w.1 : Fin c ⊕ Fin n) w.2)
    (Fin.last (K.indexed (Sum.inl w.1)).edgeCount)

theorem leftCap_internal (ε : ℝ) (e : Fin c) (k : Fin t) :
    K.leftCap ε (I.internalLeftWire (finProdFinEquiv (e,k))) =
      (K.route (Sum.inl e)).laneVertex (physicalLaneOffset ε (Sum.inl e : Fin c ⊕ Fin n) k) 0 := by
  have he : I.leftWireEquiv.symm (I.internalLeftWire (finProdFinEquiv (e,k))) =
      (Sum.inl e,k) := by simp [internalLeftWire]
  exact congrArg (fun w : (Fin c ⊕ Fin n) × Fin t =>
    (K.route w.1).laneVertex (physicalLaneOffset ε w.1 w.2) ⟨0,Nat.zero_lt_succ _⟩) he

theorem rightCap_internal (ε : ℝ) (e : Fin c) (k : Fin t) :
    K.rightCap ε (I.internalRightWire (finProdFinEquiv (e,k))) =
      (K.route (Sum.inl e)).laneVertex (physicalLaneOffset ε (Sum.inl e : Fin c ⊕ Fin n) k)
        (Fin.last (K.indexed (Sum.inl e)).edgeCount) := by
  have he : I.rightWireEquiv.symm (I.internalRightWire (finProdFinEquiv (e,k))) =
      (e,k) := by simp [internalRightWire]
  exact congrArg (fun w : Fin c × Fin t =>
    (K.route (Sum.inl w.1)).laneVertex (physicalLaneOffset ε (Sum.inl w.1 : Fin c ⊕ Fin n) w.2)
      (Fin.last (K.indexed (Sum.inl w.1)).edgeCount)) he

theorem leftCap_boundary (ε : ℝ) (p : Fin n) (k : Fin t) :
    K.leftCap ε (I.boundaryLeftWire (finProdFinEquiv (p,k))) =
      (K.route (Sum.inr p)).laneVertex (physicalLaneOffset ε (Sum.inr p : Fin c ⊕ Fin n) k) 0 := by
  have he : I.leftWireEquiv.symm (I.boundaryLeftWire (finProdFinEquiv (p,k))) =
      (Sum.inr p,k) := by simp [boundaryLeftWire]
  exact congrArg (fun w : (Fin c ⊕ Fin n) × Fin t =>
    (K.route w.1).laneVertex (physicalLaneOffset ε w.1 w.2) ⟨0,Nat.zero_lt_succ _⟩) he

/-- The bank's actual port-major left endpoint equals the physical cap. -/
theorem leftCap_local_formula (ε : ℝ) (v : Fin a)
    (i : Fin (S.leftArity (I.leftLabel v))) (k : Fin t) :
    K.leftCap ε ⟨v,finProdFinEquiv (i,k)⟩ =
      K.ordered.primitiveCenter (Sum.inl v) +
        (K.ordered.leftCutVector K.indexed K.cutRadius v i +
          ((ε*K.leftCoefficients v i k:ℝ):ℂ)*K.leftTransverse v i) := by
  have he := congrArg (fun w : (Fin c ⊕ Fin n) × Fin t =>
    (K.route w.1).laneVertex (physicalLaneOffset ε w.1 w.2) ⟨0,Nat.zero_lt_succ _⟩)
    (I.leftWireEquiv_symm_local v i k)
  change K.leftCap ε ⟨v,finProdFinEquiv (i,k)⟩ = _ at he
  rw [he]
  change (K.route (I.leftIncidence ⟨v,i⟩)).laneVertex
    (TransversePolygonalRoute.laneOffset ε t
      (leftWirePosition (I.leftIncidence ⟨v,i⟩) (leftWirePosition (I.leftIncidence ⟨v,i⟩) k))) 0 = _
  rw [leftWirePosition_twice]
  simp only [TransversePolygonalRoute.laneVertex,ribbonSection,Complex.real_smul,
    K.route_source,leftCoefficients,mul_laneOffset_one,OrderedPlanar.leftCutVector,leftTransverse]
  ring

/-- The bank's actual port-major right endpoint equals the physical cap. -/
theorem rightCap_local_formula (ε : ℝ) (v : Fin b)
    (i : Fin (S.rightArity (I.rightLabel v))) (k : Fin t) :
    K.rightCap ε ⟨v,finProdFinEquiv (i,k)⟩ =
      K.ordered.primitiveCenter (Sum.inr v) +
        (K.ordered.rightCutVector K.indexed K.cutRadius v i +
          ((ε*K.rightCoefficients v i k:ℝ):ℂ)*K.rightTransverse v i) := by
  unfold rightCap
  rw [I.rightWireEquiv_symm_local]
  simp only [physicalLaneOffset,geometricLane,leftWirePosition,Sum.elim_inl,
    TransversePolygonalRoute.laneVertex,ribbonSection,Complex.real_smul,
    K.route_target,rightCoefficients,mul_laneOffset_one,OrderedPlanar.rightCutVector,rightTransverse]
  ring

/-- Exact left connector-bank endpoint identity for every flattened port. -/
theorem leftCap_eq_blockEndpoint (ε : ℝ) (v : Fin a)
    (A : OrderedRayAngles (K.ordered.leftCutVector K.indexed K.cutRadius v))
    (q : Fin (S.leftArity (I.leftLabel v)*t)) :
    K.leftCap ε ⟨v,q⟩ = K.ordered.primitiveCenter (Sum.inl v) +
      A.blockEndpoint (K.leftTransverse v) (K.leftCoefficients v) ε q := by
  obtain ⟨⟨i,k⟩,rfl⟩ := finProdFinEquiv.surjective q
  simpa only [OrderedRayAngles.blockEndpoint,Equiv.symm_apply_apply] using K.leftCap_local_formula ε v i k

/-- Exact right connector-bank endpoint identity for every flattened port. -/
theorem rightCap_eq_blockEndpoint (ε : ℝ) (v : Fin b)
    (A : OrderedRayAngles (K.ordered.rightCutVector K.indexed K.cutRadius v))
    (q : Fin (S.rightArity (I.rightLabel v)*t)) :
    K.rightCap ε ⟨v,q⟩ = K.ordered.primitiveCenter (Sum.inr v) +
      A.blockEndpoint (K.rightTransverse v) (K.rightCoefficients v) ε q := by
  obtain ⟨⟨i,k⟩,rfl⟩ := finProdFinEquiv.surjective q
  simpa only [OrderedRayAngles.blockEndpoint,Equiv.symm_apply_apply] using K.rightCap_local_formula ε v i k

end AllLeftGadget.TransverseScaffold
end
end MatchgateWidth
