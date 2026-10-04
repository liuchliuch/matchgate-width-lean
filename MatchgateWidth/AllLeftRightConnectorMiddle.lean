import MatchgateWidth.AllLeftConnectorRaw
import MatchgateWidth.AllLeftConnectorPlacement
import MatchgateWidth.CompactCurvePerturbation

/-! # Derived right local-connector contact with whole middle ribbons

Nonfinal and nonincident pieces are separated at zero width by the actual
source collars, then by compact perturbation. The remaining final segment is
handled by the exact determinant law for the complete radial-tail connector.
-/
namespace MatchgateWidth
noncomputable section
open Set Filter Topology
namespace AllLeftGadget.TransverseScaffold
variable {S : LabelledShape} {a b c n t : ℕ} {I : AllLeftGadget S a b c n}
    (K : I.TransverseScaffold)

/-- A uniform positive separation window for every nonjoining indexed pair.
The connector and middle widths may vary independently within this window. -/
theorem exists_uniform_rightRaw_middle_separation
    (R : I.RightMatchingFamily (t := t)) (hR : R.DiskDrawn) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε η, |ε| < ε₀ → |η| < ε₀ →
      ∀ (v : Fin b) (q : Fin (S.rightArity (I.rightLabel v)*t))
        (e : Fin c ⊕ Fin n) (k : Fin t) (j : Fin (K.indexed e).edgeCount),
      (Sum.inl (I.rightIncidence ⟨v,(finProdFinEquiv.symm q).1⟩) ≠ e ∨
        j.val+1 ≠ (K.indexed e).edgeCount) →
      Disjoint (Set.range (K.rightRaw R hR v q ε)) (Set.range (K.middlePiece e k j η)) := by
  classical
  let J := (Σ v : Fin b, Fin (S.rightArity (I.rightLabel v)*t)) ⊕
    (Σ e : Fin c ⊕ Fin n, Fin t × Fin (K.indexed e).edgeCount)
  let f : J → ℝ → unitInterval → ℂ := Sum.elim
    (fun q ε => K.rightRaw R hR q.1 q.2 ε)
    (fun z ε => K.middlePiece z.1 z.2.1 z.2.2 ε)
  let Rel : J → J → Prop := fun x y => match x,y with
    | Sum.inl q, Sum.inr z =>
      Sum.inl (I.rightIncidence ⟨q.1,(finProdFinEquiv.symm q.2).1⟩) ≠ z.1 ∨
        z.2.2.val+1 ≠ (K.indexed z.1).edgeCount
    | _,_ => False
  have hbase : ∀ j, Continuous (f j 0) := by
    rintro (q | z)
    · exact K.rightRaw_zero_continuous R hR q.1 q.2
    · exact K.middlePiece_continuous _ _ _ _
  have hf : ∀ j u, ContinuousAt (fun z : ℝ × unitInterval => f j z.1 z.2) (0,u) := by
    rintro (q | z) u
    · exact K.rightRaw_continuousAt_zero R hR q.1 q.2 u
    · exact K.middlePiece_continuousAt_zero _ _ _ u
  have hd : ∀ x y, Rel x y → Disjoint (Set.range (f x 0)) (Set.range (f y 0)) := by
    rintro (q | x) (r | y) h <;> try exact h.elim
    exact K.rightRaw_zero_piece_disjoint R hR q.1 q.2 y.1 y.2.1 y.2.2 h
  obtain ⟨ε₀,hε₀,_,hsep⟩ := finite_related_curve_perturbations_disjoint Rel f hbase hf hd
    (fun _ => Set.univ) (fun _ => isOpen_univ) (fun _ => Set.subset_univ _)
  refine ⟨ε₀,hε₀,?_⟩
  intro ε η hε hη v q e k j haway
  exact hsep (Sum.inl ⟨v,q⟩) (Sum.inr ⟨e,k,j⟩) haway ε η hε hη

/-- A standalone uniform tail window for all actual right occurrences. -/
theorem exists_uniform_rightRaw_tails
    (R : I.RightMatchingFamily (t := t)) (hR : R.DiskDrawn) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε, |ε| < ε₀ → ∀ v q,
      RadialTailProperty (K.rightRaw R hR v q ε)
        (K.ordered.primitiveCenter (Sum.inr v))
        (K.rightCap ε ⟨v,q⟩ - K.ordered.primitiveCenter (Sum.inr v)) (K.collars.radius/2) := by
  classical
  have hex (v : Fin b) := (K.rightAngles v).exists_radialTail_radius
    (K.ordered.primitiveCenter (Sum.inr v)) (K.rightTransverse v) (K.rightCoefficients v)
    (R.nativeDrawing hR v).angle _ _
    ((K.rightAngles v).round_connector_parameters K.collars.radius K.collars.positive (K.rightCutVector_norm v)).1
    ((K.rightAngles v).round_connector_parameters K.collars.radius K.collars.positive (K.rightCutVector_norm v)).2.1
    ((K.rightAngles v).round_connector_parameters K.collars.radius K.collars.positive (K.rightCutVector_norm v)).2.2.1
  choose η hη hspec using hex
  obtain ⟨ε₀,hε₀,hmin⟩ := finite_positive_lower_bound η hη
  refine ⟨ε₀,hε₀,?_⟩
  intro ε hε v q
  have h := hspec v ε (hε.trans_le (hmin v)) q
  have hp := (K.rightAngles v).round_connector_parameters K.collars.radius K.collars.positive (K.rightCutVector_norm v)
  rw [hp.2.2.2] at h
  rw [K.rightCap_eq_blockEndpoint ε v (K.rightAngles v) q,add_sub_cancel_left]
  exact h


/-- Exact final-piece contact, including the complete angular head and radial
 tail and all distinct semantic lanes on the same source edge. -/
theorem rightConnector_last_middle_eq_iff
    (R : I.RightMatchingFamily (t := t)) (hR : R.DiskDrawn) {ε : ℝ} (hε : 0 < ε)
    (hW : ∀ e, (K.route e).Width ε) (BR : ∀ v, K.RightBank R hR ε v)
    (htail : ∀ v q, RadialTailProperty (K.rightConnector R hR BR ⟨v,q⟩)
      (K.ordered.primitiveCenter (Sum.inr v))
      (K.rightCap ε ⟨v,q⟩-K.ordered.primitiveCenter (Sum.inr v)) (K.collars.radius/2))
    (v : Fin b) (i : Fin (S.rightArity (I.rightLabel v))) (l k : Fin t)
    (u s : unitInterval) :
    K.rightConnector R hR BR ⟨v,finProdFinEquiv (i,l)⟩ u =
      K.middlePiece (Sum.inl (I.rightIncidence ⟨v,i⟩)) k
        (K.indexed (Sum.inl (I.rightIncidence ⟨v,i⟩))).lastEdge ε s ↔
      u=1 ∧ s=1 ∧ l=k := by
  let e : Fin c ⊕ Fin n := Sum.inl (I.rightIncidence ⟨v,i⟩)
  let j := (K.indexed e).lastEdge
  let center := K.ordered.primitiveCenter (Sum.inr v)
  have hc : K.ordered.drawing.vertex (I.graph.right e) = center := by
    simp [e,center,AllLeftGadget.graph,OrderedPlanar.primitiveCenter]
  have hcapEq : K.rightCap ε ⟨v,finProdFinEquiv (i,l)⟩ =
      ribbonSection ((K.route e).vertex j.succ) ((K.route e).transverse j.succ)
        (physicalLaneOffset ε e l) := by
    unfold rightCap
    rw [I.rightWireEquiv_symm_local]
    simp only [TransversePolygonalRoute.laneVertex,j,IndexedSimplePolygonalRoute.lastEdge_succ,e]
  let C := (K.rightConnector R hR BR ⟨v,finProdFinEquiv (i,l)⟩).cast rfl hcapEq.symm
  have hC : Function.Injective C := K.rightConnector_simple R hR BR _
  have ht : RadialTailProperty C center
      (ribbonSection ((K.route e).vertex j.succ) ((K.route e).transverse j.succ)
        (physicalLaneOffset ε e l)-center) (K.collars.radius/2) := by
    intro τ
    rcases htail v (finProdFinEquiv (i,l)) τ with hh | ⟨β,hβ0,hβ1,hβ⟩
    · exact Or.inl hh
    · exact Or.inr ⟨β,hβ0,hβ1,hβ.trans
        (congrArg (fun z => center+β • (z-center)) hcapEq)⟩
  have hhead : Disjoint (Set.range (K.middlePiece e k j ε))
      (Metric.closedBall center (K.collars.radius/2)) := by
    have hh := K.middlePiece_outside_vertex hε hW e k j (I.graph.right e)
    rw [hc] at hh
    exact hh.mono_right (Metric.closedBall_subset_closedBall (by linarith [K.collars.positive]))
  have hcap : 0 < orientedArea (center-(K.route e).vertex j.succ)
      ((K.route e).transverse j.succ) := by
    have hh := K.target_area_negative e
    rw [← K.route_target e] at hh
    simp only [hc] at hh
    rw [show center-(K.route e).vertex j.succ = -((K.route e).vertex j.succ-center) by abel,
      orientedArea_neg_left]
    simpa only [j,IndexedSimplePolygonalRoute.lastEdge_succ] using neg_pos.mpr hh
  have hwire := (hW e (physicalLaneOffset ε e k) (physicalLaneOffset_bounds hε e k).2 j).2.1
  have hiff := ribbon_radialTail_connector_eq_iff center
    ((K.route e).vertex j.castSucc) ((K.route e).vertex j.succ)
    ((K.route e).transverse j.castSucc) ((K.route e).transverse j.succ)
    _ (physicalLaneOffset ε e k) (physicalLaneOffset ε e l) (K.collars.radius/2)
    C hC ht hhead hcap hwire s u
  change C u = K.middlePiece e k j ε s ↔ _
  change K.middlePiece e k j ε s = C u ↔ _ at hiff
  rw [eq_comm,hiff]
  constructor
  · rintro ⟨hs,hu,hkl⟩
    exact ⟨hu,hs,(physicalLaneOffset_injective hε e hkl).symm⟩
  · rintro ⟨rfl,rfl,rfl⟩
    exact ⟨rfl,rfl,rfl⟩


/-- Any contact of an actual right connector with an entire middle support
identifies its precise semantic wire and its designated terminal cap. -/
theorem exists_uniform_rightConnector_middle_contact
    (R : I.RightMatchingFamily (t := t)) (hR : R.DiskDrawn) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε, 0 < ε → ε < ε₀ →
      (∀ e, (K.route e).Width ε) → ∀ (BR : ∀ v, K.RightBank R hR ε v),
      (∀ v q u, (BR v).path q u = K.rightRaw R hR v q ε u) →
      ∀ (q : Σ v : Fin b, Fin (S.rightArity (I.rightLabel v)*t))
        (e : Fin c ⊕ Fin n) (k : Fin t) (z : ℂ),
      z ∈ Set.range (K.rightConnector R hR BR q) →
      z ∈ (K.route e).laneSupport (physicalLaneOffset ε e k) →
      e = Sum.inl (I.rightWireEquiv.symm q).1 ∧
        k = (I.rightWireEquiv.symm q).2 ∧ z = K.rightCap ε q := by
  obtain ⟨ε₁,hε₁,hsep⟩ := K.exists_uniform_rightRaw_middle_separation R hR
  obtain ⟨ε₂,hε₂,htail⟩ := K.exists_uniform_rightRaw_tails R hR
  refine ⟨min ε₁ ε₂,lt_min hε₁ hε₂,?_⟩
  intro ε hε hsmall hW BR hBR
  have hsmall₁ : |ε| < ε₁ := by
    rw [abs_of_pos hε]
    exact hsmall.trans_le (min_le_left _ _)
  have hsmall₂ : |ε| < ε₂ := by
    rw [abs_of_pos hε]
    exact hsmall.trans_le (min_le_right _ _)
  have hraw (v : Fin b) (q : Fin (S.rightArity (I.rightLabel v)*t)) :
      (K.rightConnector R hR BR ⟨v,q⟩ : unitInterval → ℂ) = K.rightRaw R hR v q ε :=
    funext (hBR v q)
  have htail' : ∀ v q, RadialTailProperty (K.rightConnector R hR BR ⟨v,q⟩)
      (K.ordered.primitiveCenter (Sum.inr v))
      (K.rightCap ε ⟨v,q⟩-K.ordered.primitiveCenter (Sum.inr v)) (K.collars.radius/2) := by
    intro v q
    rw [hraw]
    exact htail ε hsmall₂ v q
  have hsep' (v : Fin b) (q : Fin (S.rightArity (I.rightLabel v)*t))
      (e : Fin c ⊕ Fin n) (k : Fin t) (j : Fin (K.indexed e).edgeCount)
      (haway : Sum.inl (I.rightIncidence ⟨v,(finProdFinEquiv.symm q).1⟩) ≠ e ∨
        j.val+1 ≠ (K.indexed e).edgeCount) :
      Disjoint (Set.range (K.rightConnector R hR BR ⟨v,q⟩))
        (Set.range (K.middlePiece e k j ε)) := by
    rw [hraw]
    exact hsep ε ε hsmall₁ hsmall₁ v q e k j haway
  rintro ⟨v,q⟩ e k z hz hm
  obtain ⟨⟨i,l⟩,rfl⟩ := finProdFinEquiv.surjective q
  rw [I.rightWireEquiv_symm_local]
  obtain ⟨u,hu⟩ := hz
  obtain ⟨j,s,hs⟩ := Set.mem_iUnion.mp hm
  have hpair : K.rightConnector R hR BR ⟨v,finProdFinEquiv (i,l)⟩ u =
      K.middlePiece e k j ε s := hu.trans hs.symm
  by_cases he : e = Sum.inl (I.rightIncidence ⟨v,i⟩)
  · subst e
    by_cases hj : j.val+1 = (K.indexed (Sum.inl (I.rightIncidence ⟨v,i⟩))).edgeCount
    · have hjj : j = (K.indexed (Sum.inl (I.rightIncidence ⟨v,i⟩))).lastEdge := by
        apply Fin.ext
        simp only [IndexedSimplePolygonalRoute.lastEdge_val]
        omega
      subst j
      obtain ⟨hu1,hs1,hlk⟩ :=
        (K.rightConnector_last_middle_eq_iff R hR hε hW BR htail' v i l k u s).mp hpair
      refine ⟨rfl,hlk.symm,?_⟩
      rw [← hu,hu1]
      exact (K.rightConnector R hR BR _).target
    · exact (Set.disjoint_left.mp (hsep' v _ _ k j (Or.inr hj))
        ⟨u,hu⟩ ⟨s,hs⟩).elim
  · have haway : Sum.inl (I.rightIncidence
        ⟨v,(finProdFinEquiv.symm (finProdFinEquiv (i,l))).1⟩) ≠ e := by
      simpa only [Equiv.symm_apply_apply] using Ne.symm he
    exact (Set.disjoint_left.mp (hsep' v _ e k j (Or.inl haway))
      ⟨u,hu⟩ ⟨s,hs⟩).elim

/-- Whole-support endpoint-only intersection and complete off-wire separation
for every right connector, in the exact source incidence and semantic indices. -/
theorem exists_uniform_rightConnector_whole_middle
    (R : I.RightMatchingFamily (t := t)) (hR : R.DiskDrawn) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε, 0 < ε → ε < ε₀ →
      (∀ e, (K.route e).Width ε) → ∀ (BR : ∀ v, K.RightBank R hR ε v),
      (∀ v q u, (BR v).path q u = K.rightRaw R hR v q ε u) →
      (∀ q : Σ v : Fin b, Fin (S.rightArity (I.rightLabel v)*t),
        Set.range (K.rightConnector R hR BR q) ∩
          (K.route (Sum.inl (I.rightWireEquiv.symm q).1)).laneSupport
            (physicalLaneOffset ε (Sum.inl (I.rightWireEquiv.symm q).1 : Fin c ⊕ Fin n)
              (I.rightWireEquiv.symm q).2) ⊆ {K.rightCap ε q}) ∧
      (∀ (q : Σ v : Fin b, Fin (S.rightArity (I.rightLabel v)*t))
        (e : Fin c ⊕ Fin n) (k : Fin t),
        (e,k) ≠ (Sum.inl (I.rightWireEquiv.symm q).1,(I.rightWireEquiv.symm q).2) →
        Disjoint (Set.range (K.rightConnector R hR BR q))
          ((K.route e).laneSupport (physicalLaneOffset ε e k))) := by
  obtain ⟨ε₀,hε₀,hcontact⟩ := K.exists_uniform_rightConnector_middle_contact R hR
  refine ⟨ε₀,hε₀,?_⟩
  intro ε hε hsmall hW BR hBR
  constructor
  · intro q z hz
    exact (hcontact ε hε hsmall hW BR hBR q _ _ z hz.1 hz.2).2.2
  · intro q e k hne
    apply Set.disjoint_left.mpr
    intro z hz hm
    obtain ⟨he,hk,_⟩ := hcontact ε hε hsmall hW BR hBR q e k z hz hm
    exact hne (Prod.ext he hk)

end AllLeftGadget.TransverseScaffold
end
end MatchgateWidth
