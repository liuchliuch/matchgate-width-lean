import MatchgateWidth.AllLeftConnectorRaw
import MatchgateWidth.AllLeftConnectorPlacement

/-! # Actual left connector contacts with entire middle wire routes

All non-adjoining pieces are separated by the source-collar reference theorem
and compact perturbation. The adjoining first strip is handled by the exact
radial-area formula, including the annular head exclusion. The resulting
whole-route contact identifies the literal local scalar port and its cap.
-/
namespace MatchgateWidth
noncomputable section
open Set
namespace AllLeftGadget.TransverseScaffold
variable {S : LabelledShape} {a b c n t : ℕ} {I : AllLeftGadget S a b c n}
    (K : I.TransverseScaffold)
set_option maxHeartbeats 1000000

/-- All original non-adjoining connector/segment pairs remain disjoint under
one common width bound. Matching first pieces are explicitly excluded. -/
theorem exists_uniform_leftRaw_middle_separation
    (L : I.LeftMatchingFamily (t := t)) (hL : L.DiskDrawn) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε η, |ε| < ε₀ → |η| < ε₀ →
      ∀ v (q : Fin (S.leftArity (I.leftLabel v)*t)) (e : Fin c ⊕ Fin n) (k : Fin t) (j : Fin (K.indexed e).edgeCount),
      (I.leftIncidence ⟨v,(finProdFinEquiv.symm q).1⟩ ≠ e ∨ j.val ≠ 0) →
      Disjoint (Set.range (K.leftRaw L hL v q ε)) (Set.range (K.middlePiece e k j η)) := by
  classical
  let C := Σ v : Fin a, Fin (S.leftArity (I.leftLabel v)*t)
  let P := Σ e : Fin c ⊕ Fin n, Fin t × Fin (K.indexed e).edgeCount
  let J := C ⊕ P
  let f : J → ℝ → unitInterval → ℂ := Sum.elim
    (fun q ε => K.leftRaw L hL q.1 q.2 ε)
    (fun z ε => K.middlePiece z.1 z.2.1 z.2.2 ε)
  let Rel : J → J → Prop := fun x y => match x,y with
    | Sum.inl q, Sum.inr z =>
      I.leftIncidence ⟨q.1,(finProdFinEquiv.symm q.2).1⟩ ≠ z.1 ∨ z.2.2.val ≠ 0
    | _,_ => False
  have hbase : ∀ j, Continuous (f j 0) := by
    rintro (q|z)
    · exact K.leftRaw_zero_continuous L hL q.1 q.2
    · exact K.middlePiece_continuous _ _ _ _
  have hf : ∀ j u, ContinuousAt (fun z : ℝ × unitInterval => f j z.1 z.2) (0,u) := by
    rintro (q|z) u
    · exact K.leftRaw_continuousAt_zero L hL q.1 q.2 u
    · exact K.middlePiece_continuousAt_zero _ _ _ u
  have hd : ∀ x y, Rel x y → Disjoint (Set.range (f x 0)) (Set.range (f y 0)) := by
    rintro (q|x) (r|y) h <;> try exact h.elim
    exact K.leftRaw_zero_piece_disjoint L hL q.1 q.2 y.1 y.2.1 y.2.2 h
  obtain ⟨ε₀,hε₀,_,hsep⟩ := finite_related_curve_perturbations_disjoint Rel f hbase hf hd
    (fun _ => Set.univ) (fun _ => isOpen_univ) (fun _ => Set.subset_univ _)
  exact ⟨ε₀,hε₀,fun ε η hε hη v q e k j haway =>
    hsep (Sum.inl ⟨v,q⟩) (Sum.inr ⟨e,k,j⟩) haway ε η hε hη⟩

/-- The excluded first-piece case has only the intended same-wire cap contact,
with all wire positions checked against the actual left incidence equivalence. -/
theorem leftRaw_first_contact (L : I.LeftMatchingFamily (t := t)) (hL : L.DiskDrawn)
    {ε : ℝ} (hε : 0 < ε) (hW : ∀ e, (K.route e).Width ε)
    (v : Fin a) (i : Fin (S.leftArity (I.leftLabel v))) (l k : Fin t)
    (htail : RadialTailProperty (K.leftRaw L hL v (finProdFinEquiv (i,l)) ε)
      (K.ordered.primitiveCenter (Sum.inl v))
      (K.leftCap ε ⟨v,finProdFinEquiv (i,l)⟩ - K.ordered.primitiveCenter (Sum.inl v))
      (K.collars.radius/2))
    (s u : unitInterval)
    (heq : K.leftRaw L hL v (finProdFinEquiv (i,l)) ε s =
      K.middlePiece (I.leftIncidence ⟨v,i⟩) k (K.indexed (I.leftIncidence ⟨v,i⟩)).firstEdge ε u) :
    (⟨v,finProdFinEquiv (i,l)⟩ : Σ v, Fin (S.leftArity (I.leftLabel v)*t)) =
      I.leftWireEquiv (I.leftIncidence ⟨v,i⟩,k) ∧
    K.leftRaw L hL v (finProdFinEquiv (i,l)) ε s = K.leftCap ε ⟨v,finProdFinEquiv (i,l)⟩ := by
  let e := I.leftIncidence ⟨v,i⟩
  let j := (K.indexed e).firstEdge
  let C := K.ordered.primitiveCenter (Sum.inl v)
  let P := (K.route e).vertex 0
  let W := (K.route e).transverse 0
  let δ := TransversePolygonalRoute.laneOffset ε t l
  let η := physicalLaneOffset ε e k
  have hc : K.ordered.drawing.vertex (I.graph.left e) = C := by
    simp [e,C,AllLeftGadget.graph,OrderedPlanar.primitiveCenter]
  have hcap : K.leftCap ε ⟨v,finProdFinEquiv (i,l)⟩ = ribbonSection P W δ := by
    rw [K.leftCap_local_formula]
    simp only [OrderedPlanar.leftCutVector,leftTransverse,leftCoefficients,mul_laneOffset_one]
    dsimp only [P,W,δ,e,C]
    rw [K.route_source]
    simp only [ribbonSection,Complex.real_smul]
    ring

  have hpiece : K.middlePiece e k j ε u =
      ribbonArc P ((K.route e).vertex j.succ) W ((K.route e).transverse j.succ) η u := by
    simp only [middlePiece,TransversePolygonalRoute.edge,j,IndexedSimplePolygonalRoute.firstEdge_castSucc]
    rfl
  have harea : 0 < orientedArea (P-C) W := by
    simpa only [P,W,K.route_source,hc] using K.source_area_positive e
  have hwire : 0 < orientedArea
      (ribbonDirection P ((K.route e).vertex j.succ) W ((K.route e).transverse j.succ) η) W := by
    simpa only [j,IndexedSimplePolygonalRoute.firstEdge_castSucc,P,W,η]
      using (hW e (physicalLaneOffset ε e k) (physicalLaneOffset_bounds hε e k).2 j).1
  rcases htail s with hhead | ⟨β,hβ0,hβ1,hβ⟩
  · have hout := (K.carrier_geometry e _
      (K.middlePiece_subset_carrier hε hW e k j ⟨u,rfl⟩)).2 (I.graph.left e)
    rw [hc] at hout
    rw [heq] at hhead
    change dist (K.middlePiece e k j ε u) C ≤ K.collars.radius/2 at hhead
    linarith [K.collars.positive]
  · have hb : K.leftRaw L hL v (finProdFinEquiv (i,l)) ε s =
        C + β • (ribbonSection P W δ-C) :=
      hβ.trans (congrArg (fun z : ℂ => C + β • (z-C)) hcap)
    have ha := congrArg (fun z => orientedArea W (z-P)) (hb.symm.trans heq)
    rw [hpiece,radialSection_point_area,ribbonArc_after_area] at ha
    have hnn : 0 ≤ (1-β)*orientedArea (P-C) W := mul_nonneg (sub_nonneg.mpr hβ1) harea.le
    have hu0 : (u : ℝ) = 0 := by nlinarith [u.property.1]
    have hbeq : β = 1 := by rw [hu0] at ha; nlinarith
    have hu : u = 0 := Subtype.ext hu0
    have hterminal : K.leftRaw L hL v (finProdFinEquiv (i,l)) ε s =
        K.leftCap ε ⟨v,finProdFinEquiv (i,l)⟩ := by
      rw [hβ,hbeq,one_smul,add_sub_cancel]
    have hw : W ≠ 0 := by intro hz; simp [hz] at harea
    have hoffset : δ = η := by
      have hh := hterminal.symm.trans heq
      rw [hcap,hpiece,hu,ribbonArc_zero] at hh
      exact smul_left_injective ℝ hw (add_left_cancel hh)
    have hlk : l = geometricLane e k :=
      (TransversePolygonalRoute.laneOffset_strictMono hε t).injective hoffset
    have hport : (⟨v,finProdFinEquiv (i,l)⟩ : Σ v, Fin (S.leftArity (I.leftLabel v)*t)) =
        I.leftWireEquiv (I.leftIncidence ⟨v,i⟩,k) := by
      rw [I.leftWireEquiv_apply_incidence]
      exact congrArg (fun z => (⟨v,finProdFinEquiv (i,z)⟩ : Σ v, Fin (S.leftArity (I.leftLabel v)*t))) hlk
    exact ⟨hport,hterminal⟩

/-- One window for all actual left radial connector tails. -/
theorem exists_uniform_leftRaw_tails (L : I.LeftMatchingFamily (t := t)) (hL : L.DiskDrawn) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε, |ε| < ε₀ → ∀ v q,
      RadialTailProperty (K.leftRaw L hL v q ε) (K.ordered.primitiveCenter (Sum.inl v))
        (K.leftCap ε ⟨v,q⟩-K.ordered.primitiveCenter (Sum.inl v)) (K.collars.radius/2) := by
  classical
  have hex (v : Fin a) := (K.leftAngles v).exists_radialTail_radius
    (K.ordered.primitiveCenter (Sum.inl v)) (K.leftTransverse v) (K.leftCoefficients v)
    (L.nativeDrawing hL v).angle _ _
    ((K.leftAngles v).round_connector_parameters K.collars.radius K.collars.positive (K.leftCutVector_norm v)).1
    ((K.leftAngles v).round_connector_parameters K.collars.radius K.collars.positive (K.leftCutVector_norm v)).2.1
    ((K.leftAngles v).round_connector_parameters K.collars.radius K.collars.positive (K.leftCutVector_norm v)).2.2.1
  choose η hη hspec using hex
  obtain ⟨ε₀,hε₀,hmin⟩ := finite_positive_lower_bound η hη
  refine ⟨ε₀,hε₀,?_⟩
  intro ε hε v q
  have h := hspec v ε (hε.trans_le (hmin v)) q
  have hp := (K.leftAngles v).round_connector_parameters K.collars.radius K.collars.positive (K.leftCutVector_norm v)
  rw [hp.2.2.2] at h
  rw [K.leftCap_eq_blockEndpoint ε v (K.leftAngles v) q,add_sub_cancel_left]
  exact h

/-- Full contact law for the actual placed-graph left connector and an entire
middle wire support. It identifies the exact semantic/local wire map. -/
theorem exists_uniform_leftConnector_middle_contact
    (L : I.LeftMatchingFamily (t := t)) (hL : L.DiskDrawn) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε, 0 < ε → ε < ε₀ →
      (∀ e, (K.route e).Width ε) →
      ∀ (BL : ∀ v, K.LeftBank L hL ε v),
      (∀ v q u, (BL v).path q u = K.leftRaw L hL v q ε u) →
      ∀ (q : Σ v : Fin a, Fin (S.leftArity (I.leftLabel v)*t))
        (e : Fin c ⊕ Fin n) (k : Fin t) (z : ℂ),
      z ∈ Set.range (K.leftConnector L hL BL q) →
      z ∈ (K.route e).laneSupport (physicalLaneOffset ε e k) →
      q = I.leftWireEquiv (e,k) ∧ z = K.leftCap ε q := by
  obtain ⟨η,hη,hsep⟩ := K.exists_uniform_leftRaw_middle_separation L hL
  obtain ⟨τ,hτ,htail⟩ := K.exists_uniform_leftRaw_tails L hL
  refine ⟨min η τ,lt_min hη hτ,?_⟩
  intro ε hε hsmall hW BL hBL q e k z hz hm
  have heη : |ε| < η := by rw [abs_of_pos hε]; exact hsmall.trans_le (min_le_left _ _)
  have heτ : |ε| < τ := by rw [abs_of_pos hε]; exact hsmall.trans_le (min_le_right _ _)
  rcases q with ⟨v,q⟩
  obtain ⟨⟨i,l⟩,rfl⟩ := finProdFinEquiv.surjective q
  obtain ⟨u,hu⟩ := hz
  obtain ⟨j,s,hs⟩ := Set.mem_iUnion.mp hm
  have hrawz : K.leftRaw L hL v (finProdFinEquiv (i,l)) ε u = z :=
    (hBL v _ u).symm.trans hu
  have hpair : K.leftRaw L hL v (finProdFinEquiv (i,l)) ε u = K.middlePiece e k j ε s :=
    hrawz.trans hs.symm
  by_cases he : e = I.leftIncidence ⟨v,i⟩
  · subst e
    by_cases hj : j.val = 0
    · have hjj : j = (K.indexed (I.leftIncidence ⟨v,i⟩)).firstEdge := Fin.ext hj
      subst j
      obtain ⟨hport,hpoint⟩ := K.leftRaw_first_contact L hL hε hW v i l k
        (htail ε heτ v _) u s hpair
      exact ⟨hport,hrawz.symm.trans hpoint⟩
    · have haway : I.leftIncidence ⟨v,(finProdFinEquiv.symm (finProdFinEquiv (i,l))).1⟩ ≠
          I.leftIncidence ⟨v,i⟩ ∨ j.val ≠ 0 := Or.inr hj
      exact (Set.disjoint_left.mp (hsep ε ε heη heη v _ _ k j haway)
        ⟨u,hrawz⟩ ⟨s,hs⟩).elim
  · have haway : I.leftIncidence ⟨v,(finProdFinEquiv.symm (finProdFinEquiv (i,l))).1⟩ ≠ e ∨ j.val ≠ 0 := by
      left
      simpa only [Equiv.symm_apply_apply] using Ne.symm he
    exact (Set.disjoint_left.mp (hsep ε ε heη heη v _ e k j haway)
      ⟨u,hrawz⟩ ⟨s,hs⟩).elim

/-- The contact law in the exact whole-support shape consumed by the final
three-piece wire constructor, including all exposed left ports. -/
theorem exists_uniform_leftConnector_whole_middle
    (L : I.LeftMatchingFamily (t := t)) (hL : L.DiskDrawn) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε, 0 < ε → ε < ε₀ →
      (∀ e, (K.route e).Width ε) →
      ∀ (BL : ∀ v, K.LeftBank L hL ε v),
      (∀ v q u, (BL v).path q u = K.leftRaw L hL v q ε u) →
      (∀ q : Σ v : Fin a, Fin (S.leftArity (I.leftLabel v)*t),
        Set.range (K.leftConnector L hL BL q) ∩
          (K.route (I.leftWireEquiv.symm q).1).laneSupport
            (physicalLaneOffset ε (I.leftWireEquiv.symm q).1 (I.leftWireEquiv.symm q).2) ⊆ {K.leftCap ε q}) ∧
      (∀ (q : Σ v : Fin a, Fin (S.leftArity (I.leftLabel v)*t)) e k,
        (e,k) ≠ I.leftWireEquiv.symm q → Disjoint (Set.range (K.leftConnector L hL BL q))
          ((K.route e).laneSupport (physicalLaneOffset ε e k))) := by
  obtain ⟨ε₀,hε₀,hcontact⟩ := K.exists_uniform_leftConnector_middle_contact L hL
  refine ⟨ε₀,hε₀,?_⟩
  intro ε hε hsmall hW BL hBL
  constructor
  · intro q z hz
    exact (hcontact ε hε hsmall hW BL hBL q _ _ z hz.1 hz.2).2
  · intro q e k hne
    apply Set.disjoint_left.mpr
    intro z hz hm
    have hq := (hcontact ε hε hsmall hW BL hBL q e k z hz hm).1
    have hh := congrArg I.leftWireEquiv.symm hq
    exact hne (by simpa only [Equiv.symm_apply_apply] using hh.symm)

end AllLeftGadget.TransverseScaffold
end
end MatchgateWidth
