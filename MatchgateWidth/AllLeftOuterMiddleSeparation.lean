import MatchgateWidth.AllLeftOuterAccessBank
import MatchgateWidth.CompactCurvePerturbation
import MatchgateWidth.OuterBoundaryAccess
import MatchgateWidth.AllLeftMiddlePieces

/-! # Derived separation of the exterior radial bank from central ribbons

The zero-width exterior ray can meet a central source support only in the
exact boundary collar cut. Source incidence and the indexed last-segment
criterion exclude every nonjoining pair. Compact perturbation then supplies
one width for all actual physical lanes and every such pair simultaneously.
-/
namespace MatchgateWidth
noncomputable section
open Set Filter Topology
namespace AllLeftGadget.TransverseScaffold
variable {S : LabelledShape} {a b c n t : ℕ} {I : AllLeftGadget S a b c n}
    (K : I.TransverseScaffold)

/-- The outer ray as an explicit curve in the common perturbation parameter. -/
def outerTail (ε : ℝ) (q : Fin (n*t)) : unitInterval → ℂ :=
  straightArc (K.boundaryCap ε q) ((2 / ‖K.boundaryCap ε q‖ : ℝ) • K.boundaryCap ε q)

@[simp] theorem boundaryCap_zero (q : Fin (n*t)) :
    K.boundaryCap 0 q = ((1-K.cutRadius:ℝ):ℂ) *
      boundaryPoint (K.ordered.drawing.angle (finProdFinEquiv.symm q).1) := by
  simp only [boundaryCap,physicalLaneOffset,TransversePolygonalRoute.laneOffset,
    zero_mul,TransversePolygonalRoute.laneVertex,ribbonSection,zero_smul,add_zero]
  exact K.boundary_target _

theorem boundaryCap_continuous (q : Fin (n*t)) : Continuous (fun ε => K.boundaryCap ε q) := by
  unfold boundaryCap TransversePolygonalRoute.laneVertex ribbonSection physicalLaneOffset
    TransversePolygonalRoute.laneOffset
  fun_prop

theorem boundaryCap_zero_norm (q : Fin (n*t)) : ‖K.boundaryCap 0 q‖ = 1-K.cutRadius := by
  rw [K.boundaryCap_zero,norm_mul,norm_boundaryPoint,mul_one,Complex.norm_real,
    Real.norm_eq_abs,abs_of_pos (sub_pos.mpr K.cutRadius_lt_one)]

theorem outerTail_continuousAt (q : Fin (n*t)) (u : unitInterval) :
    ContinuousAt (fun z : ℝ × unitInterval => K.outerTail z.1 q z.2) (0,u) := by
  have hn : ‖K.boundaryCap 0 q‖ ≠ 0 := by
    rw [K.boundaryCap_zero_norm]
    exact ne_of_gt (sub_pos.mpr K.cutRadius_lt_one)
  have hc : ContinuousAt (fun z : ℝ × unitInterval => K.boundaryCap z.1 q) (0,u) :=
    (K.boundaryCap_continuous q).continuousAt.comp continuousAt_fst
  have ht : ContinuousAt (fun z : ℝ × unitInterval => (z.2 : ℝ)) (0,u) :=
    continuous_subtype_val.continuousAt.comp continuousAt_snd
  unfold outerTail straightArc
  exact ((continuousAt_const.sub ht).smul hc).add
    (ht.smul ((continuousAt_const.div hc.norm hn).smul hc))

theorem outerTail_zero (q : Fin (n*t)) (u : unitInterval) :
    K.outerTail 0 q u = ((affineBlend (1-K.cutRadius) 2 u : ℝ):ℂ) *
      boundaryPoint (K.ordered.drawing.angle (finProdFinEquiv.symm q).1) := by
  unfold outerTail
  rw [K.boundaryCap_zero_norm,K.boundaryCap_zero]
  have hr : 1-K.cutRadius ≠ 0 := ne_of_gt (sub_pos.mpr K.cutRadius_lt_one)
  have hc : (1:ℂ) - (K.cutRadius:ℂ) ≠ 0 := by exact_mod_cast hr
  simp only [straightArc,affineBlend,Complex.real_smul,Complex.ofReal_mul,
    Complex.ofReal_add,Complex.ofReal_sub,Complex.ofReal_one,Complex.ofReal_ofNat,
    Complex.ofReal_div]
  field_simp [hc]

/-- The bank's path is the explicit radial perturbation curve. -/
theorem OuterAccessBank.path_eq_outerTail {ε : ℝ} (B : K.OuterAccessBank (t := t) ε)
    (q : Fin (n*t)) : (B.path q : unitInterval → ℂ) = K.outerTail ε q := by
  funext u
  rw [B.formula]
  have hn : ‖K.boundaryCap ε q‖ = B.radius q := by
    rw [B.cap_eq,norm_mul,norm_boundaryPoint,mul_one,Complex.norm_real,
      Real.norm_eq_abs,abs_of_pos (B.radius_pos q)]
  unfold outerTail
  rw [hn,B.cap_eq]
  have hr : B.radius q ≠ 0 := ne_of_gt (B.radius_pos q)
  simp only [straightArc,affineBlend,Complex.real_smul,Complex.ofReal_mul,
    Complex.ofReal_add,Complex.ofReal_sub,Complex.ofReal_one,Complex.ofReal_ofNat,
    Complex.ofReal_div]
  field_simp [Complex.ofReal_ne_zero.mpr hr]

private theorem cutRadius_le_four : K.cutRadius ≤ 4*K.collars.radius := by
  dsimp only [cutRadius]
  linarith [K.collars.positive]

/-- The unperturbed outer radial trace misses every original trimmed segment
except the final segment belonging to its own external edge. -/
theorem outerTail_zero_disjoint_trimmed (q : Fin (n*t)) (e : Fin c ⊕ Fin n)
    (i : Fin (K.indexed e).edgeCount)
    (haway : (Sum.inr (finProdFinEquiv.symm q).1 : Fin c ⊕ Fin n) ≠ e ∨
      i.val+1 ≠ (K.indexed e).edgeCount) :
    Disjoint (Set.range (K.outerTail 0 q))
      (segment ℝ ((K.collars.trimRoute K.cutRadius K.cutRadius_pos K.cutRadius_le_four e).vertex i.castSucc)
        ((K.collars.trimRoute K.cutRadius K.cutRadius_pos K.cutRadius_le_four e).vertex i.succ)) := by
  apply Set.disjoint_left.mpr
  rintro z ⟨u,rfl⟩ hz
  have hs : K.outerTail 0 q u ∈ K.collars.support K.cutRadius K.cutRadius_pos
      K.cutRadius_le_four e := Set.mem_iUnion.mpr ⟨i,hz⟩
  have hin := K.collars.support_inside_disk K.interior K.cutRadius K.cutRadius_pos
    K.cutRadius_le_four e hs
  have hpos : 0 < affineBlend (1-K.cutRadius) 2 u :=
    affineBlend_pos (sub_pos.mpr K.cutRadius_lt_one) (by norm_num) u
  have hnorm : ‖K.outerTail 0 q u‖ = affineBlend (1-K.cutRadius) 2 u := by
    rw [K.outerTail_zero,norm_mul,norm_boundaryPoint,mul_one,Complex.norm_real,
      Real.norm_eq_abs,abs_of_pos hpos]
  rw [hnorm] at hin
  have hlo : 1-K.cutRadius ≤ affineBlend (1-K.cutRadius) 2 u := by
    dsimp only [affineBlend]
    nlinarith [u.property.1,u.property.2,K.cutRadius_pos]
  have hb : K.outerTail 0 q u ∈ Metric.closedBall
      (K.ordered.drawing.vertex (Sum.inr (finProdFinEquiv.symm q).1)) K.cutRadius := by
    rw [K.ordered.drawing.external_vertex]
    change dist (K.outerTail 0 q u) (boundaryPoint _) ≤ K.cutRadius
    rw [K.outerTail_zero,dist_eq_norm]
    have he (x : ℝ) (b : ℂ) : (x:ℂ)*b-b = ((x-1:ℝ):ℂ)*b := by
      push_cast
      ring
    rw [he,norm_mul,norm_boundaryPoint,mul_one,Complex.norm_real,Real.norm_eq_abs,
      abs_of_neg (sub_neg.mpr hin)]
    linarith
  rcases K.collars.support_closedBall_contact K.cutRadius K.cutRadius_pos
      K.cutRadius_le_four (Sum.inr (finProdFinEquiv.symm q).1) e ⟨hs,hb⟩ with
      ⟨he,_⟩ | ⟨he,hcut⟩
  · simp only [AllLeftGadget.graph,Sum.inl_ne_inr] at he
  · have heq : e = Sum.inr (finProdFinEquiv.symm q).1 := by
      cases e with
      | inl e => simp [AllLeftGadget.graph] at he
      | inr p => exact congrArg Sum.inr (Sum.inr.inj he)
    have hlast : i.val+1 = (K.indexed e).edgeCount := by
      apply ((K.collars.trimRoute K.cutRadius K.cutRadius_pos K.cutRadius_le_four e).target_mem_segment_iff_last i).mp
      rwa [hcut] at hz
    exact haway.elim (fun h => h heq.symm) (fun h => h hlast)

/-- One genuine positive bound separates all nonjoining outer/middle pairs,
including different source edges and all earlier segments of the same edge.
The two families may be perturbed independently inside that bound. -/
theorem exists_uniform_outer_middle_separation (t : ℕ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε η, |ε| < ε₀ → |η| < ε₀ →
      ∀ (q : Fin (n*t)) (e : Fin c ⊕ Fin n) (k : Fin t)
        (i : Fin (K.indexed e).edgeCount),
      ((Sum.inr (finProdFinEquiv.symm q).1 : Fin c ⊕ Fin n) ≠ e ∨
        i.val+1 ≠ (K.indexed e).edgeCount) →
      Disjoint (Set.range (K.outerTail ε q)) (Set.range (K.middlePiece e k i η)) := by
  classical
  let J := Fin (n*t) ⊕ (Σ e : Fin c ⊕ Fin n, Fin t × Fin (K.indexed e).edgeCount)
  let f : J → ℝ → unitInterval → ℂ := Sum.elim
    (fun q ε => K.outerTail ε q)
    (fun z ε => K.middlePiece z.1 z.2.1 z.2.2 ε)
  let Rel : J → J → Prop := fun x y => match x,y with
    | Sum.inl q, Sum.inr z =>
      (Sum.inr (finProdFinEquiv.symm q).1 : Fin c ⊕ Fin n) ≠ z.1 ∨
        z.2.2.val+1 ≠ (K.indexed z.1).edgeCount
    | _,_ => False
  have hbase : ∀ j, Continuous (f j 0) := by
    rintro (q | z)
    · exact continuous_straightArc _ _
    · exact K.middlePiece_continuous _ _ _ _
  have hf : ∀ j u, ContinuousAt (fun z : ℝ × unitInterval => f j z.1 z.2) (0,u) := by
    rintro (q | z) u
    · exact K.outerTail_continuousAt q u
    · exact K.middlePiece_continuousAt_zero _ _ _ u
  have hd : ∀ x y, Rel x y → Disjoint (Set.range (f x 0)) (Set.range (f y 0)) := by
    rintro (q | x) (r | y) h <;> try exact h.elim
    change Disjoint (Set.range (K.outerTail 0 q))
      (Set.range (K.middlePiece y.1 y.2.1 y.2.2 0))
    rw [K.middlePiece_zero_range]
    exact K.outerTail_zero_disjoint_trimmed q y.1 y.2.2 h
  obtain ⟨ε₀,hε₀,_,hsep⟩ := finite_related_curve_perturbations_disjoint Rel f hbase hf hd
    (fun _ => Set.univ) (fun _ => isOpen_univ) (fun _ => Set.subset_univ _)
  refine ⟨ε₀,hε₀,?_⟩
  intro ε η hε hη q e k i haway
  exact hsep (Sum.inl q) (Sum.inr ⟨e,k,i⟩) haway ε η hε hη

/-- Separation specializes to every actual derived outer bank, independent
of the existential angle choices used to construct that bank. -/
theorem exists_uniform_outerAccess_middle_separation (t : ℕ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε, 0 < ε → ε < ε₀ →
      ∀ (B : K.OuterAccessBank (t := t) ε) (q : Fin (n*t))
        (e : Fin c ⊕ Fin n) (k : Fin t) (i : Fin (K.indexed e).edgeCount),
      ((Sum.inr (finProdFinEquiv.symm q).1 : Fin c ⊕ Fin n) ≠ e ∨
        i.val+1 ≠ (K.indexed e).edgeCount) →
      Disjoint (Set.range (B.path q)) (Set.range (K.middlePiece e k i ε)) := by
  obtain ⟨ε₀,hε₀,hsep⟩ := K.exists_uniform_outer_middle_separation t
  refine ⟨ε₀,hε₀,?_⟩
  intro ε hε hsmall B q e k i haway
  rw [B.path_eq_outerTail]
  exact hsep ε ε (by simpa only [abs_of_pos hε] using hsmall)
    (by simpa only [abs_of_pos hε] using hsmall) q e k i haway

/-- The actual outer path is the outward traversal of the radial section cap
used by the exact final-ribbon contact theorem. -/
theorem OuterAccessBank.path_eq_radialSectionCap {ε : ℝ}
    (B : K.OuterAccessBank (t := t) ε) (p : Fin n) (l : Fin t) (u : unitInterval) :
    B.path (finProdFinEquiv (p,l)) u =
      radialSectionCap 0
        ((K.route (Sum.inr p)).vertex (Fin.last (K.indexed (Sum.inr p)).edgeCount))
        ((K.route (Sum.inr p)).transverse (Fin.last (K.indexed (Sum.inr p)).edgeCount))
        (physicalLaneOffset ε (Sum.inr p : Fin c ⊕ Fin n) l)
        (2 / B.radius (finProdFinEquiv (p,l))) (LabelledInstance.reverseParameter u) := by
  rw [B.path_eq_outerTail]
  have hn : ‖K.boundaryCap ε (finProdFinEquiv (p,l))‖ = B.radius (finProdFinEquiv (p,l)) := by
    rw [B.cap_eq,norm_mul,norm_boundaryPoint,mul_one,Complex.norm_real,
      Real.norm_eq_abs,abs_of_pos (B.radius_pos _)]
  unfold outerTail
  rw [hn]
  simp only [boundaryCap,Equiv.symm_apply_apply,TransversePolygonalRoute.laneVertex,
    radialSectionCap,zero_add,sub_zero,LabelledInstance.reverseParameter,straightArc]
  rw [Equiv.symm_apply_apply]
  module

/-- The exceptional final strip has exactly the intended endpoint join. In
particular it is disjoint from the outer rays of every different physical lane. -/
theorem OuterAccessBank.last_middle_eq_iff {ε : ℝ} (hε : 0 < ε)
    (B : K.OuterAccessBank (t := t) ε) (p : Fin n) (l k : Fin t)
    (hW : (K.route (Sum.inr p)).Width ε) (u s : unitInterval) :
    B.path (finProdFinEquiv (p,l)) u =
      K.middlePiece (Sum.inr p) k (K.indexed (Sum.inr p)).lastEdge ε s ↔
      u=0 ∧ s=1 ∧ l=k := by
  let j := (K.indexed (Sum.inr p)).lastEdge
  have hα : 1 < 2 / B.radius (finProdFinEquiv (p,l)) :=
    (one_lt_div (B.radius_pos _)).mpr (B.radius_lt_two _)
  have hcap : 0 < orientedArea
      ((K.route (Sum.inr p)).vertex j.succ-0) ((K.route (Sum.inr p)).transverse j.succ) := by
    simpa only [j,IndexedSimplePolygonalRoute.lastEdge_succ,sub_zero,K.boundary_target]
      using K.boundary_area_positive p
  have hwire := (hW (physicalLaneOffset ε (Sum.inr p : Fin c ⊕ Fin n) k)
    (physicalLaneOffset_bounds hε _ k).2 j).2.1
  have hiff := ribbon_outerRadialCap_eq_iff 0
    ((K.route (Sum.inr p)).vertex j.castSucc) ((K.route (Sum.inr p)).vertex j.succ)
    ((K.route (Sum.inr p)).transverse j.castSucc) ((K.route (Sum.inr p)).transverse j.succ)
    (physicalLaneOffset ε (Sum.inr p : Fin c ⊕ Fin n) k)
    (physicalLaneOffset ε (Sum.inr p : Fin c ⊕ Fin n) l)
    (2 / B.radius (finProdFinEquiv (p,l))) hα hcap hwire s (LabelledInstance.reverseParameter u)
  rw [B.path_eq_radialSectionCap]
  change radialSectionCap 0 _ _ _ _ _ = ribbonArc _ _ _ _ _ _ ↔ _
  rw [eq_comm]
  rw [show (Fin.last (K.indexed (Sum.inr p)).edgeCount) = j.succ from
    (K.indexed (Sum.inr p)).lastEdge_succ.symm]
  rw [hiff]
  constructor
  · rintro ⟨hs,hu,hkl⟩
    have hu0 : u=0 := Subtype.ext (by
      have hh := congrArg Subtype.val hu
      change 1-(u:ℝ)=1 at hh
      change (u:ℝ)=0
      linarith)
    exact ⟨hu0,hs,(physicalLaneOffset_injective hε (Sum.inr p) hkl).symm⟩
  · rintro ⟨rfl,rfl,rfl⟩
    exact ⟨rfl,Subtype.ext (by simp [LabelledInstance.reverseParameter]),rfl⟩

/-- Whole-support contact for the actual outer bank. Any intersection already
identifies the unique semantic wire and its designated final cap point. -/
theorem exists_uniform_outerAccess_middle_contact (t : ℕ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε, 0 < ε → ε < ε₀ →
      (∀ e, (K.route e).Width ε) → ∀ (B : K.OuterAccessBank (t := t) ε)
      (q : Fin (n*t)) (e : Fin c ⊕ Fin n) (k : Fin t) (z : ℂ),
      z ∈ Set.range (B.path q) →
      z ∈ (K.route e).laneSupport (physicalLaneOffset ε e k) →
      e = Sum.inr (finProdFinEquiv.symm q).1 ∧
        k = (finProdFinEquiv.symm q).2 ∧ z = K.boundaryCap ε q := by
  obtain ⟨ε₀,hε₀,hsep⟩ := K.exists_uniform_outerAccess_middle_separation t
  refine ⟨ε₀,hε₀,?_⟩
  intro ε hε hsmall hW B q e k z hz hm
  obtain ⟨⟨p,l⟩,rfl⟩ := finProdFinEquiv.surjective q
  simp only [Equiv.symm_apply_apply]
  obtain ⟨u,hu⟩ := hz
  obtain ⟨i,s,hs⟩ := Set.mem_iUnion.mp hm
  have hpair : B.path (finProdFinEquiv (p,l)) u = K.middlePiece e k i ε s :=
    hu.trans hs.symm
  by_cases he : e = Sum.inr p
  · subst e
    by_cases hi : i.val+1 = (K.indexed (Sum.inr p)).edgeCount
    · have hii : i = (K.indexed (Sum.inr p)).lastEdge := by
        apply Fin.ext
        simp only [IndexedSimplePolygonalRoute.lastEdge_val]
        omega
      subst i
      obtain ⟨hu0,hs1,hlk⟩ := (OuterAccessBank.last_middle_eq_iff K hε B p l k (hW _) u s).mp hpair
      refine ⟨rfl,hlk.symm,?_⟩
      rw [← hu,hu0]
      exact (B.path _).source
    · exact (Set.disjoint_left.mp (hsep ε hε hsmall B _ _ k i (Or.inr hi))
        ⟨u,hu⟩ ⟨s,hs⟩).elim
  · have haway : (Sum.inr (finProdFinEquiv.symm (finProdFinEquiv (p,l))).1 : Fin c ⊕ Fin n) ≠ e := by
      simpa only [Equiv.symm_apply_apply] using Ne.symm he
    exact (Set.disjoint_left.mp (hsep ε hε hsmall B _ e k i (Or.inl haway))
      ⟨u,hu⟩ ⟨s,hs⟩).elim

/-- The contact law packaged directly as matching endpoint-only intersection
and complete off-wire disjointness, ready for concatenated path ranges. -/
theorem exists_uniform_outerAccess_whole_middle (t : ℕ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε, 0 < ε → ε < ε₀ →
      (∀ e, (K.route e).Width ε) → ∀ (B : K.OuterAccessBank (t := t) ε),
      (∀ q : Fin (n*t), Set.range (B.path q) ∩
        (K.route (Sum.inr (finProdFinEquiv.symm q).1)).laneSupport
          (physicalLaneOffset ε (Sum.inr (finProdFinEquiv.symm q).1 : Fin c ⊕ Fin n)
            (finProdFinEquiv.symm q).2) ⊆ {K.boundaryCap ε q}) ∧
      (∀ (q : Fin (n*t)) (e : Fin c ⊕ Fin n) (k : Fin t),
        (e,k) ≠ (Sum.inr (finProdFinEquiv.symm q).1,(finProdFinEquiv.symm q).2) →
        Disjoint (Set.range (B.path q))
          ((K.route e).laneSupport (physicalLaneOffset ε e k))) := by
  obtain ⟨ε₀,hε₀,hcontact⟩ := K.exists_uniform_outerAccess_middle_contact t
  refine ⟨ε₀,hε₀,?_⟩
  intro ε hε hsmall hW B
  constructor
  · intro q z hz
    exact (hcontact ε hε hsmall hW B q _ _ z hz.1 hz.2).2.2
  · intro q e k hne
    apply Set.disjoint_left.mpr
    intro z hz hm
    obtain ⟨he,hk,_⟩ := hcontact ε hε hsmall hW B q e k z hz hm
    exact hne (Prod.ext he hk)

end AllLeftGadget.TransverseScaffold
end
end MatchgateWidth
