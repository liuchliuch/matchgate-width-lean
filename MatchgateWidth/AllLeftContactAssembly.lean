import MatchgateWidth.AllLeftGlobalGraphAssembly

/-! # Semantic-index assembly of the proved whole-stage contact laws -/
namespace MatchgateWidth
noncomputable section
namespace AllLeftGadget.TransverseScaffold
variable {S : LabelledShape} {a b c n t : ℕ} {I : AllLeftGadget S a b c n}
    (K : I.TransverseScaffold)

theorem boundaryCap_prod (ε : ℝ) (p : Fin n) (k : Fin t) :
    K.boundaryCap ε (finProdFinEquiv (p,k)) =
      (K.route (Sum.inr p)).laneVertex (physicalLaneOffset ε (Sum.inr p : Fin c ⊕ Fin n) k)
        (Fin.last (K.indexed (Sum.inr p)).edgeCount) :=
  congrArg (fun z : Fin n × Fin t => (K.route (Sum.inr z.1)).laneVertex
    (physicalLaneOffset ε (Sum.inr z.1 : Fin c ⊕ Fin n) z.2)
    (Fin.last (K.indexed (Sum.inr z.1)).edgeCount)) (finProdFinEquiv.symm_apply_apply (p,k))

/-- The exact incidence/lane equality in every whole-support contact law
proves all four ThreePieceRouting joins and off-wire disjointness fields. -/
theorem pieceContacts_of_point_contacts
    (L : I.LeftMatchingFamily (t := t)) (R : I.RightMatchingFamily (t := t))
    (hL : L.DiskDrawn) (hR : R.DiskDrawn) {ε : ℝ}
    (BL : ∀ v, K.LeftBank L hL ε v) (BR : ∀ v, K.RightBank R hR ε v)
    (M : K.MiddleBank (t := t) ε) (B : K.OuterAccessBank (t := t) ε)
    (hLC : ∀ q e k z, z ∈ Set.range (K.leftConnector L hL BL q) →
      z ∈ (K.route e).laneSupport (physicalLaneOffset ε e k) →
      q = I.leftWireEquiv (e,k) ∧ z = K.leftCap ε q)
    (hRC : ∀ q e k z, z ∈ Set.range (K.rightConnector R hR BR q) →
      z ∈ (K.route e).laneSupport (physicalLaneOffset ε e k) →
      (e,k) = (Sum.inl (I.rightWireEquiv.symm q).1,(I.rightWireEquiv.symm q).2) ∧
        z = K.rightCap ε q)
    (hOC : ∀ q e k z, z ∈ Set.range (B.path q) →
      z ∈ (K.route e).laneSupport (physicalLaneOffset ε e k) →
      e = Sum.inr (finProdFinEquiv.symm q).1 ∧
        k = (finProdFinEquiv.symm q).2 ∧ z = K.boundaryCap ε q) :
    K.PieceContacts L R hL hR BL BR M B := by
  have hmid (w : (Fin c ⊕ Fin n) × Fin t) {z : ℂ} (hz : z ∈ Set.range (K.allMiddle M w)) :
      z ∈ (K.route w.1).laneSupport (physicalLaneOffset ε w.1 w.2) := by
    rw [← M.range_eq]
    exact hz
  refine ⟨?_,?_,?_,?_⟩
  · intro w z hz
    exact (hLC _ w.1 w.2 z hz.1 (hmid w hz.2)).2
  · rintro ⟨e,k⟩ z hz
    cases e with
    | inl e =>
      have hr := hz.2
      rw [K.allRight_range_internal] at hr
      have he := (hRC _ (Sum.inl e) k z hr (hmid _ hz.1)).2
      exact he.trans (K.rightCap_equiv ε e k)
    | inr p =>
      have hr := hz.2
      rw [K.allRight_range_boundary] at hr
      have he := (hOC _ (Sum.inr p) k z hr (hmid _ hz.1)).2.2
      exact he.trans (K.boundaryCap_prod ε p k)
  · intro w v hwv
    apply Set.disjoint_left.mpr
    intro z hz hm
    have he := (hLC _ v.1 v.2 z hz (hmid v hm)).1
    exact hwv (I.leftWireEquiv.injective he)
  · intro w v hwv
    apply Set.disjoint_left.mpr
    intro z hm hz
    rcases v with ⟨e,k⟩
    cases e with
    | inl e =>
      rw [K.allRight_range_internal] at hz
      have he := (hRC _ w.1 w.2 z hz (hmid w hm)).1
      apply hwv
      simpa only [Equiv.symm_apply_apply,Prod.mk.eta] using he
    | inr p =>
      rw [K.allRight_range_boundary] at hz
      obtain ⟨he,hk,_⟩ := hOC _ w.1 w.2 z hz (hmid w hm)
      apply hwv
      simp only [Equiv.symm_apply_apply] at he hk
      exact Prod.ext he hk

end AllLeftGadget.TransverseScaffold
end
end MatchgateWidth
