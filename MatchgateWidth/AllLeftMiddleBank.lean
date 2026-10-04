import MatchgateWidth.AllLeftStageCarriers

/-! # Actual middle path banks with exact matching-graph endpoint maps -/
namespace MatchgateWidth
noncomputable section
namespace AllLeftGadget.TransverseScaffold
variable {S : LabelledShape} {a b c n t : ℕ} {I : AllLeftGadget S a b c n}
    (K : I.TransverseScaffold)

structure MiddleBank (ε : ℝ) where
  width : ∀ e, (K.route e).Width ε
  path : (e : Fin c ⊕ Fin n) → (k : Fin t) →
    Path ((K.route e).laneVertex (physicalLaneOffset ε e k) 0)
      ((K.route e).laneVertex (physicalLaneOffset ε e k) (Fin.last (K.indexed e).edgeCount))
  simple : ∀ e k, Function.Injective (path e k)
  range_eq : ∀ e k, Set.range (path e k) = (K.route e).laneSupport (physicalLaneOffset ε e k)
  disjoint : Pairwise (fun x y : (Fin c ⊕ Fin n) × Fin t =>
    Disjoint (Set.range (path x.1 x.2)) (Set.range (path y.1 y.2)))

theorem exists_uniform_middle_bank (t : ℕ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε, 0 < ε → ε ≤ ε₀ → Nonempty (K.MiddleBank (t := t) ε) := by
  obtain ⟨ε₀,hε₀,hsmall⟩ := K.exists_uniform_middle_paths t
  refine ⟨ε₀,hε₀,?_⟩
  intro ε hε hεle
  obtain ⟨hW,q,hq,hd⟩ := hsmall ε hε hεle
  exact ⟨⟨hW,q,fun e k => (hq e k).1,fun e k => (hq e k).2.2,hd⟩⟩

namespace MiddleBank
variable {K} {ε : ℝ} (M : K.MiddleBank (t := t) ε)

theorem norm_lt_one (hε : 0 < ε) (e : Fin c ⊕ Fin n) (k : Fin t) (u : unitInterval) :
    ‖M.path e k u‖ < 1 := by
  have hz : M.path e k u ∈ (K.route e).laneSupport (physicalLaneOffset ε e k) := by
    rw [← M.range_eq]; exact ⟨u,rfl⟩
  obtain ⟨i,hi⟩ := Set.mem_iUnion.mp
    ((K.route e).laneSupport_subset_carriers (M.width e) (physicalLaneOffset_bounds hε e k).2 hz)
  exact (K.carrier_geometry e _ (K.route_carrier_subset e i hi)).1

theorem avoids_inner (hε : 0 < ε) (e : Fin c ⊕ Fin n) (k : Fin t) :
    Disjoint (Set.range (M.path e k)) K.innerDisks := by
  rw [M.range_eq]
  exact K.laneSupport_avoids_inner e (M.width e) (physicalLaneOffset_bounds hε e k).2

/-- The path from the literal internally reversed left scalar port to the
literal unchanged right scalar port. -/
def internalPath (w : Fin (c*t)) :
    Path (K.leftCap ε (I.internalLeftWire w)) (K.rightCap ε (I.internalRightWire w)) :=
  (M.path (Sum.inl (finProdFinEquiv.symm w).1) (finProdFinEquiv.symm w).2).cast
    (by simpa only [Prod.mk.eta,Equiv.apply_symm_apply] using
      K.leftCap_internal ε (finProdFinEquiv.symm w).1 (finProdFinEquiv.symm w).2)
    (by simpa only [Prod.mk.eta,Equiv.apply_symm_apply] using
      K.rightCap_internal ε (finProdFinEquiv.symm w).1 (finProdFinEquiv.symm w).2)

/-- The path from the unchanged exposed left scalar port to the inherited
ordered outer cap, with no boundary block reversal. -/
def boundaryPath (w : Fin (n*t)) :
    Path (K.leftCap ε (I.boundaryLeftWire w)) (K.boundaryCap ε w) :=
  (M.path (Sum.inr (finProdFinEquiv.symm w).1) (finProdFinEquiv.symm w).2).cast
    (by simpa only [Prod.mk.eta,Equiv.apply_symm_apply] using
      K.leftCap_boundary ε (finProdFinEquiv.symm w).1 (finProdFinEquiv.symm w).2) rfl

theorem internalPath_simple (w : Fin (c*t)) : Function.Injective (M.internalPath w) :=
  M.simple _ _

theorem boundaryPath_simple (w : Fin (n*t)) : Function.Injective (M.boundaryPath w) :=
  M.simple _ _

theorem internalPaths_disjoint : Pairwise (fun w z : Fin (c*t) =>
    Disjoint (Set.range (M.internalPath w)) (Set.range (M.internalPath z))) := by
  intro w z hwz
  apply M.disjoint (i := (Sum.inl (finProdFinEquiv.symm w).1,(finProdFinEquiv.symm w).2))
    (j := (Sum.inl (finProdFinEquiv.symm z).1,(finProdFinEquiv.symm z).2))
  intro h
  apply hwz
  apply (finProdFinEquiv : Fin c × Fin t ≃ Fin (c*t)).symm.injective
  exact Prod.ext (Sum.inl.inj (congrArg Prod.fst h)) (congrArg (fun q : (Fin c ⊕ Fin n) × Fin t => q.2) h)

theorem boundaryPaths_disjoint : Pairwise (fun w z : Fin (n*t) =>
    Disjoint (Set.range (M.boundaryPath w)) (Set.range (M.boundaryPath z))) := by
  intro w z hwz
  apply M.disjoint (i := (Sum.inr (finProdFinEquiv.symm w).1,(finProdFinEquiv.symm w).2))
    (j := (Sum.inr (finProdFinEquiv.symm z).1,(finProdFinEquiv.symm z).2))
  intro h
  apply hwz
  apply (finProdFinEquiv : Fin n × Fin t ≃ Fin (n*t)).symm.injective
  exact Prod.ext (Sum.inr.inj (congrArg Prod.fst h)) (congrArg (fun q : (Fin c ⊕ Fin n) × Fin t => q.2) h)

theorem internal_boundary_disjoint (w : Fin (c*t)) (z : Fin (n*t)) :
    Disjoint (Set.range (M.internalPath w)) (Set.range (M.boundaryPath z)) := by
  apply M.disjoint (i := (Sum.inl (finProdFinEquiv.symm w).1,(finProdFinEquiv.symm w).2))
    (j := (Sum.inr (finProdFinEquiv.symm z).1,(finProdFinEquiv.symm z).2))
  intro h
  exact Sum.inl_ne_inr (congrArg Prod.fst h)

end MiddleBank
end AllLeftGadget.TransverseScaffold
end
end MatchgateWidth
