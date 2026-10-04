import MatchgateWidth.ControlledLabelledRanks
import MatchgateWidth.ControlledFlagEndpoints
import MatchgateWidth.AllLeftSupportGeometry
import MatchgateWidth.PrimitiveAllLeftGadget
import MatchgateWidth.AllLeftIncidences

/-! # Actual connected-planar flag closure of the controlled family

The support sets below consist of actual, properly wired, ordered-planar
connected gadgets. Their values are finite network contractions. No lifting,
normal-form, span-closure, or matchgate identity is assumed for a gadget.
-/
namespace MatchgateWidth
noncomputable section
open scoped Classical
set_option maxHeartbeats 800000
local instance controlledFlagFinDecidableEq (m : ℕ) : DecidableEq (Fin m) := Classical.decEq _

/-- Parity is invariant under a bijection of the tensor's domain ports. -/
theorem TensorHasParity.relabel {I J D K : Type*} [Field K]
    [Fintype I] [Fintype J] [Fintype D]
    (e : J ≃ I) (χ : D → ZMod 2) (T : (I → D) → K) (ε : ZMod 2)
    (hT : TensorHasParity χ T ε) :
    TensorHasParity χ (fun x : J → D => T (x ∘ e.symm)) ε := by
  intro x hx
  have h := hT (x ∘ e.symm) hx
  calc
    (∑ j, χ (x j)) = ∑ i, χ (x (e.symm i)) := (e.symm.sum_comp _).symm
    _ = ε := h

/-- The first two links contribute even marker parity even after conversion to
the literal source order. -/
theorem orderedControlledQutrit_hasParity {k : ℕ} (f : BooleanTable k ℂ) (j : Fin k) :
    TensorHasParity qutritMarkerParity (orderedControlledQutrit f j) 0 := by
  rw [orderedControlledQutrit_eq_relabel]
  exact (controlledQutrit_hasParity f j).relabel (controlledLabelledPortEquiv k)
    qutritMarkerParity (controlledQutrit f j) 0

theorem controlledLabelledLeft_pin_eq {k : ℕ} (f : BooleanTable k ℂ) (j : Fin k) (r : Fin 3) :
    (controlledLabelledLanguage f j).left (Sum.inl r) = qutritPinTensor r := by
  funext x
  simp [controlledLabelledLanguage, coordinatePin, qutritPinTensor, eq_comm]

/-- Every controlled left primitive has exactly the source fixed plane or a
coordinate ray as its exposed support. -/
theorem controlledLabelledLeft_support {k : ℕ} (f : BooleanTable k ℂ) (j : Fin k)
    (l : (starLanguageShape (k + 2)).LeftLabel)
    (p : Fin ((starLanguageShape (k + 2)).leftArity l)) :
    columnSupport (portFlatten ((controlledLabelledLanguage f j).left l) p) =
      qutritCoordinatePlane 2 ∨
    ∃ r, columnSupport (portFlatten ((controlledLabelledLanguage f j).left l) p) =
      qutritCoordinateRay r := by
  cases l with
  | inl r =>
    right
    have hp : p = 0 := Subsingleton.elim _ _
    subst p
    refine ⟨r,?_⟩
    rw [controlledLabelledLeft_pin_eq]
    simpa only [columnSupport, Matrix.range_mulVecLin, qutritCoordinateRay] using
      (qutritPin_support (K := ℂ) r)
  | inr u =>
    left
    simpa only [controlledLabelledLanguage, columnSupport, Matrix.range_mulVecLin] using (qutritNeq_support (K := ℂ) p)

/-- Direct marker conservation for every actual all-left gadget. -/
theorem controlledAllLeft_hasParity {k a b c n : ℕ}
    (I : AllLeftGadget (starLanguageShape (k + 2)) a b c n)
    (f : BooleanTable k ℂ) (j : Fin k) :
    ∃ ε, TensorHasParity qutritMarkerParity (I.value (controlledLabelledLanguage f j)) ε := by
  let ε : Fin a ⊕ Fin b → ZMod 2 := Sum.elim
    (fun v => Sum.elim qutritMarkerParity (fun _ => 1) (I.leftLabel v)) (fun _ => 0)
  refine ⟨∑ v, ε v,?_⟩
  apply networkValue_hasParity I.incidence I.properNetworkIncidences qutritMarkerParity
    (I.tensors (controlledLabelledLanguage f j)) ε
  have hleft (l : (starLanguageShape (k + 2)).LeftLabel) :
      TensorHasParity qutritMarkerParity ((controlledLabelledLanguage f j).left l)
        (Sum.elim qutritMarkerParity (fun _ => 1) l) := by
    cases l with
    | inl r =>
      rw [controlledLabelledLeft_pin_eq]
      exact qutritPinTensor_hasParity r
    | inr u => exact qutritNeqTensor_hasParity
  intro v
  cases v with
  | inl v => exact hleft (I.leftLabel v)
  | inr v => exact orderedControlledQutrit_hasParity f j

/-- The exact support flag for actual gadgets, independently of planarity and
connectedness. The latter properties enter only the realized-support sets. -/
theorem controlledAllLeft_support_flag {k a b c n : ℕ}
    (I : AllLeftGadget (starLanguageShape (k + 2)) a b c n)
    (f : BooleanTable k ℂ) (j : Fin k) (p : Fin n) :
    let T := I.value (controlledLabelledLanguage f j)
    (portFlatten T p).rank ≤ 2 ∧
    ((portFlatten T p).rank = 2 → columnSupport (portFlatten T p) = qutritCoordinatePlane 2) ∧
    ((portFlatten T p).rank = 1 → ∃ r : Fin 3,
      columnSupport (portFlatten T p) = qutritCoordinateRay r) := by
  let T := I.value (controlledLabelledLanguage f j)
  let A := portFlatten T p
  have hdim : Module.finrank ℂ (columnSupport A) = A.rank := rfl
  have hs := I.boundary_support_le (controlledLabelledLanguage f j) p
  rcases controlledLabelledLeft_support f j (I.leftLabel (I.boundaryVertex p))
      (I.boundaryPort p) with hp | ⟨r,hr⟩
  · have hsP : columnSupport A ≤ qutritCoordinatePlane (K := ℂ) 2 := by
      apply hs.trans
      simpa only [columnSupport, Matrix.range_mulVecLin] using le_of_eq hp
    have hle : A.rank ≤ 2 := by
      have h := Submodule.finrank_mono hsP
      rw [hdim, finrank_qutritCoordinatePlane] at h
      exact h
    refine ⟨hle,?_,?_⟩
    · intro h2
      apply Submodule.eq_of_le_of_finrank_eq hsP
      rw [hdim, finrank_qutritCoordinatePlane]
      exact h2
    · intro h1
      have hz : ∀ z, A 2 z = 0 := by
        intro z
        have hc : A.col z ∈ columnSupport A := by
          rw [columnSupport, Matrix.range_mulVecLin]
          exact Submodule.subset_span ⟨z,rfl⟩
        exact hsP hc
      obtain ⟨ε,hpar⟩ := controlledAllLeft_hasParity I f j
      rcases hpar.qutrit_support_le_endpoint p (le_of_eq h1) hz with h0 | h1'
      · exact ⟨0,support_eq_coordinateRay_of_le A 0 h0 h1⟩
      · exact ⟨1,support_eq_coordinateRay_of_le A 1 h1' h1⟩
  · have hsR : columnSupport A ≤ qutritCoordinateRay (K := ℂ) r := by
      apply hs.trans
      simpa only [columnSupport, Matrix.range_mulVecLin] using le_of_eq hr
    have hle : A.rank ≤ 1 := by
      have h := Submodule.finrank_mono hsR
      rw [hdim, qutritCoordinateRay_finrank] at h
      exact h
    refine ⟨hle.trans (by decide), ?_, ?_⟩
    · intro h2
      have he : A.rank = 2 := h2
      omega
    · intro h1
      exact ⟨r,support_eq_coordinateRay_of_le A r hsR h1⟩

/-- Every unary coordinate ray is realized by its actual single-vertex pin. -/
theorem controlledAllLeft_ray_mem {k : ℕ} (f : BooleanTable k ℂ) (j : Fin k) (r : Fin 3) :
    qutritCoordinateRay r ∈ allLeftRealizedSupports (controlledLabelledLanguage f j) 1 := by
  let l : (starLanguageShape (k + 2)).LeftLabel := Sum.inl r
  refine ⟨1,0,0,1,AllLeftGadget.primitive l, AllLeftGadget.primitive_connected l,
    AllLeftGadget.primitive_orderedPlanar_of_arity_le_two l (by norm_num [l,starLanguageShape]), ?_, 0, ?_,
    qutritCoordinateRay_finrank r⟩
  · rw [AllLeftGadget.primitive_value]
    intro h
    have he := congrFun h (fun _ => r)
    simp [l, controlledLabelledLanguage, coordinatePin] at he
  · rw [AllLeftGadget.primitive_value]
    simpa only [l, controlledLabelledLeft_pin_eq, columnSupport, Matrix.range_mulVecLin,
      qutritCoordinateRay] using (qutritPin_support (K := ℂ) r).symm

/-- The fixed plane is realized by the actual single-vertex disequality. -/
theorem controlledAllLeft_plane_mem {k : ℕ} (f : BooleanTable k ℂ) (j : Fin k) :
    qutritCoordinatePlane 2 ∈ allLeftRealizedSupports (controlledLabelledLanguage f j) 2 := by
  let l : (starLanguageShape (k + 2)).LeftLabel := Sum.inr 0
  refine ⟨1,0,0,2,AllLeftGadget.primitive l, AllLeftGadget.primitive_connected l,
    AllLeftGadget.primitive_orderedPlanar_of_arity_le_two l (by norm_num [l,starLanguageShape]), ?_, 0, ?_,
    finrank_qutritCoordinatePlane 2⟩
  · rw [AllLeftGadget.primitive_value]
    intro h
    have he := congrFun h ![0,1]
    simp [l, controlledLabelledLanguage, qutritNeqTensor] at he
  · rw [AllLeftGadget.primitive_value]
    simpa only [l, controlledLabelledLanguage, columnSupport, Matrix.range_mulVecLin] using
      (qutritNeq_support (K := ℂ) 0).symm

/-- The entire realized rank-two support set is literally one fixed plane. -/
theorem controlledAllLeft_planes {k : ℕ} (f : BooleanTable k ℂ) (j : Fin k) :
    allLeftRealizedSupports (controlledLabelledLanguage f j) 2 = {qutritCoordinatePlane 2} := by
  ext U
  constructor
  · rintro ⟨a,b,c,n,I,hconn,hplan,hne,p,hU,hd⟩
    have hr : (portFlatten (I.value (controlledLabelledLanguage f j)) p).rank = 2 := by
      rw [hU] at hd
      rw [Matrix.rank_eq_finrank_span_cols]
      letI : DecidableEq (Fin n) := instDecidableEqFin n
      unfold columnSupport at hd
      rw [Matrix.range_mulVecLin] at hd
      exact hd
    apply Set.mem_singleton_iff.mpr
    rw [hU]
    simpa only [columnSupport, Matrix.range_mulVecLin] using
      ((controlledAllLeft_support_flag I f j p).2.1 hr)
  · rintro rfl
    exact controlledAllLeft_plane_mem f j

/-- All three coordinate rays, and no others, are realized. -/
theorem controlledAllLeft_rays {k : ℕ} (f : BooleanTable k ℂ) (j : Fin k) :
    allLeftRealizedSupports (controlledLabelledLanguage f j) 1 =
      {qutritCoordinateRay 0, qutritCoordinateRay 1, qutritCoordinateRay 2} := by
  ext U
  constructor
  · rintro ⟨a,b,c,n,I,hconn,hplan,hne,p,hU,hd⟩
    have hr : (portFlatten (I.value (controlledLabelledLanguage f j)) p).rank = 1 := by
      rw [hU] at hd
      rw [Matrix.rank_eq_finrank_span_cols]
      letI : DecidableEq (Fin n) := instDecidableEqFin n
      unfold columnSupport at hd
      rw [Matrix.range_mulVecLin] at hd
      exact hd
    obtain ⟨r,hr⟩ := (controlledAllLeft_support_flag I f j p).2.2 hr
    have he : U = qutritCoordinateRay r := by
      rw [hU]
      simpa only [columnSupport, Matrix.range_mulVecLin] using hr
    rw [he]
    fin_cases r <;> simp
  · intro h
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
    rcases h with rfl | rfl | rfl <;> exact controlledAllLeft_ray_mem f j _

/-- The third ray is genuinely transverse to the fixed plane. -/
theorem controlled_coordinateRay_two_transverse :
    ¬ qutritCoordinateRay (K := ℂ) 2 ≤ qutritCoordinatePlane 2 := by
  intro h
  have hc : (Pi.single (2 : Fin 3) (1 : ℂ) : Fin 3 → ℂ) ∈ qutritCoordinateRay 2 := by
    apply Submodule.mem_span_singleton.mpr
    refine ⟨1,?_⟩
    ext i
    simp [Pi.single_apply]
  have he := h hc
  change (Pi.single 2 (1 : ℂ) : Fin 3 → ℂ) 2 = 0 at he
  simpa using he

/-- The complete source monomial flag, including actual primitive witnesses,
all connected planar closure supports, both displayed-base parity endpoints,
and transversality. -/
theorem controlled_actual_monomial_flag {k : ℕ} (f : BooleanTable k ℂ) (j : Fin k) :
    allLeftRealizedSupports (controlledLabelledLanguage f j) 2 = {qutritCoordinatePlane 2} ∧
    allLeftRealizedSupports (controlledLabelledLanguage f j) 1 =
      {primitiveParityEndpoint (controlledLabelledBase k) (qutritCoordinatePlane 2) 0,
       primitiveParityEndpoint (controlledLabelledBase k) (qutritCoordinatePlane 2) 1,
       qutritCoordinateRay 2} ∧
    ¬ qutritCoordinateRay (K := ℂ) 2 ≤ qutritCoordinatePlane 2 := by
  rw [(controlled_flag_parity_endpoints k).1, (controlled_flag_parity_endpoints k).2]
  exact ⟨controlledAllLeft_planes f j,controlledAllLeft_rays f j,
    controlled_coordinateRay_two_transverse⟩

end
end MatchgateWidth
