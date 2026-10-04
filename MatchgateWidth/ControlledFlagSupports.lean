import MatchgateWidth.ParitySupportLines

/-! # Exact flag placement for every properly wired all-left controlled gadget
This proof uses actual finite network semantics, boundary support monotonicity,
and the directly proved domain marker-parity invariant. It does not assume a
Boolean gadget-lifting theorem.
-/
namespace MatchgateWidth
noncomputable section
open scoped Classical
variable {K : Type*} [Field K] {k : ℕ}

/-- The three fixed coordinate rays of the constructed qutrit language. -/
def qutritCoordinateRay (r : Fin 3) : Submodule K (Fin 3 → K) := K ∙ Pi.single r 1

theorem qutritCoordinateRay_finrank (r : Fin 3) :
    Module.finrank K (qutritCoordinateRay (K := K) r) = 1 := by
  apply finrank_span_singleton
  intro h
  have hh := congrFun h r
  simpa using hh

theorem support_eq_coordinateRay_of_le {C : Type*} [Fintype C]
    (A : Matrix (Fin 3) C K) (r : Fin 3)
    (hle : columnSupport A ≤ qutritCoordinateRay r) (hr : A.rank = 1) :
    columnSupport A = qutritCoordinateRay r := by
  apply Submodule.eq_of_le_of_finrank_eq hle
  change A.rank = _
  rw [hr, qutritCoordinateRay_finrank]

/-- Each primitive left support is the fixed plane or a fixed coordinate ray. -/
theorem controlledLeft_primitive_support (f : BooleanTable k K) (j : Fin k)
    (l : ControlledLanguageLabel) (hl : l ≠ .controlled)
    (p : controlledLanguagePorts k l) :
    columnSupport (portFlatten (controlledLanguageTensor f j l) p) = qutritCoordinatePlane 2 ∨
    ∃ r, columnSupport (portFlatten (controlledLanguageTensor f j l) p) = qutritCoordinateRay r := by
  cases l with
  | pin r =>
    right
    have hp : p = 0 := Subsingleton.elim _ _
    subst p
    exact ⟨r,qutritPin_support r⟩
  | neq => exact Or.inl (qutritNeq_support p)
  | controlled => exact (hl rfl).elim

/-- The exact per-port flag restriction for an actual network, including
nonplanar ones. All-left planar source gadgets are a subclass. -/
theorem controlled_network_support_flag {V E P : Type*}
    [Fintype V] [Fintype E] [Fintype P]
    (labels : V → ControlledLanguageLabel)
    (inc : ∀ v, controlledLanguagePorts k (labels v) → E ⊕ P)
    (hinc : ProperNetworkIncidences inc) (f : BooleanTable k K) (j : Fin k)
    (p : P)
    (hleft : ∀ v i, inc v i = Sum.inr p → labels v ≠ .controlled) :
    let T := networkValue inc (fun v => controlledLanguageTensor f j (labels v))
    (portFlatten T p).rank ≤ 2 ∧
    ((portFlatten T p).rank = 2 → columnSupport (portFlatten T p) = qutritCoordinatePlane 2) ∧
    ((portFlatten T p).rank = 1 → ∃ r : Fin 3,
      columnSupport (portFlatten T p) = qutritCoordinateRay r) := by
  let T := networkValue inc (fun v => controlledLanguageTensor f j (labels v))
  let A := portFlatten T p
  have hdim : Module.finrank K (columnSupport A) = A.rank := by rfl
  obtain ⟨a,ha⟩ := Finset.card_eq_one.mp (hinc.2 p)
  have hincident : inc a.1 a.2 = Sum.inr p := by
    have hm : a ∈ Finset.univ.filter (fun z => inc z.1 z.2 = Sum.inr p) := by rw [ha]; simp
    exact (Finset.mem_filter.mp hm).2
  have hunique : ∀ v i, inc v i = Sum.inr p →
      (⟨v,i⟩ : Sigma (fun v => controlledLanguagePorts k (labels v))) = a := by
    intro v i hi
    have hm : (⟨v,i⟩ : Sigma (fun v => controlledLanguagePorts k (labels v))) ∈
        Finset.univ.filter (fun z => inc z.1 z.2 = Sum.inr p) := by simp [hi]
    rw [ha] at hm
    exact Finset.mem_singleton.mp hm
  have hs := network_boundary_support_le_of_unique_incidence inc
    (fun v => controlledLanguageTensor f j (labels v)) a.1 a.2 p hincident hunique
  rcases controlledLeft_primitive_support f j (labels a.1) (hleft _ _ hincident) a.2 with hp | ⟨r,hr⟩
  · have hsP : columnSupport A ≤ qutritCoordinatePlane (K := K) 2 := by
      apply hs.trans
      simpa only [columnSupport, Matrix.range_mulVecLin] using le_of_eq hp
    clear hs
    have hs := hsP
    have hle : A.rank ≤ 2 := by
      have h := Submodule.finrank_mono hs
      rw [hdim, finrank_qutritCoordinatePlane] at h
      exact h
    refine ⟨hle,?_,?_⟩
    · intro h2
      apply Submodule.eq_of_le_of_finrank_eq hs
      rw [hdim, finrank_qutritCoordinatePlane]
      exact h2
    · intro h1
      have hz : ∀ b, A 2 b = 0 := by
        intro b
        have hc : A.col b ∈ columnSupport A := by
          rw [columnSupport, Matrix.range_mulVecLin]
          exact Submodule.subset_span ⟨b,rfl⟩
        exact hs hc
      have hpar := controlled_network_hasParity labels inc hinc f j
      rcases hpar.qutrit_support_le_endpoint p (le_of_eq h1) hz with h0 | h1'
      · exact ⟨0,support_eq_coordinateRay_of_le A 0 h0 h1⟩
      · exact ⟨1,support_eq_coordinateRay_of_le A 1 h1' h1⟩
  · have hsR : columnSupport A ≤ qutritCoordinateRay (K := K) r := by
      apply hs.trans
      simpa only [columnSupport, Matrix.range_mulVecLin] using le_of_eq hr
    clear hs
    have hs := hsR
    have hle : A.rank ≤ 1 := by
      have h := Submodule.finrank_mono hs
      rw [hdim, qutritCoordinateRay_finrank] at h
      exact h
    refine ⟨hle.trans (by decide), ?_, ?_⟩
    · intro h2
      have : 2 ≤ 1 := h2 ▸ hle
      omega
    · intro h1
      exact ⟨r,support_eq_coordinateRay_of_le A r hs h1⟩

end
end MatchgateWidth
