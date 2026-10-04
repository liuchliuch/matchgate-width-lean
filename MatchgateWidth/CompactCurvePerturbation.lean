import MatchgateWidth.SeparatedSegmentCarriers

/-! # Uniform preservation of geometric carriers under small perturbations

Continuity is required only at the compact zero-parameter trace. The tube
lemma then gives one two-sided parameter interval preserving the whole curve.
Finite families admit one common interval, and designated disjoint trace pairs
remain disjoint after independently chosen small parameter perturbations.
-/
namespace MatchgateWidth
noncomputable section
open Set Filter Topology

/-- A compact continuously varying curve stays in any open carrier of its
zero-parameter trace, uniformly over all points of the curve. Continuity away
from parameter zero is not assumed. -/
theorem compact_curve_perturbation_radius {T : Type*} [TopologicalSpace T] [CompactSpace T]
    (f : ℝ → T → ℂ) (hf : ∀ t, ContinuousAt (fun q : ℝ × T => f q.1 q.2) (0,t))
    {U : Set ℂ} (hU : IsOpen U) (h0 : Set.range (f 0) ⊆ U) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ δ : ℝ, |δ| < ε → Set.range (f δ) ⊆ U := by
  classical
  have hN (t : T) : ∃ N : Set (ℝ × T), N ⊆ (fun q => f q.1 q.2) ⁻¹' U ∧
      IsOpen N ∧ (0,t) ∈ N := by
    exact mem_nhds_iff.mp ((hf t).preimage_mem_nhds (hU.mem_nhds (h0 ⟨t,rfl⟩)))
  choose N hNU hNo hNt using hN
  let W : Set (ℝ × T) := ⋃ t, N t
  have hWo : IsOpen W := isOpen_iUnion hNo
  have hbase : ({0} : Set ℝ) ×ˢ (Set.univ : Set T) ⊆ W := by
    rintro ⟨δ,t⟩ ⟨hδ,ht⟩
    have hd : δ = 0 := hδ
    subst δ
    exact Set.mem_iUnion.mpr ⟨t,hNt t⟩
  obtain ⟨A,B,hAo,hBo,hA,hB,hAB⟩ := generalized_tube_lemma
    (isCompact_singleton : IsCompact ({0} : Set ℝ)) isCompact_univ hWo hbase
  obtain ⟨ε,hε,he⟩ := Metric.isOpen_iff.mp hAo 0 (hA (by simp))
  refine ⟨ε,hε,?_⟩
  intro δ hδ z hz
  obtain ⟨t,rfl⟩ := hz
  have hδA : δ ∈ A := he (by simpa [Metric.mem_ball,Real.dist_eq] using hδ)
  have hpair : (δ,t) ∈ W := hAB ⟨hδA,hB (Set.mem_univ t)⟩
  obtain ⟨u,hu⟩ := Set.mem_iUnion.mp hpair
  exact hNU u hu

/-- One common perturbation interval works simultaneously for a finite family
of local curve stages and their separate designated carriers. -/
theorem finite_compact_curve_perturbation_radius {I T : Type*} [Fintype I]
    [TopologicalSpace T] [CompactSpace T]
    (f : I → ℝ → T → ℂ)
    (hf : ∀ i t, ContinuousAt (fun q : ℝ × T => f i q.1 q.2) (0,t))
    (U : I → Set ℂ) (hU : ∀ i, IsOpen (U i))
    (h0 : ∀ i, Set.range (f i 0) ⊆ U i) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ i δ, |δ| < ε → Set.range (f i δ) ⊆ U i := by
  classical
  choose ε hε hspec using fun i => compact_curve_perturbation_radius (f i) (hf i) (hU i) (h0 i)
  cases isEmpty_or_nonempty I with
  | inl hempty => exact ⟨1,by norm_num,fun i => isEmptyElim i⟩
  | inr hne =>
    obtain ⟨i,hi,hmin⟩ := Finset.exists_min_image Finset.univ ε Finset.univ_nonempty
    exact ⟨ε i,hε i,fun j δ hδ => hspec j δ (hδ.trans_le (hmin j (Finset.mem_univ j)))⟩

/-- Nonincident compact curve traces remain disjoint under all sufficiently
small independent perturbations. Only the specified relation of disjoint pairs
is constrained; intended local endpoint joins can be excluded from `Rel`. -/
theorem finite_related_curve_perturbations_disjoint {I T : Type*} [Fintype I]
    [TopologicalSpace T] [CompactSpace T]
    (Rel : I → I → Prop) (f : I → ℝ → T → ℂ)
    (hbase : ∀ i, Continuous (f i 0))
    (hf : ∀ i t, ContinuousAt (fun q : ℝ × T => f i q.1 q.2) (0,t))
    (hdis : ∀ i j, Rel i j → Disjoint (Set.range (f i 0)) (Set.range (f j 0)))
    (O : I → Set ℂ) (hO : ∀ i, IsOpen (O i))
    (h0 : ∀ i, Set.range (f i 0) ⊆ O i) :
    ∃ ε : ℝ, 0 < ε ∧ (∀ i δ, |δ| < ε → Set.range (f i δ) ⊆ O i) ∧
      ∀ i j, Rel i j → ∀ δ η : ℝ, |δ| < ε → |η| < ε →
        Disjoint (Set.range (f i δ)) (Set.range (f j η)) := by
  obtain ⟨U,hU,hSU,hUO,hdU⟩ := finite_compact_related_open_neighborhoods Rel
    (fun i => Set.range (f i 0)) O (fun i => isCompact_range (hbase i)) hdis hO h0
  obtain ⟨ε,hε,hεspec⟩ := finite_compact_curve_perturbation_radius f hf U hU hSU
  refine ⟨ε,hε,?_,?_⟩
  · intro i δ hδ
    exact (hεspec i δ hδ).trans (hUO i)
  · intro i j hij δ η hδ hη
    exact (hdU i j hij).mono (hεspec i δ hδ) (hεspec j η hη)

end
end MatchgateWidth
