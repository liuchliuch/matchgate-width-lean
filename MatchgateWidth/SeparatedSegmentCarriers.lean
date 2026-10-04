import MatchgateWidth.PolygonalRibbonAssembly

/-! # Disjoint open carriers for nonadjacent polygon segments -/
namespace MatchgateWidth
noncomputable section
open Set Metric

/-- Finite compact sets need be separated only for the designated pairs.
Adjacent polygon edges can retain their common endpoint. -/
theorem finite_compact_related_open_neighborhoods {ι : Type*} [Finite ι]
    (Rel : ι → ι → Prop) (S O : ι → Set ℂ)
    (hS : ∀ i, IsCompact (S i))
    (hdis : ∀ i j, Rel i j → Disjoint (S i) (S j))
    (hO : ∀ i, IsOpen (O i)) (hSO : ∀ i, S i ⊆ O i) :
    ∃ U : ι → Set ℂ, (∀ i, IsOpen (U i)) ∧ (∀ i, S i ⊆ U i) ∧
      (∀ i, U i ⊆ O i) ∧ ∀ i j, Rel i j → Disjoint (U i) (U j) := by
  classical
  have hex (i j : ι) : ∃ δ : ℝ, 0 < δ ∧
      (Rel i j → Disjoint (thickening δ (S i)) (thickening δ (S j))) := by
    by_cases hij : Rel i j
    · obtain ⟨δ,hδ,hd⟩ := (hdis i j hij).exists_thickenings (hS i) (hS j).isClosed
      exact ⟨δ,hδ,fun _ => hd⟩
    · exact ⟨1,by norm_num,fun h => (hij h).elim⟩
  choose δ hδ hd using hex
  let U : ι → Set ℂ := fun i => O i ∩
    ⋂ j, (thickening (δ i j) (S i) ∩ thickening (δ j i) (S i))
  refine ⟨U,?_,?_,?_,?_⟩
  · intro i
    exact (hO i).inter (isOpen_iInter_of_finite fun j => isOpen_thickening.inter isOpen_thickening)
  · intro i x hx
    exact ⟨hSO i hx,mem_iInter.mpr fun j =>
      ⟨self_subset_thickening (hδ i j) (S i) hx,
       self_subset_thickening (hδ j i) (S i) hx⟩⟩
  · intro i x hx
    exact hx.1
  · intro i j hij
    exact (hd i j hij).mono
      (fun x hx => (mem_iInter.mp hx.2 j).1)
      (fun x hx => (mem_iInter.mp hx.2 i).2)

/-- A simple polygon's nonadjacent segment separation, together with genuine
positive transverse sections, yields all route data needed for parallel wires.
Open obstacle-avoiding carriers may be assigned separately to every segment. -/
theorem exists_transversePolygonalRoute {n : ℕ}
    (p w : Fin (n+1) → ℂ) (O : Fin n → Set ℂ)
    (hO : ∀ i, IsOpen (O i))
    (hcenter : ∀ i, Set.range (straightArc (p i.castSucc) (p i.succ)) ⊆ O i)
    (hdis : ∀ i j : Fin n, i.val + 1 < j.val ∨ j.val + 1 < i.val →
      Disjoint (Set.range (straightArc (p i.castSucc) (p i.succ)))
        (Set.range (straightArc (p j.castSucc) (p j.succ))))
    (hstart : ∀ i : Fin n, 0 < orientedArea (p i.succ-p i.castSucc) (w i.castSucc))
    (hend : ∀ i : Fin n, 0 < orientedArea (p i.succ-p i.castSucc) (w i.succ)) :
    ∃ R : TransversePolygonalRoute n, R.vertex = p ∧ R.transverse = w ∧
      ∀ i, R.carrier i ⊆ O i := by
  obtain ⟨U,hU,hSU,hUO,hdU⟩ := finite_compact_related_open_neighborhoods
    (fun i j : Fin n => i.val + 1 < j.val ∨ j.val + 1 < i.val)
    (fun i => Set.range (straightArc (p i.castSucc) (p i.succ))) O
    (fun i => isCompact_range (continuous_straightArc _ _)) hdis hO hcenter
  exact ⟨⟨p,w,U,hU,hSU,hdU,hstart,hend⟩,rfl,rfl,hUO⟩

end
end MatchgateWidth
