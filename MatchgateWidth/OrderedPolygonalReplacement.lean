import MatchgateWidth.RadialPolygonalReplacement
import MatchgateWidth.PolygonalPortOrderTransport
import MatchgateWidth.OrderedGadgetBoundaryCollars

/-! # Actual polygonal drawing replacement for ordered all-left gadgets
The graph, incidence bijections, boundary labels, and marked local port times
are fixed. Only geometric coordinates and arc parametrizations are replaced.
-/
namespace MatchgateWidth
noncomputable section
namespace AllLeftGadget
variable {S : LabelledShape} {a b c n : ℕ} {I : AllLeftGadget S a b c n}
namespace OrderedPlanar

/-- Positive radial rescaling preserves every actual marked local port order. -/
theorem exists_ordered_of_radial_replacement (P : I.OrderedPlanar)
    (R : P.drawing.RadialPolygonalReplacement) :
    ∃ Q : I.OrderedPlanar, Q.drawing = R.drawing ∧
      (∀ v, (Q.leftOrder v).time = (P.leftOrder v).time) ∧
      (∀ v, (Q.rightOrder v).time = (P.rightOrder v).time) := by
  classical
  have hleft (v : Fin a) : ∃ O : LabelledInstance.PositivePortOrder
      (R.drawing.vertex (Sum.inl (Sum.inl v)))
      (fun i t => R.drawing.edge (I.leftIncidence ⟨v,i⟩) t),
      O.rotation=(P.leftOrder v).rotation ∧ O.time=(P.leftOrder v).time := by
    apply (P.leftOrder v).exists_of_positive_germs
    intro i
    have hg := R.source_germ (I.leftIncidence ⟨v,i⟩)
      (P.leftOrder v).radius (P.leftOrder v).radius_pos
      ((P.leftOrder v).speed i • ((P.leftOrder v).rotation * twoCenterSquare ((P.leftOrder v).time i)))
      (fun t ht => by simpa [AllLeftGadget.graph] using (P.leftOrder v).germ i t ht)
    obtain ⟨κ,hκ,ρ,hρ,hg⟩ := hg
    refine ⟨κ,hκ,ρ,hρ,?_⟩
    intro t ht
    change R.stem.path (I.leftIncidence ⟨v,i⟩) t = _
    simpa [AllLeftGadget.graph] using hg t ht
  have hright (v : Fin b) : ∃ O : LabelledInstance.PositivePortOrder
      (R.drawing.vertex (Sum.inl (Sum.inr v)))
      (fun i t => R.drawing.edge (Sum.inl (I.rightIncidence ⟨v,i⟩))
        (LabelledInstance.reverseParameter t)),
      O.rotation=(P.rightOrder v).rotation ∧ O.time=(P.rightOrder v).time := by
    apply (P.rightOrder v).exists_of_positive_germs
    intro i
    have hg := R.target_germ (Sum.inl (I.rightIncidence ⟨v,i⟩))
      (P.rightOrder v).radius (P.rightOrder v).radius_pos
      ((P.rightOrder v).speed i • ((P.rightOrder v).rotation * twoCenterSquare ((P.rightOrder v).time i)))
      (fun t ht => by
        change P.drawing.edge (Sum.inl (I.rightIncidence ⟨v,i⟩))
          (LabelledInstance.reverseParameter t) = _
        simpa [AllLeftGadget.graph] using (P.rightOrder v).germ i t ht)
    obtain ⟨κ,hκ,ρ,hρ,hg⟩ := hg
    refine ⟨κ,hκ,ρ,hρ,?_⟩
    intro t ht
    change (R.stem.path (Sum.inl (I.rightIncidence ⟨v,i⟩))).symm t = _
    simpa [AllLeftGadget.graph] using hg t ht
  choose OL hOL using hleft
  choose OR hOR using hright
  exact ⟨⟨R.drawing,OL,OR⟩,rfl,fun v => (hOL v).2,fun v => (hOR v).2⟩

/-- Every actual ordered all-left gadget has a simple finite polygonal drawing
on exactly the same abstract ordered graph. Primitive vertices lie strictly
inside the disk, all original boundary labels retain their angles, and each
local marked port time is retained. This is a proved geometric replacement,
not a hypothesis about substituted matchgates. -/
theorem exists_polygonal_ordered_drawing (P : I.OrderedPlanar) :
    ∃ Q : I.OrderedPlanar,
      (∀ e, IsPolygonalPath (Q.drawing.edgePath e)) ∧
      (∀ v : Fin a ⊕ Fin b, ‖Q.drawing.vertex (Sum.inl v)‖≤1/2) ∧
      Q.drawing.angle=P.drawing.angle ∧
      (∀ v, (Q.leftOrder v).time=(P.leftOrder v).time) ∧
      (∀ v, (Q.rightOrder v).time=(P.rightOrder v).time) := by
  obtain ⟨R⟩ := P.boundaryCollarDrawing.exists_radial_polygonal_replacement
    P.boundaryCollarDrawing_edge_interior P.boundaryCollarDrawing_initial_germ
    (fun e => by simpa [PlanarDrawing.edgePath,Path.symm_apply,
      LabelledInstance.reverseParameter,unitInterval.symm] using
        P.boundaryCollarDrawing_terminal_germ e)
  obtain ⟨Q,hQD,hQL,hQR⟩ := P.boundaryCollarOrderedPlanar.exists_ordered_of_radial_replacement R
  refine ⟨Q,?_,?_,?_,?_,?_⟩
  · intro e
    rw [hQD]
    exact R.stem.polygonal e
  · intro v
    rw [hQD]
    exact P.boundaryCollarDrawing_primitive_bound v
  · rw [hQD]
    rfl
  · intro v
    exact (hQL v).trans (P.boundaryCollarOrderedPlanar_left_time v)
  · intro v
    exact (hQR v).trans (P.boundaryCollarOrderedPlanar_right_time v)

/-- Strengthened polygonal normalization retains strict disk-interior edges
and genuine inward radial germs at every original boundary label. -/
theorem exists_polygonal_ordered_drawing_with_boundary_germs (P : I.OrderedPlanar) :
    ∃ Q : I.OrderedPlanar,
      (∀ e, IsPolygonalPath (Q.drawing.edgePath e)) ∧
      (∀ e t, 0<t → t<1 → ‖Q.drawing.edge e t‖<1) ∧
      (∀ v : Fin a ⊕ Fin b, ‖Q.drawing.vertex (Sum.inl v)‖≤1/2) ∧
      Q.drawing.angle=P.drawing.angle ∧
      (∀ v, (Q.leftOrder v).time=(P.leftOrder v).time) ∧
      (∀ v, (Q.rightOrder v).time=(P.rightOrder v).time) ∧
      (∀ p : Fin n, ∃ κ : ℝ, 0<κ ∧ ∃ ρ : unitInterval, 0<ρ ∧
        ∀ t : unitInterval, t≤ρ →
          Q.drawing.edge (Sum.inr p) (LabelledInstance.reverseParameter t) =
            boundaryPoint (Q.drawing.angle p) +
              (t:ℝ) • (κ • (-boundaryPoint (Q.drawing.angle p)))) := by
  obtain ⟨R⟩ := P.boundaryCollarDrawing.exists_radial_polygonal_replacement
    P.boundaryCollarDrawing_edge_interior P.boundaryCollarDrawing_initial_germ
    (fun e => by simpa [PlanarDrawing.edgePath,Path.symm_apply,
      LabelledInstance.reverseParameter,unitInterval.symm] using
        P.boundaryCollarDrawing_terminal_germ e)
  obtain ⟨Q,hQD,hQL,hQR⟩ := P.boundaryCollarOrderedPlanar.exists_ordered_of_radial_replacement R
  refine ⟨Q,?_,?_,?_,?_,?_,?_,?_⟩
  · intro e
    rw [hQD]
    exact R.stem.polygonal e
  · intro e t ht0 ht1
    rw [hQD]
    exact R.stem.interior_in_disk e t ht0 ht1
  · intro v
    rw [hQD]
    exact P.boundaryCollarDrawing_primitive_bound v
  · rw [hQD]
    rfl
  · intro v
    exact (hQL v).trans (P.boundaryCollarOrderedPlanar_left_time v)
  · intro v
    exact (hQR v).trans (P.boundaryCollarOrderedPlanar_right_time v)
  · intro p
    have hg := R.target_germ (Sum.inr p) ⟨1/2,by constructor <;> norm_num⟩
      (by change (0:ℝ)<1/2; norm_num) (-boundaryPoint (P.drawing.angle p))
      (fun t ht => by
        change P.boundaryCollarDrawing.edge (Sum.inr p) (LabelledInstance.reverseParameter t) = _
        simp only [AllLeftGadget.graph,Sum.elim_inr]
        rw [P.boundaryCollarDrawing.external_vertex]
        exact P.boundaryCollarDrawing_boundary_reverse_germ p t ht)
    obtain ⟨κ,hκ,ρ,hρ,hg⟩ := hg
    refine ⟨κ,hκ,ρ,hρ,?_⟩
    intro t ht
    rw [hQD]
    change (R.stem.path (Sum.inr p)).symm t = _
    have hh := hg t ht
    simp only [AllLeftGadget.graph,Sum.elim_inr] at hh
    calc
      (R.stem.path (Sum.inr p)).symm t = P.boundaryCollarDrawing.vertex (Sum.inr p) +
          (t:ℝ) • (κ • (-boundaryPoint (P.drawing.angle p))) := hh
      _ = _ := by rw [P.boundaryCollarDrawing.external_vertex]; rfl

end OrderedPlanar
end AllLeftGadget
end
end MatchgateWidth
