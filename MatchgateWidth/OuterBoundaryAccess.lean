import MatchgateWidth.RadialTangentCaps
import MatchgateWidth.AnnularRouting

/-! # Outward radial boundary access after the last polygonal ribbon segment -/
namespace MatchgateWidth
noncomputable section

/-- The outward cap is traversed toward the common surrounding circle.
The displayed cap itself is reversed here only to reuse its exact formula. -/
theorem ribbon_outerRadialCap_eq_iff (c p q u v : ℂ) (δ η α : ℝ)
    (hα : 1 < α) (hcap : 0 < orientedArea (q-c) v)
    (hwire : 0 < orientedArea (ribbonDirection p q u v δ) v)
    (s t : unitInterval) :
    ribbonArc p q u v δ s = radialSectionCap c q v η α t ↔
      s=1 ∧ t=1 ∧ δ=η := by
  constructor
  · intro h
    have he := congrArg (fun z => orientedArea v (z-q)) h
    rw [ribbonArc_before_area,radialSectionCap_area] at he
    have hmul : 0 < (α-1)*orientedArea (q-c) v := mul_pos (sub_pos.mpr hα) hcap
    have hnn : 0 ≤ (1-(s:ℝ))*orientedArea (ribbonDirection p q u v δ) v :=
      mul_nonneg (sub_nonneg.mpr s.property.2) hwire.le
    have ht1 : (t:ℝ)=1 := by nlinarith [t.property.1,t.property.2]
    have hs1 : (s:ℝ)=1 := by rw [ht1] at he; nlinarith
    have hs : s=1 := Subtype.ext hs1
    have ht : t=1 := Subtype.ext ht1
    subst s
    subst t
    simp only [radialSectionCap_one,ribbonArc_one,ribbonSection,add_right_inj] at h
    have hv : v ≠ 0 := by intro hz; simp [hz] at hcap
    exact ⟨rfl,rfl,smul_left_injective ℝ hv h⟩
  · rintro ⟨rfl,rfl,rfl⟩
    simp

theorem outerRadialSectionCap_injective (c p w : ℂ) (δ α : ℝ) (hα : 1<α)
    (hpoint : ribbonSection p w δ ≠ c) : Function.Injective (radialSectionCap c p w δ α) := by
  apply straightArc_injective
  intro h
  have hs : α • (ribbonSection p w δ-c) = (1:ℝ) • (ribbonSection p w δ-c) := by
    simpa only [one_smul,eq_sub_iff_add_eq,add_comm] using h
  exact (ne_of_gt hα) (smul_left_injective ℝ (sub_ne_zero.mpr hpoint) hs)

/-- Distinct angular rays remain disjoint for arbitrary positive starting
radii, and can all terminate on the same outer circle. -/
theorem outerRadialAccess_disjoint {n : ℕ} (c : ℂ) (R : ℝ) (ρ θ : Fin n → ℝ)
    (hρ : ∀ i, 0<ρ i) (hR : ∀ i, ρ i<R)
    (hθ : StrictMono θ) (hθ0 : ∀ i, 0<θ i) (hθ1 : ∀ i, θ i<1) :
    Pairwise (fun i j => Disjoint
      (Set.range (annularConnector c (ρ i) R (θ i) (θ i)))
      (Set.range (annularConnector c (ρ j) R (θ j) (θ j)))) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  rintro z ⟨t,rfl⟩ ⟨u,hu⟩
  have hr := congrArg (fun z => ‖z-c‖) hu
  rw [annularConnector_norm c (hρ j) ((hρ j).trans (hR j)),
    annularConnector_norm c (hρ i) ((hρ i).trans (hR i))] at hr
  have hz : ((affineBlend (ρ i) R t : ℝ):ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (affineBlend_pos (hρ i) ((hρ i).trans (hR i)) t))
  have hsame (a : ℝ) (s : unitInterval) : affineBlend a a s = a := by unfold affineBlend; ring
  change c+((affineBlend (ρ j) R u : ℝ):ℂ)*boundaryPoint _ =
    c+((affineBlend (ρ i) R t : ℝ):ℂ)*boundaryPoint _ at hu
  rw [hr,hsame,hsame] at hu
  have he := mul_left_cancel₀ hz (add_left_cancel hu)
  have ha := boundaryPoint_inj_on_turn (hθ0 j) (hθ1 j) (hθ0 i) (hθ1 i) he
  exact hij (hθ.injective ha).symm

end
end MatchgateWidth
