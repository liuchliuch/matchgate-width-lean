import MatchgateWidth.LocalConnectorBank
import MatchgateWidth.RadialTangentCaps

/-! # Whole variable-radius local connectors meet only their adjoining lanes

A connector first remains in a small inner ball, then follows the exact ray
through its endpoint. The inner ball is separated by the corridor carrier;
the radial portion is separated by the proved oriented-area formula. This
combines the two actual stages, rather than treating an entire variable-annulus
connector as if it were radial.
-/
namespace MatchgateWidth
noncomputable section
open Filter Topology

/-- A geometric head/tail decomposition with a fixed ball and the actual
terminal ray. No ribbon intersection property is included. -/
def RadialTailProperty (f : unitInterval → ℂ) (c endpoint : ℂ) (S : ℝ) : Prop :=
  ∀ t, dist (f t) c ≤ S ∨ ∃ β : ℝ, 0 ≤ β ∧ β ≤ 1 ∧ f t = c + β • endpoint

/-- A complete local connector and the first ribbon segment meet only at the
same lane endpoint. The angular head is excluded using the corridor's ball
avoidance, while the radial tail is handled algebraically. -/
theorem radialTail_connector_ribbon_eq_iff (c p q w v x : ℂ) (δ η S : ℝ)
    (C : Path x (ribbonSection (c+p) w δ)) (hC : Function.Injective C)
    (htail : RadialTailProperty C c (ribbonSection (c+p) w δ-c) S)
    (hhead : Disjoint (Set.range (ribbonArc (c+p) q w v η)) (Metric.closedBall c S))
    (hcap : 0 < orientedArea p w)
    (hwire : 0 < orientedArea (ribbonDirection (c+p) q w v η) w)
    (s t : unitInterval) :
    C s = ribbonArc (c+p) q w v η t ↔ s = 1 ∧ t = 0 ∧ δ = η := by
  constructor
  · intro he
    rcases htail s with hh | ⟨β,hβ0,hβ1,hβ⟩
    · exact (Set.disjoint_left.mp hhead ⟨t,rfl⟩ (he ▸ hh)).elim
    · have ha := congrArg (fun z => orientedArea w (z-(c+p))) he
      rw [hβ,radialSection_point_area,ribbonArc_after_area] at ha
      simp only [add_sub_cancel_left] at ha
      have hnn : 0 ≤ (1-β)*orientedArea p w := mul_nonneg (sub_nonneg.mpr hβ1) hcap.le
      have ht0 : (t : ℝ) = 0 := by nlinarith [t.property.1]
      have hβeq : β = 1 := by rw [ht0] at ha; nlinarith
      have ht : t = 0 := Subtype.ext ht0
      have hs : s = 1 := by
        apply hC
        rw [hβ,hβeq,one_smul,add_sub_cancel,(C.target)]
      subst s
      subst t
      have hw : w ≠ 0 := by intro hz; simp [hz] at hcap
      have hsm : δ • w = η • w := by
        rw [C.target] at he
        simpa only [ribbonArc_zero,ribbonSection,add_right_inj] using he
      exact ⟨rfl,rfl,smul_left_injective ℝ hw hsm⟩
  · rintro ⟨rfl,rfl,rfl⟩
    simp

/-- The corresponding complete connector at the incoming end of a ribbon.
Its traversal is reversed when forming the final bridge path. -/
theorem ribbon_radialTail_connector_eq_iff (c p q u v x : ℂ) (δ η S : ℝ)
    (C : Path x (ribbonSection q v η)) (hC : Function.Injective C)
    (htail : RadialTailProperty C c (ribbonSection q v η-c) S)
    (hhead : Disjoint (Set.range (ribbonArc p q u v δ)) (Metric.closedBall c S))
    (hcap : 0 < orientedArea (c-q) v)
    (hwire : 0 < orientedArea (ribbonDirection p q u v δ) v)
    (s t : unitInterval) :
    ribbonArc p q u v δ s = C t ↔ s = 1 ∧ t = 1 ∧ δ = η := by
  constructor
  · intro he
    rcases htail t with hh | ⟨β,hβ0,hβ1,hβ⟩
    · exact (Set.disjoint_left.mp hhead ⟨s,rfl⟩ (he.symm ▸ hh)).elim
    · have ha := congrArg (fun z => orientedArea v (z-q)) he
      rw [hβ,ribbonArc_before_area,radialSection_point_area] at ha
      have hsign : orientedArea (q-c) v = -orientedArea (c-q) v := by simp [orientedArea]; ring
      rw [hsign] at ha
      have hnn : 0 ≤ (1-(s : ℝ))*orientedArea (ribbonDirection p q u v δ) v :=
        mul_nonneg (sub_nonneg.mpr s.property.2) hwire.le
      have hβeq : β = 1 := by nlinarith
      have hs1 : (s : ℝ) = 1 := by rw [hβeq] at ha; nlinarith
      have hs : s = 1 := Subtype.ext hs1
      have ht : t = 1 := by
        apply hC
        rw [hβ,hβeq,one_smul,add_sub_cancel,C.target]
      subst s
      subst t
      have hv : v ≠ 0 := by intro hz; simp [hz] at hcap
      have hsm : δ • v = η • v := by
        rw [C.target] at he
        simpa only [ribbonArc_one,ribbonSection,add_right_inj] using he
      exact ⟨rfl,rfl,smul_left_injective ℝ hv hsm⟩
  · rintro ⟨rfl,rfl,rfl⟩
    simp

namespace OrderedRayAngles
variable {n r : ℕ} {p : Fin n → ℂ} (A : OrderedRayAngles p)

/-- The explicit local connector bank has exactly the required head/tail
property, in its genuine physical frame and radius. -/
theorem localBlockConnector_radialTail (c : ℂ) (w : Fin n → ℂ)
    (d : Fin n → Fin r → ℝ) (α : Fin (n*r) → ℝ) (R S ε : ℝ)
    (hR : 0 < R) (hRS : R < S) (hρ : ∀ q, S ≤ A.blockRadius w d ε q)
    (hden : ∀ i k, 0 < 1+(ε*d i k)*(w i/p i).re) (q : Fin (n*r)) :
    RadialTailProperty (A.localBlockConnector c w d α R S ε q)
      c (A.blockEndpoint w d ε q) (‖A.rotation‖*S) := by
  intro t
  by_cases ht : affineBlend R (A.blockRadius w d ε q) t ≤ S
  · left
    rw [A.localBlockConnector_norm c w d α R S ε hR hRS hρ]
    exact mul_le_mul_of_nonneg_left ht (norm_nonneg A.rotation)
  · right
    let β := affineBlend R (A.blockRadius w d ε q) t / A.blockRadius w d ε q
    have hρpos : 0 < A.blockRadius w d ε q := (hR.trans hRS).trans_le (hρ q)
    have hb := (variableAnnularConnector_bounds 0 hR hRS (hρ q) (α q)
      (A.flatBlockAngle w d ε q) t).2
    rw [variableAnnularConnector_norm 0 hR] at hb
    refine ⟨β,div_nonneg (affineBlend_pos hR hρpos t).le hρpos.le,
      (div_le_one hρpos).mpr hb,?_⟩
    exact A.localBlockConnector_radial_point c w d α R S ε hR hRS hρ hden q t (not_le.mp ht).le

/-- The radial head/tail property is available uniformly for every sufficiently
small signed width, independently of the bank's strict positive-width order. -/
theorem exists_radialTail_radius (c : ℂ) (w : Fin n → ℂ)
    (d : Fin n → Fin r → ℝ) (α : Fin (n*r) → ℝ) (R S : ℝ)
    (hR : 0 < R) (hRS : R < S) (hS : ∀ i, S < A.radius i) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε, |ε| < ε₀ → ∀ q,
      RadialTailProperty (A.localBlockConnector c w d α R S ε q)
        c (A.blockEndpoint w d ε q) (‖A.rotation‖*S) := by
  have hradius : ∀ᶠ ε in 𝓝 (0:ℝ), ∀ q, S < A.blockRadius w d ε q := by
    rw [Filter.eventually_all]
    intro q
    exact continuousAt_const.eventually_lt (A.blockRadius_continuousAt_zero w d q)
      (by simpa using hS (finProdFinEquiv.symm q).1)
  have hh : ∀ᶠ ε in 𝓝 (0:ℝ), ∀ q,
      RadialTailProperty (A.localBlockConnector c w d α R S ε q)
        c (A.blockEndpoint w d ε q) (‖A.rotation‖*S) := by
    filter_upwards [A.eventually_blockAngle_order w d,hradius] with ε horder hrho
    intro q
    exact A.localBlockConnector_radialTail c w d α R S ε hR hRS
      (fun q => (hrho q).le) horder.1 q
  obtain ⟨ε₀,hε₀,hball⟩ := Metric.mem_nhds_iff.mp hh
  exact ⟨ε₀,hε₀,fun ε hε => hball (by simpa [Metric.mem_ball,Real.dist_eq] using hε)⟩

end OrderedRayAngles
end
end MatchgateWidth
