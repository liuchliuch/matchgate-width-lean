import MatchgateWidth.PurePencilAnnihilator

/-! # Three-point form of the intrinsic pure-pencil bound -/
namespace MatchgateWidth
noncomputable section
variable {K : Type*} [Field K] [CharZero K] {t : ℕ}

/-- Nonzero rescaling leaves the literal signed Clifford annihilator unchanged. -/
theorem spinorAnnihilator_smul_ne_zero (u : SubsetSignature t K) {a : K} (ha : a ≠ 0) :
    spinorAnnihilator (a • u) = spinorAnnihilator u := by
  ext z
  change signedCliffordAction z (a • u) = 0 ↔ signedCliffordAction z u = 0
  rw [map_smul, smul_eq_zero]
  simp only [ha, false_or]

/-- A genuinely mixed third pure point suffices for the codimension-two bound.
This uses nonzero endpoint rescaling, so no formal polynomial model for the
matchgate quadrics is required. -/
theorem MatchgateIdentities.three_point_annihilator_finrank_lower
    {u v : SubsetSignature t K} (hu : MatchgateIdentities u) (hune : u ≠ 0)
    (hv : MatchgateIdentities v) (hvne : v ≠ 0)
    {a b : K} (ha : a ≠ 0) (hb : b ≠ 0)
    (hmix : MatchgateIdentities (a • u + b • v)) :
    t - 2 ≤ Module.finrank K ↥(spinorAnnihilator u ⊓ spinorAnnihilator v) := by
  have hu' : MatchgateIdentities (a • u) := hu.const_mul a
  have hv' : MatchgateIdentities (b • v) := hv.const_mul b
  have h := hu'.pencil_annihilator_finrank_lower (smul_ne_zero ha hune)
    hv' (smul_ne_zero hb hvne) hmix
  rwa [spinorAnnihilator_smul_ne_zero u ha, spinorAnnihilator_smul_ne_zero v hb] at h

/-- Pure-spinor packaging of the three actual matchgate points. -/
theorem pure_three_point_annihilator_finrank_lower
    {u v : SubsetSignature t K} (hu : IsPureSpinor u) (hv : IsPureSpinor v)
    {a b : K} (ha : a ≠ 0) (hb : b ≠ 0)
    (hmix : IsPureSpinor (a • u + b • v)) :
    t - 2 ≤ Module.finrank K ↥(spinorAnnihilator u ⊓ spinorAnnihilator v) := by
  have hu' := (isPureSpinor_iff_matchgateIdentities u).mp hu
  have hv' := (isPureSpinor_iff_matchgateIdentities v).mp hv
  have hm' := (isPureSpinor_iff_matchgateIdentities _).mp hmix
  exact hu'.2.three_point_annihilator_finrank_lower hu'.1 hv'.2 hv'.1 ha hb hm'.2

end
end MatchgateWidth
