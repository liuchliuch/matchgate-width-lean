import MatchgateWidth.SquareDiskDrawing

/-! # Actual local geometry of parallel polygonal ribbons

A transverse vector at each polygon vertex specifies a common cross-section.
Each wire is a straight segment between equal signed positions in consecutive
cross-sections. Positive determinants prove wire separation inside a strip
and prove that consecutive strips meet only at matching section endpoints.
No planar drawing or matching-identity conclusion is assumed.
-/
namespace MatchgateWidth
noncomputable section

/-- Oriented Euclidean area, positive from a tangent toward its left normal. -/
def orientedArea (a b : ℂ) : ℝ := a.re * b.im - a.im * b.re

@[simp] theorem orientedArea_zero_left (a : ℂ) : orientedArea 0 a = 0 := by
  simp [orientedArea]
@[simp] theorem orientedArea_zero_right (a : ℂ) : orientedArea a 0 = 0 := by
  simp [orientedArea]

def ribbonSection (p u : ℂ) (δ : ℝ) : ℂ := p + δ • u

def ribbonDirection (p q u v : ℂ) (δ : ℝ) : ℂ := q - p + δ • (v - u)

def ribbonArc (p q u v : ℂ) (δ : ℝ) : unitInterval → ℂ :=
  straightArc (ribbonSection p u δ) (ribbonSection q v δ)

@[simp] theorem ribbonArc_zero (p q u v : ℂ) (δ : ℝ) :
    ribbonArc p q u v δ 0 = ribbonSection p u δ := straightArc_zero _ _
@[simp] theorem ribbonArc_one (p q u v : ℂ) (δ : ℝ) :
    ribbonArc p q u v δ 1 = ribbonSection q v δ := straightArc_one _ _

theorem continuous_ribbonArc (p q u v : ℂ) (δ : ℝ) :
    Continuous (ribbonArc p q u v δ) := continuous_straightArc _ _

theorem ribbonDirection_eq (p q u v : ℂ) (δ : ℝ) :
    ribbonDirection p q u v δ = ribbonSection q v δ - ribbonSection p u δ := by
  simp only [ribbonDirection, ribbonSection, smul_sub]
  abel

/-- Exact determinant of a point on another wire relative to this wire. -/
theorem ribbonArc_area (p q u v : ℂ) (δ η : ℝ) (t : unitInterval) :
    orientedArea (ribbonDirection p q u v δ)
      (ribbonArc p q u v η t - ribbonSection p u δ) =
    (η - δ) * ((1 - (t : ℝ)) * orientedArea (ribbonDirection p q u v δ) u +
      (t : ℝ) * orientedArea (ribbonDirection p q u v δ) v) := by
  simp [orientedArea, ribbonDirection, ribbonArc, straightArc, ribbonSection,
     ]
  ring

/-- Distinct ordered wires cannot meet anywhere within one positively
transverse strip, including the endpoint cross-sections. -/
theorem ribbonArc_disjoint_of_lt (p q u v : ℂ) {δ η : ℝ} (hδη : δ < η)
    (hu : 0 < orientedArea (ribbonDirection p q u v δ) u)
    (hv : 0 < orientedArea (ribbonDirection p q u v δ) v) :
    Disjoint (Set.range (ribbonArc p q u v δ)) (Set.range (ribbonArc p q u v η)) := by
  apply Set.disjoint_left.mpr
  rintro z ⟨s,rfl⟩ ⟨t,ht⟩
  have he := congrArg (fun z => orientedArea (ribbonDirection p q u v δ)
    (z - ribbonSection p u δ)) ht
  rw [ribbonArc_area, ribbonArc_area] at he
  have hc : 0 < (1 - (t : ℝ)) * orientedArea (ribbonDirection p q u v δ) u +
      (t : ℝ) * orientedArea (ribbonDirection p q u v δ) v := by
    by_cases ht0 : (t : ℝ) = 0
    · simpa [ht0] using hu
    · exact add_pos_of_nonneg_of_pos
        (mul_nonneg (sub_nonneg.mpr t.property.2) hu.le)
        (mul_pos (lt_of_le_of_ne t.property.1 (Ne.symm ht0)) hv)
  have hh := mul_pos (sub_pos.mpr hδη) hc
  nlinarith

/-- Each lane is itself a simple continuous segment. -/
theorem ribbonArc_injective (p q u v : ℂ) (δ : ℝ)
    (hu : 0 < orientedArea (ribbonDirection p q u v δ) u) :
    Function.Injective (ribbonArc p q u v δ) := by
  apply straightArc_injective
  intro he
  have hd : ribbonDirection p q u v δ = 0 := by rw [ribbonDirection_eq, he, sub_self]
  simp only [hd, orientedArea_zero_left, lt_self_iff_false] at hu

/-- The complete local strip map is injective in both the lane and the path
parameter on any set of permitted transverse lane offsets. -/
theorem ribbonArc_eq_iff (p q u v : ℂ) {δ η : ℝ}
    (hδu : 0 < orientedArea (ribbonDirection p q u v δ) u)
    (hδv : 0 < orientedArea (ribbonDirection p q u v δ) v)
    (hηu : 0 < orientedArea (ribbonDirection p q u v η) u)
    (hηv : 0 < orientedArea (ribbonDirection p q u v η) v)
    (s t : unitInterval) :
    ribbonArc p q u v δ s = ribbonArc p q u v η t ↔ δ = η ∧ s = t := by
  constructor
  · intro h
    have hδη : δ = η := by
      rcases lt_trichotomy δ η with hl | he | hr
      · exact (Set.disjoint_left.mp (ribbonArc_disjoint_of_lt p q u v hl hδu hδv)
          ⟨s,rfl⟩ ⟨t,h.symm⟩).elim
      · exact he
      · exact (Set.disjoint_left.mp (ribbonArc_disjoint_of_lt p q u v hr hηu hηv)
          ⟨t,rfl⟩ ⟨s,h⟩).elim
    subst η
    exact ⟨rfl, ribbonArc_injective p q u v δ hδu h⟩
  · rintro ⟨rfl,rfl⟩
    rfl

/-- Every point before a joint is on the positive side of its cross-section. -/
theorem ribbonArc_before_area (p q u v : ℂ) (δ : ℝ) (s : unitInterval) :
    orientedArea v (ribbonArc p q u v δ s - q) =
      (1 - (s : ℝ)) * orientedArea (ribbonDirection p q u v δ) v := by
  simp [orientedArea, ribbonDirection, ribbonArc, straightArc, ribbonSection,
     ]
  ring

/-- Every point after a joint is on the negative side of its cross-section. -/
theorem ribbonArc_after_area (q r v w : ℂ) (η : ℝ) (t : unitInterval) :
    orientedArea v (ribbonArc q r v w η t - q) =
      -(t : ℝ) * orientedArea (ribbonDirection q r v w η) v := by
  simp [orientedArea, ribbonDirection, ribbonArc, straightArc, ribbonSection,
     ]
  ring

/-- Consecutive strips, including arbitrary bend angles, intersect only at
their common endpoint on the same lane. This is the local ribbon-joint rule. -/
theorem ribbonArc_adjacent_eq_iff (p q r u v w : ℂ) (δ η : ℝ)
    (hδ : 0 < orientedArea (ribbonDirection p q u v δ) v)
    (hη : 0 < orientedArea (ribbonDirection q r v w η) v)
    (s t : unitInterval) :
    ribbonArc p q u v δ s = ribbonArc q r v w η t ↔
      s = 1 ∧ t = 0 ∧ δ = η := by
  constructor
  · intro h
    have he := congrArg (fun z => orientedArea v (z - q)) h
    rw [ribbonArc_before_area, ribbonArc_after_area] at he
    have hnonneg : 0 ≤ (1 - (s : ℝ)) * orientedArea (ribbonDirection p q u v δ) v :=
      mul_nonneg (sub_nonneg.mpr s.property.2) hδ.le
    have ht0 : (t : ℝ) = 0 := by nlinarith [t.property.1]
    have hs1 : (s : ℝ) = 1 := by rw [ht0] at he; nlinarith
    have ht : t = 0 := Subtype.ext ht0
    have hs : s = 1 := Subtype.ext hs1
    subst s
    subst t
    simp only [ribbonArc_one, ribbonArc_zero, ribbonSection, add_right_inj] at h
    have hv : v ≠ 0 := by
      intro hv
      rw [hv, orientedArea_zero_right] at hδ
      exact lt_irrefl _ hδ
    have hδη : δ = η := smul_left_injective ℝ hv h
    exact ⟨rfl,rfl,hδη⟩
  · rintro ⟨rfl,rfl,rfl⟩
    simp

end
end MatchgateWidth
