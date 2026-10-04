import MatchgateWidth.ConnectionPrimeCompression

/-! # Exclusive support-geometric alternatives with exact mobile compression

The geometric alternatives have the source meanings. The mobile conclusion
constructs one presentation of the same labelled language. Tensor normal forms
for the ray and flag alternatives are supplied separately by actual support
extraction and exact tensor lifting.
-/
namespace MatchgateWidth
noncomputable section

namespace RealizedMatchgateGeometry
variable {t : ℕ} (g : RealizedMatchgateGeometry t)

def RaySeparable : Prop := g.planes = ∅
def GaussianMobile : Prop := g.planes.Nonempty ∧ ¬ ∃ P L, g.MonomialFlag P L
def OnePlaneFlag : Prop := ∃ P L, g.MonomialFlag P L

/-- The three alternatives are exhaustive and pairwise exclusive. -/
theorem exclusive_trichotomy :
    (g.RaySeparable ∧ ¬ g.GaussianMobile ∧ ¬ g.OnePlaneFlag) ∨
    (g.GaussianMobile ∧ ¬ g.RaySeparable ∧ ¬ g.OnePlaneFlag) ∨
    (g.OnePlaneFlag ∧ ¬ g.RaySeparable ∧ ¬ g.GaussianMobile) := by
  classical
  have hfplane : g.OnePlaneFlag → g.planes.Nonempty := by
    rintro ⟨P, L, h⟩
    exact ⟨P, h.1⟩
  by_cases he : g.planes = ∅
  · refine Or.inl ⟨he, ?_, ?_⟩
    · rintro ⟨⟨P, hP⟩, _⟩
      simpa [he] using hP
    · intro hf
      obtain ⟨P, hP⟩ := hfplane hf
      simpa [he] using hP
  · by_cases hf : g.OnePlaneFlag
    · refine Or.inr (Or.inr ⟨hf, he, ?_⟩)
      exact fun hm => hm.2 hf
    · refine Or.inr (Or.inl ⟨⟨Set.nonempty_iff_ne_empty.mpr he, hf⟩, he, hf⟩)

/-- Essential support span converts the mobile branch into connection-primality. -/
theorem GaussianMobile.connectionPrime
    (h : g.GaussianMobile) (hspan : sSup (g.rays ∪ g.planes) = g.ambient) :
    g.ConnectionPrime := ⟨hspan, h.1, h.2⟩

end RealizedMatchgateGeometry

namespace LabelledCommonPresentation
variable {S : LabelledShape} {t : ℕ}

/-- The entire mobile alternative: same labels, same domain tensors, one fixed
smaller base, and equality on every original ordered planar instance. -/
theorem gaussianMobile_compression (p : LabelledCommonPresentation S (Fin 3) t)
    (hM : p.baseMatrix.rank = 3) (g : RealizedMatchgateGeometry t)
    (hamb : g.ambient = baseSubsetSpace p.baseMatrix)
    (hspan : sSup (g.rays ∪ g.planes) = g.ambient) (hmobile : g.GaussianMobile) :
    ∃ r ≤ 3, ∃ H : Matrix (BooleanInput r) (BooleanInput t) ℂ,
      ExactMatchgateMatrix H ∧ H.rank = 2 ^ r ∧ H.rank ≤ 8 ∧
      ∃ q : LabelledCommonPresentation S (Fin 3) r,
        p.baseMatrix = q.baseMatrix * H ∧ q.left = p.left ∧
        q.language = p.language ∧ ExactlyLabelledEquivalent p.language q.language :=
  p.connectionPrime_compression hM g hamb (hmobile.connectionPrime g hspan)

/-- Trichotomy assembly with the substantive exact-collapse conclusion attached
to the mobile case. The two-plane refinement is `two_planes_compression`. -/
theorem support_geometry_trichotomy (p : LabelledCommonPresentation S (Fin 3) t)
    (hM : p.baseMatrix.rank = 3) (g : RealizedMatchgateGeometry t)
    (hamb : g.ambient = baseSubsetSpace p.baseMatrix)
    (hspan : sSup (g.rays ∪ g.planes) = g.ambient) :
    (g.RaySeparable ∧ ¬ g.GaussianMobile ∧ ¬ g.OnePlaneFlag) ∨
    (g.GaussianMobile ∧ ¬ g.RaySeparable ∧ ¬ g.OnePlaneFlag ∧
      ∃ r ≤ 3, ∃ q : LabelledCommonPresentation S (Fin 3) r,
        q.left = p.left ∧ q.language = p.language ∧
          ExactlyLabelledEquivalent p.language q.language) ∨
    (g.OnePlaneFlag ∧ ¬ g.RaySeparable ∧ ¬ g.GaussianMobile) := by
  rcases g.exclusive_trichotomy with hi | hii | hiii
  · exact Or.inl hi
  · obtain ⟨r, hr, H, hH, hHr, hbound, q, hbase, hleft, heq, hequiv⟩ :=
      p.gaussianMobile_compression hM g hamb hspan hii.1
    exact Or.inr (Or.inl ⟨hii.1, hii.2.1, hii.2.2, r, hr, q, hleft, heq, hequiv⟩)
  · exact Or.inr (Or.inr hiii)

end LabelledCommonPresentation
end
end MatchgateWidth
