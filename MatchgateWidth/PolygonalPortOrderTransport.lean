import MatchgateWidth.PolygonalEndpointGerms
import MatchgateWidth.LabelledInstances

/-! # Preserving marked positive port order under polygonal replacement -/
namespace MatchgateWidth
noncomputable section
open Set unitInterval
namespace LabelledInstance.PositivePortOrder

variable {n : ℕ} {vertex : ℂ} {arc : Fin n → unitInterval → ℂ}

/-- Independently rescaling each velocity by a positive amount preserves the
rotation and marked port parameters. Finiteness supplies one common germ radius,
including the empty-port case. -/
def rescaleGerms (P : LabelledInstance.PositivePortOrder vertex arc)
    (newArc : Fin n → unitInterval → ℂ)
    (κ : Fin n → ℝ) (hκ : ∀ i, 0 < κ i)
    (τ : Fin n → unitInterval) (hτ : ∀ i, 0 < τ i)
    (hgerm : ∀ i t, t ≤ τ i → newArc i t = vertex +
      (t : ℝ) • (κ i • (P.speed i • (P.rotation * twoCenterSquare (P.time i))))) :
    LabelledInstance.PositivePortOrder vertex newArc where
  rotation := P.rotation
  rotation_ne_zero := P.rotation_ne_zero
  time := P.time
  time_strictMono := P.time_strictMono
  time_range := P.time_range
  speed i := κ i * P.speed i
  speed_pos i := mul_pos (hκ i) (P.speed_pos i)
  radius := Finset.univ.inf τ
  radius_pos := (Finset.lt_inf_iff (show (0 : unitInterval) < ⊤ from zero_lt_one)).mpr
    (fun i _ => hτ i)
  germ i t ht := by
    rw [hgerm i t (ht.trans (Finset.inf_le (Finset.mem_univ i)))]
    simp only [smul_smul]

@[simp] theorem rescaleGerms_rotation (P : LabelledInstance.PositivePortOrder vertex arc)
    (newArc : Fin n → unitInterval → ℂ)
    (κ : Fin n → ℝ) (hκ : ∀ i, 0 < κ i)
    (τ : Fin n → unitInterval) (hτ : ∀ i, 0 < τ i)
    (hgerm : ∀ i t, t ≤ τ i → newArc i t = vertex +
      (t : ℝ) • (κ i • (P.speed i • (P.rotation * twoCenterSquare (P.time i))))) :
    (P.rescaleGerms newArc κ hκ τ hτ hgerm).rotation = P.rotation := rfl

@[simp] theorem rescaleGerms_time (P : LabelledInstance.PositivePortOrder vertex arc)
    (newArc : Fin n → unitInterval → ℂ)
    (κ : Fin n → ℝ) (hκ : ∀ i, 0 < κ i)
    (τ : Fin n → unitInterval) (hτ : ∀ i, 0 < τ i)
    (hgerm : ∀ i t, t ≤ τ i → newArc i t = vertex +
      (t : ℝ) • (κ i • (P.speed i • (P.rotation * twoCenterSquare (P.time i))))) :
    (P.rescaleGerms newArc κ hκ τ hτ hgerm).time = P.time := rfl

@[simp] theorem rescaleGerms_speed (P : LabelledInstance.PositivePortOrder vertex arc)
    (newArc : Fin n → unitInterval → ℂ)
    (κ : Fin n → ℝ) (hκ : ∀ i, 0 < κ i)
    (τ : Fin n → unitInterval) (hτ : ∀ i, 0 < τ i)
    (hgerm : ∀ i t, t ≤ τ i → newArc i t = vertex +
      (t : ℝ) • (κ i • (P.speed i • (P.rotation * twoCenterSquare (P.time i)))))
    (i : Fin n) :
    (P.rescaleGerms newArc κ hκ τ hτ hgerm).speed i = κ i * P.speed i := rfl

/-- Existential endpoint-germ data suffice to transport positive port order,
with the old rotation and every marked time kept exactly unchanged. -/
theorem exists_of_positive_germs (P : LabelledInstance.PositivePortOrder vertex arc)
    (newArc : Fin n → unitInterval → ℂ)
    (hgerm : ∀ i, ∃ κ : ℝ, 0 < κ ∧ ∃ τ : unitInterval, 0 < τ ∧
      ∀ t : unitInterval, t ≤ τ → newArc i t = vertex +
        (t : ℝ) • (κ • (P.speed i • (P.rotation * twoCenterSquare (P.time i))))) :
    ∃ Q : LabelledInstance.PositivePortOrder vertex newArc,
      Q.rotation = P.rotation ∧ Q.time = P.time := by
  choose κ hκ τ hτ hgerm using hgerm
  exact ⟨P.rescaleGerms newArc κ hκ τ hτ hgerm,rfl,rfl⟩

end LabelledInstance.PositivePortOrder
end
end MatchgateWidth
