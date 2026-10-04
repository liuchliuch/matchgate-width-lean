import MatchgateWidth.CliffordBlockAction

/-! # Signed covariance of unsigned boundary reversal
Reversing the ordered coefficient list is not an unsigned exterior coordinate
permutation. Negating the creation half of the reversed Clifford vector gives
the exact covariance, with the target-degree sign displayed explicitly.
-/
namespace MatchgateWidth
noncomputable section
open scoped symmDiff
variable {R : Type*} [CommRing R] {t : ℕ}

/-- Unsigned reversal of coefficient subsets, as used in ordered matrices. -/
def reverseSpinor (u : SubsetSignature t R) : SubsetSignature t R :=
  fun S => u (reversePortSubset S)

/-- The Clifford-coordinate correction for unsigned coefficient reversal. -/
def reverseCliffordEquiv : CliffordVector t R ≃ₗ[R] CliffordVector t R where
  toFun z := (fun i => -z.1 i.rev, fun i => z.2 i.rev)
  invFun z := (fun i => -z.1 i.rev, fun i => z.2 i.rev)
  left_inv z := by apply Prod.ext <;> funext i <;> simp
  right_inv z := by apply Prod.ext <;> funext i <;> simp
  map_add' z w := by apply Prod.ext <;> funext i <;> simp [add_comm]
  map_smul' c z := by apply Prod.ext <;> funext i <;> simp

private theorem fermionSign_reverse_not_mem (S : Finset (Fin t)) (i : Fin t) (hi : i ∉ S) :
    (-1 : R)^S.card * fermionSign (reversePortSubset S) i.rev = fermionSign S i := by
  have hr : subsetBelow (reversePortSubset S) i.rev = (S.filter (i < ·)).card := by
    have he : (reversePortSubset S).filter (· < i.rev) = reversePortSubset (S.filter (i < ·)) := by
      ext j
      simp only [Finset.mem_filter, mem_reversePortSubset]
      rw [← Fin.rev_lt_rev]
      simp
    rw [subsetBelow, he, reversePortSubset, Finset.card_image_of_injective _ Fin.rev_injective]
  have hp : subsetBelow S i + (S.filter (i < ·)).card = S.card := by
    have he : S.filter (fun j => ¬j < i) = S.filter (i < ·) := by
      ext j
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hj, hjlt⟩
        exact ⟨hj, lt_of_le_of_ne (le_of_not_gt hjlt) (by intro h; exact hi (h ▸ hj))⟩
      · rintro ⟨hj, hlt⟩
        exact ⟨hj, not_lt_of_gt hlt⟩
    simpa only [subsetBelow, he] using Finset.card_filter_add_card_filter_not (s := S) (p := (· < i))
  rw [fermionSign, hr, ← hp, pow_add]
  have hs : (-1 : R)^(S.filter (i < ·)).card * (-1 : R)^(S.filter (i < ·)).card = 1 := by
    rw [← mul_pow]; simp
  rw [mul_assoc, hs, mul_one]
  rfl

/-- Exact reversal sign in both occupancy cases. -/
theorem fermionSign_reverse (S : Finset (Fin t)) (i : Fin t) :
    (-1 : R)^S.card * fermionSign (reversePortSubset S) i.rev =
      if i ∈ S then -fermionSign S i else fermionSign S i := by
  by_cases hi : i ∈ S
  · have he : S ∆ {i} = S.erase i := by
      ext j
      simp only [Finset.mem_symmDiff, Finset.mem_singleton, Finset.mem_erase]
      grind
    have hsign := fermionSign_reverse_not_mem (R := R) (S.erase i) i (Finset.notMem_erase i S)
    have hrev : fermionSign (R := R) (reversePortSubset (S.erase i)) i.rev =
        fermionSign (reversePortSubset S) i.rev := by
      rw [← he, reversePortSubset_symmDiff, reversePortSubset_singleton, fermionSign_toggle_self]
    have horig : fermionSign (R := R) (S.erase i) i = fermionSign S i := by
      rw [← he, fermionSign_toggle_self]
    rw [hrev, horig] at hsign
    rw [ite_eq_left hi, ← Finset.card_erase_add_one hi, pow_succ]
    calc
      _ = -((-1 : R)^(S.erase i).card * fermionSign (reversePortSubset S) i.rev) := by ring
      _ = _ := by rw [hsign]
  · simpa [hi] using fermionSign_reverse_not_mem (R := R) S i hi

/-- Actual Clifford covariance for unsigned reversal, including all degree signs. -/
theorem signedCliffordAction_reverse
    (z : CliffordVector t R) (u : SubsetSignature t R) (S : Finset (Fin t)) :
    (-1 : R)^S.card * signedCliffordAction (reverseCliffordEquiv z) (reverseSpinor u)
      (reversePortSubset S) = signedCliffordAction z u S := by
  rw [signedCliffordAction_apply, signedCliffordAction_apply, Finset.mul_sum]
  apply Finset.sum_equiv Fin.revPerm
  · intro i; simp
  · intro i _
    simp only [Fin.revPerm_apply, mem_reversePortSubset, reverseCliffordEquiv,
      LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, reverseSpinor, reversePortSubset_symmDiff,
      reversePortSubset_reversePortSubset, reversePortSubset_singleton]
    have hsign := fermionSign_reverse (R := R) S i.rev
    simp only [Fin.rev_rev] at hsign
    by_cases hi : i.rev ∈ S
    · rw [ite_eq_left hi, ite_eq_left hi] at *
      calc
        _ = -(((-1 : R)^S.card * fermionSign (reversePortSubset S) i) * z.1 i.rev * u (S ∆ {i.rev})) := by ring
        _ = _ := by rw [hsign]; ring
    · rw [ite_eq_right hi, ite_eq_right hi] at *
      calc
        _ = ((-1 : R)^S.card * fermionSign (reversePortSubset S) i) * z.2 i.rev * u (S ∆ {i.rev}) := by ring
        _ = _ := by rw [hsign]

/-- Reversal identifies the actual annihilators by the explicit corrected
linear equivalence; the target-degree sign cancels because it is a unit. -/
theorem reverseClifford_mem_annihilator_iff (z : CliffordVector t R) (u : SubsetSignature t R) :
    reverseCliffordEquiv z ∈ spinorAnnihilator (reverseSpinor u) ↔ z ∈ spinorAnnihilator u := by
  change signedCliffordAction (reverseCliffordEquiv z) (reverseSpinor u) = 0 ↔
    signedCliffordAction z u = 0
  constructor
  · intro h
    ext S
    have hc := signedCliffordAction_reverse z u S
    rw [h] at hc
    simpa using hc.symm
  · intro h
    ext S
    have hc := signedCliffordAction_reverse z u (reversePortSubset S)
    rw [reversePortSubset_reversePortSubset, h] at hc
    exact (neg_one_pow_mul_eq_zero_iff).mp hc

end
end MatchgateWidth
