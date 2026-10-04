import MatchgateWidth.SubsetSignParity
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Signed Clifford action in subset coordinates

The coefficient of `e_S` in exterior multiplication or contraction is computed
with the number of members of `S` strictly before the selected mode. These are
actual operators on coefficient tables, not an assumed spin representation.
-/
namespace MatchgateWidth
noncomputable section
open scoped symmDiff
variable {R : Type*} [CommRing R] {t : ℕ}

/-- The Koszul sign of inserting/deleting mode `i`. -/
def fermionSign (S : Finset (Fin t)) (i : Fin t) : R :=
  (-1 : R) ^ subsetBelow S i

@[simp] theorem fermionSign_sq (S : Finset (Fin t)) (i : Fin t) :
    fermionSign (R := R) S i * fermionSign S i = 1 := by
  simp [fermionSign, ← mul_pow]

@[simp] theorem fermionSign_singleton (i j : Fin t) :
    fermionSign (R := R) {j} i = if j < i then -1 else 1 := by
  by_cases h : j < i <;> simp [fermionSign, subsetBelow, Finset.filter_singleton, h]

@[simp] theorem fermionSign_toggle (S : Finset (Fin t)) (i j : Fin t) :
    fermionSign (R := R) (S ∆ {j}) i =
      fermionSign S i * (if j < i then -1 else 1) := by
  rw [fermionSign, ← subsetBelow_sign_symmDiff]
  change fermionSign S i * fermionSign {j} i = _
  rw [fermionSign_singleton]

@[simp] theorem fermionSign_toggle_self (S : Finset (Fin t)) (i : Fin t) :
    fermionSign (R := R) (S ∆ {i}) i = fermionSign S i := by simp

private theorem toggle_twice (S : Finset (Fin t)) (i : Fin t) :
    S ∆ {i} ∆ {i} = S := by simp

private theorem toggle_commute (S : Finset (Fin t)) (i j : Fin t) :
    S ∆ {i} ∆ {j} = S ∆ {j} ∆ {i} := by
  rw [symmDiff_assoc, symmDiff_comm ({i} : Finset _) {j}, ← symmDiff_assoc]

/-- Actual exterior multiplication by the basis vector `e_i`. -/
def fermionCreate (i : Fin t) : SubsetSignature t R →ₗ[R] SubsetSignature t R where
  toFun u S := if i ∈ S then fermionSign S i * u (S ∆ {i}) else 0
  map_add' u v := by ext S; by_cases h : i ∈ S <;> simp [h, mul_add]
  map_smul' c u := by ext S; by_cases h : i ∈ S <;> simp [h]; ring

/-- Actual contraction by the dual basis vector `e_i^*`. -/
def fermionContract (i : Fin t) : SubsetSignature t R →ₗ[R] SubsetSignature t R where
  toFun u S := if i ∈ S then 0 else fermionSign S i * u (S ∆ {i})
  map_add' u v := by ext S; by_cases h : i ∈ S <;> simp [h, mul_add]
  map_smul' c u := by ext S; by_cases h : i ∈ S <;> simp [h]; ring

@[simp] theorem fermionCreate_apply (i : Fin t) (u : SubsetSignature t R)
    (S : Finset (Fin t)) :
    fermionCreate i u S = if i ∈ S then fermionSign S i * u (S ∆ {i}) else 0 := rfl

@[simp] theorem fermionContract_apply (i : Fin t) (u : SubsetSignature t R)
    (S : Finset (Fin t)) :
    fermionContract i u S = if i ∈ S then 0 else fermionSign S i * u (S ∆ {i}) := rfl

@[simp] theorem fermionCreate_sq (i : Fin t) (u : SubsetSignature t R) :
    fermionCreate i (fermionCreate i u) = 0 := by
  ext S
  by_cases h : i ∈ S <;> simp [h, Finset.mem_symmDiff]

@[simp] theorem fermionContract_sq (i : Fin t) (u : SubsetSignature t R) :
    fermionContract i (fermionContract i u) = 0 := by
  ext S
  by_cases h : i ∈ S <;> simp [h, Finset.mem_symmDiff]

/-- The same-mode creation/contraction anticommutator is exactly the identity. -/
theorem fermionCreate_contract_same (i : Fin t) (u : SubsetSignature t R) :
    fermionCreate i (fermionContract i u) + fermionContract i (fermionCreate i u) = u := by
  ext S
  by_cases h : i ∈ S <;> simp [h, Finset.mem_symmDiff, ← mul_assoc]

private theorem fermionSign_anticommute (S : Finset (Fin t)) {i j : Fin t}
    (hij : i ≠ j) :
    fermionSign (R := R) S i * fermionSign (S ∆ {i}) j =
      -(fermionSign S j * fermionSign (S ∆ {j}) i) := by
  rcases lt_or_gt_of_ne hij with h | h
  · simp [h, not_lt_of_gt h]; ring
  · simp [h, not_lt_of_gt h]; ring

/-- Creation at distinct modes anticommutes, with the actual coefficient signs. -/
theorem fermionCreate_anticommute {i j : Fin t} (hij : i ≠ j)
    (u : SubsetSignature t R) :
    fermionCreate i (fermionCreate j u) = -fermionCreate j (fermionCreate i u) := by
  ext S
  have hmij : i = j ↔ False := iff_false_intro hij
  have hmji : j = i ↔ False := iff_false_intro hij.symm
  by_cases hi : i ∈ S <;> by_cases hj : j ∈ S <;>
    rcases lt_or_gt_of_ne hij with hlt | hlt <;>
    simp [hi, hj, hij, hij.symm, Finset.mem_symmDiff, toggle_commute S i j,
      hlt, not_lt_of_gt hlt] <;> ring

/-- Contraction at distinct modes anticommutes. -/
theorem fermionContract_anticommute {i j : Fin t} (hij : i ≠ j)
    (u : SubsetSignature t R) :
    fermionContract i (fermionContract j u) = -fermionContract j (fermionContract i u) := by
  ext S
  have hmij : i = j ↔ False := iff_false_intro hij
  have hmji : j = i ↔ False := iff_false_intro hij.symm
  by_cases hi : i ∈ S <;> by_cases hj : j ∈ S <;>
    rcases lt_or_gt_of_ne hij with hlt | hlt <;>
    simp [hi, hj, hij, hij.symm, Finset.mem_symmDiff, toggle_commute S i j,
      hlt, not_lt_of_gt hlt] <;> ring

/-- Creation and contraction at distinct modes anticommute. -/
theorem fermionCreate_contract_ne {i j : Fin t} (hij : i ≠ j)
    (u : SubsetSignature t R) :
    fermionCreate i (fermionContract j u) = -fermionContract j (fermionCreate i u) := by
  ext S
  have hmij : i = j ↔ False := iff_false_intro hij
  have hmji : j = i ↔ False := iff_false_intro hij.symm
  by_cases hi : i ∈ S <;> by_cases hj : j ∈ S <;>
    rcases lt_or_gt_of_ne hij with hlt | hlt <;>
    simp [hi, hj, hij, hij.symm, Finset.mem_symmDiff, toggle_commute S i j,
      hlt, not_lt_of_gt hlt] <;> ring

/-- Coordinate model of `W ⊕ W*`, using the fixed basis of `W = R^t`. -/
abbrev CliffordVector (t : ℕ) (R : Type*) := (Fin t → R) × (Fin t → R)

/-- Clifford multiplication `w ∧ u + i_φ u` in the ordered coefficient basis. -/
def signedCliffordAction (z : CliffordVector t R) :
    SubsetSignature t R →ₗ[R] SubsetSignature t R :=
  ∑ i : Fin t, (z.1 i • fermionCreate i + z.2 i • fermionContract i)

/-- Clifford multiplication is linear in the vector of the split space. -/
def signedCliffordRepresentation :
    CliffordVector t R →ₗ[R] Module.End R (SubsetSignature t R) where
  toFun := signedCliffordAction
  map_add' z w := by
    simp only [signedCliffordAction, Prod.fst_add, Prod.snd_add, Pi.add_apply, add_smul]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    abel
  map_smul' c z := by
    simp [signedCliffordAction, smul_add, Finset.smul_sum, smul_smul]

/-- The linear map whose kernel is the annihilator of a coefficient spinor. -/
def cliffordAtSpinor (u : SubsetSignature t R) :
    CliffordVector t R →ₗ[R] SubsetSignature t R :=
  (LinearMap.applyₗ u).comp signedCliffordRepresentation

@[simp] theorem cliffordAtSpinor_apply (u : SubsetSignature t R)
    (z : CliffordVector t R) : cliffordAtSpinor u z = signedCliffordAction z u := rfl

/-- Annihilator in the genuine signed creation/contraction representation. -/
def spinorAnnihilator (u : SubsetSignature t R) : Submodule R (CliffordVector t R) :=
  LinearMap.ker (cliffordAtSpinor u)

/-- The vector `e_i` in the creation summand. -/
def cliffordCreationVector (i : Fin t) : CliffordVector t R :=
  (Pi.single i 1, 0)

/-- The covector `e_i*` in the contraction summand. -/
def cliffordContractionVector (i : Fin t) : CliffordVector t R :=
  (0, Pi.single i 1)

@[simp] theorem signedCliffordAction_creation (i : Fin t) :
    signedCliffordAction (cliffordCreationVector (R := R) i) = fermionCreate i := by
  ext u S
  simp [signedCliffordAction, cliffordCreationVector, Pi.single_apply]

@[simp] theorem signedCliffordAction_contraction (i : Fin t) :
    signedCliffordAction (cliffordContractionVector (R := R) i) = fermionContract i := by
  ext u S
  simp [signedCliffordAction, cliffordContractionVector, Pi.single_apply]

private theorem create_create_car (i j : Fin t) :
    fermionCreate (R := R) i * fermionCreate j + fermionCreate j * fermionCreate i = 0 := by
  apply LinearMap.ext
  intro u
  ext S
  by_cases h : i = j
  · subst j; simp [Module.End.mul_apply]
  · simpa [Module.End.mul_apply] using congrFun (eq_neg_iff_add_eq_zero.mp (fermionCreate_anticommute h u)) S

private theorem contract_contract_car (i j : Fin t) :
    fermionContract (R := R) i * fermionContract j +
      fermionContract j * fermionContract i = 0 := by
  apply LinearMap.ext
  intro u
  ext S
  by_cases h : i = j
  · subst j; simp [Module.End.mul_apply]
  · simpa [Module.End.mul_apply] using congrFun (eq_neg_iff_add_eq_zero.mp (fermionContract_anticommute h u)) S

private theorem create_contract_car (i j : Fin t) :
    fermionCreate (R := R) i * fermionContract j + fermionContract j * fermionCreate i =
      if i = j then 1 else 0 := by
  apply LinearMap.ext
  intro u
  ext S
  by_cases h : i = j
  · subst j
    simpa only [ite_true, Module.End.mul_apply, LinearMap.add_apply, Pi.add_apply,
      Module.End.one_apply] using congrFun (fermionCreate_contract_same i u) S
  · simpa [h, Module.End.mul_apply] using congrFun (eq_neg_iff_add_eq_zero.mp (fermionCreate_contract_ne h u)) S

private theorem mode_car (i j : Fin t) (a b c d : R) :
    (a • fermionCreate i + b • fermionContract i) *
        (c • fermionCreate j + d • fermionContract j) +
      (c • fermionCreate j + d • fermionContract j) *
        (a • fermionCreate i + b • fermionContract i) =
      if i = j then (a * d + c * b) • (1 : Module.End R (SubsetSignature t R)) else 0 := by
  have h₁ := create_create_car (R := R) i j
  have h₂ := contract_contract_car (R := R) i j
  have h₃ := create_contract_car (R := R) i j
  have h₄ := create_contract_car (R := R) j i
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm]
  calc
    _ = (a * c) • (fermionCreate i * fermionCreate j + fermionCreate j * fermionCreate i) +
        (b * d) • (fermionContract i * fermionContract j + fermionContract j * fermionContract i) +
        (a * d) • (fermionCreate i * fermionContract j + fermionContract j * fermionCreate i) +
        (c * b) • (fermionCreate j * fermionContract i + fermionContract i * fermionCreate j) := by
          module
    _ = _ := by
      rw [h₁, h₂, h₃, h₄]
      by_cases h : i = j
      · subst j; simp [add_smul]
      · simp [h, Ne.symm h]

/-- The split symmetric pairing, with no factor of one half. -/
def cliffordPairing (z w : CliffordVector t R) : R :=
  ∑ i : Fin t, (z.1 i * w.2 i + w.1 i * z.2 i)

/-- The canonical anticommutation relation, proved from the ordered subset signs. -/
theorem signedCliffordAction_car (z w : CliffordVector t R) :
    signedCliffordAction z * signedCliffordAction w +
      signedCliffordAction w * signedCliffordAction z =
      cliffordPairing z w • (1 : Module.End R (SubsetSignature t R)) := by
  simp only [signedCliffordAction, Finset.sum_mul, Finset.mul_sum]
  conv_lhs => lhs; rw [Finset.sum_comm]
  simp only [← Finset.sum_add_distrib, mode_car]
  simp [cliffordPairing, Finset.sum_smul]

/-- A subspace is isotropic for precisely the split pairing used by the action. -/
def CliffordIsotropic (K : Submodule R (CliffordVector t R)) : Prop :=
  ∀ z ∈ K, ∀ w ∈ K, cliffordPairing z w = 0

/-- Every nonzero spinor has an isotropic annihilator. -/
theorem spinorAnnihilator_isotropic [IsDomain R]
    {u : SubsetSignature t R} (hu : u ≠ 0) : CliffordIsotropic (spinorAnnihilator u) := by
  intro z hz w hw
  have hz' : signedCliffordAction z u = 0 := hz
  have hw' : signedCliffordAction w u = 0 := hw
  have h := congrArg (fun f : Module.End R (SubsetSignature t R) => f u)
    (signedCliffordAction_car z w)
  simp only [LinearMap.add_apply, Module.End.mul_apply, hz', hw', map_zero,
    add_zero, LinearMap.smul_apply, Module.End.one_apply] at h
  exact (smul_eq_zero.mp h.symm).resolve_right hu

/-- The genuine common annihilator for a subspace of the split quadratic space. -/
def cliffordJointKernel (K : Submodule R (CliffordVector t R)) :
    Submodule R (SubsetSignature t R) :=
  ⨅ z : K, LinearMap.ker (signedCliffordAction (z : CliffordVector t R))

@[simp] theorem mem_cliffordJointKernel (K : Submodule R (CliffordVector t R))
    (u : SubsetSignature t R) :
    u ∈ cliffordJointKernel K ↔ ∀ z ∈ K, signedCliffordAction z u = 0 := by
  simp [cliffordJointKernel]

end
end MatchgateWidth
