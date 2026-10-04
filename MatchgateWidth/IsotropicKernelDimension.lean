import MatchgateWidth.SignedCliffordAction
import MatchgateWidth.AnticommutingKernel
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! # General isotropic common-annihilator dimension
A dual family for the split pairing is constructed by extending coordinate
functionals. The CAR then gives the dimension by successive kernel halving,
without Witt extension or a presumed Pin lift.
-/
namespace MatchgateWidth
noncomputable section
variable {K : Type*} [Field K] {t : ℕ}

/-- Every split-space vector is its literal sum of creation and contraction coordinates. -/
theorem cliffordVector_decomposition (z : CliffordVector t K) :
    z = ∑ i : Fin t, (z.1 i • cliffordCreationVector i + z.2 i • cliffordContractionVector i) := by
  apply Prod.ext <;> ext j <;>
    simp [cliffordCreationVector, cliffordContractionVector, Pi.single_apply,
      Finset.sum_apply, Prod.fst_sum, Prod.snd_sum]

/-- The nondegenerate split pairing represents every linear functional. -/
theorem exists_cliffordPairing_dual (f : CliffordVector t K →ₗ[K] K) :
    ∃ w : CliffordVector t K, ∀ z, cliffordPairing z w = f z := by
  refine ⟨(fun i => f (cliffordContractionVector i), fun i => f (cliffordCreationVector i)), ?_⟩
  intro z
  conv_rhs => rw [cliffordVector_decomposition z]
  simp [cliffordPairing, map_sum, map_add, map_smul, smul_eq_mul, mul_comm]

/-- Every basis of an arbitrary subspace has a dual family in the split space. -/
theorem exists_cliffordPairing_dual_basis {ι : Type*} [DecidableEq ι] (L : Submodule K (CliffordVector t K))
    (b : Module.Basis ι K L) :
    ∃ w : ι → CliffordVector t K, ∀ i j, cliffordPairing (b i : CliffordVector t K) (w j) =
      if i = j then 1 else 0 := by
  classical
  have hex (j : ι) : ∃ w : CliffordVector t K, ∀ i,
      cliffordPairing (b i : CliffordVector t K) w = if i = j then 1 else 0 := by
    obtain ⟨f, hf⟩ := (b.coord j).exists_extend
    obtain ⟨w, hw⟩ := exists_cliffordPairing_dual f
    refine ⟨w, fun i => ?_⟩
    rw [hw]
    have heq := congrArg (fun g : L →ₗ[K] K => g (b i)) hf
    simpa [Module.Basis.coord_apply, Finsupp.single_apply, eq_comm] using heq
  choose w hw using hex
  exact ⟨w, fun i j => hw j i⟩

variable [CharZero K]

/-- Isotropic vectors act by actual square-zero operators. -/
theorem signedCliffordAction_sq_zero {z : CliffordVector t K}
    (hz : cliffordPairing z z = 0) : signedCliffordAction z * signedCliffordAction z = 0 := by
  have h := signedCliffordAction_car z z
  rw [hz, zero_smul] at h
  have h' : (2 : K) • (signedCliffordAction z * signedCliffordAction z) = 0 := by
    simpa [two_smul] using h
  exact (smul_eq_zero.mp h').resolve_left (by norm_num)

/-- The common kernel can be checked on any basis of the actual subspace. -/
theorem cliffordJointKernel_eq_basis {ι : Type*} [Fintype ι]
    (L : Submodule K (CliffordVector t K)) (b : Module.Basis ι K L) :
    cliffordJointKernel L = ⨅ i, LinearMap.ker (signedCliffordAction (b i : CliffordVector t K)) := by
  ext u
  simp only [mem_cliffordJointKernel, Submodule.mem_iInf, LinearMap.mem_ker]
  constructor
  · intro h i
    exact h (b i) (b i).property
  · intro h z hz
    let v : L := ⟨z, hz⟩
    have heq : z = ∑ i, (b.repr v i) • (b i : CliffordVector t K) := by
      change (v : CliffordVector t K) = _
      conv_lhs => rw [← b.sum_repr v]
      simp only [Submodule.coe_sum, Submodule.coe_smul]
    rw [heq]
    change cliffordAtSpinor u _ = 0
    simp only [map_sum, map_smul, cliffordAtSpinor_apply, h, smul_zero, Finset.sum_const_zero]

/-- General common-annihilator dimension, with no assumed normal form. -/
theorem cliffordJointKernel_finrank_mul (L : Submodule K (CliffordVector t K))
    (hL : CliffordIsotropic L) :
    2 ^ Module.finrank K L * Module.finrank K (cliffordJointKernel L) = 2 ^ t := by
  let b := Module.finBasis K L
  obtain ⟨w, hw⟩ := exists_cliffordPairing_dual_basis L b
  let A := fun i => signedCliffordAction (b i : CliffordVector t K)
  let B := fun i => signedCliffordAction (w i)
  have hsq i : A i * A i = 0 := signedCliffordAction_sq_zero (hL _ (b i).property _ (b i).property)
  have hAA i j : A i * A j + A j * A i = 0 := by
    simpa only [hL _ (b i).property _ (b j).property, zero_smul] using
      signedCliffordAction_car (b i : CliffordVector t K) (b j : CliffordVector t K)
  have hAB i j : A i * B j + B j * A i = if i = j then 1 else 0 := by
    have h := signedCliffordAction_car (b i : CliffordVector t K) (w j)
    rw [hw] at h
    by_cases hij : i = j <;> simpa [hij] using h
  have hdim := finrank_eq_pow_mul_jointKernel A B hsq hAA hAB
  rw [cliffordJointKernel_eq_basis L b]
  change 2 ^ Module.finrank K L * Module.finrank K (operatorJointKernel A) = _
  rw [← hdim]
  simp [SubsetSignature]

/-- Source dimension formula for an isotropic subspace of codimension parameter `r`. -/
theorem cliffordJointKernel_finrank (L : Submodule K (CliffordVector t K))
    (hL : CliffordIsotropic L) {r : ℕ} (hr : r ≤ t)
    (hdim : Module.finrank K L = t - r) :
    Module.finrank K (cliffordJointKernel L) = 2 ^ r := by
  have h := cliffordJointKernel_finrank_mul L hL
  rw [hdim] at h
  apply Nat.eq_of_mul_eq_mul_left (Nat.two_pow_pos (t - r))
  rw [h, ← pow_add, Nat.sub_add_cancel hr]

/-- Every isotropic common kernel is the range of an explicit finite product
of actual Clifford-vector operators. The factors are constructed from a basis
and extended dual coordinate functionals. -/
theorem exists_signedClifford_jointKernel_product
    (L : Submodule K (CliffordVector t K)) (hL : CliffordIsotropic L) :
    ∃ a b : Fin (Module.finrank K L) → CliffordVector t K,
      LinearMap.range (fermionicKernelProjector
        (fun i => signedCliffordAction (a i)) (fun i => signedCliffordAction (b i))) =
        cliffordJointKernel L := by
  let a := Module.finBasis K L
  obtain ⟨b, hb⟩ := exists_cliffordPairing_dual_basis L a
  refine ⟨fun i => a i, b, ?_⟩
  rw [fermionicKernelProjector_range]
  · exact (cliffordJointKernel_eq_basis L a).symm
  · intro i
    exact signedCliffordAction_sq_zero (hL _ (a i).property _ (a i).property)
  · intro i j
    simpa only [hL _ (a i).property _ (a j).property, zero_smul] using
      signedCliffordAction_car (a i : CliffordVector t K) (a j : CliffordVector t K)
  · intro i j
    have h := signedCliffordAction_car (a i : CliffordVector t K) (b j)
    rw [hb] at h
    by_cases hij : i = j <;> simpa [hij] using h

end
end MatchgateWidth
