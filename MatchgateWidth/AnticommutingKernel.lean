import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Tactic

/-!
# Dimension of a common fermionic kernel

A finite collection of square-zero annihilators with dual anticommuting
operators cuts dimension by exactly two for each annihilator. No canonical
form, spin-group lift, or nonzero common vector is assumed.
-/
namespace MatchgateWidth
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Joint kernel of a finite indexed operator family. -/
def operatorJointKernel {n : ℕ} (A : Fin n → Module.End K V) : Submodule K V :=
  ⨅ i, LinearMap.ker (A i)

@[simp] theorem mem_operatorJointKernel {n : ℕ} (A : Fin n → Module.End K V) (u : V) :
    u ∈ operatorJointKernel A ↔ ∀ i, A i u = 0 := by
  simp [operatorJointKernel]

/-- Square-zero and a dual anticommutator force range to equal kernel. -/
theorem range_eq_ker_of_anticommutator (A B : Module.End K V)
    (hA : A * A = 0) (hAB : A * B + B * A = 1) : LinearMap.range A = LinearMap.ker A := by
  apply le_antisymm
  · rintro _ ⟨v, rfl⟩
    change A (A v) = 0
    exact congrArg (fun f : Module.End K V => f v) hA
  · intro v hv
    refine ⟨B v, ?_⟩
    have h := congrArg (fun f : Module.End K V => f v) hAB
    simpa only [LinearMap.add_apply, Module.End.mul_apply, Module.End.one_apply,
      show A v = 0 from hv, map_zero, add_zero] using h

/-- One genuine fermionic annihilator has a half-dimensional kernel. -/
theorem finrank_eq_two_mul_ker [FiniteDimensional K V] (A B : Module.End K V)
    (hA : A * A = 0) (hAB : A * B + B * A = 1) :
    Module.finrank K V = 2 * Module.finrank K (LinearMap.ker A) := by
  have h := LinearMap.finrank_range_add_finrank_ker A
  rw [range_eq_ker_of_anticommutator A B hA hAB] at h
  omega

/-- Restriction of an operator preserving a specified kernel. -/
def restrictToKernel (Z A : Module.End K V)
    (h : ∀ v, Z v = 0 → Z (A v) = 0) : Module.End K (LinearMap.ker Z) where
  toFun v := ⟨A v, h v v.property⟩
  map_add' v w := Subtype.ext (map_add A (v : V) (w : V))
  map_smul' c v := Subtype.ext (map_smul A c (v : V))

@[simp] theorem restrictToKernel_apply (Z A : Module.End K V)
    (h : ∀ v, Z v = 0 → Z (A v) = 0) (v : LinearMap.ker Z) :
    (restrictToKernel Z A h v : V) = A v := rfl

private theorem preserves_kernel_of_anticommute (Z A : Module.End K V)
    (h : Z * A + A * Z = 0) (v : V) (hv : Z v = 0) : Z (A v) = 0 := by
  have h' := congrArg (fun f : Module.End K V => f v) h
  simpa only [LinearMap.add_apply, Module.End.mul_apply, hv, map_zero, add_zero,
    LinearMap.zero_apply] using h'

/-- Every independent fermionic annihilator cuts dimension by a factor of two.
The dual operators need not square to zero or anticommute with one another. -/
theorem finrank_eq_pow_mul_jointKernel [FiniteDimensional K V] {n : ℕ}
    (A B : Fin n → Module.End K V)
    (hsq : ∀ i, A i * A i = 0)
    (hAA : ∀ i j, A i * A j + A j * A i = 0)
    (hAB : ∀ i j, A i * B j + B j * A i = if i = j then 1 else 0) :
    Module.finrank K V = 2 ^ n * Module.finrank K (operatorJointKernel A) := by
  induction n generalizing V with
  | zero =>
    have heq : operatorJointKernel A = ⊤ := by
      apply top_unique
      intro v _
      exact (mem_operatorJointKernel A v).mpr (fun i => Fin.elim0 i)
    rw [heq]
    simp only [pow_zero, one_mul, finrank_top]
  | succ n ih =>
    let Z := A 0
    have hAk (i : Fin n) : ∀ v, Z v = 0 → Z (A i.succ v) = 0 :=
      preserves_kernel_of_anticommute Z (A i.succ) (hAA 0 i.succ)
    have hBk (i : Fin n) : ∀ v, Z v = 0 → Z (B i.succ v) = 0 := by
      apply preserves_kernel_of_anticommute
      have hn : (0 : Fin (n + 1)) ≠ i.succ := (Fin.succ_ne_zero i).symm
      simpa only [ite_eq_right_iff, ite_false, hn] using hAB 0 i.succ
    let A' : Fin n → Module.End K (LinearMap.ker Z) :=
      fun i => restrictToKernel Z (A i.succ) (hAk i)
    let B' : Fin n → Module.End K (LinearMap.ker Z) :=
      fun i => restrictToKernel Z (B i.succ) (hBk i)
    have hsq' (i : Fin n) : A' i * A' i = 0 := by
      apply LinearMap.ext
      intro v
      apply Subtype.ext
      exact congrArg (fun f : Module.End K V => f v) (hsq i.succ)
    have hAA' (i j : Fin n) : A' i * A' j + A' j * A' i = 0 := by
      apply LinearMap.ext
      intro v
      apply Subtype.ext
      exact congrArg (fun f : Module.End K V => f v) (hAA i.succ j.succ)
    have hAB' (i j : Fin n) : A' i * B' j + B' j * A' i = if i = j then 1 else 0 := by
      apply LinearMap.ext
      intro v
      apply Subtype.ext
      have h := congrArg (fun f : Module.End K V => f v) (hAB i.succ j.succ)
      by_cases hij : i = j
      · subst j
        simp only [ite_true]
        change A i.succ (B i.succ v) + B i.succ (A i.succ v) = (v : V)
        simpa only [ite_true, LinearMap.add_apply, Module.End.mul_apply, Module.End.one_apply] using h
      · simp only [hij, ite_false]
        change A i.succ (B j.succ v) + B j.succ (A i.succ v) = 0
        simpa only [Fin.succ_inj, hij, ite_false, LinearMap.add_apply,
          Module.End.mul_apply, LinearMap.zero_apply] using h
    let e : operatorJointKernel A ≃ₗ[K] operatorJointKernel A' :=
      { toFun := fun u => ⟨⟨u, (mem_operatorJointKernel A u).mp u.property 0⟩,
          (mem_operatorJointKernel A' _).mpr (fun i => Subtype.ext
            ((mem_operatorJointKernel A u).mp u.property i.succ))⟩
        invFun := fun u => ⟨u.val.val, (mem_operatorJointKernel A _).mpr (fun i => by
          induction i using Fin.cases with
          | zero => exact u.val.property
          | succ i =>
            exact congrArg Subtype.val ((mem_operatorJointKernel A' u).mp u.property i))⟩
        left_inv := fun u => rfl
        right_inv := fun u => rfl
        map_add' := fun u v => rfl
        map_smul' := fun c u => rfl }
    calc
      Module.finrank K V = 2 * Module.finrank K (LinearMap.ker Z) :=
        finrank_eq_two_mul_ker Z (B 0) (hsq 0) (by simpa using hAB 0 0)
      _ = 2 * (2 ^ n * Module.finrank K (operatorJointKernel A')) := by
        rw [ih A' B' hsq' hAA' hAB']
      _ = 2 ^ (n + 1) * Module.finrank K (operatorJointKernel A) := by
        rw [← e.finrank_eq, pow_succ]
        ring

/-- Ordered product of the elementary annihilator projections. -/
def fermionicKernelProjector : {n : ℕ} →
    (Fin n → Module.End K V) → (Fin n → Module.End K V) → Module.End K V
  | 0, _, _ => 1
  | n + 1, A, B => A 0 * B 0 *
      fermionicKernelProjector (fun i : Fin n => A i.succ) (fun i : Fin n => B i.succ)

private theorem commute_pair_of_anticommute (Z A B : Module.End K V)
    (hA : Z * A + A * Z = 0) (hB : Z * B + B * Z = 0) :
    Z * (A * B) = (A * B) * Z := by
  have hA' : Z * A = -(A * Z) := eq_neg_iff_add_eq_zero.mpr hA
  have hB' : Z * B = -(B * Z) := eq_neg_iff_add_eq_zero.mpr hB
  calc
    Z * (A * B) = (Z * A) * B := (mul_assoc _ _ _).symm
    _ = -(A * (Z * B)) := by rw [hA', neg_mul, mul_assoc]
    _ = (A * B) * Z := by rw [hB', mul_neg, neg_neg, mul_assoc]

/-- The explicit ordered product lands in the true common kernel and fixes it. -/
theorem fermionicKernelProjector_spec {n : ℕ} (A B : Fin n → Module.End K V)
    (hsq : ∀ i, A i * A i = 0)
    (hAA : ∀ i j, A i * A j + A j * A i = 0)
    (hAB : ∀ i j, A i * B j + B j * A i = if i = j then 1 else 0) :
    (∀ v, fermionicKernelProjector A B v ∈ operatorJointKernel A) ∧
      (∀ v ∈ operatorJointKernel A, fermionicKernelProjector A B v = v) := by
  induction n with
  | zero =>
    constructor
    · intro v; exact (mem_operatorJointKernel A v).mpr (fun i => Fin.elim0 i)
    · intro v _; rfl
  | succ n ih =>
    let At := fun i : Fin n => A i.succ
    let Bt := fun i : Fin n => B i.succ
    obtain ⟨hland, hfix⟩ := ih At Bt (fun i => hsq i.succ)
      (fun i j => hAA i.succ j.succ) (fun i j => by simpa [At, Bt] using hAB i.succ j.succ)
    constructor
    · intro v
      apply (mem_operatorJointKernel A _).mpr
      intro i
      induction i using Fin.cases with
      | zero =>
        change A 0 (A 0 (B 0 (fermionicKernelProjector At Bt v))) = 0
        exact congrArg (fun f : Module.End K V => f (B 0 (fermionicKernelProjector At Bt v))) (hsq 0)
      | succ i =>
        have hcomm := commute_pair_of_anticommute (A i.succ) (A 0) (B 0)
          (hAA i.succ 0) (by simpa using hAB i.succ 0)
        have h := congrArg (fun f : Module.End K V => f (fermionicKernelProjector At Bt v)) hcomm
        change A i.succ (A 0 (B 0 (fermionicKernelProjector At Bt v))) = 0
        rw [show A i.succ (A 0 (B 0 (fermionicKernelProjector At Bt v))) =
          A 0 (B 0 (A i.succ (fermionicKernelProjector At Bt v))) from h]
        rw [(mem_operatorJointKernel At _).mp (hland v) i, map_zero, map_zero]
    · intro v hv
      have ht : v ∈ operatorJointKernel At :=
        (mem_operatorJointKernel At v).mpr (fun i => (mem_operatorJointKernel A v).mp hv i.succ)
      change A 0 (B 0 (fermionicKernelProjector At Bt v)) = v
      rw [hfix v ht]
      have h := congrArg (fun f : Module.End K V => f v) (hAB 0 0)
      simpa only [ite_true, LinearMap.add_apply, Module.End.mul_apply, Module.End.one_apply,
        (mem_operatorJointKernel A v).mp hv 0, map_zero, add_zero] using h

/-- The range of the explicit Clifford product equals, rather than merely contains,
the full joint kernel. -/
theorem fermionicKernelProjector_range {n : ℕ} (A B : Fin n → Module.End K V)
    (hsq : ∀ i, A i * A i = 0)
    (hAA : ∀ i j, A i * A j + A j * A i = 0)
    (hAB : ∀ i j, A i * B j + B j * A i = if i = j then 1 else 0) :
    LinearMap.range (fermionicKernelProjector A B) = operatorJointKernel A := by
  obtain ⟨hland, hfix⟩ := fermionicKernelProjector_spec A B hsq hAA hAB
  apply le_antisymm
  · rintro _ ⟨v, rfl⟩; exact hland v
  · intro v hv; exact ⟨v, hfix v hv⟩

end
end MatchgateWidth
