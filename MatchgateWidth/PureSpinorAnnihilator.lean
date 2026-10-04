import MatchgateWidth.GeneralIsotropicKernelCover
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

/-! # Pure spinors and the literal matchgate identities
The annihilator is defined using the actual signed creation/contraction action.
The split bilinear form and its coefficient vectors identify the MGI equations
with isotropy of the dual image. No pure-spinor classification is assumed.
-/
namespace MatchgateWidth
noncomputable section
open scoped symmDiff
variable {R : Type*} [CommRing R] {t : ℕ}

theorem cliffordPairing_add_left (z w v : CliffordVector t R) :
    cliffordPairing (z+w) v = cliffordPairing z v + cliffordPairing w v := by
  simp only [cliffordPairing, Prod.fst_add, Prod.snd_add, Pi.add_apply, add_mul, mul_add,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem cliffordPairing_smul_left (c : R) (z w : CliffordVector t R) :
    cliffordPairing (c • z) w = c * cliffordPairing z w := by
  simp only [cliffordPairing, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem cliffordPairing_comm (z w : CliffordVector t R) :
    cliffordPairing z w = cliffordPairing w z := by
  unfold cliffordPairing
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The actual split pairing, packaged as a bilinear form. -/
def cliffordBilinForm : LinearMap.BilinForm R (CliffordVector t R) where
  toFun z :=
    { toFun := cliffordPairing z
      map_add' w v := by simp only [cliffordPairing_comm z, cliffordPairing_add_left]
      map_smul' c w := by simp only [cliffordPairing_comm z, cliffordPairing_smul_left, smul_eq_mul, RingHom.id_apply] }
  map_add' z w := by apply LinearMap.ext; intro v; exact cliffordPairing_add_left z w v
  map_smul' c z := by apply LinearMap.ext; intro w; exact cliffordPairing_smul_left c z w

@[simp] theorem cliffordBilinForm_apply (z w : CliffordVector t R) :
    cliffordBilinForm z w = cliffordPairing z w := rfl

@[simp] theorem cliffordPairing_creation (z : CliffordVector t R) (i : Fin t) :
    cliffordPairing z (cliffordCreationVector i) = z.2 i := by
  simp [cliffordPairing, cliffordCreationVector, Pi.single_apply]

@[simp] theorem cliffordPairing_contraction (z : CliffordVector t R) (i : Fin t) :
    cliffordPairing z (cliffordContractionVector i) = z.1 i := by
  simp [cliffordPairing, cliffordContractionVector, Pi.single_apply]

/-- Nondegeneracy follows by testing the named creation and contraction vectors. -/
theorem cliffordBilinForm_nondegenerate :
    (cliffordBilinForm (R := R) (t := t)).Nondegenerate := by
  have hleft : (cliffordBilinForm (R := R) (t := t)).SeparatingLeft := by
    intro z hz
    apply Prod.ext
    · ext i
      exact cliffordPairing_contraction z i ▸ hz (cliffordContractionVector i)
    · ext i
      exact cliffordPairing_creation z i ▸ hz (cliffordCreationVector i)
  refine ⟨hleft, ?_⟩
  intro z hz
  apply hleft z
  intro w
  rw [cliffordBilinForm_apply, cliffordPairing_comm]
  exact hz w

/-- The pairing-dual of one coefficient functional of the spinor action. -/
def spinorCoefficientVector (u : SubsetSignature t R) (S : Finset (Fin t)) : CliffordVector t R :=
  (fun i => fermionContract i u S, fun i => fermionCreate i u S)

/-- Pairing against the coefficient vector recovers the literal action coefficient. -/
theorem cliffordPairing_coefficient (u : SubsetSignature t R) (S : Finset (Fin t))
    (z : CliffordVector t R) :
    cliffordPairing z (spinorCoefficientVector u S) = signedCliffordAction z u S := by
  simp [cliffordPairing, spinorCoefficientVector, signedCliffordAction,
    Finset.sum_apply, mul_comm]

/-- The coefficient-vector pairing is precisely the negative alternating MGI sum. -/
theorem cliffordPairing_coefficient_coefficient (u : SubsetSignature t R)
    (A B : Finset (Fin t)) :
    cliffordPairing (spinorCoefficientVector u A) (spinorCoefficientVector u B) =
      -matchgateSum u A B ((A ∆ B).sort (· ≤ ·)) := by
  rw [matchgateSum_eq_neg_sum, neg_neg]
  unfold cliffordPairing spinorCoefficientVector
  calc
    _ = ∑ i : Fin t, if i ∈ A ∆ B then
        (-1 : R) ^ subsetBelow (A ∆ B) i * u (A ∆ {i}) * u (B ∆ {i}) else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← subsetBelow_sign_symmDiff]
      by_cases hi : i ∈ A <;> by_cases hj : i ∈ B <;>
        simp [fermionCreate_apply, fermionContract_apply, Finset.mem_symmDiff, hi, hj, fermionSign] <;> ring
    _ = _ := by simp

/-- The space of all coefficient-duals of the actual action on a spinor. -/
def spinorCoefficientSpace (u : SubsetSignature t R) : Submodule R (CliffordVector t R) :=
  Submodule.span R (Set.range (spinorCoefficientVector u))

/-- Generator-wise isotropy extends to the actual linear span. -/
theorem CliffordIsotropic.span {s : Set (CliffordVector t R)}
    (h : ∀ z ∈ s, ∀ w ∈ s, cliffordPairing z w = 0) :
    CliffordIsotropic (Submodule.span R s) := by
  intro z hz
  induction hz using Submodule.span_induction with
  | mem z hz =>
    intro w hw
    induction hw using Submodule.span_induction with
    | mem w hw => exact h z hz w hw
    | zero => simp [cliffordPairing]
    | add w v hw hv ihw ihv =>
      change cliffordBilinForm z (w+v) = 0
      simp only [map_add, cliffordBilinForm_apply, ihw, ihv, add_zero]
    | smul c w hw ih =>
      change cliffordBilinForm z (c • w) = 0
      simp only [map_smul, cliffordBilinForm_apply, ih, smul_zero]
  | zero => intro w _; simp [cliffordPairing]
  | add z v hz hv ihz ihv =>
    intro w hw
    rw [cliffordPairing_add_left, ihz w hw, ihv w hw, add_zero]
  | smul c z hz ih =>
    intro w hw
    rw [cliffordPairing_smul_left, ih w hw, mul_zero]

/-- The full MGI imply isotropy of the coefficient-dual image. -/
theorem MatchgateIdentities.coefficientSpace_isotropic {u : SubsetSignature t R}
    (hu : MatchgateIdentities u) : CliffordIsotropic (spinorCoefficientSpace u) := by
  apply CliffordIsotropic.span
  rintro _ ⟨A, rfl⟩ _ ⟨B, rfl⟩
  rw [cliffordPairing_coefficient_coefficient, hu, neg_zero]

/-- The genuine annihilator is exactly the orthogonal of the coefficient-dual image. -/
theorem spinorAnnihilator_eq_orthogonal (u : SubsetSignature t R) :
    spinorAnnihilator u = cliffordBilinForm.orthogonal (spinorCoefficientSpace u) := by
  ext z
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  constructor
  · intro hz w hw
    have hz' : signedCliffordAction z u = 0 := hz
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨S, rfl⟩ := hw
      rw [cliffordBilinForm_apply, cliffordPairing_comm, cliffordPairing_coefficient, hz']
      rfl
    | zero => simp
    | add w v hw hv ihw ihv => simp [ihw, ihv]
    | smul c w hw ih => simp [ih]
  · intro hz
    change signedCliffordAction z u = 0
    ext S
    have h := hz (spinorCoefficientVector u S) (Submodule.subset_span ⟨S, rfl⟩)
    rwa [cliffordBilinForm_apply, cliffordPairing_comm, cliffordPairing_coefficient] at h

variable {K : Type*} [Field K] [CharZero K]

/-- No isotropic subspace of the split space can exceed dimension `t`. -/
theorem CliffordIsotropic.finrank_le {L : Submodule K (CliffordVector t K)}
    (hL : CliffordIsotropic L) : Module.finrank K L ≤ t := by
  have h := cliffordJointKernel_finrank_mul L hL
  have hp : 0 < Module.finrank K (cliffordJointKernel L) := by
    by_contra hn
    have heq : Module.finrank K (cliffordJointKernel L) = 0 := by omega
    rw [heq, mul_zero] at h
    exact (Nat.ne_of_gt (Nat.two_pow_pos t)) h.symm
  have hpow : 2 ^ Module.finrank K L ≤ 2 ^ t := by
    calc
      _ = 2 ^ Module.finrank K L * 1 := by simp
      _ ≤ 2 ^ Module.finrank K L * Module.finrank K (cliffordJointKernel L) := Nat.mul_le_mul_left _ hp
      _ = _ := h
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hpow

/-- Literal nonzero MGI spinors have the full `t`-dimensional annihilator. -/
theorem MatchgateIdentities.annihilator_finrank {u : SubsetSignature t K}
    (hu : MatchgateIdentities u) (hne : u ≠ 0) :
    Module.finrank K (spinorAnnihilator u) = t := by
  have hAnn := (spinorAnnihilator_isotropic hne).finrank_le
  have hCoeff := hu.coefficientSpace_isotropic.finrank_le
  rw [spinorAnnihilator_eq_orthogonal,
    LinearMap.BilinForm.finrank_orthogonal cliffordBilinForm_nondegenerate]
  have hdim : Module.finrank K (CliffordVector t K) = 2 * t := by
    simp [CliffordVector, Module.finrank_prod,  two_mul]
  rw [hdim]
  rw [spinorAnnihilator_eq_orthogonal,
    LinearMap.BilinForm.finrank_orthogonal cliffordBilinForm_nondegenerate, hdim] at hAnn
  omega

/-- Full annihilator dimension forces the literal MGI, using the proved
zero-input isotropic-kernel cover, not an assumed pure-spinor classification. -/
theorem matchgateIdentities_of_annihilator_finrank {u : SubsetSignature t K}
    (hne : u ≠ 0) (hdim : Module.finrank K (spinorAnnihilator u) = t) :
    MatchgateIdentities u := by
  obtain ⟨P, hP, _, hrow⟩ := isotropic_kernel_cover (spinorAnnihilator u)
    (spinorAnnihilator_isotropic hne) (Nat.zero_le t) (by simpa using hdim)
  have hker : u ∈ cliffordJointKernel (spinorAnnihilator u) := by
    rw [mem_cliffordJointKernel]
    intro z hz
    exact hz
  rw [← hrow] at hker
  obtain ⟨v, hv, hveq⟩ := hker
  let x₀ : BooleanInput 0 := fun _ => 0
  have hx (x : BooleanInput 0) : x = x₀ := by
    funext i
    exact Fin.elim0 i
  have hrange : Set.range P.row = {P.row x₀} := by
    ext w
    constructor
    · rintro ⟨x, rfl⟩
      rw [hx x]
      exact Set.mem_singleton _
    · intro h
      exact ⟨x₀, (Set.mem_singleton_iff.mp h).symm⟩
  change v ∈ Submodule.span K (Set.range P.row) at hv
  rw [hrange, Submodule.mem_span_singleton] at hv
  obtain ⟨c, hcv⟩ := hv
  have hvmgi := (hP.row x₀).smul c
  rw [hcv] at hvmgi
  change MatchgateIdentities (spinorSubsetEquiv v) at hvmgi
  change spinorSubsetEquiv v = u at hveq
  rwa [hveq] at hvmgi

/-- Source pure-spinor condition in the fixed ordered exterior coefficient basis. -/
def IsPureSpinor (u : SubsetSignature t K) : Prop :=
  u ≠ 0 ∧ Module.finrank K (spinorAnnihilator u) = t

/-- The exact pure-spinor/MGI equivalence, including an explicit nonzero condition. -/
theorem isPureSpinor_iff_matchgateIdentities (u : SubsetSignature t K) :
    IsPureSpinor u ↔ u ≠ 0 ∧ MatchgateIdentities u := by
  constructor
  · rintro ⟨hne, hdim⟩
    exact ⟨hne, matchgateIdentities_of_annihilator_finrank hne hdim⟩
  · rintro ⟨hne, hmgi⟩
    exact ⟨hne, hmgi.annihilator_finrank hne⟩

/-- Every pure complex spinor has an exact certified disk realization in the
specified increasing-subset coefficient basis. -/
theorem IsPureSpinor.diskRealizable {u : SubsetSignature t ℂ} (hu : IsPureSpinor u) :
    DiskRealizable (fun y => u ((booleanSubsetEquiv t) ((booleanWordEquiv t).symm y))) := by
  have hmgi := (isPureSpinor_iff_matchgateIdentities u).mp hu |>.2
  have hbool : BooleanMatchgateIdentities (fun x => u ((booleanSubsetEquiv t) x)) := by
    simpa only [BooleanMatchgateIdentities, Equiv.apply_symm_apply] using hmgi
  exact hbool.diskRealizable

end
end MatchgateWidth
