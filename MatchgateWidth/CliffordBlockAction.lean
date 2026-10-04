import MatchgateWidth.PureSpinorAnnihilator

/-! # Actual Clifford action across a consecutive tensor cut
Output-only Clifford vectors act on every coefficient slice, with precisely
the Koszul sign of the selected input prefix. This is the coordinate interface
needed to compute common annihilators without assuming Pin covariance.
-/
namespace MatchgateWidth
noncomputable section
open scoped symmDiff
variable {R : Type*} [CommRing R] {m t : ℕ}

/-- Direct coefficient formula for the full signed action. -/
theorem signedCliffordAction_apply (z : CliffordVector t R) (u : SubsetSignature t R)
    (S : Finset (Fin t)) :
    signedCliffordAction z u S = ∑ i : Fin t, fermionSign S i *
      (if i ∈ S then z.1 i else z.2 i) * u (S ∆ {i}) := by
  simp only [signedCliffordAction, LinearMap.sum_apply, LinearMap.add_apply,
    LinearMap.smul_apply, Pi.add_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul,
    fermionCreate_apply, fermionContract_apply]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i ∈ S <;> simp [hi] <;> ring

/-- Embedding of an output Clifford vector, with zero input components. -/
def cliffordOutputEmbedding : CliffordVector t R →ₗ[R] CliffordVector (m+t) R where
  toFun z := (Fin.addCases (fun _ => 0) z.1, Fin.addCases (fun _ => 0) z.2)
  map_add' z w := by
    apply Prod.ext <;> funext i <;> induction i using Fin.addCases <;> simp
  map_smul' c z := by
    apply Prod.ext <;> funext i <;> induction i using Fin.addCases <;> simp

/-- Restriction to the input vector and covector components. -/
def cliffordInputProjection : CliffordVector (m+t) R →ₗ[R] CliffordVector m R where
  toFun z := (fun i => z.1 (Fin.castAdd t i), fun i => z.2 (Fin.castAdd t i))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Restriction to the output vector and covector components. -/
def cliffordOutputProjection : CliffordVector (m+t) R →ₗ[R] CliffordVector t R where
  toFun z := (fun i => z.1 (Fin.natAdd m i), fun i => z.2 (Fin.natAdd m i))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem cliffordOutputProjection_embedding (z : CliffordVector t R) :
    cliffordOutputProjection (m := m) (cliffordOutputEmbedding z) = z := by
  apply Prod.ext <;> funext i <;> simp [cliffordOutputProjection, cliffordOutputEmbedding]

@[simp] theorem cliffordInputProjection_embedding (z : CliffordVector t R) :
    cliffordInputProjection (m := m) (cliffordOutputEmbedding z) = 0 := by
  apply Prod.ext <;> funext i <;> simp [cliffordInputProjection, cliffordOutputEmbedding]

theorem cliffordOutputEmbedding_projection {z : CliffordVector (m+t) R}
    (hz : cliffordInputProjection z = 0) :
    cliffordOutputEmbedding (cliffordOutputProjection z) = z := by
  have h₁ := congrArg Prod.fst hz
  have h₂ := congrArg Prod.snd hz
  apply Prod.ext
  · funext i
    induction i using Fin.addCases with
    | left i => simpa [cliffordOutputEmbedding, cliffordInputProjection] using (congrFun h₁ i).symm
    | right i => simp [cliffordOutputEmbedding, cliffordOutputProjection]
  · funext i
    induction i using Fin.addCases with
    | left i => simpa [cliffordOutputEmbedding, cliffordInputProjection] using (congrFun h₂ i).symm
    | right i => simp [cliffordOutputEmbedding, cliffordOutputProjection]

/-- Koszul position in the output block includes the entire selected input prefix. -/
theorem subsetBelow_blockJoin_right (X : Finset (Fin m)) (Y : Finset (Fin t))
    (i : Fin t) : subsetBelow (blockJoin X Y) (Fin.natAdd m i) = X.card + subsetBelow Y i := by
  have heq : (blockJoin X Y).filter (· < Fin.natAdd m i) = blockJoin X (Y.filter (· < i)) := by
    ext j
    induction j using Fin.addCases with
    | left j =>
      simp only [Finset.mem_filter, ← mem_firstBlock, firstBlock_blockJoin, and_iff_left_iff_imp]
      intro _
      have := j.isLt
      change j.val < m + i.val
      omega
    | right j =>
      simp only [Finset.mem_filter, ← mem_secondBlock, secondBlock_blockJoin, Fin.natAdd_lt_natAdd_iff]
  simp only [subsetBelow, heq, blockJoin_card]

/-- Actual output-only action on a tensor is its slice action with one common
invertible Koszul sign. No parity hypothesis is needed. -/
theorem signedCliffordAction_output_block
    (z : CliffordVector t R) (F : SubsetSignature (m+t) R)
    (X : Finset (Fin m)) (Y : Finset (Fin t)) :
    signedCliffordAction (cliffordOutputEmbedding z) F (blockJoin X Y) =
      (-1 : R)^X.card * signedCliffordAction z (fun T => F (blockJoin X T)) Y := by
  rw [signedCliffordAction_apply, Fin.sum_univ_add]
  simp only [cliffordOutputEmbedding, LinearMap.coe_mk, AddHom.coe_mk, Fin.addCases_left,
    Fin.addCases_right, ite_self, mul_zero, zero_mul, Finset.sum_const_zero, zero_add]
  rw [signedCliffordAction_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [← mem_secondBlock, secondBlock_blockJoin, blockJoin_flip_right,
    fermionSign, subsetBelow_blockJoin_right, pow_add]
  ring

/-- Common annihilator of all output coefficient slices across the chosen cut. -/
def sliceCommonAnnihilator (F : SubsetSignature (m+t) R) : Submodule R (CliffordVector t R) :=
  ⨅ X : Finset (Fin m), spinorAnnihilator (fun Y => F (blockJoin X Y))

@[simp] theorem mem_sliceCommonAnnihilator (F : SubsetSignature (m+t) R) (z : CliffordVector t R) :
    z ∈ sliceCommonAnnihilator F ↔ ∀ X, signedCliffordAction z (fun Y => F (blockJoin X Y)) = 0 := by
  simp [sliceCommonAnnihilator, spinorAnnihilator]

/-- Output-only annihilation of the entire tensor equals simultaneous annihilation
of every slice, in actual signed coefficients. -/
theorem outputEmbedding_mem_annihilator_iff
    (F : SubsetSignature (m+t) R) (z : CliffordVector t R) :
    cliffordOutputEmbedding z ∈ spinorAnnihilator F ↔ z ∈ sliceCommonAnnihilator F := by
  rw [mem_sliceCommonAnnihilator]
  change signedCliffordAction (cliffordOutputEmbedding z) F = 0 ↔ _
  constructor
  · intro h X
    ext Y
    have h' := congrFun h (blockJoin X Y)
    rw [signedCliffordAction_output_block] at h'
    exact (neg_one_pow_mul_eq_zero_iff).mp h'
  · intro h
    ext S
    have hS : blockJoin (firstBlock S) (secondBlock S) = S := by
      ext i
      induction i using Fin.addCases <;> simp [← mem_firstBlock, ← mem_secondBlock]
    rw [← hS, signedCliffordAction_output_block, h]
    simp

/-- The full split pairing restricts to the output pairing without distortion. -/
theorem cliffordPairing_outputEmbedding (z w : CliffordVector t R) :
    cliffordPairing (cliffordOutputEmbedding (m := m) z) (cliffordOutputEmbedding w) =
      cliffordPairing z w := by
  rw [cliffordPairing, Fin.sum_univ_add]
  simp [cliffordOutputEmbedding, cliffordPairing]

/-- Common output annihilators are exactly the total annihilators with zero
input components, via an explicit linear equivalence. -/
def sliceCommonAnnihilatorEquiv (F : SubsetSignature (m+t) R) :
    sliceCommonAnnihilator F ≃ₗ[R]
      LinearMap.ker ((cliffordInputProjection (m := m) (t := t)).comp (spinorAnnihilator F).subtype) where
  toFun z := ⟨⟨cliffordOutputEmbedding z,
      (outputEmbedding_mem_annihilator_iff F z).mpr z.property⟩,
    by change cliffordInputProjection (cliffordOutputEmbedding z.val) = 0
       exact cliffordInputProjection_embedding z.val⟩
  invFun z := ⟨cliffordOutputProjection z.val.val, by
    apply (outputEmbedding_mem_annihilator_iff F _).mp
    rw [cliffordOutputEmbedding_projection (show cliffordInputProjection z.val.val = 0 from z.property)]
    exact z.val.property⟩
  left_inv z := by
    apply Subtype.ext
    change cliffordOutputProjection (cliffordOutputEmbedding z.val) = z.val
    exact cliffordOutputProjection_embedding (m := m) z.val
  right_inv z := Subtype.ext (Subtype.ext
    (cliffordOutputEmbedding_projection (show cliffordInputProjection z.val.val = 0 from z.property)))
  map_add' z w := Subtype.ext (Subtype.ext (map_add cliffordOutputEmbedding z.val w.val))
  map_smul' c z := Subtype.ext (Subtype.ext (map_smul cliffordOutputEmbedding c z.val))

variable {K : Type*} [Field K] [CharZero K]

/-- A nonzero tensor's common output annihilator is isotropic, independently
of whether the tensor satisfies MGI. -/
theorem sliceCommonAnnihilator_isotropic {F : SubsetSignature (m+t) K} (hne : F ≠ 0) :
    CliffordIsotropic (sliceCommonAnnihilator F) := by
  intro z hz w hw
  rw [← cliffordPairing_outputEmbedding (m := m)]
  exact spinorAnnihilator_isotropic hne _ ((outputEmbedding_mem_annihilator_iff F z).mpr hz)
    _ ((outputEmbedding_mem_annihilator_iff F w).mpr hw)

/-- A pure tensor across an `m|t` cut has at least `t-m` common output
annihilators. The loss of at most `2m` dimensions is the ordinary input
vector/covector projection, with all signs proved above. -/
theorem MatchgateIdentities.sliceCommonAnnihilator_finrank_ge
    {F : SubsetSignature (m+t) K} (hF : MatchgateIdentities F) (hne : F ≠ 0) :
    t - m ≤ Module.finrank K (sliceCommonAnnihilator F) := by
  let q := (cliffordInputProjection (m := m) (t := t)).comp (spinorAnnihilator F).subtype
  have hdim := hF.annihilator_finrank hne
  have hrank := LinearMap.finrank_range_add_finrank_ker q
  have hbound := Submodule.finrank_le (q.range)
  have htarget : Module.finrank K (CliffordVector m K) = 2 * m := by
    simp [CliffordVector, Module.finrank_prod, two_mul]
  rw [htarget] at hbound
  rw [← (sliceCommonAnnihilatorEquiv F).finrank_eq] at hrank
  rw [hdim] at hrank
  omega

end
end MatchgateWidth
