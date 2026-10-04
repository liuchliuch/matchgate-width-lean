import MatchgateWidth.PureSpinorAnnihilator

/-!
# Common annihilators of a pure spinor pencil

The proof is intrinsic to the actual signed Clifford representation. Polarized
matchgate identities make a pure pencil tangent to one Clifford orbit. The CAR
then kills every triple product from its annihilator. Maximal isotropy bounds
the resulting annihilator quotient by two. No spinor-line classification,
Clifford covariance, or normal-form theorem is assumed.
-/
namespace MatchgateWidth
noncomputable section
set_option maxHeartbeats 1000000
variable {K : Type*} [Field K] [CharZero K] {t : ℕ}

/-- Applying the signed CAR to an actual coefficient spinor. -/
theorem signedCliffordAction_car_apply (z w : CliffordVector t K)
    (u : SubsetSignature t K) :
    signedCliffordAction z (signedCliffordAction w u) +
      signedCliffordAction w (signedCliffordAction z u) = cliffordPairing z w • u := by
  exact congrArg (fun f : Module.End K (SubsetSignature t K) => f u)
    (signedCliffordAction_car z w)

/-- Literal MGI make each coefficient-dual vector annihilate the same spinor. -/
theorem MatchgateIdentities.coefficientVector_annihilates
    {u : SubsetSignature t K} (hu : MatchgateIdentities u) (S : Finset (Fin t)) :
    signedCliffordAction (spinorCoefficientVector u S) u = 0 := by
  ext T
  rw [← cliffordPairing_coefficient, cliffordPairing_coefficient_coefficient, hu, neg_zero]
  rfl

/-- The coefficient-dual image of a nonzero pure spinor equals its annihilator. -/
theorem MatchgateIdentities.coefficientSpace_eq_annihilator
    {u : SubsetSignature t K} (hu : MatchgateIdentities u) (hne : u ≠ 0) :
    spinorCoefficientSpace u = spinorAnnihilator u := by
  apply Submodule.eq_of_le_of_finrank_eq
  · apply Submodule.span_le.mpr
    rintro _ ⟨S, rfl⟩
    exact hu.coefficientVector_annihilates S
  · have hdim := hu.annihilator_finrank hne
    have horth := LinearMap.BilinForm.finrank_orthogonal
      (W := spinorCoefficientSpace u) cliffordBilinForm_nondegenerate
    rw [← spinorAnnihilator_eq_orthogonal, hdim] at horth
    have hc := hu.coefficientSpace_isotropic.finrank_le
    have hspace : Module.finrank K (CliffordVector t K) = 2 * t := by
      simp [CliffordVector, Module.finrank_prod,  two_mul]
    rw [hspace] at horth
    omega

/-- A nonzero pure annihilator is literally its own orthogonal space. -/
theorem MatchgateIdentities.annihilator_orthogonal
    {u : SubsetSignature t K} (hu : MatchgateIdentities u) (hne : u ≠ 0) :
    cliffordBilinForm.orthogonal (spinorAnnihilator u) = spinorAnnihilator u := by
  rw [← hu.coefficientSpace_eq_annihilator hne, ← spinorAnnihilator_eq_orthogonal]
  exact (hu.coefficientSpace_eq_annihilator hne).symm

@[simp] theorem spinorCoefficientVector_add (u v : SubsetSignature t K)
    (S : Finset (Fin t)) :
    spinorCoefficientVector (u+v) S =
      spinorCoefficientVector u S + spinorCoefficientVector v S := by
  apply Prod.ext
  · funext i
    exact congrFun ((fermionContract i).map_add u v) S
  · funext i
    exact congrFun ((fermionCreate i).map_add u v) S

/-- Polarization of the actual coefficient-vector annihilation identity. -/
theorem MatchgateIdentities.coefficientVector_polarized
    {u v : SubsetSignature t K} (hu : MatchgateIdentities u)
    (hv : MatchgateIdentities v) (huv : MatchgateIdentities (u+v))
    (S : Finset (Fin t)) :
    signedCliffordAction (spinorCoefficientVector u S) v =
      signedCliffordAction (-spinorCoefficientVector v S) u := by
  have h := huv.coefficientVector_annihilates S
  rw [spinorCoefficientVector_add] at h
  change (signedCliffordRepresentation (_ + _)) (u+v) = 0 at h
  rw [map_add signedCliffordRepresentation] at h
  simp only [LinearMap.add_apply, map_add] at h
  change signedCliffordAction (spinorCoefficientVector u S) u +
    signedCliffordAction (spinorCoefficientVector v S) u +
    (signedCliffordAction (spinorCoefficientVector u S) v +
      signedCliffordAction (spinorCoefficientVector v S) v) = 0 at h
  rw [hu.coefficientVector_annihilates S, hv.coefficientVector_annihilates S,
    zero_add, add_zero] at h
  change _ = signedCliffordRepresentation (-spinorCoefficientVector v S) u
  rw [map_neg, LinearMap.neg_apply]
  exact eq_neg_of_add_eq_zero_right h

/-- The tangent consequence of a pure pencil, in actual signed coordinates. -/
theorem MatchgateIdentities.pencil_tangent
    {u v : SubsetSignature t K} (hu : MatchgateIdentities u) (hne : u ≠ 0)
    (hv : MatchgateIdentities v) (huv : MatchgateIdentities (u+v))
    {z : CliffordVector t K} (hz : z ∈ spinorAnnihilator u) :
    ∃ w : CliffordVector t K, signedCliffordAction z v = signedCliffordAction w u := by
  rw [← hu.coefficientSpace_eq_annihilator hne] at hz
  have hz' : cliffordAtSpinor v z ∈ LinearMap.range (cliffordAtSpinor u) := by
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨S, rfl⟩ := hz
      exact ⟨-spinorCoefficientVector v S,
        (hu.coefficientVector_polarized hv huv S).symm⟩
    | zero =>
      rw [map_zero]
      exact Submodule.zero_mem _
    | add z w hz hw ihz ihw =>
      rw [map_add]
      exact Submodule.add_mem _ ihz ihw
    | smul c z hz ih =>
      rw [map_smul]
      exact Submodule.smul_mem _ c ih
  obtain ⟨w, hw⟩ := hz'
  exact ⟨w, hw.symm⟩

/-- Three vectors annihilating one point of a pure pencil also kill the other. -/
theorem MatchgateIdentities.pencil_triple_action_zero
    {u v : SubsetSignature t K} (hu : MatchgateIdentities u) (hne : u ≠ 0)
    (hv : MatchgateIdentities v) (huv : MatchgateIdentities (u+v))
    {x y z : CliffordVector t K}
    (hx : x ∈ spinorAnnihilator u) (hy : y ∈ spinorAnnihilator u)
    (hz : z ∈ spinorAnnihilator u) :
    signedCliffordAction x (signedCliffordAction y (signedCliffordAction z v)) = 0 := by
  obtain ⟨w, hw⟩ := hu.pencil_tangent hne hv huv hz
  rw [hw]
  have hy' : signedCliffordAction y u = 0 := hy
  have hx' : signedCliffordAction x u = 0 := hx
  have h := signedCliffordAction_car_apply y w u
  rw [hy', map_zero, add_zero] at h
  rw [h, map_smul, hx', smul_zero]


private theorem finrank_inf_lower_of_pair_kernel
    (L M : Submodule K (CliffordVector t K)) (f : L →ₗ[K] K × K)
    (hf : ∀ x : L, f x = 0 → (x : CliffordVector t K) ∈ M) :
    Module.finrank K L - 2 ≤ Module.finrank K ↥(L ⊓ M) := by
  let g : LinearMap.ker f →ₗ[K] ↥(L ⊓ M) :=
    { toFun := fun x => ⟨x.val.val, x.val.property, hf x.val x.property⟩
      map_add' := fun x y => by rfl
      map_smul' := fun c x => by rfl }
  have hg : Function.Injective g := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : ↥(L ⊓ M) => (z : CliffordVector t K)) h
  have hker := LinearMap.finrank_le_finrank_of_injective hg
  have hrange := (LinearMap.range f).finrank_le
  have hsum := f.finrank_range_add_finrank_ker
  have hdim : Module.finrank K (K × K) = 2 := by simp
  rw [hdim] at hrange
  omega

/-- Moving an annihilator through three Clifford factors is the alternating
three-term contraction identity, with the signs fixed by the literal CAR. -/
theorem signedCliffordAction_triple_pairing
    {v : SubsetSignature t K} (a b c y : CliffordVector t K)
    (hy : y ∈ spinorAnnihilator v)
    (hzero : signedCliffordAction a (signedCliffordAction b
      (signedCliffordAction c v)) = 0) :
    cliffordPairing y a • signedCliffordAction b (signedCliffordAction c v) -
      cliffordPairing y b • signedCliffordAction a (signedCliffordAction c v) +
      cliffordPairing y c • signedCliffordAction a (signedCliffordAction b v) = 0 := by
  have hy' : signedCliffordAction y v = 0 := hy
  have h₁ := signedCliffordAction_car_apply y a
    (signedCliffordAction b (signedCliffordAction c v))
  rw [hzero, map_zero, zero_add] at h₁
  have h₂ := congrArg (signedCliffordAction a)
    (signedCliffordAction_car_apply y b (signedCliffordAction c v))
  simp only [map_add, map_smul] at h₂
  have h₃ := congrArg (fun w => signedCliffordAction a (signedCliffordAction b w))
    (signedCliffordAction_car_apply y c v)
  simp only [hy', map_zero, add_zero, map_smul] at h₃
  rw [h₁, h₃] at h₂
  have h := sub_eq_zero.mpr h₂
  convert h using 1 <;> abel

/-- The analogous two-factor identity. -/
theorem signedCliffordAction_double_pairing
    {v : SubsetSignature t K} (a b y : CliffordVector t K)
    (hy : y ∈ spinorAnnihilator v)
    (hzero : signedCliffordAction a (signedCliffordAction b v) = 0) :
    cliffordPairing y a • signedCliffordAction b v =
      cliffordPairing y b • signedCliffordAction a v := by
  have hy' : signedCliffordAction y v = 0 := hy
  have h₁ := signedCliffordAction_car_apply y a (signedCliffordAction b v)
  rw [hzero, map_zero, zero_add] at h₁
  have h₂ := congrArg (signedCliffordAction a)
    (signedCliffordAction_car_apply y b v)
  simp only [hy', map_zero, add_zero, map_smul] at h₂
  exact h₁.symm.trans h₂

/-- A maximal-isotropic annihilator and cubic vanishing force codimension at
most two, without choosing a normal form for either spinor or split space. -/
theorem annihilator_inf_finrank_lower_of_triple_zero
    (L : Submodule K (CliffordVector t K)) {v : SubsetSignature t K}
    (hv : MatchgateIdentities v) (hne : v ≠ 0)
    (htriple : ∀ a ∈ L, ∀ b ∈ L, ∀ c ∈ L,
      signedCliffordAction a (signedCliffordAction b (signedCliffordAction c v)) = 0) :
    Module.finrank K L - 2 ≤ Module.finrank K ↥(L ⊓ spinorAnnihilator v) := by
  classical
  have horth {x : CliffordVector t K}
      (hx : ∀ y ∈ spinorAnnihilator v, cliffordPairing y x = 0) :
      x ∈ spinorAnnihilator v := by
    rw [← hv.annihilator_orthogonal hne, LinearMap.BilinForm.mem_orthogonal_iff]
    exact hx
  by_cases h₂ : ∃ b ∈ L, ∃ c ∈ L,
      signedCliffordAction b (signedCliffordAction c v) ≠ 0
  · obtain ⟨b, hb, c, hc, hbc⟩ := h₂
    obtain ⟨S, hS⟩ : ∃ S, signedCliffordAction b (signedCliffordAction c v) S ≠ 0 := by
      by_contra h
      push Not at h
      exact hbc (funext h)
    let f₁ : L →ₗ[K] K := ((LinearMap.proj S).comp
      (cliffordAtSpinor (signedCliffordAction c v))).domRestrict L
    let f₂ : L →ₗ[K] K := ((LinearMap.proj S).comp
      (cliffordAtSpinor (signedCliffordAction b v))).domRestrict L
    apply finrank_inf_lower_of_pair_kernel L (spinorAnnihilator v) (f₁.prod f₂)
    intro x hx
    have hx₁ : signedCliffordAction (x : CliffordVector t K) (signedCliffordAction c v) S = 0 :=
      congrArg Prod.fst hx
    have hx₂ : signedCliffordAction (x : CliffordVector t K) (signedCliffordAction b v) S = 0 :=
      congrArg Prod.snd hx
    apply horth
    intro y hy
    have h := congrFun (signedCliffordAction_triple_pairing x b c y hy
      (htriple x x.property b hb c hc)) S
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hx₁, hx₂,
      mul_zero, sub_zero, add_zero, Pi.zero_apply] at h
    exact (mul_eq_zero.mp h).resolve_right hS
  · push Not at h₂
    by_cases h₁ : ∃ b ∈ L, signedCliffordAction b v ≠ 0
    · obtain ⟨b, hb, hbc⟩ := h₁
      obtain ⟨S, hS⟩ : ∃ S, signedCliffordAction b v S ≠ 0 := by
        by_contra h
        push Not at h
        exact hbc (funext h)
      let f : L →ₗ[K] K := ((LinearMap.proj S).comp (cliffordAtSpinor v)).domRestrict L
      apply finrank_inf_lower_of_pair_kernel L (spinorAnnihilator v) (f.prod 0)
      intro x hx
      have hx₁ : signedCliffordAction (x : CliffordVector t K) v S = 0 :=
        congrArg Prod.fst hx
      apply horth
      intro y hy
      have h := congrFun (signedCliffordAction_double_pairing x b y hy
        (h₂ x x.property b hb)) S
      simp only [Pi.smul_apply, smul_eq_mul, hx₁, mul_zero] at h
      exact (mul_eq_zero.mp h).resolve_right hS
    · push Not at h₁
      have hle : L ≤ spinorAnnihilator v := fun z hz => h₁ z hz
      rw [inf_eq_left.mpr hle]
      omega

/-- Three actual MGI points already give the common-annihilator bound for the
whole pure pencil. The natural-number subtraction handles every small arity. -/
theorem MatchgateIdentities.pencil_annihilator_finrank_lower
    {u v : SubsetSignature t K} (hu : MatchgateIdentities u) (hune : u ≠ 0)
    (hv : MatchgateIdentities v) (hvne : v ≠ 0)
    (huv : MatchgateIdentities (u+v)) :
    t - 2 ≤ Module.finrank K ↥(spinorAnnihilator u ⊓ spinorAnnihilator v) := by
  have h := annihilator_inf_finrank_lower_of_triple_zero
    (spinorAnnihilator u) hv hvne (fun _ ha _ hb _ hc =>
      hu.pencil_triple_action_zero hune hv huv ha hb hc)
  rwa [hu.annihilator_finrank hune] at h

/-- Source-facing pure-pencil form. Independence and same-parity assumptions
are unnecessary for this lower bound; they may be retained by callers. -/
theorem pure_pencil_annihilator_finrank_lower
    {u v : SubsetSignature t K} (hu : IsPureSpinor u) (hv : IsPureSpinor v)
    (hpencil : ∀ a b : K, IsPureSpinor (a • u + b • v) ∨ a • u + b • v = 0) :
    t - 2 ≤ Module.finrank K ↥(spinorAnnihilator u ⊓ spinorAnnihilator v) := by
  have humgi := (isPureSpinor_iff_matchgateIdentities u).mp hu
  have hvmgi := (isPureSpinor_iff_matchgateIdentities v).mp hv
  apply humgi.2.pencil_annihilator_finrank_lower humgi.1 hvmgi.2 hvmgi.1
  have hsum := hpencil 1 1
  simp only [one_smul] at hsum
  rcases hsum with hsum | hsum
  · exact ((isPureSpinor_iff_matchgateIdentities (u+v)).mp hsum).2
  · rw [hsum]
    intro A B
    simp [matchgateSum]

end
end MatchgateWidth
