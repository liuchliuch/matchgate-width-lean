import MatchgateWidth.VarietyDimension
import MatchgateWidth.RationalClosure
import MatchgateWidth.RankTwoGaussianHull
import Mathlib.Algebra.CharZero.Infinite

/-!
# Matchgate and star-table affine varieties

The defining point sets are the matchgate-identity locus and its actual sampled
star image. Dimension is the Krull dimension of their vanishing-ideal coordinate
rings. Rational definition means an equality with a rational polynomial zero
locus, not containment in one.
-/

namespace MatchgateWidth

open MvPolynomial
open scoped symmDiff

noncomputable section

/-- Polynomial Zariski closure is the least common zero locus containing a set. -/
theorem polynomialZariskiClosure_idempotent {K τ : Type*} [CommRing K]
    (S : Set (τ → K)) :
    polynomialZariskiClosure (polynomialZariskiClosure S) = polynomialZariskiClosure S := by
  ext x
  constructor
  · intro hx p hp
    exact hx p (fun y hy => hy p hp)
  · intro hx p hp
    apply hx p
    intro y hy
    exact hp y (fun q hq => hq y hy)

@[simp] theorem vanishingIdeal_univ {K τ : Type*} [Field K] [Infinite K] :
    vanishingIdeal (Set.univ : Set (τ → K)) = ⊥ := by
  ext p
  simp only [mem_vanishingIdeal, Set.mem_univ, forall_true_left, Ideal.mem_bot]
  constructor
  · intro h
    apply MvPolynomial.funext
    intro x
    simpa using h x
  · rintro rfl x
    exact map_zero _

/-- The usual dimension of affine space, with the empty-variable case included. -/
theorem affineDimension_univ (K τ : Type) [Field K] [Infinite K] [Fintype τ] :
    affineDimension (Set.univ : Set (τ → K)) = Fintype.card τ := by
  unfold affineDimension CoordinateRing
  rw [vanishingIdeal_univ,
    ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot (MvPolynomial τ K))]
  simp [Nat.card_eq_fintype_card]

/-- One literal MGI equation as a polynomial in the signature entries. -/
def matchgateIdentityPolynomial (s : ℕ) (R : Type*) [CommRing R]
    (α β : Finset (Fin s)) : MvPolynomial (BooleanInput s) R :=
  matchgateSum (fun S => X ((booleanSubsetEquiv s).symm S)) α β
    ((α ∆ β).sort (· ≤ ·))

/-- Evaluating the defining polynomial recovers the literal MGI equation. -/
theorem eval_matchgateIdentityPolynomial {s : ℕ} {R : Type*} [CommRing R]
    (f : BooleanTable s R) (α β : Finset (Fin s)) :
    eval f (matchgateIdentityPolynomial s R α β) =
      matchgateSum (fun S => f ((booleanSubsetEquiv s).symm S)) α β
        ((α ∆ β).sort (· ≤ ·)) := by
  classical
  simp [matchgateIdentityPolynomial, matchgateSum]

/-- The MGI point locus is genuinely polynomial closed. -/
theorem matchgateIdentityLocus_polynomialZariskiClosure
    (K : Type*) [CommRing K] (s : ℕ) :
    polynomialZariskiClosure (matchgateIdentityLocus K s) = matchgateIdentityLocus K s := by
  ext f
  constructor
  · intro hf α β
    have h := hf (matchgateIdentityPolynomial s K α β) (fun g hg => by
      rw [eval_matchgateIdentityPolynomial]
      exact hg α β)
    exact (eval_matchgateIdentityPolynomial f α β) ▸ h
  · intro hf p hp
    exact hp f hf

/-- A pure-parity locus imposes MGI and vanishing of the opposite parity coordinates. -/
def matchgateParityLocus (K : Type*) [CommRing K] (s : ℕ) (e : Fin 2) :
    Set (BooleanTable s K) :=
  {f | BooleanMatchgateIdentities f ∧ ∀ z, booleanParity z ≠ e.val → f z = 0}

/-- Every MGI tensor has a single parity, including the zero tensor. -/
theorem BooleanMatchgateIdentities.exists_parity {s : ℕ} {K : Type*} [Field K]
    {f : BooleanTable s K} (hf : BooleanMatchgateIdentities f) :
    ∃ e : Fin 2, ∀ z, booleanParity z ≠ e.val → f z = 0 := by
  obtain ⟨pivot, a, rfl⟩ := hf.exists_pfaffianPivotChart
  refine ⟨⟨booleanParity pivot, booleanParity_lt_two pivot⟩, ?_⟩
  intro z hz
  simp only [pfaffianPivotChart, Fin.val_zero, pow_zero, one_mul]
  apply pfaffianChart_odd
  have ho : booleanParity (pfaffianXor pivot z) = 1 := by
    rw [booleanParity_xor]
    have hp := booleanParity_lt_two pivot
    have hzp := booleanParity_lt_two z
    dsimp only at hz
    omega
  simpa [pfaffianSelectedPorts, booleanParity, booleanSubsetEquiv] using ho

/-- The full MGI variety is exactly the union of the two parity components. -/
theorem matchgateIdentityLocus_eq_union_parity (K : Type*) [Field K] (s : ℕ) :
    matchgateIdentityLocus K s = matchgateParityLocus K s 0 ∪ matchgateParityLocus K s 1 := by
  ext f
  constructor
  · intro hf
    obtain ⟨e, he⟩ := hf.exists_parity
    fin_cases e
    · exact Or.inl ⟨hf, he⟩
    · exact Or.inr ⟨hf, he⟩
  · rintro (hf | hf)
    · exact hf.1
    · exact hf.1

/-- The zero tensor belongs to both parity components. -/
theorem zero_mem_matchgateParityLocus (K : Type*) [CommRing K] (s : ℕ) (e : Fin 2) :
    (0 : BooleanTable s K) ∈ matchgateParityLocus K s e := by
  constructor
  · intro α β
    simp [matchgateSum]
  · intro z hz
    rfl

/-- At arity zero the matchgate variety is the entire one-coordinate scalar space. -/
theorem matchgateIdentityLocus_zero_eq_univ (K : Type*) [CommRing K] :
    matchgateIdentityLocus K 0 = Set.univ := by
  apply Set.eq_univ_of_forall
  intro f α β
  have ha : α = ∅ := Subsingleton.elim _ _
  have hb : β = ∅ := Subsingleton.elim _ _
  subst α
  subst β
  simp [matchgateSum]

/-- The arity-zero table space is canonically one copy of the coefficient ring. -/
def arityZeroScalarEquiv (K : Type*) : BooleanTable 0 K ≃ K where
  toFun f := f Fin.elim0
  invFun c := fun _ => c
  left_inv f := by
    funext z
    exact congrArg f (Subsingleton.elim _ _)
  right_inv c := rfl

/-- Exact canonical Pfaffian chart description of the complex MGI locus. -/
theorem matchgateIdentityLocus_eq_rationalPolynomialChartUnion (s : ℕ) :
    matchgateIdentityLocus ℂ s = rationalPolynomialChartUnion
      (fun pivot => pfaffianPivotChartPolynomial s ℚ pivot (fun _ => 0)) := by
  ext f
  constructor
  · intro hf
    obtain ⟨pivot, a, rfl⟩ := hf.exists_pfaffianPivotChart
    refine ⟨pivot, a, ?_⟩
    funext z
    exact eval₂_pfaffianPivotChartPolynomial (Rat.castHom ℂ) pivot (fun _ => 0) a z
  · rintro ⟨pivot, a, rfl⟩
    have h : polynomialMap (Rat.castHom ℂ)
        (pfaffianPivotChartPolynomial s ℚ pivot (fun _ => 0)) a =
        pfaffianPivotChart pivot (fun _ => 0) a := by
      funext z
      exact eval₂_pfaffianPivotChartPolynomial (Rat.castHom ℂ) pivot (fun _ => 0) a z
    rw [h]
    exact pfaffianPivotChart_booleanMatchgateIdentities pivot a

/-- The same exact canonical charts over an arbitrary field. -/
theorem matchgateIdentityLocus_eq_polynomialChartUnion
    (K : Type) [Field K] (s : ℕ) :
    matchgateIdentityLocus K s = polynomialChartUnion
      (fun pivot => pfaffianPivotChartPolynomial s K pivot (fun _ => 0)) := by
  ext f
  constructor
  · intro hf
    obtain ⟨pivot, a, rfl⟩ := hf.exists_pfaffianPivotChart
    refine ⟨pivot, a, ?_⟩
    funext z
    exact eval₂_pfaffianPivotChartPolynomial (RingHom.id K) pivot (fun _ => 0) a z
  · rintro ⟨pivot, a, rfl⟩
    have h : polynomialMap (RingHom.id K)
        (pfaffianPivotChartPolynomial s K pivot (fun _ => 0)) a =
        pfaffianPivotChart pivot (fun _ => 0) a := by
      funext z
      exact eval₂_pfaffianPivotChartPolynomial (RingHom.id K) pivot (fun _ => 0) a z
    rw [h]
    exact pfaffianPivotChart_booleanMatchgateIdentities pivot a

/-- Rational defining ideal for the reduced matchgate variety. Its complex
zero locus is proved below to be exactly the MGI locus. -/
def matchgateVarietyIdeal (s : ℕ) : Ideal (MvPolynomial (BooleanInput s) ℚ) :=
  vanishingIdeal (matchgateIdentityLocus ℚ s)

/-- This rational ideal cuts out exactly the original complex matchgate locus. -/
theorem matchgateVarietyIdeal_complex_zeroLocus (s : ℕ) :
    polynomialZeroLocus (Rat.castHom ℂ) (matchgateVarietyIdeal s : Set _) =
      matchgateIdentityLocus ℂ s := by
  have h := rationalPolynomialChartUnion_closure_eq_rational_points
    (fun pivot => pfaffianPivotChartPolynomial s ℚ pivot (fun _ => 0))
  rw [← matchgateIdentityLocus_eq_rationalPolynomialChartUnion,
    matchgateIdentityLocus_polynomialZariskiClosure] at h
  change matchgateIdentityLocus ℂ s = polynomialZariskiClosure
    ((fun y t => (y t : ℂ)) '' polynomialChartUnion
      (fun pivot => pfaffianPivotChartPolynomial s ℚ pivot (fun _ => 0))) at h
  rw [← matchgateIdentityLocus_eq_polynomialChartUnion,
    polynomialZariskiClosure_rational_points] at h
  simpa only [matchgateVarietyIdeal, polynomialZeroLocus, SetLike.mem_coe, mem_vanishingIdeal,
    Set.mem_ofPred_eq] using h.symm

/-- Lemma 5.3 for the rational affine variety: this is the Krull dimension
of its rational coordinate ring, whose complex points were identified above. -/
theorem matchgateVariety_dimension_le (s : ℕ) :
    ringKrullDim (MvPolynomial (BooleanInput s) ℚ ⧸ matchgateVarietyIdeal s) ≤ delta s :=
  matchgateIdentityLocus_affineDimension_le ℚ s

/-- The paper's arity-zero convention has dimension exactly one. -/
theorem matchgateVariety_dimension_zero :
    ringKrullDim (MvPolynomial (BooleanInput 0) ℚ ⧸ matchgateVarietyIdeal 0) = 1 := by
  change affineDimension (matchgateIdentityLocus ℚ 0) = 1
  rw [matchgateIdentityLocus_zero_eq_univ, affineDimension_univ, card_booleanInput]
  norm_num

/-- The finite discrete data in the canonical star charts. -/
abbrev StarPivotChoice (k r : ℕ) :=
  (Fin 2 → BooleanInput r) × BooleanInput (k * r)

/-- Canonical charts use the MGI-preserving zero sign choices. -/
def canonicalStarChartChoice {k r : ℕ} (c : StarPivotChoice k r) :
    AlphabetStarChartChoice (Fin 2) k r :=
  ((fun l => (c.1 l, fun _ => 0)), (c.2, fun _ => 0))

/-- Rational coordinate polynomials for the canonical sampled-star charts. -/
def starPivotChartPolynomial {k r : ℕ} (c : StarPivotChoice k r) :
    BooleanInput k → MvPolynomial (AlphabetStarChartParameter (Fin 2) k r) ℚ :=
  sampledAlphabetChartStarPolynomial (canonicalStarChartChoice c)

/-- The actual star-table locus, with no extra sign choices, is exactly a
finite union of rational polynomial images. -/
theorem starTableLocus_eq_rationalPolynomialChartUnion (k r : ℕ) :
    starTableLocus ℂ k r = rationalPolynomialChartUnion
      (starPivotChartPolynomial (k := k) (r := r)) := by
  ext f
  constructor
  · rintro ⟨Q, g, hQ, hg, rfl⟩
    choose pivot a ha using fun l => (hg l).exists_pfaffianPivotChart
    obtain ⟨pivotQ, aQ, hQa⟩ := hQ.exists_pfaffianPivotChart
    refine ⟨(pivot, pivotQ), Sum.elim (fun t => a t.1 t.2) aQ, ?_⟩
    funext z
    change eval₂ (Rat.castHom ℂ) _ (sampledAlphabetChartStarPolynomial _ z) = _
    rw [eval₂_sampledAlphabetChartStarPolynomial]
    simp only [sampledAlphabetChartStar, canonicalStarChartChoice,
      Sum.elim_inl, Sum.elim_inr, ← ha, ← hQa]
  · rintro ⟨c, a, rfl⟩
    refine ⟨pfaffianPivotChart c.2 (fun _ => 0) (fun t => a (.inr t)),
      (fun l => pfaffianPivotChart (c.1 l) (fun _ => 0) (fun t => a (.inl (l, t)))),
      pfaffianPivotChart_booleanMatchgateIdentities _ _,
      (fun l => pfaffianPivotChart_booleanMatchgateIdentities _ _), ?_⟩
    funext z
    exact (eval₂_sampledAlphabetChartStarPolynomial (Rat.castHom ℂ)
      (canonicalStarChartChoice c) a z).symm

/-- Exact rational points of the star-table image in the same canonical charts. -/
theorem starTableLocus_rat_eq_polynomialChartUnion (k r : ℕ) :
    starTableLocus ℚ k r = polynomialChartUnion
      (starPivotChartPolynomial (k := k) (r := r)) := by
  ext f
  constructor
  · rintro ⟨Q, g, hQ, hg, rfl⟩
    choose pivot a ha using fun l => (hg l).exists_pfaffianPivotChart
    obtain ⟨pivotQ, aQ, hQa⟩ := hQ.exists_pfaffianPivotChart
    refine ⟨(pivot, pivotQ), Sum.elim (fun t => a t.1 t.2) aQ, ?_⟩
    funext z
    change eval₂ (RingHom.id ℚ) _ (sampledAlphabetChartStarPolynomial _ z) = _
    rw [eval₂_sampledAlphabetChartStarPolynomial]
    simp only [sampledAlphabetChartStar, canonicalStarChartChoice,
      Sum.elim_inl, Sum.elim_inr, ← ha, ← hQa]
  · rintro ⟨c, a, rfl⟩
    refine ⟨pfaffianPivotChart c.2 (fun _ => 0) (fun t => a (.inr t)),
      (fun l => pfaffianPivotChart (c.1 l) (fun _ => 0) (fun t => a (.inl (l, t)))),
      pfaffianPivotChart_booleanMatchgateIdentities _ _,
      (fun l => pfaffianPivotChart_booleanMatchgateIdentities _ _), ?_⟩
    funext z
    exact (eval₂_sampledAlphabetChartStarPolynomial (RingHom.id ℚ)
      (canonicalStarChartChoice c) a z).symm

/-- The matchgate locus is defined over the rationals. -/
theorem matchgateIdentityLocus_defined_over_rat (s : ℕ) :
    ∃ P : Set (MvPolynomial (BooleanInput s) ℚ),
      matchgateIdentityLocus ℂ s = polynomialZeroLocus (Rat.castHom ℂ) P := by
  obtain ⟨P, hP⟩ := rationalPolynomialChartUnion_closure_defined_over_rat
    (fun pivot => pfaffianPivotChartPolynomial s ℚ pivot (fun _ => 0))
  rw [← matchgateIdentityLocus_eq_rationalPolynomialChartUnion,
    matchgateIdentityLocus_polynomialZariskiClosure] at hP
  exact ⟨P, hP⟩

/-- Source-coordinate variables: both sampler tables and the central table. -/
abbrev StarSourceCoordinate (k r : ℕ) :=
  (Fin 2 × BooleanInput r) ⊕ BooleanInput (k * r)

/-- Pack the two shared samplers and center into source coordinates. -/
def starSourceCoordinates {K : Type*} {k r : ℕ}
    (Q : BooleanTable (k * r) K) (g : Fin 2 → BooleanTable r K) :
    StarSourceCoordinate k r → K := Sum.elim (fun t => g t.1 t.2) Q

/-- The literal integer polynomials of the source star-table morphism. -/
def starTableMorphismPolynomial (k r : ℕ) (z : BooleanInput k) :
    MvPolynomial (StarSourceCoordinate k r) ℤ :=
  sampledAlphabetStar (fun x => X (.inr x)) (fun l x => X (.inl (l, x))) z

/-- The polynomial formula evaluates exactly to the stated star contraction. -/
theorem eval₂_starTableMorphismPolynomial {K : Type*} [CommRing K]
    {k r : ℕ} (Q : BooleanTable (k * r) K) (g : Fin 2 → BooleanTable r K)
    (z : BooleanInput k) :
    eval₂ (Int.castRingHom K) (starSourceCoordinates Q g) (starTableMorphismPolynomial k r z) =
      sampledAlphabetStar Q g z := by
  classical
  change (eval₂Hom (Int.castRingHom K) (starSourceCoordinates Q g))
    (starTableMorphismPolynomial k r z) = _
  simp [starTableMorphismPolynomial, sampledAlphabetStar, starContract, starSourceCoordinates]

/-- The source is exactly the product of the two sampler varieties and the
central matchgate variety from the paper. -/
abbrev StarVarietySource (K : Type*) [CommRing K] (k r : ℕ) :=
  (matchgateIdentityLocus K r) × (matchgateIdentityLocus K r) ×
    (matchgateIdentityLocus K (k * r))

/-- Recover the two shared sampler labels from a source triple. -/
def starVarietySamplers {K : Type*} [CommRing K] {k r : ℕ}
    (u : StarVarietySource K k r) (l : Fin 2) : BooleanTable r K :=
  Fin.cases u.1.val (fun _ => u.2.1.val) l

/-- The source morphism is the restriction of the displayed integer polynomial map. -/
def starTableMorphism {K : Type*} [CommRing K] {k r : ℕ}
    (u : StarVarietySource K k r) : BooleanTable k K :=
  polynomialMap (Int.castRingHom K) (starTableMorphismPolynomial k r)
    (starSourceCoordinates u.2.2.val (starVarietySamplers u))

/-- This restricted polynomial morphism has exactly the paper's contraction coordinates. -/
theorem starTableMorphism_eq_sampledAlphabetStar
    {K : Type*} [CommRing K] {k r : ℕ} (u : StarVarietySource K k r) :
    starTableMorphism u = sampledAlphabetStar u.2.2.val (starVarietySamplers u) := by
  funext z
  exact eval₂_starTableMorphismPolynomial _ _ z

/-- The image of the actual product-source polynomial morphism is precisely
`starTableLocus`; no source/image identification is assumed. -/
theorem range_starTableMorphism (K : Type*) [CommRing K] (k r : ℕ) :
    Set.range (starTableMorphism (K := K) (k := k) (r := r)) = starTableLocus K k r := by
  ext f
  constructor
  · rintro ⟨u, rfl⟩
    refine ⟨u.2.2.val, starVarietySamplers u, u.2.2.property, ?_, ?_⟩
    · intro l
      fin_cases l
      · exact u.1.property
      · exact u.2.1.property
    · exact (starTableMorphism_eq_sampledAlphabetStar u).symm
  · rintro ⟨Q, g, hQ, hg, rfl⟩
    let u : StarVarietySource K k r := (⟨g 0, hg 0⟩, ⟨g 1, hg 1⟩, ⟨Q, hQ⟩)
    refine ⟨u, ?_⟩
    rw [starTableMorphism_eq_sampledAlphabetStar]
    have hsamplers : starVarietySamplers u = g := by
      funext l
      fin_cases l <;> rfl
    rw [hsamplers]

/-- Rational defining ideal for the actual star-image closure. -/
def starTableVarietyIdeal (k r : ℕ) : Ideal (MvPolynomial (BooleanInput k) ℚ) :=
  vanishingIdeal (starTableLocus ℚ k r)

/-- The specified rational ideal cuts out the actual complex star-image closure. -/
theorem starTableVarietyIdeal_complex_zeroLocus (k r : ℕ) :
    polynomialZeroLocus (Rat.castHom ℂ) (starTableVarietyIdeal k r : Set _) =
      polynomialZariskiClosure (starTableLocus ℂ k r) := by
  have h := rationalPolynomialChartUnion_closure_eq_rational_points
    (starPivotChartPolynomial (k := k) (r := r))
  rw [← starTableLocus_eq_rationalPolynomialChartUnion] at h
  change polynomialZariskiClosure (starTableLocus ℂ k r) = polynomialZariskiClosure
    ((fun y t => (y t : ℂ)) '' polynomialChartUnion
      (starPivotChartPolynomial (k := k) (r := r))) at h
  rw [← starTableLocus_rat_eq_polynomialChartUnion,
    polynomialZariskiClosure_rational_points] at h
  simpa only [starTableVarietyIdeal, polynomialZeroLocus, SetLike.mem_coe, mem_vanishingIdeal,
    Set.mem_ofPred_eq] using h.symm

/-- The rational coordinate ring of the star-image closure obeys the same bound. -/
theorem starTableVariety_dimension_le (k r : ℕ) :
    ringKrullDim (MvPolynomial (BooleanInput k) ℚ ⧸ starTableVarietyIdeal k r) ≤ D k r :=
  starTableLocus_affineDimension_le ℚ k r

/-- Proposition 5.4: exact rational definition and the true coordinate-ring
dimension bound for the Zariski closure of the sampled-star image. -/
theorem algebraic_star_table_bound (k r : ℕ) :
    (∃ P : Set (MvPolynomial (BooleanInput k) ℚ),
      polynomialZariskiClosure (starTableLocus ℂ k r) =
        polynomialZeroLocus (Rat.castHom ℂ) P) ∧
    affineDimension (polynomialZariskiClosure (starTableLocus ℂ k r)) ≤ D k r := by
  constructor
  · rw [starTableLocus_eq_rationalPolynomialChartUnion]
    exact rationalPolynomialChartUnion_closure_defined_over_rat _
  · exact starTableLocus_closure_affineDimension_le ℂ k r

/-- The strict parameter-budget inequality makes the actual rational-defined
star-image closure a proper subset of affine space. -/
theorem starTableLocus_closure_ne_univ {k r : ℕ} (h : D k r < 2 ^ k) :
    polynomialZariskiClosure (starTableLocus ℂ k r) ≠ Set.univ := by
  intro heq
  have hd := starTableLocus_closure_affineDimension_le ℂ k r
  rw [heq, affineDimension_univ, card_booleanInput] at hd
  have hn : 2 ^ k ≤ D k r := by exact_mod_cast hd
  exact (Nat.not_le_of_lt h) hn

end
end MatchgateWidth
