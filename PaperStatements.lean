import MatchgateWidth.AlgebraicVarietyBounds
import MatchgateWidth.AllLeftBinaryArbitraryBasis
import MatchgateWidth.BlockInterpolationTheorem
import MatchgateWidth.CompleteIntegerMainTheorem
import MatchgateWidth.CompleteSourceStructure
import MatchgateWidth.ControlledPresentationProposition
import MatchgateWidth.ControlledRanksProposition
import MatchgateWidth.EffectiveIntegerObstruction
import MatchgateWidth.ExactFlagNormalForm
import MatchgateWidth.ExactMatchgateBounds
import MatchgateWidth.ExactMatchgateLinear
import MatchgateWidth.ExactTranscendentalWidth
import MatchgateWidth.GeneralIsotropicKernelCover
import MatchgateWidth.IndependentPrimeExponentials
import MatchgateWidth.OrderedAllLeftGadget
import MatchgateWidth.PositiveGrid
import MatchgateWidth.RationalPresentationGraphs
import MatchgateWidth.SourceDefinitions
import MatchgateWidth.TranscendentalCompanionPresentation
import MatchgateWidth.TranscendentalObstruction
import MatchgateWidth.TransformedSupport
import MatchgateWidth.TwoCenterGadget

/-! Explicit statement contracts for arXiv:2610.00079v1.
Review this file and its imported definitions for correspondence.
The contracts contain no proof placeholders and no inferred theorem types.
Implementation proofs are connected in PaperProofs.lean. -/
namespace MatchgateWidth.Paper
noncomputable section
open Algebra
open scoped Classical BigOperators

/-- Paper 3.1. -/
def claim_3_1 : Prop :=
  ∀ (C : ∀ k, LabelledInstanceClass (starLanguageShape (k + 2)))
    (_hC : ∀ k, ContainsOrderedPlanar (C k)) (k : ℕ) (_hk : 2 ≤ k),
    IntegerMainConclusions k _hk ∧
    (booleanParity (controlledLabelledCode k 0) = 0 ∧
      booleanParity (controlledLabelledCode k 1) = 1 ∧
      booleanParity (controlledLabelledCode k 2) = 0) ∧
    RationalCoefficientPresentation (integerRationalPresentation k _hk) ∧
    RationalGraphPresentation (integerRationalPresentation k _hk) ∧
    (integerRationalPresentation k _hk).baseMatrix.rank = 3 ∧
    (integerRationalPresentation k _hk).language = integerControlledLanguage k _hk ∧
    IntegerPositiveDeficient (integerRationalPresentation k _hk).language ∧
    AllLeftMonomialFlag (integerRationalPresentation k _hk)
      (qutritCoordinatePlane 2) (qutritCoordinateRay 2) ∧
    HasExactCommonWidthOn (C k) (integerControlledLanguage k _hk) (integerSourceMinimum C k) ∧
    (∀ r, HasExactCommonWidthOn (C k) (integerControlledLanguage k _hk) r →
      integerSourceMinimum C k ≤ r) ∧
    2 ^ k ≤ 2 * (1 + (integerSourceMinimum C k).choose 2) + 1 +
      (k * integerSourceMinimum C k).choose 2 ∧
    ⌈Real.sqrt (((2 : ℝ) ^ k - 3) / (1 + (k : ℝ) ^ 2 / 2))⌉₊ ≤
      integerSourceMinimum C k ∧
    integerSourceMinimum C k ≤ 2 ^ k + 3 ∧
    AllLeftFlagNormalForm (integerRationalPresentation k _hk)
      (qutritCoordinatePlane 2) (qutritCoordinateRay 2) ∧
    PaperOmega (fun k => (integerSourceMinimum C k : ℝ))
      (fun k => Real.rpow 2 ((k : ℝ) / 2) / (k : ℝ))

/-- Paper 3.2. -/
def claim_3_2 : Prop :=
  ∀ (C : ∀ S : LabelledShape, LabelledInstanceClass S)
    (_hC : ∀ S, ContainsOrderedPlanar (C S)),
    ¬ ∃ h : ℕ → ℕ,
      ∀ (S : LabelledShape) (E : Type) (_ : Fintype E) (_ : Nonempty E)
        (r : ℕ) (p : LabelledCommonPresentation S E r),
      RationalCoefficientPresentation p → RationalGraphPresentation p →
      IntegerPositiveDeficient p.language →
      ∃ s, HasExactCommonWidthOn (C S) p.language s ∧ s ≤ h (Fintype.card E)

/-- Paper 3.3. -/
def claim_3_3 : Prop :=
  ∀ {S : LabelledShape} {t : ℕ}
    (p : LabelledCommonPresentation S (Fin 3) t) (_hM : p.baseMatrix.rank = 3)
    (_hleft : LeftPortDeficient p.language) (_hright : RightPortDeficient p.language)
    (_hessleft : LeftSupportEssential p.language) (_hessright : RightSupportEssential p.language),
    (AllLeftRayAlternative p ∧ ¬ AllLeftMobileAlternative p ∧ ¬ AllLeftFlagAlternative p) ∨
    (AllLeftMobileAlternative p ∧ ¬ AllLeftRayAlternative p ∧ ¬ AllLeftFlagAlternative p) ∨
    (AllLeftFlagAlternative p ∧ ¬ AllLeftRayAlternative p ∧ ¬ AllLeftMobileAlternative p)

/-- Paper 3.3-family. -/
def claim_3_3_family : Prop :=
  ∀ (C : ∀ k, LabelledInstanceClass (starLanguageShape (k + 2)))
    (_hC : ∀ k, ContainsOrderedPlanar (C k)),
    (∀ k (_hk : 2 ≤ k), IntegerMainConclusions k _hk ∧
      AllLeftFlagAlternative (integerRationalPresentation k _hk)) ∧
    PaperOmega (fun k => (integerSourceMinimum C k : ℝ))
      (fun k => Real.rpow 2 ((k : ℝ) / 2) / (k : ℝ)) ∧
    ∀ B, B < integerSourceMinimum C (4 * B + 8)

/-- Paper 4.1. -/
def claim_4_1 : Prop :=
  ∀ {s : ℕ} {G : BooleanTable s ℂ} (_hG : ExactMatchgate G),
    ExactMatchgate (fun x => G (fun i => x i.rev))

/-- Paper 4.2. -/
def claim_4_2 : Prop :=
  ∀ {s : ℕ} (K : Subfield ℂ)
    (G : BooleanTable s K) (_hG : BooleanMatchgateIdentities G),
    ∃ (v e : ℕ) (H : WeightedGraph (Fin v) (Fin e) ℂ) (ext : Fin s → Fin v),
      Nonempty (PlanarDrawing H ext) ∧ (∀ a, H.weight a ∈ K) ∧
      ∀ y, deletionSignature H ext y = (G ((booleanWordEquiv s).symm y) : ℂ)

/-- Paper 4.3-transpose. -/
def claim_4_3_transpose : Prop :=
  ∀ {r t : ℕ}
    {P : Matrix (BooleanInput r) (BooleanInput t) ℂ} (_hP : ExactMatchgateMatrix P),
    ExactMatchgateMatrix P.transpose

/-- Paper 4.3-pin. -/
def claim_4_3_pin : Prop :=
  ∀ {t : ℕ}
    (x : pinGroup (splitCliffordQuadratic (K := ℂ) (t := t)))
    (c : ℂ) (_hc : c ≠ 0),
    let C := c • cliffordAlgebraMatrix (x : CliffordAlgebra (splitCliffordQuadratic (K := ℂ) (t := t)))
    let D := c⁻¹ • cliffordAlgebraMatrix (↑(x⁻¹) : CliffordAlgebra (splitCliffordQuadratic (K := ℂ) (t := t)))
    ExactMatchgateMatrix C ∧ ExactMatchgateMatrix D ∧ C*D=1 ∧ D*C=1

/-- Paper 5.1. -/
def claim_5_1 : Prop :=
  ∀ {s : ℕ} {G : BooleanTable s ℂ}
    (_hG : ExactMatchgate G),
    trdeg ℚ (coordinateField G) ≤ delta s

/-- Paper 5.2. -/
def claim_5_2 : Prop :=
  ∀ {L : Type} [Fintype L] {k r : ℕ}
    {Q : BooleanTable (k*r) ℂ} {g : L → BooleanTable r ℂ}
    (_hQ : ExactMatchgate Q) (_hg : ∀ l, ExactMatchgate (g l)),
    trdeg ℚ (coordinateField (sampledAlphabetStar Q g)) ≤
      (Fintype.card L * delta r + delta (k*r) : ℕ)

/-- Paper 5.3. -/
def claim_5_3 : Prop :=
  ∀ (s : ℕ),
    ringKrullDim (MvPolynomial (BooleanInput s) ℚ ⧸ matchgateVarietyIdeal s) ≤ delta s

/-- Paper 5.4. -/
def claim_5_4 : Prop :=
  ∀ (k r : ℕ),
    (∃ P : Set (MvPolynomial (BooleanInput k) ℚ),
      polynomialZariskiClosure (starTableLocus ℂ k r) =
        polynomialZeroLocus (Rat.castHom ℂ) P) ∧
    affineDimension (polynomialZariskiClosure (starTableLocus ℂ k r)) ≤ D k r

/-- Paper 6.1. -/
def claim_6_1 : Prop :=
  ∀ {ι : Type*} [Fintype ι] (p : ι → ℕ)
    (_hp : ∀ i, (p i).Prime) (_hinj : Function.Injective p),
    AlgebraicIndependent ℚ (fun i => Complex.exp (primeSquareRoot (p i)))

/-- Paper 6.2. -/
def claim_6_2 : Prop :=
  ∀ (k : ℕ) (_hk : 2 ≤ k),
    (∀ i : Fin k, (oneVsRestFlattening (transcendentalTable k) i).rank = 2) ∧
    (∀ (r : ℕ) (g : Fin 2 → BooleanTable r ℂ) (Q : BooleanTable (k*r) ℂ),
      (∀ b, ExactMatchgate (g b)) → ExactMatchgate Q →
      (∀ z, transcendentalTable k z =
        starContract (fun x => Q (flattenBooleanBlocks x)) (fun i => g (z i))) →
      2^k ≤ 2*delta r + delta (k*r))

/-- Paper 6.3. -/
def claim_6_3 : Prop :=
  ∀ (N : ℕ),
    polynomialZariskiClosure (positiveGrid (Fin N) ℂ) = Set.univ

/-- Paper 6.4. -/
def claim_6_4 : Prop :=
  ∀ (k : ℕ) (_hk : 2 ≤ k),
    ∃ a : BooleanTable k ℕ, (∀ z, 0 < a z) ∧
      (∀ (r : ℕ) (g : Fin 2 → BooleanTable r ℂ) (Q : BooleanTable (k*r) ℂ),
        (∀ b, ExactMatchgate (g b)) → ExactMatchgate Q →
        (∀ z, (a z : ℂ) = starContract (fun x => Q (flattenBooleanBlocks x)) (fun i => g (z i))) →
        2^k ≤ 2*delta r + delta (k*r)) ∧
      ∀ i : Fin k, (oneVsRestFlattening (fun z => (a z : ℂ)) i).rank = 2

/-- Paper 7.1. -/
def claim_7_1 : Prop :=
  ∀ (K : Subfield ℂ) (k : ℕ) (_hk : 1 ≤ k)
    (f : Finset (Fin k) → K) (hf : ∀ S, f S ≠ 0),
    (interpolationBoundaryOrder k).length = k * 2 ^ k ∧
    ∃ (A : Matrix (Fin (interpolationBoundaryOrder k).length)
        (Fin (interpolationBoundaryOrder k).length) K)
      (v e : ℕ) (G : WeightedGraph (Fin v) (Fin e) ℂ)
      (ext : Fin (interpolationBoundaryOrder k).length → Fin v),
      A = interpolationPositionMatrix f hf ∧
      (∀ i j, A i j = -A j i) ∧ (∀ i, A i i = 0) ∧
      principalPfaffian A ∅ = 1 ∧
      Nonempty (PlanarDrawing G ext) ∧ (∀ a, G.weight a ∈ K) ∧
      (∀ y, deletionSignature G ext y = (f ∅ : ℂ) *
        principalPfaffian (fun i j => (A i j : ℂ)) (bridgeBitsEquiv _ y)) ∧
      (∀ y, deletionSignature G ext y ∈ K) ∧
      (∀ x : Fin k → Bool,
        List.ofFn (interpolationRepeatedBoundary x) = booleanRepetitionWord x ∧
        principalPfaffian A (booleanSubsetEquiv _ (interpolationRepetitionBits x)) =
          f (Finset.univ.filter fun i => x i) / f ∅ ∧
        deletionSignature G ext (interpolationRepeatedBoundary x) =
          (f (Finset.univ.filter fun i => x i) : ℂ))

/-- Paper 8.1. -/
def claim_8_1 : Prop :=
  ∀ {k : ℕ}
    (f : BooleanTable k ℚ) (hf : ∀ x, f x ≠ 0)
    (_hint : ∀ x, ∃ n : ℤ, f x = n) (j : Fin k),
    let R := rightTransform (controlledCoordinateBase (K := ℚ) k)
      (controlledPhysicalSignature (booleanSubsetTable f) (fun _ => hf _) j)
    Fintype.card ControlledLanguageLabel = 5 ∧
    (controlledCoordinateBase (K := ℚ) k).rank = 3 ∧
    (controlledPhysicalOrder k).length = (k + 2) * (2 ^ k + 3) ∧
    (∀ l : ControlledLanguageLabel,
      ∃ (v e : ℕ) (G : WeightedGraph (Fin v) (Fin e) ℂ)
        (ext : Fin (controlledLanguageBooleanArity k l) → Fin v),
        Nonempty (PlanarDrawing G ext) ∧ (∀ a, ∃ q : ℚ, G.weight a = q) ∧
        ∀ y, deletionSignature G ext y =
          ((controlledLanguageBoolean f hf j l
            ((booleanWordEquiv _).symm y) : ℚ) : ℂ)) ∧
    R = controlledQutrit f j ∧
    (∀ a, ∃ n : ℤ, R a = n) ∧
    (∀ a, ((∃ i, a (Sum.inr i) = 1) ∨
      (a (Sum.inl 0) = 2 ∨ a (Sum.inl 1) = 2)) → R a = 0) ∧
    (∀ x, R (controlledQutritAssignment 0 0 x) = f x ∧
      R (controlledQutritAssignment 1 1 x) = hardControlWeight (x j) * f x ∧
      R (controlledQutritAssignment 0 1 x) = 0 ∧
      R (controlledQutritAssignment 1 0 x) = 0)

/-- Paper 8.2. -/
def claim_8_2 : Prop :=
  ∀ (k : ℕ) (_hk : 2 ≤ k)
    (j : Fin k),
    ∃ (a : BooleanTable k ℕ) (ha : ∀ x, 0 < a x),
      let R := positiveControlledRightTensor a ha j
      (∀ r, HasMGIStarRepresentation k r (fun x => (a x : ℂ)) → 2 ^ k ≤ D k r) ∧
      (∀ i : Fin k, (oneVsRestFlattening (fun x => (a x : ℂ)) i).rank = 2) ∧
      R = controlledQutrit (fun x => (a x : ℂ)) j ∧
      (∀ r : Fin 3, ∀ p : Fin 1,
        (portFlatten (qutritPinTensor (K := ℂ) r) p).rank = 1) ∧
      (∀ l : Fin 2, (portFlatten (qutritNeqTensor (K := ℂ)) l).rank = 2) ∧
      (∀ p : ControlledQutritPort k, (portFlatten R p).rank = 2) ∧
      (∀ l : Fin 2, columnSupport (portFlatten R (Sum.inl l)) =
        Submodule.span ℂ ({Pi.single 0 (1 : ℂ), Pi.single 1 (1 : ℂ)} :
          Set (Fin 3 → ℂ))) ∧
      (∀ i : Fin k, columnSupport (portFlatten R (Sum.inr i)) =
        Submodule.span ℂ ({Pi.single 0 (1 : ℂ), Pi.single 2 (1 : ℂ)} :
          Set (Fin 3 → ℂ))) ∧
      ((⨆ r : Fin 3, columnSupport (portFlatten (qutritPinTensor (K := ℂ) r) 0)) ⊔
        (⨆ l : Fin 2, columnSupport (portFlatten (qutritNeqTensor (K := ℂ)) l)) = ⊤) ∧
      (⨆ p : ControlledQutritPort k, columnSupport (portFlatten R p)) = ⊤

/-- Paper 8.3. -/
def claim_8_3 : Prop :=
  ∀ {K : Type*} [Field K] {k : ℕ} [CharZero K] (f : BooleanTable k K)
    (hf : ∀ x, f x ≠ 0) (j : Fin k),
    Nonempty (TwoCenterNetworkPlanarCertificate k) ∧
    (∀ z y, twoCenterValue f hf j z y = hardTableExtension f z * hardTableExtension f y *
      (hardWeightExtension j z + hardWeightExtension j y)) ∧
    Matrix.rank (twoCenterValue f hf j : Matrix (Fin k → Fin 3) (Fin k → Fin 3) K) = 2 ∧
    ¬ ∃ U V : (Fin k → Fin 3) → K, ∀ z y, twoCenterValue f hf j z y = U z * V y

/-- Paper 8.4. -/
def claim_8_4 : Prop :=
  ∀ (k : ℕ) (_hk : 2 ≤ k)
    (j : Fin k),
    let K := transcendentalCompanionField k
    let f := transcendentalCompanionTable k
    let R := transcendentalCompanionRightTensor k j
    Fintype.card ControlledLanguageLabel = 5 ∧
    (controlledCoordinateBase (K := K) k).rank = 3 ∧
    (controlledPhysicalOrder k).length = (k + 2) * (2 ^ k + 3) ∧
    (∀ l : ControlledLanguageLabel,
      ∃ (v e : ℕ) (G : WeightedGraph (Fin v) (Fin e) ℂ)
        (ext : Fin (controlledLanguageBooleanArity k l) → Fin v),
        Nonempty (PlanarDrawing G ext) ∧
        (∀ a, G.weight a ∈ K) ∧
        ∀ y, deletionSignature G ext y =
          (controlledLanguageBoolean f (transcendentalCompanionTable_ne_zero k) j l
            ((booleanWordEquiv _).symm y) : ℂ)) ∧
    R = controlledQutrit f j ∧
    (∀ a, ((∃ i, a (Sum.inr i) = 1) ∨
      (a (Sum.inl 0) = 2 ∨ a (Sum.inl 1) = 2)) → R a = 0) ∧
    (∀ x, R (controlledQutritAssignment 0 0 x) = f x ∧
      R (controlledQutritAssignment 1 1 x) = hardControlWeight (x j) * f x ∧
      R (controlledQutritAssignment 0 1 x) = 0 ∧
      R (controlledQutritAssignment 1 0 x) = 0) ∧
    (∀ l p, (portFlatten (controlledLanguageTensor f j l) p).rank =
      controlledLanguagePortRank l) ∧
    (∀ l : Fin 2, columnSupport (portFlatten R (Sum.inl l)) =
      Submodule.span K ({Pi.single 0 (1 : K), Pi.single 1 (1 : K)} : Set (Fin 3 → K))) ∧
    (∀ i : Fin k, columnSupport (portFlatten R (Sum.inr i)) =
      Submodule.span K ({Pi.single 0 (1 : K), Pi.single 2 (1 : K)} : Set (Fin 3 → K))) ∧
    ((⨆ r : Fin 3, columnSupport (portFlatten (qutritPinTensor (K := K) r) 0)) ⊔
      (⨆ l : Fin 2, columnSupport (portFlatten (qutritNeqTensor (K := K)) l)) = ⊤) ∧
    (⨆ p : ControlledQutritPort k, columnSupport (portFlatten R p)) = ⊤ ∧
    Nonempty (TwoCenterNetworkPlanarCertificate k) ∧
    (∀ z y, twoCenterValue f (transcendentalCompanionTable_ne_zero k) j z y =
      hardTableExtension f z * hardTableExtension f y *
        (hardWeightExtension j z + hardWeightExtension j y)) ∧
    Matrix.rank (twoCenterValue f (transcendentalCompanionTable_ne_zero k) j :
      Matrix (Fin k → Fin 3) (Fin k → Fin 3) K) = 2 ∧
    ¬ ∃ U V : (Fin k → Fin 3) → K, ∀ z y,
      twoCenterValue f (transcendentalCompanionTable_ne_zero k) j z y = U z * V y

/-- Paper 9.1. -/
def claim_9_1 : Prop :=
  ∀ (C : ∀ k, LabelledInstanceClass (starLanguageShape (k+2)))
    (_hC : ∀ k, ContainsOrderedPlanar (C k)),
    let W := transcendentalClassWidthCriterion C
    let hW := transcendentalClassWidthCriterion_nonempty C
    (∀ k, 2 ≤ k → 2^k ≤ D k (admissibleWidthSequence W hW k) ∧
      ⌈Real.sqrt (((2 : ℝ)^k-3)/(1+(k : ℝ)^2/2))⌉₊ ≤ admissibleWidthSequence W hW k) ∧
    PaperOmega (fun k => (admissibleWidthSequence W hW k : ℝ))
      (fun k => Real.rpow 2 ((k : ℝ)/2)/(k : ℝ)) ∧
    (∀ B, B < admissibleWidthSequence W hW (4*B+8))

section
attribute [local instance] orderedGadgetFinDecidableEq

/-- Paper 10.1. -/
def claim_10_1 : Prop :=
  ∀ {S : LabelledShape} {a b c n : ℕ} {D : Type} [Fintype D]
    (I : AllLeftGadget S a b c n) (F : LabelledLanguage S D) (p : Fin n),
    columnSupport (portFlatten (I.value F) p) ≤
      columnSupport (portFlatten (F.left (I.leftLabel (I.boundaryVertex p)))
        (I.boundaryPort p))

end

/-- Paper 10.2. -/
def claim_10_2 : Prop :=
  ∀ (n t : ℕ)
    (M : Matrix (Fin 3) (Fin t → Bool) ℂ) (_hM : M.rank = 3)
    (F : (Fin (n + 1) → Fin 3) → ℂ) (j : Fin (n + 1)),
    columnSupport (portFlatten (leftTransform M F) j) =
        (columnSupport (portFlatten F j)).map M.transpose.mulVecLin ∧
      Module.finrank ℂ (columnSupport (portFlatten (leftTransform M F) j)) =
        Module.finrank ℂ (columnSupport (portFlatten F j))

/-- Paper 10.3. -/
def claim_10_3 : Prop :=
  ∀ {r s t : ℕ}
    {P : Matrix (BooleanInput r) (BooleanInput t) ℂ}
    {Q : Matrix (BooleanInput s) (BooleanInput t) ℂ}
    (_hP : ExactMatchgateMatrix P) (_hQ : ExactMatchgateMatrix Q)
    (_hrP : P.rank=2) (_hrQ : Q.rank=2)
    (_hne : orderedRowSpace P ≠ orderedRowSpace Q)
    (_hmeet : orderedRowSpace P ⊓ orderedRowSpace Q ≠ ⊥),
    ∃ H : Matrix (BooleanInput 2) (BooleanInput t) ℂ,
      ExactMatchgateMatrix H ∧ H.rank=4 ∧
      orderedRowSpace P ⊔ orderedRowSpace Q ≤ orderedRowSpace H

/-- Paper 10.4. -/
def claim_10_4 : Prop :=
  ∀ {r t : ℕ}
    {P : Matrix (BooleanInput r) (BooleanInput t) ℂ} (_hP : ExactMatchgateMatrix P)
    (_hr : P.rank=2^r),
    ∃ D : Matrix (BooleanInput t) (BooleanInput r) ℂ,
      ExactMatchgateMatrix D ∧ P*D=1

/-- Paper 10.5. -/
def claim_10_5 : Prop :=
  ∀ {A : Type*} [Fintype A] {r t : ℕ}
    (M : Matrix A (BooleanInput t) ℂ) (P : Matrix (BooleanInput r) (BooleanInput t) ℂ)
    (_hP : ExactMatchgateMatrix P) (_hr : P.rank=2^r)
    (_hcover : Submodule.span ℂ (Set.range M.row) ≤ orderedRowSpace P),
    ∃ N : Matrix A (BooleanInput r) ℂ,
      M=N*P ∧
      (∀ k (F : (Fin k → A) → ℂ), ExactMatchgate (leftBooleanLift M k F) →
        ExactMatchgate (leftBooleanLift N k F)) ∧
      (∀ k (H : BooleanTable (k*t) ℂ), ExactMatchgate H →
        ExactMatchgate (blockwiseTransform P k H) ∧
        rightBooleanRestriction M k H = rightBooleanRestriction N k (blockwiseTransform P k H))

/-- Paper 10.6. -/
def claim_10_6 : Prop :=
  ∀ {t r : ℕ} (L : Submodule ℂ (CliffordVector t ℂ)) (_hL : CliffordIsotropic L)
    (_hr : r ≤ t) (_hdim : Module.finrank ℂ L = t - r),
    ∃ P : Matrix (BooleanInput r) (BooleanInput t) ℂ,
      OrderedMatchgateMatrix P ∧ P.rank = 2 ^ r ∧
      (orderedRowSpace P).map spinorSubsetEquiv.toLinearMap = cliffordJointKernel L ∧
      DiskRealizable (fun y => orderedMatrixSignature P ((booleanWordEquiv (r+t)).symm y))

/-- Paper 10.7. -/
def claim_10_7 : Prop :=
  ∀ {S : LabelledShape} {t : ℕ}
    (p : LabelledCommonPresentation S (Fin 3) t) (_hM : p.baseMatrix.rank = 3)
    (_hleft : LeftPortDeficient p.language) (_hright : RightPortDeficient p.language)
    (_hessright : RightSupportEssential p.language) (_hprime : AllLeftConnectionPrime p),
    AllLeftWidthThreeCompression p ∧
      ∀ P Q : Submodule ℂ (Fin 3 → ℂ),
        P ∈ allLeftRealizedSupports p.language 2 →
        Q ∈ allLeftRealizedSupports p.language 2 → P ≠ Q →
        ∃ H : Matrix (BooleanInput 2) (BooleanInput t) ℂ,
          ExactMatchgateMatrix H ∧ H.rank = 4 ∧
          ∃ q : LabelledCommonPresentation S (Fin 3) 2,
            p.baseMatrix = q.baseMatrix * H ∧ q.left = p.left ∧
            q.language = p.language ∧ ExactlyLabelledEquivalent p.language q.language

/-- Paper 10.8. -/
def claim_10_8 : Prop :=
  ∀ {r t : ℕ}
    (B : Matrix (BooleanInput r) (BooleanInput t) ℂ)
    (_hB : ExactMatchgateMatrix B) (_hr : B.rank = 2),
    ∃ (Q : Matrix (BooleanInput 1) (BooleanInput t) ℂ)
      (D : Matrix (BooleanInput t) (BooleanInput 1) ℂ)
      (ht : 0<t) (C Cinv : Matrix (BooleanInput t) (BooleanInput t) ℂ),
      ExactMatchgateMatrix Q ∧ ExactMatchgateMatrix D ∧ Q*D=1 ∧
      Q.rank=2 ∧ orderedRowSpace Q = orderedRowSpace B ∧
      Q.row (fun _ => 0) ≠ 0 ∧ Q.row (fun _ => 1) ≠ 0 ∧
      (∀ y, booleanParity y ≠ 0 → Q (fun _ => 0) y = 0) ∧
      (∀ y, booleanParity y = 0 → Q (fun _ => 1) y = 0) ∧
      ExactMatchgateMatrix C ∧ ExactMatchgateMatrix Cinv ∧ C*Cinv=1 ∧ Cinv*C=1 ∧
      Matrix.vecMul (Q.row (fun _ => 0)) C = outputVacuum ∧
      Matrix.vecMul (Q.row (fun _ => 1)) C = Pi.single (singletonWord ⟨0,ht⟩) 1 ∧
      (∀ m (h : BooleanTable m ℂ),
        ExactMatchgate (leftBooleanLift Q m (fun x => h (fun i => x i 0))) →
        ExactMatchgate h) ∧
      (∀ m (G : BooleanTable (m*t) ℂ), ExactMatchgate G →
        (∀ j, columnSupport (portFlatten (fun x => G (flattenBooleanBlocks x)) j) ≤
          orderedRowSpace B) →
        ExactMatchgate (booleanPlanePullback D m G) ∧
        leftBooleanLift Q m (fun x => booleanPlanePullback D m G (fun i => x i 0)) = G)

/-- Paper 10.9-lines. -/
def claim_10_9_lines : Prop :=
  ∀ {n t : ℕ}
    (M : Matrix (Fin 3) (BooleanInput t) ℂ) (_hM : M.rank=3)
    (T : (Fin n → Fin 3) → ℂ) (_hne : T ≠ 0)
    (_hT : ExactMatchgate (leftBooleanLift M n T))
    (_hline : ∀ j, Module.finrank ℂ (columnSupport (portFlatten T j)) = 1),
    ∃ (c : ℂ) (q : Fin n → Fin 3 → ℂ), c ≠ 0 ∧ (∀ j, q j ≠ 0) ∧
      (∀ x, T x = c * ∏ j, q j (x j)) ∧
      (∀ j, ExactMatchgate (unaryTransform M (q j)))

/-- Paper 10.9-flag. -/
def claim_10_9_flag : Prop :=
  ∀ {s t : ℕ}
    (M : Matrix (Fin 3) (BooleanInput t) ℂ) (_hM : M.rank=3)
    (P : Submodule ℂ (Fin 3 → ℂ))
    (B : Matrix (BooleanInput s) (BooleanInput t) ℂ)
    (_hB : ExactMatchgateMatrix B) (_hrB : B.rank=2)
    (_hspace : orderedRowSpace B = P.map M.transpose.mulVecLin),
    ∃ (E : Matrix (BooleanInput 1) (Fin 3) ℂ)
      (D : Matrix (BooleanInput t) (BooleanInput 1) ℂ),
      Submodule.span ℂ (Set.range E.row) = P ∧
      ExactMatchgateMatrix (E*M) ∧ ExactMatchgateMatrix D ∧ (E*M)*D=1 ∧
      (E*M).rank=2 ∧
      (E*M).row (fun _ => 0) ≠ 0 ∧ (E*M).row (fun _ => 1) ≠ 0 ∧
      (∀ y, booleanParity y ≠ 0 → (E*M) (fun _ => 0) y = 0) ∧
      (∀ y, booleanParity y = 0 → (E*M) (fun _ => 1) y = 0) ∧
      primitiveParityEndpoint M P 0 = Submodule.span ℂ {E.row (fun _ => 0)} ∧
      primitiveParityEndpoint M P 1 = Submodule.span ℂ {E.row (fun _ => 1)} ∧
      (∃ (ht : 0<t) (C Cinv : Matrix (BooleanInput t) (BooleanInput t) ℂ),
        ExactMatchgateMatrix C ∧ ExactMatchgateMatrix Cinv ∧ C*Cinv=1 ∧ Cinv*C=1 ∧
        Matrix.vecMul ((E*M).row (fun _ => 0)) C = outputVacuum ∧
        Matrix.vecMul ((E*M).row (fun _ => 1)) C = Pi.single (singletonWord ⟨0,ht⟩) 1) ∧
      ∀ (r : Fin 3 → ℂ), r ≠ 0 → r ∉ P →
      ∀ (n : ℕ) (T : (Fin n → Fin 3) → ℂ), T ≠ 0 →
        ExactMatchgate (leftBooleanLift M n T) →
        (∀ j, columnSupport (portFlatten T j) = P ∨
          columnSupport (portFlatten T j) = primitiveParityEndpoint M P 0 ∨
          columnSupport (portFlatten T j) = primitiveParityEndpoint M P 1 ∨
          columnSupport (portFlatten T j) = Submodule.span ℂ {r}) →
        let I := planeSupportedPorts P T
        let e := (planePortEmbedding P T).toEmbedding
        let q := fun j => fixedFlagRay E r (columnSupport (portFlatten T j))
        ∃ h : BooleanTable I.card ℂ, ExactMatchgate h ∧ h ≠ 0 ∧
          StrictMono e ∧ T = flagTensor E e q h ∧
          (∀ i, Module.finrank ℂ (columnSupport (portFlatten h i)) = 2) ∧
          (I.card = 0 ∨ 2 ≤ I.card) ∧
          (∀ j, j ∉ Set.range e → q j ≠ 0 ∧
            columnSupport (portFlatten T j) = Submodule.span ℂ {q j} ∧
            ExactMatchgate (unaryTransform M (q j))) ∧
          ExactMatchgate (unaryTransform M (E.row (fun _ => 0))) ∧
          ExactMatchgate (unaryTransform M (E.row (fun _ => 1)))

/-- Paper 10.10. -/
def claim_10_10 : Prop :=
  ∀ {S : LabelledShape} {t : ℕ} (p : LabelledCommonPresentation S (Fin 3) t)
    (_hM : p.baseMatrix.rank = 3)
    (P L : Submodule ℂ (Fin 3 → ℂ))
    (_hP : P ∈ allLeftRealizedSupports p.language 2)
    (_hL : L ∈ allLeftRealizedSupports p.language 1) (_hLP : ¬ L ≤ P)
    (pPlus pMinus ell : Fin 3 → ℂ)
    (_hplus : pPlus ≠ 0) (_hminus : pMinus ≠ 0) (_hell : ell ≠ 0)
    (_hplus_mem : pPlus ∈ primitiveParityEndpoint p.baseMatrix P 0)
    (_hminus_mem : pMinus ∈ primitiveParityEndpoint p.baseMatrix P 1)
    (_hell_mem : ell ∈ L),
    let U : Matrix (Fin 3) (Fin 3) ℂ := ![pPlus,pMinus,ell]
    ∃ N : Matrix (Fin 3) (Fin 3) ℂ,
      U.rank = 3 ∧ U * N = 1 ∧ N * U = 1 ∧
      (BinarySmallCover p.baseMatrix ∨
        ∀ a b c (I : AllLeftGadget S a b c 2), I.Connected → Nonempty I.OrderedPlanar →
          PartialMonomial (binaryContextCoordinates N (I.value p.language))) ∧
      (∀ a b c (I : AllLeftGadget S a b c 2), I.Connected → Nonempty I.OrderedPlanar →
        ¬ PartialMonomial (binaryContextCoordinates N (I.value p.language)) →
        ∃ w ≤ 3, ∃ q : LabelledCommonPresentation S (Fin 3) w,
          q.left = p.left ∧ q.language = p.language ∧
          ExactlyLabelledEquivalent p.language q.language)

/-- Paper 2.1. -/
def claim_2_1 : Prop :=
  ∀ {S T : LabelledShape} {D E : Type}
    [Fintype D] [Fintype E] (F : LabelledLanguage S D) (G : LabelledLanguage T E),
    ExactlyLabelledEquivalent F G ↔ ExactlyLabelledEquivalentOn
      (fun _ _ _ I => Nonempty I.OrderedPlanar) F G

/-- Paper 2.2-existence. -/
def claim_2_2_existence : Prop :=
  ∀ {S : LabelledShape} {D : Type} [Fintype D]
    (C : LabelledInstanceClass S) (F : LabelledLanguage S D)
    (h : ∃ r, HasExactCommonWidthOn C F r),
    HasExactCommonWidthOn C F (minimumExactCommonWidthOn C F h)

/-- Paper 2.2-minimum. -/
def claim_2_2_minimum : Prop :=
  ∀ {S : LabelledShape} {D : Type} [Fintype D]
    (C : LabelledInstanceClass S) (F : LabelledLanguage S D)
    (h : ∃ r, HasExactCommonWidthOn C F r) {r : ℕ}
    (_hr : HasExactCommonWidthOn C F r),
    minimumExactCommonWidthOn C F h ≤ r

/-- Paper 4.4. -/
def claim_4_4 : Prop :=
  ∀ {S : LabelledShape} {D : Type} [Fintype D] {t : ℕ} (p : LabelledCommonPresentation S D t),
    (∀ l, ExactMatchgate (fun z => leftTransform p.base (p.left l)
      (fun i j => z (finProdFinEquiv (i,j))))) ∧
    (∀ l, ExactMatchgate (p.rightPreimage l))

/-- Paper 4.5-flag. -/
def claim_4_5_flag : Prop :=
  ∀ {S : LabelledShape} {t : ℕ}
    (p : LabelledCommonPresentation S (Fin 3) t)
    (P L : Submodule ℂ (Fin 3 → ℂ)),
    AllLeftMonomialFlag p P L ↔
      P ∈ allLeftRealizedSupports p.language 2 ∧
      L ∈ allLeftRealizedSupports p.language 1 ∧ ¬L≤P ∧
      allLeftRealizedSupports p.language 2 = {P} ∧
      allLeftRealizedSupports p.language 1 ⊆
        {primitiveParityEndpoint p.baseMatrix P 0,primitiveParityEndpoint p.baseMatrix P 1,L}

/-- Paper 4.5-prime. -/
def claim_4_5_prime : Prop :=
  ∀ {S : LabelledShape} {t : ℕ}
    (p : LabelledCommonPresentation S (Fin 3) t),
    AllLeftConnectionPrime p ↔
      sSup (allLeftRealizedSupports p.language 1 ∪ allLeftRealizedSupports p.language 2)=⊤ ∧
      (allLeftRealizedSupports p.language 2).Nonempty ∧
      ¬∃ P L, AllLeftMonomialFlag p P L

/-- Paper 3.4. -/
def claim_3_4 : Prop :=
  IntegerMainConclusions 2 (by decide) ∧
    AllLeftFlagAlternative (integerRationalPresentation 2 (by decide)) ∧
    ∀ C : LabelledInstanceClass (starLanguageShape 4),
      HasExactCommonWidthOn C (integerRationalPresentation 2 (by decide)).language 7

/-- Paper 6.5. -/
def claim_6_5 : Prop :=
  ∀ (k : ℕ) (_hk : 2 ≤ k),
    (∀ z, 0 < Effective.integerTableForArity k z) ∧
    (∀ r, HasMGIStarRepresentation k r (fun z => (Effective.integerTableForArity k z : ℂ)) →
      2 ^ k ≤ D k r) ∧
    ∀ i : Fin k, (oneVsRestFlattening (fun z => (Effective.integerTableForArity k z : ℂ)) i).rank = 2

end
end MatchgateWidth.Paper
