import MatchgateWidth.AlgebraicObstruction
import MatchgateWidth.MGIBlockContraction
import MatchgateWidth.WidthAsymptotics
import Mathlib.Algebra.BigOperators.Fin

/-!
# Arbitrary-domain closed-star extraction and its width obstruction

This is the coordinate interface of Section 9 of arXiv:2610.00079v1.
The competitor domain, common base, and complex coefficients are arbitrary.
The observational hypothesis says exactly that the fixed closed labelled stars
have the specified values. It is weaker than exact equivalence of entire
labelled planar languages, and is not a width hypothesis.

The first two whole unary leaves are contracted in order. The final hard blocks
keep their original order, as witnessed by `flattenBooleanBlocks_cons` below.
The only changes of `Fin` type are equality casts, never wire permutations.

For the paper's graph-defined matchgates and full exact-labelled equivalence,
two source interfaces remain outside this theorem: necessity of the literal
MGI for planar graph deletion signatures, and an API turning exact-labelled
language equivalence and its selected stars into this observational equality.
Neither interface is asserted or assumed as a proved graph theorem here.
-/

namespace MatchgateWidth

noncomputable section

/-- Changing a boundary length by an equality preserves every index value. -/
def castBooleanTable {m n : ℕ} {R : Type*} (h : m = n)
    (Q : BooleanTable m R) : BooleanTable n R :=
  fun z => Q (z ∘ Fin.cast h)

/-- An equality cast is not a permutation of the ordered boundary. -/
theorem BooleanMatchgateIdentities.cast {m n : ℕ} {R : Type*} [CommRing R]
    (h : m = n) {Q : BooleanTable m R} (hQ : BooleanMatchgateIdentities Q) :
    BooleanMatchgateIdentities (castBooleanTable h Q) := by
  cases h
  exact hQ

/-- Flattening a first block followed by the remaining blocks is exactly
`Fin.append`, up to the arithmetic equality of the two boundary lengths. -/
theorem flattenBooleanBlocks_cons {k r : ℕ} (x : BooleanInput r)
    (xs : Fin k → BooleanInput r) :
    flattenBooleanBlocks (Fin.cons x xs) =
      Fin.append x (flattenBooleanBlocks xs) ∘
        Fin.cast (show (k + 1) * r = r + k * r by ring) := by
  funext j
  obtain ⟨⟨i, t⟩, rfl⟩ := finProdFinEquiv.surjective j
  rw [flattenBooleanBlocks_apply]
  induction i using Fin.cases with
  | zero =>
    have hi : Fin.cast (show (k + 1) * r = r + k * r by ring)
        (finProdFinEquiv (0, t)) = Fin.castAdd (k * r) t := by
      apply Fin.ext
      simp [finProdFinEquiv]
    simp only [Function.comp_apply, hi, Fin.append_left, Fin.cons_zero]
  | succ i =>
    have hi : Fin.cast (show (k + 1) * r = r + k * r by ring)
        (finProdFinEquiv (i.succ, t)) = Fin.natAdd r (finProdFinEquiv (i, t)) := by
      apply Fin.ext
      simp only [Fin.val_cast, finProdFinEquiv, Equiv.coe_fn_mk,
        Fin.val_succ, Fin.val_natAdd]
      ring
    simp only [Function.comp_apply, hi, Fin.append_right,
      flattenBooleanBlocks_apply, Fin.cons_succ]

/-- Contract exactly the first whole block, leaving all remaining ports ordered. -/
def contractFirstStarBlock {k r : ℕ} {R : Type*} [CommSemiring R]
    (g : BooleanTable r R) (Q : BooleanTable ((k + 1) * r) R) :
    BooleanTable (k * r) R :=
  fun y => ∑ x : BooleanInput r, g x *
    castBooleanTable (show (k + 1) * r = r + k * r by ring) Q (Fin.append x y)

/-- The concrete first-block contraction satisfies the literal MGI. -/
theorem BooleanMatchgateIdentities.contractFirstStarBlock {k r : ℕ}
    {R : Type*} [CommRing R] {g : BooleanTable r R}
    {Q : BooleanTable ((k + 1) * r) R}
    (hg : BooleanMatchgateIdentities g) (hQ : BooleanMatchgateIdentities Q) :
    BooleanMatchgateIdentities (MatchgateWidth.contractFirstStarBlock g Q) :=
  hg.unaryBlockContraction (hQ.cast _)

/-- Actual finite-sum associativity for a whole first leaf. In particular this
is valid at width zero, and no nonzero or normalization condition is imposed. -/
theorem starContract_cons_contractFirst {k r : ℕ} {R : Type*} [CommSemiring R]
    (Q : BooleanTable ((k + 1) * r) R) (g : BooleanTable r R)
    (gs : Fin k → BooleanTable r R) :
    starContract (fun x => Q (flattenBooleanBlocks x)) (Fin.cons g gs) =
      starContract (fun x => contractFirstStarBlock g Q (flattenBooleanBlocks x)) gs := by
  classical
  unfold starContract
  calc
    _ = ∑ p : BooleanInput r × (Fin k → BooleanInput r),
        Q (flattenBooleanBlocks (Fin.cons p.1 p.2)) *
          ∏ i, (Fin.cons g gs : Fin (k + 1) → BooleanTable r R) i
            ((Fin.cons p.1 p.2 : Fin (k + 1) → BooleanInput r) i) := by
      convert ((Fin.consEquiv (fun _ : Fin (k + 1) => BooleanInput r)).sum_comp
        (fun x => Q (flattenBooleanBlocks x) *
          ∏ i, (Fin.cons g gs : Fin (k + 1) → BooleanTable r R) i (x i))).symm using 1
      · congr 1
        ext
        simp
      · congr 1
    _ = _ := by
      rw [Fintype.sum_prod_type]
      simp only [Fin.prod_univ_succ, Fin.cons_zero,
        Fin.cons_succ, flattenBooleanBlocks_cons]
      unfold contractFirstStarBlock castBooleanTable
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr (by ext; simp)
      intro xs _
      apply Finset.sum_congr (by ext; simp)
      intro x _
      ring

/-- The original hard stars use labels 0 and 2, never label 1. -/
def hardStarLabel (b : Fin 2) : Fin 3 := if b = 0 then 0 else 2

/-- Two link leaves labelled 0, followed by the hard leaves in their given order. -/
def closedStarLeaves {k : ℕ} {E R : Type*} (P : Fin 3 → E → R)
    (z : BooleanInput k) : Fin (k + 2) → E → R :=
  Fin.cons (P 0) (Fin.cons (P 0) (fun i => P (hardStarLabel (z i))))

/-- The arbitrary competitor data actually needed to extract the sampled star.
The domain can be empty and the base need not be injective or full rank.
`observes` is equality of particular closed-star values, not language equivalence
or a lower-bound premise. Label 1 is retained to record all three unary labels. -/
structure CommonBaseClosedStarPresentation (E : Type*) [Fintype E]
    (k r : ℕ) (f : BooleanTable k ℂ) where
  base : E → BooleanInput r → ℂ
  labels : Fin 3 → E → ℂ
  center : BooleanTable ((k + 2) * r) ℂ
  validUnary : ∀ b, BooleanMatchgateIdentities (unaryTransform base (labels b))
  validCenter : BooleanMatchgateIdentities center
  observes : ∀ z, f z =
    starContract (rightTransform base (fun x => center (flattenBooleanBlocks x)))
      (closedStarLeaves labels z)

/-- Direct Section 9 extraction from arbitrary finite-domain coordinate data.
`Q₀` is constructed by two consecutive entire-leaf contractions. -/
theorem closedStar_extraction {E : Type*} [Fintype E] {k r : ℕ}
    {f : BooleanTable k ℂ} (N : E → BooleanInput r → ℂ)
    (P : Fin 3 → E → ℂ) (Q : BooleanTable ((k + 2) * r) ℂ)
    (hP : ∀ b, BooleanMatchgateIdentities (unaryTransform N (P b)))
    (hQ : BooleanMatchgateIdentities Q)
    (hstars : ∀ z, f z =
      starContract (rightTransform N (fun x => Q (flattenBooleanBlocks x)))
        (closedStarLeaves P z)) :
    HasMGIStarRepresentation k r f := by
  classical
  let g : Fin 3 → BooleanTable r ℂ := fun b => unaryTransform N (P b)
  let Q₁ : BooleanTable ((k + 1) * r) ℂ := contractFirstStarBlock (g 0) Q
  let Q₀ : BooleanTable (k * r) ℂ := contractFirstStarBlock (g 0) Q₁
  refine ⟨(fun b => g (hardStarLabel b)), Q₀, ?_, ?_, ?_⟩
  · intro b
    exact hP (hardStarLabel b)
  · exact (hP 0).contractFirstStarBlock ((hP 0).contractFirstStarBlock hQ)
  · intro z
    calc
      f z = starContract
          (rightTransform N (fun x => Q (flattenBooleanBlocks x)))
          (closedStarLeaves P z) := hstars z
      _ = starContract (fun x => Q (flattenBooleanBlocks x))
          (fun i => unaryTransform N (closedStarLeaves P z i)) :=
        starContract_rightTransform N _ _
      _ = starContract (fun x => Q (flattenBooleanBlocks x))
          (Fin.cons (g 0) (Fin.cons (g 0) (fun i => g (hardStarLabel (z i))))) := by
        congr 1
        funext i
        induction i using Fin.cases with
        | zero => rfl
        | succ i =>
          induction i using Fin.cases with
          | zero => rfl
          | succ i => rfl
      _ = starContract (fun x => Q₁ (flattenBooleanBlocks x))
          (Fin.cons (g 0) (fun i => g (hardStarLabel (z i)))) :=
        starContract_cons_contractFirst Q (g 0) _
      _ = starContract (fun x => Q₀ (flattenBooleanBlocks x))
          (fun i => g (hardStarLabel (z i))) :=
        starContract_cons_contractFirst Q₁ (g 0) _

/-- A convenient packaged form of the same extraction theorem. -/
theorem CommonBaseClosedStarPresentation.hasMGIStarRepresentation
    {E : Type*} [Fintype E] {k r : ℕ} {f : BooleanTable k ℂ}
    (p : CommonBaseClosedStarPresentation E k r f) :
    HasMGIStarRepresentation k r f :=
  closedStar_extraction p.base p.labels p.center p.validUnary p.validCenter p.observes

/-- Applying the constructed obstruction to actual competitor coordinates.
There is no width conclusion among the competitor hypotheses. -/
theorem CommonBaseClosedStarPresentation.budget
    {E : Type*} [Fintype E] {k r : ℕ} {f : BooleanTable k ℂ}
    (p : CommonBaseClosedStarPresentation E k r f)
    (hf : ∀ s, HasMGIStarRepresentation k s f → 2 ^ k ≤ D k s) :
    2 ^ k ≤ D k r :=
  hf r p.hasMGIStarRepresentation

/-- Exact polynomial necessary inequality, now obtained from closed-star data. -/
theorem CommonBaseClosedStarPresentation.exact_lower_bound
    {E : Type*} [Fintype E] {k r : ℕ} {f : BooleanTable k ℂ}
    (p : CommonBaseClosedStarPresentation E k r f)
    (hf : ∀ s, HasMGIStarRepresentation k s f → 2 ^ k ≤ D k s) :
    (2 : ℝ) ^ k ≤ 3 + (r : ℝ) * ((r : ℝ) - 1) +
      ((k : ℝ) * (r : ℝ)) * ((k : ℝ) * (r : ℝ) - 1) / 2 :=
  exact_necessary_inequality (p.budget hf)

/-- The natural ceiling lower bound includes the possible competitor width zero. -/
theorem CommonBaseClosedStarPresentation.ceil_lower_bound
    {E : Type*} [Fintype E] {k r : ℕ} {f : BooleanTable k ℂ}
    (p : CommonBaseClosedStarPresentation E k r f)
    (hf : ∀ s, HasMGIStarRepresentation k s f → 2 ^ k ≤ D k s) :
    ⌈Real.sqrt (((2 : ℝ) ^ k - 3) / (1 + (k : ℝ) ^ 2 / 2))⌉₊ ≤ r :=
  natCeil_sqrt_lower_bound (p.budget hf)

/-- A concrete pointwise constant for the exponential-over-linear scale. -/
theorem CommonBaseClosedStarPresentation.exponential_lower_bound
    {E : Type*} [Fintype E] {k r : ℕ} {f : BooleanTable k ℂ}
    (p : CommonBaseClosedStarPresentation E k r f) (hk : 2 ≤ k)
    (hf : ∀ s, HasMGIStarRepresentation k s f → 2 ^ k ≤ D k s) :
    (1 / 2 : ℝ) * (Real.rpow 2 ((k : ℝ) / 2) / (k : ℝ)) ≤ (r : ℝ) :=
  half_rpow_div_le_width hk (p.budget hf)

/-- An actual positive, full-flattening-rank integer obstruction works against
every finite competitor domain, every common base, and all complex weights. -/
theorem exists_positive_integer_closedStar_obstruction (k : ℕ) (hk : 2 ≤ k) :
    ∃ a : BooleanTable k ℕ, (∀ z, 0 < a z) ∧
      (∀ i : Fin k, (oneVsRestFlattening (fun z => (a z : ℂ)) i).rank = 2) ∧
      ∀ (E : Type*) [Fintype E] (r : ℕ),
        CommonBaseClosedStarPresentation E k r (fun z => (a z : ℂ)) →
          2 ^ k ≤ D k r ∧
          ⌈Real.sqrt (((2 : ℝ) ^ k - 3) / (1 + (k : ℝ) ^ 2 / 2))⌉₊ ≤ r ∧
          (1 / 2 : ℝ) * (Real.rpow 2 ((k : ℝ) / 2) / (k : ℝ)) ≤ (r : ℝ) := by
  obtain ⟨a, ha, hbudget, hrank⟩ := exists_positive_integer_MGI_obstruction k hk
  refine ⟨a, ha, hrank, ?_⟩
  intro E inst r p
  exact ⟨p.budget hbudget, p.ceil_lower_bound hbudget,
    p.exponential_lower_bound hk hbudget⟩

/-- Any sequence of actual closed-star presentations of an obstructed family
has the stated asymptotic scale, even with different domains and bases at each
arity. Only the observation equations and literal MGI validity are used. -/
theorem closedStar_widths_paperOmega
    (f : (k : ℕ) → BooleanTable k ℂ)
    (hf : ∀ k, 2 ≤ k → ∀ r, HasMGIStarRepresentation k r (f k) → 2 ^ k ≤ D k r)
    (E : ℕ → Type*) [∀ k, Fintype (E k)] (width : ℕ → ℕ)
    (hp : ∀ k, 2 ≤ k →
      Nonempty (CommonBaseClosedStarPresentation (E k) k (width k) (f k))) :
    PaperOmega (fun k => (width k : ℝ))
      (fun k => Real.rpow 2 ((k : ℝ) / 2) / (k : ℝ)) := by
  apply paperOmega_widths_of_budget
  intro k hk
  obtain ⟨p⟩ := hp k hk
  exact p.budget (hf k hk)

/-- The corresponding Mathlib `IsBigO` formulation of the same Ω statement. -/
theorem closedStar_widths_scale_isBigO
    (f : (k : ℕ) → BooleanTable k ℂ)
    (hf : ∀ k, 2 ≤ k → ∀ r, HasMGIStarRepresentation k r (f k) → 2 ^ k ≤ D k r)
    (E : ℕ → Type*) [∀ k, Fintype (E k)] (width : ℕ → ℕ)
    (hp : ∀ k, 2 ≤ k →
      Nonempty (CommonBaseClosedStarPresentation (E k) k (width k) (f k))) :
    Asymptotics.IsBigO Filter.atTop
      (fun k : ℕ => Real.rpow 2 ((k : ℝ) / 2) / (k : ℝ))
      (fun k : ℕ => (width k : ℝ)) :=
  (paperOmega_iff_isBigO _ _).mp (closedStar_widths_paperOmega f hf E width hp)

/-- A family of positive integer tables, constructed by the established
obstruction theorem, forces Ω(2^(k/2)/k) for arbitrary-domain competitors.
The family is positive at every arity and has every flattening rank two from
arity two. There is no family-wide budget assumption in this conclusion. -/
theorem exists_positive_integer_closedStar_family :
    ∃ a : (k : ℕ) → BooleanTable k ℕ,
      (∀ k z, 0 < a k z) ∧
      (∀ k, 2 ≤ k → ∀ i : Fin k,
        (oneVsRestFlattening (fun z => (a k z : ℂ)) i).rank = 2) ∧
      ∀ (E : ℕ → Type*) [∀ k, Fintype (E k)] (width : ℕ → ℕ),
        (∀ k, 2 ≤ k → Nonempty
          (CommonBaseClosedStarPresentation (E k) k (width k) (fun z => (a k z : ℂ)))) →
        PaperOmega (fun k => (width k : ℝ))
          (fun k => Real.rpow 2 ((k : ℝ) / 2) / (k : ℝ)) := by
  classical
  have hex (k : ℕ) : ∃ a : BooleanTable k ℕ, (∀ z, 0 < a z) ∧
      (2 ≤ k → (∀ r, HasMGIStarRepresentation k r (fun z => (a z : ℂ)) →
        2 ^ k ≤ D k r) ∧
        ∀ i : Fin k, (oneVsRestFlattening (fun z => (a z : ℂ)) i).rank = 2) := by
    by_cases hk : 2 ≤ k
    · obtain ⟨a, ha, hb, hr⟩ := exists_positive_integer_MGI_obstruction k hk
      exact ⟨a, ha, fun _ => ⟨hb, hr⟩⟩
    · exact ⟨fun _ => 1, fun _ => Nat.zero_lt_one, fun h => (hk h).elim⟩
  choose a ha hrest using hex
  refine ⟨a, ha, (fun k hk => (hrest k hk).2), ?_⟩
  intro E inst width hp
  exact closedStar_widths_paperOmega (fun k z => (a k z : ℂ))
    (fun k hk => (hrest k hk).1) E width hp

/-- For every proposed uniform width bound there is a positive full-rank table
whose observed stars require larger width over every finite competitor domain. -/
theorem positive_integer_closedStars_require_unbounded_width (B : ℕ) :
    ∃ k : ℕ, 2 ≤ k ∧ ∃ a : BooleanTable k ℕ,
      (∀ z, 0 < a z) ∧
      (∀ i : Fin k, (oneVsRestFlattening (fun z => (a z : ℂ)) i).rank = 2) ∧
      ∀ (E : Type*) [Fintype E] (r : ℕ),
        CommonBaseClosedStarPresentation E k r (fun z => (a z : ℂ)) → B < r := by
  obtain ⟨k, hk, a, ha, hrank, hwidth⟩ :=
    positive_integer_tables_require_unbounded_MGI_star_width B
  refine ⟨k, hk, a, ha, hrank, ?_⟩
  intro E inst r p
  exact hwidth r p.hasMGIStarRepresentation

end
end MatchgateWidth
