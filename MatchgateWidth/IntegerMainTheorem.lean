import MatchgateWidth.ControlledRanksProposition
import MatchgateWidth.ControlledPresentationProposition
import MatchgateWidth.ControlledLabelledPresentation
import MatchgateWidth.ControlledFlagSupports
import MatchgateWidth.TwoCenterGadget
import MatchgateWidth.LabelledStarExtraction
import MatchgateWidth.WidthAdmissibility

/-! # The integer unbounded-width family of Theorem 3.1

One positive integer table is selected at each `k ≥ 2`. Every assertion below
uses that same table: the rational Pfaffian presentation, integer coordinates,
exact ranks, essentiality, connected planar coupling, and unrestricted
competitor lower bounds. Competitors may change the domain, base, and labelled
shape and use arbitrary complex weights. The explicit model only restricts the
class of observed instances, not competitors. The stronger-admissibility
versions apply to the full source instance class without identifying minima.
-/
namespace MatchgateWidth
noncomputable section
open scoped Classical

/-- A single fixed positive integer table per arity. The unused small arities
are filled with ones so that the chosen family is an ordinary sequence. -/
def integerHardTable (k : ℕ) : BooleanTable k ℕ :=
  if hk : 2 ≤ k then Classical.choose (exists_positive_integer_MGI_obstruction k hk)
  else fun _ => 1

theorem integerHardTable_positive (k : ℕ) : ∀ x, 0 < integerHardTable k x := by
  by_cases hk : 2 ≤ k
  · simpa only [integerHardTable, dite_eq_left hk] using
      (Classical.choose_spec (exists_positive_integer_MGI_obstruction k hk)).1
  · simp [integerHardTable, hk]

theorem integerHardTable_budget (k : ℕ) (hk : 2 ≤ k) :
    ∀ r, HasMGIStarRepresentation k r (fun x => (integerHardTable k x : ℂ)) →
      2 ^ k ≤ D k r := by
  simpa only [integerHardTable, dite_eq_left hk] using
    (Classical.choose_spec (exists_positive_integer_MGI_obstruction k hk)).2.1

theorem integerHardTable_ranks (k : ℕ) (hk : 2 ≤ k) :
    ∀ i, (oneVsRestFlattening (fun x => (integerHardTable k x : ℂ)) i).rank = 2 := by
  simpa only [integerHardTable, dite_eq_left hk] using
    (Classical.choose_spec (exists_positive_integer_MGI_obstruction k hk)).2.2

/-- The common table interpreted in a characteristic-zero field. -/
def integerHardTableIn (K : Type*) [Field K] [CharZero K] (k : ℕ) : BooleanTable k K :=
  fun x => (integerHardTable k x : K)

theorem integerHardTableIn_ne_zero (K : Type*) [Field K] [CharZero K] (k : ℕ) :
    ∀ x, integerHardTableIn K k x ≠ 0 :=
  fun x => Nat.cast_ne_zero.mpr (Nat.ne_of_gt (integerHardTable_positive k x))

theorem integerHardTableIn_integer (K : Type*) [Field K] [CharZero K] (k : ℕ) :
    ∀ x, ∃ n : ℤ, integerHardTableIn K k x = n := by
  intro x
  exact ⟨(integerHardTable k x : ℤ), by simp [integerHardTableIn]⟩

/-- Fix the first of the ordered hard ports. -/
def integerControlPort (k : ℕ) (hk : 2 ≤ k) : Fin k := ⟨0, by omega⟩

/-- The four left labels and sole right label of the main family. -/
def integerControlledLanguage (k : ℕ) (hk : 2 ≤ k) :
    LabelledLanguage (starLanguageShape (k + 2)) (Fin 3) :=
  controlledLabelledLanguage (integerHardTableIn ℂ k) (integerControlPort k hk)

/-- The displayed source presentation has finite exact common width. -/
theorem integerControlledLanguage_hasWidth (k : ℕ) (hk : 2 ≤ k) :
    HasExactCommonWidth (integerControlledLanguage k hk) (2 ^ k + 3) :=
  controlledLabelledLanguage_hasExactCommonWidth (integerHardTableIn ℂ k)
    (integerHardTableIn_ne_zero ℂ k) (integerControlPort k hk)

theorem integerControlledLanguage_finiteWidth (k : ℕ) (hk : 2 ≤ k) :
    ∃ r, HasExactCommonWidth (integerControlledLanguage k hk) r :=
  ⟨2 ^ k + 3, integerControlledLanguage_hasWidth k hk⟩

/-- The true minimum in the explicit ordered geometric instance model. -/
def integerControlledMinimum (k : ℕ) (hk : 2 ≤ k) : ℕ :=
  minimumExactCommonWidth (integerControlledLanguage k hk)
    (integerControlledLanguage_finiteWidth k hk)

/-- Every competing finite domain, common base and arity-preserving labelled
shape obeys the source budget; no full-rank or normalization is assumed. -/
theorem integer_main_competitor_bound (k : ℕ) (hk : 2 ≤ k) {r : ℕ}
    {T : LabelledShape} {E : Type} [Fintype E]
    (p : LabelledCommonPresentation T E r)
    (h : ExactlyLabelledEquivalent (integerControlledLanguage k hk) p.language) :
    2 ^ k ≤ 2 * (1 + r.choose 2) + 1 + (k * r).choose 2 := by
  have hb := integerHardTable_budget k hk r
    (exactEquivalence_hasMGIStarRepresentation (integerHardTableIn ℂ k)
      (integerControlPort k hk) p h)
  simpa only [D, delta, Nat.add_assoc] using hb

theorem integer_main_width_budget (k : ℕ) (hk : 2 ≤ k) {r : ℕ}
    (h : HasExactCommonWidth (integerControlledLanguage k hk) r) : 2 ^ k ≤ D k r :=
  exactCommonWidth_budget (integerHardTableIn ℂ k) (integerControlPort k hk)
    (integerHardTable_budget k hk) h

/-- Exact inequality, source ceiling, and constructed upper bound for the
minimum. The lower bound includes width-zero competitors. -/
theorem integer_main_minimum_bounds (k : ℕ) (hk : 2 ≤ k) :
    2 ^ k ≤ 2 * (1 + (integerControlledMinimum k hk).choose 2) + 1 +
      (k * integerControlledMinimum k hk).choose 2 ∧
    ⌈Real.sqrt (((2 : ℝ) ^ k - 3) / (1 + (k : ℝ) ^ 2 / 2))⌉₊ ≤
      integerControlledMinimum k hk ∧
    integerControlledMinimum k hk ≤ 2 ^ k + 3 := by
  have hb := integer_main_width_budget k hk
    (minimumExactCommonWidth_spec _ (integerControlledLanguage_finiteWidth k hk))
  refine ⟨?_, natCeil_sqrt_lower_bound hb, ?_⟩
  · simpa only [integerControlledMinimum, D, delta, Nat.add_assoc] using hb
  · exact minimumExactCommonWidth_le _ _ (integerControlledLanguage_hasWidth k hk)

/-- All algebraic, arithmetic, planar and support clauses use the same selected
integer table. The network flag field quantifies every properly wired finite
network whose indicated boundary port is left-exposed, including all connected
ordered planar source gadgets. -/
structure IntegerMainConclusions (k : ℕ) (hk : 2 ≤ k) : Prop where
  domain_card : Fintype.card (Fin 3) = 3
  label_card : Fintype.card ControlledLanguageLabel = 5
  base_rank : (controlledCoordinateBase (K := ℚ) k).rank = 3
  base_columns : Fintype.card (ControlledWord k) = 2 ^ (2 ^ k + 3)
  positive_arity : ∀ l, 0 < Fintype.card (controlledLanguagePorts k l)
  maximum_arity : ∀ l, Fintype.card (controlledLanguagePorts k l) ≤ k + 2
  right_arity : Fintype.card (controlledLanguagePorts k .controlled) = k + 2
  rational_graphs : ∀ l : ControlledLanguageLabel,
    ∃ (v e : ℕ) (G : WeightedGraph (Fin v) (Fin e) ℂ)
      (ext : Fin (controlledLanguageBooleanArity k l) → Fin v),
      Nonempty (PlanarDrawing G ext) ∧ (∀ a, ∃ q : ℚ, G.weight a = q) ∧
      ∀ y, deletionSignature G ext y =
        ((controlledLanguageBoolean (integerHardTableIn ℚ k)
          (integerHardTableIn_ne_zero ℚ k) (integerControlPort k hk) l
          ((booleanWordEquiv _).symm y) : ℚ) : ℂ)
  actual_right_transform : sourceControlledB (integerHardTableIn ℂ k)
      (integerHardTableIn_ne_zero ℂ k) (integerControlPort k hk) =
    controlledQutrit (integerHardTableIn ℂ k) (integerControlPort k hk)
  integer_coordinates : ∀ l x, ∃ z : ℤ,
    controlledLanguageTensor (integerHardTableIn ℂ k) (integerControlPort k hk) l x = z
  port_ranks : ∀ l p,
    (portFlatten (controlledLanguageTensor (integerHardTableIn ℂ k)
      (integerControlPort k hk) l) p).rank = controlledLanguagePortRank l
  link_supports : ∀ l : Fin 2,
    columnSupport (portFlatten (controlledQutrit (integerHardTableIn ℂ k)
      (integerControlPort k hk)) (Sum.inl l)) =
    Submodule.span ℂ ({Pi.single 0 (1 : ℂ), Pi.single 1 (1 : ℂ)} : Set (Fin 3 → ℂ))
  hard_supports : ∀ i : Fin k,
    columnSupport (portFlatten (controlledQutrit (integerHardTableIn ℂ k)
      (integerControlPort k hk)) (Sum.inr i)) =
    Submodule.span ℂ ({Pi.single 0 (1 : ℂ), Pi.single 2 (1 : ℂ)} : Set (Fin 3 → ℂ))
  left_essential : ((⨆ r : Fin 3, columnSupport (portFlatten
      (qutritPinTensor (K := ℂ) r) 0)) ⊔
    (⨆ l : Fin 2, columnSupport (portFlatten (qutritNeqTensor (K := ℂ)) l))) = ⊤
  right_essential : (⨆ p : ControlledQutritPort k, columnSupport
    (portFlatten (controlledQutrit (integerHardTableIn ℂ k) (integerControlPort k hk)) p)) = ⊤
  connected_planar_two_center : Nonempty (TwoCenterNetworkPlanarCertificate k)
  two_center_rank : Matrix.rank (twoCenterValue (integerHardTableIn ℂ k)
    (integerHardTableIn_ne_zero ℂ k) (integerControlPort k hk) :
      Matrix (Fin k → Fin 3) (Fin k → Fin 3) ℂ) = 2
  flag_supports : ∀ {V E P : Type} [Fintype V] [Fintype E] [Fintype P]
    (labels : V → ControlledLanguageLabel)
    (inc : ∀ v, controlledLanguagePorts k (labels v) → E ⊕ P),
    ProperNetworkIncidences inc → ∀ p : P,
    (∀ v i, inc v i = Sum.inr p → labels v ≠ .controlled) →
    let T := networkValue inc (fun v => controlledLanguageTensor
      (integerHardTableIn ℂ k) (integerControlPort k hk) (labels v))
    (portFlatten T p).rank ≤ 2 ∧
    ((portFlatten T p).rank = 2 → columnSupport (portFlatten T p) = qutritCoordinatePlane 2) ∧
    ((portFlatten T p).rank = 1 → ∃ r : Fin 3,
      columnSupport (portFlatten T p) = qutritCoordinateRay r)
  finite_width : HasExactCommonWidth (integerControlledLanguage k hk) (2 ^ k + 3)
  every_width_budget : ∀ r, HasExactCommonWidth (integerControlledLanguage k hk) r →
    2 ^ k ≤ D k r

/-- Theorem 3.1's simultaneous construction and quantitative obstruction. -/
theorem integer_main_theorem (k : ℕ) (hk : 2 ≤ k) : IntegerMainConclusions k hk := by
  have hf := integerHardTableIn_ne_zero ℂ k
  have hr : ∀ i, (oneVsRestFlattening (integerHardTableIn ℂ k) i).rank = 2 :=
    integerHardTable_ranks k hk
  have hp := controlled_rational_presentation_proposition (integerHardTableIn ℚ k)
    (integerHardTableIn_ne_zero ℚ k) (integerHardTableIn_integer ℚ k) (integerControlPort k hk)
  refine {
    domain_card := Fintype.card_fin 3
    label_card := controlledLanguageLabel_card
    base_rank := controlledCoordinateBase_rank k
    base_columns := by simp [ControlledWord]
    positive_arity := ?_
    maximum_arity := ?_
    right_arity := by simp [controlledLanguagePorts, ControlledQutritPort, Nat.add_comm]
    rational_graphs := hp.2.2.2.1
    actual_right_transform := sourceControlledB_eq _ _ _
    integer_coordinates := controlledLanguageTensor_integer _ (integerHardTableIn_integer ℂ k) _
    port_ranks := controlledLanguageTensor_port_ranks _ hf _ hr
    link_supports := ?_
    hard_supports := ?_
    left_essential := qutritPins_and_neq_support_essential
    right_essential := controlledQutrit_support_essential _ _ (hf _) (hr _)
    connected_planar_two_center := ⟨twoCenterNetworkPlanarCertificate k⟩
    two_center_rank := twoCenterValue_rank _ hf _
    flag_supports := ?_
    finite_width := integerControlledLanguage_hasWidth k hk
    every_width_budget := fun _ h => integer_main_width_budget k hk h }
  · intro l
    cases l <;> simp [controlledLanguagePorts, ControlledQutritPort]
  · intro l
    cases l <;> simp [controlledLanguagePorts, ControlledQutritPort] <;> omega
  · intro l
    rw [controlledQutrit_link_support _ _ (hf _) l, qutritCoordinatePlane_two_eq_span]
  · intro i
    rw [controlledQutrit_hard_support _ _ i (hr i), qutritCoordinatePlane_one_eq_span]
  · intro V E P _ _ _ labels inc hinc p hleft
    exact controlled_network_support_flag labels inc hinc _ _ p hleft

/-- The sequence uses the actual minimum whenever the source parameter is at
least two. -/
def integerMainWidth (k : ℕ) : ℕ :=
  if hk : 2 ≤ k then integerControlledMinimum k hk else 0

theorem integerMainWidth_budget (k : ℕ) (hk : 2 ≤ k) :
    2 ^ k ≤ D k (integerMainWidth k) := by
  have h := (integer_main_minimum_bounds k hk).1
  simpa only [integerMainWidth, dite_eq_left hk, D, delta, Nat.add_assoc] using h

theorem integer_main_width_omega :
    PaperOmega (fun k => (integerMainWidth k : ℝ))
      (fun k => Real.rpow 2 ((k : ℝ) / 2) / (k : ℝ)) :=
  paperOmega_widths_of_budget integerMainWidth integerMainWidth_budget

theorem integer_main_width_unbounded (B : ℕ) : B < integerMainWidth (4 * B + 8) := by
  have hb := integerMainWidth_budget (4 * B + 8) (by omega)
  have hx := budget_lt_two_pow_at_explicit_arity B
  by_contra hn
  have hm := D_mono_width (4 * B + 8) (Nat.le_of_not_gt hn)
  omega

/-- Corollary 3.2's fixed-domain counterexample family. Every member has the
rational graph presentation, integer coordinates, positive arities, and only
rank-one/rank-two primitive ports proved in `integer_main_theorem`. -/
theorem integer_no_domain_cardinality_bound :
    ¬ ∃ h : ℕ → ℕ, ∀ k, 2 ≤ k → integerMainWidth k ≤ h (Fintype.card (Fin 3)) := by
  rintro ⟨h,hh⟩
  exact (not_le_of_gt (integer_main_width_unbounded (h 3)))
    (by simpa using hh (4 * h 3 + 8) (by omega))

/-- The full source minimum may use a stronger observational criterion. Its
budget still follows from the constructed stars; finiteness is justified by
acceptance of the literal displayed presentation at width `2^k+3`. -/
theorem integer_main_stronger_admissibility
    (W : ℕ → ℕ → Prop)
    (hdisplayed : ∀ k, 2 ≤ k → W k (2 ^ k + 3))
    (hmodel : ∀ k (hk : 2 ≤ k) r, W k r →
      HasExactCommonWidth (integerControlledLanguage k hk) r) :
    let hW : ∀ k, 2 ≤ k → ∃ r, W k r := fun k hk => ⟨2 ^ k + 3,hdisplayed k hk⟩
    (∀ k (hk : 2 ≤ k),
      2 ^ k ≤ D k (admissibleWidthSequence W hW k) ∧
      ⌈Real.sqrt (((2 : ℝ) ^ k - 3) / (1 + (k : ℝ) ^ 2 / 2))⌉₊ ≤
        admissibleWidthSequence W hW k ∧
      admissibleWidthSequence W hW k ≤ 2 ^ k + 3) ∧
    PaperOmega (fun k => (admissibleWidthSequence W hW k : ℝ))
      (fun k => Real.rpow 2 ((k : ℝ) / 2) / (k : ℝ)) ∧
    (∀ B, B < admissibleWidthSequence W hW (4 * B + 8)) ∧
    ¬ ∃ h : ℕ → ℕ, ∀ k, 2 ≤ k → admissibleWidthSequence W hW k ≤ h 3 := by
  dsimp only
  let hW : ∀ k, 2 ≤ k → ∃ r, W k r := fun k hk => ⟨2 ^ k + 3,hdisplayed k hk⟩
  have hb : ∀ k, 2 ≤ k → ∀ r, W k r → 2 ^ k ≤ D k r :=
    fun k hk r hr => integer_main_width_budget k hk (hmodel k hk r hr)
  refine ⟨?_, admissibleWidthSequence_omega W hW hb,
    admissibleWidthSequence_unbounded W hW hb, no_domain_cardinality_bound_of_budgets W hW hb⟩
  intro k hk
  have h := admissibleWidthSequence_lower_bound W hW hb k hk
  exact ⟨h.1,h.2,admissibleWidthSequence_le W hW k hk (hdisplayed k hk)⟩

end
end MatchgateWidth
