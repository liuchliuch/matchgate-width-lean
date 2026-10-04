import MatchgateWidth.OrderedAllLeftGadget
import MatchgateWidth.ConnectionPrimeCompression
import MatchgateWidth.FlagTensorNormalForm

/-!
# Actual all-left support closure and its Gaussian extraction interface

The support sets quantify actual connected ordered-planar gadgets and their
literal nonzero boundary tensors. Primitive port deficiency is propagated by
the proved boundary-support inclusion. Exact ordered lifting and cyclic block
rowspace extraction are named explicit dependencies, not definitions of a
gadget or assumptions of the desired common cover.
-/
namespace MatchgateWidth
noncomputable section
open scoped Classical
set_option maxHeartbeats 800000

/-- Source realized supports: actual ports of actual connected planar gadgets,
with the zero boundary tensor explicitly excluded. -/
def allLeftRealizedSupports {S : LabelledShape} (F : LabelledLanguage S (Fin 3))
    (d : ℕ) : Set (Submodule ℂ (Fin 3 → ℂ)) :=
  {U | ∃ a b c n, ∃ I : AllLeftGadget S a b c n,
    I.Connected ∧ Nonempty I.OrderedPlanar ∧ I.value F ≠ 0 ∧
    ∃ j : Fin n, U = columnSupport (portFlatten (I.value F) j) ∧ Module.finrank ℂ U = d}

/-- Port deficiency for the original labelled primitive left tensors. -/
def LeftPortDeficient {S : LabelledShape} (F : LabelledLanguage S (Fin 3)) : Prop :=
  ∀ l j, (portFlatten (F.left l) j).rank ≤ 2

/-- Port deficiency for every induced primitive right tensor. -/
def RightPortDeficient {S : LabelledShape} (F : LabelledLanguage S (Fin 3)) : Prop :=
  ∀ l j, (portFlatten (F.right l) j).rank ≤ 2

/-- A nonzero tensor has nonzero support at every actual port. -/
theorem portSupport_finrank_pos {n : ℕ} (T : (Fin n → Fin 3) → ℂ)
    (hne : T ≠ 0) (j : Fin n) :
    0 < Module.finrank ℂ (columnSupport (portFlatten T j)) := by
  by_contra h
  have hz : Module.finrank ℂ (columnSupport (portFlatten T j)) = 0 := by omega
  have hbot := Submodule.finrank_eq_zero.mp hz
  apply hne
  funext x
  have hc := portFlatten_column_mem T j (fun i => x i)
  rw [hbot] at hc
  have he : (fun d => T (insertBoundaryCoordinate j d (fun i => x i))) = 0 := hc
  have hx : insertBoundaryCoordinate j (x j) (fun i => x i) = x := by
    funext i
    by_cases hi : i = j <;> simp [insertBoundaryCoordinate, hi]
  simpa only [hx, Pi.zero_apply] using congrFun he (x j)

/-- Mode supports do not depend on the chosen finite equality algorithm. -/
private theorem portSupport_decidableEq_eq {n : ℕ}
    (d₁ d₂ : DecidableEq (Fin n)) (T : (Fin n → Fin 3) → ℂ) (j : Fin n) :
    (letI := d₁; columnSupport (portFlatten T j)) =
    (letI := d₂; columnSupport (portFlatten T j)) := by
  have h : d₁ = d₂ := Subsingleton.elim _ _
  subst d₂
  rfl

/-- Source primitive deficiency propagates to every gadget, without using any
matchgate-lifting assertion and without restrictions on zero/nullary tensors. -/
theorem AllLeftGadget.boundary_port_deficient {S : LabelledShape} {a b c n : ℕ}
    (I : AllLeftGadget S a b c n) (F : LabelledLanguage S (Fin 3))
    (hF : LeftPortDeficient F) (j : Fin n) :
    Module.finrank ℂ (columnSupport (portFlatten (I.value F) j)) ≤ 2 := by
  have hsupport : columnSupport (portFlatten (I.value F) j) ≤
      columnSupport (portFlatten (F.left (I.leftLabel (I.boundaryVertex j))) (I.boundaryPort j)) := by
    convert I.boundary_support_le F j using 1 <;>
      exact portSupport_decidableEq_eq _ _ _ _
  exact (Submodule.finrank_mono hsupport).trans
    (hF (I.leftLabel (I.boundaryVertex j)) (I.boundaryPort j))


/-- Every nonzero exposed port has dimension exactly one or two. -/
theorem AllLeftGadget.boundary_support_one_or_two {S : LabelledShape} {a b c n : ℕ}
    (I : AllLeftGadget S a b c n) (F : LabelledLanguage S (Fin 3))
    (hF : LeftPortDeficient F) (hne : I.value F ≠ 0) (j : Fin n) :
    Module.finrank ℂ (columnSupport (portFlatten (I.value F) j)) = 1 ∨
      Module.finrank ℂ (columnSupport (portFlatten (I.value F) j)) = 2 := by
  have hp := portSupport_finrank_pos (I.value F) hne j
  have hl := I.boundary_port_deficient F hF j
  omega

/-- No planes in the actual closure forces all nonzero boundary tensors to be
completely decomposable, including the arity-zero scalar case. -/
theorem allLeft_rayOnly_decomposable {S : LabelledShape} (F : LabelledLanguage S (Fin 3))
    (hF : LeftPortDeficient F) (hempty : allLeftRealizedSupports F 2 = ∅)
    {a b c n : ℕ} (I : AllLeftGadget S a b c n) (hconn : I.Connected)
    (hplan : Nonempty I.OrderedPlanar) (hne : I.value F ≠ 0) :
    ∃ (c : ℂ) (q : Fin n → Fin 3 → ℂ), c ≠ 0 ∧ (∀ j, q j ≠ 0) ∧
      ∀ x, I.value F x = c * ∏ j, q j (x j) := by
  apply rankOne_strip_all_ports (I.value F) hne
  intro j
  rcases I.boundary_support_one_or_two F hF hne j with h | h
  · exact h
  · have hm : columnSupport (portFlatten (I.value F) j) ∈ allLeftRealizedSupports F 2 :=
      ⟨a, b, c, n, I, hconn, hplan, hne, j, rfl, h⟩
    rw [hempty] at hm
    exact False.elim hm

/-- Explicit remaining planar-substitution dependency: exactness of the
literal Boolean lift of each actual ordered connected boundary tensor. -/
def AllLeftExactLifting {S : LabelledShape} {t : ℕ}
    (p : LabelledCommonPresentation S (Fin 3) t) : Prop :=
  ∀ a b c n (I : AllLeftGadget S a b c n), I.Connected → Nonempty I.OrderedPlanar →
    ExactMatchgate (leftBooleanLift p.baseMatrix n (I.value p.language))

/-- Explicit cyclic-rerooting extraction dependency. Only a rowspace witness
is requested here; its rank is derived from the literal transformed support. -/
def AllLeftPlaneExtraction {S : LabelledShape} {t : ℕ}
    (p : LabelledCommonPresentation S (Fin 3) t) : Prop :=
  ∀ a b c n (I : AllLeftGadget S a b c n), I.Connected → Nonempty I.OrderedPlanar →
    I.value p.language ≠ 0 → ∀ j : Fin n,
    Module.finrank ℂ (columnSupport (portFlatten (I.value p.language) j)) = 2 →
    ∃ m, ∃ A : Matrix (BooleanInput m) (BooleanInput t) ℂ,
      ExactMatchgateMatrix A ∧ orderedRowSpace A =
        (columnSupport (portFlatten (I.value p.language) j)).map p.baseMatrix.transpose.mulVecLin

/-- The literal qutrit row map followed by the fixed subset-coordinate map. -/
def qutritSubsetMap {t : ℕ} (M : Matrix (Fin 3) (BooleanInput t) ℂ) :
    (Fin 3 → ℂ) →ₗ[ℂ] SubsetSignature t ℂ :=
  spinorSubsetEquiv.toLinearMap.comp M.transpose.mulVecLin

theorem qutritSubsetMap_injective {t : ℕ} (M : Matrix (Fin 3) (BooleanInput t) ℂ)
    (hM : M.rank = 3) : Function.Injective (qutritSubsetMap M) := by
  exact spinorSubsetEquiv.injective.comp
    (transpose_injective_of_rank_eq_card M (by simpa using hM))

theorem qutritSubsetMap_map_le {t : ℕ} (M : Matrix (Fin 3) (BooleanInput t) ℂ)
    (U : Submodule ℂ (Fin 3 → ℂ)) : U.map (qutritSubsetMap M) ≤ baseSubsetSpace M := by
  rintro v ⟨u, hu, rfl⟩
  refine ⟨M.transpose.mulVecLin u, ?_, rfl⟩
  have hh : LinearMap.range M.transpose.mulVecLin = Submodule.span ℂ (Set.range M.row) := by
    exact Matrix.range_mulVecLin M.transpose
  rw [← hh]
  exact ⟨u, rfl⟩

/-- Faithful images of the actual realized domain-support sets. -/
def allLeftSubsetSupports {S : LabelledShape} {t : ℕ}
    (p : LabelledCommonPresentation S (Fin 3) t) (d : ℕ) :
    Set (Submodule ℂ (SubsetSignature t ℂ)) :=
  (fun U => U.map (qutritSubsetMap p.baseMatrix)) '' allLeftRealizedSupports p.language d

/-- Extract the genuine matchgate support geometry from the actual source
closure, given the two explicitly named ordered lifting dependencies. -/
def allLeftMatchgateGeometry {S : LabelledShape} {t : ℕ}
    (p : LabelledCommonPresentation S (Fin 3) t) (hM : p.baseMatrix.rank = 3)
    (hlift : AllLeftExactLifting p) (hextract : AllLeftPlaneExtraction p) :
    RealizedMatchgateGeometry t where
  ambient := baseSubsetSpace p.baseMatrix
  rays := allLeftSubsetSupports p 1
  planes := allLeftSubsetSupports p 2
  ray_le := by
    rintro R ⟨U, hU, rfl⟩
    exact qutritSubsetMap_map_le p.baseMatrix U
  plane_le := by
    rintro R ⟨U, hU, rfl⟩
    exact qutritSubsetMap_map_le p.baseMatrix U
  ray_realized := by
    rintro R ⟨U, ⟨a, b, c, n, I, hconn, hplan, hne, j, hU, hd⟩, rfl⟩
    obtain ⟨q, hq, hUq⟩ := exists_generator_of_finrank_one U hd
    have hM' := transpose_injective_of_rank_eq_card p.baseMatrix (by simpa using hM)
    have hqmg := transformed_ray_is_pure p.baseMatrix hM' (I.value p.language) hne
      (hlift a b c n I hconn hplan).matchgateIdentities j q (by rw [← hU, hUq])
    refine ⟨qutritSubsetMap p.baseMatrix q, ?_, ?_⟩
    · apply (isPureSpinor_iff_matchgateIdentities _).mpr
      constructor
      · intro hz
        exact hq (qutritSubsetMap_injective p.baseMatrix hM (hz.trans (map_zero _).symm))
      · change MatchgateIdentities (spinorSubsetEquiv (p.baseMatrix.transpose.mulVecLin q))
        rw [transpose_mulVecLin_eq_unaryTransform]
        exact hqmg
    · change U.map (qutritSubsetMap p.baseMatrix) = Submodule.span ℂ {qutritSubsetMap p.baseMatrix q}
      rw [hUq, Submodule.map_span, Set.image_singleton]
  plane_realized := by
    rintro R ⟨U, ⟨a, b, c, n, I, hconn, hplan, hne, j, hU, hd⟩, rfl⟩
    obtain ⟨m, A, hA, hrow⟩ := hextract a b c n I hconn hplan hne j (hU ▸ hd)
    refine ⟨m, A, hA, ?_, ?_⟩
    · rw [Matrix.rank_eq_finrank_span_row]
      change Module.finrank ℂ (orderedRowSpace A) = 2
      rw [hrow, finrank_map_transpose_eq p.baseMatrix
        (transpose_injective_of_rank_eq_card p.baseMatrix (by simpa using hM)), ← hU]
      exact hd
    · change U.map (qutritSubsetMap p.baseMatrix) = (orderedRowSpace A).map spinorSubsetEquiv.toLinearMap
      rw [hrow, ← Submodule.map_comp, ← hU]
      rfl

/-- Full domain support mapped through the displayed base is exactly its rowspace. -/
theorem qutritSubsetMap_top {t : ℕ} (M : Matrix (Fin 3) (BooleanInput t) ℂ) :
    (⊤ : Submodule ℂ (Fin 3 → ℂ)).map (qutritSubsetMap M) = baseSubsetSpace M := by
  rw [qutritSubsetMap, Submodule.map_comp, Submodule.map_top, Matrix.range_mulVecLin,
    Matrix.col_transpose]
  rfl

/-- Essentiality of the actual domain closure is transported without loss
through the displayed base and the fixed coefficient equivalence. -/
theorem allLeftSubsetSupports_span {S : LabelledShape} {t : ℕ}
    (p : LabelledCommonPresentation S (Fin 3) t)
    (hspan : sSup (allLeftRealizedSupports p.language 1 ∪ allLeftRealizedSupports p.language 2) = ⊤) :
    sSup (allLeftSubsetSupports p 1 ∪ allLeftSubsetSupports p 2) = baseSubsetSpace p.baseMatrix := by
  unfold allLeftSubsetSupports
  rw [← Set.image_union, sSup_image]
  have hmap := congrArg (Submodule.map (qutritSubsetMap p.baseMatrix)) hspan
  rw [sSup_eq_iSup] at hmap
  simp_rw [Submodule.map_iSup] at hmap
  exact hmap.trans (qutritSubsetMap_top p.baseMatrix)

/-- Primitive left support-essentiality, with zero and nullary labels retained. -/
def LeftSupportEssential {S : LabelledShape} (F : LabelledLanguage S (Fin 3)) : Prop :=
  sSup {U | ∃ l j, U = columnSupport (portFlatten (F.left l) j)} = ⊤

/-- Primitive induced right support-essentiality. -/
def RightSupportEssential {S : LabelledShape} (F : LabelledLanguage S (Fin 3)) : Prop :=
  sSup {U | ∃ l j, U = columnSupport (portFlatten (F.right l) j)} = ⊤

/-- Explicit primitive one-vertex realization dependency, including an actual
connected ordered disk embedding and exact boundary-tensor equality. -/
def PrimitiveAllLeftRealization {S : LabelledShape} (F : LabelledLanguage S (Fin 3)) : Prop :=
  ∀ l, ∃ a b c, ∃ I : AllLeftGadget S a b c (S.leftArity l),
    I.Connected ∧ Nonempty I.OrderedPlanar ∧ I.value F = F.left l

/-- Once primitive one-vertex gadgets are realized, left essentiality forces
all actual realized rays and planes together to span the full qutrit domain. -/
theorem allLeftRealizedSupports_span {S : LabelledShape} (F : LabelledLanguage S (Fin 3))
    (hdef : LeftPortDeficient F) (hess : LeftSupportEssential F)
    (hprim : PrimitiveAllLeftRealization F) :
    sSup (allLeftRealizedSupports F 1 ∪ allLeftRealizedSupports F 2) = ⊤ := by
  apply top_unique
  rw [← hess]
  apply sSup_le
  rintro U ⟨l, j, rfl⟩
  by_cases hzero : F.left l = 0
  · simp only [hzero]
    have he : portFlatten (0 : (Fin (S.leftArity l) → Fin 3) → ℂ) j = 0 := rfl
    rw [he]
    simp [columnSupport]
  · obtain ⟨a, b, c, I, hconn, hplan, hvalue⟩ := hprim l
    have hne : I.value F ≠ 0 := hvalue ▸ hzero
    have hr := I.boundary_support_one_or_two F hdef hne j
    rw [hvalue] at hr
    rcases hr with h | h
    · apply le_sSup
      exact Or.inl ⟨a, b, c, S.leftArity l, I, hconn, hplan, hne, j,
        congrArg (fun T => columnSupport (portFlatten T j)) hvalue.symm, h⟩
    · apply le_sSup
      exact Or.inr ⟨a, b, c, S.leftArity l, I, hconn, hplan, hne, j,
        congrArg (fun T => columnSupport (portFlatten T j)) hvalue.symm, h⟩

end
end MatchgateWidth
