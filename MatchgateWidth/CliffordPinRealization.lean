import MatchgateWidth.SpinorOperatorMatrix
import MatchgateWidth.CliffordMatchgateMatrix
import MatchgateWidth.PivotCircuitRealization
import Mathlib.LinearAlgebra.CliffordAlgebra.SpinGroup

/-!
# Genuine Clifford-algebra and Pin-unit realization

The actual signed coefficient action is lifted through mathlib's universal
Clifford algebra for the split quadratic form. Every Lipschitz unit, hence every
Pin unit, acts by an exact ordered MGI matrix. Its ordinary transpose is the
source's row-coordinate transformation; the inverse and the exact disk graph
realizations are supplied without assuming a matchgate realization of the lift.
-/
namespace MatchgateWidth
noncomputable section
variable {K : Type*} [Field K] [CharZero K] {t : ℕ}

/-- The quadratic form whose polarization is the source's split pairing. -/
def splitCliffordQuadratic : QuadraticForm K (CliffordVector t K) :=
  ∑ i : Fin t, QuadraticMap.linMulLin
    ((LinearMap.proj i).comp (LinearMap.fst K (Fin t → K) (Fin t → K)))
    ((LinearMap.proj i).comp (LinearMap.snd K (Fin t → K) (Fin t → K)))

@[simp] theorem splitCliffordQuadratic_apply (z : CliffordVector t K) :
    splitCliffordQuadratic z = ∑ i : Fin t, z.1 i * z.2 i := by
  simp [splitCliffordQuadratic, QuadraticMap.linMulLin_apply]

theorem cliffordPairing_self (z : CliffordVector t K) :
    cliffordPairing z z = 2 * splitCliffordQuadratic z := by
  rw [splitCliffordQuadratic_apply, Finset.mul_sum]
  unfold cliffordPairing
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Polarization of the actual quadratic form is exactly the source's
symmetric pairing, with no unrecorded factor of two. -/
theorem splitCliffordQuadratic_polar (z w : CliffordVector t K) :
    QuadraticMap.polar splitCliffordQuadratic z w = cliffordPairing z w := by
  simp only [QuadraticMap.polar, splitCliffordQuadratic_apply, Prod.fst_add,
    Prod.snd_add, Pi.add_apply, ← Finset.sum_sub_distrib, cliffordPairing]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The signed operators satisfy the actual universal Clifford square relation. -/
theorem signedCliffordRepresentation_square (z : CliffordVector t K) :
    signedCliffordRepresentation z * signedCliffordRepresentation z =
      algebraMap K (Module.End K (SubsetSignature t K)) (splitCliffordQuadratic z) := by
  have h := signedCliffordAction_car z z
  rw [cliffordPairing_self] at h
  apply LinearMap.ext
  intro u
  ext S
  have hc := congrArg (fun f : Module.End K (SubsetSignature t K) => f u S) h
  simp only [LinearMap.add_apply, Pi.add_apply, LinearMap.smul_apply, Pi.smul_apply,
    smul_eq_mul, Module.End.one_apply] at hc
  change (signedCliffordAction z * signedCliffordAction z) u S = _
  rw [Module.algebraMap_end_apply]
  change (signedCliffordAction z * signedCliffordAction z) u S = splitCliffordQuadratic z * u S
  linear_combination (1 / 2 : K) * hc

/-- The genuine spinor representation of the universal split Clifford algebra. -/
def cliffordSpinorRepresentation :
    CliffordAlgebra (splitCliffordQuadratic (K := K) (t := t)) →ₐ[K]
      Module.End K (SubsetSignature t K) :=
  CliffordAlgebra.lift (splitCliffordQuadratic (K := K) (t := t))
    (A := Module.End K (SubsetSignature t K))
    ⟨signedCliffordRepresentation (R := K) (t := t), fun z => signedCliffordRepresentation_square z⟩

@[simp] theorem cliffordSpinorRepresentation_ι (z : CliffordVector t K) :
    cliffordSpinorRepresentation (CliffordAlgebra.ι splitCliffordQuadratic z) = signedCliffordAction z := by
  unfold cliffordSpinorRepresentation
  rw [CliffordAlgebra.lift_ι_apply]
  rfl

/-- The literal Boolean coefficient matrix of the universal algebra action. -/
def cliffordAlgebraMatrix (a : CliffordAlgebra (splitCliffordQuadratic (K := K) (t := t))) :
    Matrix (BooleanInput t) (BooleanInput t) K :=
  spinorOperatorMatrix (cliffordSpinorRepresentation a)

@[simp] theorem cliffordAlgebraMatrix_one :
    cliffordAlgebraMatrix (1 : CliffordAlgebra (splitCliffordQuadratic (K := K) (t := t))) = 1 := by
  simp [cliffordAlgebraMatrix]

@[simp] theorem cliffordAlgebraMatrix_mul
    (a b : CliffordAlgebra (splitCliffordQuadratic (K := K) (t := t))) :
    cliffordAlgebraMatrix (a*b) = cliffordAlgebraMatrix a * cliffordAlgebraMatrix b := by
  simp [cliffordAlgebraMatrix]

@[simp] theorem cliffordAlgebraMatrix_ι (z : CliffordVector t K) :
    cliffordAlgebraMatrix (CliffordAlgebra.ι splitCliffordQuadratic z) = signedCliffordMatrix z := by
  simp only [cliffordAlgebraMatrix, cliffordSpinorRepresentation_ι]
  rfl

/-- The actual matrix action of a Clifford unit has its algebraic inverse exactly. -/
theorem cliffordAlgebraMatrix_unit_inverse
    (x : (CliffordAlgebra (splitCliffordQuadratic (K := K) (t := t)))ˣ) :
    cliffordAlgebraMatrix (↑x : CliffordAlgebra (splitCliffordQuadratic (K := K) (t := t))) * cliffordAlgebraMatrix (↑(x⁻¹) : CliffordAlgebra (splitCliffordQuadratic (K := K) (t := t))) = 1 ∧
    cliffordAlgebraMatrix (↑(x⁻¹) : CliffordAlgebra (splitCliffordQuadratic (K := K) (t := t))) * cliffordAlgebraMatrix (↑x : CliffordAlgebra (splitCliffordQuadratic (K := K) (t := t))) = 1 := by
  constructor <;> rw [← cliffordAlgebraMatrix_mul] <;> simp

/-- Every actual Lipschitz unit acts by a literal ordered MGI matrix. This
uses its genuine group-generation definition, not a proposed realization field. -/
theorem cliffordAlgebraMatrix_isMatchgate_of_lipschitz
    {x : (CliffordAlgebra (splitCliffordQuadratic (K := K) (t := t)))ˣ}
    (hx : x ∈ lipschitzGroup splitCliffordQuadratic) :
    OrderedMatchgateMatrix (cliffordAlgebraMatrix (↑x : CliffordAlgebra (splitCliffordQuadratic (K := K) (t := t)))) := by
  unfold lipschitzGroup at hx
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨z, hz⟩ := hx
    rw [← hz, cliffordAlgebraMatrix_ι]
    exact signedCliffordMatrix_isMatchgate z
  | one => simpa using OrderedMatchgateMatrix.one (R := K) t
  | mul x y hx hy ihx ihy =>
    simpa only [Units.val_mul, cliffordAlgebraMatrix_mul] using ihx.mul ihy
  | inv x hx ih =>
    exact ih.leftInverse (cliffordAlgebraMatrix_unit_inverse x).2

/-- In particular every genuine mathlib Pin unit acts by an exact ordered MGI matrix. -/
theorem cliffordAlgebraMatrix_isMatchgate_of_pin
    {x : (CliffordAlgebra (splitCliffordQuadratic (K := K) (t := t)))ˣ}
    (hx : (↑x : CliffordAlgebra (splitCliffordQuadratic (K := K) (t := t))) ∈ pinGroup splitCliffordQuadratic) :
    OrderedMatchgateMatrix (cliffordAlgebraMatrix (↑x : CliffordAlgebra (splitCliffordQuadratic (K := K) (t := t)))) :=
  cliffordAlgebraMatrix_isMatchgate_of_lipschitz (pinGroup.units_mem_lipschitzGroup hx)

/-- Ordinary transpose is exactly the source's row-coordinate action matrix. -/
def cliffordRowMatrix (a : CliffordAlgebra (splitCliffordQuadratic (K := K) (t := t))) :
    Matrix (BooleanInput t) (BooleanInput t) K := (cliffordAlgebraMatrix a).transpose

/-- Row coefficients transformed by the ordinary transpose are precisely the
column-spinor action, with only the explicit Boolean/subset coordinate change. -/
theorem cliffordRowMatrix_vecMul
    (a : CliffordAlgebra (splitCliffordQuadratic (K := K) (t := t))) (u : BooleanTable t K) :
    Matrix.vecMul u (cliffordRowMatrix a) =
      spinorSubsetEquiv.symm (cliffordSpinorRepresentation a (spinorSubsetEquiv u)) := by
  rw [cliffordRowMatrix, Matrix.vecMul_transpose]
  exact spinorOperatorMatrix_mulVec _ u

/-- Exact ordered MGI realization of a lift and its inverse in row coordinates. -/
theorem cliffordRowMatrix_lipschitz_inverse
    {x : (CliffordAlgebra (splitCliffordQuadratic (K := K) (t := t)))ˣ}
    (hx : x ∈ lipschitzGroup splitCliffordQuadratic) :
    OrderedMatchgateMatrix (cliffordRowMatrix (↑x : CliffordAlgebra (splitCliffordQuadratic (K := K) (t := t)))) ∧
    OrderedMatchgateMatrix (cliffordRowMatrix (↑(x⁻¹) : CliffordAlgebra (splitCliffordQuadratic (K := K) (t := t)))) ∧
    cliffordRowMatrix (↑x : CliffordAlgebra (splitCliffordQuadratic (K := K) (t := t))) * cliffordRowMatrix (↑(x⁻¹) : CliffordAlgebra (splitCliffordQuadratic (K := K) (t := t))) = 1 ∧
    cliffordRowMatrix (↑(x⁻¹) : CliffordAlgebra (splitCliffordQuadratic (K := K) (t := t))) * cliffordRowMatrix (↑x : CliffordAlgebra (splitCliffordQuadratic (K := K) (t := t))) = 1 := by
  refine ⟨(cliffordAlgebraMatrix_isMatchgate_of_lipschitz hx).transpose,
    (cliffordAlgebraMatrix_isMatchgate_of_lipschitz ((lipschitzGroup _).inv_mem hx)).transpose, ?_, ?_⟩
  · rw [cliffordRowMatrix, cliffordRowMatrix, ← Matrix.transpose_mul,
      (cliffordAlgebraMatrix_unit_inverse x).2, Matrix.transpose_one]
  · rw [cliffordRowMatrix, cliffordRowMatrix, ← Matrix.transpose_mul,
      (cliffordAlgebraMatrix_unit_inverse x).1, Matrix.transpose_one]

/-- Mathlib's genuine Pin elements, without a separately supplied units wrapper,
also have exact ordered MGI action matrices. -/
theorem cliffordAlgebraMatrix_isMatchgate_pinElement
    (x : pinGroup (splitCliffordQuadratic (K := K) (t := t))) :
    OrderedMatchgateMatrix (cliffordAlgebraMatrix (x : CliffordAlgebra (splitCliffordQuadratic (K := K) (t := t)))) := by
  obtain ⟨a, ha, hax⟩ := pinGroup.mem_lipschitzGroup x.property
  have h := cliffordAlgebraMatrix_isMatchgate_of_lipschitz ha
  change (↑a : CliffordAlgebra (splitCliffordQuadratic (K := K) (t := t))) =
    (↑x : CliffordAlgebra (splitCliffordQuadratic (K := K) (t := t))) at hax
  rw [hax] at h
  exact h

/-- Applying the universal representation to an actual Clifford intertwiner
produces the source's signed operator intertwining identity coefficientwise. -/
theorem cliffordSpinorRepresentation_intertwining
    (a : CliffordAlgebra (splitCliffordQuadratic (K := K) (t := t)))
    (z w : CliffordVector t K)
    (h : a * CliffordAlgebra.ι splitCliffordQuadratic z =
      CliffordAlgebra.ι splitCliffordQuadratic w * a) (u : SubsetSignature t K) :
    cliffordSpinorRepresentation a (signedCliffordAction z u) =
      signedCliffordAction w (cliffordSpinorRepresentation a u) := by
  have h' := congrArg cliffordSpinorRepresentation h
  simp only [map_mul, cliffordSpinorRepresentation_ι] at h'
  exact congrArg (fun f : Module.End K (SubsetSignature t K) => f u) h'

/-- A genuine Clifford unit acts invertibly on the full coefficient-spinor space. -/
theorem cliffordSpinorRepresentation_unit_leftInverse
    (x : (CliffordAlgebra (splitCliffordQuadratic (K := K) (t := t)))ˣ) :
    Function.LeftInverse
      (cliffordSpinorRepresentation (↑(x⁻¹) : CliffordAlgebra (splitCliffordQuadratic (K := K) (t := t))))
      (cliffordSpinorRepresentation (↑x : CliffordAlgebra (splitCliffordQuadratic (K := K) (t := t)))) := by
  intro u
  have h : cliffordSpinorRepresentation
      ((↑(x⁻¹) : CliffordAlgebra (splitCliffordQuadratic (K := K) (t := t))) * (↑x : CliffordAlgebra (splitCliffordQuadratic (K := K) (t := t)))) = 1 := by simp
  rw [map_mul] at h
  exact congrArg (fun f : Module.End K (SubsetSignature t K) => f u) h

/-- Exact annihilator transport for an actual algebraic Clifford lift of a
linear equivalence. This is derived from the intertwining equality and the
unit inverse, rather than assumed as a spinor axiom. -/
theorem cliffordUnit_annihilator_transport
    (x : (CliffordAlgebra (splitCliffordQuadratic (K := K) (t := t)))ˣ)
    (g : CliffordVector t K ≃ₗ[K] CliffordVector t K)
    (hg : ∀ z, (↑x : CliffordAlgebra (splitCliffordQuadratic (K := K) (t := t))) *
      CliffordAlgebra.ι splitCliffordQuadratic z =
      CliffordAlgebra.ι splitCliffordQuadratic (g z) * (↑x : CliffordAlgebra (splitCliffordQuadratic (K := K) (t := t))))
    (u : SubsetSignature t K) :
    (spinorAnnihilator u).map g.toLinearMap =
      spinorAnnihilator (cliffordSpinorRepresentation (↑x : CliffordAlgebra (splitCliffordQuadratic (K := K) (t := t))) u) := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    change signedCliffordAction (g w) (cliffordSpinorRepresentation (↑x : CliffordAlgebra (splitCliffordQuadratic (K := K) (t := t))) u) = 0
    rw [← cliffordSpinorRepresentation_intertwining _ w (g w) (hg w) u]
    rw [show signedCliffordAction w u = 0 from hw, map_zero]
  · intro hz
    refine ⟨g.symm z, ?_, g.apply_symm_apply z⟩
    change signedCliffordAction (g.symm z) u = 0
    apply (cliffordSpinorRepresentation_unit_leftInverse x).injective
    rw [map_zero, cliffordSpinorRepresentation_intertwining _ _ _ (hg (g.symm z)) u,
      g.apply_symm_apply]
    exact hz

/-- The ordinary row transpose of a genuine Pin element and its group inverse
are exact ordered MGI inverses. -/
theorem cliffordRowMatrix_pinElement_inverse
    (x : pinGroup (splitCliffordQuadratic (K := K) (t := t))) :
    OrderedMatchgateMatrix (cliffordRowMatrix (x : CliffordAlgebra (splitCliffordQuadratic (K := K) (t := t)))) ∧
    OrderedMatchgateMatrix (cliffordRowMatrix (↑(x⁻¹) : CliffordAlgebra (splitCliffordQuadratic (K := K) (t := t)))) ∧
    cliffordRowMatrix (x : CliffordAlgebra (splitCliffordQuadratic (K := K) (t := t))) * cliffordRowMatrix (↑(x⁻¹) : CliffordAlgebra (splitCliffordQuadratic (K := K) (t := t))) = 1 ∧
    cliffordRowMatrix (↑(x⁻¹) : CliffordAlgebra (splitCliffordQuadratic (K := K) (t := t))) * cliffordRowMatrix (x : CliffordAlgebra (splitCliffordQuadratic (K := K) (t := t))) = 1 := by
  have hleft : (↑(x⁻¹) : CliffordAlgebra (splitCliffordQuadratic (K := K) (t := t))) * (↑x : CliffordAlgebra (splitCliffordQuadratic (K := K) (t := t))) = 1 := by
    exact congrArg (fun a : pinGroup (splitCliffordQuadratic (K := K) (t := t)) =>
      (a : CliffordAlgebra (splitCliffordQuadratic (K := K) (t := t)))) (inv_mul_cancel x)
  have hright : (↑x : CliffordAlgebra (splitCliffordQuadratic (K := K) (t := t))) * ↑(x⁻¹) = 1 := by
    exact congrArg (fun a : pinGroup (splitCliffordQuadratic (K := K) (t := t)) =>
      (a : CliffordAlgebra (splitCliffordQuadratic (K := K) (t := t)))) (mul_inv_cancel x)
  refine ⟨(cliffordAlgebraMatrix_isMatchgate_pinElement x).transpose,
    (cliffordAlgebraMatrix_isMatchgate_pinElement x⁻¹).transpose, ?_, ?_⟩
  · rw [cliffordRowMatrix, cliffordRowMatrix, ← Matrix.transpose_mul,
      ← cliffordAlgebraMatrix_mul, hleft, cliffordAlgebraMatrix_one, Matrix.transpose_one]
  · rw [cliffordRowMatrix, cliffordRowMatrix, ← Matrix.transpose_mul,
      ← cliffordAlgebraMatrix_mul, hright, cliffordAlgebraMatrix_one, Matrix.transpose_one]

/-- Source Lemma 4.3(b), in genuine mathlib Pin-group terms over the source
field: the standard coefficient action's ordinary transpose and inverse have
exact ordered disk-graph realizations, without scalar or port-order ambiguity. -/
theorem pinElement_ordered_disk_realization
    (x : pinGroup (splitCliffordQuadratic (K := ℂ) (t := t))) :
    OrderedMatchgateMatrix (cliffordRowMatrix (x : CliffordAlgebra (splitCliffordQuadratic (K := ℂ) (t := t)))) ∧
    OrderedMatchgateMatrix (cliffordRowMatrix (↑(x⁻¹) : CliffordAlgebra (splitCliffordQuadratic (K := ℂ) (t := t)))) ∧
    cliffordRowMatrix (x : CliffordAlgebra (splitCliffordQuadratic (K := ℂ) (t := t))) * cliffordRowMatrix (↑(x⁻¹) : CliffordAlgebra (splitCliffordQuadratic (K := ℂ) (t := t))) = 1 ∧
    cliffordRowMatrix (↑(x⁻¹) : CliffordAlgebra (splitCliffordQuadratic (K := ℂ) (t := t))) * cliffordRowMatrix (x : CliffordAlgebra (splitCliffordQuadratic (K := ℂ) (t := t))) = 1 ∧
    DiskRealizable (fun y => orderedMatrixSignature (cliffordRowMatrix (x : CliffordAlgebra (splitCliffordQuadratic (K := ℂ) (t := t))))
      ((booleanWordEquiv (t+t)).symm y)) ∧
    DiskRealizable (fun y => orderedMatrixSignature (cliffordRowMatrix (↑(x⁻¹) : CliffordAlgebra (splitCliffordQuadratic (K := ℂ) (t := t))))
      ((booleanWordEquiv (t+t)).symm y)) := by
  obtain ⟨hC, hD, hCD, hDC⟩ := cliffordRowMatrix_pinElement_inverse x
  exact ⟨hC, hD, hCD, hDC, BooleanMatchgateIdentities.diskRealizable hC,
    BooleanMatchgateIdentities.diskRealizable hD⟩

end
end MatchgateWidth
