import MatchgateWidth.CompleteSourceStructure

/-! # Binary contexts in every adapted ray basis

The generators of the even endpoint, odd endpoint, and transverse ray are
arbitrary nonzero vectors. Changing their scales changes the coordinate matrix
by independent nonzero row and column factors, preserving partial monomiality.
-/
namespace MatchgateWidth
noncomputable section
open scoped Classical
set_option maxHeartbeats 800000

/-- Partial monomiality depends only on the zero pattern. -/
theorem partialMonomial_iff_of_zero_iff
    (A B : Matrix (Fin 3) (Fin 3) ℂ)
    (h : ∀ i j, A i j = 0 ↔ B i j = 0) : PartialMonomial A ↔ PartialMonomial B := by
  have hn (i j) : A i j ≠ 0 ↔ B i j ≠ 0 := not_congr (h i j)
  simp only [PartialMonomial, hn]

/-- Independent nonzero coordinate scaling preserves every binary zero
pattern, and hence the partial-monomial predicate. -/
theorem partialMonomial_rescale_iff (A : Matrix (Fin 3) (Fin 3) ℂ)
    (d e : Fin 3 → ℂ) (hd : ∀ i, d i ≠ 0) (he : ∀ i, e i ≠ 0) :
    PartialMonomial (fun i j => d i * A i j * e j) ↔ PartialMonomial A := by
  apply partialMonomial_iff_of_zero_iff
  intro i j
  simp [hd i, he j]

/-- A diagonal tensor transform scales the coefficient at each port. -/
theorem leftTransform_diagonal_coefficients {q : ℕ} (d : Fin 3 → ℂ)
    (F : (Fin q → Fin 3) → ℂ) (x : Fin q → Fin 3) :
    leftTransform (Matrix.diagonal d) F x = F x * ∏ i, d (x i) := by
  classical
  unfold leftTransform
  rw [Finset.sum_eq_single x]
  · simp
  · intro y _ hy
    obtain ⟨j,hj⟩ := Function.ne_iff.mp hy
    have hz : (∏ i : Fin q, Matrix.diagonal d (y i) (x i)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ j) (by simp [Matrix.diagonal, hj])
    rw [hz, mul_zero]
  · simp

/-- Scaling inverse-basis columns gives the literal expected coefficient
scaling, without replacing the original boundary tensor. -/
theorem binaryContextCoordinates_mul_diagonal
    (N : Matrix (Fin 3) (Fin 3) ℂ) (d : Fin 3 → ℂ)
    (F : (Fin 2 → Fin 3) → ℂ) (i j : Fin 3) :
    binaryContextCoordinates (N * Matrix.diagonal d) F i j =
      d i * binaryContextCoordinates N F i j * d j := by
  unfold binaryContextCoordinates
  rw [← leftTransform_compose, leftTransform_diagonal_coefficients]
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-- The exact inverse-coordinate transformation preserves partial
monomiality under every nonzero diagonal change of ray generators. -/
theorem binaryContextCoordinates_rescale_iff
    (N : Matrix (Fin 3) (Fin 3) ℂ) (d : Fin 3 → ℂ) (hd : ∀ i, d i ≠ 0)
    (F : (Fin 2 → Fin 3) → ℂ) :
    PartialMonomial (binaryContextCoordinates (N * Matrix.diagonal d) F) ↔
      PartialMonomial (binaryContextCoordinates N F) := by
  have h : binaryContextCoordinates (N * Matrix.diagonal d) F =
      fun i j => d i * binaryContextCoordinates N F i j * d j := by
    ext i j
    exact binaryContextCoordinates_mul_diagonal N d F i j
  rw [h]
  exact partialMonomial_rescale_iff _ d d hd hd

/-- Any nonzero row chosen on each of three specified row rays differs by
an invertible diagonal matrix, with no compatibility assumption on scales. -/
theorem rows_on_rays_diagonal (T U : Matrix (Fin 3) (Fin 3) ℂ)
    (hne : ∀ i, U.row i ≠ 0)
    (hmem : ∀ i, U.row i ∈ Submodule.span ℂ {T.row i}) :
    ∃ d : Fin 3 → ℂ, (∀ i, d i ≠ 0) ∧ U = Matrix.diagonal d * T := by
  classical
  choose d hd using fun i => Submodule.mem_span_singleton.mp (hmem i)
  refine ⟨d, ?_, ?_⟩
  · intro i hz
    apply hne i
    rw [← hd i, hz, zero_smul]
  · ext i j
    simpa only [Matrix.diagonal_mul, Matrix.row, Pi.smul_apply, smul_eq_mul] using (congrFun (hd i) j).symm

/-- Inverse and full rank of an arbitrary diagonal rescaling of a basis. -/
theorem rescaled_basis_inverse (T N : Matrix (Fin 3) (Fin 3) ℂ)
    (hTN : T * N = 1) (hNT : N * T = 1)
    (d : Fin 3 → ℂ) (hd : ∀ i, d i ≠ 0) :
    (Matrix.diagonal d * T).rank = 3 ∧
      (Matrix.diagonal d * T) * (N * Matrix.diagonal (fun i => (d i)⁻¹)) = 1 ∧
      (N * Matrix.diagonal (fun i => (d i)⁻¹)) * (Matrix.diagonal d * T) = 1 := by
  have hdd : Matrix.diagonal d * Matrix.diagonal (fun i => (d i)⁻¹) =
      (1 : Matrix (Fin 3) (Fin 3) ℂ) := by
    rw [Matrix.diagonal_mul_diagonal]
    simp [hd]
  have hdd' : Matrix.diagonal (fun i => (d i)⁻¹) * Matrix.diagonal d =
      (1 : Matrix (Fin 3) (Fin 3) ℂ) := by
    rw [Matrix.diagonal_mul_diagonal]
    simp [hd]
  have hright : (Matrix.diagonal d * T) *
      (N * Matrix.diagonal (fun i => (d i)⁻¹)) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc T, hTN, Matrix.one_mul, hdd]
  have hleft : (N * Matrix.diagonal (fun i => (d i)⁻¹)) *
      (Matrix.diagonal d * T) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (Matrix.diagonal (fun i => (d i)⁻¹)),
      hdd', Matrix.one_mul, hNT]
  refine ⟨?_, hright, hleft⟩
  apply le_antisymm
  · simpa using Matrix.rank_le_card_width (Matrix.diagonal d * T)
  · have h := Matrix.rank_mul_le_left (Matrix.diagonal d * T)
      (N * Matrix.diagonal (fun i => (d i)⁻¹))
    simpa only [hright, Matrix.rank_one, Fintype.card_fin] using h

/-- Source Corollary 10.10 for any previously chosen adapted ray basis.
Only nonzero membership in the three literal rays is assumed; invertibility,
the inverse coordinates, alternatives, and compression are all derived. -/
theorem allLeft_binary_context_corollary_any_basis
    {S : LabelledShape} {t : ℕ} (p : LabelledCommonPresentation S (Fin 3) t)
    (hM : p.baseMatrix.rank = 3)
    (P L : Submodule ℂ (Fin 3 → ℂ))
    (hP : P ∈ allLeftRealizedSupports p.language 2)
    (hL : L ∈ allLeftRealizedSupports p.language 1) (hLP : ¬ L ≤ P)
    (U : Matrix (Fin 3) (Fin 3) ℂ) (hne : ∀ i, U.row i ≠ 0)
    (hu0 : U.row 0 ∈ primitiveParityEndpoint p.baseMatrix P 0)
    (hu1 : U.row 1 ∈ primitiveParityEndpoint p.baseMatrix P 1)
    (hu2 : U.row 2 ∈ L) :
    ∃ N : Matrix (Fin 3) (Fin 3) ℂ,
      U.rank = 3 ∧ U * N = 1 ∧ N * U = 1 ∧
      (BinarySmallCover p.baseMatrix ∨
        ∀ a b c (I : AllLeftGadget S a b c 2), I.Connected → Nonempty I.OrderedPlanar →
          PartialMonomial (binaryContextCoordinates N (I.value p.language))) ∧
      (∀ a b c (I : AllLeftGadget S a b c 2), I.Connected → Nonempty I.OrderedPlanar →
        ¬ PartialMonomial (binaryContextCoordinates N (I.value p.language)) →
        ∃ w ≤ 3, ∃ q : LabelledCommonPresentation S (Fin 3) w,
          q.left = p.left ∧ q.language = p.language ∧
          ExactlyLabelledEquivalent p.language q.language) := by
  obtain ⟨T,N,hT,hTN,hNT,hT2,hT0,hT1,halt,hwidth⟩ :=
    allLeft_binary_context_corollary p hM P L hP hL hLP
  have hmem : ∀ i, U.row i ∈ Submodule.span ℂ {T.row i} := by
    intro i
    fin_cases i
    · change U.row 0 ∈ Submodule.span ℂ {T.row 0}
      rwa [← hT0]
    · change U.row 1 ∈ Submodule.span ℂ {T.row 1}
      rwa [← hT1]
    · change U.row 2 ∈ Submodule.span ℂ {T.row 2}
      rwa [hT2]
  obtain ⟨d,hd,hU⟩ := rows_on_rays_diagonal T U hne hmem
  obtain ⟨hr,hUN,hNU⟩ := rescaled_basis_inverse T N hTN hNT d hd
  rw [← hU] at hr hUN hNU
  refine ⟨N * Matrix.diagonal (fun i => (d i)⁻¹), hr,hUN,hNU,?_,?_⟩
  · rcases halt with hc | hm
    · exact Or.inl hc
    · right
      intro a b c I hconn hplan
      exact (binaryContextCoordinates_rescale_iff N (fun i => (d i)⁻¹)
        (fun i => inv_ne_zero (hd i)) (I.value p.language)).mpr
          (hm a b c I hconn hplan)
  · intro a b c I hconn hplan hn
    apply hwidth a b c I hconn hplan
    intro hm
    exact hn ((binaryContextCoordinates_rescale_iff N (fun i => (d i)⁻¹)
      (fun i => inv_ne_zero (hd i)) (I.value p.language)).mpr hm)

/-- Literal arbitrary-generator form of source Corollary 10.10. The three
vectors are inputs, chosen before every binary context, and no normalization
or coordinated choice of their nonzero scales is required. -/
theorem allLeft_binary_context_corollary_any_generators
    {S : LabelledShape} {t : ℕ} (p : LabelledCommonPresentation S (Fin 3) t)
    (hM : p.baseMatrix.rank = 3)
    (P L : Submodule ℂ (Fin 3 → ℂ))
    (hP : P ∈ allLeftRealizedSupports p.language 2)
    (hL : L ∈ allLeftRealizedSupports p.language 1) (hLP : ¬ L ≤ P)
    (pPlus pMinus ell : Fin 3 → ℂ)
    (hplus : pPlus ≠ 0) (hminus : pMinus ≠ 0) (hell : ell ≠ 0)
    (hplus_mem : pPlus ∈ primitiveParityEndpoint p.baseMatrix P 0)
    (hminus_mem : pMinus ∈ primitiveParityEndpoint p.baseMatrix P 1)
    (hell_mem : ell ∈ L) :
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
          ExactlyLabelledEquivalent p.language q.language) := by
  apply allLeft_binary_context_corollary_any_basis p hM P L hP hL hLP
  · intro i
    fin_cases i
    · exact hplus
    · exact hminus
    · exact hell
  · exact hplus_mem
  · exact hminus_mem
  · exact hell_mem

end
end MatchgateWidth
