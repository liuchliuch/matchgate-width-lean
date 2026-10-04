import MatchgateWidth.UniformBooleanPlaneEmbedding

/-! # A square canonical output map for a rank-two ordered matchgate plane

The output transformation is square and has an exact ordered matchgate inverse.
The active output is the first physical mode, not an arity-dependent pinning map.
-/
namespace MatchgateWidth
noncomputable section
variable {K : Type*} [Field K] [CharZero K]

/-- Complete one nonzero row to a nonsingular square matrix, with that row at
any prescribed input position. -/
theorem exists_invertible_matrix_with_row {t : ℕ} (b : Fin t → K) (hb : b ≠ 0)
    (i₀ : Fin t) :
    ∃ B : Matrix (Fin t) (Fin t) K, B.rank = t ∧ B.row i₀ = b := by
  classical
  obtain ⟨j, hj⟩ : ∃ j, b j ≠ 0 := by
    by_contra h
    push Not at h
    exact hb (funext h)
  let A : Matrix (Fin t) (Fin t) K := fun i k => if i = j then b k else if i = k then 1 else 0
  have hA : Function.Injective A.transpose.mulVecLin := by
    apply (injective_iff_map_eq_zero _).mpr
    intro x hx
    have heq (k : Fin t) : (A.transpose.mulVecLin x) k =
        x j * b k + if k = j then 0 else x k := by
      change (∑ i, A i k * x i) = _
      calc
        _ = ∑ i, ((if i = j then b k * x j else 0) +
            (if i = k then (if k = j then 0 else x k) else 0)) := by
          apply Finset.sum_congr rfl
          intro i _
          by_cases hij : i = j <;> by_cases hik : i = k <;>
            simp_all [A]
        _ = _ := by rw [Finset.sum_add_distrib]; simp; ring
    have hxj : x j = 0 := by
      have h := congrFun hx j
      rw [heq] at h
      simpa [hj] using h
    funext k
    have h := congrFun hx k
    rw [heq, hxj, zero_mul, zero_add] at h
    by_cases hk : k = j
    · simpa [hk] using hxj
    · simpa [hk] using h
  let B := A.submatrix (Equiv.swap i₀ j) (Equiv.refl _)
  refine ⟨B, ?_, ?_⟩
  · dsimp only [B]
    rw [Matrix.rank_submatrix]
    simpa using rank_eq_card_of_transpose_injective A hA
  · ext k
    change A (Equiv.swap i₀ j i₀) k = b k
    simp [A]

/-- Normalize a nonzero one-particle vector while fixing the vacuum, by an
invertible ordered matchgate output transformation. -/
theorem exists_singleton_output_normalization {t : ℕ} (b : Fin t → K) (hb : b ≠ 0)
    (i₀ : Fin t) :
    ∃ C E : Matrix (BooleanInput t) (BooleanInput t) K,
      OrderedMatchgateMatrix C ∧ OrderedMatchgateMatrix E ∧ C*E=1 ∧ E*C=1 ∧
      Matrix.vecMul outputVacuum C = outputVacuum ∧
      Matrix.vecMul (singletonLift b) C = Pi.single (singletonWord i₀) 1 := by
  classical
  obtain ⟨B, hB, hrow⟩ := exists_invertible_matrix_with_row b hb i₀
  let E := gaussianOrderedMatrix 0 B 0
  have hE : OrderedMatchgateMatrix E :=
    gaussianOrderedMatrix_isMatchgate _ _ _ (by simp) (by simp) (by simp) (by simp)
  have hrE : E.rank = Fintype.card (BooleanInput t) := by
    dsimp only [E]
    rw [gaussianOrderedMatrix_rank _ _ _ (by simp) (by simp), hB]
    simp [BooleanInput]
  obtain ⟨C, hEC⟩ := exists_baseDecoder E (transpose_injective_of_rank_eq_card E hrE)
  have hCE : C*E=1 := mul_eq_one_comm.mp hEC
  refine ⟨C,E,hE.leftInverse hCE,hE,hCE,hEC,?_,?_⟩
  · have hv := gaussianOrderedMatrix_vacuum (0 : Matrix (Fin t) (Fin t) K) B
    funext z
    have hh := congrArg (fun A : Matrix (BooleanInput t) (BooleanInput t) K => A (fun _ => 0) z) hEC
    have hrowE : ∀ y, E (fun _ => 0) y = outputVacuum y := congrFun hv
    simpa only [Matrix.mul_apply, hrowE, Matrix.one_apply, Matrix.vecMul, dotProduct,
      outputVacuum] using hh
  · have hs := gaussianOrderedMatrix_singleton_row (0 : Matrix (Fin t) (Fin t) K) B i₀
    funext z
    have hh := congrArg (fun A : Matrix (BooleanInput t) (BooleanInput t) K => A (singletonWord i₀) z) hEC
    have hrowE : ∀ y, E (singletonWord i₀) y = singletonLift b y := by
      intro y
      simpa only [E, Matrix.row_apply, show B i₀ = b from hrow] using congrFun hs y
    simpa only [Matrix.mul_apply, hrowE, Matrix.one_apply, Matrix.vecMul, dotProduct,
      Pi.single_apply, eq_comm] using hh


/-- A full-row-rank one-input matchgate matrix has a square exact canonical
output transformation taking its two literal rows to the vacuum and first
one-particle coordinate. Its inverse is supplied explicitly. -/
theorem OrderedMatchgateMatrix.one_input_canonical_output {t : ℕ}
    {Q : Matrix (BooleanInput 1) (BooleanInput t) K}
    (hQ : OrderedMatchgateMatrix Q) (hr : Q.rank = 2) :
    ∃ (ht : 0 < t) (C E : Matrix (BooleanInput t) (BooleanInput t) K),
      OrderedMatchgateMatrix C ∧ OrderedMatchgateMatrix E ∧ C*E=1 ∧ E*C=1 ∧
      Matrix.vecMul (Q.row (fun _ => 0)) C = outputVacuum ∧
      Matrix.vecMul (Q.row (fun _ => 1)) C = Pi.single (singletonWord ⟨0,ht⟩) 1 := by
  classical
  obtain ⟨_, _, h₀, _, _, _⟩ := hQ.one_input_endpoint_parity hr
  obtain ⟨C₀,E₀,hC₀,hE₀,hCE₀,hEC₀,hvac⟩ :=
    exists_orderedMatchgate_vacuum_normalization (Q.row (fun _ => 0)) (hQ.row _) h₀
  let Q' := Q*C₀
  have hQ' : OrderedMatchgateMatrix Q' := hQ.mul hC₀
  have hr' : Q'.rank = 2 := (rank_mul_of_right_inverse Q C₀ E₀ hCE₀).trans hr
  have hrow0 : Q'.row (fun _ => 0) = outputVacuum := hvac
  have hv : outputVacuum ∈ orderedRowSpace Q' := hrow0 ▸ row_mem_orderedRowSpace Q' _
  obtain ⟨b,hb,hspace⟩ := hQ'.rank_two_vacuum_normal_form hr' hv
  obtain ⟨k,hk,_,h₁,hp₀,hp₁⟩ := hQ'.one_input_endpoint_parity hr'
  have hk0 : k=0 := by
    by_contra hn
    have hz := hp₀ (fun _ => 0) (by simpa [booleanParity] using Ne.symm hn)
    have he := congrFun hrow0 (fun _ => 0)
    simp [outputVacuum] at he
    change Q' (fun _ => 0) (fun _ => 0) = 1 at he
    exact one_ne_zero (he.symm.trans hz)
  have h1zero : Q' (fun _ => 1) (fun _ => 0) = 0 := hp₁ _ (by simp [booleanParity, hk0])
  obtain ⟨a,c,hac⟩ := Submodule.mem_span_pair.mp
    (hspace ▸ row_mem_orderedRowSpace Q' (fun _ => 1))
  have ha : a=0 := by
    have hh := congrFun hac (fun _ => 0)
    simpa [outputVacuum, h1zero] using hh
  have hrow1 : Q'.row (fun _ => 1) = singletonLift (c • b) := by
    rw [ha, zero_smul, zero_add] at hac
    simpa only [map_smul] using hac.symm
  have hb' : c • b ≠ 0 := by
    intro hz
    apply h₁
    rw [hrow1, hz, map_zero]
  obtain ⟨j,hj⟩ : ∃ j, (c • b) j ≠ 0 := by
    by_contra h
    push Not at h
    exact hb' (funext h)
  have ht : 0<t := Nat.zero_lt_of_lt j.isLt
  obtain ⟨C₁,E₁,hC₁,hE₁,hCE₁,hEC₁,hvac₁,hfirst⟩ :=
    exists_singleton_output_normalization (c • b) hb' ⟨0,ht⟩
  refine ⟨ht,C₀*C₁,E₁*E₀,hC₀.mul hC₁,hE₁.mul hE₀,?_,?_,?_,?_⟩
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc C₁, hCE₁, Matrix.one_mul, hCE₀]
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc E₀, hEC₀, Matrix.one_mul, hEC₁]
  · rw [← Matrix.vecMul_vecMul, hvac]
    exact hvac₁
  · rw [← Matrix.vecMul_vecMul]
    change Matrix.vecMul (Q'.row (fun _ => 1)) C₁ = _
    rw [hrow1]
    exact hfirst

end
end MatchgateWidth
