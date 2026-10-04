import MatchgateWidth.GaussianOrderedMatrix

/-! # Exact algebraic normalization of a nonzero pure row
No Pin/Clifford normalization theorem is assumed: a Gaussian completion is
constructed and its inverse is proved to satisfy the ordered identities.
Graphical realization remains a separate interface.
-/
namespace MatchgateWidth
noncomputable section
variable {R : Type*} [CommRing R] {r t : ℕ}

/-- Scalar multiplication preserves the homogeneous identities. -/
theorem OrderedMatchgateMatrix.smul {P : Matrix (BooleanInput r) (BooleanInput t) R}
    (hP : OrderedMatchgateMatrix P) (c : R) : OrderedMatchgateMatrix (c • P) := by
  rw [orderedMatchgateMatrix_iff] at hP ⊢
  exact hP.const_mul c

/-- Output XOR is a common boundary pivot, with the reversal handled explicitly. -/
theorem OrderedMatchgateMatrix.outputXor
    {P : Matrix (BooleanInput r) (BooleanInput t) R}
    (hP : OrderedMatchgateMatrix P) (p : BooleanInput t) :
    OrderedMatchgateMatrix (fun x y => P x (pfaffianXor p y)) := by
  have h := hP.pivot (Fin.append (fun _ : Fin r => (0 : Fin 2)) (fun j => p j.rev))
  have heq : (fun z => orderedMatrixSignature P
      (pfaffianXor (Fin.append (fun _ : Fin r => (0 : Fin 2)) (fun j => p j.rev)) z)) =
      orderedMatrixSignature (fun x y => P x (pfaffianXor p y)) := by
    funext z
    unfold orderedMatrixSignature
    congr 1
    · funext i
      simp only [pfaffianXor, Fin.append_left]
      generalize z (Fin.castAdd t i) = b
      fin_cases b <;> rfl
    · funext j
      simp [pfaffianXor, Fin.append]
  change BooleanMatchgateIdentities _
  rw [heq] at h
  exact h

/-- XOR permutes Boolean words bijectively. -/
def booleanXorEquiv (p : BooleanInput t) : BooleanInput t ≃ BooleanInput t where
  toFun := pfaffianXor p
  invFun := pfaffianXor p
  left_inv := pfaffianXor_involutive p
  right_inv := pfaffianXor_involutive p

section Field
variable {K : Type*} [Field K] [CharZero K]

/-- Any nonzero Boolean MGI row is literally the vacuum row of an invertible
ordered MGI matrix. This includes arbitrary parity and nonempty XOR pivots. -/
theorem exists_orderedMatchgate_completion
    (u : BooleanTable t K) (hu : BooleanMatchgateIdentities u) (hne : u ≠ 0) :
    ∃ C E : Matrix (BooleanInput t) (BooleanInput t) K,
      OrderedMatchgateMatrix C ∧ OrderedMatchgateMatrix E ∧ C * E = 1 ∧ E * C = 1 ∧
      ∀ z, C (fun _ => 0) z = u z := by
  obtain ⟨p, a, ha⟩ := hu.exists_pfaffianPivotChart
  have hc : a none ≠ 0 := by
    intro h
    apply hne
    rw [ha]
    exact pfaffianPivotChart_zero_scale p (fun _ => 0) a h
  let D := pfaffianChartMatrix a
  have hD : ∀ i j, D i j = -D j i := fun i j => pfaffianChartMatrix_skew a j i
  have hD0 : ∀ i, D i i = 0 := pfaffianChartMatrix_diag a
  let G := gaussianOrderedMatrix 0 (1 : Matrix (Fin t) (Fin t) K) (-D)
  have hn : ∀ i j, (-D) i j = -(-D) j i := by
    intro i j
    simpa using congrArg Neg.neg (hD i j)
  have hG : OrderedMatchgateMatrix G :=
    gaussianOrderedMatrix_isMatchgate _ _ _ (by simp) hn (by simp) (by simpa using hD0)
  let C := (a none) • G.submatrix (Equiv.refl _) (booleanXorEquiv p)
  have hC : OrderedMatchgateMatrix C := (hG.outputXor p).smul (a none)
  have hr : C.rank = Fintype.card (BooleanInput t) := by
    rw [Matrix.rank_smul_of_mem_nonZeroDivisors _ (mem_nonZeroDivisors_of_ne_zero hc),
      Matrix.rank_submatrix]
    exact gaussianOrderedMatrix_identity_cross_rank (-D) hn
  obtain ⟨E, hCE⟩ := exists_baseDecoder C (transpose_injective_of_rank_eq_card C hr)
  have hEC : E * C = 1 := mul_eq_one_comm.mp hCE
  refine ⟨C, E, hC, hC.leftInverse hEC, hCE, hEC, ?_⟩
  intro z
  change a none * G (fun _ => 0) (pfaffianXor p z) = u z
  dsimp only [G]
  rw [gaussianOrderedMatrix_vacuum_row D hD, ha]
  simp [pfaffianPivotChart, pfaffianChart, principalPfaffian,
    pfaffianSelectedPorts, booleanSubsetEquiv, D]

/-- A nonzero pure row can be sent exactly to the vacuum by an invertible
ordered matchgate transformation. The inverse is also explicitly supplied. -/
theorem exists_orderedMatchgate_vacuum_normalization
    (u : BooleanTable t K) (hu : BooleanMatchgateIdentities u) (hne : u ≠ 0) :
    ∃ C E : Matrix (BooleanInput t) (BooleanInput t) K,
      OrderedMatchgateMatrix C ∧ OrderedMatchgateMatrix E ∧ C * E = 1 ∧ E * C = 1 ∧
      Matrix.vecMul u C = fun z => if (fun _ => 0) = z then 1 else 0 := by
  obtain ⟨E, C, hE, hC, hEC, hCE, hrow⟩ := exists_orderedMatchgate_completion u hu hne
  refine ⟨C, E, hC, hE, hCE, hEC, ?_⟩
  funext z
  have h := congrArg (fun M : Matrix (BooleanInput t) (BooleanInput t) K => M (fun _ => 0) z) hEC
  simpa only [Matrix.mul_apply, hrow, Matrix.one_apply, Matrix.vecMul, dotProduct] using h

end Field
end
end MatchgateWidth
