import MatchgateWidth.BinaryContextAlternative
import MatchgateWidth.RankTwoBlockReversal

/-! # Actual two-port boundary tensors and the ordered-matrix convention -/
namespace MatchgateWidth
noncomputable section
set_option maxHeartbeats 800000

def binaryDomainTensor (A : Matrix (Fin 3) (Fin 3) ℂ) : (Fin 2 → Fin 3) → ℂ :=
  fun x => A (x 0) (x 1)

def binaryPhysicalLift {t : ℕ} (M : Matrix (Fin 3) (BooleanInput t) ℂ)
    (A : Matrix (Fin 3) (Fin 3) ℂ) : BooleanTable (t+t) ℂ :=
  fun z => binaryMatrixLift M A (fun i => z (Fin.castAdd t i)) (fun i => z (Fin.natAdd t i))

def reverseBooleanEquiv (t : ℕ) : BooleanInput t ≃ BooleanInput t where
  toFun := fun x i => x i.rev
  invFun := fun x i => x i.rev
  left_inv := by intro x; ext i; simp
  right_inv := by intro x; ext i; simp

 theorem binaryMatrixLift_exact_of_physical {t : ℕ}
    (M : Matrix (Fin 3) (BooleanInput t) ℂ) (hM : M.rank=3)
    (A : Matrix (Fin 3) (Fin 3) ℂ) (hA : ExactMatchgate (binaryPhysicalLift M A)) :
    ExactMatchgateMatrix (binaryMatrixLift M A) := by
  let R : Matrix (BooleanInput t) (BooleanInput t) ℂ :=
    fun x y => binaryMatrixLift M A x (fun i => y i.rev)
  have hR : ExactMatchgateMatrix R := by
    have he : orderedMatrixSignature R = binaryPhysicalLift M A := by
      ext z
      simp only [orderedMatrixSignature,R,binaryPhysicalLift,Fin.rev_rev]
    change ExactMatchgate (orderedMatrixSignature R)
    rw [he]
    exact hA
  have hr : R.rank=(binaryMatrixLift M A).rank :=
    Matrix.rank_submatrix (binaryMatrixLift M A) (Equiv.refl _) (reverseBooleanEquiv t)
  have hle : R.rank ≤ 3 := by
    rw [hr,binaryMatrixLift_rank M hM A]
    simpa using Matrix.rank_le_card_width A
  have hle2 : R.rank ≤ 2 := by
    rcases hR.identities.rank_zero_or_power with hz | ⟨k,hk⟩
    · omega
    · have hk1 : k ≤ 1 := by
        by_contra hn
        have hp := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (show 2 ≤ k by omega)
        rw [← hk] at hp
        norm_num at hp
        omega
      rcases (show k=0 ∨ k=1 by omega) with rfl | rfl <;> norm_num at hk ⊢ <;> omega
  have hh := hR.identities.reverse_output_of_rank_le_two hle2
  have he : (fun x y => R x (fun i => y i.rev)) = binaryMatrixLift M A := by
    ext x y
    simp only [R,Fin.rev_rev]
  rw [he] at hh
  exact hh.exactMatrix

 theorem leftTransform_binaryDomainTensor {t : ℕ}
    (M : Matrix (Fin 3) (BooleanInput t) ℂ) (A : Matrix (Fin 3) (Fin 3) ℂ)
    (y : Fin 2 → BooleanInput t) :
    leftTransform M (binaryDomainTensor A) y = binaryMatrixLift M A (y 0) (y 1) := by
  classical
  unfold leftTransform
  rw [← (finTwoArrowEquiv (Fin 3)).symm.sum_comp]
  rw [Fintype.sum_prod_type]
  simp only [binaryDomainTensor,finTwoArrowEquiv_symm_apply,Matrix.cons_val_zero,
    Matrix.cons_val_one,Fin.prod_univ_two]
  simp only [binaryMatrixLift,Matrix.mul_apply,Matrix.transpose_apply]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

 theorem binaryPhysicalLift_eq_cast_leftBooleanLift {t : ℕ}
    (M : Matrix (Fin 3) (BooleanInput t) ℂ) (A : Matrix (Fin 3) (Fin 3) ℂ) :
    binaryPhysicalLift M A = fun z : BooleanInput (t+t) =>
      leftBooleanLift M 2 (binaryDomainTensor A) (fun i => z (Fin.cast (by omega : 2*t=t+t) i)) := by
  ext z
  unfold leftBooleanLift
  rw [leftTransform_binaryDomainTensor]
  unfold binaryPhysicalLift
  congr 1
  · funext j
    congr 1
    apply Fin.ext
    simp [finProdFinEquiv]

/-- The source's actual block-major exact lift implies exactness of the
natural bilinear matrix. The reversal is justified by its proved rank ≤ 2. -/
 theorem binaryMatrixLift_exact_of_leftBooleanLift {t : ℕ}
    (M : Matrix (Fin 3) (BooleanInput t) ℂ) (hM : M.rank=3)
    (A : Matrix (Fin 3) (Fin 3) ℂ)
    (hA : ExactMatchgate (leftBooleanLift M 2 (binaryDomainTensor A))) :
    ExactMatchgateMatrix (binaryMatrixLift M A) := by
  apply binaryMatrixLift_exact_of_physical M hM A
  rw [binaryPhysicalLift_eq_cast_leftBooleanLift]
  exact (hA.matchgateIdentities.castArity (by omega : 2*t=t+t)).exactMatchgate

/-- Full binary alternative for actual two-port tensors and their actual
block-major lifts. The adapted basis is fixed before every tensor is quantified. -/
 theorem exact_binary_context_alternative {t : ℕ}
    (M : Matrix (Fin 3) (BooleanInput t) ℂ) (hM : M.rank=3)
    (Q : Matrix (BooleanInput 1) (BooleanInput t) ℂ) (d : BinaryAdaptedRows M Q) :
    BinarySmallCover M ∨ ∀ A : Matrix (Fin 3) (Fin 3) ℂ,
      ExactMatchgate (leftBooleanLift M 2 (binaryDomainTensor A)) → PartialMonomial A := by
  rcases binary_context_alternative M hM Q d with hc | hm
  · exact Or.inl hc
  · exact Or.inr (fun A hA => hm A (binaryMatrixLift_exact_of_leftBooleanLift M hM A hA))

end
end MatchgateWidth
