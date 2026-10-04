import MatchgateWidth.BinaryLiftMatrix

/-! # Binary plane confinement and exact global parity -/
namespace MatchgateWidth
noncomputable section
set_option maxHeartbeats 800000

 theorem OrderedMatchgateMatrix.matrix_parity {r t : ℕ}
    {P : Matrix (BooleanInput r) (BooleanInput t) ℂ} (hP : OrderedMatchgateMatrix P) :
    ∃ k < 2, ∀ x y, (booleanParity x+booleanParity y)%2 ≠ k → P x y=0 := by
  obtain ⟨p,q,c,A,B,D,_,_,_,_,he⟩ := hP.exists_gaussian_chart
  refine ⟨(booleanParity p+booleanParity q)%2,Nat.mod_lt _ (by decide),?_⟩
  intro x y hxy
  rw [he]
  have hz : (booleanParity (pfaffianXor p x)+booleanParity (pfaffianXor q y))%2=1 := by
    rw [booleanParity_xor,booleanParity_xor]
    have hp := booleanParity_lt_two p
    have hq := booleanParity_lt_two q
    have hx := booleanParity_lt_two x
    have hy := booleanParity_lt_two y
    omega
  rw [gaussianOrderedMatrix_odd A B D _ _ hz,mul_zero]

 theorem BinaryAdaptedRows.plane_binary_partial_monomial {t : ℕ}
    {M : Matrix (Fin 3) (BooleanInput t) ℂ}
    {Q : Matrix (BooleanInput 1) (BooleanInput t) ℂ}
    (d : BinaryAdaptedRows M Q) (hM : M.rank=3)
    (A : Matrix (Fin 3) (Fin 3) ℂ) (hA : ExactMatchgateMatrix (binaryMatrixLift M A))
    (hr : ∀ i, A i 2=0) (hc : ∀ j, A 2 j=0) : PartialMonomial A := by
  obtain ⟨x,hx⟩ := Function.ne_iff.mp (fullrank_row_ne_zero M hM 0)
  obtain ⟨y,hy⟩ := Function.ne_iff.mp (fullrank_row_ne_zero M hM 1)
  have hpx : booleanParity x=0 := by
    by_contra hn
    exact hx (d.evenParity x hn)
  have hpy : booleanParity y=1 := by
    by_contra hn
    exact hy (d.oddParity y hn)
  have hx1 : M 1 x=0 := d.oddParity x (by omega)
  have hy0 : M 0 y=0 := d.evenParity y (by omega)
  have hxx : binaryMatrixLift M A x x = M 0 x * A 0 0 * M 0 x := by
    simp [binaryMatrixLift,Matrix.mul_apply,Fin.sum_univ_succ,hx1,hr,hc]
  have hxy : binaryMatrixLift M A x y = M 0 x * A 0 1 * M 1 y := by
    simp [binaryMatrixLift,Matrix.mul_apply,Fin.sum_univ_succ,hx1,hy0,hr,hc]
  have hyx : binaryMatrixLift M A y x = M 1 y * A 1 0 * M 0 x := by
    simp [binaryMatrixLift,Matrix.mul_apply,Fin.sum_univ_succ,hx1,hy0,hr,hc]
  have hyy : binaryMatrixLift M A y y = M 1 y * A 1 1 * M 1 y := by
    simp [binaryMatrixLift,Matrix.mul_apply,Fin.sum_univ_succ,hy0,hr,hc]
  obtain ⟨k,hk,hpar⟩ := hA.identities.matrix_parity
  have hdiag : (A 0 1=0 ∧ A 1 0=0) ∨ (A 0 0=0 ∧ A 1 1=0) := by
    rcases (show k=0 ∨ k=1 by omega) with rfl | rfl
    · left
      have hp1 := hpar x y (by simp [hpx,hpy])
      have hp2 := hpar y x (by simp [hpx,hpy])
      rw [hxy] at hp1
      rw [hyx] at hp2
      exact ⟨(mul_eq_zero.mp ((mul_eq_zero.mp hp1).resolve_right hy)).resolve_left hx,
        (mul_eq_zero.mp ((mul_eq_zero.mp hp2).resolve_right hx)).resolve_left hy⟩
    · right
      have hp1 := hpar x x (by simp [hpx])
      have hp2 := hpar y y (by simp [hpy])
      rw [hxx] at hp1
      rw [hyy] at hp2
      exact ⟨(mul_eq_zero.mp ((mul_eq_zero.mp hp1).resolve_right hx)).resolve_left hx,
        (mul_eq_zero.mp ((mul_eq_zero.mp hp2).resolve_right hy)).resolve_left hy⟩
  rcases hdiag with ⟨h01,h10⟩ | ⟨h00,h11⟩
  · constructor <;> intro i j k hj hk <;> fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all
  · constructor <;> intro i j k hj hk <;> fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all

end
end MatchgateWidth
