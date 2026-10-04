import MatchgateWidth.ControlledFlagEndpoints

/-! # The third coordinate code is an even pure ray -/
namespace MatchgateWidth
noncomputable section
open scoped Classical

theorem controlledLabelledCode_two (k : ℕ) :
    controlledLabelledCode k 2 = fun i => if i = 0 then 0 else 1 := by
  funext i
  by_cases hi : i = 0 <;>
    simp [controlledLabelledCode, booleanWordEquiv, controlledCode, hi]

theorem controlledLabelledCode_two_parity (k : ℕ) (hk : 0 < k) :
    booleanParity (controlledLabelledCode k 2) = 0 := by
  rw [controlledLabelledCode_two]
  have hs : booleanSubsetEquiv (2 ^ k + 3) (fun i => if i = 0 then 0 else 1) =
      (Finset.univ : Finset (Fin (2 ^ k + 3))).erase 0 := by
    ext i
    by_cases hi : i = 0 <;> simp [booleanSubsetEquiv, hi]
  rw [booleanParity,hs,Finset.card_erase_of_mem (Finset.mem_univ _),Finset.card_univ,
    Fintype.card_fin]
  have he : 2 ^ k % 2 = 0 := by
    obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
    simp [pow_succ]
  omega

/-- Exact even/odd/even placement in the single displayed common base. -/
theorem controlled_flag_code_parities (k : ℕ) (hk : 2 ≤ k) :
    booleanParity (controlledLabelledCode k 0) = 0 ∧
    booleanParity (controlledLabelledCode k 1) = 1 ∧
    booleanParity (controlledLabelledCode k 2) = 0 :=
  ⟨controlledLabelledCode_zero_parity k,controlledLabelledCode_one_parity k,
    controlledLabelledCode_two_parity k (by omega)⟩

end
end MatchgateWidth
