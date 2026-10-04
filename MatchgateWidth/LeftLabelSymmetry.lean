import MatchgateWidth.IntegerMainTheorem

/-!
# Port symmetry of every left label

The three unary pins and the binary disequality label are invariant under
arbitrary permutations of their ports. This proves the symmetry assertion in
the paper's introduction (lines 193–197) for the actual labelled language,
independently of the chosen hard table. No symmetry of the right label is used.
-/

namespace MatchgateWidth
noncomputable section
open scoped Classical

/-- A unary qutrit pin is unchanged by every permutation of its single port. -/
theorem qutritPinTensor_perm {K : Type*} [Field K] (r : Fin 3)
    (σ : Equiv.Perm (Fin 1)) (x : Fin 1 → Fin 3) :
    qutritPinTensor (K := K) r (x ∘ σ) = qutritPinTensor r x := by
  have hσ : σ 0 = 0 := Subsingleton.elim _ _
  simp [qutritPinTensor, Function.comp_apply, hσ]

/-- Binary disequality on states zero and one is invariant under every
permutation of its two ports, including when an input is the forbidden state. -/
theorem qutritNeqTensor_perm {K : Type*} [Field K]
    (σ : Equiv.Perm (Fin 2)) (x : Fin 2 → Fin 3) :
    qutritNeqTensor (K := K) (x ∘ σ) = qutritNeqTensor x := by
  have hne : σ 0 ≠ σ 1 := σ.injective.ne (by decide)
  have h0 : σ 0 = 0 ∨ σ 0 = 1 := by omega
  have h1 : σ 1 = 0 ∨ σ 1 = 1 := by omega
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;>
    simp_all [qutritNeqTensor, Function.comp_apply, and_comm, or_comm]

/-- Every left label of the controlled language is symmetric in its ports.
The hard table and chosen control port are arbitrary. -/
theorem controlledLabelledLanguage_left_perm {k : ℕ}
    (f : BooleanTable k ℂ) (j : Fin k)
    (l : (starLanguageShape (k + 2)).LeftLabel)
    (σ : Equiv.Perm (Fin ((starLanguageShape (k + 2)).leftArity l)))
    (x : Fin ((starLanguageShape (k + 2)).leftArity l) → Fin 3) :
    (controlledLabelledLanguage f j).left l (x ∘ σ) =
      (controlledLabelledLanguage f j).left l x := by
  cases l with
  | inl r =>
    have hσ : σ 0 = 0 := Subsingleton.elim _ _
    simp [controlledLabelledLanguage, Function.comp_apply, hσ]
  | inr r =>
    exact qutritNeqTensor_perm σ x

/-- All left labels in the fixed positive-integer family of Theorem 3.1
are invariant under arbitrary port permutations. -/
theorem integerControlledLanguage_left_perm (k : ℕ) (hk : 2 ≤ k)
    (l : (starLanguageShape (k + 2)).LeftLabel)
    (σ : Equiv.Perm (Fin ((starLanguageShape (k + 2)).leftArity l)))
    (x : Fin ((starLanguageShape (k + 2)).leftArity l) → Fin 3) :
    (integerControlledLanguage k hk).left l (x ∘ σ) =
      (integerControlledLanguage k hk).left l x :=
  controlledLabelledLanguage_left_perm (integerHardTableIn ℂ k)
    (integerControlPort k hk) l σ x

end
end MatchgateWidth
