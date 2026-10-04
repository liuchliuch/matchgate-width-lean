import MatchgateWidth.MGIMatrixComposition

/-! # Exact ordered transpose closure
Transposition is total boundary reversal, with the equality of the two sums of
arities transported explicitly. There is no arbitrary port permutation.
-/
namespace MatchgateWidth
variable {R : Type*} [CommRing R] {r t : ℕ}

/-- Transport of a signature across equality of its number of ports. -/
theorem BooleanMatchgateIdentities.castArity {m n : ℕ} (h : m = n)
    {f : BooleanTable m R} (hf : BooleanMatchgateIdentities f) :
    BooleanMatchgateIdentities (fun z : BooleanInput n => f (fun i => z (Fin.cast h i))) := by
  subst n
  exact hf

/-- Transposition preserves the literal ordered matchgate identities. -/
theorem OrderedMatchgateMatrix.transpose
    {P : Matrix (BooleanInput r) (BooleanInput t) R}
    (hP : OrderedMatchgateMatrix P) : OrderedMatchgateMatrix P.transpose := by
  have h := (BooleanMatchgateIdentities.reverse hP).castArity (Nat.add_comm r t)
  have heq : (fun z : BooleanInput (t + r) =>
      orderedMatrixSignature P (fun i => z (Fin.cast (Nat.add_comm r t) i.rev))) =
      orderedMatrixSignature P.transpose := by
    funext z
    unfold orderedMatrixSignature
    change P _ _ = P _ _
    congr 1
    · funext i
      apply congrArg z
      apply Fin.ext
      simp only [Fin.val_cast, Fin.val_rev, Fin.val_castAdd, Fin.val_natAdd]
      omega
    · funext j
      apply congrArg z
      apply Fin.ext
      simp only [Fin.val_cast, Fin.val_rev, Fin.val_castAdd, Fin.val_natAdd]
      omega
  change BooleanMatchgateIdentities _
  rw [heq] at h
  exact h

end MatchgateWidth
