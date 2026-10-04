import MatchgateWidth.MatchgateIdentities
import MatchgateWidth.StarContraction

/-!
# Sparse coordinate signatures satisfy the literal matchgate identities

Coordinate pins, and arbitrary weighted sums of two coordinate pins at Boolean
words of Hamming distance two, satisfy every MGI. The proof is direct:
all possible nonzero identities reduce to a pair of cancelling summands.
No planar realization or sparse-signature realization theorem is assumed.
-/

namespace MatchgateWidth

open scoped symmDiff

variable {R : Type*} [CommRing R] {s : ℕ}

private theorem coordinate_xor_common (A B C : Finset (Fin s)) :
    (A ∆ C) ∆ (B ∆ C) = A ∆ B := by
  rw [symmDiff_symmDiff_symmDiff_comm, symmDiff_self, symmDiff_bot]

/-- A signature supported on one coordinate satisfies every literal MGI. -/
theorem matchgateIdentities_of_support_singleton (G : SubsetSignature s R)
    (P : Finset (Fin s)) (hsupport : ∀ S, S ≠ P → G S = 0) :
    MatchgateIdentities G := by
  intro A B
  by_cases hAB : A = B
  · subst B
    simp [matchgateSum]
  · unfold matchgateSum
    apply Finset.sum_eq_zero
    intro j _
    by_cases hA : A ∆ {((A ∆ B).sort (· ≤ ·))[j]} = P
    · have hB : B ∆ {((A ∆ B).sort (· ≤ ·))[j]} ≠ P := by
        intro hB
        apply hAB
        exact symmDiff_left_inj.mp (hA.trans hB.symm)
      rw [hsupport _ hB, mul_zero]
    · rw [hsupport _ hA, mul_zero, zero_mul]

private theorem coordinate_matchgateSum_pair (G : SubsetSignature s R)
    (A B : Finset (Fin s)) (i j : Fin s) (hij : i < j)
    (hAB : A ∆ B = {i, j}) :
    matchgateSum G A B ((A ∆ B).sort (· ≤ ·)) = 0 := by
  have hsort : ({i, j} : Finset (Fin s)).sort (· ≤ ·) = [i, j] := by
    rw [Finset.sort_insert (· ≤ ·)]
    · simp
    · intro x hx
      simpa only [Finset.mem_singleton.mp hx] using hij.le
    · simpa using hij.ne
  have hpair : ({i} : Finset (Fin s)) ∆ {j} = {i, j} := by
    ext x
    simp only [Finset.mem_symmDiff, Finset.mem_singleton, Finset.mem_insert]
    grind
  have h₁ : A ∆ {i} = B ∆ {j} := by
    apply symmDiff_eq_bot.mp
    rw [symmDiff_symmDiff_symmDiff_comm, hAB, hpair, symmDiff_self]
  have h₂ : B ∆ {i} = A ∆ {j} := by
    apply symmDiff_eq_bot.mp
    rw [symmDiff_symmDiff_symmDiff_comm, symmDiff_comm B A, hAB, hpair,
      symmDiff_self]
  rw [hAB, hsort]
  simp only [matchgateSum, List.length_cons, List.length_nil, Fin.sum_univ_succ,
    Fin.sum_univ_zero]
  simp only [Fin.getElem_fin, Fin.val_zero, Fin.val_succ,
    List.getElem_cons_zero, List.getElem_cons_succ]
  rw [h₁, h₂]
  ring

/-- A signature supported on two subsets whose symmetric difference has two
ports satisfies all literal matchgate identities, over any commutative ring. -/
theorem matchgateIdentities_of_support_pair (G : SubsetSignature s R)
    (P Q : Finset (Fin s)) (hPQ : (P ∆ Q).card = 2)
    (hsupport : ∀ S, S ≠ P → S ≠ Q → G S = 0) :
    MatchgateIdentities G := by
  intro A B
  by_cases hAB : A = B
  · subst B
    simp [matchgateSum]
  · by_cases hdiff : A ∆ B = P ∆ Q
    · obtain ⟨i, j, hij, hpq⟩ := Finset.card_eq_two.mp hPQ
      rcases lt_or_gt_of_ne hij with hij | hji
      · exact coordinate_matchgateSum_pair G A B i j hij (hdiff.trans hpq)
      · apply coordinate_matchgateSum_pair G A B j i hji
        rw [hdiff, hpq, Finset.pair_comm]
    · unfold matchgateSum
      apply Finset.sum_eq_zero
      intro j _
      let x := ((A ∆ B).sort (· ≤ ·))[j]
      have hzero : G (A ∆ {x}) * G (B ∆ {x}) = 0 := by
        by_cases hAP : A ∆ {x} = P
        · by_cases hBP : B ∆ {x} = P
          · exact (hAB (symmDiff_left_inj.mp (hAP.trans hBP.symm))).elim
          · have hBQ : B ∆ {x} ≠ Q := by
              intro hBQ
              apply hdiff
              rw [← coordinate_xor_common A B {x}, hAP, hBQ]
            rw [hsupport _ hBP hBQ, mul_zero]
        · by_cases hAQ : A ∆ {x} = Q
          · have hBP : B ∆ {x} ≠ P := by
              intro hBP
              apply hdiff
              rw [← coordinate_xor_common A B {x}, hAQ, hBP, symmDiff_comm]
            have hBQ : B ∆ {x} ≠ Q := by
              intro hBQ
              exact hAB (symmDiff_left_inj.mp (hAQ.trans hBQ.symm))
            rw [hsupport _ hBP hBQ, mul_zero]
          · rw [hsupport _ hAP hAQ, zero_mul]
      change (-1 : R) ^ (j.val + 1) * G (A ∆ {x}) * G (B ∆ {x}) = 0
      rw [mul_assoc, hzero, mul_zero]

/-- Every coordinate pin at every Boolean word satisfies the actual MGI. -/
theorem coordinatePin_booleanMatchgateIdentities (p : BooleanInput s) :
    BooleanMatchgateIdentities (coordinatePin (K := R) p) := by
  classical
  apply matchgateIdentities_of_support_singleton _ (booleanSubsetEquiv s p)
  intro S hS
  have h : (booleanSubsetEquiv s).symm S ≠ p := by
    intro hp
    apply hS
    rw [← hp, Equiv.apply_symm_apply]
  simp [coordinatePin, h]

/-- A weighted sum of two Boolean coordinate pins at Hamming distance two
satisfies the actual MGI. The weights may vanish and the ring may have zero
divisors. -/
theorem weightedCoordinatePair_booleanMatchgateIdentities
    (p q : BooleanInput s) (a b : R)
    (hpq : (booleanSubsetEquiv s p ∆ booleanSubsetEquiv s q).card = 2) :
    BooleanMatchgateIdentities
      (fun z => a * coordinatePin p z + b * coordinatePin q z) := by
  classical
  apply matchgateIdentities_of_support_pair _ (booleanSubsetEquiv s p)
    (booleanSubsetEquiv s q) hpq
  intro S hP hQ
  have hSP : (booleanSubsetEquiv s).symm S ≠ p := by
    intro h
    apply hP
    rw [← h, Equiv.apply_symm_apply]
  have hSQ : (booleanSubsetEquiv s).symm S ≠ q := by
    intro h
    apply hQ
    rw [← h, Equiv.apply_symm_apply]
  simp [coordinatePin, hSP, hSQ]

/-- The subset symmetric difference is exactly the set of differing Boolean
positions, so the preceding hypothesis is ordinary Hamming distance two. -/
theorem booleanSubsetEquiv_symmDiff_eq_disagreements (p q : BooleanInput s) :
    booleanSubsetEquiv s p ∆ booleanSubsetEquiv s q =
      Finset.univ.filter (fun i => p i ≠ q i) := by
  ext i
  simp only [Finset.mem_symmDiff, mem_booleanSubsetEquiv, Finset.mem_filter,
    Finset.mem_univ, true_and]
  generalize hp : p i = a
  generalize hq : q i = b
  fin_cases a <;> fin_cases b <;> simp

/-- A user-facing form with the two different positions named explicitly. -/
theorem weightedCoordinatePair_booleanMatchgateIdentities_of_two_positions
    (p q : BooleanInput s) (a b : R) (i j : Fin s) (hij : i ≠ j)
    (hpq : ∀ k, p k ≠ q k ↔ k = i ∨ k = j) :
    BooleanMatchgateIdentities
      (fun z => a * coordinatePin p z + b * coordinatePin q z) := by
  apply weightedCoordinatePair_booleanMatchgateIdentities
  rw [booleanSubsetEquiv_symmDiff_eq_disagreements]
  have hset : Finset.univ.filter (fun k => p k ≠ q k) = {i, j} := by
    ext k
    simp [hpq k]
  rw [hset]
  simp [hij]

/-- The two one-hot marker words, with every other port zero, give the lifted
marker disequality used in the Section 8 left family. -/
def liftedMarkerDisequality (i j : Fin s) : BooleanTable s R :=
  fun z => coordinatePin ((booleanSubsetEquiv s).symm {i}) z +
    coordinatePin ((booleanSubsetEquiv s).symm {j}) z

/-- Lifted marker disequality satisfies the full algebraic matchgate identities.
This does not assert a planar realization. -/
theorem liftedMarkerDisequality_booleanMatchgateIdentities
    (i j : Fin s) (hij : i ≠ j) :
    BooleanMatchgateIdentities (liftedMarkerDisequality (R := R) i j) := by
  have hpair : ({i} : Finset (Fin s)) ∆ {j} = {i, j} := by
    ext k
    simp only [Finset.mem_symmDiff, Finset.mem_singleton, Finset.mem_insert]
    grind
  have hcard : (booleanSubsetEquiv s ((booleanSubsetEquiv s).symm {i}) ∆
      booleanSubsetEquiv s ((booleanSubsetEquiv s).symm {j})).card = 2 := by
    simp only [Equiv.apply_symm_apply, hpair]
    simp [hij]
  unfold liftedMarkerDisequality
  simpa only [one_mul] using weightedCoordinatePair_booleanMatchgateIdentities
    ((booleanSubsetEquiv s).symm {i}) ((booleanSubsetEquiv s).symm {j})
    (1 : R) 1 hcard

end MatchgateWidth
