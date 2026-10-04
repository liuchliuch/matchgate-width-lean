import MatchgateWidth.MatchgateIdentities
import Mathlib.Data.Fin.Rev

/-!
# Global reversal of matchgate coordinates

Reversing the complete linear order of the external ports preserves the literal
matchgate identities. This is a statement about the algebraic identities only.
-/

namespace MatchgateWidth

open scoped symmDiff

/-- Reverse all port labels of a subset coordinate. -/
def reversePortSubset {s : ℕ} (S : Finset (Fin s)) : Finset (Fin s) :=
  S.image Fin.rev

@[simp] theorem mem_reversePortSubset {s : ℕ} (S : Finset (Fin s)) (i : Fin s) :
    i ∈ reversePortSubset S ↔ i.rev ∈ S := by
  simp only [reversePortSubset, Finset.mem_image]
  constructor
  · rintro ⟨j, hj, rfl⟩
    simpa using hj
  · intro h
    exact ⟨i.rev, h, Fin.rev_rev i⟩

@[simp] theorem reversePortSubset_symmDiff {s : ℕ} (S T : Finset (Fin s)) :
    reversePortSubset (S ∆ T) = reversePortSubset S ∆ reversePortSubset T := by
  ext i
  simp [Finset.mem_symmDiff]

@[simp] theorem reversePortSubset_singleton {s : ℕ} (i : Fin s) :
    reversePortSubset {i} = {i.rev} := by
  simp [reversePortSubset]

@[simp] theorem reversePortSubset_reversePortSubset {s : ℕ} (S : Finset (Fin s)) :
    reversePortSubset (reversePortSubset S) = S := by
  ext i
  simp

/-- Sorting a globally reversed subset reverses the sorted list of reversed labels. -/
theorem sort_reversePortSubset {s : ℕ} (S : Finset (Fin s)) :
    (reversePortSubset S).sort (· ≤ ·) = ((S.sort (· ≤ ·)).map Fin.rev).reverse := by
  have hn : (((S.sort (· ≤ ·)).map Fin.rev).reverse).Nodup :=
    List.nodup_reverse.mpr ((List.nodup_map_iff Fin.rev_injective).mpr (Finset.sort_nodup S _))
  have hset : (((S.sort (· ≤ ·)).map Fin.rev).reverse).toFinset = reversePortSubset S := by
    ext i
    simp only [List.toFinset_reverse, List.mem_toFinset, List.mem_map,
      Finset.mem_sort, reversePortSubset, Finset.mem_image]
  rw [← hset]
  apply (List.toFinset_sort (· ≤ ·) hn).mpr
  rw [List.pairwise_reverse]
  exact (S.pairwise_sort (· ≤ ·)).map Fin.rev (fun _ _ h => Fin.rev_le_rev.mpr h)

/-- Reversing the difference list changes the alternating expression by one
common sign, including the empty-list case. -/
theorem matchgateSum_reverse {s : ℕ} {R : Type*} [CommRing R]
    (G : SubsetSignature s R) (α β : Finset (Fin s)) (p : List (Fin s)) :
    matchgateSum G α β p.reverse =
      (-1 : R) ^ (p.length + 1) * matchgateSum G α β p := by
  unfold matchgateSum
  rw [Finset.mul_sum]
  apply Finset.sum_equiv
    ((Fin.castOrderIso (List.length_reverse (as := p))).toEquiv.trans Fin.revPerm)
  · intro i
    simp
  · intro i _
    simp only [Equiv.trans_apply, Fin.revPerm_apply, Fin.castOrderIso,
      Fin.getElem_fin, List.getElem_reverse, Fin.val_rev, Fin.val_cast, Equiv.coe_fn_mk, Nat.sub_sub]
    have hi : i.val < p.length := by simpa using i.isLt
    have hs : (-1 : R) ^ (i.val + 1) =
        (-1 : R) ^ (p.length + 1) * (-1 : R) ^ (p.length - 1 - i.val + 1) := by
      rw [← pow_add]
      conv_lhs => rw [neg_one_pow_eq_pow_mod_two]
      conv_rhs => rw [neg_one_pow_eq_pow_mod_two]
      congr 1
      omega
    rw [hs]
    simp only [Nat.sub_sub, mul_assoc, Nat.add_comm]

/-- Relabel the entries and both arguments of an explicitly ordered MGI sum. -/
theorem matchgateSum_reversePortSubset {s : ℕ} {R : Type*} [CommRing R]
    (G : SubsetSignature s R) (α β : Finset (Fin s)) (p : List (Fin s)) :
    matchgateSum G (reversePortSubset α) (reversePortSubset β) (p.map Fin.rev) =
      matchgateSum (fun S => G (reversePortSubset S)) α β p := by
  unfold matchgateSum
  apply Finset.sum_equiv
    (Fin.castOrderIso (by simp : (p.map Fin.rev).length = p.length)).toEquiv
  · intro i
    simp
  · intro i _
    simp [Fin.castOrderIso, Fin.getElem_fin, List.getElem_map]

/-- Global reversal, rather than an arbitrary coordinate permutation,
preserves the literal ordered matchgate identities over every commutative ring. -/
theorem MatchgateIdentities.reverse {s : ℕ} {R : Type*} [CommRing R]
    {G : SubsetSignature s R} (hG : MatchgateIdentities G) :
    MatchgateIdentities (fun S => G (reversePortSubset S)) := by
  intro α β
  have h := hG (reversePortSubset α) (reversePortSubset β)
  rw [← reversePortSubset_symmDiff, sort_reversePortSubset, matchgateSum_reverse,
    matchgateSum_reversePortSubset] at h
  exact (neg_one_pow_mul_eq_zero_iff).mp h

@[simp] theorem booleanSubsetEquiv_symm_reversePortSubset {s : ℕ}
    (S : Finset (Fin s)) :
    (booleanSubsetEquiv s).symm (reversePortSubset S) =
      fun i => (booleanSubsetEquiv s).symm S i.rev := by
  funext i
  simp [booleanSubsetEquiv]

/-- Reversing all Boolean coordinates preserves the full MGI, including arity
zero. No planar realization theorem or extra parity hypothesis is needed. -/
theorem BooleanMatchgateIdentities.reverse {s : ℕ} {R : Type*} [CommRing R]
    {f : BooleanTable s R} (hf : BooleanMatchgateIdentities f) :
    BooleanMatchgateIdentities (fun z => f (fun i => z i.rev)) := by
  simpa only [BooleanMatchgateIdentities, booleanSubsetEquiv_symm_reversePortSubset]
    using MatchgateIdentities.reverse hf

end MatchgateWidth
