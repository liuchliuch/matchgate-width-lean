import MatchgateWidth.PfaffianPairPartitions
import MatchgateWidth.PfaffianGeneralPermutation
import Mathlib.Data.List.NodupEquivFin

/-!
# The permutation sign of a pair partition

The canonical pair sequence determines a unique coordinate permutation. Its
ordinary permutation sign agrees with the inversion-count sign used by the
signed pair-partition sum, closing both conventions in the source definition.
-/

namespace MatchgateWidth
variable {ι R : Type*} [LinearOrder ι]

/-- The recursive list inversion count agrees with the ordinary permutation's
number of inverted position pairs, in any strictly increasing coordinate scale. -/
theorem pairInversions_ofFn_comp_perm {n : ℕ} (f : Fin n → ι)
    (hf : StrictMono f) (σ : Equiv.Perm (Fin n)) :
    pairInversions (List.ofFn (f ∘ σ)) = permutationInversions σ := by
  rw [pairInversions_eq_sum_positions]
  have hn : n = (List.ofFn (f ∘ σ)).length := List.length_ofFn.symm
  rw [← Fin.sum_congr' _ hn]
  unfold permutationInversions
  apply Finset.sum_congr rfl
  intro i _
  rw [← Fin.sum_congr' _ hn]
  simp only [Fin.getElem_fin, List.getElem_ofFn, Function.comp_def,
    Fin.val_cast, Fin.eta, hf.lt_iff_lt, Fin.cast_lt_cast]
  have hs : (Finset.Ioi i).filter (fun j => σ j < σ i) =
      Finset.univ.filter (fun j => i < j ∧ σ j < σ i) := by
    ext j
    simp
  rw [hs, Finset.card_filter]

/-- The unique coordinate permutation whose one-line coordinate sequence is
the flattened sequence of a canonical pair partition. -/
def pairPartitionPermutation {xs : List ι} (hs : xs.Pairwise (· < ·))
    {ps : List (ι × ι)} (hp : ps ∈ pairPartitions xs) : Equiv.Perm (Fin xs.length) :=
  let hperm := pairSequence_perm_of_mem_pairPartitions hp
  (finCongr hperm.length_eq.symm).trans
    ((List.Nodup.getEquiv (pairSequence ps) (hperm.symm.nodup hs.nodup)).trans
      ((Equiv.subtypeEquivRight (fun _ => hperm.mem_iff)).trans
        (List.Nodup.getEquiv xs hs.nodup).symm))

/-- The defining coordinate identity of the pair partition's permutation. -/
theorem ofFn_pairPartitionPermutation {xs : List ι} (hs : xs.Pairwise (· < ·))
    {ps : List (ι × ι)} (hp : ps ∈ pairPartitions xs) :
    List.ofFn (xs.get ∘ pairPartitionPermutation hs hp) = pairSequence ps := by
  apply List.ext_getElem
  · simp only [List.length_ofFn]
    exact (pairSequence_perm_of_mem_pairPartitions hp).length_eq.symm
  · intro k hk₁ hk₂
    simp only [List.getElem_ofFn, Function.comp_def, pairPartitionPermutation,
      Equiv.trans_apply, finCongr_apply]
    simp

/-- The flattening coordinate identity uniquely determines the permutation. -/
theorem pairPartitionPermutation_unique {xs : List ι} (hs : xs.Pairwise (· < ·))
    {ps : List (ι × ι)} (hp : ps ∈ pairPartitions xs)
    (σ : Equiv.Perm (Fin xs.length))
    (hσ : List.ofFn (xs.get ∘ σ) = pairSequence ps) :
    σ = pairPartitionPermutation hs hp := by
  have heq := List.ofFn_injective (hσ.trans (ofFn_pairPartitionPermutation hs hp).symm)
  apply Equiv.ext
  intro i
  exact hs.nodup.get_inj_iff.mp (congrFun heq i)

/-- The inversion exponent of a pair partition is exactly the inversion count
of its uniquely specified coordinate permutation. -/
theorem pairInversions_eq_permutationInversions {xs : List ι}
    (hs : xs.Pairwise (· < ·)) {ps : List (ι × ι)}
    (hp : ps ∈ pairPartitions xs) :
    pairInversions (pairSequence ps) =
      permutationInversions (pairPartitionPermutation hs hp) := by
  rw [← ofFn_pairPartitionPermutation hs hp]
  exact pairInversions_ofFn_comp_perm xs.get hs.sortedLT.strictMono_get _

/-- The source identity `sgn(π) = sgn(σπ) = (-1)^Nπ`, with the ordinary
permutation sign in the units of the integers. -/
theorem pairPartitionPermutation_sign {xs : List ι} (hs : xs.Pairwise (· < ·))
    {ps : List (ι × ι)} (hp : ps ∈ pairPartitions xs) :
    Equiv.Perm.sign (pairPartitionPermutation hs hp) =
      (-1 : ℤˣ) ^ pairInversions (pairSequence ps) := by
  rw [permutationSign_eq_negOne_pow, pairInversions_eq_permutationInversions hs hp]

variable [CommRing R]

/-- Every term in the proved Pfaffian pair-partition sum has precisely the
source's permutation sign times its perfect-matching monomial. -/
theorem signedPairMonomial_eq_permutationSign (A : Matrix ι ι R)
    {xs : List ι} (hs : xs.Pairwise (· < ·)) {ps : List (ι × ι)}
    (hp : ps ∈ pairPartitions xs) :
    signedPairMonomial A ps =
      ((Equiv.Perm.sign (pairPartitionPermutation hs hp) : ℤ) : R) *
        (ps.map (fun p => A p.1 p.2)).prod := by
  rw [pairPartitionPermutation_sign hs hp]
  simp [signedPairMonomial, pairMonomial]

/-- The complete source definition, using the ordinary sign of the unique
flattening permutation and a finite sum over all canonical pair partitions. -/
theorem pfaffianList_eq_sum_permutationSign (A : Matrix ι ι R)
    {xs : List ι} (hs : xs.Pairwise (· < ·)) :
    pfaffianList A xs = ∑ ps : ↥(canonicalPairPartitions xs),
      ((Equiv.Perm.sign (pairPartitionPermutation hs
        (List.mem_toFinset.mp ps.property)) : ℤ) : R) *
          (ps.val.map (fun p => A p.1 p.2)).prod := by
  calc
    pfaffianList A xs = ∑ ps ∈ canonicalPairPartitions xs,
        signedPairMonomial A ps := pfaffianList_eq_sum_pairPartitions A hs
    _ = ∑ ps : ↥(canonicalPairPartitions xs), signedPairMonomial A ps.val :=
      (Finset.sum_coe_sort _ _).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro ps _
      exact signedPairMonomial_eq_permutationSign A hs
        (List.mem_toFinset.mp ps.property)

end MatchgateWidth
