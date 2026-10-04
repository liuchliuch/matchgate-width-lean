import MatchgateWidth.FullRowDecoder
import MatchgateWidth.GaussianFullRank

/-! # Full-rank output-mode minors of Gaussian matrices

A full-row-rank cross block has an increasing square column minor of full
rank. Restricting the actual Gaussian/Pfaffian matrix to those modes leaves
both quadratic blocks intact and gives a nonsingular square Boolean cube.
-/
namespace MatchgateWidth
noncomputable section

variable {K : Type*} [Field K]

/-- Full row rank admits a square column minor whose columns retain their
original increasing order. -/
theorem exists_increasing_fullRank_column_minor {r t : ℕ}
    (B : Matrix (Fin r) (Fin t) K) (hB : B.rank = r) :
    ∃ e : Fin r ↪o Fin t, (B.submatrix id e).rank = r := by
  classical
  obtain ⟨s, _, _, hs, hli⟩ := exists_linearIndepOn_extension
    (linearIndepOn_empty K B.col) (Set.empty_subset (Set.univ : Set (Fin t)))
  have htop : Submodule.span K (Set.range B.col) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [← Matrix.rank_eq_finrank_span_cols, hB, Module.finrank_pi, Fintype.card_fin]
  have hspan : Submodule.span K (B.col '' s) = ⊤ := by
    apply top_unique
    rw [← htop]
    apply Submodule.span_le.mpr
    simpa only [Set.image_univ] using hs
  have hrange : Set.range (fun i : s => B.col i) = B.col '' s := by
    ext v
    simp
  let : Fintype s := Fintype.ofFinite s
  have hc : Fintype.card s = r := by
    have h := linearIndependent_iff_card_eq_finrank_span.mp hli
    change Fintype.card s = Module.finrank K (Submodule.span K (Set.range (fun i : s => B.col i))) at h
    rw [hrange, hspan, finrank_top, Module.finrank_pi, Fintype.card_fin] at h
    exact h
  let sf := s.toFinset
  have hsf : sf.card = r := by simpa only [sf, Set.toFinset_card] using hc
  let e : Fin r ↪o Fin t := sf.orderEmbOfFin hsf
  refine ⟨e, ?_⟩
  rw [Matrix.rank_eq_finrank_span_cols]
  have hr : Set.range (B.submatrix id e).col = B.col '' s := by
    change Set.range (B.col ∘ e) = _
    rw [Set.range_comp, show Set.range e = s from by
      simpa only [e, sf, Set.coe_toFinset] using sf.range_orderEmbOfFin hsf]
  rw [hr, hspan, finrank_top, Module.finrank_pi, Fintype.card_fin]

variable {R I J J' : Type*} [CommRing R]

/-- Principal-Pfaffian coefficients are natural under a relabeling of the
output block; both internal quadratic blocks remain present. -/
theorem gaussianFullPfaffian_map_output
    (A : Matrix I I R) (B : Matrix I J R) (D : Matrix J J R)
    (e : J' → J) (xs : List I) (ys : List J') :
    gaussianFullPfaffian A B D xs (ys.map e) =
      gaussianFullPfaffian A (B.submatrix id e) (D.submatrix e e) xs ys := by
  let f : I ⊕ J' → I ⊕ J := Sum.map id e
  have hlist : xs.map Sum.inl ++ (ys.map e).map Sum.inr =
      (xs.map Sum.inl ++ ys.map Sum.inr).map f := by
    simp [List.map_append, List.map_map, f, Function.comp_def]
  simp only [gaussianFullPfaffian, hlist, pfaffianList_map]
  congr 1
  funext x y
  cases x <;> cases y <;> rfl

/-- Increasing mode selection commutes with the actual full Gaussian matrix. -/
theorem gaussianFullPlanarPfaffianMatrix_map_output
    [LinearOrder I] [LinearOrder J] [LinearOrder J']
    (A : Matrix I I R) (B : Matrix I J R) (D : Matrix J J R)
    (e : J' ↪o J) :
    (gaussianFullPlanarPfaffianMatrix A B D).submatrix id
      (fun S => S.map e.toEmbedding) =
      gaussianFullPlanarPfaffianMatrix A (B.submatrix id e) (D.submatrix e e) := by
  ext s t
  simp only [Matrix.submatrix_apply, id_eq, gaussianFullPlanarPfaffianMatrix,
    gaussianSubsetList_eq_sort]
  rw [← Finset.map_sort e.toEmbedding t (· ≤ ·) (· ≤ ·)
    (fun a _ b _ => e.le_iff_le.symm), ← List.map_reverse]
  exact gaussianFullPfaffian_map_output A B D e _ _

variable [CharZero K]

/-- The full Gaussian principal-Pfaffian matrix has a nonsingular output-mode
cube whenever its cross block has full row rank.  No Gaussian elimination
or exact-matchgate canonical form is assumed. -/
theorem gaussianFullPlanarPfaffianMatrix_exists_mode_minor {r t : ℕ}
    (A : Matrix (Fin r) (Fin r) K) (B : Matrix (Fin r) (Fin t) K)
    (D : Matrix (Fin t) (Fin t) K)
    (hA : ∀ i j, A i j = -A j i) (hD : ∀ i j, D i j = -D j i)
    (hB : B.rank = r) :
    ∃ e : Fin r ↪o Fin t,
      IsUnit ((gaussianFullPlanarPfaffianMatrix A B D).submatrix id
        (fun S => S.map e.toEmbedding)).det := by
  obtain ⟨e, he⟩ := exists_increasing_fullRank_column_minor B hB
  refine ⟨e, ?_⟩
  rw [gaussianFullPlanarPfaffianMatrix_map_output]
  let Q := gaussianFullPlanarPfaffianMatrix A (B.submatrix id e) (D.submatrix e e)
  have hQ : Q.rank = Fintype.card (Finset (Fin r)) := by
    dsimp only [Q]
    rw [gaussianFullPlanarPfaffianMatrix_rank A (B.submatrix id e) (D.submatrix e e) hA
      (fun i j => hD (e i) (e j)), he]
    simp
  obtain ⟨N, hN⟩ := exists_baseDecoder Q (transpose_injective_of_rank_eq_card Q hQ)
  exact Matrix.isUnit_det_of_right_inverse hN

/-- Full row rank of the actual full Gaussian matrix suffices for the same
increasing mode-cube certificate. -/
theorem gaussianFullPlanarPfaffianMatrix_exists_mode_minor_of_fullRank {r t : ℕ}
    (A : Matrix (Fin r) (Fin r) K) (B : Matrix (Fin r) (Fin t) K)
    (D : Matrix (Fin t) (Fin t) K)
    (hA : ∀ i j, A i j = -A j i) (hD : ∀ i j, D i j = -D j i)
    (hfull : (gaussianFullPlanarPfaffianMatrix A B D).rank = 2 ^ r) :
    ∃ e : Fin r ↪o Fin t,
      IsUnit ((gaussianFullPlanarPfaffianMatrix A B D).submatrix id
        (fun S => S.map e.toEmbedding)).det := by
  apply gaussianFullPlanarPfaffianMatrix_exists_mode_minor A B D hA hD
  apply Nat.pow_right_injective (by decide : 2 ≤ 2)
  rwa [gaussianFullPlanarPfaffianMatrix_rank A B D hA hD] at hfull

end
end MatchgateWidth
