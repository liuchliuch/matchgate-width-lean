import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Rank of the full exterior map

The full exterior algebra of a finite-dimensional vector space has dimension
`2 ^ finrank`.  Factoring a linear map through its actual image proves that its
induced exterior-algebra map has image dimension `2 ^ rank`.

This is the exterior-compound rank calculation used in the rank-two Gaussian
hull argument.  It does not identify any Pfaffian chart or matchgate flattening
with this exterior map.
-/

namespace MatchgateWidth

noncomputable section

variable {K V W : Type*} [Field K]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

/-- The full exterior algebra has one basis vector for every subset of a finite
basis of the original vector space. -/
theorem exteriorAlgebra_finrank [Module.Finite K V] :
    Module.finrank K (ExteriorAlgebra K V) = 2 ^ Module.finrank K V := by
  classical
  rw [Module.finrank_eq_card_basis (Module.finBasis K V).ExteriorAlgebra]
  simp

/-- The actual image of the full exterior map is the image of the exterior
algebra on `range f` under the inclusion into the target exterior algebra. -/
theorem exteriorAlgebra_map_range (f : V →ₗ[K] W) :
    (ExteriorAlgebra.map f).toLinearMap.range =
      (ExteriorAlgebra.map f.range.subtype).toLinearMap.range := by
  have hs : Function.Surjective (ExteriorAlgebra.map f.rangeRestrict) :=
    ExteriorAlgebra.map_surjective_iff.mpr f.surjective_rangeRestrict
  have hc : (ExteriorAlgebra.map f.range.subtype).toLinearMap.comp
      (ExteriorAlgebra.map f.rangeRestrict).toLinearMap =
      (ExteriorAlgebra.map f).toLinearMap := by
    rw [← AlgHom.comp_toLinearMap, ExteriorAlgebra.map_comp_map,
      LinearMap.subtype_comp_rangeRestrict]
  rw [← hc]
  exact LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr hs)

/-- The exterior map on the inclusion of an actual linear-map image is
injective.  No rank equality is assumed. -/
theorem exteriorAlgebra_map_range_subtype_injective (f : V →ₗ[K] W) :
    Function.Injective (ExteriorAlgebra.map f.range.subtype) :=
  ExteriorAlgebra.map_injective_field (Submodule.ker_subtype _)

/-- Full exterior/compound rank formula.  Only the original image needs to be
finite-dimensional; in particular this applies to every map between finite
dimensional vector spaces. -/
theorem exteriorAlgebra_map_finrank_range (f : V →ₗ[K] W)
    [Module.Finite K f.range] :
    Module.finrank K (ExteriorAlgebra.map f).toLinearMap.range =
      2 ^ Module.finrank K f.range := by
  rw [exteriorAlgebra_map_range,
    LinearMap.finrank_range_of_inj (exteriorAlgebra_map_range_subtype_injective f),
    exteriorAlgebra_finrank]

/-- The corresponding degree-by-degree image factorization. -/
theorem exteriorPower_map_range (n : ℕ) (f : V →ₗ[K] W) :
    (exteriorPower.map n f).range = (exteriorPower.map n f.range.subtype).range := by
  have hs : Function.Surjective (exteriorPower.map n f.rangeRestrict) :=
    exteriorPower.map_surjective (n := n) f.surjective_rangeRestrict
  rw [← LinearMap.subtype_comp_rangeRestrict f, exteriorPower.map_comp]
  exact LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr hs)

/-- Each homogeneous compound map has rank the corresponding binomial
coefficient of the rank of the original map. -/
theorem exteriorPower_map_finrank_range (n : ℕ) (f : V →ₗ[K] W)
    [Module.Finite K f.range] :
    Module.finrank K (exteriorPower.map n f).range =
      (Module.finrank K f.range).choose n := by
  rw [exteriorPower_map_range,
    LinearMap.finrank_range_of_inj
      (exteriorPower.map_injective_field (n := n) (Submodule.subtype_injective _)),
    exteriorPower.finrank_eq]

/-- On a homogeneous exterior element, the full subset-basis coordinates of
the same degree are the homogeneous exterior-power coordinates. -/
theorem exteriorAlgebra_basis_repr_homogeneous {I : Type*} [LinearOrder I]
    (b : Module.Basis I K V) (n : ℕ) (x : ⋀[K]^n V)
    (s : Set.powersetCard I n) :
    b.ExteriorAlgebra.repr (x : ExteriorAlgebra K V) (s : Finset I) =
      (b.exteriorPower n).repr x s := by
  rw [Module.Basis.ExteriorAlgebra, Module.Basis.repr_reindex_apply]
  have hs : Set.powersetCard.prodEquiv.symm (s : Finset I) = ⟨n, s⟩ :=
    (Equiv.symm_apply_eq _).mpr rfl
  rw [hs]
  exact DirectSum.IsInternal.collectedBasis_repr_of_mem _ _ x.property

/-- Full subset-basis coordinates of a homogeneous exterior element vanish
at every different degree. -/
theorem exteriorAlgebra_basis_repr_homogeneous_ne {I : Type*} [LinearOrder I]
    (b : Module.Basis I K V) (n : ℕ) (x : ⋀[K]^n V)
    (s : Finset I) (h : n ≠ s.card) :
    b.ExteriorAlgebra.repr (x : ExteriorAlgebra K V) s = 0 := by
  rw [Module.Basis.ExteriorAlgebra, Module.Basis.repr_reindex_apply]
  exact DirectSum.IsInternal.collectedBasis_repr_of_mem_ne _ _ h x.property

section Matrix

variable {I J : Type*} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

/-- The full exterior-compound matrix, in the subset-indexed exterior bases of
the standard coordinate spaces. -/
def exteriorCompoundMatrix (B : Matrix I J K) : Matrix (Finset I) (Finset J) K :=
  LinearMap.toMatrix (Pi.basisFun K J).ExteriorAlgebra
    (Pi.basisFun K I).ExteriorAlgebra (ExteriorAlgebra.map B.mulVecLin).toLinearMap

/-- The full finite-subset-indexed compound matrix has rank `2 ^ rank B`.
This statement has no hypothesis on the rank of the compound matrix. -/
theorem exteriorCompoundMatrix_rank (B : Matrix I J K) :
    (exteriorCompoundMatrix B).rank = 2 ^ B.rank := by
  rw [exteriorCompoundMatrix, Matrix.rank_eq_finrank_range_toLin _
    (Pi.basisFun K I).ExteriorAlgebra (Pi.basisFun K J).ExteriorAlgebra,
    Matrix.toLin_toMatrix, exteriorAlgebra_map_finrank_range]
  rfl

/-- Recovering the rank of a cross matrix from the rank of its full compound
matrix uses injectivity of the powers of two, rather than another rank premise. -/
theorem exteriorCompoundMatrix_rank_eq_two_pow_iff (B : Matrix I J K) (d : ℕ) :
    (exteriorCompoundMatrix B).rank = 2 ^ d ↔ B.rank = d := by
  rw [exteriorCompoundMatrix_rank]
  exact (Nat.pow_right_injective (by decide : 2 ≤ 2)).eq_iff

/-- The rank-two case of the compound rank formula forces rank one in the
cross matrix, as required in the rank-two Gaussian argument. -/
theorem exteriorCompoundMatrix_rank_two_iff (B : Matrix I J K) :
    (exteriorCompoundMatrix B).rank = 2 ↔ B.rank = 1 := by
  simpa using exteriorCompoundMatrix_rank_eq_two_pow_iff B 1

/-- A rank-two cross matrix produces a rank-four full compound matrix. -/
theorem exteriorCompoundMatrix_rank_four_iff (B : Matrix I J K) :
    (exteriorCompoundMatrix B).rank = 4 ↔ B.rank = 2 := by
  simpa using exteriorCompoundMatrix_rank_eq_two_pow_iff B 2

/-- The degree-`n` compound matrix in the increasing-subset bases. -/
def exteriorPowerMatrix (n : ℕ) (B : Matrix I J K) :
    Matrix (Set.powersetCard I n) (Set.powersetCard J n) K :=
  LinearMap.toMatrix ((Pi.basisFun K J).exteriorPower n)
    ((Pi.basisFun K I).exteriorPower n) (exteriorPower.map n B.mulVecLin)

/-- The rank of the `n`th compound matrix is the binomial coefficient of the
rank of the original matrix. -/
theorem exteriorPowerMatrix_rank (n : ℕ) (B : Matrix I J K) :
    (exteriorPowerMatrix n B).rank = B.rank.choose n := by
  rw [exteriorPowerMatrix, Matrix.rank_eq_finrank_range_toLin _
    ((Pi.basisFun K I).exteriorPower n) ((Pi.basisFun K J).exteriorPower n),
    Matrix.toLin_toMatrix, exteriorPower_map_finrank_range]
  rfl

/-- Entries of a homogeneous compound matrix are the corresponding ordinary
minors, with each finite subset enumerated in increasing order. -/
theorem exteriorPowerMatrix_apply (n : ℕ) (B : Matrix I J K)
    (s : Set.powersetCard I n) (t : Set.powersetCard J n) :
    exteriorPowerMatrix n B s t =
      (B.submatrix (Set.powersetCard.ofFinEmbEquiv.symm s)
        (Set.powersetCard.ofFinEmbEquiv.symm t)).det := by
  rw [exteriorPowerMatrix, LinearMap.toMatrix_apply, exteriorPower.basis_apply,
    exteriorPower.map_apply_ιMulti_family, exteriorPower.basis_repr_apply]
  simp only [exteriorPower.ιMulti_family, exteriorPower.ιMultiDual_apply_ιMulti,
    Function.comp_apply, Module.Basis.coord_apply, Pi.basisFun_repr,
    Pi.basisFun_apply, Matrix.mulVecLin_apply, Matrix.mulVec_single_one]
  exact Matrix.det_transpose _

/-- The homogeneous diagonal blocks of the full compound matrix are exactly
the matrices of the individual exterior powers. -/
theorem exteriorCompoundMatrix_apply_same_degree (n : ℕ) (B : Matrix I J K)
    (s : Set.powersetCard I n) (t : Set.powersetCard J n) :
    exteriorCompoundMatrix B (s : Finset I) (t : Finset J) =
      exteriorPowerMatrix n B s t := by
  rw [exteriorCompoundMatrix, LinearMap.toMatrix_apply,
    ExteriorAlgebra.basis_eq_coe_basis, exteriorPowerMatrix, LinearMap.toMatrix_apply]
  change (Pi.basisFun K I).ExteriorAlgebra.repr
    (ExteriorAlgebra.map B.mulVecLin
      (((Pi.basisFun K J).exteriorPower n t) : ExteriorAlgebra K (J → K)))
      (s : Finset I) = _
  rw [← exteriorPower.coe_map, exteriorAlgebra_basis_repr_homogeneous]

/-- Entries between different degrees vanish, so the full matrix is the
direct sum of its ordinary compound blocks. -/
theorem exteriorCompoundMatrix_apply_different_degree (B : Matrix I J K)
    (s : Finset I) (t : Finset J) (h : s.card ≠ t.card) :
    exteriorCompoundMatrix B s t = 0 := by
  let t' : Set.powersetCard J t.card := Set.powersetCard.ofCard rfl
  have ht : (t' : Finset J) = t := rfl
  rw [← ht, exteriorCompoundMatrix, LinearMap.toMatrix_apply,
    ExteriorAlgebra.basis_eq_coe_basis]
  change (Pi.basisFun K I).ExteriorAlgebra.repr
    (ExteriorAlgebra.map B.mulVecLin
      (((Pi.basisFun K J).exteriorPower t.card t') : ExteriorAlgebra K (J → K))) s = 0
  rw [← exteriorPower.coe_map]
  exact exteriorAlgebra_basis_repr_homogeneous_ne _ _ _ _ h.symm

end Matrix

end

end MatchgateWidth
