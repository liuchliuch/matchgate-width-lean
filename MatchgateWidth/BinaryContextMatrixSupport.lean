import MatchgateWidth.BinaryContextGeometry

/-! # Pulling binary mode supports back to fixed coordinates -/
namespace MatchgateWidth
noncomputable section
set_option maxHeartbeats 800000

theorem matrix_rows_zero_of_image_coordinate {t : ℕ}
    (M : Matrix (Fin 3) (BooleanInput t) ℂ) (hM : M.rank=3)
    (A : Matrix (Fin 3) (Fin 3) ℂ) (j : Fin 3)
    (h : (Submodule.span ℂ (Set.range A.row)).map M.transpose.mulVecLin ≤
      Submodule.span ℂ {M.row j}) :
    ∀ i k, k ≠ j → A i k=0 := by
  have hi := transpose_injective_of_rank_eq_card M (by simpa using hM)
  intro i k hk
  have hh := h ⟨A.row i,Submodule.subset_span ⟨i,rfl⟩,rfl⟩
  obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp hh
  have he : c • (Pi.single j (1 : ℂ) : Fin 3 → ℂ) = A.row i := by
    apply hi
    simpa only [map_smul,transpose_mulVecLin_single_row] using hc
  have he' := congrFun he k
  simpa [hk] using he'.symm

theorem matrix_rows_zero_third_of_image_plane {t : ℕ}
    (M : Matrix (Fin 3) (BooleanInput t) ℂ) (hM : M.rank=3)
    (A : Matrix (Fin 3) (Fin 3) ℂ)
    (h : (Submodule.span ℂ (Set.range A.row)).map M.transpose.mulVecLin ≤
      Submodule.span ℂ {M.row 0,M.row 1}) : ∀ i, A i 2=0 := by
  have hi := transpose_injective_of_rank_eq_card M (by simpa using hM)
  intro i
  have hh := h ⟨A.row i,Submodule.subset_span ⟨i,rfl⟩,rfl⟩
  obtain ⟨a,b,hc⟩ := Submodule.mem_span_pair.mp hh
  have he : a • (Pi.single 0 (1 : ℂ) : Fin 3 → ℂ) + b • Pi.single 1 1 = A.row i := by
    apply hi
    simpa only [map_add,map_smul,transpose_mulVecLin_single_row] using hc
  have he' := congrFun he 2
  simpa using he'.symm

theorem partialMonomial_of_single_coordinate
    (A : Matrix (Fin 3) (Fin 3) ℂ) (a b : Fin 3)
    (hr : ∀ i j, j ≠ b → A i j=0) (hc : ∀ i j, i ≠ a → A i j=0) :
    PartialMonomial A := by
  constructor
  · intro i j k hj hk
    have hjb : j=b := by by_contra hn; exact hj (hr i j hn)
    have hkb : k=b := by by_contra hn; exact hk (hr i k hn)
    exact hjb.trans hkb.symm
  · intro i j k hi hj
    have hia : i=a := by by_contra hn; exact hi (hc i k hn)
    have hja : j=a := by by_contra hn; exact hj (hc j k hn)
    exact hia.trans hja.symm

@[simp] theorem partialMonomial_zero : PartialMonomial (0 : Matrix (Fin 3) (Fin 3) ℂ) := by
  constructor <;> simp

end
end MatchgateWidth
