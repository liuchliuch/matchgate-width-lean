import MatchgateWidth.BinaryContextFixedBasis

/-! # Constructing the fixed adapted basis from the realized plane and ray -/
namespace MatchgateWidth
noncomputable section
set_option maxHeartbeats 800000

/-- A realized rank-two plane and a transverse exact ray construct all adapted
coordinate data, before any binary context is selected. -/
theorem exists_binary_adapted_basis {s t : ℕ}
    (M : Matrix (Fin 3) (BooleanInput t) ℂ) (hM : M.rank=3)
    (P : Submodule ℂ (Fin 3 → ℂ))
    (B : Matrix (BooleanInput s) (BooleanInput t) ℂ)
    (hB : ExactMatchgateMatrix B) (hrB : B.rank=2)
    (hspace : orderedRowSpace B=P.map M.transpose.mulVecLin)
    (r : Fin 3 → ℂ) (hrP : r ∉ P) (hr : ExactMatchgate (unaryTransform M r)) :
    ∃ (T : Matrix (Fin 3) (Fin 3) ℂ) (Q : Matrix (BooleanInput 1) (BooleanInput t) ℂ),
      T.rank=3 ∧ T.row 2=r ∧
      primitiveParityEndpoint M P 0=Submodule.span ℂ {T.row 0} ∧
      primitiveParityEndpoint M P 1=Submodule.span ℂ {T.row 1} ∧
      BinaryAdaptedRows (T*M) Q := by
  classical
  have hMinj := transpose_injective_of_rank_eq_card M (by simpa using hM)
  obtain ⟨E,D,hEP,hEM,hD,hED,hEMr,h0,h1,hp0,hp1⟩ :=
    exists_uniform_even_odd_flag_basis M hMinj P B hB.identities hrB hspace
  have hPr : Module.finrank ℂ P=2 := by
    rw [← finrank_map_transpose_eq M hMinj P,← hspace]
    change Module.finrank ℂ (Submodule.span ℂ (Set.range B.row))=2
    rw [← Matrix.rank_eq_finrank_span_row,hrB]
  let T : Matrix (Fin 3) (Fin 3) ℂ := ![E.row (fun _ => 0),E.row (fun _ => 1),r]
  have hEset : Set.range E.row={E.row (fun _ => 0),E.row (fun _ => 1)} := by
    ext u
    constructor
    · rintro ⟨x,rfl⟩
      rcases booleanInput_one_cases x with rfl | rfl <;> simp
    · rintro (rfl | rfl)
      · exact ⟨_,rfl⟩
      · exact ⟨_,rfl⟩
  have hTset : Set.range T.row=Set.range E.row ∪ {r} := by
    rw [hEset]
    ext u
    constructor
    · rintro ⟨i,rfl⟩
      fin_cases i
      · exact Or.inl (Or.inl rfl)
      · exact Or.inl (Or.inr rfl)
      · exact Or.inr rfl
    · rintro ((rfl | rfl) | rfl)
      · exact ⟨0,rfl⟩
      · exact ⟨1,rfl⟩
      · exact ⟨2,rfl⟩
  have hTr : T.rank=3 := by
    rw [Matrix.rank_eq_finrank_span_row,hTset,Submodule.span_union,hEP,
      Submodule.finrank_sup_span_singleton hrP,hPr]
  have hT0 : (T*M).row 0=(E*M).row (fun _ => 0) := by
    rfl
  have hT1 : (T*M).row 1=(E*M).row (fun _ => 1) := by
    rfl
  have hT2 : (T*M).row 2=unaryTransform M r := by
    rfl
  obtain ⟨he0,he1⟩ := primitive_parity_endpoint_eq_span M hMinj P E hEP h0 h1 hp0 hp1
  refine ⟨T,E*M,hTr,rfl,he0,he1,?_⟩
  refine ⟨hEM.exactMatrix,hEMr,hT0.symm,hT1.symm,?_,?_,?_⟩
  · intro y hy
    exact congrFun hT0 y ▸ hp0 y hy
  · intro y hy
    have hz : booleanParity y=0 := by have := booleanParity_lt_two y; omega
    exact congrFun hT1 y ▸ hp1 y hz
  · rwa [hT2]

/-- Source Corollary 10.10, from the actual plane-plus-ray data alone. The
output fixes the endpoint coordinate basis once, uniformly over all binary
contexts, and returns covers for the original common base. -/
theorem exact_binary_context_alternative_from_plane_ray {s t : ℕ}
    (M : Matrix (Fin 3) (BooleanInput t) ℂ) (hM : M.rank=3)
    (P : Submodule ℂ (Fin 3 → ℂ))
    (B : Matrix (BooleanInput s) (BooleanInput t) ℂ)
    (hB : ExactMatchgateMatrix B) (hrB : B.rank=2)
    (hspace : orderedRowSpace B=P.map M.transpose.mulVecLin)
    (r : Fin 3 → ℂ) (hrP : r ∉ P) (hr : ExactMatchgate (unaryTransform M r)) :
    ∃ T : Matrix (Fin 3) (Fin 3) ℂ, T.rank=3 ∧ T.row 2=r ∧
      primitiveParityEndpoint M P 0=Submodule.span ℂ {T.row 0} ∧
      primitiveParityEndpoint M P 1=Submodule.span ℂ {T.row 1} ∧
      (BinarySmallCover M ∨ ∀ A : Matrix (Fin 3) (Fin 3) ℂ,
        ExactMatchgate (leftBooleanLift M 2 (leftTransform T (binaryDomainTensor A))) →
        PartialMonomial A) := by
  obtain ⟨T,Q,hT,hTr,he0,he1,d⟩ := exists_binary_adapted_basis M hM P B hB hrB hspace r hrP hr
  exact ⟨T,hT,hTr,he0,he1,exact_binary_context_alternative_fixed_basis M hM T hT Q d⟩

end
end MatchgateWidth
