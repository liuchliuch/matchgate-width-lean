import MatchgateWidth.ExactMatchgateLinear
import MatchgateWidth.RankTwoCanonicalOutput
import MatchgateWidth.FlagTensorNormalFormDisk
import MatchgateWidth.UniformBooleanPlaneDisk

/-! # Exact source rank-two decoding and flag normal form

These statements use the geometric exact-matchgate class with a certified
ordered exterior access. Every tensor hypothesis is a statement about its
actual flattening supports. The common base, plane endpoint basis and decoder
are fixed before the tensor's arity is quantified. No factorization is assumed.
-/
namespace MatchgateWidth
noncomputable section

/-- The even or odd Boolean coordinate subspace, in the original wire order. -/
def booleanParitySubspace (t b : ℕ) : Submodule ℂ (BooleanTable t ℂ) where
  carrier := {u | ∀ y, booleanParity y ≠ b → u y=0}
  zero_mem' := by simp
  add_mem' := by intro u v hu hv y hy; simp [hu y hy, hv y hy]
  smul_mem' := by intro a u hu y hy; simp [hu y hy]

/-- The source pullback parity endpoint, defined independently of any chosen
basis or tensor normal form. -/
def primitiveParityEndpoint {A : Type*} [Fintype A] {t : ℕ}
    (M : Matrix A (BooleanInput t) ℂ) (P : Submodule ℂ (A → ℂ)) (b : ℕ) :
    Submodule ℂ (A → ℂ) := P ⊓ (booleanParitySubspace t b).comap M.transpose.mulVecLin

/-- Two opposite homogeneous generators have precisely their displayed
coordinate lines as parity endpoints. -/
theorem span_pair_parity_endpoint {t b c : ℕ} (hbc : b ≠ c)
    (u v : BooleanTable t ℂ) (hv : v ≠ 0)
    (hupar : u ∈ booleanParitySubspace t b) (hvpar : v ∈ booleanParitySubspace t c) :
    Submodule.span ℂ ({u,v} : Set (BooleanTable t ℂ)) ⊓ booleanParitySubspace t b =
      Submodule.span ℂ {u} := by
  classical
  apply le_antisymm
  · intro w hw
    obtain ⟨a,d,heq⟩ := Submodule.mem_span_pair.mp hw.1
    obtain ⟨y,hy⟩ : ∃ y, v y ≠ 0 := by
      by_contra h
      push Not at h
      exact hv (funext h)
    have hyc : booleanParity y=c := by
      by_contra hn
      exact hy (hvpar y hn)
    have hyb : booleanParity y≠b := by rw [hyc]; exact Ne.symm hbc
    have hd : d=0 := by
      have hh := congrFun heq y
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hupar y hyb,
        mul_zero, zero_add, hw.2 y hyb] at hh
      exact (mul_eq_zero.mp hh).resolve_right hy
    rw [hd, zero_smul, add_zero] at heq
    exact Submodule.mem_span_singleton.mpr ⟨a,heq⟩
  · apply Submodule.span_le.mpr
    intro w hw
    rcases Set.mem_singleton_iff.mp hw with rfl
    exact ⟨Submodule.subset_span (Set.mem_insert _ _),hupar⟩

/-- Pullback endpoints really are the even and odd lines of the primitive
plane; this derives their identities from parity and injectivity. -/
theorem primitive_parity_endpoint_eq_span {t : ℕ}
    (M : Matrix (Fin 3) (BooleanInput t) ℂ)
    (hM : Function.Injective M.transpose.mulVecLin)
    (P : Submodule ℂ (Fin 3 → ℂ))
    (E : Matrix (BooleanInput 1) (Fin 3) ℂ)
    (hEP : Submodule.span ℂ (Set.range E.row) = P)
    (h₀ : (E*M).row (fun _ => 0) ≠ 0) (h₁ : (E*M).row (fun _ => 1) ≠ 0)
    (hp₀ : ∀ y, booleanParity y ≠ 0 → (E*M) (fun _ => 0) y = 0)
    (hp₁ : ∀ y, booleanParity y = 0 → (E*M) (fun _ => 1) y = 0) :
    primitiveParityEndpoint M P 0 = Submodule.span ℂ {E.row (fun _ => 0)} ∧
    primitiveParityEndpoint M P 1 = Submodule.span ℂ {E.row (fun _ => 1)} := by
  have hmap : P.map M.transpose.mulVecLin = orderedRowSpace (E*M) := by
    rw [← hEP, span_rows_map_transpose]
    rfl
  have hp₁' : (E*M).row (fun _ => 1) ∈ booleanParitySubspace t 1 := by
    intro y hy
    apply hp₁
    have := booleanParity_lt_two y
    omega
  have hspan0 : orderedRowSpace (E*M) ⊓ booleanParitySubspace t 0 =
      Submodule.span ℂ {(E*M).row (fun _ => 0)} := by
    rw [orderedRowSpace_one_input]
    exact span_pair_parity_endpoint (by decide) _ _ h₁ hp₀ hp₁'
  have hspan1 : orderedRowSpace (E*M) ⊓ booleanParitySubspace t 1 =
      Submodule.span ℂ {(E*M).row (fun _ => 1)} := by
    rw [orderedRowSpace_one_input, Set.pair_comm]
    exact span_pair_parity_endpoint (by decide) _ _ h₀ hp₁' hp₀
  have hrow (a : BooleanInput 1) : M.transpose.mulVecLin (E.row a) = (E*M).row a := by
    rw [transpose_mulVecLin_eq_unaryTransform]
    rfl
  have hgen (a : BooleanInput 1) : E.row a ∈ P := by
    rw [← hEP]
    exact Submodule.subset_span ⟨a,rfl⟩
  have hgeneral (b : ℕ) (a : BooleanInput 1)
      (he : orderedRowSpace (E*M) ⊓ booleanParitySubspace t b = Submodule.span ℂ {(E*M).row a}) :
      primitiveParityEndpoint M P b = Submodule.span ℂ {E.row a} := by
    apply le_antisymm
    · intro u hu
      have hm : M.transpose.mulVecLin u ∈ orderedRowSpace (E*M) ⊓ booleanParitySubspace t b :=
        ⟨hmap ▸ ⟨u,hu.1,rfl⟩,hu.2⟩
      rw [he] at hm
      obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp hm
      apply Submodule.mem_span_singleton.mpr
      refine ⟨c,hM ?_⟩
      rw [map_smul,hrow]
      exact hc
    · apply Submodule.span_le.mpr
      intro u hu
      rcases Set.mem_singleton_iff.mp hu with rfl
      refine ⟨hgen a,?_⟩
      change M.transpose.mulVecLin (E.row a) ∈ booleanParitySubspace t b
      rw [hrow]
      have hh : (E*M).row a ∈ orderedRowSpace (E*M) ⊓ booleanParitySubspace t b := by
        rw [he]
        exact Submodule.subset_span (Set.mem_singleton _)
      exact hh.2
  exact ⟨hgeneral 0 _ hspan0,hgeneral 1 _ hspan1⟩

/-- Source Lemma 10.8. The chosen generators are the even and odd endpoint
rows of `Q`. One square invertible exact output transformation sends them to
`e_(0^t)` and `e_(10^(t-1))`, literally. The final two clauses quantify all
arities, including zero, and recover the same coefficients without rescaling. -/
theorem exact_rank_two_block_decoding {r t : ℕ}
    (B : Matrix (BooleanInput r) (BooleanInput t) ℂ)
    (hB : ExactMatchgateMatrix B) (hr : B.rank = 2) :
    ∃ (Q : Matrix (BooleanInput 1) (BooleanInput t) ℂ)
      (D : Matrix (BooleanInput t) (BooleanInput 1) ℂ)
      (ht : 0<t) (C Cinv : Matrix (BooleanInput t) (BooleanInput t) ℂ),
      ExactMatchgateMatrix Q ∧ ExactMatchgateMatrix D ∧ Q*D=1 ∧
      Q.rank=2 ∧ orderedRowSpace Q = orderedRowSpace B ∧
      Q.row (fun _ => 0) ≠ 0 ∧ Q.row (fun _ => 1) ≠ 0 ∧
      (∀ y, booleanParity y ≠ 0 → Q (fun _ => 0) y = 0) ∧
      (∀ y, booleanParity y = 0 → Q (fun _ => 1) y = 0) ∧
      ExactMatchgateMatrix C ∧ ExactMatchgateMatrix Cinv ∧ C*Cinv=1 ∧ Cinv*C=1 ∧
      Matrix.vecMul (Q.row (fun _ => 0)) C = outputVacuum ∧
      Matrix.vecMul (Q.row (fun _ => 1)) C = Pi.single (singletonWord ⟨0,ht⟩) 1 ∧
      (∀ m (h : BooleanTable m ℂ),
        ExactMatchgate (leftBooleanLift Q m (fun x => h (fun i => x i 0))) →
        ExactMatchgate h) ∧
      (∀ m (G : BooleanTable (m*t) ℂ), ExactMatchgate G →
        (∀ j, columnSupport (portFlatten (fun x => G (flattenBooleanBlocks x)) j) ≤
          orderedRowSpace B) →
        ExactMatchgate (booleanPlanePullback D m G) ∧
        leftBooleanLift Q m (fun x => booleanPlanePullback D m G (fun i => x i 0)) = G) := by
  obtain ⟨Q,D,hQ,hD,hQD,hrQ,hspace,h₀,h₁,hp₀,hp₁⟩ :=
    exists_even_odd_boolean_plane_encoder hB.identities hr
  obtain ⟨ht,C,Cinv,hC,hCinv,hCC,hCiC,hg₀,hg₁⟩ := hQ.one_input_canonical_output hrQ
  refine ⟨Q,D,ht,C,Cinv,hQ.exactMatrix,hD.exactMatrix,hQD,hrQ,hspace,h₀,h₁,hp₀,hp₁,
    hC.exactMatrix,hCinv.exactMatrix,hCC,hCiC,hg₀,hg₁,?_,?_⟩
  · intro m h hh
    exact (booleanMatchgateIdentities_of_plane_lift Q D hD hQD m h hh.matchgateIdentities).exactMatchgate
  · intro m G hG hs
    exact ⟨(hD.booleanPlanePullback m hG.matchgateIdentities).exactMatchgate,
      booleanPlanePullback_reconstruct Q D hQD m G (by simpa only [hspace] using hs)⟩

/-- Source Lemma 10.9, first (all-rays) alternative. The actual line-support
hypotheses imply complete decomposability; every factor has an exact pure lift. -/
theorem exact_all_line_supports_decomposition {n t : ℕ}
    (M : Matrix (Fin 3) (BooleanInput t) ℂ) (hM : M.rank=3)
    (T : (Fin n → Fin 3) → ℂ) (hne : T ≠ 0)
    (hT : ExactMatchgate (leftBooleanLift M n T))
    (hline : ∀ j, Module.finrank ℂ (columnSupport (portFlatten T j)) = 1) :
    ∃ (c : ℂ) (q : Fin n → Fin 3 → ℂ), c ≠ 0 ∧ (∀ j, q j ≠ 0) ∧
      (∀ x, T x = c * ∏ j, q j (x j)) ∧
      (∀ j, ExactMatchgate (unaryTransform M (q j))) := by
  obtain ⟨c,q,hc,hq,hfac,hpure⟩ := all_line_supports_pure_decomposition M
    (transpose_injective_of_rank_eq_card M (by simpa using hM)) T hne hT.matchgateIdentities hline
  exact ⟨c,q,hc,hq,hfac,fun j => (hpure j).exactMatchgate⟩

/-- Source Lemma 10.9, uniform flag alternative. The single even/odd endpoint
basis is chosen from `M,P,B` before the transverse ray, arity or tensor. For a
fixed nonzero transverse vector `r`, every stripped factor is literally one of
these three fixed vectors. The retained ports are canonically enumerated in
increasing original order; the expansion is `flagTensor`'s actual coefficient
sum. Both nullary cores and the impossibility of unary cores are explicit. -/
theorem exact_uniform_flag_normal_form {s t : ℕ}
    (M : Matrix (Fin 3) (BooleanInput t) ℂ) (hM : M.rank=3)
    (P : Submodule ℂ (Fin 3 → ℂ))
    (B : Matrix (BooleanInput s) (BooleanInput t) ℂ)
    (hB : ExactMatchgateMatrix B) (hrB : B.rank=2)
    (hspace : orderedRowSpace B = P.map M.transpose.mulVecLin) :
    ∃ (E : Matrix (BooleanInput 1) (Fin 3) ℂ)
      (D : Matrix (BooleanInput t) (BooleanInput 1) ℂ),
      Submodule.span ℂ (Set.range E.row) = P ∧
      ExactMatchgateMatrix (E*M) ∧ ExactMatchgateMatrix D ∧ (E*M)*D=1 ∧
      (E*M).rank=2 ∧
      (E*M).row (fun _ => 0) ≠ 0 ∧ (E*M).row (fun _ => 1) ≠ 0 ∧
      (∀ y, booleanParity y ≠ 0 → (E*M) (fun _ => 0) y = 0) ∧
      (∀ y, booleanParity y = 0 → (E*M) (fun _ => 1) y = 0) ∧
      primitiveParityEndpoint M P 0 = Submodule.span ℂ {E.row (fun _ => 0)} ∧
      primitiveParityEndpoint M P 1 = Submodule.span ℂ {E.row (fun _ => 1)} ∧
      (∃ (ht : 0<t) (C Cinv : Matrix (BooleanInput t) (BooleanInput t) ℂ),
        ExactMatchgateMatrix C ∧ ExactMatchgateMatrix Cinv ∧ C*Cinv=1 ∧ Cinv*C=1 ∧
        Matrix.vecMul ((E*M).row (fun _ => 0)) C = outputVacuum ∧
        Matrix.vecMul ((E*M).row (fun _ => 1)) C = Pi.single (singletonWord ⟨0,ht⟩) 1) ∧
      ∀ (r : Fin 3 → ℂ), r ≠ 0 → r ∉ P →
      ∀ (n : ℕ) (T : (Fin n → Fin 3) → ℂ), T ≠ 0 →
        ExactMatchgate (leftBooleanLift M n T) →
        (∀ j, columnSupport (portFlatten T j) = P ∨
          columnSupport (portFlatten T j) = primitiveParityEndpoint M P 0 ∨
          columnSupport (portFlatten T j) = primitiveParityEndpoint M P 1 ∨
          columnSupport (portFlatten T j) = Submodule.span ℂ {r}) →
        let I := planeSupportedPorts P T
        let e := (planePortEmbedding P T).toEmbedding
        let q := fun j => fixedFlagRay E r (columnSupport (portFlatten T j))
        ∃ h : BooleanTable I.card ℂ, ExactMatchgate h ∧ h ≠ 0 ∧
          StrictMono e ∧ T = flagTensor E e q h ∧
          (∀ i, Module.finrank ℂ (columnSupport (portFlatten h i)) = 2) ∧
          (I.card = 0 ∨ 2 ≤ I.card) ∧
          (∀ j, j ∉ Set.range e → q j ≠ 0 ∧
            columnSupport (portFlatten T j) = Submodule.span ℂ {q j} ∧
            ExactMatchgate (unaryTransform M (q j))) ∧
          ExactMatchgate (unaryTransform M (E.row (fun _ => 0))) ∧
          ExactMatchgate (unaryTransform M (E.row (fun _ => 1))) := by
  have hMinj := transpose_injective_of_rank_eq_card M (by simpa using hM)
  obtain ⟨E,D,hEP,hEM,hD,hED,hr,h₀,h₁,hp₀,hp₁⟩ :=
    exists_uniform_even_odd_flag_basis M hMinj P B hB.identities hrB hspace
  obtain ⟨he0,he1⟩ := primitive_parity_endpoint_eq_span M hMinj P E hEP h₀ h₁ hp₀ hp₁
  refine ⟨E,D,hEP,hEM.exactMatrix,hD.exactMatrix,hED,hr,h₀,h₁,hp₀,hp₁,he0,he1,?_,?_⟩
  · obtain ⟨ht,C,Cinv,hC,hCi,hCCi,hCiC,hv,hs⟩ := hEM.one_input_canonical_output hr
    exact ⟨ht,C,Cinv,hC.exactMatrix,hCi.exactMatrix,hCCi,hCiC,hv,hs⟩
  · intro r hr _ n T hne hT hflag
    have hf : ∀ j, columnSupport (portFlatten T j) = Submodule.span ℂ (Set.range E.row) ∨
        columnSupport (portFlatten T j) = Submodule.span ℂ {E.row (fun _ => 0)} ∨
        columnSupport (portFlatten T j) = Submodule.span ℂ {E.row (fun _ => 1)} ∨
        columnSupport (portFlatten T j) = Submodule.span ℂ {r} := by
      simpa only [hEP,he0,he1] using hflag
    have hh := fixed_adapted_flag_normal_form M hMinj E hEM D hD hED r hr
      T hne hT.matchgateIdentities hf
    dsimp only at hh
    rw [hEP] at hh
    obtain ⟨h,hmg,hne,hfac,hranks,harity,hrays,heven,hodd⟩ := hh
    refine ⟨h,hmg.exactMatchgate,hne,(planePortEmbedding P T).strictMono,
      hfac,hranks,harity,?_,heven.exactMatchgate,hodd.exactMatchgate⟩
    intro j hj
    exact ⟨(hrays j hj).1,(hrays j hj).2.1,(hrays j hj).2.2.exactMatchgate⟩


/-- The geometric class includes every zero tensor, at every arity. -/
theorem exactMatchgate_zero (n : ℕ) : ExactMatchgate (0 : BooleanTable n ℂ) := by
  apply BooleanMatchgateIdentities.exactMatchgate
  simp [BooleanMatchgateIdentities, MatchgateIdentities, matchgateSum]

/-- The source convention `MG₀ = ℂ`, proved in the geometric class. -/
theorem exactMatchgate_nullary (h : BooleanTable 0 ℂ) : ExactMatchgate h := by
  apply BooleanMatchgateIdentities.exactMatchgate
  intro α β
  have ha : α=∅ := Finset.eq_empty_of_isEmpty α
  have hb : β=∅ := Finset.eq_empty_of_isEmpty β
  simp [ha,hb,matchgateSum]

end
end MatchgateWidth
