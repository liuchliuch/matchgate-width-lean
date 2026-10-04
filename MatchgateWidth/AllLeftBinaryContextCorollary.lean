import MatchgateWidth.BinaryContextCorollary
import MatchgateWidth.AllLeftSupportExtraction

/-! # Binary-context alternative for the actual all-left closure
This conditional wrapper isolates the general exact ordered gadget-lifting
theorem, subsequently proved in AllLeftSubstitutionRouting. No port-deficiency or connection-prime
hypothesis is added. Supports and binary contexts are actual connected
ordered-planar all-left gadgets and their literal boundary coefficients.
-/
namespace MatchgateWidth
noncomputable section
open scoped Classical
set_option maxHeartbeats 800000

theorem allLeft_binary_context_corollary_of_exactLifting
    {S : LabelledShape} {t : ℕ} (p : LabelledCommonPresentation S (Fin 3) t)
    (hM : p.baseMatrix.rank=3) (hlift : AllLeftExactLifting p)
    (P L : Submodule ℂ (Fin 3 → ℂ))
    (hP : P ∈ allLeftRealizedSupports p.language 2)
    (hL : L ∈ allLeftRealizedSupports p.language 1) (hLP : ¬ L ≤ P) :
    ∃ T N : Matrix (Fin 3) (Fin 3) ℂ,
      T.rank=3 ∧ T*N=1 ∧ N*T=1 ∧ Submodule.span ℂ {T.row 2}=L ∧
      primitiveParityEndpoint p.baseMatrix P 0=Submodule.span ℂ {T.row 0} ∧
      primitiveParityEndpoint p.baseMatrix P 1=Submodule.span ℂ {T.row 1} ∧
      (BinarySmallCover p.baseMatrix ∨
        ∀ a b c (I : AllLeftGadget S a b c 2), I.Connected → Nonempty I.OrderedPlanar →
          PartialMonomial (binaryContextCoordinates N (I.value p.language))) ∧
      (∀ a b c (I : AllLeftGadget S a b c 2), I.Connected → Nonempty I.OrderedPlanar →
        ¬ PartialMonomial (binaryContextCoordinates N (I.value p.language)) →
        ∃ w ≤ 3, ∃ q : LabelledCommonPresentation S (Fin 3) w,
          q.left=p.left ∧ q.language=p.language ∧ ExactlyLabelledEquivalent p.language q.language) := by
  obtain ⟨a,b,c,n,I,hconn,hplan,hne,j,hPs,hdP⟩ := hP
  obtain ⟨B,hB,hrow⟩ := exact_lift_block_rowSpace p.baseMatrix hM
    (I.value p.language) (hlift a b c n I hconn hplan) j
  have hspace : orderedRowSpace B=P.map p.baseMatrix.transpose.mulVecLin := by
    simpa only [hPs] using hrow
  have hBr : B.rank=2 := by
    rw [Matrix.rank_eq_finrank_span_row]
    change Module.finrank ℂ (orderedRowSpace B)=2
    rw [hspace,finrank_map_transpose_eq p.baseMatrix
      (transpose_injective_of_rank_eq_card p.baseMatrix (by simpa using hM))]
    exact hdP
  obtain ⟨a',b',c',n',J,hconn',hplan',hne',j',hLs,hdL⟩ := hL
  obtain ⟨r,hr,hLr⟩ := exists_generator_of_finrank_one L hdL
  have hrP : r ∉ P := by
    intro hh
    apply hLP
    rw [hLr]
    exact Submodule.span_le.mpr (by simpa using hh)
  have hrmg := transformed_ray_is_pure p.baseMatrix
    (transpose_injective_of_rank_eq_card p.baseMatrix (by simpa using hM))
    (J.value p.language) hne' (hlift a' b' c' n' J hconn' hplan').matchgateIdentities
    j' r (by rw [← hLs,hLr])
  obtain ⟨T,N,hT,hTN,hNT,hTr,he0,he1,halt,hwidth⟩ :=
    p.binary_context_corollary hM P B hB hBr hspace r hrP hrmg.exactMatchgate
  refine ⟨T,N,hT,hTN,hNT,?_,he0,he1,?_,?_⟩
  · rw [hTr,← hLr]
  · rcases halt with hc | hm
    · exact Or.inl hc
    · exact Or.inr (fun a b c I hconn hplan => hm (I.value p.language)
        (hlift a b c 2 I hconn hplan))
  · intro a b c I hconn hplan hn
    exact hwidth (I.value p.language) (hlift a b c 2 I hconn hplan) hn

end
end MatchgateWidth
