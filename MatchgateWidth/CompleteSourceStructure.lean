import MatchgateWidth.AllLeftSubstitutionRouting
import MatchgateWidth.AllLeftStructuralTrichotomy
import MatchgateWidth.AllLeftBinaryContextCorollary

/-!
# Unconditional source support structure and exact collapse

The actual ordered all-left lifting theorem discharges the last geometric
dependency of the source structural results. These wrappers preserve the
previous conclusions and all their other hypotheses. Supports still range over
actual connected ordered-planar gadgets. Compressions use one common base and
preserve the original labels, arities, port order, zero tensors, and nullaries.

The source Theorem 3.3 structural alternatives are proved here. Its separate
unbounded-family assertion is joined with the integer construction elsewhere.
-/
namespace MatchgateWidth
noncomputable section
open scoped Classical

/-- Unconditional connection-prime collapse (source Theorem 10.7). This
stronger formulation only needs full base rank and actual connection-primality;
no deficiency or essentiality premise is needed after those are supplied. -/
theorem allLeft_connectionPrime_compression {S : LabelledShape} {t : ℕ}
    (p : LabelledCommonPresentation S (Fin 3) t) (hM : p.baseMatrix.rank = 3)
    (hprime : AllLeftConnectionPrime p) :
    ∃ r ≤ 3, ∃ H : Matrix (BooleanInput r) (BooleanInput t) ℂ,
      ExactMatchgateMatrix H ∧ H.rank = 2 ^ r ∧ H.rank ≤ 8 ∧
      ∃ q : LabelledCommonPresentation S (Fin 3) r,
        p.baseMatrix = q.baseMatrix * H ∧ q.left = p.left ∧
        q.language = p.language ∧ ExactlyLabelledEquivalent p.language q.language :=
  allLeft_connectionPrime_compression_of_exactLifting p hM
    (allLeftExactLifting_of_full_rank p hM) hprime

/-- Two distinct actual realized planes give a rank-four common exact cover
and a width-two presentation, on exactly the same labelled language. -/
theorem allLeft_two_planes_compression {S : LabelledShape} {t : ℕ}
    (p : LabelledCommonPresentation S (Fin 3) t) (hM : p.baseMatrix.rank = 3)
    {P Q : Submodule ℂ (Fin 3 → ℂ)}
    (hP : P ∈ allLeftRealizedSupports p.language 2)
    (hQ : Q ∈ allLeftRealizedSupports p.language 2) (hne : P ≠ Q) :
    ∃ H : Matrix (BooleanInput 2) (BooleanInput t) ℂ,
      ExactMatchgateMatrix H ∧ H.rank = 4 ∧
      ∃ q : LabelledCommonPresentation S (Fin 3) 2,
        p.baseMatrix = q.baseMatrix * H ∧ q.left = p.left ∧
        q.language = p.language ∧ ExactlyLabelledEquivalent p.language q.language :=
  allLeft_two_planes_compression_of_exactLifting p hM
    (allLeftExactLifting_of_full_rank p hM) hP hQ hne

/-- Source Theorem 10.7 with its displayed primitive hypotheses and its
two-distinct-planes refinement in one statement. -/
theorem source_connection_prime_collapse {S : LabelledShape} {t : ℕ}
    (p : LabelledCommonPresentation S (Fin 3) t) (hM : p.baseMatrix.rank = 3)
    (_hleft : LeftPortDeficient p.language) (_hright : RightPortDeficient p.language)
    (_hessright : RightSupportEssential p.language) (hprime : AllLeftConnectionPrime p) :
    AllLeftWidthThreeCompression p ∧
      ∀ P Q : Submodule ℂ (Fin 3 → ℂ),
        P ∈ allLeftRealizedSupports p.language 2 →
        Q ∈ allLeftRealizedSupports p.language 2 → P ≠ Q →
        ∃ H : Matrix (BooleanInput 2) (BooleanInput t) ℂ,
          ExactMatchgateMatrix H ∧ H.rank = 4 ∧
          ∃ q : LabelledCommonPresentation S (Fin 3) 2,
            p.baseMatrix = q.baseMatrix * H ∧ q.left = p.left ∧
            q.language = p.language ∧ ExactlyLabelledEquivalent p.language q.language :=
  ⟨allLeft_connectionPrime_compression p hM hprime,
    fun _ _ hP hQ hne => allLeft_two_planes_compression p hM hP hQ hne⟩

/-- The actual ray-separable closure has complete pure-ray factorization at
every arity, with the empty product giving the nullary scalar case. -/
theorem allLeft_ray_normal_form {S : LabelledShape} {t : ℕ}
    (p : LabelledCommonPresentation S (Fin 3) t) (hM : p.baseMatrix.rank = 3)
    (hdef : LeftPortDeficient p.language)
    (hempty : allLeftRealizedSupports p.language 2 = ∅) : AllLeftRayNormalForm p :=
  allLeft_ray_normal_form_of_exactLifting p hM hdef
    (allLeftExactLifting_of_full_rank p hM) hempty

/-- One fixed endpoint encoder and transverse ray work for every actual
all-left boundary tensor of a monomial flag, including the nullary case. -/
theorem allLeft_flag_normal_form {S : LabelledShape} {t : ℕ}
    (p : LabelledCommonPresentation S (Fin 3) t) (hM : p.baseMatrix.rank = 3)
    (hdef : LeftPortDeficient p.language)
    {P L : Submodule ℂ (Fin 3 → ℂ)} (hflag : AllLeftMonomialFlag p P L) :
    AllLeftFlagNormalForm p P L :=
  allLeft_flag_normal_form_of_exactLifting p hM hdef
    (allLeftExactLifting_of_full_rank p hM) hflag

/-- The mutually exclusive and exhaustive structural alternatives of source
Theorem 3.3 under its exact full-rank, bi-essential, port-deficient hypotheses.
The two-plane refinement is `allLeft_two_planes_compression`. -/
theorem allLeft_structural_trichotomy {S : LabelledShape} {t : ℕ}
    (p : LabelledCommonPresentation S (Fin 3) t) (hM : p.baseMatrix.rank = 3)
    (hleft : LeftPortDeficient p.language) (hright : RightPortDeficient p.language)
    (hessleft : LeftSupportEssential p.language) (hessright : RightSupportEssential p.language) :
    (AllLeftRayAlternative p ∧ ¬ AllLeftMobileAlternative p ∧ ¬ AllLeftFlagAlternative p) ∨
    (AllLeftMobileAlternative p ∧ ¬ AllLeftRayAlternative p ∧ ¬ AllLeftFlagAlternative p) ∨
    (AllLeftFlagAlternative p ∧ ¬ AllLeftRayAlternative p ∧ ¬ AllLeftMobileAlternative p) :=
  allLeft_structural_trichotomy_of_exactLifting p hM hleft hright hessleft hessright
    (allLeftExactLifting_of_full_rank p hM)

/-- Unconditional source Corollary 10.10 on actual binary contexts. It gives
one fixed adapted ray basis, the rank-four/rank-eight cover alternative, and
same-language width-three compression from any non-partial-monomial context.
The displayed right-essentiality assumption is unnecessary for this stronger
formulation because full base rank is explicit. -/
theorem allLeft_binary_context_corollary
    {S : LabelledShape} {t : ℕ} (p : LabelledCommonPresentation S (Fin 3) t)
    (hM : p.baseMatrix.rank = 3)
    (P L : Submodule ℂ (Fin 3 → ℂ))
    (hP : P ∈ allLeftRealizedSupports p.language 2)
    (hL : L ∈ allLeftRealizedSupports p.language 1) (hLP : ¬ L ≤ P) :
    ∃ T N : Matrix (Fin 3) (Fin 3) ℂ,
      T.rank = 3 ∧ T * N = 1 ∧ N * T = 1 ∧ Submodule.span ℂ {T.row 2} = L ∧
      primitiveParityEndpoint p.baseMatrix P 0 = Submodule.span ℂ {T.row 0} ∧
      primitiveParityEndpoint p.baseMatrix P 1 = Submodule.span ℂ {T.row 1} ∧
      (BinarySmallCover p.baseMatrix ∨
        ∀ a b c (I : AllLeftGadget S a b c 2), I.Connected → Nonempty I.OrderedPlanar →
          PartialMonomial (binaryContextCoordinates N (I.value p.language))) ∧
      (∀ a b c (I : AllLeftGadget S a b c 2), I.Connected → Nonempty I.OrderedPlanar →
        ¬ PartialMonomial (binaryContextCoordinates N (I.value p.language)) →
        ∃ w ≤ 3, ∃ q : LabelledCommonPresentation S (Fin 3) w,
          q.left = p.left ∧ q.language = p.language ∧
          ExactlyLabelledEquivalent p.language q.language) :=
  allLeft_binary_context_corollary_of_exactLifting p hM
    (allLeftExactLifting_of_full_rank p hM) P L hP hL hLP

end
end MatchgateWidth
