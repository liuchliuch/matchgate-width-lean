import MatchgateWidth.SourceSupportTrichotomy
import MatchgateWidth.GeneralPrimitiveAllLeftGadget

/-!
# All-arity structural alternatives on the actual source gadget closure

The source primitive rank/essentiality conditions are literal. The only
geometric input isolated here is exact ordered lifting of actual gadget
boundary tensors, subsequently proved in AllLeftSubstitutionRouting; primitive inclusion, transformed supports, pure rays, Gaussian
planes, flag transport, common covers and labelwise compression are derived.
-/
namespace MatchgateWidth
noncomputable section
open scoped Classical
set_option maxHeartbeats 800000

/-- All primitive labels, including nullary labels, occur as actual connected
ordered planar one-vertex gadgets. -/
theorem primitiveAllLeftRealization {S : LabelledShape} (F : LabelledLanguage S (Fin 3)) :
    PrimitiveAllLeftRealization F := by
  intro l
  exact ⟨1, 0, 0, AllLeftGadget.primitive l, AllLeftGadget.primitive_connected l,
    AllLeftGadget.primitive_orderedPlanar l, AllLeftGadget.primitive_value F l⟩

/-- The source closure-essentiality equation, derived from primitive
left-essentiality and deficiency rather than imposed on the closure. -/
theorem allLeft_span_of_leftEssential {S : LabelledShape} (F : LabelledLanguage S (Fin 3))
    (hdef : LeftPortDeficient F) (hess : LeftSupportEssential F) :
    sSup (allLeftRealizedSupports F 1 ∪ allLeftRealizedSupports F 2) = ⊤ :=
  allLeftRealizedSupports_span F hdef hess (primitiveAllLeftRealization F)

/-- Uniform all-rays conclusion, stated for actual nonzero boundary tensors.
Arity zero is included as the empty product scalar. -/
def AllLeftRayNormalForm {S : LabelledShape} {t : ℕ}
    (p : LabelledCommonPresentation S (Fin 3) t) : Prop :=
  ∀ a b c n (I : AllLeftGadget S a b c n), I.Connected → Nonempty I.OrderedPlanar →
    I.value p.language ≠ 0 →
    ∃ (c : ℂ) (q : Fin n → Fin 3 → ℂ), c ≠ 0 ∧ (∀ j, q j ≠ 0) ∧
      (∀ x, I.value p.language x = c * ∏ j, q j (x j)) ∧
      ∀ j, ExactMatchgate (unaryTransform p.baseMatrix (q j))

/-- Uniform Boolean-core-times-rays conclusion. One endpoint encoder and one
transverse ray generator are selected before every arity and every gadget.
The retained ports keep their canonical increasing original order. -/
def AllLeftFlagNormalForm {S : LabelledShape} {t : ℕ}
    (p : LabelledCommonPresentation S (Fin 3) t)
    (P L : Submodule ℂ (Fin 3 → ℂ)) : Prop :=
  ∃ (E : Matrix (BooleanInput 1) (Fin 3) ℂ) (r : Fin 3 → ℂ),
    Submodule.span ℂ (Set.range E.row) = P ∧ Function.Injective E.transpose.mulVecLin ∧
    r ≠ 0 ∧ L = Submodule.span ℂ {r} ∧ r ∉ P ∧
    primitiveParityEndpoint p.baseMatrix P 0 = Submodule.span ℂ {E.row (fun _ => 0)} ∧
    primitiveParityEndpoint p.baseMatrix P 1 = Submodule.span ℂ {E.row (fun _ => 1)} ∧
    ExactMatchgateMatrix (E*p.baseMatrix) ∧
    ∀ a b c n (I : AllLeftGadget S a b c n), I.Connected → Nonempty I.OrderedPlanar →
      I.value p.language ≠ 0 →
      let T := I.value p.language
      let A := planeSupportedPorts P T
      let e := (planePortEmbedding P T).toEmbedding
      let q := fun j => fixedFlagRay E r (columnSupport (portFlatten T j))
      ∃ h : BooleanTable A.card ℂ, ExactMatchgate h ∧ h ≠ 0 ∧ StrictMono e ∧
        T = flagTensor E e q h ∧
        (∀ i, Module.finrank ℂ (columnSupport (portFlatten h i)) = 2) ∧
        (A.card = 0 ∨ 2 ≤ A.card) ∧
        (∀ j, j ∉ Set.range e → q j ≠ 0 ∧
          columnSupport (portFlatten T j) = Submodule.span ℂ {q j} ∧
          ExactMatchgate (unaryTransform p.baseMatrix (q j)))

/-- Empty actual plane-support set forces complete pure-ray factorization. -/
theorem allLeft_ray_normal_form_of_exactLifting {S : LabelledShape} {t : ℕ}
    (p : LabelledCommonPresentation S (Fin 3) t) (hM : p.baseMatrix.rank = 3)
    (hdef : LeftPortDeficient p.language) (hlift : AllLeftExactLifting p)
    (hempty : allLeftRealizedSupports p.language 2 = ∅) : AllLeftRayNormalForm p := by
  intro a b c n I hconn hplan hne
  apply exact_all_line_supports_decomposition p.baseMatrix hM (I.value p.language) hne
    (hlift a b c n I hconn hplan)
  intro j
  rcases I.boundary_support_one_or_two p.language hdef hne j with h | h
  · exact h
  · have hm : columnSupport (portFlatten (I.value p.language) j) ∈
        allLeftRealizedSupports p.language 2 := ⟨a,b,c,n,I,hconn,hplan,hne,j,rfl,h⟩
    rw [hempty] at hm
    exact False.elim hm

/-- One actual source flag gives a single endpoint-basis normal form for the
whole closure. No factorization, endpoint choice, or Boolean core is assumed. -/
theorem allLeft_flag_normal_form_of_exactLifting {S : LabelledShape} {t : ℕ}
    (p : LabelledCommonPresentation S (Fin 3) t) (hM : p.baseMatrix.rank = 3)
    (hdef : LeftPortDeficient p.language) (hlift : AllLeftExactLifting p)
    {P L : Submodule ℂ (Fin 3 → ℂ)} (hflag : AllLeftMonomialFlag p P L) :
    AllLeftFlagNormalForm p P L := by
  obtain ⟨a,b,c,n,I,hconn,hplan,hne,j,hP,hd⟩ := hflag.1
  obtain ⟨B,hB,hspace⟩ := exact_lift_block_rowSpace p.baseMatrix hM (I.value p.language)
    (hlift a b c n I hconn hplan) j
  have hrB : B.rank = 2 := by
    rw [Matrix.rank_eq_finrank_span_row]
    change Module.finrank ℂ (orderedRowSpace B) = 2
    rw [hspace, finrank_map_transpose_eq p.baseMatrix
      (transpose_injective_of_rank_eq_card p.baseMatrix (by simpa using hM)), ← hP]
    exact hd
  rw [← hP] at hspace
  obtain ⟨E,D,hEP,hEM,hD,hED,hr,h₀,h₁,hp₀,hp₁,he₀,he₁,hcanonical,hnormal⟩ :=
    exact_uniform_flag_normal_form p.baseMatrix hM P B hB hrB hspace
  have hLdim : Module.finrank ℂ L = 1 := by
    obtain ⟨a,b,c,n,I,hc,hp,hn,j,hL,hd⟩ := hflag.2.1
    exact hd
  obtain ⟨r, hrne, hLr⟩ := exists_generator_of_finrank_one L hLdim
  have hrP : r ∉ P := by
    intro h
    exact hflag.2.2.1 (hLr.symm ▸ Submodule.span_le.mpr (by simpa using h))
  refine ⟨E,r,hEP,primitive_encoder_injective p.baseMatrix E D hED,
    hrne,hLr,hrP,he₀,he₁,hEM,?_⟩
  intro a b c n I hconn hplan hne
  have hsupport : ∀ j, columnSupport (portFlatten (I.value p.language) j) = P ∨
      columnSupport (portFlatten (I.value p.language) j) = primitiveParityEndpoint p.baseMatrix P 0 ∨
      columnSupport (portFlatten (I.value p.language) j) = primitiveParityEndpoint p.baseMatrix P 1 ∨
      columnSupport (portFlatten (I.value p.language) j) = Submodule.span ℂ {r} := by
    intro j
    rcases I.boundary_support_one_or_two p.language hdef hne j with h | h
    · have hm : columnSupport (portFlatten (I.value p.language) j) ∈
          allLeftRealizedSupports p.language 1 := ⟨a,b,c,n,I,hconn,hplan,hne,j,rfl,h⟩
      have hx := hflag.2.2.2.2 hm
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, hLr] at hx
      exact Or.inr hx
    · have hm : columnSupport (portFlatten (I.value p.language) j) ∈
          allLeftRealizedSupports p.language 2 := ⟨a,b,c,n,I,hconn,hplan,hne,j,rfl,h⟩
      rw [hflag.2.2.2.1] at hm
      exact Or.inl (Set.mem_singleton_iff.mp hm)
  obtain ⟨h, hh, hne, he, hf, hmodes, harity, hrays, _⟩ :=
    hnormal r hrne hrP n (I.value p.language) hne (hlift a b c n I hconn hplan) hsupport
  exact ⟨h, hh, hne, he, hf, hmodes, harity, hrays⟩

/-- Actual rank-at-most-eight cover and one common smaller presentation on the
same label sets, with every original induced tensor literally unchanged. -/
def AllLeftWidthThreeCompression {S : LabelledShape} {t : ℕ}
    (p : LabelledCommonPresentation S (Fin 3) t) : Prop :=
  ∃ r ≤ 3, ∃ H : Matrix (BooleanInput r) (BooleanInput t) ℂ,
    ExactMatchgateMatrix H ∧ H.rank = 2 ^ r ∧ H.rank ≤ 8 ∧
    ∃ q : LabelledCommonPresentation S (Fin 3) r,
      p.baseMatrix = q.baseMatrix * H ∧ q.left = p.left ∧
      q.language = p.language ∧ ExactlyLabelledEquivalent p.language q.language

def AllLeftRayAlternative {S : LabelledShape} {t : ℕ}
    (p : LabelledCommonPresentation S (Fin 3) t) : Prop :=
  allLeftRealizedSupports p.language 2 = ∅ ∧ AllLeftRayNormalForm p

def AllLeftMobileAlternative {S : LabelledShape} {t : ℕ}
    (p : LabelledCommonPresentation S (Fin 3) t) : Prop :=
  (allLeftRealizedSupports p.language 2).Nonempty ∧
    (¬ ∃ P L, AllLeftMonomialFlag p P L) ∧ AllLeftWidthThreeCompression p

def AllLeftFlagAlternative {S : LabelledShape} {t : ℕ}
    (p : LabelledCommonPresentation S (Fin 3) t) : Prop :=
  ∃ P L, AllLeftMonomialFlag p P L ∧ AllLeftFlagNormalForm p P L

/-- Source Theorem 3.3's three structural alternatives, conditional only on the
separately named exact ordered gadget-lifting obligation. Every port of each
original left AND induced right primitive is deficient, and bi-essentiality is
explicit. The geometric argument itself only uses the left halves once exact
lifting is supplied. The unbounded-family clause is assembled separately. -/
theorem allLeft_structural_trichotomy_of_exactLifting {S : LabelledShape} {t : ℕ}
    (p : LabelledCommonPresentation S (Fin 3) t) (hM : p.baseMatrix.rank = 3)
    (hleft : LeftPortDeficient p.language) (_hright : RightPortDeficient p.language)
    (hessleft : LeftSupportEssential p.language) (_hessright : RightSupportEssential p.language)
    (hlift : AllLeftExactLifting p) :
    (AllLeftRayAlternative p ∧ ¬ AllLeftMobileAlternative p ∧ ¬ AllLeftFlagAlternative p) ∨
    (AllLeftMobileAlternative p ∧ ¬ AllLeftRayAlternative p ∧ ¬ AllLeftFlagAlternative p) ∨
    (AllLeftFlagAlternative p ∧ ¬ AllLeftRayAlternative p ∧ ¬ AllLeftMobileAlternative p) := by
  classical
  have hspan := allLeft_span_of_leftEssential p.language hleft hessleft
  have ray_mobile : AllLeftRayAlternative p → ¬ AllLeftMobileAlternative p := by
    rintro hr ⟨⟨P,hP⟩,_,_⟩
    rw [hr.1] at hP
    exact hP
  have ray_flag : AllLeftRayAlternative p → ¬ AllLeftFlagAlternative p := by
    rintro hr ⟨P,L,hf,_⟩
    have hP := hf.1
    rw [hr.1] at hP
    exact hP
  have mobile_flag : AllLeftMobileAlternative p → ¬ AllLeftFlagAlternative p := by
    rintro hm ⟨P,L,hf,_⟩
    exact hm.2.1 ⟨P,L,hf⟩
  by_cases he : allLeftRealizedSupports p.language 2 = ∅
  · have hr : AllLeftRayAlternative p :=
      ⟨he, allLeft_ray_normal_form_of_exactLifting p hM hleft hlift he⟩
    exact Or.inl ⟨hr,ray_mobile hr,ray_flag hr⟩
  · by_cases hf : ∃ P L, AllLeftMonomialFlag p P L
    · obtain ⟨P,L,hf⟩ := hf
      have hf' : AllLeftFlagAlternative p :=
        ⟨P,L,hf,allLeft_flag_normal_form_of_exactLifting p hM hleft hlift hf⟩
      exact Or.inr (Or.inr ⟨hf',fun hr => ray_flag hr hf',fun hm => mobile_flag hm hf'⟩)
    · have hm : AllLeftMobileAlternative p :=
        ⟨Set.nonempty_iff_ne_empty.mpr he,hf,
          allLeft_connectionPrime_compression_of_exactLifting p hM hlift
            ⟨hspan,Set.nonempty_iff_ne_empty.mpr he,hf⟩⟩
      exact Or.inr (Or.inl ⟨hm,fun hr => ray_mobile hr hm,mobile_flag hm⟩)

/-- The source two-distinct-planes refinement constructs width exactly two and
an actual rank-four exact cover of the same labelled presentation. -/
theorem allLeft_two_planes_compression_of_exactLifting {S : LabelledShape} {t : ℕ}
    (p : LabelledCommonPresentation S (Fin 3) t) (hM : p.baseMatrix.rank = 3)
    (hlift : AllLeftExactLifting p) {P Q : Submodule ℂ (Fin 3 → ℂ)}
    (hP : P ∈ allLeftRealizedSupports p.language 2)
    (hQ : Q ∈ allLeftRealizedSupports p.language 2) (hne : P ≠ Q) :
    ∃ H : Matrix (BooleanInput 2) (BooleanInput t) ℂ,
      ExactMatchgateMatrix H ∧ H.rank = 4 ∧
      ∃ q : LabelledCommonPresentation S (Fin 3) 2,
        p.baseMatrix = q.baseMatrix * H ∧ q.left = p.left ∧
        q.language = p.language ∧ ExactlyLabelledEquivalent p.language q.language := by
  apply p.two_planes_compression hM (allLeftExactSupportGeometry p hM hlift) rfl
    (P := P.map (qutritSubsetMap p.baseMatrix)) (Q := Q.map (qutritSubsetMap p.baseMatrix))
  · exact ⟨P,hP,rfl⟩
  · exact ⟨Q,hQ,rfl⟩
  · exact fun he => hne (Submodule.map_injective_of_injective
      (qutritSubsetMap_injective p.baseMatrix hM) he)

end
end MatchgateWidth
