import MatchgateWidth.AllLeftSupportExtraction
import MatchgateWidth.SupportGeometryTrichotomy
import MatchgateWidth.ExactFlagNormalForm

/-!
# Source support terminology on the actual all-left gadget closure

The domain rays/planes are exactly actual realized gadget supports. Parity
endpoints are defined by the displayed base, independently of a chosen basis.
The remaining ordered planar lifting premise is explicitly named wherever used.
-/
namespace MatchgateWidth
noncomputable section
open scoped Classical
set_option maxHeartbeats 600000

/-- Source Definition 4.5 on actual qutrit-domain gadget supports. -/
def AllLeftMonomialFlag {S : LabelledShape} {t : ℕ}
    (p : LabelledCommonPresentation S (Fin 3) t)
    (P L : Submodule ℂ (Fin 3 → ℂ)) : Prop :=
  P ∈ allLeftRealizedSupports p.language 2 ∧
  L ∈ allLeftRealizedSupports p.language 1 ∧ ¬ L ≤ P ∧
  allLeftRealizedSupports p.language 2 = {P} ∧
  allLeftRealizedSupports p.language 1 ⊆
    {primitiveParityEndpoint p.baseMatrix P 0, primitiveParityEndpoint p.baseMatrix P 1, L}

/-- Source connection-primality, with no ambient cover assumption. -/
def AllLeftConnectionPrime {S : LabelledShape} {t : ℕ}
    (p : LabelledCommonPresentation S (Fin 3) t) : Prop :=
  sSup (allLeftRealizedSupports p.language 1 ∪ allLeftRealizedSupports p.language 2) = ⊤ ∧
  (allLeftRealizedSupports p.language 2).Nonempty ∧
  ¬ ∃ P L, AllLeftMonomialFlag p P L

/-- Fixed points of the subset projection are exactly the literal Boolean
parity subspace used to define the source pullback endpoints. -/
theorem subsetProjection_fixed_iff {t : ℕ} (u : BooleanTable t ℂ) (k : ℕ) :
    subsetParityProjection k (spinorSubsetEquiv u) = spinorSubsetEquiv u ↔
      u ∈ booleanParitySubspace t k := by
  constructor
  · intro h y hy
    have hh := congrFun h ((booleanSubsetEquiv t) y)
    change ((booleanSubsetEquiv t) y).card % 2 ≠ k at hy
    simpa only [subsetParityProjection, LinearMap.coe_mk, AddHom.coe_mk,
      spinorSubsetEquiv_apply, Equiv.symm_apply_apply, ite_eq_right hy] using hh.symm
  · intro h
    ext A
    by_cases hk : A.card % 2 = k
    · simp [subsetParityProjection, hk]
    · have hz := h ((booleanSubsetEquiv t).symm A) (by simpa [booleanParity] using hk)
      simp [subsetParityProjection, hk, spinorSubsetEquiv_apply, hz]

/-- Projection onto either Gaussian endpoint remains inside the plane. -/
theorem RealizedMatchgateGeometry.endpoint_le {t : ℕ} (g : RealizedMatchgateGeometry t)
    {P : Submodule ℂ (SubsetSignature t ℂ)} (hP : P ∈ g.planes)
    (k : ℕ) (hk : k < 2) : supportParityEndpoint P k ≤ P := by
  obtain ⟨m, A, hA, hr, rfl⟩ := g.plane_realized P hP
  obtain ⟨u, w, he, hu, huk, hwk⟩ := hA.identities.exists_subset_parity_endpoints hr k hk
  unfold supportParityEndpoint
  rw [he, Submodule.map_span, Set.image_pair, huk, hwk]
  apply Submodule.span_le.mpr
  intro v hv
  rcases hv with rfl | hv
  · exact Submodule.subset_span (by simp)
  · have : v = 0 := Set.mem_singleton_iff.mp hv
    subst v
    exact Submodule.zero_mem _

/-- The actual source-domain parity endpoint maps to the actual Gaussian
parity endpoint. This is an equality, not just a support containment. -/
theorem primitiveParityEndpoint_map {t : ℕ}
    (M : Matrix (Fin 3) (BooleanInput t) ℂ) (P : Submodule ℂ (Fin 3 → ℂ))
    (k : ℕ)
    (hstable : supportParityEndpoint (P.map (qutritSubsetMap M)) k ≤ P.map (qutritSubsetMap M)) :
    (primitiveParityEndpoint M P k).map (qutritSubsetMap M) =
      supportParityEndpoint (P.map (qutritSubsetMap M)) k := by
  have hid (v : SubsetSignature t ℂ) : subsetParityProjection k (subsetParityProjection k v) =
      subsetParityProjection k v := by
    ext A
    by_cases ha : A.card % 2 = k <;> simp [subsetParityProjection, ha]
  have hfixed (u : Fin 3 → ℂ) : subsetParityProjection k (qutritSubsetMap M u) =
      qutritSubsetMap M u ↔ M.transpose.mulVecLin u ∈ booleanParitySubspace t k :=
    subsetProjection_fixed_iff (M.transpose.mulVecLin u) k
  apply le_antisymm
  · rintro v ⟨u, hu, rfl⟩
    exact ⟨qutritSubsetMap M u, ⟨u, hu.1, rfl⟩, (hfixed u).mpr hu.2⟩
  · rintro v ⟨w, hw, rfl⟩
    have hv := hstable ⟨w, hw, rfl⟩
    obtain ⟨u, hu, he⟩ := hv
    refine ⟨u, ⟨hu, (hfixed u).mp ?_⟩, he⟩
    rw [he, hid]

/-- Full rank makes image membership in the realized support sets exact. -/
theorem allLeftSubsetSupports_mem_iff {S : LabelledShape} {t : ℕ}
    (p : LabelledCommonPresentation S (Fin 3) t) (hM : p.baseMatrix.rank = 3)
    (d : ℕ) (U : Submodule ℂ (Fin 3 → ℂ)) :
    U.map (qutritSubsetMap p.baseMatrix) ∈ allLeftSubsetSupports p d ↔
      U ∈ allLeftRealizedSupports p.language d := by
  constructor
  · rintro ⟨V, hV, he⟩
    exact (Submodule.map_injective_of_injective
      (qutritSubsetMap_injective p.baseMatrix hM) he) ▸ hV
  · intro hU
    exact ⟨U, hU, rfl⟩

/-- The source monomial-flag definition agrees exactly with its faithful
image in actual subset-coefficient matchgate support geometry. -/
theorem allLeftMonomialFlag_iff_image {S : LabelledShape} {t : ℕ}
    (p : LabelledCommonPresentation S (Fin 3) t) (hM : p.baseMatrix.rank = 3)
    (hlift : AllLeftExactLifting p) (P L : Submodule ℂ (Fin 3 → ℂ)) :
    AllLeftMonomialFlag p P L ↔
      (allLeftExactSupportGeometry p hM hlift).MonomialFlag
        (P.map (qutritSubsetMap p.baseMatrix)) (L.map (qutritSubsetMap p.baseMatrix)) := by
  let g := allLeftExactSupportGeometry p hM hlift
  let f := qutritSubsetMap p.baseMatrix
  have hfi := qutritSubsetMap_injective p.baseMatrix hM
  have hmi := Submodule.map_injective_of_injective hfi
  have hmem (d : ℕ) (U : Submodule ℂ (Fin 3 → ℂ)) := allLeftSubsetSupports_mem_iff p hM d U
  have hend (hP : P ∈ allLeftRealizedSupports p.language 2) (k : ℕ) (hk : k < 2) :
      (primitiveParityEndpoint p.baseMatrix P k).map f = supportParityEndpoint (P.map f) k := by
    apply primitiveParityEndpoint_map
    exact g.endpoint_le ((hmem 2 P).mpr hP) k hk
  constructor
  · rintro ⟨hP, hL, hLP, hplanes, hrays⟩
    refine ⟨(hmem 2 P).mpr hP, (hmem 1 L).mpr hL,
      fun h => hLP ((Submodule.map_le_map_iff_of_injective hfi L P).mp h), ?_, ?_⟩
    · change (fun U => U.map f) '' allLeftRealizedSupports p.language 2 = {P.map f}
      rw [hplanes, Set.image_singleton]
    · rintro R ⟨U, hU, rfl⟩
      have hh := hrays hU
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hh ⊢
      rcases hh with h | h | h
      · exact Or.inl (congrArg (Submodule.map f) h |>.trans (hend hP 0 (by decide)))
      · exact Or.inr (Or.inl (congrArg (Submodule.map f) h |>.trans (hend hP 1 (by decide))))
      · exact Or.inr (Or.inr (congrArg (Submodule.map f) h))
  · rintro ⟨hPmap, hLmap, hLPmap, hplanes, hrays⟩
    have hP := (hmem 2 P).mp hPmap
    refine ⟨hP, (hmem 1 L).mp hLmap,
      fun h => hLPmap (Submodule.map_mono h), ?_, ?_⟩
    · ext U
      simp only [Set.mem_singleton_iff]
      constructor
      · intro hU
        have hu := (hmem 2 U).mpr hU
        change U.map f ∈ g.planes at hu
        rw [hplanes] at hu
        exact hmi (Set.mem_singleton_iff.mp hu)
      · rintro rfl
        exact hP
    · intro U hU
      have hu := hrays ((hmem 1 U).mpr hU)
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu ⊢
      rcases hu with h | h | h
      · exact Or.inl (hmi (h.trans (hend hP 0 (by decide)).symm))
      · exact Or.inr (Or.inl (hmi (h.trans (hend hP 1 (by decide)).symm)))
      · exact Or.inr (Or.inr (hmi h))

/-- Every flag of the faithful image comes from an actual source-domain flag. -/
theorem allLeftMonomialFlag_exists_iff_image {S : LabelledShape} {t : ℕ}
    (p : LabelledCommonPresentation S (Fin 3) t) (hM : p.baseMatrix.rank = 3)
    (hlift : AllLeftExactLifting p) :
    (∃ P L, AllLeftMonomialFlag p P L) ↔
      ∃ P L, (allLeftExactSupportGeometry p hM hlift).MonomialFlag P L := by
  constructor
  · rintro ⟨P, L, h⟩
    exact ⟨_, _, (allLeftMonomialFlag_iff_image p hM hlift P L).mp h⟩
  · rintro ⟨P, L, h⟩
    obtain ⟨P₀, hP₀, rfl⟩ := h.1
    obtain ⟨L₀, hL₀, rfl⟩ := h.2.1
    exact ⟨P₀, L₀, (allLeftMonomialFlag_iff_image p hM hlift P₀ L₀).mpr h⟩

/-- Actual source connection-primality transports through the full base. -/
theorem allLeftConnectionPrime_image {S : LabelledShape} {t : ℕ}
    (p : LabelledCommonPresentation S (Fin 3) t) (hM : p.baseMatrix.rank = 3)
    (hlift : AllLeftExactLifting p) (hprime : AllLeftConnectionPrime p) :
    (allLeftExactSupportGeometry p hM hlift).ConnectionPrime := by
  refine ⟨allLeftSubsetSupports_span p hprime.1, ?_, ?_⟩
  · obtain ⟨P, hP⟩ := hprime.2.1
    exact ⟨P.map (qutritSubsetMap p.baseMatrix), P, hP, rfl⟩
  · intro hflag
    exact hprime.2.2 ((allLeftMonomialFlag_exists_iff_image p hM hlift).mpr hflag)

/-- Source Theorem 10.7 after the explicitly named ordered gadget-lifting
obligation. The result is an actual common cover and a genuinely identical
labelled presentation, including all nullary and zero labels. -/
theorem allLeft_connectionPrime_compression_of_exactLifting {S : LabelledShape} {t : ℕ}
    (p : LabelledCommonPresentation S (Fin 3) t) (hM : p.baseMatrix.rank = 3)
    (hlift : AllLeftExactLifting p) (hprime : AllLeftConnectionPrime p) :
    ∃ r ≤ 3, ∃ H : Matrix (BooleanInput r) (BooleanInput t) ℂ,
      ExactMatchgateMatrix H ∧ H.rank = 2 ^ r ∧ H.rank ≤ 8 ∧
      ∃ q : LabelledCommonPresentation S (Fin 3) r,
        p.baseMatrix = q.baseMatrix * H ∧ q.left = p.left ∧
        q.language = p.language ∧ ExactlyLabelledEquivalent p.language q.language :=
  p.connectionPrime_compression hM (allLeftExactSupportGeometry p hM hlift) rfl
    (allLeftConnectionPrime_image p hM hlift hprime)

end
end MatchgateWidth
