import MatchgateWidth.NonflagDiskCover
import MatchgateWidth.ExactMatchgateLinear

/-!
# Connection-prime incidence forces a common exact cover

The geometric input records actual pure rays and actual exact ordered matchgate
rowspaces. It does not assume a cover, an annihilator, a pure pencil, or a parity
of the transverse rays. The source gadget-to-support bridge is a separate
obligation: this module proves the complete incidence implication after that
bridge, without pretending an arbitrary family is a gadget closure.
-/
namespace MatchgateWidth
noncomputable section
set_option maxHeartbeats 800000

/-- The actual parity endpoint of a Gaussian plane, in its fixed subset
coordinates. Its dimension one is a theorem for realized rank-two planes. -/
def supportParityEndpoint {t : ℕ} (P : Submodule ℂ (SubsetSignature t ℂ)) (k : ℕ) :
    Submodule ℂ (SubsetSignature t ℂ) := P.map (subsetParityProjection k)

/-- Data extracted from realized rank-one and rank-two supports. Realization
requires literal pure coefficients and literal exact ordered matrix witnesses.
The type deliberately does not assert an underlying gadget realization. -/
structure RealizedMatchgateGeometry (t : ℕ) where
  ambient : Submodule ℂ (SubsetSignature t ℂ)
  rays : Set (Submodule ℂ (SubsetSignature t ℂ))
  planes : Set (Submodule ℂ (SubsetSignature t ℂ))
  ray_le : ∀ R ∈ rays, R ≤ ambient
  plane_le : ∀ P ∈ planes, P ≤ ambient
  ray_realized : ∀ R ∈ rays, ∃ v, IsPureSpinor v ∧ R = Submodule.span ℂ {v}
  plane_realized : ∀ P ∈ planes, ∃ m, ∃ A : Matrix (BooleanInput m) (BooleanInput t) ℂ,
    ExactMatchgateMatrix A ∧ A.rank = 2 ∧ P = (orderedRowSpace A).map spinorSubsetEquiv.toLinearMap

namespace RealizedMatchgateGeometry
variable {t : ℕ} (g : RealizedMatchgateGeometry t)

/-- Source Definition 4.5, using the two actual parity endpoints. -/
def MonomialFlag (P L : Submodule ℂ (SubsetSignature t ℂ)) : Prop :=
  P ∈ g.planes ∧ L ∈ g.rays ∧ ¬ L ≤ P ∧ g.planes = {P} ∧
    g.rays ⊆ {supportParityEndpoint P 0, supportParityEndpoint P 1, L}

/-- Spanning, a realized plane, and absence of a monomial flag. -/
def ConnectionPrime : Prop :=
  sSup (g.rays ∪ g.planes) = g.ambient ∧ g.planes.Nonempty ∧
    ¬ ∃ P L, g.MonomialFlag P L

theorem ray_finrank {R : Submodule ℂ (SubsetSignature t ℂ)} (hR : R ∈ g.rays) :
    Module.finrank ℂ R = 1 := by
  obtain ⟨v, hv, rfl⟩ := g.ray_realized R hR
  exact finrank_span_singleton hv.1

theorem plane_finrank {P : Submodule ℂ (SubsetSignature t ℂ)} (hP : P ∈ g.planes) :
    Module.finrank ℂ P = 2 := by
  obtain ⟨m, A, _, hr, rfl⟩ := g.plane_realized P hP
  rw [← (spinorSubsetEquiv.submoduleMap (orderedRowSpace A)).finrank_eq]
  change Module.finrank ℂ (Submodule.span ℂ (Set.range A.row)) = 2
  rw [← Matrix.rank_eq_finrank_span_row, hr]

/-- The endpoint subspace is a nonzero line, derived from actual pinned rows. -/
theorem endpoint_finrank {P : Submodule ℂ (SubsetSignature t ℂ)} (hP : P ∈ g.planes)
    (k : ℕ) (hk : k < 2) : Module.finrank ℂ (supportParityEndpoint P k) = 1 := by
  obtain ⟨m, A, hA, hr, rfl⟩ := g.plane_realized P hP
  obtain ⟨u, w, he, hu, huk, hwk⟩ := hA.identities.exists_subset_parity_endpoints hr k hk
  unfold supportParityEndpoint
  rw [he, Submodule.map_span]
  rw [Set.image_pair]
  rw [huk, hwk]
  rw [Set.pair_comm u (0 : SubsetSignature t ℂ), Submodule.span_insert_zero]
  exact finrank_span_singleton hu.1

/-- Purity excludes any third realized ray inside a rank-two Gaussian plane. -/
theorem ray_le_plane_is_endpoint {R P : Submodule ℂ (SubsetSignature t ℂ)}
    (hR : R ∈ g.rays) (hP : P ∈ g.planes) (hle : R ≤ P) :
    R = supportParityEndpoint P 0 ∨ R = supportParityEndpoint P 1 := by
  obtain ⟨v, hv, hRv⟩ := g.ray_realized R hR
  obtain ⟨k, hk, hkv⟩ := hv.exists_subset_parity
  have hRend : R ≤ supportParityEndpoint P k := by
    rw [hRv]
    apply Submodule.span_le.mpr
    intro x hx
    have hxv : x = v := Set.mem_singleton_iff.mp hx
    subst x
    exact ⟨v, hle (hRv.symm ▸ Submodule.subset_span (by simp)), hkv⟩
  have heq := Submodule.eq_of_le_of_finrank_eq hRend
    ((g.ray_finrank hR).trans (g.endpoint_finrank hP k hk).symm)
  have : k = 0 ∨ k = 1 := by omega
  rcases this with rfl | rfl
  · exact Or.inl heq
  · exact Or.inr heq

/-- Spanning forbids all rays from lying in the unique realized plane. -/
theorem exists_transverse_ray (hdim : Module.finrank ℂ g.ambient = 3)
    (hspan : sSup (g.rays ∪ g.planes) = g.ambient)
    {P : Submodule ℂ (SubsetSignature t ℂ)} (hP : P ∈ g.planes)
    (hunique : g.planes = {P}) : ∃ L ∈ g.rays, ¬ L ≤ P := by
  by_contra hn
  push Not at hn
  have hall : sSup (g.rays ∪ g.planes) ≤ P := by
    apply sSup_le
    intro R hR
    rcases hR with hR | hR
    · exact hn R hR
    · have : R = P := by simpa [hunique] using hR
      subst R
      exact le_rfl
  rw [hspan] at hall
  have hh := Submodule.finrank_mono hall
  rw [hdim, g.plane_finrank hP] at hh
  omega

/-- The exact combinatorial split in source Theorem 10.7: two distinct
Gaussian planes, or two distinct pure rays transverse to one Gaussian plane. -/
theorem connectionPrime_incidence (hdim : Module.finrank ℂ g.ambient = 3)
    (hprime : g.ConnectionPrime) :
    (∃ P ∈ g.planes, ∃ Q ∈ g.planes, P ≠ Q) ∨
    (∃ P ∈ g.planes, ∃ L ∈ g.rays, ∃ R ∈ g.rays,
      ¬ L ≤ P ∧ ¬ R ≤ P ∧ L ≠ R) := by
  classical
  obtain ⟨hspan, ⟨P, hP⟩, hflag⟩ := hprime
  by_cases htwo : ∃ Q ∈ g.planes, P ≠ Q
  · obtain ⟨Q, hQ, hPQ⟩ := htwo
    exact Or.inl ⟨P, hP, Q, hQ, hPQ⟩
  · have hsingle : g.planes = {P} := by
      ext Q
      simp only [Set.mem_singleton_iff]
      constructor
      · intro hQ
        by_contra hQP
        exact htwo ⟨Q, hQ, Ne.symm hQP⟩
      · rintro rfl
        exact hP
    obtain ⟨L, hL, hLP⟩ := g.exists_transverse_ray hdim hspan hP hsingle
    have hthird : ∃ R ∈ g.rays,
        R ≠ supportParityEndpoint P 0 ∧ R ≠ supportParityEndpoint P 1 ∧ R ≠ L := by
      by_contra hn
      apply hflag
      refine ⟨P, L, hP, hL, hLP, hsingle, ?_⟩
      intro R hR
      by_contra hm
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hm
      exact hn ⟨R, hR, hm.1, hm.2.1, hm.2.2⟩
    obtain ⟨R, hR, hR0, hR1, hRL⟩ := hthird
    refine Or.inr ⟨P, hP, L, hL, R, hR, hLP, ?_, Ne.symm hRL⟩
    intro hRP
    exact (g.ray_le_plane_is_endpoint hR hP hRP).elim hR0 hR1

/-- Distinct realized planes give a rank-four exact common cover. -/
theorem two_planes_cover (hdim : Module.finrank ℂ g.ambient = 3)
    {P Q : Submodule ℂ (SubsetSignature t ℂ)}
    (hP : P ∈ g.planes) (hQ : Q ∈ g.planes) (hne : P ≠ Q) :
    ∃ H : Matrix (BooleanInput 2) (BooleanInput t) ℂ,
      ExactMatchgateMatrix H ∧ H.rank = 4 ∧
      g.ambient ≤ (orderedRowSpace H).map spinorSubsetEquiv.toLinearMap := by
  obtain ⟨m, A, hA, hrA, hPA⟩ := g.plane_realized P hP
  obtain ⟨n, B, hB, hrB, hQB⟩ := g.plane_realized Q hQ
  have hAB : orderedRowSpace A ≠ orderedRowSpace B := by
    intro he
    apply hne
    rw [hPA, hQB, he]
  obtain ⟨H, hH, hr, hcover⟩ := exists_rank_four_subset_cover_of_two_planes
    g.ambient hdim hA.identities hB.identities hrA hrB
    (hPA ▸ g.plane_le P hP) (hQB ▸ g.plane_le Q hQ) hAB
  exact ⟨H, hH.exactMatrix, hr, hcover⟩

/-- Connection-primality alone supplies the actual rank-at-most-eight
common cover. All intermediate pure-spinor geometry is proved upstream. -/
theorem connectionPrime_cover (hdim : Module.finrank ℂ g.ambient = 3)
    (hprime : g.ConnectionPrime) :
    ∃ r ≤ 3, ∃ H : Matrix (BooleanInput r) (BooleanInput t) ℂ,
      ExactMatchgateMatrix H ∧ H.rank = 2 ^ r ∧
      g.ambient ≤ (orderedRowSpace H).map spinorSubsetEquiv.toLinearMap := by
  rcases g.connectionPrime_incidence hdim hprime with htwo | hrays
  · obtain ⟨P, hP, Q, hQ, hne⟩ := htwo
    obtain ⟨H, hH, hr, hc⟩ := g.two_planes_cover hdim hP hQ hne
    exact ⟨2, by decide, H, hH, hr, hc⟩
  · obtain ⟨P, hP, L, hL, R, hR, hLP, hRP, hLR⟩ := hrays
    obtain ⟨m, A, hA, hrA, hPA⟩ := g.plane_realized P hP
    obtain ⟨v, hv, hLv⟩ := g.ray_realized L hL
    obtain ⟨s, hs, hRs⟩ := g.ray_realized R hR
    have hvL : v ∈ L := hLv.symm ▸ Submodule.subset_span (by simp)
    have hsR : s ∈ R := hRs.symm ▸ Submodule.subset_span (by simp)
    have hvP : v ∉ P := by
      intro h
      exact hLP (hLv.symm ▸ Submodule.span_le.mpr (by simpa using h))
    have hsP : s ∉ P := by
      intro h
      exact hRP (hRs.symm ▸ Submodule.span_le.mpr (by simpa using h))
    have hsL : s ∉ Submodule.span ℂ {v} := by
      intro h
      have hle : R ≤ L := by rw [hRs, hLv]; exact Submodule.span_le.mpr (by simpa using h)
      have he := Submodule.eq_of_le_of_finrank_eq hle
        ((g.ray_finrank hR).trans (g.ray_finrank hL).symm)
      exact hLR he.symm
    obtain ⟨r, hr, H, hH, hHr, hcover⟩ := exists_rank_eight_cover_of_nonflag_ray_incidence
      g.ambient hdim hA.identities hrA (hPA ▸ g.plane_le P hP) v s
      (g.ray_le L hL hvL) (g.ray_le R hR hsR) (hPA ▸ hvP) (hPA ▸ hsP) hsL hv hs
    exact ⟨r, hr, H, hH.exactMatrix, hHr, hcover⟩

end RealizedMatchgateGeometry
end
end MatchgateWidth
