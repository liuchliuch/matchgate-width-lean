import MatchgateWidth.PolygonalRouting

/-! # Compact separation for local vertex disks
These lemmas give positive-radius neighborhoods that every later arc tail
avoids. They are geometric facts only, independent of tensor identities.
-/
namespace MatchgateWidth
noncomputable section
open Set Metric

/-- A finite collection of compact obstacles missing a point has a common
positive-radius ball around that point disjoint from all obstacles. -/
theorem finite_compact_obstacles_avoid_ball {ι : Type*} [Finite ι]
    (K : ι → Set ℂ) (hK : ∀ i, IsCompact (K i)) (x : ℂ)
    (hx : ∀ i, x ∉ K i) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ i y, y ∈ K i → ε ≤ dist y x := by
  have hc : IsClosed (⋃ i, K i) := (isCompact_iUnion hK).isClosed
  have hn : x ∈ (⋃ i, K i)ᶜ := by simpa using hx
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp hc.isOpen_compl x hn
  refine ⟨ε,hε,?_⟩
  intro i y hy
  apply le_of_not_gt
  intro hd
  exact hball hd (mem_iUnion.mpr ⟨i,hy⟩)

/-- An injective arc cannot re-enter a sufficiently small endpoint ball after
any prescribed positive parameter. This justifies retaining only a radial germ. -/
theorem path_initial_ball_avoids_tail {x y : ℂ} (p : Path x y)
    (hinj : Function.Injective p) (τ : unitInterval) (hτ : 0 < τ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : unitInterval, τ ≤ t → ε ≤ dist (p t) x := by
  let K : Set ℂ := p '' Ici τ
  have hK : IsCompact K := isClosed_Ici.isCompact.image p.continuous
  have hx : x ∉ K := by
    rintro ⟨t,ht,hpx⟩
    have ht0 : t=0 := hinj (hpx.trans p.source.symm)
    subst t
    exact (not_le_of_gt hτ) ht
  obtain ⟨ε,hε,hsep⟩ := finite_compact_obstacles_avoid_ball
    (fun _ : Unit => K) (fun _ => hK) x (fun _ => hx)
  exact ⟨ε,hε,fun t ht => hsep () (p t) ⟨t,ht,rfl⟩⟩

/-- The same separation at the terminal endpoint, without changing the arc. -/
theorem path_terminal_ball_avoids_prefix {x y : ℂ} (p : Path x y)
    (hinj : Function.Injective p) (τ : unitInterval) (hτ : τ < 1) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : unitInterval, t ≤ τ → ε ≤ dist (p t) y := by
  let K : Set ℂ := p '' Iic τ
  have hK : IsCompact K := isClosed_Iic.isCompact.image p.continuous
  have hy : y ∉ K := by
    rintro ⟨t,ht,hpy⟩
    have ht1 : t=1 := hinj (hpy.trans p.target.symm)
    subst t
    exact (not_le_of_gt hτ) ht
  obtain ⟨ε,hε,hsep⟩ := finite_compact_obstacles_avoid_ball
    (fun _ : Unit => K) (fun _ => hK) y (fun _ => hy)
  exact ⟨ε,hε,fun t ht => hsep () (p t) ⟨t,ht,rfl⟩⟩

/-- A simple path with a positive linear initial germ has arbitrarily small
round vertex collars. It exits each such ball exactly once and never returns. -/
theorem path_radial_collar_radii {x y : ℂ} (p : Path x y)
    (hinj : Function.Injective p) (τ : unitInterval) (hτ : 0 < τ)
    (v : ℂ) (hv : v ≠ 0)
    (hgerm : ∀ t : unitInterval, t ≤ τ → p t = x + (t : ℝ) • v) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ →
      ∃ a : unitInterval, 0 < a ∧ a < τ ∧ dist (p a) x = ε ∧
        ∀ t : unitInterval, dist (p t) x < ε ↔ t < a := by
  obtain ⟨η,hη,htail⟩ := path_initial_ball_avoids_tail p hinj τ hτ
  have hvn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hτr : 0 < (τ : ℝ) := hτ
  refine ⟨min η ((τ : ℝ)*‖v‖),lt_min hη (mul_pos hτr hvn),?_⟩
  intro ε hε hεδ
  have hεη : ε < η := lt_of_lt_of_le hεδ (min_le_left _ _)
  have hετ : ε < (τ : ℝ)*‖v‖ := lt_of_lt_of_le hεδ (min_le_right _ _)
  have ha0 : 0 < ε/‖v‖ := div_pos hε hvn
  have haτ : ε/‖v‖ < (τ : ℝ) := (div_lt_iff₀ hvn).mpr hετ
  let a : unitInterval := ⟨ε/‖v‖,ha0.le,haτ.le.trans τ.property.2⟩
  have hdist (t : unitInterval) (ht : t ≤ τ) : dist (p t) x = (t : ℝ)*‖v‖ := by
    rw [hgerm t ht, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg t.property.1]
  refine ⟨a,ha0,haτ,?_,?_⟩
  · rw [hdist a haτ.le]
    exact div_mul_cancel₀ ε (ne_of_gt hvn)
  · intro t
    by_cases ht : t ≤ τ
    · rw [hdist t ht]
      exact (lt_div_iff₀ hvn).symm
    · have htt : τ < t := lt_of_not_ge ht
      have hleft : ¬ dist (p t) x < ε := not_lt.mpr
        (hεη.le.trans (htail t htt.le))
      have hright : ¬ t < a := not_lt.mpr (haτ.le.trans htt.le)
      exact iff_of_false hleft hright

/-- Simplicity itself forces a nonzero velocity in a positive radial germ. -/
theorem path_radial_germ_ne_zero {x y : ℂ} (p : Path x y)
    (hinj : Function.Injective p) (τ : unitInterval) (hτ : 0 < τ)
    (v : ℂ) (hgerm : ∀ t : unitInterval, t ≤ τ → p t = x + (t : ℝ) • v) : v ≠ 0 := by
  intro hv
  have hpτ : p τ = p 0 := by simpa [hv, p.source] using hgerm τ le_rfl
  have ht := hinj hpτ
  exact (ne_of_gt hτ) ht

/-- A finite collection of strictly positive bounds has a common positive
lower bound, including an empty collection. -/
theorem finite_positive_lower_bound {ι : Type*} [Finite ι]
    (f : ι → ℝ) (hf : ∀ i, 0 < f i) : ∃ ε : ℝ, 0 < ε ∧ ∀ i, ε ≤ f i := by
  classical
  cases nonempty_fintype ι
  have aux (s : Finset ι) : ∃ ε : ℝ, 0 < ε ∧ ∀ i ∈ s, ε ≤ f i := by
    induction s using Finset.induction_on with
    | empty => exact ⟨1,by norm_num,by simp⟩
    | @insert a s ha ih =>
      obtain ⟨ε,hε,hh⟩ := ih
      refine ⟨min (f a) ε,lt_min (hf a) hε,?_⟩
      intro i hi
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact min_le_left _ _
      · exact (min_le_right _ _).trans (hh i hi)
  obtain ⟨ε,hε,hh⟩ := aux Finset.univ
  exact ⟨ε,hε,fun i => hh i (Finset.mem_univ i)⟩

/-- All finitely many incident simple radial germs can use the same arbitrarily
small round collar radius; each retains its own exact exit parameter. -/
theorem finite_paths_common_radial_collars {ι : Type*} [Finite ι]
    (x y : ι → ℂ) (p : ∀ i, Path (x i) (y i))
    (hinj : ∀ i, Function.Injective (p i))
    (τ : ι → unitInterval) (hτ : ∀ i, 0 < τ i) (v : ι → ℂ)
    (hgerm : ∀ i (t : unitInterval), t ≤ τ i → p i t = x i + (t : ℝ) • v i) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ →
      ∀ i, ∃ a : unitInterval, 0 < a ∧ a < τ i ∧ dist (p i a) (x i) = ε ∧
        ∀ t : unitInterval, dist (p i t) (x i) < ε ↔ t < a := by
  classical
  have hex i := path_radial_collar_radii (p i) (hinj i) (τ i) (hτ i) (v i)
    (path_radial_germ_ne_zero (p i) (hinj i) (τ i) (hτ i) (v i) (hgerm i)) (hgerm i)
  choose δ hδ hd using hex
  obtain ⟨ε,hε,he⟩ := finite_positive_lower_bound δ hδ
  exact ⟨ε,hε,fun r hr hre i => hd i r hr (hre.trans_le (he i))⟩

end
end MatchgateWidth
