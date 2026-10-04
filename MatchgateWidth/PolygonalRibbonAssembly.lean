import MatchgateWidth.PolygonalRibbonNeighborhoods

/-! # Finite noncrossing polygonal ribbon assembly

The route specifies its original polygon vertices, transverse sections, and
open segment carriers separated only for nonadjacent segments. A positive
uniform width is derived. Every pair of different wire lanes is then disjoint
throughout the whole route, by the same-strip, adjacent-strip, or separated-
carrier argument. No whole-output drawing or disjoint-lane premise is used.
-/
namespace MatchgateWidth
noncomputable section

/-- Original finite route data, before any parallel wires are drawn. -/
structure TransversePolygonalRoute (n : ℕ) where
  vertex : Fin (n+1) → ℂ
  transverse : Fin (n+1) → ℂ
  carrier : Fin n → Set ℂ
  carrier_open : ∀ i, IsOpen (carrier i)
  center_mem : ∀ i, Set.range (straightArc (vertex i.castSucc) (vertex i.succ)) ⊆ carrier i
  carrier_disjoint : ∀ i j, i.val + 1 < j.val ∨ j.val + 1 < i.val →
    Disjoint (carrier i) (carrier j)
  start_positive : ∀ i : Fin n, 0 < orientedArea (vertex i.succ - vertex i.castSucc) (transverse i.castSucc)
  end_positive : ∀ i : Fin n, 0 < orientedArea (vertex i.succ - vertex i.castSucc) (transverse i.succ)

namespace TransversePolygonalRoute
variable {n : ℕ} (R : TransversePolygonalRoute n)

def edge (δ : ℝ) (i : Fin n) : unitInterval → ℂ :=
  ribbonArc (R.vertex i.castSucc) (R.vertex i.succ)
    (R.transverse i.castSucc) (R.transverse i.succ) δ

/-- A geometric property of one width, involving only explicit segment
positions, determinant inequalities, and carrier containment. -/
def Width (ε : ℝ) : Prop := ∀ δ : ℝ, |δ| < ε → ∀ i : Fin n,
  (0 < orientedArea (ribbonDirection (R.vertex i.castSucc) (R.vertex i.succ)
    (R.transverse i.castSucc) (R.transverse i.succ) δ) (R.transverse i.castSucc)) ∧
  (0 < orientedArea (ribbonDirection (R.vertex i.castSucc) (R.vertex i.succ)
    (R.transverse i.castSucc) (R.transverse i.succ) δ) (R.transverse i.succ)) ∧
  Set.range (R.edge δ i) ⊆ R.carrier i

theorem exists_width : ∃ ε : ℝ, 0 < ε ∧ R.Width ε :=
  finite_ribbon_segment_radius (fun i : Fin n => R.vertex i.castSucc) (fun i : Fin n => R.vertex i.succ)
    (fun i : Fin n => R.transverse i.castSucc) (fun i : Fin n => R.transverse i.succ)
    R.carrier R.carrier_open R.center_mem R.start_positive R.end_positive

/-- Each individual edge in every admissible lane is continuous and simple. -/
theorem edge_injective {ε δ : ℝ} (hε : R.Width ε) (hδ : |δ| < ε) (i : Fin n) :
    Function.Injective (R.edge δ i) :=
  ribbonArc_injective _ _ _ _ δ (hε δ hδ i).1

theorem edge_continuous (δ : ℝ) (i : Fin n) : Continuous (R.edge δ i) :=
  continuous_ribbonArc _ _ _ _ _

/-- Nonadjacent segments of any two permitted lanes stay in disjoint carriers. -/
theorem nonadjacent_disjoint {ε δ η : ℝ} (hε : R.Width ε)
    (hδ : |δ| < ε) (hη : |η| < ε) (i j : Fin n)
    (hij : i.val + 1 < j.val ∨ j.val + 1 < i.val) :
    Disjoint (Set.range (R.edge δ i)) (Set.range (R.edge η j)) :=
  (R.carrier_disjoint i j hij).mono (hε δ hδ i).2.2 (hε η hη j).2.2

/-- Consecutive segment indices use literally the same intervening section. -/
theorem adjacent_eq_iff {ε δ η : ℝ} (hε : R.Width ε)
    (hδ : |δ| < ε) (hη : |η| < ε) (i j : Fin n)
    (hij : i.val + 1 = j.val) (s t : unitInterval) :
    R.edge δ i s = R.edge η j t ↔ s = 1 ∧ t = 0 ∧ δ = η := by
  have he : i.succ = j.castSucc := Fin.ext hij
  have h1 := (hε δ hδ i).2.1
  have h2 := (hε η hη j).1
  unfold edge
  rw [← he] at h2 ⊢
  exact ribbonArc_adjacent_eq_iff _ _ _ _ _ _ _ _ h1 h2 s t

/-- A point shared by any two edge pieces must belong to the same wire lane.
This explicitly handles both possible orientations of an adjacent edge pair. -/
theorem eq_offset_of_common_point {ε δ η : ℝ} (hε : R.Width ε)
    (hδ : |δ| < ε) (hη : |η| < ε) (i j : Fin n) (s t : unitInterval)
    (h : R.edge δ i s = R.edge η j t) : δ = η := by
  by_cases hij : i = j
  · subst j
    exact ((ribbonArc_eq_iff _ _ _ _ (hε δ hδ i).1 (hε δ hδ i).2.1
      (hε η hη i).1 (hε η hη i).2.1 s t).mp h).1
  · by_cases ha : i.val + 1 = j.val
    · exact ((R.adjacent_eq_iff hε hδ hη i j ha s t).mp h).2.2
    · by_cases hb : j.val + 1 = i.val
      · exact ((R.adjacent_eq_iff hε hη hδ j i hb t s).mp h.symm).2.2.symm
      · have hfar : i.val + 1 < j.val ∨ j.val + 1 < i.val := by
          have hne : i.val ≠ j.val := fun he => hij (Fin.ext he)
          omega
        exact (Set.disjoint_left.mp (R.nonadjacent_disjoint hε hδ hη i j hfar)
          ⟨s,rfl⟩ ⟨t,h.symm⟩).elim

/-- The complete geometric support of one finite polygonal wire. -/
def laneSupport (δ : ℝ) : Set ℂ := ⋃ i : Fin n, Set.range (R.edge δ i)

/-- Distinct wires are disjoint across every segment and every corner of the
finite route, with one radius chosen uniformly for all lanes. -/
theorem lanes_disjoint {ε δ η : ℝ} (hε : R.Width ε)
    (hδ : |δ| < ε) (hη : |η| < ε) (hne : δ ≠ η) :
    Disjoint (R.laneSupport δ) (R.laneSupport η) := by
  apply Set.disjoint_left.mpr
  intro z hzδ hzη
  obtain ⟨i,s,hs⟩ := Set.mem_iUnion.mp hzδ
  obtain ⟨j,t,ht⟩ := Set.mem_iUnion.mp hzη
  exact hne (R.eq_offset_of_common_point hε hδ hη i j s t (hs.trans ht.symm))

/-- At arbitrary finite wire count, every injectively chosen list of small
offsets gives a family of pairwise-disjoint complete wire supports. -/
theorem finite_parallel_lanes {k : ℕ} {ε : ℝ} (hε : R.Width ε)
    (δ : Fin k → ℝ) (hinj : Function.Injective δ) (hδ : ∀ i, |δ i| < ε) :
    Pairwise (fun i j => Disjoint (R.laneSupport (δ i)) (R.laneSupport (δ j))) := by
  intro i j hij
  exact R.lanes_disjoint hε (hδ i) (hδ j) (fun he => hij (hinj he))

/-- Explicit increasing offsets for any finite wire count, all strictly
inside the permitted positive side of the common ribbon width. -/
def laneOffset (ε : ℝ) (k : ℕ) (i : Fin k) : ℝ := ε * ((i.val + 1) / (k + 1))

theorem laneOffset_bounds {ε : ℝ} (hε : 0 < ε) {k : ℕ} (i : Fin k) :
    0 < laneOffset ε k i ∧ |laneOffset ε k i| < ε := by
  have hd : (0 : ℝ) < k + 1 := by positivity
  have hi : (i.val : ℝ) < k := by exact_mod_cast i.isLt
  have hp : 0 < ((i.val : ℝ) + 1) / (k + 1) := div_pos (by positivity) hd
  have hl : ((i.val : ℝ) + 1) / (k + 1) < 1 := (div_lt_one hd).mpr (by linarith)
  have ho : 0 < laneOffset ε k i := mul_pos hε hp
  refine ⟨ho, ?_⟩
  rw [abs_of_pos ho]
  exact (mul_lt_mul_of_pos_left hl hε).trans_eq (mul_one ε)

theorem laneOffset_strictMono {ε : ℝ} (hε : 0 < ε) (k : ℕ) :
    StrictMono (laneOffset ε k) := by
  intro i j hij
  have h : (i.val : ℝ) < j.val := by exact_mod_cast hij
  apply mul_lt_mul_of_pos_left _ hε
  exact (div_lt_div_iff_of_pos_right (by positivity : (0 : ℝ) < k+1)).mpr (by linarith)

/-- The finite parallel bundle exists at every requested wire count, with
explicit endpoints p_i+δ_j w_i and no added crossings at polygonal bends. -/
theorem exists_finite_parallel_bundle (k : ℕ) :
    ∃ ε : ℝ, 0 < ε ∧ R.Width ε ∧
      Pairwise (fun i j : Fin k => Disjoint
        (R.laneSupport (laneOffset ε k i)) (R.laneSupport (laneOffset ε k j))) := by
  obtain ⟨ε,hε,hwidth⟩ := R.exists_width
  exact ⟨ε,hε,hwidth,R.finite_parallel_lanes hwidth (laneOffset ε k)
    (laneOffset_strictMono hε k).injective (fun i => (laneOffset_bounds hε i).2)⟩

end TransversePolygonalRoute
end
end MatchgateWidth
