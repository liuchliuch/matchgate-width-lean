import MatchgateWidth.PolygonalTransverseBisector
import MatchgateWidth.SimplePolygonalRouting

/-! # Positive transverse sections exist at every simple polygon vertex -/
namespace MatchgateWidth
noncomputable section

/-- The left-normal direction is positive transverse to a nonzero tangent. -/
theorem orientedArea_leftNormal_pos {a : ℂ} (ha : a ≠ 0) :
    0 < orientedArea a (Complex.I * a) := by
  have he : orientedArea a (Complex.I * a) = ‖a‖^2 := by
    rw [← Complex.normSq_eq_norm_sq]
    simp [orientedArea, Complex.normSq_apply]
  rw [he]
  exact sq_pos_of_pos (norm_pos_iff.mpr ha)

/-- Every vertex of an indexed simple polygon has a vector simultaneously
positive transverse to all incident forward tangents. Interior vectors are
explicit bisectors; endpoint vectors are left normals. -/
theorem exists_vertex_transverse {n : ℕ} (p : Fin (n+1) → ℂ)
    (hne : ∀ i : Fin n, p i.castSucc ≠ p i.succ)
    (hadj : ∀ i j : Fin n, i.val + 1 = j.val →
      segment ℝ (p i.castSucc) (p i.succ) ∩ segment ℝ (p j.castSucc) (p j.succ) ⊆ {p i.succ})
    (j : Fin (n+1)) : ∃ w : ℂ,
      (∀ i : Fin n, i.castSucc = j → 0 < orientedArea (p i.succ - p i.castSucc) w) ∧
      (∀ i : Fin n, i.succ = j → 0 < orientedArea (p i.succ - p i.castSucc) w) := by
  classical
  by_cases hn : n = 0
  · subst n
    exact ⟨0,fun i => i.elim0,fun i => i.elim0⟩
  have hn0 : 0 < n := Nat.pos_of_ne_zero hn
  by_cases hj0 : j.val = 0
  · let e : Fin n := ⟨0,hn0⟩
    refine ⟨Complex.I * (p e.succ - p e.castSucc), ?_, ?_⟩
    · intro i hi
      have hie : i = e := Fin.ext (by have hv := congrArg Fin.val hi; simpa [e,hj0] using hv)
      subst i
      exact orientedArea_leftNormal_pos (sub_ne_zero.mpr (hne e).symm)
    · intro i hi
      have hv := congrArg Fin.val hi
      simp only [Fin.val_succ] at hv
      omega
  by_cases hjn : j.val = n
  · let e : Fin n := ⟨n-1,by omega⟩
    refine ⟨Complex.I * (p e.succ - p e.castSucc), ?_, ?_⟩
    · intro i hi
      have hv := congrArg Fin.val hi
      simp only [Fin.val_castSucc] at hv
      omega
    · intro i hi
      have hie : i = e := Fin.ext (by have hv := congrArg Fin.val hi; dsimp [e]; simp only [Fin.val_succ] at hv; omega)
      subst i
      exact orientedArea_leftNormal_pos (sub_ne_zero.mpr (hne e).symm)
  have hjpos : 0 < j.val := Nat.pos_of_ne_zero hj0
  have hjlt : j.val < n := by omega
  let a : Fin n := ⟨j.val-1,by omega⟩
  let b : Fin n := ⟨j.val,hjlt⟩
  have hab : a.val+1=b.val := by dsimp [a,b]; omega
  have has : a.succ = j := Fin.ext (by dsimp [a]; omega)
  have hbc : b.castSucc = j := rfl
  have hc : p b.castSucc = p a.succ := congrArg p (hbc.trans has.symm)
  have hcorner := hadj a b hab
  rw [hc] at hcorner
  have hbis : tangentBisector (p a.succ - p a.castSucc) (p b.succ - p a.succ) ≠ 0 := by
    apply norm_smul_add_norm_smul_ne_zero_of_corner (hne a)
    · simpa only [hc] using hne b
    · exact hcorner
  have ht := transverseBisector_positive (sub_ne_zero.mpr (hne a).symm)
    (sub_ne_zero.mpr (show p a.succ ≠ p b.succ by simpa only [hc] using hne b).symm) hbis
  refine ⟨transverseBisector (p a.succ-p a.castSucc) (p b.succ-p a.succ), ?_, ?_⟩
  · intro i hi
    have hib : i = b := Fin.castSucc_injective n (hi.trans hbc.symm)
    subst i
    simpa only [hc] using ht.2
  · intro i hi
    have hia : i = a := Fin.succ_injective n (hi.trans has.symm)
    subst i
    exact ht.1

/-- A simultaneous transverse-vector choice for every vertex of a finite
simple polygon, including an empty edge family. -/
theorem exists_positive_polygonal_sections {n : ℕ} (p : Fin (n+1) → ℂ)
    (hne : ∀ i : Fin n, p i.castSucc ≠ p i.succ)
    (hadj : ∀ i j : Fin n, i.val + 1 = j.val →
      segment ℝ (p i.castSucc) (p i.succ) ∩ segment ℝ (p j.castSucc) (p j.succ) ⊆ {p i.succ}) :
    ∃ w : Fin (n+1) → ℂ,
      (∀ i : Fin n, 0 < orientedArea (p i.succ-p i.castSucc) (w i.castSucc)) ∧
      (∀ i : Fin n, 0 < orientedArea (p i.succ-p i.castSucc) (w i.succ)) := by
  classical
  choose w hw using exists_vertex_transverse p hne hadj
  exact ⟨w,fun i => (hw i.castSucc).1 i rfl,fun i => (hw i.succ).2 i rfl⟩

end
end MatchgateWidth
