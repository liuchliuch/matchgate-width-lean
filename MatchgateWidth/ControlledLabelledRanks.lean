import MatchgateWidth.ControlledLabelledPresentation

/-! # Source port-order preservation of all controlled ranks
Only the enumeration of the port type changes. Flattenings are identified by
an explicit bijection of their complementary assignments, not a matchgate
closure claim under arbitrary Boolean-wire permutations.
-/
namespace MatchgateWidth
noncomputable section
open scoped Classical
set_option maxHeartbeats 1200000

/-- Exact flattening-rank invariance under a bijection of domain ports. -/
theorem portFlatten_rank_relabel {I J D K : Type*} [Field K]
    [Fintype I] [Fintype J] [Fintype D] [DecidableEq I] [DecidableEq J]
    (e : J ≃ I) (T : (I → D) → K) (p : J) :
    (portFlatten (fun x : J → D => T (x ∘ e.symm)) p).rank =
      (portFlatten T (e p)).rank := by
  let c : {i : J // i ≠ p} ≃ {i : I // i ≠ e p} := {
    toFun := fun i => ⟨e i, fun h => i.2 (e.injective h)⟩
    invFun := fun i => ⟨e.symm i, fun h => i.2 (by simpa using congrArg e h)⟩
    left_inv := by intro i; ext; simp
    right_inv := by intro i; ext; simp }
  let a := Equiv.arrowCongr c (Equiv.refl D)
  have he : portFlatten (fun x : J → D => T (x ∘ e.symm)) p =
      (portFlatten T (e p)).submatrix (Equiv.refl D) a := by
    ext d z
    apply congrArg T
    funext i
    by_cases hi : i = e p
    · subst i
      simp []
    · have hpi : e.symm i ≠ p := fun h => hi (by simpa using congrArg e h)
      simp [ Function.comp_def,  insertBoundaryCoordinate,
        hi, hpi, a, c, Equiv.arrowCongr]
  rw [he, Matrix.rank_submatrix]

/-- The semantic source order: link zero, link one, then the hard ports. -/
def controlledLabelledPortEquiv (k : ℕ) : Fin (k + 2) ≃ ControlledQutritPort k where
  toFun := controlledLabelledPort k
  invFun := Sum.elim (fun l => if l = 0 then 0 else 1) (fun i => i.succ.succ)
  left_inv p := by
    induction p using Fin.cases with
    | zero => simp [controlledLabelledPort]
    | succ p =>
      induction p using Fin.cases with
      | zero => simp [controlledLabelledPort]
      | succ p => simp [controlledLabelledPort]
  right_inv p := by
    cases p with
    | inl l => fin_cases l <;> simp [controlledLabelledPort]
    | inr i => simp [controlledLabelledPort]

/-- Literal equality of ordered and semantically named assignments. -/
theorem orderedControlledQutrit_eq_relabel {k : ℕ} (f : BooleanTable k ℂ) (j : Fin k) :
    orderedControlledQutrit f j = fun x =>
      controlledQutrit f j (x ∘ (controlledLabelledPortEquiv k).symm) := by
  funext x
  apply congrArg (controlledQutrit f j)
  funext p
  cases p with
  | inl l => fin_cases l <;> rfl
  | inr i => rfl

theorem orderedControlledQutrit_port_rank {k : ℕ} (f : BooleanTable k ℂ)
    (hf : ∀ x, f x ≠ 0) (j : Fin k)
    (hrank : ∀ i, (oneVsRestFlattening f i).rank = 2) (p : Fin (k + 2)) :
    (portFlatten (orderedControlledQutrit f j) p).rank = 2 := by
  rw [orderedControlledQutrit_eq_relabel]
  have he := portFlatten_rank_relabel (controlledLabelledPortEquiv k) (controlledQutrit f j) p
  have hr := controlledQutrit_all_port_ranks f j (hf _) hrank ((controlledLabelledPortEquiv k) p)
  exact he.trans hr

end
end MatchgateWidth
