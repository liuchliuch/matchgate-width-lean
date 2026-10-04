import MatchgateWidth.EffectiveIntegerObstruction

/-!
# Executable regressions for rational obstruction certificates

These deliberately test arithmetic and certificate checking, not the astronomically
slow unbounded table search. The ordinary Lean evaluator is used; no native_decide
or additional axiom is involved in any theorem.
-/

namespace MatchgateWidth.Effective

/-- Zero-width chart with all discrete signs positive. -/
def zeroWidthTestChart : StarChartChoice 2 0 :=
  ((fun _ => ((fun i => Fin.elim0 i), fun _ => 0)),
   ((fun i => Fin.elim0 i), fun _ => 0))

/-- info: 5 -/
#guard_msgs in
#eval Polynomial.eval₂ (RingHom.id ℚ) (fun _ : Fin 1 => 3)
  ((Polynomial.X 0 + Polynomial.C 2) * (Polynomial.X 0 - Polynomial.C 2))

/-- info: true -/
#guard_msgs in
#eval decide (IsRelation zeroWidthTestChart (minor (0 : Fin 2)))

/-- info: false -/
#guard_msgs in
#eval decide (IsRelation zeroWidthTestChart (Polynomial.C 1))

/-- info: false -/
#guard_msgs in
#eval decide (IsRelation zeroWidthTestChart 0)

/-- info: 1 -/
#guard_msgs in
#eval integerTableForArity 0 (fun i => Fin.elim0 i)


end MatchgateWidth.Effective
