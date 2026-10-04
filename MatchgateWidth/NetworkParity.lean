import MatchgateWidth.TensorNetwork
import Mathlib.Data.ZMod.Basic

/-! # Parity conservation in actual finite tensor networks -/
namespace MatchgateWidth
noncomputable section
open scoped Classical
variable {K V E P D : Type*} {I : V → Type*}
  [Field K] [Fintype V] [Fintype E] [Fintype P] [Fintype D]
  [∀ v, Fintype (I v)]

/-- Every internal edge has two incidences and every exposed edge one. -/
def ProperNetworkIncidences (inc : ∀ v, I v → E ⊕ P) : Prop :=
  (∀ e : E, (Finset.univ.filter (fun a : Sigma I => inc a.1 a.2 = Sum.inl e)).card = 2) ∧
  (∀ p : P, (Finset.univ.filter (fun a : Sigma I => inc a.1 a.2 = Sum.inr p)).card = 1)

/-- The total local parity equals the boundary parity; every internal label
occurs twice and cancels in ZMod 2. -/
theorem network_incidence_parity (inc : ∀ v, I v → E ⊕ P)
    (hinc : ProperNetworkIncidences inc) (χ : D → ZMod 2) (e : E → D) (b : P → D) :
    (∑ v, ∑ i, χ (Sum.elim e b (inc v i))) = ∑ p, χ (b p) := by
  rw [← Fintype.sum_sigma']
  have h := Finset.sum_fiberwise' (Finset.univ : Finset (Sigma I))
    (fun a => inc a.1 a.2) (fun w => χ (Sum.elim e b w))
  rw [← h]
  simp only [Finset.sum_const, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
  have h2 : (2 : ZMod 2) = 0 := by decide
  simp [hinc.1, hinc.2, nsmul_eq_mul, h2]

/-- A tensor with a fixed parity of its nonzero coordinates. -/
def TensorHasParity {J : Type*} [Fintype J] (χ : D → ZMod 2)
    (T : (J → D) → K) (ε : ZMod 2) : Prop :=
  ∀ x, T x ≠ 0 → ∑ j, χ (x j) = ε

/-- Actual network contraction preserves parity, without any planarity or
matchgate premise. -/
theorem networkValue_hasParity (inc : ∀ v, I v → E ⊕ P)
    (hinc : ProperNetworkIncidences inc) (χ : D → ZMod 2)
    (T : ∀ v, (I v → D) → K) (ε : V → ZMod 2)
    (hT : ∀ v, TensorHasParity χ (T v) (ε v)) :
    TensorHasParity χ (networkValue inc T) (∑ v, ε v) := by
  intro b hb
  obtain ⟨e,he⟩ : ∃ e : E → D, (∏ v, T v (fun i => Sum.elim e b (inc v i))) ≠ 0 := by
    by_contra h
    push Not at h
    apply hb
    exact Finset.sum_eq_zero (fun e _ => h e)
  have hlocal (v : V) :
      ∑ i, χ (Sum.elim e b (inc v i)) = ε v := by
    apply hT v
    exact (Finset.prod_ne_zero_iff.mp he) v (Finset.mem_univ v)
  rw [← network_incidence_parity inc hinc χ e b]
  exact Finset.sum_congr rfl (fun v _ => hlocal v)

end
end MatchgateWidth
