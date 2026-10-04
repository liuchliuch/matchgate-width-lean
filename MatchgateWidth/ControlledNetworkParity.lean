import MatchgateWidth.NetworkParity
import MatchgateWidth.AlgebraicQutritLanguage

/-! # The controlled language conserves the marker-state parity
This is a direct domain-network invariant, independent of any Boolean gadget
lifting or planar graph necessity theorem.
-/
namespace MatchgateWidth
noncomputable section
open scoped Classical

/-- Only qutrit state one has odd marker parity. -/
def qutritMarkerParity (d : Fin 3) : ZMod 2 := if d = 1 then 1 else 0

def controlledLabelParity : ControlledLanguageLabel → ZMod 2
  | .pin d => qutritMarkerParity d
  | .neq => 1
  | .controlled => 0

variable {K : Type*} [Field K] {k : ℕ}

theorem qutritPinTensor_hasParity (d : Fin 3) :
    TensorHasParity qutritMarkerParity (qutritPinTensor (K := K) d) (qutritMarkerParity d) := by
  intro a ha
  have he : a 0 = d := by
    by_contra h
    exact ha (by simp [qutritPinTensor, h])
  simpa using congrArg qutritMarkerParity he

theorem qutritNeqTensor_hasParity :
    TensorHasParity qutritMarkerParity (qutritNeqTensor (K := K)) 1 := by
  intro a ha
  have h : (a 0 = 0 ∧ a 1 = 1) ∨ (a 0 = 1 ∧ a 1 = 0) := by
    by_contra h
    exact ha (by simp [qutritNeqTensor, h])
  rw [Fin.sum_univ_two]
  rcases h with h | h <;> simp [qutritMarkerParity, h.1, h.2]

theorem controlledQutrit_hasParity (f : BooleanTable k K) (j : Fin k) :
    TensorHasParity qutritMarkerParity (controlledQutrit f j) 0 := by
  intro a ha
  change (∑ i : Fin 2 ⊕ Fin k, qutritMarkerParity (a i)) = 0
  rw [Fintype.sum_sum_type]
  have h2 : (2 : ZMod 2) = 0 := by decide
  unfold controlledQutrit at ha
  split_ifs at ha with hh h00 h11
  · have hhard : ∑ i : Fin k, qutritMarkerParity (a (Sum.inr i)) = 0 :=
      Finset.sum_eq_zero (fun i _ => by simp [qutritMarkerParity, hh i])
    rw [hhard, Fin.sum_univ_two]
    simp [qutritMarkerParity, h00.1, h00.2]
  · have hhard : ∑ i : Fin k, qutritMarkerParity (a (Sum.inr i)) = 0 :=
      Finset.sum_eq_zero (fun i _ => by simp [qutritMarkerParity, hh i])
    rw [hhard, Fin.sum_univ_two]
    simp [qutritMarkerParity, h11.1, h11.2]
    exact h2
  · exact (ha rfl).elim
  · exact (ha rfl).elim

theorem controlledLanguageTensor_hasParity (f : BooleanTable k K) (j : Fin k)
    (l : ControlledLanguageLabel) :
    TensorHasParity qutritMarkerParity (controlledLanguageTensor f j l) (controlledLabelParity l) := by
  cases l with
  | pin d => exact qutritPinTensor_hasParity d
  | neq => exact qutritNeqTensor_hasParity
  | controlled => exact controlledQutrit_hasParity f j

/-- Every properly wired gadget over the actual controlled primitive tensors
has a fixed marker parity. Planarity is unnecessary for this invariant. -/
theorem controlled_network_hasParity {V E P : Type*} [Fintype V] [Fintype E] [Fintype P]
    (labels : V → ControlledLanguageLabel)
    (inc : ∀ v, controlledLanguagePorts k (labels v) → E ⊕ P)
    (hinc : ProperNetworkIncidences inc) (f : BooleanTable k K) (j : Fin k) :
    TensorHasParity qutritMarkerParity
      (networkValue inc (fun v => controlledLanguageTensor f j (labels v)))
      (∑ v, controlledLabelParity (labels v)) :=
  networkValue_hasParity inc hinc qutritMarkerParity _ _
    (fun v => controlledLanguageTensor_hasParity f j (labels v))

end
end MatchgateWidth
