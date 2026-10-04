import MatchgateWidth.PfaffianIdentities
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Guard against an invalid untyped block-contraction rule

Two explicit four-mode Pfaffian tensors satisfy the literal MGI, but their
ordinary same-order two-wire block contraction does not. This is NOT a
counterexample to a numbered paper theorem: no qutrit or deficient-port
hypotheses are asserted. It guards against silently replacing ordered
planar composition by an unrestricted raw block contraction.
-/

namespace MatchgateWidth

/-- First exact integer skew matrix. -/
def orderMatrixA : Matrix (Fin 4) (Fin 4) ℚ :=
  ![![0,-1,-2,0], ![1,0,2,-1], ![2,-2,0,2], ![0,1,-2,0]]

/-- Second exact integer skew matrix. -/
def orderMatrixB : Matrix (Fin 4) (Fin 4) ℚ :=
  ![![0,1,0,-2], ![-1,0,-2,1], ![0,2,0,-2], ![2,-1,2,0]]

def orderSelected (x : BooleanInput 4) : List (Fin 4) :=
  (List.finRange 4).filter (fun i => decide (x i = 1))

theorem orderSelected_eq (x : BooleanInput 4) : orderSelected x = pfaffianSelectedPorts x := by
  have hn : (orderSelected x).Nodup := (List.nodup_finRange 4).filter _
  have hp : (orderSelected x).Pairwise (· ≤ ·) := (List.pairwise_le_finRange 4).filter _
  have he : (orderSelected x).toFinset = Finset.univ.filter (fun i => x i = 1) := by
    ext i
    simp [orderSelected]
  symm
  rw [pfaffianSelectedPorts, ← he]
  exact (List.toFinset_sort (· ≤ ·) hn).mpr hp

def orderGateA (x : BooleanInput 4) : ℚ := pfaffianList orderMatrixA (orderSelected x)
def orderGateB (x : BooleanInput 4) : ℚ := pfaffianList orderMatrixB (orderSelected x)

theorem orderGateA_mgi : BooleanMatchgateIdentities orderGateA := by
  have h := principalPfaffian_matchgateIdentities orderMatrixA (by intro i j; fin_cases i <;> fin_cases j <;> norm_num [orderMatrixA, orderMatrixB]) (by intro i; fin_cases i <;> norm_num [orderMatrixA, orderMatrixB])
  change MatchgateIdentities (fun S => orderGateA ((booleanSubsetEquiv 4).symm S))
  convert h using 1
  funext S
  simp [orderGateA, orderSelected_eq, pfaffianSelectedPorts, principalPfaffian, booleanSubsetEquiv]

theorem orderGateB_mgi : BooleanMatchgateIdentities orderGateB := by
  have h := principalPfaffian_matchgateIdentities orderMatrixB (by intro i j; fin_cases i <;> fin_cases j <;> norm_num [orderMatrixA, orderMatrixB]) (by intro i; fin_cases i <;> norm_num [orderMatrixA, orderMatrixB])
  change MatchgateIdentities (fun S => orderGateB ((booleanSubsetEquiv 4).symm S))
  convert h using 1
  funext S
  simp [orderGateB, orderSelected_eq, pfaffianSelectedPorts, principalPfaffian, booleanSubsetEquiv]

/-- Both independently summed bits have the same order at the two tensor blocks. -/
def rawSameOrderContraction (x : BooleanInput 4) : ℚ :=
  ∑ u : Fin 2, ∑ v : Fin 2,
    orderGateA ![x 0,x 1,u,v] * orderGateB ![u,v,x 2,x 3]

def rawContractionFourModeResidual : ℚ :=
  rawSameOrderContraction ![0,0,0,0] * rawSameOrderContraction ![1,1,1,1] -
  rawSameOrderContraction ![1,1,0,0] * rawSameOrderContraction ![0,0,1,1] +
  rawSameOrderContraction ![1,0,1,0] * rawSameOrderContraction ![0,1,0,1] -
  rawSameOrderContraction ![1,0,0,1] * rawSameOrderContraction ![0,1,1,0]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem rawContractionFourModeResidual_value : rawContractionFourModeResidual = -16 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- A concrete defining MGI has nonzero value 16. -/
theorem rawContraction_mgi_witness :
    matchgateSum (fun S => rawSameOrderContraction ((booleanSubsetEquiv 4).symm S))
      {0} {1,2,3} [0,1,2,3] = 16 := by
  decide +kernel

theorem rawSameOrderContraction_not_mgi :
    ¬ BooleanMatchgateIdentities rawSameOrderContraction := by
  intro h
  have hm := h {0} {1,2,3}
  have hs : (symmDiff ({0} : Finset (Fin 4)) {1,2,3}).sort (· ≤ ·) = [0,1,2,3] := by
    have he : symmDiff ({0} : Finset (Fin 4)) {1,2,3} = Finset.univ := by
      ext i
      fin_cases i <;> simp [Finset.mem_symmDiff]
    rw [he, Fin.sort_univ]
    decide
  rw [hs, rawContraction_mgi_witness] at hm
  norm_num at hm

/-- Two-wire block flattening of the first tensor; both indices are in lexicographic order. -/
def orderGateA_blockMatrix : Matrix (Fin 4) (Fin 4) ℚ :=
  fun i j => orderGateA ![(finProdFinEquiv.symm i : Fin 2 × Fin 2).1,
    (finProdFinEquiv.symm i : Fin 2 × Fin 2).2,
    (finProdFinEquiv.symm j : Fin 2 × Fin 2).1,
    (finProdFinEquiv.symm j : Fin 2 × Fin 2).2]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem orderGateA_blockMatrix_det : orderGateA_blockMatrix.det = -4 := by
  decide +kernel

/-- The example has block rank four, so it is outside the qutrit deficient-port setting. -/
theorem orderGateA_blockMatrix_rank : orderGateA_blockMatrix.rank = 4 := by
  have hd : orderGateA_blockMatrix.det ≠ 0 := by rw [orderGateA_blockMatrix_det]; norm_num
  simpa using Matrix.rank_of_det_ne_zero hd

end MatchgateWidth
