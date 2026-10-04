import MatchgateWidth.PfaffianEdgeUpdate
import MatchgateWidth.ElementaryPlanarGates

/-!
# Nearest-neighbor synthesis of principal Pfaffian tables

The circuit gates below act on occupied subsets. Swaps carry the fermionic
minus sign on double occupancy. Circuit correctness refers to the recursive
principal Pfaffian, and makes no topological or realizability assumption.
-/
namespace MatchgateWidth

variable {R : Type*} [CommRing R] {s : ℕ}

/-- Exchange two coordinate names in both indices of a matrix. -/
def pfaffianSwapMatrix (A : Matrix (Fin s) (Fin s) R) (i j : Fin s) :
    Matrix (Fin s) (Fin s) R :=
  fun x y => A (Equiv.swap i j x) (Equiv.swap i j y)

theorem pfaffianSwapMatrix_skew (A : Matrix (Fin s) (Fin s) R)
    (hA : ∀ x y, A x y = -A y x) (i j : Fin s) :
    ∀ x y, pfaffianSwapMatrix A i j x y = -pfaffianSwapMatrix A i j y x :=
  fun x y => hA (Equiv.swap i j x) (Equiv.swap i j y)

omit [CommRing R] in
@[simp] theorem pfaffianSwapMatrix_twice (A : Matrix (Fin s) (Fin s) R)
    (i j : Fin s) : pfaffianSwapMatrix (pfaffianSwapMatrix A i j) i j = A := by
  funext x y
  simp [pfaffianSwapMatrix]

/-- Occupied-subset action of the actual signed crossover transfer matrix. -/
def pfaffianSignedSwap (i j : Fin s) (F : SubsetSignature s R) :
    SubsetSignature s R := fun S =>
  (if i ∈ S ∧ j ∈ S then -1 else 1) * F (S.image (Equiv.swap i j))

private theorem swap_sort_fixed (i j : Fin s) (T : Finset (Fin s))
    (hi : i ∉ T) (hj : j ∉ T) :
    (T.sort (· ≤ ·)).map (Equiv.swap i j) = T.sort (· ≤ ·) := by
  conv_rhs => rw [← List.map_id' (T.sort (· ≤ ·))]
  apply List.map_congr_left
  intro x hx
  have hxT : x ∈ T := by simpa using hx
  exact Equiv.swap_apply_of_ne_of_ne (fun h => hi (h ▸ hxT))
    (fun h => hj (h ▸ hxT))

private theorem swap_image_fixed (i j : Fin s) (T : Finset (Fin s))
    (hi : i ∉ T) (hj : j ∉ T) : T.image (Equiv.swap i j) = T := by
  conv_rhs => rw [← Finset.image_id (s := T)]
  apply Finset.image_congr
  intro x hx
  exact Equiv.swap_apply_of_ne_of_ne (fun h => hi (h ▸ hx))
    (fun h => hj (h ▸ hx))

private theorem adjacent_filter_eq (i j : Fin s) (hij : j.val = i.val + 1)
    (T : Finset (Fin s)) (hi : i ∉ T) :
    T.filter (· < i) = T.filter (· < j) := by
  ext x
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hx, hxi⟩
    exact ⟨hx, lt_trans hxi (by omega)⟩
  · rintro ⟨hx, hxj⟩
    have hne : x ≠ i := fun h => hi (h ▸ hx)
    have hnval : x.val ≠ i.val := fun h => hne (Fin.ext h)
    exact ⟨hx, by simp only [Fin.lt_def] at *; omega⟩

private theorem pfaffian_swap_single_insert (A : Matrix (Fin s) (Fin s) R)
    (hA : ∀ x y, A x y = -A y x) (i j : Fin s)
    (T : Finset (Fin s)) (hi : i ∉ T) (hj : j ∉ T)
    (hc : (T.filter (· < i)).card = (T.filter (· < j)).card) :
    principalPfaffian (pfaffianSwapMatrix A i j) (insert i T) =
      principalPfaffian A (insert j T) := by
  have hB := pfaffianList_insert_sort (pfaffianSwapMatrix A i j)
    (pfaffianSwapMatrix_skew A hA i j) T i hi
  have hC := pfaffianList_insert_sort A hA T j hj
  have he : pfaffianList (pfaffianSwapMatrix A i j) (i :: T.sort (· ≤ ·)) =
      pfaffianList A (j :: T.sort (· ≤ ·)) := by
    unfold pfaffianSwapMatrix
    rw [← pfaffianList_map]
    simp [swap_sort_fixed i j T hi hj]
  rw [he, hC, ← hc] at hB
  exact ((isUnit_one.neg).pow _).mul_left_cancel hB.symm

/-- Swapping neighboring matrix coordinates is exactly a signed nearest-wire
swap on the entire actual principal-Pfaffian table. -/
theorem principalPfaffian_swap_adjacent (A : Matrix (Fin s) (Fin s) R)
    (hA : ∀ x y, A x y = -A y x) (i j : Fin s)
    (hij : j.val = i.val + 1) :
    principalPfaffian (pfaffianSwapMatrix A i j) =
      pfaffianSignedSwap i j (principalPfaffian A) := by
  have hne : i ≠ j := by intro h; have := congrArg Fin.val h; omega
  have hs (S : Finset (Fin s)) : pfaffianPairCreationSign (R := R) S i j = 1 := by
    apply pfaffianPairCreationSign_of_no_between S (by omega)
    intro k _ hk
    have h₁ := hk.1
    have h₂ := hk.2
    simp only [Fin.lt_def] at h₁ h₂
    omega
  funext S
  by_cases hi : i ∈ S
  · by_cases hj : j ∈ S
    · let T := (S.erase i).erase j
      have hiT : i ∉ T := by simp [T]
      have hjT : j ∉ T := by simp [T]
      have hS : S = insert i (insert j T) := by
        simp [T, Finset.insert_erase (Finset.mem_erase.mpr ⟨hne.symm, hj⟩),
          Finset.insert_erase hi]
      have himage : S.image (Equiv.swap i j) = S := by
        rw [hS]
        simp [swap_image_fixed i j T hiT hjT, Finset.insert_comm]
      have hB := pfaffianList_pair_sort (pfaffianSwapMatrix A i j)
        (pfaffianSwapMatrix_skew A hA i j) S hne hi hj
      have hC := pfaffianList_pair_sort A hA S hne hi hj
      rw [hs S, one_mul] at hB hC
      change pfaffianList (pfaffianSwapMatrix A i j) (i :: j :: T.sort (· ≤ ·)) = _ at hB
      have he : pfaffianList (pfaffianSwapMatrix A i j) (i :: j :: T.sort (· ≤ ·)) =
          -pfaffianList A (i :: j :: T.sort (· ≤ ·)) := by
        unfold pfaffianSwapMatrix
        rw [← pfaffianList_map]
        simp only [List.map_cons, Equiv.swap_apply_left, Equiv.swap_apply_right,
          swap_sort_fixed i j T hiT hjT]
        exact pfaffianList_swap_head A hA j i _
      simp only [pfaffianSignedSwap, hi, hj, and_self, ite_true, himage, neg_one_mul]
      change pfaffianList _ _ = -pfaffianList A _
      rw [← hB, he, hC]
    · let T := S.erase i
      have hiT : i ∉ T := by simp [T]
      have hjT : j ∉ T := by simp [T, hj]
      have hS : S = insert i T := (Finset.insert_erase hi).symm
      rw [hS]
      simpa [pfaffianSignedSwap, hne, hne.symm, hiT, hjT,
        swap_image_fixed i j T hiT hjT] using
        pfaffian_swap_single_insert A hA i j T hiT hjT
          (congrArg Finset.card (adjacent_filter_eq i j hij T hiT))
  · by_cases hj : j ∈ S
    · let T := S.erase j
      have hiT : i ∉ T := by simp [T, hi]
      have hjT : j ∉ T := by simp [T]
      have hS : S = insert j T := (Finset.insert_erase hj).symm
      rw [hS]
      have h := pfaffian_swap_single_insert A hA j i T hjT hiT
        (congrArg Finset.card (adjacent_filter_eq i j hij T hiT)).symm
      have hm : pfaffianSwapMatrix A j i = pfaffianSwapMatrix A i j := by
        unfold pfaffianSwapMatrix
        rw [Equiv.swap_comm j i]
      rw [hm] at h
      simpa [pfaffianSignedSwap,
        hne, hne.symm, hiT, hjT, swap_image_fixed i j T hiT hjT,
        swap_image_fixed j i T hjT hiT] using h
    · simp only [pfaffianSignedSwap, hi, false_and, ite_false, one_mul,
        swap_image_fixed i j S hi hj, principalPfaffian]
      unfold pfaffianSwapMatrix
      rw [← pfaffianList_map, swap_sort_fixed i j S hi hj]

/-- The two allowed gates on a finite ordered row of wires. Their stored
positions include a proof that the wires are nearest neighbors. -/
inductive PfaffianLocalGate (s : ℕ) (R : Type*) where
  | swap (i j : Fin s) (adjacent : j.val = i.val + 1)
  | create (i j : Fin s) (adjacent : j.val = i.val + 1) (coefficient : R)

/-- Exact occupied-subset action of one local gate. -/
def PfaffianLocalGate.act : PfaffianLocalGate s R → SubsetSignature s R →
    SubsetSignature s R
  | .swap i j _ => pfaffianSignedSwap i j
  | .create i j _ t => pfaffianPairCreation i j t

/-- A circuit is read in matrix-product order: the rightmost gate acts first. -/
def pfaffianCircuitAct (c : List (PfaffianLocalGate s R))
    (F : SubsetSignature s R) : SubsetSignature s R :=
  c.foldr PfaffianLocalGate.act F

@[simp] theorem pfaffianCircuitAct_nil (F : SubsetSignature s R) :
    pfaffianCircuitAct [] F = F := rfl

@[simp] theorem pfaffianCircuitAct_cons (g : PfaffianLocalGate s R)
    (c : List (PfaffianLocalGate s R)) (F : SubsetSignature s R) :
    pfaffianCircuitAct (g :: c) F = g.act (pfaffianCircuitAct c F) := rfl

theorem pfaffianCircuitAct_append (c d : List (PfaffianLocalGate s R))
    (F : SubsetSignature s R) :
    pfaffianCircuitAct (c ++ d) F = pfaffianCircuitAct c (pfaffianCircuitAct d F) :=
  List.foldr_append

/-- Bubble the right endpoint towards the left, create the adjacent pair,
and undo every swap. This is an explicit finite nearest-neighbor circuit. -/
def pfaffianCompileEdge (i j : Fin s) (hij : i < j) (t : R) :
    List (PfaffianLocalGate s R) :=
  if h : j.val = i.val + 1 then [.create i j h t]
  else
    let k : Fin s := ⟨j.val - 1, by omega⟩
    have hik : i < k := by simp only [Fin.lt_def] at *; dsimp [k]; omega
    have hkj : j.val = k.val + 1 := by dsimp [k]; simp only [Fin.lt_def] at hij; omega
    [.swap k j hkj] ++ pfaffianCompileEdge i k hik t ++ [.swap k j hkj]
termination_by j.val

private theorem pfaffianSwapMatrix_edge_conjugate
    (A : Matrix (Fin s) (Fin s) R) (i k j : Fin s)
    (hik : i ≠ k) (hij : i ≠ j) (t : R) :
    pfaffianSwapMatrix (pfaffianEdgeUpdate (pfaffianSwapMatrix A k j) i k t) k j =
      pfaffianEdgeUpdate A i j t := by
  have hs : Equiv.swap k j i = i := Equiv.swap_apply_of_ne_of_ne hik hij
  have heq (x a : Fin s) : Equiv.swap k j x = a ↔ x = Equiv.swap k j a := by
    constructor
    · intro h
      simpa using congrArg (Equiv.swap k j) h
    · intro h
      rw [h]
      simp
  funext x y
  simp [pfaffianSwapMatrix, pfaffianEdgeUpdate, heq, hs]

/-- Every compiled edge performs the desired exact update on every alternating
input matrix. The internal crossover signs cancel in precisely the required way. -/
theorem pfaffianCompileEdge_correct (A : Matrix (Fin s) (Fin s) R)
    (hA : ∀ x y, A x y = -A y x) (i j : Fin s) (hij : i < j) (t : R) :
    pfaffianCircuitAct (pfaffianCompileEdge i j hij t) (principalPfaffian A) =
      principalPfaffian (pfaffianEdgeUpdate A i j t) := by
  rw [pfaffianCompileEdge]
  split
  · simpa [PfaffianLocalGate.act] using
      (principalPfaffian_edgeUpdate A hA (ne_of_lt hij) t).symm
  · rename_i h
    let k : Fin s := ⟨j.val - 1, by omega⟩
    have hik : i < k := by simp only [Fin.lt_def] at *; dsimp [k]; omega
    have hkj : j.val = k.val + 1 := by dsimp [k]; simp only [Fin.lt_def] at hij; omega
    change pfaffianCircuitAct
      ([.swap k j hkj] ++ pfaffianCompileEdge i k hik t ++ [.swap k j hkj])
      (principalPfaffian A) = _
    rw [pfaffianCircuitAct_append, pfaffianCircuitAct_append]
    simp only [pfaffianCircuitAct_cons, pfaffianCircuitAct_nil, PfaffianLocalGate.act]
    rw [← principalPfaffian_swap_adjacent A hA k j hkj,
      pfaffianCompileEdge_correct (pfaffianSwapMatrix A k j)
        (pfaffianSwapMatrix_skew A hA k j) i k hik t,
      ← principalPfaffian_swap_adjacent _
        (pfaffianEdgeUpdate_skew _ (pfaffianSwapMatrix_skew A hA k j) i k t) k j hkj,
      pfaffianSwapMatrix_edge_conjugate A i k j (ne_of_lt hik) (ne_of_lt hij) t]
termination_by j.val

/-- Compile the algebraic upper-edge synthesis into a concrete local gate list. -/
def pfaffianCompileEdges (A : Matrix (Fin s) (Fin s) R) :
    List (PfaffianUpperPair s) → List (PfaffianLocalGate s R)
  | [] => []
  | p :: ps => pfaffianCompileEdge p.val.1 p.val.2 p.property (A p.val.1 p.val.2) ++
      pfaffianCompileEdges A ps

theorem pfaffianCompileEdges_correct (A : Matrix (Fin s) (Fin s) R)
    (ps : List (PfaffianUpperPair s)) :
    pfaffianCircuitAct (pfaffianCompileEdges A ps) pfaffianVacuum =
      principalPfaffian (pfaffianEdgeBuildMatrix A ps) := by
  induction ps with
  | nil => exact principalPfaffian_zero.symm
  | cons p ps ih =>
    simp only [pfaffianCompileEdges, pfaffianCircuitAct_append, ih,
      pfaffianEdgeBuildMatrix]
    exact pfaffianCompileEdge_correct _ (pfaffianEdgeBuildMatrix_skew A ps) _ _ _ _

/-- Canonical finite nearest-neighbor synthesis of an alternating matrix. -/
noncomputable def principalPfaffianCircuit (A : Matrix (Fin s) (Fin s) R) :
    List (PfaffianLocalGate s R) :=
  pfaffianCompileEdges A (Finset.univ.toList : List (PfaffianUpperPair s))

/-- Starting with the vacuum, the compiled local circuit gives every actual
principal Pfaffian of `A`, with its exact scalar and sign. -/
theorem principalPfaffianCircuit_correct (A : Matrix (Fin s) (Fin s) R)
    (hA : ∀ x y, A x y = -A y x) (hdiag : ∀ x, A x x = 0) :
    pfaffianCircuitAct (principalPfaffianCircuit A) pfaffianVacuum =
      principalPfaffian A := by
  rw [principalPfaffianCircuit, pfaffianCompileEdges_correct,
    pfaffianEdgeBuildMatrix_all A hA hdiag]

/-- Restrict an occupied subset to the two active wire coordinates. -/
def pfaffianLocalBits (i j : Fin s) (S : Finset (Fin s)) : Fin 2 → Bool :=
  ![decide (i ∈ S), decide (j ∈ S)]

/-- Replace precisely two wire bits, leaving all other coordinates unchanged. -/
def pfaffianLocalInput (i j : Fin s) (S : Finset (Fin s)) (a : Fin 2 → Bool) :
    Finset (Fin s) :=
  let T := (S.erase i).erase j
  (if a 0 then {i} else ∅) ∪ (if a 1 then {j} else ∅) ∪ T

@[simp] theorem pfaffianLocalInput_same (i j : Fin s) (hij : i ≠ j)
    (S : Finset (Fin s)) : pfaffianLocalInput i j S (pfaffianLocalBits i j S) = S := by
  ext x
  by_cases hxi : x = i <;> by_cases hxj : x = j <;>
    by_cases hi : i ∈ S <;> by_cases hj : j ∈ S <;>
    simp_all [pfaffianLocalInput, pfaffianLocalBits]

@[simp] theorem pfaffianLocalInput_empty (i j : Fin s) (S : Finset (Fin s)) :
    pfaffianLocalInput i j S (fun _ => false) = (S.erase i).erase j := by
  simp [pfaffianLocalInput]

@[simp] theorem pfaffianLocalBits_full (i j : Fin s) (S : Finset (Fin s)) :
    pfaffianLocalBits i j S = (fun _ => true) ↔ i ∈ S ∧ j ∈ S := by
  simp [pfaffianLocalBits, funext_iff, Fin.forall_fin_succ]

/-- State action obtained by contracting a genuine two-wire transfer kernel
against all four possible local input states. -/
def pfaffianLocalKernelAct (i j : Fin s)
    (M : (Fin 2 → Bool) → (Fin 2 → Bool) → R)
    (F : SubsetSignature s R) (S : Finset (Fin s)) : R :=
  ∑ a, F (pfaffianLocalInput i j S a) * M a (pfaffianLocalBits i j S)

/-- The create gate action is the contraction of its actual weighted matching
signature, with the two output ports read in reverse boundary order. -/
theorem pfaffianLocalKernelAct_pairCreation (i j : Fin s)
    (hij : j.val = i.val + 1) (t : R) (F : SubsetSignature s R) :
    pfaffianLocalKernelAct i j (pairCreationMatrix t) F =
      pfaffianPairCreation i j t F := by
  have hne : i ≠ j := by intro h; have := congrArg Fin.val h; omega
  funext S
  simp only [pfaffianLocalKernelAct, pairCreationMatrix_eq, mul_add,
    Finset.sum_add_distrib]
  simp only [mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq', pfaffianLocalInput_same i j hne S,
    pfaffianPairCreation_adjacent i j hij t F S]
  by_cases h : i ∈ S ∧ j ∈ S
  · simp [h.1, h.2, mul_comm]
  · have hn : pfaffianLocalBits i j S ≠ fun _ => true :=
      fun he => h ((pfaffianLocalBits_full i j S).mp he)
    simp [hn, h]

private theorem mem_swap_image (i j x : Fin s) (S : Finset (Fin s)) :
    x ∈ S.image (Equiv.swap i j) ↔ Equiv.swap i j x ∈ S := by
  rw [Finset.mem_image]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro h
    exact ⟨Equiv.swap i j x, h, by simp⟩

/-- Reversing the local input bits exchanges precisely the two wire names. -/
theorem pfaffianLocalInput_reverse (i j : Fin s) (hij : i ≠ j)
    (S : Finset (Fin s)) :
    pfaffianLocalInput i j S (fun p => pfaffianLocalBits i j S p.rev) =
      S.image (Equiv.swap i j) := by
  ext x
  rw [mem_swap_image]
  by_cases hxi : x = i <;> by_cases hxj : x = j <;>
    by_cases hi : i ∈ S <;> by_cases hj : j ∈ S <;>
    simp_all [pfaffianLocalInput, pfaffianLocalBits, Fin.rev,
      Equiv.swap_apply_of_ne_of_ne]

private theorem twoBits_reverse_eq (a b : Fin 2 → Bool) :
    b = (fun p => a p.rev) ↔ a = (fun p => b p.rev) := by
  constructor <;> intro h <;> ext p
  · have hh := congrFun h p.rev
    simpa using hh.symm
  · have hh := congrFun h p.rev
    simpa using hh.symm

/-- The signed swap action is the contraction of the actual seven-edge
crossover matching signature, including its doubly occupied minus sign. -/
theorem pfaffianLocalKernelAct_crossover (i j : Fin s) (hij : i ≠ j)
    (F : SubsetSignature s R) :
    pfaffianLocalKernelAct i j (crossoverMatrix (K := R)) F =
      pfaffianSignedSwap i j F := by
  funext S
  simp only [pfaffianLocalKernelAct, crossoverMatrix_eq, twoBits_reverse_eq,
    mul_ite, mul_zero]
  rw [Finset.sum_ite_eq']
  rw [pfaffianLocalInput_reverse i j hij S]
  simp only [pfaffianLocalBits, pfaffianSignedSwap]
  by_cases hi : i ∈ S <;> by_cases hj : j ∈ S <;>
    simp [hi, hj, mul_comm, Fin.rev]

/-- The actual local graph transfer kernel selected by a compiled gate. -/
noncomputable def PfaffianLocalGate.kernel : PfaffianLocalGate s R →
    ((Fin 2 → Bool) → (Fin 2 → Bool) → R)
  | .swap _ _ _ => crossoverMatrix
  | .create _ _ _ t => pairCreationMatrix t

/-- First active wire, exposed for diagram composition. -/
def PfaffianLocalGate.left : PfaffianLocalGate s R → Fin s
  | .swap i _ _ => i
  | .create i _ _ _ => i

/-- Second active wire, exposed for diagram composition. -/
def PfaffianLocalGate.right : PfaffianLocalGate s R → Fin s
  | .swap _ j _ => j
  | .create _ j _ _ => j

omit [CommRing R] in
theorem PfaffianLocalGate.adjacent (g : PfaffianLocalGate s R) :
    g.right.val = g.left.val + 1 := by cases g <;> assumption

/-- Each circuit instruction is exactly contraction with its actual elementary
graph kernel. All spectator bits stay fixed. -/
theorem PfaffianLocalGate.act_eq_kernel (g : PfaffianLocalGate s R)
    (F : SubsetSignature s R) :
    g.act F = pfaffianLocalKernelAct g.left g.right g.kernel F := by
  cases g with
  | swap i j h =>
    exact (pfaffianLocalKernelAct_crossover i j (by intro he; have := congrArg Fin.val he; omega) F).symm
  | create i j h t => exact (pfaffianLocalKernelAct_pairCreation i j h t F).symm

/-- A property required only of the variable creation coefficients. Swaps
carry no parameter: their actual graph weights are the fixed units. -/
def PfaffianLocalGate.coefficientsIn (P : R → Prop) : PfaffianLocalGate s R → Prop
  | .swap _ _ _ => True
  | .create _ _ _ t => P t

omit [CommRing R] in
/-- The bubble compilation introduces no new creation coefficient. -/
theorem pfaffianCompileEdge_coefficients (P : R → Prop) (i j : Fin s)
    (hij : i < j) (t : R) (ht : P t) :
    ∀ g ∈ pfaffianCompileEdge i j hij t, g.coefficientsIn P := by
  rw [pfaffianCompileEdge]
  split
  · intro g hg
    simp only [List.mem_singleton] at hg
    subst g
    exact ht
  · rename_i h
    let k : Fin s := ⟨j.val - 1, by omega⟩
    have hik : i < k := by simp only [Fin.lt_def] at *; dsimp [k]; omega
    have hkj : j.val = k.val + 1 := by dsimp [k]; simp only [Fin.lt_def] at hij; omega
    change ∀ g ∈ ([.swap k j hkj] ++ pfaffianCompileEdge i k hik t ++
      [.swap k j hkj]), g.coefficientsIn P
    intro g hg
    simp only [List.mem_append, List.mem_singleton] at hg
    rcases hg with (rfl | hg) | rfl
    · trivial
    · exact pfaffianCompileEdge_coefficients P i k hik t ht g hg
    · trivial
termination_by j.val

omit [CommRing R] in
theorem pfaffianCompileEdges_coefficients (P : R → Prop)
    (A : Matrix (Fin s) (Fin s) R) (ps : List (PfaffianUpperPair s))
    (hA : ∀ p ∈ ps, P (A p.val.1 p.val.2)) :
    ∀ g ∈ pfaffianCompileEdges A ps, g.coefficientsIn P := by
  induction ps with
  | nil => simp [pfaffianCompileEdges]
  | cons p ps ih =>
    intro g hg
    simp only [pfaffianCompileEdges, List.mem_append] at hg
    rcases hg with hg | hg
    · exact pfaffianCompileEdge_coefficients P _ _ _ _ (hA p (by simp)) g hg
    · exact ih (fun p hp => hA p (by simp [hp])) g hg

omit [CommRing R] in
/-- Every variable gate coefficient is one of the original strict-upper matrix
entries. The actual elementary graphs add only their fixed weights `1` and `-1`. -/
theorem principalPfaffianCircuit_coefficients (A : Matrix (Fin s) (Fin s) R) :
    ∀ g ∈ principalPfaffianCircuit A,
      g.coefficientsIn (fun t => ∃ i j : Fin s, i < j ∧ t = A i j) := by
  apply pfaffianCompileEdges_coefficients
  intro p _
  exact ⟨p.val.1, p.val.2, p.property, rfl⟩

/-- In particular the circuit is defined over every coefficient subfield of
its matrix entries, with no divisions or extra algebraic constants. -/
theorem principalPfaffianCircuit_subfield (F : Subfield ℂ)
    (A : Matrix (Fin s) (Fin s) ℂ) (hA : ∀ i j, i < j → A i j ∈ F) :
    ∀ g ∈ principalPfaffianCircuit A, g.coefficientsIn (· ∈ F) := by
  apply pfaffianCompileEdges_coefficients
  intro p _
  exact hA _ _ p.property

/-- The two-wire graph kernel extended by identity on every spectator wire. -/
def pfaffianPaddedKernel (i j : Fin s)
    (M : (Fin 2 → Bool) → (Fin 2 → Bool) → R)
    (T S : Finset (Fin s)) : R :=
  if (T.erase i).erase j = (S.erase i).erase j then
    M (pfaffianLocalBits i j T) (pfaffianLocalBits i j S) else 0

@[simp] theorem pfaffianLocalInput_erase (i j : Fin s) (S : Finset (Fin s))
    (a : Fin 2 → Bool) :
    ((pfaffianLocalInput i j S a).erase i).erase j = (S.erase i).erase j := by
  ext x
  cases ha : a 0 <;> cases hb : a 1 <;> simp [pfaffianLocalInput, ha, hb]
  all_goals tauto

@[simp] theorem pfaffianLocalBits_input (i j : Fin s) (hij : i ≠ j)
    (S : Finset (Fin s)) (a : Fin 2 → Bool) :
    pfaffianLocalBits i j (pfaffianLocalInput i j S a) = a := by
  ext p
  fin_cases p <;> cases ha : a 0 <;> cases hb : a 1 <;>
    simp [pfaffianLocalBits, pfaffianLocalInput, ha, hb, hij, hij.symm]

theorem pfaffianLocalInput_of_erase_eq (i j : Fin s) (hij : i ≠ j)
    (S T : Finset (Fin s)) (h : (T.erase i).erase j = (S.erase i).erase j) :
    pfaffianLocalInput i j S (pfaffianLocalBits i j T) = T := by
  have he : pfaffianLocalInput i j S (pfaffianLocalBits i j T) =
      pfaffianLocalInput i j T (pfaffianLocalBits i j T) := by
    unfold pfaffianLocalInput
    rw [h]
  rw [he, pfaffianLocalInput_same i j hij T]

/-- Contracting the fully padded gate over all global input states reduces
exactly to the four-term local contraction. -/
theorem pfaffianPaddedKernel_contract (i j : Fin s) (hij : i ≠ j)
    (M : (Fin 2 → Bool) → (Fin 2 → Bool) → R)
    (F : SubsetSignature s R) (S : Finset (Fin s)) :
    (∑ T, F T * pfaffianPaddedKernel i j M T S) =
      pfaffianLocalKernelAct i j M F S := by
  classical
  simp only [pfaffianPaddedKernel, mul_ite, mul_zero]
  rw [← Finset.sum_filter]
  unfold pfaffianLocalKernelAct
  refine Finset.sum_bij (fun T _ => pfaffianLocalBits i j T) ?_ ?_ ?_ ?_
  · intro T hT
    exact Finset.mem_univ _
  · intro T hT U hU hbits
    have ht := pfaffianLocalInput_of_erase_eq i j hij S T (Finset.mem_filter.mp hT).2
    have hu := pfaffianLocalInput_of_erase_eq i j hij S U (Finset.mem_filter.mp hU).2
    rw [← ht, ← hu, hbits]
  · intro a _
    refine ⟨pfaffianLocalInput i j S a, ?_, pfaffianLocalBits_input i j hij S a⟩
    simp
  · intro T hT
    rw [pfaffianLocalInput_of_erase_eq i j hij S T (Finset.mem_filter.mp hT).2]

end MatchgateWidth
