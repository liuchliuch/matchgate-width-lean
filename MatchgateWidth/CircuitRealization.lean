import MatchgateWidth.PfaffianCircuit
import MatchgateWidth.PlanarWireDrawing
import MatchgateWidth.MatchingReindex

/-!
# Actual strip-drawn graphs for finite local circuits

Graphs are assembled by disjoint unions and unit-weight bridge edges. The
algebraic semantics are the weighted matching sums of those very graphs.
-/
namespace MatchgateWidth
noncomputable section

/-- A finite graph equipped with a checked two-sided strip drawing. -/
structure DrawnWire (n : ℕ) where
  V : Type
  E : Type
  [finiteV : Fintype V]
  [finiteE : Fintype E]
  graph : WeightedGraph V E ℂ
  input : Fin n → V
  output : Fin n → V
  drawing : WireDrawing graph input output

/-- A finite graph equipped with a checked ordered output-only strip drawing. -/
structure DrawnState (n : ℕ) where
  V : Type
  E : Type
  [finiteV : Fintype V]
  [finiteE : Fintype E]
  graph : WeightedGraph V E ℂ
  output : Fin n → V
  drawing : StateDrawing graph output

attribute [instance] DrawnWire.finiteV DrawnWire.finiteE
attribute [instance] DrawnState.finiteV DrawnState.finiteE

namespace DrawnWire
variable {n m : ℕ}

def kernel (W : DrawnWire n) : (Fin n → Bool) → (Fin n → Bool) → ℂ :=
  wireKernel W.graph W.input W.output

def parallel (W : DrawnWire n) (Z : DrawnWire m) : DrawnWire (n + m) where
  V := W.V ⊕ Z.V
  E := W.E ⊕ Z.E
  graph := disjointUnionGraph W.graph Z.graph
  input := WireDrawing.parallelPorts W.input Z.input
  output := WireDrawing.parallelPorts W.output Z.output
  drawing := W.drawing.parallel Z.drawing

/-- Equality transport preserves the ordered numeric wire coordinates. -/
def cast (h : n = m) (W : DrawnWire n) : DrawnWire m := h ▸ W

end DrawnWire

namespace DrawnState
variable {n m : ℕ}

def signature (W : DrawnState n) : (Fin n → Bool) → ℂ :=
  deletionSignature W.graph W.output

def parallel (W : DrawnState n) (Z : DrawnState m) : DrawnState (n + m) where
  V := W.V ⊕ Z.V
  E := W.E ⊕ Z.E
  graph := disjointUnionGraph W.graph Z.graph
  output := WireDrawing.parallelPorts W.output Z.output
  drawing := W.drawing.parallel Z.drawing

def applyGate (W : DrawnState n) (Z : DrawnWire n) : DrawnState n where
  V := W.V ⊕ Z.V
  E := (W.E ⊕ Z.E) ⊕ Fin n
  graph := bridgeGraph W.graph Z.graph W.output Z.input
  output := fun i => Sum.inr (Z.output i)
  drawing := W.drawing.applyGate Z.drawing

def cast (h : n = m) (W : DrawnState n) : DrawnState m := h ▸ W

end DrawnState

private theorem deletionActive_parallel {V W : Type*} [Fintype V] [Fintype W]
    {n m : ℕ} (f : Fin n → V) (g : Fin m → W) (a : Fin (n + m) → Bool) :
    deletionActive (WireDrawing.parallelPorts f g) a =
      (deletionActive f (fun i => a (Fin.castAdd m i))).disjSum
        (deletionActive g (fun i => a (Fin.natAdd n i))) := by
  classical
  ext v
  cases v <;>
    simp [deletionActive, WireDrawing.parallelPorts, Fin.forall_fin_add]

namespace DrawnWire
variable {n m : ℕ}

theorem kernel_parallel (W : DrawnWire n) (Z : DrawnWire m)
    (a b : Fin (n + m) → Bool) :
    (W.parallel Z).kernel a b =
      W.kernel (fun i => a (Fin.castAdd m i)) (fun i => b (Fin.castAdd m i)) *
      Z.kernel (fun i => a (Fin.natAdd n i)) (fun i => b (Fin.natAdd n i)) := by
  classical
  unfold kernel wireKernel parallel
  rw [deletionActive_parallel, deletionActive_parallel]
  have hi {A C : Finset W.V} {B D : Finset Z.V} :
      A.disjSum B ∩ C.disjSum D = (A ∩ C).disjSum (B ∩ D) := by
    classical
    ext x
    cases x <;> simp
  convert weightedPerfectMatch_disjointUnion W.graph Z.graph
    (deletionActive W.input (fun i => a (Fin.castAdd m i)) ∩
      deletionActive W.output (fun i => b (Fin.castAdd m i)))
    (deletionActive Z.input (fun i => a (Fin.natAdd n i)) ∩
      deletionActive Z.output (fun i => b (Fin.natAdd n i))) using 1
  congr 1
  ext x
  cases x <;> simp

end DrawnWire

namespace DrawnState
variable {n m : ℕ}

theorem signature_parallel (W : DrawnState n) (Z : DrawnState m)
    (a : Fin (n + m) → Bool) :
    (W.parallel Z).signature a =
      W.signature (fun i => a (Fin.castAdd m i)) *
      Z.signature (fun i => a (Fin.natAdd n i)) := by
  unfold signature deletionSignature parallel
  rw [deletionActive_parallel, weightedPerfectMatch_disjointUnion]

theorem signature_applyGate (W : DrawnState n) (Z : DrawnWire n)
    (b : Fin n → Bool) :
    (W.applyGate Z).signature b = ∑ a, W.signature a * Z.kernel a b := by
  exact W.drawing.applyGate_deletionSignature Z.drawing b

end DrawnState
private theorem finFun_eq_split {n m : ℕ} {α : Type*} (a b : Fin (n + m) → α) :
    a = b ↔ (fun i => a (Fin.castAdd m i)) = (fun i => b (Fin.castAdd m i)) ∧
      (fun i => a (Fin.natAdd n i)) = (fun i => b (Fin.natAdd n i)) := by
  constructor
  · rintro rfl
    exact ⟨rfl, rfl⟩
  · rintro ⟨hl, hr⟩
    ext i
    induction i using Fin.addCases with
    | left i => exact congrFun hl i
    | right i => exact congrFun hr i

namespace DrawnWire

def elementary {s : ℕ} : PfaffianLocalGate s ℂ → DrawnWire 2
  | .swap _ _ _ => {
      V := Fin 6
      E := Fin 7
      graph := crossoverGraphOver ℂ
      input := fun i => crossoverExternal (twoWireInput i)
      output := fun i => crossoverExternal (twoWireOutput i)
      drawing := crossoverWireDrawing }
  | .create _ _ _ t => {
      V := Fin 4
      E := Fin 3
      graph := pairCreationGraph t
      input := twoWireInput
      output := twoWireOutput
      drawing := pairCreationWireDrawing t }

theorem kernel_elementary {s : ℕ} (g : PfaffianLocalGate s ℂ) (a b : Fin 2 → Bool) :
    (elementary g).kernel a b = g.kernel a b := by
  cases g with
  | swap i j h => exact crossover_wireKernel a b
  | create i j h t => exact pairCreation_wireKernel t a b

def identityOne : DrawnWire 1 where
  V := Fin 2
  E := Fin 1
  graph := pinZeroGraph ℂ
  input := fun _ => 0
  output := fun _ => 1
  drawing := identityWireDrawing

def empty : DrawnWire 0 where
  V := Fin 0
  E := Fin 0
  graph := emptyWireGraph
  input := Fin.elim0
  output := Fin.elim0
  drawing := emptyWireDrawing

/-- Parallel unit wires, built from actual unit edges. -/
def identity : (n : ℕ) → DrawnWire n
  | 0 => empty
  | n + 1 => (identity n).parallel identityOne

@[simp] theorem kernel_identity (n : ℕ) (a b : Fin n → Bool) :
    (identity n).kernel a b = if a = b then 1 else 0 := by
  induction n with
  | zero =>
    have h : a = b := Subsingleton.elim _ _
    change wireKernel emptyWireGraph Fin.elim0 Fin.elim0 a b = _
    rw [emptyWireGraph_wireKernel, ite_eq_left h]
  | succ n ih =>
    rw [identity, kernel_parallel, ih]
    change _ * wireKernel (pinZeroGraph ℂ) (fun _ => 0) (fun _ => 1) _ _ = _
    rw [identity_wireKernel]
    simp only [finFun_eq_split a b]
    split_ifs <;> simp_all

/-- Put a two-wire gate between explicit left and right identity strips. -/
def pad (W : DrawnWire 2) (l r : ℕ) : DrawnWire ((l + 2) + r) :=
  ((identity l).parallel W).parallel (identity r)

theorem kernel_pad (W : DrawnWire 2) (l r : ℕ) (a b : Fin ((l + 2) + r) → Bool) :
    (W.pad l r).kernel a b =
      (if (fun k : Fin l => a (Fin.castAdd r (Fin.castAdd 2 k))) =
          (fun k : Fin l => b (Fin.castAdd r (Fin.castAdd 2 k))) then 1 else 0) *
      W.kernel (fun p => a (Fin.castAdd r (Fin.natAdd l p)))
        (fun p => b (Fin.castAdd r (Fin.natAdd l p))) *
      (if (fun k : Fin r => a (Fin.natAdd (l + 2) k)) =
          (fun k : Fin r => b (Fin.natAdd (l + 2) k)) then 1 else 0) := by
  rw [pad, kernel_parallel, kernel_parallel, kernel_identity, kernel_identity]

end DrawnWire

namespace DrawnState

def empty : DrawnState 0 where
  V := Fin 0
  E := Fin 0
  graph := emptyWireGraph
  output := Fin.elim0
  drawing := emptyStateDrawing

def vacuumOne : DrawnState 1 where
  V := Fin 2
  E := Fin 1
  graph := pinZeroGraph ℂ
  output := fun _ => 0
  drawing := pinZeroStateDrawing

/-- A row of zero pins is the actual vacuum state graph. -/
def vacuum : (n : ℕ) → DrawnState n
  | 0 => empty
  | n + 1 => (vacuum n).parallel vacuumOne

theorem signature_vacuum (n : ℕ) (b : Fin n → Bool) :
    (vacuum n).signature b = if b = (fun _ => false) then 1 else 0 := by
  induction n with
  | zero =>
    have h : b = fun _ => false := Subsingleton.elim _ _
    change deletionSignature emptyWireGraph Fin.elim0 b = _
    rw [emptyWireGraph_deletionSignature, ite_eq_left h]
  | succ n ih =>
    rw [vacuum, signature_parallel, ih]
    change _ * deletionSignature (pinZeroGraph ℂ) (fun _ => 0) _ = _
    rw [pinZero_deletionSignature]
    simp only [finFun_eq_split b (fun _ => false)]
    have he : (fun i : Fin 1 => b (Fin.natAdd n i)) = (fun _ => false) ↔
        b (Fin.natAdd n 0) = false := by simp [funext_iff, Fin.forall_fin_succ]
    simp only [he]
    split_ifs <;> simp_all

end DrawnState
/-- A two-wire transfer matrix padded by exact identity on every other wire. -/
def localWireKernel {s : ℕ} (i j : Fin s)
    (M : (Fin 2 → Bool) → (Fin 2 → Bool) → ℂ) (a b : Fin s → Bool) : ℂ :=
  if (∀ k, k ≠ i → k ≠ j → a k = b k) then
    M ![a i, a j] ![b i, b j] else 0

private def padFirst (l r : ℕ) : Fin ((l + 2) + r) :=
  Fin.castAdd r (Fin.natAdd l (0 : Fin 2))
private def padSecond (l r : ℕ) : Fin ((l + 2) + r) :=
  Fin.castAdd r (Fin.natAdd l (1 : Fin 2))

private theorem pad_spectators_iff (l r : ℕ) (a b : Fin ((l + 2) + r) → Bool) :
    (∀ k, k ≠ padFirst l r → k ≠ padSecond l r → a k = b k) ↔
      (fun k : Fin l => a (Fin.castAdd r (Fin.castAdd 2 k))) =
        (fun k : Fin l => b (Fin.castAdd r (Fin.castAdd 2 k))) ∧
      (fun k : Fin r => a (Fin.natAdd (l + 2) k)) =
        (fun k : Fin r => b (Fin.natAdd (l + 2) k)) := by
  constructor
  · intro h
    constructor
    · ext k
      apply h <;> intro he <;> have hv := congrArg Fin.val he <;>
        simp only [Fin.val_castAdd, Fin.val_natAdd, padFirst, padSecond] at hv
      all_goals dsimp at hv; have hk := k.isLt; omega
    · ext k
      apply h <;> intro he <;> have hv := congrArg Fin.val he <;>
        simp only [Fin.val_castAdd, Fin.val_natAdd, padFirst, padSecond] at hv
      all_goals dsimp at hv; omega
  · rintro ⟨hl, hr⟩ k hi hj
    induction k using Fin.addCases with
    | left k =>
      induction k using Fin.addCases with
      | left k => exact congrFun hl k
      | right k =>
        fin_cases k
        · exact (hi rfl).elim
        · exact (hj rfl).elim
    | right k => exact congrFun hr k

namespace DrawnWire

theorem kernel_pad_local (W : DrawnWire 2) (l r : ℕ)
    (a b : Fin ((l + 2) + r) → Bool) :
    (W.pad l r).kernel a b = localWireKernel (padFirst l r) (padSecond l r) W.kernel a b := by
  rw [kernel_pad]
  have ha : (fun p : Fin 2 => a (Fin.castAdd r (Fin.natAdd l p))) =
      ![a (padFirst l r), a (padSecond l r)] := by ext p; fin_cases p <;> rfl
  have hb : (fun p : Fin 2 => b (Fin.castAdd r (Fin.natAdd l p))) =
      ![b (padFirst l r), b (padSecond l r)] := by ext p; fin_cases p <;> rfl
  rw [ha, hb]
  simp only [localWireKernel, pad_spectators_iff]
  split_ifs <;> simp_all

theorem kernel_cast {n m : ℕ} (h : n = m) (W : DrawnWire n) (a b : Fin m → Bool) :
    (W.cast h).kernel a b = W.kernel (fun i => a (Fin.cast h i))
      (fun i => b (Fin.cast h i)) := by cases h; rfl

private theorem localWireKernel_cast {n m : ℕ} (h : n = m) (i j : Fin n)
    (M : (Fin 2 → Bool) → (Fin 2 → Bool) → ℂ) (a b : Fin m → Bool) :
    localWireKernel i j M (fun k => a (Fin.cast h k)) (fun k => b (Fin.cast h k)) =
      localWireKernel (Fin.cast h i) (Fin.cast h j) M a b := by cases h; rfl

/-- The actual width-`s` graph for one nearest-neighbor circuit instruction. -/
def localGate {s : ℕ} (g : PfaffianLocalGate s ℂ) : DrawnWire s :=
  let l := g.left.val
  let r := s - (l + 2)
  have h : (l + 2) + r = s := by
    have hg := g.adjacent
    have hj := g.right.isLt
    dsimp [l, r]
    omega
  ((elementary g).pad l r).cast h

/-- The assembled spectator wires are exact identities; the active graph has
exactly its verified two-wire matching kernel. -/
theorem kernel_localGate {s : ℕ} (g : PfaffianLocalGate s ℂ) (a b : Fin s → Bool) :
    (localGate g).kernel a b = localWireKernel g.left g.right g.kernel a b := by
  unfold localGate
  rw [kernel_cast, kernel_pad_local, localWireKernel_cast]
  have hM : (elementary g).kernel = g.kernel := by
    funext a b
    exact kernel_elementary g a b
  rw [hM]
  congr 1
  apply Fin.ext
  simp [padSecond, g.adjacent]

end DrawnWire
/-- Occupancy/deletion bits of a selected subset. -/
def circuitSubsetBits {n : ℕ} (S : Finset (Fin n)) : Fin n → Bool :=
  fun i => decide (i ∈ S)

@[simp] theorem bridgeBits_inverse {n : ℕ} (S : Finset (Fin n)) :
    (bridgeBitsEquiv (Fin n)).symm S = circuitSubsetBits S := by
  ext i
  simp [bridgeBitsEquiv, circuitSubsetBits]

private theorem erase_pair_eq_iff {n : ℕ} (i j : Fin n) (T S : Finset (Fin n)) :
    (T.erase i).erase j = (S.erase i).erase j ↔
      ∀ k, k ≠ i → k ≠ j → (k ∈ T ↔ k ∈ S) := by
  constructor
  · intro h k hi hj
    have he := Finset.ext_iff.mp h k
    simpa [hi, hj] using he
  · intro h
    ext k
    by_cases hi : k = i <;> by_cases hj : k = j <;> simp_all

/-- The Boolean padded-wire convention equals the occupied-subset kernel. -/
theorem localWireKernel_subset {n : ℕ} (i j : Fin n)
    (M : (Fin 2 → Bool) → (Fin 2 → Bool) → ℂ) (T S : Finset (Fin n)) :
    localWireKernel i j M (circuitSubsetBits T) (circuitSubsetBits S) =
      pfaffianPaddedKernel i j M T S := by
  have he : (∀ k, k ≠ i → k ≠ j → circuitSubsetBits T k = circuitSubsetBits S k) ↔
      (T.erase i).erase j = (S.erase i).erase j := by
    simp only [circuitSubsetBits, decide_eq_decide]
    exact (erase_pair_eq_iff i j T S).symm
  simp only [localWireKernel, pfaffianPaddedKernel]
  exact if_congr he rfl rfl

namespace DrawnState
variable {n : ℕ}

def table (W : DrawnState n) : SubsetSignature n ℂ :=
  fun S => W.signature (circuitSubsetBits S)

@[simp] theorem table_vacuum (n : ℕ) : (vacuum n).table = pfaffianVacuum := by
  funext S
  rw [table, signature_vacuum]
  have he : circuitSubsetBits S = (fun _ => false) ↔ S = ∅ := by
    simp [circuitSubsetBits, funext_iff, Finset.eq_empty_iff_forall_notMem]
  simp only [he, pfaffianVacuum]

theorem table_applyGate (W : DrawnState n) (Z : DrawnWire n) (S : Finset (Fin n)) :
    (W.applyGate Z).table S =
      ∑ T : Finset (Fin n), W.table T * Z.kernel (circuitSubsetBits T) (circuitSubsetBits S) := by
  rw [table, signature_applyGate]
  have hsum := ((bridgeBitsEquiv (Fin n)).symm.sum_comp
    (fun a => W.signature a * Z.kernel a (circuitSubsetBits S))).symm
  simpa only [bridgeBits_inverse, table] using hsum

/-- Applying the padded graph for a local gate gives exactly its algebraic
state action, by actual bridge matching sums. -/
theorem table_applyLocal (W : DrawnState n) (g : PfaffianLocalGate n ℂ) :
    (W.applyGate (DrawnWire.localGate g)).table = g.act W.table := by
  have hne : g.left ≠ g.right := by
    intro h
    have hv := congrArg Fin.val h
    have ha := g.adjacent
    omega
  funext S
  rw [table_applyGate]
  simp_rw [DrawnWire.kernel_localGate, localWireKernel_subset]
  rw [pfaffianPaddedKernel_contract _ _ hne, ← PfaffianLocalGate.act_eq_kernel]

/-- An actual finite graph for a circuit, composed from its rightmost gate. -/
def circuit (c : List (PfaffianLocalGate n ℂ)) : DrawnState n :=
  c.foldr (fun g W => W.applyGate (DrawnWire.localGate g)) (vacuum n)

/-- The graph's deletion signature agrees with the circuit at every subset. -/
theorem table_circuit (c : List (PfaffianLocalGate n ℂ)) :
    (circuit c).table = pfaffianCircuitAct c pfaffianVacuum := by
  induction c with
  | nil => exact table_vacuum n
  | cons g c ih =>
    change ((circuit c).applyGate (DrawnWire.localGate g)).table =
      g.act (pfaffianCircuitAct c pfaffianVacuum)
    rw [table_applyLocal, ih]

/-- Explicit finite graph with a genuine ordered strip drawing for `A`. -/
def principalPfaffian (A : Matrix (Fin n) (Fin n) ℂ) : DrawnState n :=
  circuit (principalPfaffianCircuit A)

/-- Exact synthesis into the actual matching signature of the assembled graph. -/
theorem table_principalPfaffian (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ i j, A i j = -A j i) (hdiag : ∀ i, A i i = 0) :
    (principalPfaffian A).table = MatchgateWidth.principalPfaffian A := by
  rw [principalPfaffian, table_circuit, principalPfaffianCircuit_correct A hA hdiag]

end DrawnState
namespace DrawnWire
variable {n m : ℕ}

/-- Every actual edge weight belongs to the specified coefficient subfield. -/
def weightsIn (W : DrawnWire n) (K : Subfield ℂ) : Prop :=
  ∀ e, W.graph.weight e ∈ K

theorem weightsIn_parallel (W : DrawnWire n) (Z : DrawnWire m) (K : Subfield ℂ)
    (hW : W.weightsIn K) (hZ : Z.weightsIn K) : (W.parallel Z).weightsIn K := by
  rintro (e | e)
  · exact hW e
  · exact hZ e

theorem weightsIn_cast (W : DrawnWire n) (h : n = m) (K : Subfield ℂ)
    (hW : W.weightsIn K) : (W.cast h).weightsIn K := by cases h; exact hW

theorem weightsIn_identity (n : ℕ) (K : Subfield ℂ) : (identity n).weightsIn K := by
  induction n with
  | zero => intro e; exact e.elim0
  | succ n ih =>
    apply weightsIn_parallel _ _ K ih
    intro e
    exact K.one_mem

theorem weightsIn_elementary {s : ℕ} (g : PfaffianLocalGate s ℂ) (K : Subfield ℂ)
    (hg : g.coefficientsIn (· ∈ K)) : (elementary g).weightsIn K := by
  cases g with
  | swap i j h => exact crossover_weights_mem K
  | create i j h t => exact pairCreation_weights_mem K hg

theorem weightsIn_pad (W : DrawnWire 2) (l r : ℕ) (K : Subfield ℂ)
    (hW : W.weightsIn K) : (W.pad l r).weightsIn K :=
  weightsIn_parallel _ _ K
    (weightsIn_parallel _ _ K (weightsIn_identity l K) hW) (weightsIn_identity r K)

theorem weightsIn_localGate {s : ℕ} (g : PfaffianLocalGate s ℂ) (K : Subfield ℂ)
    (hg : g.coefficientsIn (· ∈ K)) : (localGate g).weightsIn K := by
  unfold localGate
  apply weightsIn_cast
  exact weightsIn_pad _ _ _ K (weightsIn_elementary g K hg)

end DrawnWire

namespace DrawnState
variable {n m : ℕ}

def weightsIn (W : DrawnState n) (K : Subfield ℂ) : Prop :=
  ∀ e, W.graph.weight e ∈ K

theorem weightsIn_parallel (W : DrawnState n) (Z : DrawnState m) (K : Subfield ℂ)
    (hW : W.weightsIn K) (hZ : Z.weightsIn K) : (W.parallel Z).weightsIn K := by
  rintro (e | e)
  · exact hW e
  · exact hZ e

theorem weightsIn_applyGate (W : DrawnState n) (Z : DrawnWire n) (K : Subfield ℂ)
    (hW : W.weightsIn K) (hZ : Z.weightsIn K) : (W.applyGate Z).weightsIn K := by
  rintro ((e | e) | e)
  · exact hW e
  · exact hZ e
  · exact K.one_mem

theorem weightsIn_vacuum (n : ℕ) (K : Subfield ℂ) : (vacuum n).weightsIn K := by
  induction n with
  | zero => intro e; exact e.elim0
  | succ n ih =>
    apply weightsIn_parallel _ _ K ih
    exact pinZero_weights_mem K

theorem weightsIn_circuit (c : List (PfaffianLocalGate n ℂ)) (K : Subfield ℂ)
    (hc : ∀ g ∈ c, g.coefficientsIn (· ∈ K)) : (circuit c).weightsIn K := by
  induction c with
  | nil => exact weightsIn_vacuum n K
  | cons g c ih =>
    apply weightsIn_applyGate
    · exact ih (fun h hh => hc h (by simp [hh]))
    · exact DrawnWire.weightsIn_localGate g K (hc g (by simp))

/-- Actual graph weights never leave the subfield of the input matrix entries. -/
theorem weightsIn_principalPfaffian (A : Matrix (Fin n) (Fin n) ℂ)
    (K : Subfield ℂ) (hA : ∀ i j, i < j → A i j ∈ K) :
    (principalPfaffian A).weightsIn K :=
  weightsIn_circuit _ K (principalPfaffianCircuit_subfield K A hA)

/-- The same synthesized finite graph also has a genuine ordered disk drawing. -/
def principalPfaffian_diskDrawing (A : Matrix (Fin n) (Fin n) ℂ) :
    PlanarDrawing (principalPfaffian A).graph (principalPfaffian A).output :=
  (principalPfaffian A).drawing.toDisk

end DrawnState
/-- The Boolean signature selects precisely the true output modes, in their
original increasing `Fin` order. -/
theorem DrawnState.signature_principalPfaffian {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : ∀ i j, A i j = -A j i)
    (hdiag : ∀ i, A i i = 0) (x : Fin n → Bool) :
    (DrawnState.principalPfaffian A).signature x =
      MatchgateWidth.principalPfaffian A (bridgeBitsEquiv (Fin n) x) := by
  have h := congrFun (DrawnState.table_principalPfaffian A hA hdiag)
    (bridgeBitsEquiv (Fin n) x)
  have hx : circuitSubsetBits (bridgeBitsEquiv (Fin n) x) = x :=
    (bridgeBits_inverse _).symm.trans ((bridgeBitsEquiv (Fin n)).symm_apply_apply x)
  simpa only [DrawnState.table, hx] using h

/-- Every alternating principal-Pfaffian table has an actual finite ordered
disk matching-graph realization, including its exact normalization. -/
theorem principalPfaffian_diskRealizable {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : ∀ i j, A i j = -A j i)
    (hdiag : ∀ i, A i i = 0) :
    DiskRealizable (fun x => MatchgateWidth.principalPfaffian A (bridgeBitsEquiv (Fin n) x)) := by
  have h := diskRealizable_of_finite_drawing (DrawnState.principalPfaffian A).graph
    (DrawnState.principalPfaffian A).output (DrawnState.principalPfaffian_diskDrawing A)
  have he : deletionSignature (DrawnState.principalPfaffian A).graph
      (DrawnState.principalPfaffian A).output =
      (fun x => MatchgateWidth.principalPfaffian A (bridgeBitsEquiv (Fin n) x)) := by
    funext x
    exact DrawnState.signature_principalPfaffian A hA hdiag x
  rwa [he] at h

/-- The finite disk witness can be chosen with every edge weight in the
subfield containing the strict-upper entries of the input matrix. -/
theorem principalPfaffian_diskWitness {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : ∀ i j, A i j = -A j i)
    (hdiag : ∀ i, A i i = 0) (K : Subfield ℂ)
    (hK : ∀ i j, i < j → A i j ∈ K) :
    ∃ (v e : ℕ) (G : WeightedGraph (Fin v) (Fin e) ℂ) (ext : Fin n → Fin v),
      Nonempty (PlanarDrawing G ext) ∧ (∀ a, G.weight a ∈ K) ∧
      ∀ x, deletionSignature G ext x = MatchgateWidth.principalPfaffian A (bridgeBitsEquiv (Fin n) x) := by
  let W := DrawnState.principalPfaffian A
  let v := (Fintype.equivFin W.V).symm
  let e := (Fintype.equivFin W.E).symm
  refine ⟨Fintype.card W.V, Fintype.card W.E, W.graph.reindex v e,
    (fun i => v.symm (W.output i)), ⟨W.drawing.toDisk.reindex v e⟩, ?_, ?_⟩
  · intro a
    exact DrawnState.weightsIn_principalPfaffian A K hK (e a)
  · intro x
    rw [deletionSignature_reindex]
    exact DrawnState.signature_principalPfaffian A hA hdiag x

end
end MatchgateWidth
