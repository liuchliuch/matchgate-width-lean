import MatchgateWidth.ScaledCircuitRealization
import MatchgateWidth.AlgebraicQutritLanguage

/-!
# Actual graph realization of XOR-pivoted Pfaffian tables

A three-vertex path realizes an unsigned one-bit complement. Parallel copies
of these paths and identity edges give independent output complements, with
explicit crossing-free drawings and no enlargement of the coefficient field.
-/
namespace MatchgateWidth
noncomputable section
open scoped symmDiff

/-- A three-vertex unit path, with the middle vertex internal. -/
def flipWireGraph : WeightedGraph (Fin 3) (Fin 2) ℂ where
  left := Fin.castSucc
  right := Fin.succ
  loopless := by intro e; fin_cases e <;> decide
  weight := fun _ => 1

/-- A genuine straight vertical drawing of the complement path. -/
def flipWireDrawing : WireDrawing flipWireGraph
    (fun _ => 0 : Fin 1 → Fin 3) (fun _ => 2 : Fin 1 → Fin 3) := by
  let D : PlaneArcDrawing flipWireGraph := {
    vertex := fun v => ⟨0, 1 - (v.val : ℝ) / 2⟩
    vertex_injective := by
      intro v w h
      apply Fin.ext
      have h' := congrArg Complex.im h
      dsimp at h'
      exact_mod_cast (by linarith : (v.val : ℝ) = (w.val : ℝ))
    edge := fun e t => ⟨0, 1 - ((e.val : ℝ) + (t : ℝ)) / 2⟩
    edge_continuous := by
      intro e
      change Continuous (Complex.equivRealProdCLM.symm ∘
        fun t : unitInterval => ((0 : ℝ), 1 - ((e.val : ℝ) + (t : ℝ)) / 2))
      exact Complex.equivRealProdCLM.symm.continuous.comp (by fun_prop)
    edge_injective := by
      intro e t u h
      apply Subtype.ext
      have h' := congrArg Complex.im h
      dsimp at h'
      linarith
    edge_left := by intro e; apply Complex.ext <;> simp [flipWireGraph]
    edge_right := by
      intro e
      apply Complex.ext <;> simp [flipWireGraph]
    interior_avoids_vertices := by
      intro e t ht₀ ht₁ v h
      have ht0 : 0 < (t : ℝ) := ht₀
      have ht1 : (t : ℝ) < 1 := ht₁
      have h' := congrArg Complex.im h
      fin_cases e <;> fin_cases v <;> norm_num at h' <;>
        first | exact (ne_of_gt ht₀) h' | linarith
    interiors_disjoint := by
      intro e f hef t u ht₀ ht₁ hu₀ hu₁ h
      have ht0 : 0 < (t : ℝ) := ht₀
      have ht1 : (t : ℝ) < 1 := ht₁
      have hu0 : 0 < (u : ℝ) := hu₀
      have hu1 : (u : ℝ) < 1 := hu₁
      have h' := congrArg Complex.im h
      fin_cases e <;> fin_cases f <;> norm_num at h' hef <;> linarith }
  refine {
    toStripDrawing := StripDrawing.ofStraight D 1 ?_ ?_ ?_ ?_ ?_
    input_vertex := ?_
    output_vertex := ?_ }
  · intro e t
    apply Complex.ext <;> simp [D, straightArc, flipWireGraph] <;> ring
  · intro v; norm_num [D]
  · intro v; norm_num [D]
  · intro v; fin_cases v <;> norm_num [D]
  · intro v; fin_cases v <;> norm_num [D]
  · intro i; fin_cases i; norm_num [StripDrawing.ofStraight, D]
  · intro i; fin_cases i; norm_num [StripDrawing.ofStraight, D]

/-- Exact matching enumeration for the path: its kernel is the unsigned NOT. -/
theorem flip_wireKernel (a b : Fin 1 → Bool) :
    wireKernel flipWireGraph (fun _ => 0 : Fin 1 → Fin 3)
      (fun _ => 2 : Fin 1 → Fin 3) a b =
        if a = (fun i => !(b i)) then 1 else 0 := by
  classical
  have ha : a = fun _ => a 0 := by ext i; fin_cases i; rfl
  have hb : b = fun _ => b 0 := by ext i; fin_cases i; rfl
  have hu : (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} := by decide
  rw [ha, hb]
  generalize a 0 = a₀
  generalize b 0 = b₀
  cases a₀ <;> cases b₀ <;>
    simp +decide [wireKernel, weightedPerfectMatch, hu, MatchesExactly,
      matchingDegree, flipWireGraph, deletionActive, Fin.forall_fin_succ] <;>
      norm_num [Finset.filter_insert, Finset.filter_singleton]

namespace DrawnWire

/-- The unit-weight complement path with its actual drawing. -/
def flipOne : DrawnWire 1 where
  V := Fin 3
  E := Fin 2
  graph := flipWireGraph
  input := fun _ => 0
  output := fun _ => 2
  drawing := flipWireDrawing

@[simp] theorem kernel_flipOne (a b : Fin 1 → Bool) :
    flipOne.kernel a b = if a = (fun i => !(b i)) then 1 else 0 :=
  flip_wireKernel a b

/-- Choose an identity edge or complement path for one output. -/
def pivotOne (p : Bool) : DrawnWire 1 := if p then flipOne else identityOne

theorem kernel_pivotOne (p : Bool) (a b : Fin 1 → Bool) :
    (pivotOne p).kernel a b = if a = (fun i => Bool.xor p (b i)) then 1 else 0 := by
  classical
  cases p
  · have hb : (fun i => Bool.xor false (b i)) = b := by funext i; exact Bool.false_xor _
    rw [hb]
    exact identity_wireKernel a b
  · simpa [pivotOne] using kernel_flipOne a b

/-- Parallel independent complements, with identity edges on every unselected wire. -/
def pivot : (n : ℕ) → (Fin n → Bool) → DrawnWire n
  | 0, _ => empty
  | n + 1, p => (pivot n (fun i => p (Fin.castSucc i))).parallel (pivotOne (p (Fin.last n)))

private theorem eq_split {n m : ℕ} {α : Type*} (a b : Fin (n + m) → α) :
    a = b ↔ (fun i => a (Fin.castAdd m i)) = (fun i => b (Fin.castAdd m i)) ∧
      (fun i => a (Fin.natAdd n i)) = (fun i => b (Fin.natAdd n i)) := by
  constructor
  · rintro rfl; exact ⟨rfl, rfl⟩
  · rintro ⟨hl, hr⟩
    ext i
    induction i using Fin.addCases with
    | left i => exact congrFun hl i
    | right i => exact congrFun hr i

/-- The matching sum of the parallel path construction is exactly common XOR. -/
@[simp] theorem kernel_pivot (n : ℕ) (p a b : Fin n → Bool) :
    (pivot n p).kernel a b = if a = (fun i => Bool.xor (p i) (b i)) then 1 else 0 := by
  classical
  induction n with
  | zero =>
    have h : a = (fun i => Bool.xor (p i) (b i)) := Subsingleton.elim _ _
    change wireKernel emptyWireGraph Fin.elim0 Fin.elim0 a b = _
    rw [emptyWireGraph_wireKernel, ite_eq_left h]
  | succ n ih =>
    rw [pivot, kernel_parallel, ih, kernel_pivotOne]
    simp only [eq_split a (fun i => Bool.xor (p i) (b i))]
    have hp : (fun i : Fin 1 => Bool.xor (p (Fin.last n)) (b (Fin.natAdd n i))) =
        (fun i : Fin 1 => Bool.xor (p (Fin.natAdd n i)) (b (Fin.natAdd n i))) := by
      ext i; fin_cases i; rfl
    rw [hp]
    have hcast (i : Fin n) : Fin.castAdd 1 i = i.castSucc := by apply Fin.ext; rfl
    simp only [hcast]
    split_ifs <;> simp_all

theorem weightsIn_pivotOne (p : Bool) (K : Subfield ℂ) : (pivotOne p).weightsIn K := by
  cases p <;> intro e <;> exact K.one_mem

theorem weightsIn_pivot (n : ℕ) (p : Fin n → Bool) (K : Subfield ℂ) :
    (pivot n p).weightsIn K := by
  induction n with
  | zero => intro e; exact e.elim0
  | succ n ih => exact weightsIn_parallel _ _ K (ih _) (weightsIn_pivotOne _ K)

end DrawnWire

namespace DrawnState
variable {n : ℕ}

/-- Attach one explicit identity/complement component at each output. -/
def pivot (W : DrawnState n) (p : Fin n → Bool) : DrawnState n :=
  W.applyGate (DrawnWire.pivot n p)

/-- The signature of the actual glued graph is the unsigned XOR pivot. -/
theorem signature_pivot (W : DrawnState n) (p x : Fin n → Bool) :
    (W.pivot p).signature x = W.signature (fun i => Bool.xor (p i) (x i)) := by
  classical
  rw [pivot, signature_applyGate]
  simp [DrawnWire.kernel_pivot]

theorem weightsIn_pivot (W : DrawnState n) (p : Fin n → Bool) (K : Subfield ℂ)
    (hW : W.weightsIn K) : (W.pivot p).weightsIn K :=
  weightsIn_applyGate _ _ K hW (DrawnWire.weightsIn_pivot n p K)

end DrawnState


/-- Explicit finite disk witness for every scaled XOR-pivoted Pfaffian table,
with every weight in the original coefficient subfield. -/
theorem pivotedPrincipalPfaffian_diskWitness {n : ℕ}
    (c : ℂ) (A : Matrix (Fin n) (Fin n) ℂ) (p : Fin n → Bool) (hn : 0 < n)
    (hA : ∀ i j, A i j = -A j i) (hdiag : ∀ i, A i i = 0)
    (K : Subfield ℂ) (hc : c ∈ K) (hK : ∀ i j, i < j → A i j ∈ K) :
    ∃ (v e : ℕ) (G : WeightedGraph (Fin v) (Fin e) ℂ) (ext : Fin n → Fin v),
      Nonempty (PlanarDrawing G ext) ∧ (∀ a, G.weight a ∈ K) ∧
      ∀ x, deletionSignature G ext x =
        c * MatchgateWidth.principalPfaffian A
          (bridgeBitsEquiv (Fin n) (fun i => Bool.xor (p i) (x i))) := by
  let W := (DrawnState.scaledPrincipalPfaffian c A hn).pivot p
  let v := (Fintype.equivFin W.V).symm
  let e := (Fintype.equivFin W.E).symm
  refine ⟨Fintype.card W.V, Fintype.card W.E, W.graph.reindex v e,
    (fun i => v.symm (W.output i)), ⟨W.drawing.toDisk.reindex v e⟩, ?_, ?_⟩
  · intro a
    exact DrawnState.weightsIn_pivot _ p K
      (DrawnState.weightsIn_scaledPrincipalPfaffian c A hn K hc hK) (e a)
  · intro x
    rw [deletionSignature_reindex]
    change W.signature x = _
    rw [DrawnState.signature_pivot]
    exact DrawnState.signature_scaledPrincipalPfaffian c A hn hA hdiag _

/-- The Boolean and graph boundary conventions agree under arbitrary XOR. -/
theorem bridgeBitsEquiv_booleanWord_xor {n : ℕ} (p : BooleanInput n)
    (y : Fin n → Bool) :
    bridgeBitsEquiv (Fin n) (fun i => Bool.xor ((booleanWordEquiv n) p i) (y i)) =
      booleanSubsetEquiv n (pfaffianXor p ((booleanWordEquiv n).symm y)) := by
  ext i
  simp only [bridgeBitsEquiv, Equiv.coe_fn_mk, Finset.mem_filter, Finset.mem_univ, true_and,
    mem_booleanSubsetEquiv]
  change Bool.xor (decide (p i = 1)) (y i) = true ↔
    (if p i = (if y i then (1 : Fin 2) else 0) then (0 : Fin 2) else 1) = 1
  generalize p i = a
  generalize y i = b
  fin_cases a <;> cases b <;> decide

/-- The literal MGI locus has constructive finite disk realizations over any
coefficient field embedded in the complex numbers. -/
theorem BooleanMatchgateIdentities.diskWitness_map {n : ℕ} {K : Type*} [Field K]
    (φ : K →+* ℂ) {f : BooleanTable n K} (hf : BooleanMatchgateIdentities f)
    (hn : 0 < n) :
    ∃ (v e : ℕ) (G : WeightedGraph (Fin v) (Fin e) ℂ) (ext : Fin n → Fin v),
      Nonempty (PlanarDrawing G ext) ∧ (∀ a, ∃ k : K, G.weight a = φ k) ∧
      ∀ y, deletionSignature G ext y = φ (f ((booleanWordEquiv n).symm y)) := by
  obtain ⟨p, a, ha⟩ := hf.exists_pfaffianPivotChart
  let b : PfaffianChartParameter n → ℂ := fun t => φ (a t)
  obtain ⟨v, e, G, ext, hd, hw, hs⟩ := pivotedPrincipalPfaffian_diskWitness
    (b none) (pfaffianChartMatrix b) ((booleanWordEquiv n) p) hn
    (fun i j => pfaffianChartMatrix_skew b j i) (pfaffianChartMatrix_diag b)
    φ.fieldRange (by exact ⟨a none, rfl⟩)
    (by intro i j hij; rw [pfaffianChartMatrix_upper b i j hij]; exact ⟨_, rfl⟩)
  refine ⟨v, e, G, ext, hd, ?_, ?_⟩
  · intro q
    obtain ⟨k, hk⟩ := hw q
    exact ⟨k, hk.symm⟩
  · intro y
    rw [hs, bridgeBitsEquiv_booleanWord_xor, ha]
    simp only [pfaffianPivotChart, Fin.val_zero, pow_zero, one_mul,
      pfaffianChart_map]
    rfl

/-- Rational MGI signatures are realized by actual rational-weighted finite
planar graphs, in exactly the project's Boolean boundary enumeration. -/
theorem BooleanMatchgateIdentities.rational_diskWitness {n : ℕ}
    {f : BooleanTable n ℚ} (hf : BooleanMatchgateIdentities f) (hn : 0 < n) :
    ∃ (v e : ℕ) (G : WeightedGraph (Fin v) (Fin e) ℂ) (ext : Fin n → Fin v),
      Nonempty (PlanarDrawing G ext) ∧ (∀ a, ∃ q : ℚ, G.weight a = (q : ℂ)) ∧
      ∀ y, deletionSignature G ext y = (f ((booleanWordEquiv n).symm y) : ℂ) :=
  hf.diskWitness_map (Rat.castHom ℂ) hn


/-- The constructive coefficient-field theorem also includes nullary signatures:
the only graph needed there is a single internal edge of the prescribed weight. -/
theorem BooleanMatchgateIdentities.diskWitness_map_all {n : ℕ} {K : Type*} [Field K]
    (φ : K →+* ℂ) {f : BooleanTable n K} (hf : BooleanMatchgateIdentities f) :
    ∃ (v e : ℕ) (G : WeightedGraph (Fin v) (Fin e) ℂ) (ext : Fin n → Fin v),
      Nonempty (PlanarDrawing G ext) ∧ (∀ a, ∃ k : K, G.weight a = φ k) ∧
      ∀ y, deletionSignature G ext y = φ (f ((booleanWordEquiv n).symm y)) := by
  cases n with
  | zero =>
    let z : BooleanInput 0 := Fin.elim0
    refine ⟨2, 1, scalarEdgeGraph (φ (f z)), Fin.elim0,
      ⟨scalarEdgeDrawing (φ (f z))⟩, ?_, ?_⟩
    · intro a; exact ⟨f z, rfl⟩
    · intro y
      have hy : (booleanWordEquiv 0).symm y = z := Subsingleton.elim _ _
      have ha : deletionActive (Fin.elim0 : Fin 0 → Fin 2) y = Finset.univ := by
        ext v; simp [deletionActive]
      rw [deletionSignature, ha, scalarEdgeGraph_perfectMatch, hy]
  | succ n => exact hf.diskWitness_map φ (Nat.succ_pos n)

/-- Rational field preservation, including zero arity and zero signatures. -/
theorem BooleanMatchgateIdentities.rational_diskWitness_all {n : ℕ}
    {f : BooleanTable n ℚ} (hf : BooleanMatchgateIdentities f) :
    ∃ (v e : ℕ) (G : WeightedGraph (Fin v) (Fin e) ℂ) (ext : Fin n → Fin v),
      Nonempty (PlanarDrawing G ext) ∧ (∀ a, ∃ q : ℚ, G.weight a = (q : ℂ)) ∧
      ∀ y, deletionSignature G ext y = (f ((booleanWordEquiv n).symm y) : ℂ) :=
  hf.diskWitness_map_all (Rat.castHom ℂ)

/-- Every literal complex MGI signature is an actual ordered disk matchgate,
with the Boolean coordinate conversion exposed and no realization assumption. -/
theorem BooleanMatchgateIdentities.diskRealizable {n : ℕ}
    {f : BooleanTable n ℂ} (hf : BooleanMatchgateIdentities f) :
    DiskRealizable (fun y => f ((booleanWordEquiv n).symm y)) := by
  obtain ⟨v, e, G, ext, hd, _, hs⟩ := hf.diskWitness_map_all (RingHom.id ℂ)
  exact ⟨v, e, G, ext, hd, fun y => (hs y).symm⟩

end
end MatchgateWidth
