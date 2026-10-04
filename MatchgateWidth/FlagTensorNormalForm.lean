import MatchgateWidth.TransformedSupport
import MatchgateWidth.MGIOperations
import MatchgateWidth.RankTwoGaussianHull
import MatchgateWidth.UniformBooleanPlaneEmbedding
import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition

/-! # Rank-one stripping without changing the order of ports

This is the algebraic form of source Lemma 10.9, with complete finite-array
semantics and literal ordered matchgate identities as the incoming hypothesis.
All factorizations are proved from actual flattening supports. Selected ports
are replaced in place; no permutation of Boolean boundary wires occurs.

Main results:
* `rankOne_strip_all_ports` and `all_line_supports_pure_decomposition` give the
  all-rays case, including nonzero factors and pure transformed vectors.
* `exists_uniform_even_odd_flag_basis` chooses primitive endpoint data from the plane
  alone, independently of the tensor and its arity.
* `fixed_adapted_flag_normal_form` uses just this fixed endpoint basis and one
  fixed ray vector, preserving the original order and proving that the core is
  nonzero, has all mode ranks two, and has arity zero or at least two.
* `flag_normal_form_plane_or_line` derives the ray generators and the canonical
  increasing retained-port embedding directly from the actual supports.

`FlagTensorNormalFormDisk` constructs genuine disk graph witnesses for the
resulting cores. A graph-to-MGI theorem is not assumed in the algebraic proofs.
-/
namespace MatchgateWidth
noncomputable section
open scoped Classical symmDiff

variable {K P D : Type*} [Field K] [Fintype P] [DecidableEq P] [Fintype D]

/-- An actual column of a flattening belongs to its column support. -/
theorem portFlatten_column_mem (T : (P → D) → K) (j : P)
    (a : {i : P // i ≠ j} → D) :
    (fun d => T (insertBoundaryCoordinate j d a)) ∈ columnSupport (portFlatten T j) := by
  classical
  refine ⟨Pi.single a 1, ?_⟩
  ext d
  simp [Matrix.mulVec, dotProduct, portFlatten, Pi.single_apply]

/-- A one-dimensional mode is genuinely a vector factor: changing only that
coordinate multiplies by the ratio of the vector's two entries. -/
theorem rankOne_port_factor (T : (P → D) → K) (j : P) (q : D → K)
    (hq : columnSupport (portFlatten T j) ≤ Submodule.span K {q})
    (p : D) (hp : q p ≠ 0) (x : P → D) :
    T x = (q (x j) / q p) * T (Function.update x j p) := by
  classical
  let a : {i : P // i ≠ j} → D := fun i => x i
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hq (portFlatten_column_mem T j a))
  have hx : insertBoundaryCoordinate j (x j) a = x := by
    funext i
    by_cases hi : i = j <;> simp [insertBoundaryCoordinate, a, hi]
  have hp' : insertBoundaryCoordinate j p a = Function.update x j p := by
    funext i
    by_cases hi : i = j <;> simp [insertBoundaryCoordinate, a, hi]
  have hcx := congrFun hc (x j)
  have hcp := congrFun hc p
  simp only [Pi.smul_apply, smul_eq_mul] at hcx hcp
  rw [hx] at hcx
  rw [hp'] at hcp
  rw [← hcx, ← hcp]
  field_simp

/-- Pin a finite set of ports in place. -/
def pinPorts (s : Finset P) (p x : P → D) : P → D :=
  fun i => if i ∈ s then p i else x i

omit [Fintype P] [Fintype D] in
@[simp] theorem pinPorts_empty (p x : P → D) : pinPorts ∅ p x = x := by
  funext i
  simp [pinPorts]

/-- Simultaneous rank-one stripping, with the exact scalar normalization. -/
theorem rankOne_strip_ports (T : (P → D) → K) (s : Finset P)
    (q : P → D → K) (p : P → D)
    (hq : ∀ j ∈ s, columnSupport (portFlatten T j) ≤ Submodule.span K {q j})
    (hp : ∀ j ∈ s, q j (p j) ≠ 0) (x : P → D) :
    T x = (∏ j ∈ s, q j (x j) / q j (p j)) * T (pinPorts s p x) := by
  classical
  induction s using Finset.induction_on generalizing x with
  | empty => simp
  | @insert j s hj ih =>
    have hsj := hq j (Finset.mem_insert_self _ _)
    have hpj := hp j (Finset.mem_insert_self _ _)
    rw [rankOne_port_factor T j (q j) hsj (p j) hpj x]
    rw [ih (fun i hi => hq i (Finset.mem_insert_of_mem hi))
      (fun i hi => hp i (Finset.mem_insert_of_mem hi)) (Function.update x j (p j))]
    have hprod : (∏ i ∈ s, q i (Function.update x j (p j) i) / q i (p i)) =
        ∏ i ∈ s, q i (x i) / q i (p i) := by
      apply Finset.prod_congr rfl
      intro i hi
      have hij : i ≠ j := by
        intro he
        subst i
        exact hj hi
      rw [Function.update_of_ne hij]
    have hpin : pinPorts s p (Function.update x j (p j)) = pinPorts (insert j s) p x := by
      funext i
      by_cases hij : i = j
      · subst i; simp [pinPorts, hj]
      · simp [pinPorts, hij]
    rw [hprod, hpin, Finset.prod_insert hj]
    ring

/-- Every line support has a nonzero generator; this is derived from its
actual finite-dimensional support, not an assumed tensor factorization. -/
theorem exists_generator_of_finrank_one (S : Submodule K (D → K))
    (hS : Module.finrank K S = 1) :
    ∃ q : D → K, q ≠ 0 ∧ S = Submodule.span K {q} := by
  obtain ⟨v, hv, hgen⟩ := finrank_eq_one_iff'.mp hS
  refine ⟨v, ?_, ?_⟩
  · intro hz
    exact hv (Subtype.ext hz)
  · apply le_antisymm
    · intro w hw
      obtain ⟨c, hc⟩ := hgen ⟨w, hw⟩
      exact Submodule.mem_span_singleton.mpr ⟨c, congrArg Subtype.val hc⟩
    · exact Submodule.span_le.mpr (by simp)

/-- If every port has line support, the full array is completely
 decomposable, including the precise scalar and all original port positions. -/
theorem rankOne_strip_all_ports (T : (P → D) → K)
    (hT : T ≠ 0)
    (hline : ∀ j, Module.finrank K (columnSupport (portFlatten T j)) = 1) :
    ∃ (c : K) (q : P → D → K), c ≠ 0 ∧ (∀ j, q j ≠ 0) ∧
      ∀ x, T x = c * ∏ j, q j (x j) := by
  classical
  have hgen := fun j => exists_generator_of_finrank_one _ (hline j)
  choose q hq hspan using hgen
  have hpin : ∀ j, ∃ d, q j d ≠ 0 := by
    intro j
    by_contra h
    push Not at h
    exact hq j (funext h)
  choose p hp using hpin
  let v : P → D → K := fun j d => q j d / q j (p j)
  have heq (x : P → D) : T x = T p * ∏ j, v j (x j) := by
    have h := rankOne_strip_ports T Finset.univ q p
      (fun j _ => (hspan j).le) (fun j _ => hp j) x
    have hp' : pinPorts Finset.univ p x = p := by funext i; simp [pinPorts]
    simpa only [hp', mul_comm, v] using h
  refine ⟨T p, v, ?_, ?_, heq⟩
  · intro hz
    apply hT
    funext x
    simpa [hz] using heq x
  · intro j hv
    have := congrFun hv (p j)
    simp [v, hp j] at this

/-- The residual tensor obtained by pinning the complement of an embedding.
For ordered port types the embedding will always be strictly increasing. -/
def arrayPin {A : Type*} (e : A ↪ P) (p : P → D)
    (T : (P → D) → K) : (A → D) → K :=
  fun x => T (Function.extend e x p)

/-- Pinning complementary coordinates only selects flattening columns. -/
theorem arrayPin_port_support_le {A : Type*} [Fintype A] [DecidableEq A]
    (e : A ↪ P) (p : P → D) (T : (P → D) → K) (j : A) :
    columnSupport (portFlatten (arrayPin e p T) j) ≤
      columnSupport (portFlatten T (e j)) := by
  classical
  rw [columnSupport, Matrix.range_mulVecLin, Submodule.span_le]
  rintro _ ⟨a, rfl⟩
  let y := Function.extend e (insertBoundaryCoordinate j (p (e j)) a) p
  have heq (d : D) : Function.extend e (insertBoundaryCoordinate j d a) p =
      insertBoundaryCoordinate (e j) d (fun i => y i) := by
    funext i
    by_cases hi : ∃ k, e k = i
    · obtain ⟨k, rfl⟩ := hi
      rw [e.injective.extend_apply]
      by_cases hk : k = j
      · subst k; simp
      · rw [insertBoundaryCoordinate_ne _ _ _ _ hk,
          insertBoundaryCoordinate_ne _ _ _ _ (fun h => hk (e.injective h))]
        simp [y, e.injective.extend_apply, insertBoundaryCoordinate, hk]
    · rw [Function.extend_apply' _ _ _ hi]
      have hij : i ≠ e j := fun h => hi ⟨j, h.symm⟩
      rw [insertBoundaryCoordinate_ne _ _ _ _ hij]
      exact (Function.extend_apply' _ _ _ hi).symm
  have hcol := portFlatten_column_mem T (e j) (fun i => y i)
  have heqcol : (portFlatten (arrayPin e p T) j).col a =
      (fun d => T (insertBoundaryCoordinate (e j) d (fun i => y i))) := by
    funext d
    exact congrArg T (heq d)
  rw [heqcol]
  exact hcol

/-- The finite array factorization expressed as an actual residual tensor on
precisely the retained ports. -/
theorem rankOne_strip_complement {A : Type*} [Fintype A] [DecidableEq A]
    (e : A ↪ P) (T : (P → D) → K) (q : P → D → K) (p : P → D)
    (hq : ∀ j, j ∉ Set.range e →
      columnSupport (portFlatten T j) ≤ Submodule.span K {q j})
    (hp : ∀ j, j ∉ Set.range e → q j (p j) ≠ 0) (x : P → D) :
    T x = (∏ j ∈ Finset.univ.filter (fun j => j ∉ Set.range e),
      q j (x j) / q j (p j)) * arrayPin e p T (x ∘ e) := by
  classical
  have h := rankOne_strip_ports T (Finset.univ.filter (fun j => j ∉ Set.range e)) q p
    (fun j hj => hq j (Finset.mem_filter.mp hj).2)
    (fun j hj => hp j (Finset.mem_filter.mp hj).2) x
  have heq : pinPorts (Finset.univ.filter (fun j => j ∉ Set.range e)) p x =
      Function.extend e (x ∘ e) p := by
    funext j
    by_cases hj : ∃ i, e i = j
    · obtain ⟨i, rfl⟩ := hj
      simp [pinPorts, e.injective.extend_apply, Set.mem_range]
    · rw [Function.extend_apply' _ _ _ hj]
      simp [pinPorts, Set.mem_range, hj]
  simpa only [heq, arrayPin] using h

/-- Coordinate pinning along an increasing subsequence preserves literal
Boolean MGI and, importantly, preserves the inherited boundary order. -/
theorem BooleanMatchgateIdentities.arrayPin {s t : ℕ}
    {G : BooleanTable t K} (hG : BooleanMatchgateIdentities G)
    (e : Fin s ↪ Fin t) (he : StrictMono e) (p : BooleanInput t) :
    BooleanMatchgateIdentities (arrayPin e p G) := by
  classical
  let P : Finset (Fin t) := Finset.univ.filter (fun j => j ∉ Set.range e ∧ p j = 1)
  have h := hG.ordered_pin e he P
  have heq : (fun S => G (Function.extend e ((booleanSubsetEquiv s).symm S) p)) =
      (fun S => G ((booleanSubsetEquiv t).symm (S.map e ∆ P))) := by
    funext S
    congr 1
    funext j
    by_cases hj : ∃ i, e i = j
    · obtain ⟨i, rfl⟩ := hj
      rw [e.injective.extend_apply]
      simp [booleanSubsetEquiv, P, Finset.mem_symmDiff, Set.mem_range]
    · rw [Function.extend_apply' _ _ _ hj]
      have hmap : j ∉ S.map e := by
        simpa [Finset.mem_map] using (fun i (_ : i ∈ S) => fun hij => hj ⟨i, hij⟩)
      have hnot : j ∉ Set.range e := hj
      simp only [booleanSubsetEquiv, Equiv.coe_fn_symm_mk]
      simp [Finset.mem_symmDiff, hmap, P]
      generalize hval : p j = b
      fin_cases b <;> simp_all
  change MatchgateIdentities (fun S => G (Function.extend e ((booleanSubsetEquiv s).symm S) p))
  rw [heq]
  exact h

/-- Keep complete Boolean blocks at increasing original port positions. -/
def blockPortEmb {m n : ℕ} (e : Fin m ↪ Fin n) (t : ℕ) : Fin (m*t) ↪ Fin (n*t) :=
  { toFun := fun j => finProdFinEquiv (e (finProdFinEquiv.symm j).1,
        (finProdFinEquiv.symm j).2)
    inj' := by
      intro a b h
      have he := finProdFinEquiv.injective h
      apply finProdFinEquiv.symm.injective
      apply Prod.ext
      · exact e.injective (congrArg Prod.fst he)
      · exact congrArg (fun z : Fin n × Fin t => z.2) he }

@[simp] theorem blockPortEmb_apply {m n t : ℕ} (e : Fin m ↪ Fin n)
    (i : Fin m) (j : Fin t) :
    blockPortEmb e t (finProdFinEquiv (i,j)) = finProdFinEquiv (e i,j) := by
  change finProdFinEquiv (e (finProdFinEquiv.symm (finProdFinEquiv (i,j))).1,
    (finProdFinEquiv.symm (finProdFinEquiv (i,j))).2) = _
  rw [Equiv.symm_apply_apply]

/-- Block pinning is increasing at the wire level, even across gaps between
retained ports. This is the order certificate used for MGI closure. -/
theorem blockPortEmb_strictMono {m n t : ℕ} (e : Fin m ↪ Fin n)
    (he : StrictMono e) : StrictMono (blockPortEmb e t) := by
  intro a b hab
  obtain ⟨⟨i,j⟩, rfl⟩ := finProdFinEquiv.surjective a
  obtain ⟨⟨k,l⟩, rfl⟩ := finProdFinEquiv.surjective b
  simp only [blockPortEmb_apply]
  change j.val + t * i.val < l.val + t * k.val at hab
  change j.val + t * (e i).val < l.val + t * (e k).val
  have hj := j.isLt
  have hl := l.isLt
  have hik : i ≤ k := by
    by_contra h
    have hki : k.val + 1 ≤ i.val := by omega
    nlinarith
  rcases hik.eq_or_lt with hik | hik
  · subst k
    omega
  · have hei : (e i).val < (e k).val := he hik
    nlinarith

/-- Extending a block assignment and then flattening is literally the same
assignment as pinning all omitted wires. -/
theorem flattenBooleanBlocks_extend {m n t : ℕ} (e : Fin m ↪ Fin n)
    (p : Fin n → BooleanInput t) (x : Fin m → BooleanInput t) :
    flattenBooleanBlocks (Function.extend e x p) =
      Function.extend (blockPortEmb e t) (flattenBooleanBlocks x) (flattenBooleanBlocks p) := by
  funext a
  obtain ⟨⟨i,j⟩, rfl⟩ := finProdFinEquiv.surjective a
  rw [flattenBooleanBlocks_apply]
  by_cases hi : ∃ k, e k = i
  · obtain ⟨k, rfl⟩ := hi
    rw [e.injective.extend_apply,
      ← blockPortEmb_apply e k j, (blockPortEmb e t).injective.extend_apply]
    simp
  · have hn : ¬∃ a, blockPortEmb e t a = finProdFinEquiv (i,j) := by
      rintro ⟨a, ha⟩
      obtain ⟨⟨k,l⟩, rfl⟩ := finProdFinEquiv.surjective a
      rw [blockPortEmb_apply] at ha
      exact hi ⟨k, congrArg Prod.fst (finProdFinEquiv.injective ha)⟩
    rw [Function.extend_apply' _ _ _ hi, Function.extend_apply' _ _ _ hn]
    simp

/-- Actual arbitrary-pattern block pins preserve MGI in the inherited order. -/
theorem BooleanMatchgateIdentities.blockArrayPin {m n t : ℕ}
    {G : (Fin n → BooleanInput t) → K}
    (hG : BooleanMatchgateIdentities (fun z => G ((booleanBlocksEquiv n t).symm z)))
    (e : Fin m ↪ Fin n) (he : StrictMono e) (p : Fin n → BooleanInput t) :
    BooleanMatchgateIdentities
      (fun z => MatchgateWidth.arrayPin e p G ((booleanBlocksEquiv m t).symm z)) := by
  have h := hG.arrayPin (blockPortEmb e t) (blockPortEmb_strictMono e he)
    (flattenBooleanBlocks p)
  have heq : (fun z => MatchgateWidth.arrayPin e p G ((booleanBlocksEquiv m t).symm z)) =
      MatchgateWidth.arrayPin (blockPortEmb e t) (flattenBooleanBlocks p)
        (fun z => G ((booleanBlocksEquiv n t).symm z)) := by
    funext z
    unfold MatchgateWidth.arrayPin
    congr 1
    apply (booleanBlocksEquiv n t).injective
    change flattenBooleanBlocks (Function.extend e ((booleanBlocksEquiv m t).symm z) p) = _
    rw [flattenBooleanBlocks_extend]
    change Function.extend (blockPortEmb e t)
      ((booleanBlocksEquiv m t) ((booleanBlocksEquiv m t).symm z)) _ = _
    simp only [Equiv.apply_symm_apply]
  rw [heq]
  exact h

/-- The wires of one block form an increasing subsequence of all wires. -/
def portWireEmb {n t : ℕ} (j : Fin n) : Fin t ↪ Fin (n*t) :=
  { toFun := fun k => finProdFinEquiv (j,k)
    inj' := by intro a b h; exact congrArg Prod.snd (finProdFinEquiv.injective h) }

theorem portWireEmb_strictMono {n t : ℕ} (j : Fin n) : StrictMono (portWireEmb (t := t) j) := by
  intro a b hab
  change a.val + t * j.val < b.val + t * j.val
  exact Nat.add_lt_add_right hab _

/-- Every actual one-block slice of an MGI tensor is MGI, by coordinate pins
outside that block, rather than by moving that block to another position. -/
theorem BooleanMatchgateIdentities.portSlice {n t : ℕ}
    {G : (Fin n → BooleanInput t) → K}
    (hG : BooleanMatchgateIdentities (fun z => G ((booleanBlocksEquiv n t).symm z)))
    (j : Fin n) (a : {i : Fin n // i ≠ j} → BooleanInput t) :
    BooleanMatchgateIdentities (fun d => G (insertBoundaryCoordinate j d a)) := by
  let p := insertBoundaryCoordinate j (fun _ => 0) a
  have h := hG.arrayPin (portWireEmb j) (portWireEmb_strictMono j) (flattenBooleanBlocks p)
  have heq (d : BooleanInput t) :
      (booleanBlocksEquiv n t).symm
        (Function.extend (portWireEmb j) d (flattenBooleanBlocks p)) =
      insertBoundaryCoordinate j d a := by
    funext i k
    change Function.extend (portWireEmb j) d (flattenBooleanBlocks p)
      (finProdFinEquiv (i,k)) = _
    by_cases hi : i = j
    · subst i
      change Function.extend (portWireEmb j) d (flattenBooleanBlocks p)
        (portWireEmb j k) = _
      rw [(portWireEmb j).injective.extend_apply, insertBoundaryCoordinate_same]
    · have hn : ¬∃ l, portWireEmb j l = finProdFinEquiv (i,k) := by
        rintro ⟨l, hl⟩
        exact hi (congrArg Prod.fst (finProdFinEquiv.injective hl)).symm
      rw [Function.extend_apply' _ _ _ hn, flattenBooleanBlocks_apply]
      simp [p, insertBoundaryCoordinate_ne _ _ _ _ hi]
  change BooleanMatchgateIdentities (fun d => G ((booleanBlocksEquiv n t).symm
    (Function.extend (portWireEmb j) d (flattenBooleanBlocks p)))) at h
  simpa only [heq] using h

/-- A ray in a nonzero block-MGI tensor is itself a pure MGI vector.
The nonzero scalar is found in an actual column by pinning all other wires. -/
theorem BooleanMatchgateIdentities.ray_of_port_support {n t : ℕ}
    {G : (Fin n → BooleanInput t) → K}
    (hG : BooleanMatchgateIdentities (fun z => G ((booleanBlocksEquiv n t).symm z)))
    (hne : G ≠ 0) (j : Fin n) (q : BooleanTable t K)
    (hq : columnSupport (portFlatten G j) ≤ Submodule.span K {q}) :
    BooleanMatchgateIdentities q := by
  classical
  obtain ⟨x, hx⟩ : ∃ x, G x ≠ 0 := by
    by_contra h
    push Not at h
    exact hne (funext h)
  let a : {i : Fin n // i ≠ j} → BooleanInput t := fun i => x i
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hq (portFlatten_column_mem G j a))
  have hcne : c ≠ 0 := by
    intro hc0
    have he := congrFun hc (x j)
    have hi : insertBoundaryCoordinate j (x j) a = x := by
      funext i
      by_cases hij : i = j <;> simp [insertBoundaryCoordinate, a, hij]
    simp [hc0, hi] at he
    exact hx he.symm
  have hslice := hG.portSlice j a
  rw [← hc] at hslice
  have hpure := hslice.smul c⁻¹
  simpa [smul_smul, hcne] using hpure

/-- Rank-one stripping leaves every retained mode support unchanged. -/
theorem rankOne_strip_preserves_support {A : Type*} [Fintype A] [DecidableEq A]
    (e : A ↪ P) (T : (P → D) → K) (q : P → D → K) (p : P → D)
    (hq : ∀ j, j ∉ Set.range e →
      columnSupport (portFlatten T j) ≤ Submodule.span K {q j})
    (hp : ∀ j, j ∉ Set.range e → q j (p j) ≠ 0) (j : A) :
    columnSupport (portFlatten (arrayPin e p T) j) =
      columnSupport (portFlatten T (e j)) := by
  classical
  apply le_antisymm (arrayPin_port_support_le e p T j)
  rw [columnSupport, Matrix.range_mulVecLin, Submodule.span_le]
  rintro _ ⟨a, rfl⟩
  let x : P → D := insertBoundaryCoordinate (e j) (p (e j)) a
  let b : {i : A // i ≠ j} → D := fun i => x (e i)
  let c := ∏ i ∈ Finset.univ.filter (fun i => i ∉ Set.range e), q i (x i) / q i (p i)
  have heq : (portFlatten T (e j)).col a =
      c • (fun d => arrayPin e p T (insertBoundaryCoordinate j d b)) := by
    funext d
    have h := rankOne_strip_complement e T q p hq hp (insertBoundaryCoordinate (e j) d a)
    have hprod : (∏ i ∈ Finset.univ.filter (fun i => i ∉ Set.range e),
        q i (insertBoundaryCoordinate (e j) d a i) / q i (p i)) = c := by
      apply Finset.prod_congr rfl
      intro i hi
      have hn : i ≠ e j := by
        intro hij
        exact (Finset.mem_filter.mp hi).2 ⟨j, hij.symm⟩
      simp [x, insertBoundaryCoordinate_ne _ _ _ _ hn]
    have harg : insertBoundaryCoordinate (e j) d a ∘ e = insertBoundaryCoordinate j d b := by
      funext i
      by_cases hi : i = j
      · subst i; simp
      · have hn : e i ≠ e j := fun h => hi (e.injective h)
        simp [Function.comp_apply, insertBoundaryCoordinate_ne _ _ _ _ hi,
          insertBoundaryCoordinate_ne _ _ _ _ hn, b, x]
    simpa only [hprod, harg, Pi.smul_apply, smul_eq_mul, Matrix.col_apply, portFlatten] using h
  rw [heq]
  exact Submodule.smul_mem _ _ (portFlatten_column_mem (arrayPin e p T) j b)

/-- A residual tensor obtained by genuine rank-one stripping is nonzero. -/
theorem rankOne_strip_residual_ne_zero {A : Type*} [Fintype A] [DecidableEq A]
    (e : A ↪ P) (T : (P → D) → K) (q : P → D → K) (p : P → D)
    (hne : T ≠ 0)
    (hq : ∀ j, j ∉ Set.range e →
      columnSupport (portFlatten T j) ≤ Submodule.span K {q j})
    (hp : ∀ j, j ∉ Set.range e → q j (p j) ≠ 0) : arrayPin e p T ≠ 0 := by
  intro hz
  apply hne
  funext x
  have h := rankOne_strip_complement e T q p hq hp x
  simpa [hz] using h

/-- One wire in each block is exactly one Boolean coordinate per port. -/
def singleWireBlocksEquiv (m : ℕ) : (Fin m → BooleanInput 1) ≃ BooleanInput m where
  toFun x i := x i 0
  invFun z i _ := z i
  left_inv x := by funext i j; exact congrArg (x i) (Subsingleton.elim _ _)
  right_inv _ := rfl

/-- Expansion in a one-input encoder is an ordinary Boolean sum. -/
theorem leftTransform_one_input_eq {m t : ℕ}
    (Q : Matrix (BooleanInput 1) (BooleanInput t) K)
    (h : BooleanTable m K) (y : Fin m → BooleanInput t) :
    leftTransform Q (fun x => h (fun i => x i 0)) y =
      ∑ z : BooleanInput m, h z * ∏ i, Q (fun _ => z i) (y i) := by
  classical
  unfold leftTransform
  rw [← (singleWireBlocksEquiv m).symm.sum_comp]
  rfl

/-- Flag normal form for an actual ordered block-MGI tensor. A single fixed
encoder and decoder are used, all omitted ray factors are kept exactly as
specified, and every retained port keeps its original position. -/
theorem ordered_flag_normal_form {m n t : ℕ}
    (Q : Matrix (BooleanInput 1) (BooleanInput t) K)
    (D : Matrix (BooleanInput t) (BooleanInput 1) K)
    (hD : OrderedMatchgateMatrix D) (hQD : Q * D = 1)
    (e : Fin m ↪ Fin n) (he : StrictMono e)
    (G : (Fin n → BooleanInput t) → K)
    (hG : BooleanMatchgateIdentities (fun z => G ((booleanBlocksEquiv n t).symm z)))
    (hplane : ∀ i, columnSupport (portFlatten G (e i)) ≤ orderedRowSpace Q)
    (q : Fin n → BooleanTable t K)
    (hq : ∀ j, j ∉ Set.range e →
      columnSupport (portFlatten G j) ≤ Submodule.span K {q j})
    (hqne : ∀ j, j ∉ Set.range e → q j ≠ 0) :
    ∃ h : BooleanTable m K, BooleanMatchgateIdentities h ∧
      ∀ x, G x = (∑ z : BooleanInput m, h z * ∏ i, Q (fun _ => z i) (x (e i))) *
        ∏ j ∈ Finset.univ.filter (fun j => j ∉ Set.range e), q j (x j) := by
  classical
  have hex : ∀ j, ∃ y : BooleanInput t, j ∉ Set.range e → q j y ≠ 0 := by
    intro j
    by_cases hj : j ∈ Set.range e
    · exact ⟨fun _ => 0, fun h => (h hj).elim⟩
    · have hh : ∃ y, q j y ≠ 0 := by
        by_contra h
        push Not at h
        exact hqne j hj (funext h)
      obtain ⟨y, hy⟩ := hh
      exact ⟨y, fun _ => hy⟩
  choose p hp using hex
  let S := Finset.univ.filter (fun j => j ∉ Set.range e)
  let c : K := ∏ j ∈ S, q j (p j)
  have hc : c ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun j hj => hp j (Finset.mem_filter.mp hj).2)
  let T : BooleanTable (m*t) K := fun z => arrayPin e p G ((booleanBlocksEquiv m t).symm z)
  have hT : BooleanMatchgateIdentities T := hG.blockArrayPin e he p
  have hTblocks : (fun x => T (flattenBooleanBlocks x)) = arrayPin e p G := by
    funext x
    exact congrArg (arrayPin e p G) ((booleanBlocksEquiv m t).symm_apply_apply x)
  have hsupp : ∀ j, columnSupport (portFlatten (fun x => T (flattenBooleanBlocks x)) j) ≤
      orderedRowSpace Q := by
    rw [hTblocks]
    intro j
    exact (arrayPin_port_support_le e p G j).trans (hplane j)
  let h₀ := booleanPlanePullback D m T
  have h₀mg : BooleanMatchgateIdentities h₀ := hD.booleanPlanePullback m hT
  have hrec := booleanPlanePullback_reconstruct Q D hQD m T hsupp
  have hcoeff (y : Fin m → BooleanInput t) :
      (∑ z : BooleanInput m, h₀ z * ∏ i, Q (fun _ => z i) (y i)) = arrayPin e p G y := by
    have h := congrFun hrec (flattenBooleanBlocks y)
    change leftTransform Q (fun x => h₀ (fun i => x i 0))
      ((booleanBlocksEquiv m t).symm ((booleanBlocksEquiv m t) y)) = _ at h
    rw [Equiv.symm_apply_apply, leftTransform_one_input_eq] at h
    exact h.trans (congrFun hTblocks y)
  refine ⟨c⁻¹ • h₀, h₀mg.smul c⁻¹, ?_⟩
  intro x
  have hstrip := rankOne_strip_complement e G q p hq hp x
  have hprod : (∏ j ∈ S, q j (x j) / q j (p j)) =
      (∏ j ∈ S, q j (x j)) / c := Finset.prod_div_distrib _ _
  change G x = _ * ∏ j ∈ S, q j (x j)
  simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]
  rw [← Finset.mul_sum, hcoeff]
  rw [show (∏ j ∈ Finset.univ.filter (fun j => j ∉ Set.range e),
      q j (x j) / q j (p j)) = (∏ j ∈ S, q j (x j)) / c from hprod] at hstrip
  rw [hstrip]
  simp only [Function.comp_def]
  ring

/-- Product over an injected set of ports and its actual complement. -/
theorem prod_embedding_complement {A : Type*} [Fintype A]
    (e : A ↪ P) (f : P → K) :
    (∏ i, f (e i)) * (∏ j ∈ Finset.univ.filter (fun j => j ∉ Set.range e), f j) =
      ∏ j, f j := by
  classical
  have hc : (Finset.univ.map e)ᶜ = Finset.univ.filter (fun j => j ∉ Set.range e) := by
    ext j
    simp [Set.mem_range]
  have h := Finset.prod_mul_prod_compl (Finset.univ.map e) f
  simpa only [hc, Finset.prod_map] using h

/-- Insert the retained Boolean encoder rows and the fixed ray vectors in the
original port order, then take their genuine sum of tensor products. -/
def flagTensor {m n : ℕ} (E : Matrix (BooleanInput 1) D K)
    (e : Fin m ↪ Fin n) (q : Fin n → D → K) (h : BooleanTable m K) :
    (Fin n → D) → K := fun x =>
  ∑ z : BooleanInput m, h z *
    ∏ j, Function.extend e (fun i => E (fun _ => z i)) q j (x j)

omit [Fintype D] in
/-- The full product definition equals the separate core/ray expression. -/
theorem flagTensor_eq_core_mul_rays {m n : ℕ} (E : Matrix (BooleanInput 1) D K)
    (e : Fin m ↪ Fin n) (q : Fin n → D → K) (h : BooleanTable m K) (x : Fin n → D) :
    flagTensor E e q h x =
      (∑ z : BooleanInput m, h z * ∏ i, E (fun _ => z i) (x (e i))) *
        ∏ j ∈ Finset.univ.filter (fun j => j ∉ Set.range e), q j (x j) := by
  classical
  unfold flagTensor
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro z _
  rw [← prod_embedding_complement e (fun j => Function.extend e (fun i => E (fun _ => z i)) q j (x j))]
  simp only [e.injective.extend_apply]
  have hc : (∏ j ∈ Finset.univ.filter (fun j => j ∉ Set.range e),
      Function.extend e (fun i => E (fun _ => z i)) q j (x j)) =
      ∏ j ∈ Finset.univ.filter (fun j => j ∉ Set.range e), q j (x j) := by
    apply Finset.prod_congr rfl
    intro j hj
    rw [Function.extend_apply' _ _ _ (Finset.mem_filter.mp hj).2]
  rw [hc, mul_assoc]

/-- A coordinate transform of an actual product array transforms every vector. -/
theorem leftTransform_product {B : Type*} [Fintype B]
    (M : Matrix D B K) (q : P → D → K) (y : P → B) :
    leftTransform M (fun x => ∏ i, q i (x i)) y =
      ∏ i, unaryTransform M (q i) (y i) := by
  classical
  simp only [leftTransform, unaryTransform, Fintype.prod_sum, Finset.prod_mul_distrib]

/-- Transforming a sum of pure tensors is the corresponding sum of transformed
pure tensors. This is proved from the complete finite coordinate sum. -/
theorem leftTransform_sum_products {B S : Type*} [Fintype B] [Fintype S]
    (M : Matrix D B K) (q : S → P → D → K) (h : S → K) (y : P → B) :
    leftTransform M (fun x => ∑ z, h z * ∏ i, q z i (x i)) y =
      ∑ z, h z * ∏ i, unaryTransform M (q z i) (y i) := by
  classical
  simp only [leftTransform, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  have hprod := leftTransform_product M (q z) y
  simp only [leftTransform] at hprod
  calc
    _ = h z * (∑ x : P → D, (∏ i, q z i (x i)) * ∏ i, M (x i) (y i)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = _ := by rw [hprod]

/-- Mixed plane/ray reconstruction commutes with the common base transform. -/
theorem leftTransform_flagTensor {B : Type*} [Fintype B] {m n : ℕ}
    (M : Matrix D B K) (E : Matrix (BooleanInput 1) D K)
    (e : Fin m ↪ Fin n) (q : Fin n → D → K) (h : BooleanTable m K) :
    leftTransform M (flagTensor E e q h) =
      flagTensor (E * M) e (fun j => unaryTransform M (q j)) h := by
  classical
  funext y
  unfold flagTensor
  rw [leftTransform_sum_products]
  apply Finset.sum_congr rfl
  intro z _
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  by_cases hj : ∃ i, e i = j
  · obtain ⟨i, rfl⟩ := hj
    simp only [e.injective.extend_apply]
    rfl
  · rw [Function.extend_apply' _ _ _ hj, Function.extend_apply' _ _ _ hj]

/-- The common base maps the span of actual encoder rows to the span of the
actual product rows. -/
theorem span_rows_map_transpose {A B : Type*} [Fintype A] [Fintype B]
    (E : Matrix A D K) (M : Matrix D B K) :
    (Submodule.span K (Set.range E.row)).map M.transpose.mulVecLin =
      Submodule.span K (Set.range (E*M).row) := by
  rw [Submodule.map_span]
  congr 1
  ext u
  constructor
  · rintro ⟨v, ⟨i, rfl⟩, rfl⟩
    refine ⟨i, ?_⟩
    rw [transpose_mulVecLin_eq_unaryTransform]
    rfl
  · rintro ⟨i, rfl⟩
    refine ⟨E.row i, ⟨i, rfl⟩, ?_⟩
    rw [transpose_mulVecLin_eq_unaryTransform]
    rfl

/-- **Primitive-coordinate flag normal form.** The encoder rows and ray
vectors are fixed before the tensor is considered. Full row rank of the
common base transfers an exact lifted factorization back to the original
finite array, with every factor still at its original port. -/
theorem fullRank_flag_normal_form {m n t : ℕ}
    (M : Matrix D (BooleanInput t) K)
    (hM : Function.Injective M.transpose.mulVecLin)
    (E : Matrix (BooleanInput 1) D K)
    (C : Matrix (BooleanInput t) (BooleanInput 1) K)
    (hC : OrderedMatchgateMatrix C) (hEC : (E*M)*C = 1)
    (e : Fin m ↪ Fin n) (he : StrictMono e)
    (T : (Fin n → D) → K)
    (hT : BooleanMatchgateIdentities (leftBooleanLift M n T))
    (hplane : ∀ i, columnSupport (portFlatten T (e i)) ≤
      Submodule.span K (Set.range E.row))
    (q : Fin n → D → K)
    (hq : ∀ j, j ∉ Set.range e →
      columnSupport (portFlatten T j) ≤ Submodule.span K {q j})
    (hqne : ∀ j, j ∉ Set.range e → q j ≠ 0) :
    ∃ h : BooleanTable m K, BooleanMatchgateIdentities h ∧ T = flagTensor E e q h := by
  classical
  let G := leftTransform M T
  let r := fun j => unaryTransform M (q j)
  have hG : BooleanMatchgateIdentities (fun z => G ((booleanBlocksEquiv n t).symm z)) := hT
  have hplaneG : ∀ i, columnSupport (portFlatten G (e i)) ≤ orderedRowSpace (E*M) := by
    intro i
    rw [transformed_port_support M hM]
    exact (Submodule.map_mono (hplane i)).trans_eq (span_rows_map_transpose E M)
  have hr : ∀ j, j ∉ Set.range e → columnSupport (portFlatten G j) ≤ Submodule.span K {r j} := by
    intro j hj
    rw [transformed_port_support M hM]
    have h := Submodule.map_mono (f := M.transpose.mulVecLin) (hq j hj)
    rw [Submodule.map_span] at h
    simpa only [Set.image_singleton, transpose_mulVecLin_eq_unaryTransform] using h
  have hrne : ∀ j, j ∉ Set.range e → r j ≠ 0 := by
    intro j hj hz
    apply hqne j hj
    apply hM
    rw [map_zero, transpose_mulVecLin_eq_unaryTransform]
    exact hz
  obtain ⟨h, hmg, hfactor⟩ := ordered_flag_normal_form (E*M) C hC hEC e he G hG hplaneG r hr hrne
  refine ⟨h, hmg, leftTransform_injective M hM ?_⟩
  rw [leftTransform_flagTensor]
  funext x
  exact (hfactor x).trans (flagTensor_eq_core_mul_rays (E*M) e r h x).symm

/-- Any fixed family of vectors in the transformed plane has unique primitive
preimages under a full-row-rank base; spanning is reflected as well. -/
theorem exists_primitive_plane_encoder {r t : ℕ}
    (M : Matrix D (BooleanInput t) K)
    (hM : Function.Injective M.transpose.mulVecLin)
    (P₀ : Submodule K (D → K))
    (Q : Matrix (BooleanInput r) (BooleanInput t) K)
    (hspace : orderedRowSpace Q = P₀.map M.transpose.mulVecLin) :
    ∃ E : Matrix (BooleanInput r) D K, E*M = Q ∧
      Submodule.span K (Set.range E.row) = P₀ := by
  classical
  have hex : ∀ i, ∃ u : D → K, u ∈ P₀ ∧ M.transpose.mulVecLin u = Q.row i := by
    intro i
    have hi := row_mem_orderedRowSpace Q i
    rw [hspace] at hi
    exact hi
  choose u huP huQ using hex
  let E : Matrix (BooleanInput r) D K := u
  have hEQ (i) : M.transpose.mulVecLin (E i) = Q.row i := huQ i
  have hmul : E*M = Q := by
    funext i b
    have hh := congrFun (hEQ i) b
    rw [transpose_mulVecLin_eq_unaryTransform] at hh
    exact hh
  refine ⟨E, hmul, ?_⟩
  apply Submodule.map_injective_of_injective hM
  rw [span_rows_map_transpose, hmul]
  exact hspace

/-- **One fixed adapted plane basis, simultaneously at every arity.**
The endpoint encoder is selected from the plane alone. Every admissible left
tensor then has the original-port-order flag expansion in this same basis.
The ray generators are supplied before the tensor and are not normalized or
changed by the construction; all pinning scalars enter the Boolean core. -/
theorem exists_uniform_fullRank_flag_normal_form [CharZero K] {r t : ℕ}
    (M : Matrix D (BooleanInput t) K)
    (hM : Function.Injective M.transpose.mulVecLin)
    (P₀ : Submodule K (D → K))
    (B : Matrix (BooleanInput r) (BooleanInput t) K)
    (hB : OrderedMatchgateMatrix B) (hrB : B.rank = 2)
    (hspace : orderedRowSpace B = P₀.map M.transpose.mulVecLin) :
    ∃ (E : Matrix (BooleanInput 1) D K) (b : ℕ),
      Submodule.span K (Set.range E.row) = P₀ ∧
      OrderedMatchgateMatrix (E*M) ∧ (E*M).rank = 2 ∧ b < 2 ∧
      (E*M).row (fun _ => 0) ≠ 0 ∧ (E*M).row (fun _ => 1) ≠ 0 ∧
      (∀ y, booleanParity y ≠ b → (E*M) (fun _ => 0) y = 0) ∧
      (∀ y, booleanParity y = b → (E*M) (fun _ => 1) y = 0) ∧
      ∀ (m n : ℕ) (e : Fin m ↪ Fin n), StrictMono e →
        ∀ (q : Fin n → D → K), (∀ j, j ∉ Set.range e → q j ≠ 0) →
        ∀ (T : (Fin n → D) → K), BooleanMatchgateIdentities (leftBooleanLift M n T) →
        (∀ i, columnSupport (portFlatten T (e i)) ≤ P₀) →
        (∀ j, j ∉ Set.range e → columnSupport (portFlatten T j) ≤ Submodule.span K {q j}) →
        ∃ h : BooleanTable m K, BooleanMatchgateIdentities h ∧ T = flagTensor E e q h := by
  obtain ⟨Q, C, b, hQ, hC, hQC, hrQ, hQP, hb, h₀, h₁, hp₀, hp₁, _⟩ :=
    exists_uniform_boolean_plane_embedding hB hrB
  obtain ⟨E, hEM, hEP⟩ := exists_primitive_plane_encoder M hM P₀ Q (hQP.trans hspace)
  refine ⟨E, b, hEP, ?_, ?_, hb, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [hEM] using hQ
  · simpa only [hEM] using hrQ
  · simpa only [hEM] using h₀
  · simpa only [hEM] using h₁
  · simpa only [hEM] using hp₀
  · simpa only [hEM] using hp₁
  · intro m n e he q hqne T hT hplane hq
    apply fullRank_flag_normal_form M hM E C hC (by rw [hEM]; exact hQC) e he T hT
    · simpa only [hEP] using hplane
    · exact hq
    · exact hqne

omit [Fintype D] in
/-- A nonzero tensor's flag core cannot be zero. -/
theorem flagTensor_core_ne_zero {m n : ℕ}
    (E : Matrix (BooleanInput 1) D K) (e : Fin m ↪ Fin n)
    (q : Fin n → D → K) (h : BooleanTable m K)
    (hne : flagTensor E e q h ≠ 0) : h ≠ 0 := by
  intro hz
  apply hne
  funext x
  simp [flagTensor, hz]

/-- Every stripped primitive ray maps to an actual pure MGI vector. -/
theorem transformed_ray_is_pure {n t : ℕ}
    (M : Matrix D (BooleanInput t) K)
    (hM : Function.Injective M.transpose.mulVecLin)
    (T : (Fin n → D) → K) (hne : T ≠ 0)
    (hT : BooleanMatchgateIdentities (leftBooleanLift M n T))
    (j : Fin n) (q : D → K)
    (hq : columnSupport (portFlatten T j) ≤ Submodule.span K {q}) :
    BooleanMatchgateIdentities (unaryTransform M q) := by
  have hnon : leftTransform M T ≠ 0 := by
    intro hz
    apply hne
    apply leftTransform_injective M hM
    funext y
    have h := congrFun hz y
    simpa [leftTransform] using h
  apply BooleanMatchgateIdentities.ray_of_port_support hT hnon j (unaryTransform M q)
  rw [transformed_port_support M hM]
  have h := Submodule.map_mono (f := M.transpose.mulVecLin) hq
  rw [Submodule.map_span] at h
  simpa only [Set.image_singleton, transpose_mulVecLin_eq_unaryTransform] using h

/-- Nonzero scalar multiplication leaves an actual port support unchanged. -/
theorem portSupport_smul {c : K} (hc : c ≠ 0) (T : (P → D) → K) (j : P) :
    columnSupport (portFlatten (c • T) j) = columnSupport (portFlatten T j) := by
  have heq : (portFlatten (c • T) j).mulVecLin = c • (portFlatten T j).mulVecLin := by
    apply LinearMap.ext
    intro x
    funext d
    change ((c • portFlatten T j).mulVec x) d = _
    rw [Matrix.smul_mulVec]
    rfl
  unfold columnSupport
  rw [heq]
  exact LinearMap.range_smul _ c hc

omit [Fintype D] in
/-- Pinning the rays of the flag expansion leaves precisely its encoded core,
scaled by the product of the chosen nonzero ray entries. -/
theorem arrayPin_flagTensor {m n : ℕ}
    (E : Matrix (BooleanInput 1) D K) (e : Fin m ↪ Fin n)
    (q : Fin n → D → K) (h : BooleanTable m K) (p : Fin n → D) :
    arrayPin e p (flagTensor E e q h) =
      (∏ j ∈ Finset.univ.filter (fun j => j ∉ Set.range e), q j (p j)) •
        leftTransform E (fun x => h (fun i => x i 0)) := by
  classical
  funext x
  rw [arrayPin, flagTensor_eq_core_mul_rays]
  simp only [e.injective.extend_apply, Pi.smul_apply, smul_eq_mul]
  have hp : (∏ j ∈ Finset.univ.filter (fun j => j ∉ Set.range e),
      q j (Function.extend e x p j)) =
      ∏ j ∈ Finset.univ.filter (fun j => j ∉ Set.range e), q j (p j) := by
    apply Finset.prod_congr rfl
    intro j hj
    rw [Function.extend_apply' _ _ _ (Finset.mem_filter.mp hj).2]
  rw [hp]
  have heq : leftTransform E (fun x => h (fun i => x i 0)) x =
      ∑ z, h z * ∏ i, E (fun _ => z i) (x i) := by
    unfold leftTransform
    rw [← (singleWireBlocksEquiv m).symm.sum_comp]
    rfl
  rw [heq, mul_comm]

/-- Unpacking the one-wire alphabet is a coordinate equivalence, hence does
not change a core's mode ranks. -/
theorem singleWireBlocks_port_finrank {m : ℕ} (h : BooleanTable m K) (j : Fin m) :
    Module.finrank K (columnSupport (portFlatten (fun x : Fin m → BooleanInput 1 =>
      h (fun i => x i 0)) j)) = Module.finrank K (columnSupport (portFlatten h j)) := by
  classical
  let b : BooleanInput 1 ≃ Fin 2 :=
    { toFun := fun x => x 0
      invFun := fun d _ => d
      left_inv := by intro x; funext i; exact congrArg x (Subsingleton.elim _ _)
      right_inv := fun _ => rfl }
  let c : ({i : Fin m // i ≠ j} → BooleanInput 1) ≃ ({i : Fin m // i ≠ j} → Fin 2) :=
    Equiv.piCongrRight (fun _ => b)
  have heq : portFlatten (fun x : Fin m → BooleanInput 1 => h (fun i => x i 0)) j =
      (portFlatten h j).submatrix b c := by
    ext d a
    change h (fun i => insertBoundaryCoordinate j d a i 0) =
      h (insertBoundaryCoordinate j (b d) (c a))
    congr 1
    funext i
    by_cases hi : i = j
    · subst i; simp [b, insertBoundaryCoordinate]
    · simp [b, c, insertBoundaryCoordinate, hi]
  change (portFlatten (fun x : Fin m → BooleanInput 1 => h (fun i => x i 0)) j).rank =
    (portFlatten h j).rank
  rw [heq]
  exact Matrix.rank_submatrix _ b c

/-- If the retained primitive support has dimension two, the corresponding
literal Boolean core mode also has dimension two. -/
theorem flagTensor_core_mode_rank_two {m n : ℕ}
    (E : Matrix (BooleanInput 1) D K)
    (hE : Function.Injective E.transpose.mulVecLin)
    (e : Fin m ↪ Fin n) (q : Fin n → D → K) (h : BooleanTable m K)
    (p : Fin n → D)
    (hq : ∀ j, j ∉ Set.range e → columnSupport (portFlatten (flagTensor E e q h) j) ≤
      Submodule.span K {q j})
    (hp : ∀ j, j ∉ Set.range e → q j (p j) ≠ 0)
    (j : Fin m)
    (hrank : Module.finrank K (columnSupport (portFlatten (flagTensor E e q h) (e j))) = 2) :
    Module.finrank K (columnSupport (portFlatten h j)) = 2 := by
  classical
  have hc : (∏ i ∈ Finset.univ.filter (fun i => i ∉ Set.range e), q i (p i)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i hi => hp i (Finset.mem_filter.mp hi).2)
  have hsupp := rankOne_strip_preserves_support e (flagTensor E e q h) q p hq hp j
  rw [arrayPin_flagTensor, portSupport_smul hc] at hsupp
  have hd := transformed_port_support_finrank E hE (fun x => h (fun i => x i 0)) j
  rw [singleWireBlocks_port_finrank] at hd
  rw [hsupp, hrank] at hd
  exact hd.symm

/-- A Boolean tensor all of whose modes have rank two has either no ports
or at least two; the unary flattening has only one column. -/
theorem boolean_core_arity_zero_or_ge_two {m : ℕ} (h : BooleanTable m K)
    (hrank : ∀ j, Module.finrank K (columnSupport (portFlatten h j)) = 2) :
    m = 0 ∨ 2 ≤ m := by
  by_contra hn
  have hm : m = 1 := by omega
  subst m
  letI : IsEmpty {i : Fin 1 // i ≠ 0} := ⟨fun i => i.property (Subsingleton.elim _ _)⟩
  have hle := Matrix.rank_le_card_width (portFlatten h 0)
  change Module.finrank K (columnSupport (portFlatten h 0)) ≤ _ at hle
  have hh := hrank 0
  have hcard : Fintype.card ({i : Fin 1 // i ≠ 0} → Fin 2) = 1 := by simp
  rw [hh, hcard] at hle
  omega

/-- The endpoint encoder is injective when its transformed rows admit a
right inverse. This uses the actual matrix rank, not an extra basis axiom. -/
theorem primitive_encoder_injective {t : ℕ}
    (M : Matrix D (BooleanInput t) K) (E : Matrix (BooleanInput 1) D K)
    (C : Matrix (BooleanInput t) (BooleanInput 1) K) (hEC : (E*M)*C = 1) :
    Function.Injective E.transpose.mulVecLin := by
  apply transpose_injective_of_rank_eq_card
  apply le_antisymm (Matrix.rank_le_card_height E)
  have hle : ((E*M)*C).rank ≤ E.rank :=
    (Matrix.rank_mul_le_left (E*M) C).trans (Matrix.rank_mul_le_left E M)
  simpa only [hEC, Matrix.rank_one] using hle

omit [Fintype P] in
/-- Choose genuine nonzero coordinates on a specified collection of rays. -/
theorem exists_ray_coordinate_pins [Nonempty D] {A : Type*} [Fintype A]
    (e : A ↪ P) (q : P → D → K)
    (hne : ∀ j, j ∉ Set.range e → q j ≠ 0) :
    ∃ p : P → D, ∀ j, j ∉ Set.range e → q j (p j) ≠ 0 := by
  classical
  have hex : ∀ j, ∃ d : D, j ∉ Set.range e → q j d ≠ 0 := by
    intro j
    by_cases hj : j ∈ Set.range e
    · exact ⟨Classical.choice ‹Nonempty D›, fun h => (h hj).elim⟩
    · have hh : ∃ d, q j d ≠ 0 := by
        by_contra h
        push Not at h
        exact hne j hj (funext h)
      obtain ⟨d, hd⟩ := hh
      exact ⟨d, fun _ => hd⟩
  exact Classical.skolem.mp hex

/-- The complete rank-one/plane normal form in a preselected fixed encoder:
the Boolean core is nonzero, every retained mode has rank two, and every
stripped ray transforms to a pure MGI vector. -/
theorem fullRank_flag_normal_form_complete [Nonempty D] {m n t : ℕ}
    (M : Matrix D (BooleanInput t) K)
    (hM : Function.Injective M.transpose.mulVecLin)
    (E : Matrix (BooleanInput 1) D K)
    (C : Matrix (BooleanInput t) (BooleanInput 1) K)
    (hC : OrderedMatchgateMatrix C) (hEC : (E*M)*C = 1)
    (e : Fin m ↪ Fin n) (he : StrictMono e)
    (T : (Fin n → D) → K) (hne : T ≠ 0)
    (hT : BooleanMatchgateIdentities (leftBooleanLift M n T))
    (hplane : ∀ i, columnSupport (portFlatten T (e i)) =
      Submodule.span K (Set.range E.row))
    (q : Fin n → D → K)
    (hq : ∀ j, j ∉ Set.range e →
      columnSupport (portFlatten T j) ≤ Submodule.span K {q j})
    (hqne : ∀ j, j ∉ Set.range e → q j ≠ 0) :
    ∃ h : BooleanTable m K, BooleanMatchgateIdentities h ∧ h ≠ 0 ∧
      T = flagTensor E e q h ∧
      (∀ i, Module.finrank K (columnSupport (portFlatten h i)) = 2) ∧
      (m = 0 ∨ 2 ≤ m) ∧
      (∀ j, j ∉ Set.range e → BooleanMatchgateIdentities (unaryTransform M (q j))) := by
  obtain ⟨h, hmg, hfac⟩ := fullRank_flag_normal_form M hM E C hC hEC e he T hT
    (fun i => (hplane i).le) q hq hqne
  have hE := primitive_encoder_injective M E C hEC
  have hdim : Module.finrank K (Submodule.span K (Set.range E.row)) = 2 := by
    rw [← Matrix.rank_eq_finrank_span_row]
    simpa using rank_eq_card_of_transpose_injective E hE
  obtain ⟨p, hp⟩ := exists_ray_coordinate_pins e q hqne
  have hcore : ∀ i, Module.finrank K (columnSupport (portFlatten h i)) = 2 := by
    intro i
    apply flagTensor_core_mode_rank_two E hE e q h p
    · simpa only [← hfac] using hq
    · exact hp
    · rw [← hfac, hplane i, hdim]
  refine ⟨h, hmg, flagTensor_core_ne_zero E e q h (by simpa only [← hfac] using hne),
    hfac, hcore, boolean_core_arity_zero_or_ge_two h hcore, ?_⟩
  intro j hj
  exact transformed_ray_is_pure M hM T hne hT j (q j) (hq j hj)

/-- The plane-supported ports, as an actual finite subset of the original
ordered ports. -/
def planeSupportedPorts {n : ℕ} (S : Submodule K (D → K))
    (T : (Fin n → D) → K) : Finset (Fin n) :=
  Finset.univ.filter (fun j => columnSupport (portFlatten T j) = S)

/-- Enumerate the selected plane ports in increasing original order. -/
def planePortEmbedding {n : ℕ} (S : Submodule K (D → K)) (T : (Fin n → D) → K) :
    Fin (planeSupportedPorts S T).card ↪o Fin n :=
  (planeSupportedPorts S T).orderEmbOfFin rfl

/-- **Rank-one/plane form with no assumed factorization or supplied ray
vectors.** The line generators are obtained from the actual flattenings and
the surviving Boolean order is the canonical increasing subsequence. -/
theorem flag_normal_form_plane_or_line [Nonempty D] {n t : ℕ}
    (M : Matrix D (BooleanInput t) K)
    (hM : Function.Injective M.transpose.mulVecLin)
    (E : Matrix (BooleanInput 1) D K)
    (C : Matrix (BooleanInput t) (BooleanInput 1) K)
    (hC : OrderedMatchgateMatrix C) (hEC : (E*M)*C = 1)
    (T : (Fin n → D) → K) (hne : T ≠ 0)
    (hT : BooleanMatchgateIdentities (leftBooleanLift M n T))
    (hline : ∀ j, columnSupport (portFlatten T j) ≠ Submodule.span K (Set.range E.row) →
      Module.finrank K (columnSupport (portFlatten T j)) = 1) :
    let S := Submodule.span K (Set.range E.row)
    let I := planeSupportedPorts S T
    let e := (planePortEmbedding S T).toEmbedding
    ∃ (q : Fin n → D → K) (h : BooleanTable I.card K),
      (∀ j, j ∉ Set.range e → q j ≠ 0 ∧ columnSupport (portFlatten T j) = Submodule.span K {q j}) ∧
      BooleanMatchgateIdentities h ∧ h ≠ 0 ∧ T = flagTensor E e q h ∧
      (∀ i, Module.finrank K (columnSupport (portFlatten h i)) = 2) ∧
      (I.card = 0 ∨ 2 ≤ I.card) ∧
      (∀ j, j ∉ Set.range e → BooleanMatchgateIdentities (unaryTransform M (q j))) := by
  classical
  let S := Submodule.span K (Set.range E.row)
  let I := planeSupportedPorts S T
  let e := (planePortEmbedding S T).toEmbedding
  have hrange : Set.range e = (I : Set (Fin n)) := Finset.range_orderEmbOfFin I rfl
  have hsel (i : Fin I.card) : columnSupport (portFlatten T (e i)) = S := by
    have hi : e i ∈ I := (planeSupportedPorts S T).orderEmbOfFin_mem rfl i
    exact (Finset.mem_filter.mp hi).2
  have hgen : ∀ j, ∃ u : D → K, j ∉ Set.range e →
      u ≠ 0 ∧ columnSupport (portFlatten T j) = Submodule.span K {u} := by
    intro j
    by_cases hj : j ∈ Set.range e
    · exact ⟨0, fun h => (h hj).elim⟩
    · have hneq : columnSupport (portFlatten T j) ≠ S := by
        intro hh
        apply hj
        rw [hrange]
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hh⟩
      obtain ⟨u, hu, hspan⟩ := exists_generator_of_finrank_one _ (hline j hneq)
      exact ⟨u, fun _ => ⟨hu, hspan⟩⟩
  choose q hq using hgen
  obtain ⟨h, hmg, hnon, hfac, hranks, harity, hpure⟩ := fullRank_flag_normal_form_complete
    M hM E C hC hEC e (planePortEmbedding S T).strictMono T hne hT hsel q
    (fun j hj => (hq j hj).2.le) (fun j hj => (hq j hj).1)
  exact ⟨q, h, hq, hmg, hnon, hfac, hranks, harity, hpure⟩

/-- Each mode of a literal pure tensor lies in the span of its displayed
factor. The proof uses the actual flattening columns. -/
theorem product_tensor_port_support (c : K) (q : P → D → K) (j : P) :
    columnSupport (portFlatten (fun x => c * ∏ i, q i (x i)) j) ≤ Submodule.span K {q j} := by
  classical
  rw [columnSupport, Matrix.range_mulVecLin, Submodule.span_le]
  rintro _ ⟨a, rfl⟩
  apply Submodule.mem_span_singleton.mpr
  refine ⟨c * ∏ i : {i : P // i ≠ j}, q i (a i), ?_⟩
  funext d
  change (c * ∏ i : {i : P // i ≠ j}, q i (a i)) * q j d =
    c * ∏ i, q i (insertBoundaryCoordinate j d a i)
  rw [prod_eq_selected_mul_complement j]
  simp only [insertBoundaryCoordinate_same]
  have heq : (∏ i : {i : P // i ≠ j}, q i (insertBoundaryCoordinate j d a i)) =
      ∏ i : {i : P // i ≠ j}, q i (a i) := by
    apply Finset.prod_congr rfl
    intro i _
    rw [insertBoundaryCoordinate_ne _ _ _ _ i.property]
  rw [heq]
  ring

/-- The source's all-rays alternative: a nonzero tensor whose actual modes
are lines is a scalar times pure-ray factors, and each transformed factor is
itself a pure MGI vector. -/
theorem all_line_supports_pure_decomposition {n t : ℕ}
    (M : Matrix D (BooleanInput t) K)
    (hM : Function.Injective M.transpose.mulVecLin)
    (T : (Fin n → D) → K) (hne : T ≠ 0)
    (hT : BooleanMatchgateIdentities (leftBooleanLift M n T))
    (hline : ∀ j, Module.finrank K (columnSupport (portFlatten T j)) = 1) :
    ∃ (c : K) (q : Fin n → D → K), c ≠ 0 ∧ (∀ j, q j ≠ 0) ∧
      (∀ x, T x = c * ∏ j, q j (x j)) ∧
      (∀ j, BooleanMatchgateIdentities (unaryTransform M (q j))) := by
  obtain ⟨c, q, hc, hq, hfac⟩ := rankOne_strip_all_ports T hne hline
  refine ⟨c, q, hc, hq, hfac, ?_⟩
  intro j
  apply transformed_ray_is_pure M hM T hne hT j (q j)
  rw [show T = (fun x => c * ∏ i, q i (x i)) from funext hfac]
  exact product_tensor_port_support c q j

/-- In one preselected endpoint/ray basis, choose the vector named by a
one-dimensional support. The plane case is never used for stripped ports. -/
def fixedFlagRay (E : Matrix (BooleanInput 1) D K) (r : D → K)
    (S : Submodule K (D → K)) : D → K :=
  if S = Submodule.span K {E.row (fun _ => 0)} then E.row (fun _ => 0)
  else if S = Submodule.span K {E.row (fun _ => 1)} then E.row (fun _ => 1) else r

/-- The literal source flag case, using just one fixed pair of plane endpoint
vectors and one fixed outside-ray vector for all factors. -/
theorem fixed_adapted_flag_normal_form [Nonempty D] {n t : ℕ}
    (M : Matrix D (BooleanInput t) K)
    (hM : Function.Injective M.transpose.mulVecLin)
    (E : Matrix (BooleanInput 1) D K)
    (hEM : OrderedMatchgateMatrix (E*M))
    (C : Matrix (BooleanInput t) (BooleanInput 1) K)
    (hC : OrderedMatchgateMatrix C) (hEC : (E*M)*C = 1)
    (r : D → K) (hr : r ≠ 0)
    (T : (Fin n → D) → K) (hne : T ≠ 0)
    (hT : BooleanMatchgateIdentities (leftBooleanLift M n T))
    (hflag : ∀ j, columnSupport (portFlatten T j) = Submodule.span K (Set.range E.row) ∨
      columnSupport (portFlatten T j) = Submodule.span K {E.row (fun _ => 0)} ∨
      columnSupport (portFlatten T j) = Submodule.span K {E.row (fun _ => 1)} ∨
      columnSupport (portFlatten T j) = Submodule.span K {r}) :
    let S := Submodule.span K (Set.range E.row)
    let I := planeSupportedPorts S T
    let e := (planePortEmbedding S T).toEmbedding
    let q := fun j => fixedFlagRay E r (columnSupport (portFlatten T j))
    ∃ h : BooleanTable I.card K, BooleanMatchgateIdentities h ∧ h ≠ 0 ∧
      T = flagTensor E e q h ∧
      (∀ i, Module.finrank K (columnSupport (portFlatten h i)) = 2) ∧
      (I.card = 0 ∨ 2 ≤ I.card) ∧
      (∀ j, j ∉ Set.range e → q j ≠ 0 ∧
        columnSupport (portFlatten T j) = Submodule.span K {q j} ∧
        BooleanMatchgateIdentities (unaryTransform M (q j))) ∧
      BooleanMatchgateIdentities (unaryTransform M (E.row (fun _ => 0))) ∧
      BooleanMatchgateIdentities (unaryTransform M (E.row (fun _ => 1))) := by
  classical
  let S := Submodule.span K (Set.range E.row)
  let I := planeSupportedPorts S T
  let e := (planePortEmbedding S T).toEmbedding
  let q := fun j => fixedFlagRay E r (columnSupport (portFlatten T j))
  have hE := primitive_encoder_injective M E C hEC
  have hrow (a : BooleanInput 1) : E.row a ≠ 0 := by
    intro hz
    have hlin := (Matrix.vecMul_injective_iff.mp (show Function.Injective E.vecMul from by
      intro x y hxy
      apply hE
      simpa only [Matrix.mulVecLin_apply, Matrix.mulVec_transpose] using hxy)).ne_zero a
    exact hlin hz
  have hrange : Set.range e = (I : Set (Fin n)) := Finset.range_orderEmbOfFin I rfl
  have hsel (i : Fin I.card) : columnSupport (portFlatten T (e i)) = S := by
    exact (Finset.mem_filter.mp ((planeSupportedPorts S T).orderEmbOfFin_mem rfl i)).2
  have hq : ∀ j, j ∉ Set.range e → q j ≠ 0 ∧
      columnSupport (portFlatten T j) = Submodule.span K {q j} := by
    intro j hj
    have hn : columnSupport (portFlatten T j) ≠ S := by
      intro hh
      apply hj
      rw [hrange]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hh⟩
    rcases hflag j with hp | h₀ | h₁ | hray
    · exact (hn hp).elim
    · simp only [q, fixedFlagRay, h₀, ite_true]
      exact ⟨hrow _, trivial⟩
    · by_cases hsame : columnSupport (portFlatten T j) = Submodule.span K {E.row (fun _ => 0)}
      · simp only [q, fixedFlagRay, hsame, ite_true]
        exact ⟨hrow _, trivial⟩
      · simp only [q, fixedFlagRay, ite_eq_right hsame, h₁, ite_true]
        exact ⟨hrow _, trivial⟩
    · by_cases h₀ : columnSupport (portFlatten T j) = Submodule.span K {E.row (fun _ => 0)}
      · simp only [q, fixedFlagRay, h₀, ite_true]
        exact ⟨hrow _, trivial⟩
      · by_cases h₁ : columnSupport (portFlatten T j) = Submodule.span K {E.row (fun _ => 1)}
        · simp only [q, fixedFlagRay, ite_eq_right h₀, h₁, ite_true]
          exact ⟨hrow _, trivial⟩
        · simp only [q, fixedFlagRay, ite_eq_right h₀, ite_eq_right h₁]
          exact ⟨hr, hray⟩
  obtain ⟨h, hmg, hnon, hfac, hranks, harity, hpure⟩ := fullRank_flag_normal_form_complete
    M hM E C hC hEC e (planePortEmbedding S T).strictMono T hne hT hsel q
    (fun j hj => (hq j hj).2.le) (fun j hj => (hq j hj).1)
  refine ⟨h, hmg, hnon, hfac, hranks, harity, ?_, ?_, ?_⟩
  · intro j hj
    exact ⟨(hq j hj).1, (hq j hj).2, hpure j hj⟩
  · exact hEM.row (fun _ => 0)
  · exact hEM.row (fun _ => 1)

/-- Choose all fixed primitive-plane data before any left tensor: the two
endpoint vectors, their ordered encoder and decoder, and their parity labels. -/
theorem exists_uniform_flag_basis [CharZero K] {r t : ℕ}
    (M : Matrix D (BooleanInput t) K)
    (hM : Function.Injective M.transpose.mulVecLin)
    (P₀ : Submodule K (D → K))
    (B : Matrix (BooleanInput r) (BooleanInput t) K)
    (hB : OrderedMatchgateMatrix B) (hrB : B.rank = 2)
    (hspace : orderedRowSpace B = P₀.map M.transpose.mulVecLin) :
    ∃ (E : Matrix (BooleanInput 1) D K)
      (C : Matrix (BooleanInput t) (BooleanInput 1) K) (b : ℕ),
      Submodule.span K (Set.range E.row) = P₀ ∧
      OrderedMatchgateMatrix (E*M) ∧ OrderedMatchgateMatrix C ∧ (E*M)*C = 1 ∧
      (E*M).rank = 2 ∧ b < 2 ∧
      (E*M).row (fun _ => 0) ≠ 0 ∧ (E*M).row (fun _ => 1) ≠ 0 ∧
      (∀ y, booleanParity y ≠ b → (E*M) (fun _ => 0) y = 0) ∧
      (∀ y, booleanParity y = b → (E*M) (fun _ => 1) y = 0) := by
  obtain ⟨Q, C, b, hQ, hC, hQC, hrQ, hQP, hb, h₀, h₁, hp₀, hp₁, _⟩ :=
    exists_uniform_boolean_plane_embedding hB hrB
  obtain ⟨E, hEM, hEP⟩ := exists_primitive_plane_encoder M hM P₀ Q (hQP.trans hspace)
  refine ⟨E, C, b, hEP, ?_⟩
  simpa only [hEM] using ⟨hQ, hC, hQC, hrQ, hb, h₀, h₁, hp₀, hp₁⟩

/-- The source's precisely labelled fixed endpoints: row zero is even and
row one is odd. These primitive vectors and the decoder depend only on the
common base and the plane, and may be used in `fixed_adapted_flag_normal_form`
for every arity and every tensor. -/
theorem exists_uniform_even_odd_flag_basis [CharZero K] {r t : ℕ}
    (M : Matrix D (BooleanInput t) K)
    (hM : Function.Injective M.transpose.mulVecLin)
    (P₀ : Submodule K (D → K))
    (B : Matrix (BooleanInput r) (BooleanInput t) K)
    (hB : OrderedMatchgateMatrix B) (hrB : B.rank = 2)
    (hspace : orderedRowSpace B = P₀.map M.transpose.mulVecLin) :
    ∃ (E : Matrix (BooleanInput 1) D K)
      (C : Matrix (BooleanInput t) (BooleanInput 1) K),
      Submodule.span K (Set.range E.row) = P₀ ∧
      OrderedMatchgateMatrix (E*M) ∧ OrderedMatchgateMatrix C ∧ (E*M)*C = 1 ∧
      (E*M).rank = 2 ∧
      (E*M).row (fun _ => 0) ≠ 0 ∧ (E*M).row (fun _ => 1) ≠ 0 ∧
      (∀ y, booleanParity y ≠ 0 → (E*M) (fun _ => 0) y = 0) ∧
      (∀ y, booleanParity y = 0 → (E*M) (fun _ => 1) y = 0) := by
  obtain ⟨Q, C, hQ, hC, hQC, hrQ, hQP, h₀, h₁, hp₀, hp₁⟩ :=
    exists_even_odd_boolean_plane_encoder hB hrB
  obtain ⟨E, hEM, hEP⟩ := exists_primitive_plane_encoder M hM P₀ Q (hQP.trans hspace)
  refine ⟨E, C, hEP, ?_⟩
  simpa only [hEM] using ⟨hQ, hC, hQC, hrQ, h₀, h₁, hp₀, hp₁⟩

end
end MatchgateWidth
