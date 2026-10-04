import MatchgateWidth.ControlledPfaffian
import MatchgateWidth.TwoCenterCoupling
import MatchgateWidth.TwoCenterDrawing

/-! The actual four-vertex, four-internal-edge network of Proposition 8.3. -/
set_option maxHeartbeats 600000
namespace MatchgateWidth
noncomputable section
open scoped Classical
variable {K : Type*} [Field K] {k : ℕ}

/-- The two centers precede the upper and lower disequality vertices. -/
abbrev TwoCenterVertex := Fin 2 ⊕ Fin 2
abbrev TwoCenterBoundary (k : ℕ) := Fin 2 × Fin k

abbrev twoCenterPort (k : ℕ) : TwoCenterVertex → Type
  | Sum.inl _ => ControlledQutritPort k
  | Sum.inr _ => Fin 2

instance (v : TwoCenterVertex) : Fintype (twoCenterPort k v) := by
  cases v <;> dsimp [twoCenterPort] <;> infer_instance

/-- Edge names are `a = L.ℓ₁`, `b = L.ℓ₂`, `c = R.ℓ₁`, `d = R.ℓ₂`.
The upper vertex meets `b,c`; the lower meets `a,d`. The local arguments at
both centers are links first, followed by the ordered hard ports. -/
def twoCenterIncidence : (v : TwoCenterVertex) → twoCenterPort k v →
    Fin 4 ⊕ TwoCenterBoundary k
  | Sum.inl c, Sum.inl l => Sum.inl (if c = 0 then
      (if l = 0 then 0 else 1) else (if l = 0 then 2 else 3))
  | Sum.inl c, Sum.inr i => Sum.inr (c, i)
  | Sum.inr x, l => Sum.inl (if x = 0 then
      (if l = 0 then 1 else 2) else (if l = 0 then 0 else 3))

/-- The actual source `B`, obtained by its common coordinate-base transform. -/
def sourceControlledB (f : BooleanTable k K) (hf : ∀ x, f x ≠ 0) (j : Fin k) :=
  rightTransform (controlledCoordinateBase k)
    (controlledPhysicalSignature (booleanSubsetTable f) (fun _ => hf _) j)

@[simp] theorem sourceControlledB_eq (f : BooleanTable k K)
    (hf : ∀ x, f x ≠ 0) (j : Fin k) :
    sourceControlledB f hf j = controlledQutrit f j :=
  controlledPhysicalSignature_boolean_rightTransform f hf j

def twoCenterTensor (f : BooleanTable k K) (hf : ∀ x, f x ≠ 0) (j : Fin k) :
    (v : TwoCenterVertex) → (twoCenterPort k v → Fin 3) → K
  | Sum.inl _ => sourceControlledB f hf j
  | Sum.inr _ => qutritNeqTensor

/-- Each center carries the exact common-base source B. -/
theorem twoCenterTensor_sourceB (f : BooleanTable k K) (hf : ∀ x, f x ≠ 0)
    (j : Fin k) (c : Fin 2) :
    twoCenterTensor f hf j (Sum.inl c) =
      rightTransform (controlledCoordinateBase k)
        (controlledPhysicalSignature (booleanSubsetTable f) (fun _ => hf _) j) := rfl

/-- Each binary source vertex is literally X₀₁ = E₀₁ + E₁₀. -/
theorem twoCenterTensor_sourceX01 (f : BooleanTable k K) (hf : ∀ x, f x ≠ 0)
    (j : Fin k) (x : Fin 2) (a : Fin 2 → Fin 3) :
    twoCenterTensor f hf j (Sum.inr x) a =
      (if a 0 = 0 ∧ a 1 = 1 then 1 else 0) +
      (if a 0 = 1 ∧ a 1 = 0 then 1 else 0) := by
  simp only [twoCenterTensor, qutritNeqTensor]
  generalize a 0 = b
  generalize a 1 = c
  fin_cases b <;> fin_cases c <;> norm_num

/-- Full network value, with all `3^(2k)` boundary coordinates retained. -/
def twoCenterValue (f : BooleanTable k K) (hf : ∀ x, f x ≠ 0) (j : Fin k)
    (z y : Fin k → Fin 3) : K :=
  networkValue twoCenterIncidence (twoCenterTensor f hf j)
    (fun p => if p.1 = 0 then z p.2 else y p.2)

/-- Source relabeling extended by zero to every forbidden hard assignment. -/
def hardTableExtension (f : BooleanTable k K) (z : Fin k → Fin 3) : K :=
  if ∀ i, z i ≠ 1 then f (fun i => hardBooleanLabel (z i)) else 0

def hardWeightExtension (j : Fin k) (z : Fin k → Fin 3) : K :=
  hardControlWeight (hardBooleanLabel (z j))

/-- General hard assignments, including the forbidden state one. -/
def fullControlledAssignment (a b : Fin 3) (z : Fin k → Fin 3) :
    ControlledQutritPort k → Fin 3 :=
  Sum.elim (fun l => if l = 0 then a else b) z

theorem sourceControlledB_links (f : BooleanTable k K) (hf : ∀ x, f x ≠ 0)
    (j : Fin k) (a b : Fin 3) (z : Fin k → Fin 3) :
    sourceControlledB f hf j (fullControlledAssignment a b z) =
      controlledLinks (hardTableExtension f) (hardWeightExtension j) a b z := by
  rw [sourceControlledB_eq]
  by_cases hz : ∀ i, z i ≠ 1
  · simp [controlledQutrit, fullControlledAssignment, controlledLinks,
      hardTableExtension, hardWeightExtension, hz]
  · simp [controlledQutrit, fullControlledAssignment, controlledLinks,
      hardTableExtension, hz]

private def fourLabelsEquiv : (Fin 4 → Fin 3) ≃ Fin 3 × Fin 3 × Fin 3 × Fin 3 where
  toFun e := (e 0, e 1, e 2, e 3)
  invFun e := ![e.1, e.2.1, e.2.2.1, e.2.2.2]
  left_inv e := by ext i; fin_cases i <;> rfl
  right_inv e := by rcases e with ⟨a,b,c,d⟩; rfl

section
local instance : DecidableEq (Fin 4) := Classical.decEq _

private theorem fourLabels_sum (F : (Fin 4 → Fin 3) → K) :
    (∑ e, F e) = ∑ a, ∑ b, ∑ c, ∑ d, F ![a,b,c,d] := by
  calc (∑ e, F e) = ∑ e : Fin 3 × Fin 3 × Fin 3 × Fin 3,
      F (fourLabelsEquiv.symm e) := (Equiv.sum_comp fourLabelsEquiv.symm F).symm
    _ = _ := by simp [Fintype.sum_prod_type, fourLabelsEquiv]

/-- The generic network semantics is exactly the four-edge contraction, with
neither a permutation nor a reflection of the right tensor's arguments. -/
theorem twoCenterValue_eq_coupledBoundary (f : BooleanTable k K)
    (hf : ∀ x, f x ≠ 0) (j : Fin k) (z y : Fin k → Fin 3) :
    twoCenterValue f hf j z y =
      coupledBoundary (hardTableExtension f) (hardWeightExtension j) z y := by
  unfold twoCenterValue networkValue
  rw [fourLabels_sum]
  unfold coupledBoundary
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro b _
  apply Finset.sum_congr rfl; intro c _
  apply Finset.sum_congr rfl; intro d _
  simp only [Fintype.prod_sum_type, Fin.prod_univ_two]
  simp [twoCenterTensor, twoCenterIncidence,
    sourceControlledB_eq, controlledQutrit, controlledLinks, neq01, qutritNeqTensor,
    hardTableExtension, hardWeightExtension]
  split_ifs <;> simp_all
end

/-- Exact complete boundary table of the source gadget. -/
theorem twoCenterValue_eq (f : BooleanTable k K) (hf : ∀ x, f x ≠ 0)
    (j : Fin k) (z y : Fin k → Fin 3) :
    twoCenterValue f hf j z y = hardTableExtension f z * hardTableExtension f y *
      (hardWeightExtension j z + hardWeightExtension j y) := by
  rw [twoCenterValue_eq_coupledBoundary, coupledBoundary_eq]

@[simp] theorem hardTableExtension_embed (f : BooleanTable k K) (x : BooleanInput k) :
    hardTableExtension f (fun i => hardQutritLabel (x i)) = f x := by
  simp [hardTableExtension]

@[simp] theorem hardWeightExtension_embed (j : Fin k) (x : BooleanInput k) :
    hardWeightExtension (K := K) j (fun i => hardQutritLabel (x i)) =
      hardControlWeight (x j) := by simp [hardWeightExtension]

/-- The displayed source formula on admissible hard states. -/
theorem twoCenterValue_hard (f : BooleanTable k K) (hf : ∀ x, f x ≠ 0)
    (j : Fin k) (x y : BooleanInput k) :
    twoCenterValue f hf j (fun i => hardQutritLabel (x i))
      (fun i => hardQutritLabel (y i)) =
      f x * f y * (hardControlWeight (x j) + hardControlWeight (y j)) := by
  simp [twoCenterValue_eq]

theorem twoCenterValue_forbidden (f : BooleanTable k K) (hf : ∀ x, f x ≠ 0)
    (j : Fin k) (z y : Fin k → Fin 3)
    (h : (∃ i, z i = 1) ∨ (∃ i, y i = 1)) : twoCenterValue f hf j z y = 0 := by
  rw [twoCenterValue_eq]
  rcases h with ⟨i, hi⟩ | ⟨i, hi⟩ <;>
    simp [hardTableExtension, show ¬ ∀ i, _ ≠ (1 : Fin 3) from fun h => h i hi]

/-- Exact Schmidt rank on the full qutrit boundary, without a rank hypothesis on f. -/
theorem twoCenterValue_rank [CharZero K] (f : BooleanTable k K)
    (hf : ∀ x, f x ≠ 0) (j : Fin k) :
    Matrix.rank (twoCenterValue f hf j : Matrix (Fin k → Fin 3) (Fin k → Fin 3) K) = 2 := by
  have he : twoCenterValue f hf j =
      coupledBoundary (hardTableExtension f) (hardWeightExtension j) := by
    funext z y; exact twoCenterValue_eq_coupledBoundary f hf j z y
  rw [he]
  apply coupledBoundary_rank_eq_two _ _ (fun _ => 0) (fun _ => 2)
  · simpa [hardTableExtension, hardBooleanLabel] using hf (fun _ => 0)
  · simpa [hardTableExtension, hardBooleanLabel] using hf (fun _ => 1)
  · norm_num [hardWeightExtension, hardBooleanLabel, hardControlWeight]

/-- A nonzero two-by-two minor rules out a product of one tensor per center. -/
theorem twoCenterValue_not_factor [CharZero K] (f : BooleanTable k K)
    (hf : ∀ x, f x ≠ 0) (j : Fin k) :
    ¬ ∃ U V : (Fin k → Fin 3) → K, ∀ z y, twoCenterValue f hf j z y = U z * V y := by
  rintro ⟨U,V,h⟩
  have hd := coupledBoundary_minor_det (hardTableExtension f) (hardWeightExtension j)
    (fun _ => 0) (fun _ => 2)
  have he : coupledBoundary (hardTableExtension f) (hardWeightExtension j) =
      twoCenterValue f hf j := by
    funext z y; exact (twoCenterValue_eq_coupledBoundary f hf j z y).symm
  rw [he] at hd
  simp only [Matrix.det_fin_two, Matrix.submatrix, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, h] at hd
  have hz : U (fun _ => 0) * V (fun _ => 0) * (U (fun _ => 2) * V (fun _ => 2)) -
      U (fun _ => 0) * V (fun _ => 2) * (U (fun _ => 2) * V (fun _ => 0)) = 0 := by ring
  rw [hz] at hd
  have hn : -(hardTableExtension f (fun _ => 0) * hardTableExtension f (fun _ => 2) *
      (hardWeightExtension j (fun _ => 0) - hardWeightExtension j (fun _ => 2))) ^ 2 ≠ 0 := by
    apply neg_ne_zero.mpr
    apply pow_ne_zero
    apply mul_ne_zero
    · apply mul_ne_zero
      · simpa [hardTableExtension, hardBooleanLabel] using hf (fun _ => 0)
      · simpa [hardTableExtension, hardBooleanLabel] using hf (fun _ => 1)
    · norm_num [hardWeightExtension, hardBooleanLabel, hardControlWeight]
  exact hn hd.symm

/-- The four tensor-network edges are precisely the four drawn link segments. -/
def twoCenterDrawnInternalEdge (e : Fin 4) : TwoCenterDrawingEdge k :=
  ![(0,Sum.inl 0), (0,Sum.inl 1), (1,Sum.inl 0), (1,Sum.inl 1)] e

/-- Boundary wires are the actual outer fan segments, with their center labels. -/
def twoCenterDrawnWire : Fin 4 ⊕ TwoCenterBoundary k → TwoCenterDrawingEdge k :=
  Sum.elim twoCenterDrawnInternalEdge (fun p => (p.1,Sum.inr p.2))

/-- Every local source-center port maps to the correspondingly named drawn
edge, with no reordering at either center. -/
theorem twoCenter_center_incidence (c : Fin 2) (p : ControlledQutritPort k) :
    twoCenterDrawnWire (twoCenterIncidence (Sum.inl c) p) = (c,p) := by
  cases p with
  | inl l => fin_cases c <;> fin_cases l <;>
      simp [twoCenterDrawnWire, twoCenterDrawnInternalEdge, twoCenterIncidence]
  | inr i => simp [twoCenterDrawnWire, twoCenterIncidence]

/-- Bijection from all internal and dangling tensor wires to drawing edges.
Consequently the planar witness draws exactly this network, with no extra edges. -/
def twoCenterDrawnWireEquiv : (Fin 4 ⊕ TwoCenterBoundary k) ≃ TwoCenterDrawingEdge k where
  toFun := twoCenterDrawnWire
  invFun e := twoCenterIncidence (Sum.inl e.1) e.2
  left_inv w := by
    cases w with
    | inl e => fin_cases e <;> simp [twoCenterDrawnWire, twoCenterDrawnInternalEdge,
        twoCenterIncidence]
    | inr p => rcases p with ⟨c,i⟩; simp [twoCenterDrawnWire, twoCenterIncidence]
  right_inv e := twoCenter_center_incidence e.1 e.2

/-- The drawn endpoints at each X₀₁ vertex are precisely its two network ports. -/
theorem twoCenter_neq_incidence (x l : Fin 2) :
    (twoCenterDrawingGraph k).right
      (twoCenterDrawnWire (twoCenterIncidence (Sum.inr x) l)) = Sum.inr (Sum.inl x) := by
  fin_cases x <;> fin_cases l <;>
    simp [twoCenterDrawnWire, twoCenterDrawnInternalEdge, twoCenterIncidence,
      twoCenterDrawingGraph]

/-- The first length-two path is above the centers and the second is below. -/
theorem twoCenter_cross_pairing :
    (twoCenterDrawingGraph k).right (0,Sum.inl 1) = Sum.inr (Sum.inl 0) ∧
    (twoCenterDrawingGraph k).right (1,Sum.inl 0) = Sum.inr (Sum.inl 0) ∧
    (twoCenterDrawingGraph k).right (0,Sum.inl 0) = Sum.inr (Sum.inl 1) ∧
    (twoCenterDrawingGraph k).right (1,Sum.inl 1) = Sum.inr (Sum.inl 1) := by
  norm_num [twoCenterDrawingGraph]

/-- The cyclic port enumeration in the drawing is the source B enumeration. -/
theorem twoCenter_source_port_order : List.ofFn (twoCenterOrderedPort (k := k)) =
    controlledPortOrder k := by
  rw [List.ofFn_add]
  simp [twoCenterOrderedPort, controlledPortOrder, List.ofFn_succ, List.ofFn_eq_map, Fin.addCases]
  exact ⟨rfl, rfl, fun a => by omega⟩

/-- Internal edges have exactly their two named incidences. -/
def twoCenterNetworkEdgeEnds (e : Fin 4) :
    (Sigma (twoCenterPort k)) × (Sigma (twoCenterPort k)) :=
  ![(⟨Sum.inl 0,Sum.inl 0⟩, ⟨Sum.inr 1,0⟩),
    (⟨Sum.inl 0,Sum.inl 1⟩, ⟨Sum.inr 0,0⟩),
    (⟨Sum.inl 1,Sum.inl 0⟩, ⟨Sum.inr 0,1⟩),
    (⟨Sum.inl 1,Sum.inl 1⟩, ⟨Sum.inr 1,1⟩)] e

theorem twoCenter_internal_incidence_iff (v : TwoCenterVertex) (p : twoCenterPort k v)
    (e : Fin 4) : twoCenterIncidence v p = Sum.inl e ↔
      (⟨v,p⟩ : Sigma (twoCenterPort k)) = (twoCenterNetworkEdgeEnds e).1 ∨
      (⟨v,p⟩ : Sigma (twoCenterPort k)) = (twoCenterNetworkEdgeEnds e).2 := by
  cases v with
  | inl c =>
    cases p with
    | inl l => fin_cases c <;> fin_cases l <;> fin_cases e <;>
        simp [twoCenterIncidence, twoCenterNetworkEdgeEnds]
    | inr i => fin_cases c <;> fin_cases e <;>
        simp [twoCenterIncidence, twoCenterNetworkEdgeEnds]
  | inr x => fin_cases x <;> fin_cases p <;> fin_cases e <;>
      simp [twoCenterIncidence, twoCenterNetworkEdgeEnds]

theorem twoCenter_internal_endpoints_distinct (e : Fin 4) :
    (twoCenterNetworkEdgeEnds (k := k) e).1 ≠ (twoCenterNetworkEdgeEnds e).2 := by
  fin_cases e <;> simp [twoCenterNetworkEdgeEnds]

/-- Each hard boundary wire has a unique primitive incidence. -/
theorem twoCenter_boundary_incidence_iff (v : TwoCenterVertex) (p : twoCenterPort k v)
    (c : Fin 2) (i : Fin k) : twoCenterIncidence v p = Sum.inr (c,i) ↔
      (⟨v,p⟩ : Sigma (twoCenterPort k)) = ⟨Sum.inl c,Sum.inr i⟩ := by
  cases v with
  | inl d =>
    cases p with
    | inl l => fin_cases c <;> fin_cases d <;> fin_cases l <;> simp [twoCenterIncidence]
    | inr h => fin_cases c <;> fin_cases d <;> simp [twoCenterIncidence]
  | inr x => fin_cases c <;> fin_cases x <;> fin_cases p <;> simp [twoCenterIncidence]

/-- The planar geometry together with the incidence isomorphism to the exact
source tensor network. This packages the local source order, the two-edge
internal-wire condition and the unique dangling-wire condition. -/
structure TwoCenterNetworkPlanarCertificate (k : ℕ) extends TwoCenterPlanarCertificate k where
  center_incidence : ∀ (c : Fin 2) (p : ControlledQutritPort k),
    twoCenterDrawnWire (twoCenterIncidence (Sum.inl c) p) = (c,p)
  neq_incidence : ∀ x l : Fin 2, (twoCenterDrawingGraph k).right
    (twoCenterDrawnWire (twoCenterIncidence (Sum.inr x) l)) = Sum.inr (Sum.inl x)
  source_port_order : List.ofFn (twoCenterOrderedPort (k := k)) = controlledPortOrder k
  wire_bijective : Function.Bijective (twoCenterDrawnWire (k := k))
  internal_incidence : ∀ (v : TwoCenterVertex) (p : twoCenterPort k v) (e : Fin 4),
    twoCenterIncidence v p = Sum.inl e ↔
      (⟨v,p⟩ : Sigma (twoCenterPort k)) = (twoCenterNetworkEdgeEnds e).1 ∨
      (⟨v,p⟩ : Sigma (twoCenterPort k)) = (twoCenterNetworkEdgeEnds e).2
  boundary_incidence : ∀ (v : TwoCenterVertex) (p : twoCenterPort k v) (c : Fin 2) (i : Fin k),
    twoCenterIncidence v p = Sum.inr (c,i) ↔
      (⟨v,p⟩ : Sigma (twoCenterPort k)) = ⟨Sum.inl c,Sum.inr i⟩
  connected : ∀ v : TwoCenterDrawingVertex k,
    Relation.ReflTransGen twoCenterGraphAdjacent (Sum.inl 0) v

def twoCenterNetworkPlanarCertificate (k : ℕ) : TwoCenterNetworkPlanarCertificate k where
  toTwoCenterPlanarCertificate := twoCenterPlanarCertificate k
  center_incidence := twoCenter_center_incidence
  neq_incidence := twoCenter_neq_incidence
  source_port_order := twoCenter_source_port_order
  wire_bijective := twoCenterDrawnWireEquiv.bijective
  internal_incidence := twoCenter_internal_incidence_iff
  boundary_incidence := twoCenter_boundary_incidence_iff
  connected := twoCenterDrawing_reachable

/-- Proposition 8.3, with the source common-base B tensors, the actual finite
network semantics, a constructed ordered planar embedding, the complete
boundary table, exact Schmidt rank two and nonfactorization. The statement
holds for every nowhere-zero table over a characteristic-zero field; no
one-port/full-rank hypothesis on the table is used. -/
theorem twoCenter_coupling_proposition [CharZero K] (f : BooleanTable k K)
    (hf : ∀ x, f x ≠ 0) (j : Fin k) :
    Nonempty (TwoCenterNetworkPlanarCertificate k) ∧
    (∀ z y, twoCenterValue f hf j z y = hardTableExtension f z * hardTableExtension f y *
      (hardWeightExtension j z + hardWeightExtension j y)) ∧
    Matrix.rank (twoCenterValue f hf j : Matrix (Fin k → Fin 3) (Fin k → Fin 3) K) = 2 ∧
    ¬ ∃ U V : (Fin k → Fin 3) → K, ∀ z y, twoCenterValue f hf j z y = U z * V y :=
  ⟨⟨twoCenterNetworkPlanarCertificate k⟩, twoCenterValue_eq f hf j,
    twoCenterValue_rank f hf j, twoCenterValue_not_factor f hf j⟩

end
end MatchgateWidth
