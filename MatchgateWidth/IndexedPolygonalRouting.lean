import MatchgateWidth.PolygonalPathRealization
import Mathlib.Data.List.OfFn

namespace MatchgateWidth
noncomputable section
open Set

private theorem getElem_splice_left {l p r : List ℂ} {a b : ℂ}
    (heq : l = p ++ a :: b :: r) :
    l[p.length]'(by rw [heq]; simp) = a := by
  subst l
  simp

private theorem getElem_splice_right {l p r : List ℂ} {a b : ℂ}
    (heq : l = p ++ a :: b :: r) :
    l[p.length+1]'(by rw [heq]; simp) = b := by
  subst l
  simp

/-- Index-based conditions sufficient for a simple polygonal vertex list. -/
theorem SimplePolygonalList.of_getElem {l : List ℂ}
    (hnonzero : ∀ (i : ℕ) (hi : i+1 < l.length),
      l[i]'(by omega) ≠ l[i+1])
    (hadj : ∀ (i : ℕ) (hi : i+2 < l.length),
      segment ℝ l[i] l[i+1] ∩ segment ℝ l[i+1] l[i+2] ⊆ {l[i+1]})
    (hdis : ∀ (i j : ℕ) (hi : i+1 < l.length) (hj : j+1 < l.length),
      i+1 < j → Disjoint (segment ℝ l[i] l[i+1]) (segment ℝ l[j] l[j+1])) :
    SimplePolygonalList l := by
  refine ⟨List.isChain_iff_getElem.mpr hnonzero,?_,?_⟩
  · intro p r a b c heq
    have hi : p.length+2 < l.length := by rw [heq]; simp
    have hh := hadj p.length hi
    simpa [heq, Nat.add_assoc] using hh
  · intro p q r a b c d heq
    have hi : p.length+1 < l.length := by rw [heq]; simp
    have hj : p.length+q.length+3 < l.length := by rw [heq]; simp; omega
    have hh := hdis p.length (p.length+q.length+2) hi (by omega) (by omega)
    simpa [heq, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh

/-- The finite-indexed version of the simple polygonal list certificate. -/
theorem SimplePolygonalList.ofFn {n : ℕ} (v : Fin (n+1) → ℂ)
    (hnonzero : ∀ i : Fin n, v i.castSucc ≠ v i.succ)
    (hadj : ∀ i j : Fin n, i.val+1=j.val →
      segment ℝ (v i.castSucc) (v i.succ) ∩ segment ℝ (v j.castSucc) (v j.succ) ⊆
        {v i.succ})
    (hdis : ∀ i j : Fin n, i.val+1<j.val →
      Disjoint (segment ℝ (v i.castSucc) (v i.succ))
        (segment ℝ (v j.castSucc) (v j.succ))) : SimplePolygonalList (List.ofFn v) := by
  apply SimplePolygonalList.of_getElem
  · intro i hi
    have hin : i<n := by simpa using hi
    simpa only [List.getElem_ofFn,Fin.castSucc_mk,Fin.succ_mk] using hnonzero ⟨i,hin⟩
  · intro i hi
    have hin : i+1<n := by simp only [List.length_ofFn] at hi; omega
    simpa only [List.getElem_ofFn,Fin.castSucc,Fin.castAdd,Fin.castLE,Fin.succ,Nat.add_assoc,Nat.reduceAdd] using hadj ⟨i,by omega⟩ ⟨i+1,hin⟩ rfl
  · intro i j hi hj hij
    have hin : i<n := by simpa using hi
    have hjn : j<n := by simpa using hj
    simpa only [List.getElem_ofFn,Fin.castSucc_mk,Fin.succ_mk] using hdis ⟨i,hin⟩ ⟨j,hjn⟩ hij

private theorem trace_cons_ofFn {n : ℕ} (v : Fin (n+1) → ℂ) (a : ℂ) :
    polygonalTrace (a :: List.ofFn v) =
      segment ℝ a (v 0) ∪ polygonalTrace (List.ofFn v) := by
  rw [List.ofFn_succ]
  rfl

/-- The trace of an indexed polygonal chain is precisely the union of its
closed edges. -/
theorem polygonalTrace_ofFn {n : ℕ} (hn : 0<n) (v : Fin (n+1) → ℂ) :
    polygonalTrace (List.ofFn v) =
      ⋃ i : Fin n, segment ℝ (v i.castSucc) (v i.succ) := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  induction n with
  | zero =>
    simp only [List.ofFn_succ,List.ofFn_zero,polygonalTrace]
    have hu : (⋃ i : Fin 1, segment ℝ (v i.castSucc) (v i.succ)) =
        segment ℝ (v 0) (v 1) := by ext z; simp
    rw [hu]
    exact Set.union_eq_left.mpr (by simpa using right_mem_segment ℝ (v 0) (v 1))
  | succ n ih =>
    rw [List.ofFn_succ,trace_cons_ofFn,ih (by omega)]
    ext z
    simp only [Set.mem_union,Set.mem_iUnion,Fin.exists_fin_succ,
      Fin.castSucc_zero,Fin.succ_zero_eq_one,Fin.castSucc_succ]

/-- Indexed realization of a finite simple polygonal chain, with exact edge
union as its image. This form can be reused for the lanes of a ribbon. -/
theorem exists_injective_polygonal_path_of_indexed {n : ℕ} (hn : 0<n)
    (v : Fin (n+1) → ℂ)
    (hnonzero : ∀ i : Fin n, v i.castSucc ≠ v i.succ)
    (hadj : ∀ i j : Fin n, i.val+1=j.val →
      segment ℝ (v i.castSucc) (v i.succ) ∩ segment ℝ (v j.castSucc) (v j.succ) ⊆
        {v i.succ})
    (hdis : ∀ i j : Fin n, i.val+1<j.val →
      Disjoint (segment ℝ (v i.castSucc) (v i.succ))
        (segment ℝ (v j.castSucc) (v j.succ))) :
    ∃ p : Path (v 0) (v (Fin.last n)), Function.Injective p ∧ IsPolygonalPath p ∧
      Set.range p = ⋃ i : Fin n, segment ℝ (v i.castSucc) (v i.succ) := by
  have hs := SimplePolygonalList.ofFn v hnonzero hadj hdis
  have hlast : (List.ofFn v).getLast? = some (v (Fin.last n)) := by
    rw [List.getLast?_eq_some_getLast (by simp)]
    exact congrArg some (List.getLast_ofFn_succ v)
  have hlen : 2 ≤ (List.ofFn v).length := by simp; omega
  obtain ⟨a,b,l,heq⟩ : ∃ (a b : ℂ) (l : List ℂ), List.ofFn v = a::b::l := by
    cases hh : List.ofFn v with
    | nil => rw [hh] at hlen; simp at hlen
    | cons a l =>
      cases l with
      | nil => rw [hh] at hlen; simp at hlen
      | cons b l => exact ⟨a,b,l,rfl⟩
  have hhead := congrArg List.head? heq
  rw [List.ofFn_succ] at hhead
  simp only [List.head?_cons,Option.some.injEq] at hhead
  subst a
  rw [heq] at hs hlast
  obtain ⟨p,hp,hpoly,hrange⟩ := hs.exists_injective_path hlast
  refine ⟨p,hp,hpoly,?_⟩
  rw [← heq,polygonalTrace_ofFn hn] at hrange
  exact hrange

private theorem list_eq_take_two {l : List ℂ} {i : ℕ} (hi : i+1<l.length) :
    l = l.take i ++ l[i] :: l[i+1] :: l.drop (i+2) := by
  conv_lhs => rw [← List.take_append_drop i l]
  rw [List.drop_eq_getElem_cons (by omega), List.drop_eq_getElem_cons hi]

/-- Adjacent-edge control expressed using arbitrary valid list indices. -/
theorem SimplePolygonalList.getElem_adjacent {l : List ℂ} (h : SimplePolygonalList l)
    (i : ℕ) (hi : i+2 < l.length) :
    segment ℝ l[i] l[i+1] ∩ segment ℝ l[i+1] l[i+2] ⊆ {l[i+1]} := by
  have heq := list_eq_take_two (l := l) (i := i) (by omega)
  rw [List.drop_eq_getElem_cons hi] at heq
  exact h.adjacent_inter (l.take i) (l.drop (i+2+1)) _ _ _ heq

/-- Separated-edge control expressed using arbitrary valid list indices. -/
theorem SimplePolygonalList.getElem_nonadjacent {l : List ℂ} (h : SimplePolygonalList l)
    (i j : ℕ) (hi : i+1 < l.length) (hj : j+1 < l.length) (hij : i+1<j) :
    Disjoint (segment ℝ l[i] l[i+1]) (segment ℝ l[j] l[j+1]) := by
  have heq := list_eq_take_two hi
  have hdrop : l.drop (i+2) =
      (l.drop (i+2)).take (j-(i+2)) ++ l.drop j := by
    have hh := (List.take_append_drop (j-(i+2)) (l.drop (i+2))).symm
    rw [List.drop_drop] at hh
    have he : i+2+(j-(i+2)) = j := by omega
    simpa only [he] using hh
  rw [hdrop,List.drop_eq_getElem_cons (i := j) (by omega),List.drop_eq_getElem_cons hj] at heq
  exact h.nonadjacent_disjoint (l.take i) ((l.drop (i+2)).take (j-(i+2)))
    (l.drop (j+2)) _ _ _ _ (by simpa [Nat.add_assoc] using heq)

/-- Full index-based characterization of a simple polygonal list. -/
theorem SimplePolygonalList.getElem_conditions {l : List ℂ} (h : SimplePolygonalList l) :
    (∀ (i : ℕ) (hi : i+1 < l.length), l[i]'(by omega) ≠ l[i+1]) ∧
    (∀ (i : ℕ) (hi : i+2 < l.length),
      segment ℝ l[i] l[i+1] ∩ segment ℝ l[i+1] l[i+2] ⊆ {l[i+1]}) ∧
    (∀ (i j : ℕ) (hi : i+1 < l.length) (hj : j+1 < l.length),
      i+1 < j → Disjoint (segment ℝ l[i] l[i+1]) (segment ℝ l[j] l[j+1])) :=
  ⟨List.isChain_iff_getElem.mp h.nonzero_edges,h.getElem_adjacent,h.getElem_nonadjacent⟩

/-- A finite indexed simple polygonal route, with all geometry verified. -/
structure IndexedSimplePolygonalRoute (U : Set ℂ) (x y : ℂ) where
  edgeCount : ℕ
  positive : 0 < edgeCount
  vertex : Fin (edgeCount+1) → ℂ
  source : vertex 0 = x
  target : vertex (Fin.last edgeCount) = y
  segment_subset : ∀ i : Fin edgeCount, segment ℝ (vertex i.castSucc) (vertex i.succ) ⊆ U
  nonzero : ∀ i : Fin edgeCount, vertex i.castSucc ≠ vertex i.succ
  adjacent : ∀ i j : Fin edgeCount, i.val+1=j.val →
    segment ℝ (vertex i.castSucc) (vertex i.succ) ∩
      segment ℝ (vertex j.castSucc) (vertex j.succ) ⊆ {vertex i.succ}
  nonadjacent : ∀ i j : Fin edgeCount, i.val+1<j.val →
    Disjoint (segment ℝ (vertex i.castSucc) (vertex i.succ))
      (segment ℝ (vertex j.castSucc) (vertex j.succ))

/-- Extracting indexed route data from a nontrivial simple vertex list. -/
theorem SimplePolygonalList.exists_indexed_route {U : Set ℂ} {a b y : ℂ} {l : List ℂ}
    (h : SimplePolygonalList (a::b::l))
    (hc : (a::b::l).IsChain (fun x y => segment ℝ x y ⊆ U))
    (hy : (a::b::l).getLast? = some y) :
    Nonempty (IndexedSimplePolygonalRoute U a y) := by
  let n := l.length+1
  let v : Fin (n+1) → ℂ := fun i => (a::b::l)[i.val]'(by simpa [n] using i.isLt)
  have hlast : v (Fin.last n) = y := by
    rw [List.getLast?_eq_some_getLast (by simp),List.getLast_eq_getElem] at hy
    have hh := Option.some.inj hy
    change (a::b::l)[l.length+1] = y
    simpa only [List.length_cons, Nat.add_sub_cancel] using hh
  refine ⟨⟨n,by dsimp [n]; omega,v,rfl,hlast,?_,?_,?_,?_⟩⟩
  · intro i
    exact List.isChain_iff_getElem.mp hc i.val (by simpa [n] using i.isLt)
  · intro i
    exact List.isChain_iff_getElem.mp h.nonzero_edges i.val (by simpa [n] using i.isLt)
  · intro i j hij
    have hi : i.val+2 < (a::b::l).length := by
      have hj := j.isLt
      dsimp [n] at hj
      simp only [List.length_cons]
      omega
    have hh := h.getElem_adjacent i.val hi
    change segment ℝ (a::b::l)[i.val] (a::b::l)[i.val+1] ∩
      segment ℝ (a::b::l)[j.val] (a::b::l)[j.val+1] ⊆ {(a::b::l)[i.val+1]}
    simpa only [← hij,Nat.add_assoc] using hh
  · intro i j hij
    exact h.getElem_nonadjacent i.val j.val (by simpa [n] using i.isLt)
      (by simpa [n] using j.isLt) hij

/-- A polygonal walk with distinct endpoints yields all the indexed geometric
data needed to construct a narrow noncrossing ribbon. -/
theorem PolygonallyJoinedIn.exists_indexed_simple_route {U : Set ℂ} {x y : ℂ}
    (h : PolygonallyJoinedIn U x y) (hne : x ≠ y) :
    Nonempty (IndexedSimplePolygonalRoute U x y) := by
  obtain ⟨l,hx,hy,hc,hs⟩ := h.exists_simple_list
  cases l with
  | nil => simp at hx
  | cons a l =>
    have hax : a=x := by simpa using hx
    subst a
    cases l with
    | nil => exact (hne (by simpa using hy)).elim
    | cons b l => exact hs.exists_indexed_route hc hy

/-- Continuous routes in open carriers yield a nondegenerate indexed simple
polygonal route with their original endpoints. -/
theorem Path.exists_indexed_simple_route {U : Set ℂ} (hU : IsOpen U) {x y : ℂ}
    (p : Path x y) (hp : Set.range p ⊆ U) (hne : x ≠ y) :
    Nonempty (IndexedSimplePolygonalRoute U x y) :=
  (Path.polygonallyJoinedIn hU p hp).exists_indexed_simple_route hne

end
end MatchgateWidth
