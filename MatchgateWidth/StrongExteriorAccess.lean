import MatchgateWidth.ExteriorAccessCharacterization

/-! # Simple global exterior-star convention for ordered matchgates

The marked external order is certified by mutually disjoint simple access arcs
avoiding all graph vertices/edges except their own starts. This makes explicit
the global exterior-star convention used for disconnected matchgates in
Cai–Gorenstein, Matchgates Revisited, p.178. The signature characterization is
proved; no unchanged-graph normalization from a separate facial-walk model is
claimed.
-/
namespace MatchgateWidth
noncomputable section

/-- The strong standard exterior-star certificate, including isolated-vertex
avoidance and simplicity of each access arc. -/
structure StrongOrderedExteriorAccess {V E : Type*} {G : WeightedGraph V E ℂ}
    (P : PlaneDrawing G) {s : ℕ} (ext : Fin s → V)
    extends OrderedExteriorAccess P ext where
  access_injective : ∀ i, Function.Injective (access i)
  access_meets_vertex_only_at_start : ∀ i t v, access i t = P.vertex v →
    t = 0 ∧ v = ext i

namespace PlanarDrawing
variable {V E : Type*} {G : WeightedGraph V E ℂ} {s : ℕ} {ext : Fin s → V}

/-- A disk drawing has simple radial exterior access on its unchanged graph,
including avoidance of isolated vertices. -/
def strongOrderedExteriorAccess (D : PlanarDrawing G ext) :
    StrongOrderedExteriorAccess D.toPlaneDrawing ext where
  toOrderedExteriorAccess := D.orderedExteriorAccess
  access_injective := by
    intro i t u h
    have hn := congrArg norm h
    change ‖D.radialAccess i t‖ = ‖D.radialAccess i u‖ at hn
    rw [D.norm_radialAccess, D.norm_radialAccess] at hn
    exact Subtype.ext (by linarith)
  access_meets_vertex_only_at_start := by
    intro i t v h
    have hn := congrArg norm h
    change ‖D.radialAccess i t‖ = ‖D.vertex v‖ at hn
    rw [D.norm_radialAccess] at hn
    have ht : t = 0 := Subtype.ext (by
      change (t : ℝ) = 0
      linarith [D.vertex_in_disk v, t.property.1])
    refine ⟨ht, ?_⟩
    subst t
    have he : D.vertex (ext i) = D.vertex v := by
      change D.radialAccess i 0 = D.vertex v at h
      simpa only [Path.source] using h
    exact (D.vertex_injective he).symm
end PlanarDrawing

/-- Finite weighted plane matching signatures with the explicit simple global
exterior-star order certificate. Exact values, labels and first port are retained. -/
def StrongAccessRealizable {s : ℕ} (f : (Fin s → Bool) → ℂ) : Prop :=
  ∃ (n m : ℕ) (G : WeightedGraph (Fin n) (Fin m) ℂ) (ext : Fin s → Fin n)
    (P : PlaneDrawing G), Nonempty (StrongOrderedExteriorAccess P ext) ∧
      ∀ x, f x = deletionSignature G ext x

theorem StrongAccessRealizable.exteriorAccessRealizable {s : ℕ}
    {f : (Fin s → Bool) → ℂ} (hf : StrongAccessRealizable f) : ExteriorAccessRealizable f := by
  obtain ⟨n,m,G,ext,P,⟨A⟩,h⟩ := hf
  exact ⟨n,m,G,ext,P,⟨A.toOrderedExteriorAccess⟩,h⟩

theorem StrongAccessRealizable.diskRealizable {s : ℕ}
    {f : (Fin s → Bool) → ℂ} (hf : StrongAccessRealizable f) : DiskRealizable f :=
  hf.exteriorAccessRealizable.diskRealizable

theorem DiskRealizable.strongAccessRealizable {s : ℕ}
    {f : (Fin s → Bool) → ℂ} (hf : DiskRealizable f) : StrongAccessRealizable f := by
  obtain ⟨n,m,G,ext,⟨D⟩,h⟩ := hf
  exact ⟨n,m,G,ext,D.toPlaneDrawing,⟨D.strongOrderedExteriorAccess⟩,h⟩

/-- Equality of exact signature classes, not an unchanged-graph normalization
of every plane drawing. The disk-to-access direction keeps graph and weights. -/
theorem strongAccessRealizable_iff_diskRealizable {s : ℕ} (f : (Fin s → Bool) → ℂ) :
    StrongAccessRealizable f ↔ DiskRealizable f :=
  ⟨StrongAccessRealizable.diskRealizable, DiskRealizable.strongAccessRealizable⟩

/-- The weaker proof interface admits exactly the same signatures because its
MGI consequences have independently constructed strong realizations. -/
theorem strongAccessRealizable_iff_exteriorAccessRealizable {s : ℕ}
    (f : (Fin s → Bool) → ℂ) :
    StrongAccessRealizable f ↔ ExteriorAccessRealizable f := by
  rw [strongAccessRealizable_iff_diskRealizable, exteriorAccessRealizable_iff_diskRealizable]

/-- The source geometric matchgate class in `Fin 2` coordinates, under the
explicit global exterior-star convention. -/
def ExactMatchgate {s : ℕ} (f : BooleanTable s ℂ) : Prop :=
  StrongAccessRealizable (fun y => f ((booleanWordEquiv s).symm y))

theorem exactMatchgate_iff_booleanDiskRealizable {s : ℕ} (f : BooleanTable s ℂ) :
    ExactMatchgate f ↔ BooleanDiskRealizable f := strongAccessRealizable_iff_diskRealizable _

theorem exactMatchgate_iff_matchgateIdentities {s : ℕ} (f : BooleanTable s ℂ) :
    ExactMatchgate f ↔ BooleanMatchgateIdentities f := by
  rw [exactMatchgate_iff_booleanDiskRealizable, booleanDiskRealizable_iff_matchgateIdentities]

theorem ExactMatchgate.matchgateIdentities {s : ℕ} {f : BooleanTable s ℂ}
    (hf : ExactMatchgate f) : BooleanMatchgateIdentities f :=
  (exactMatchgate_iff_matchgateIdentities f).mp hf

theorem BooleanMatchgateIdentities.exactMatchgate {s : ℕ} {f : BooleanTable s ℂ}
    (hf : BooleanMatchgateIdentities f) : ExactMatchgate f :=
  (exactMatchgate_iff_matchgateIdentities f).mpr hf

end
end MatchgateWidth
