import MatchgateWidth.TranscendenceBounds
import MatchgateWidth.PfaffianIdentities
import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.KrullDimension.Field

/-!
# Coordinate rings and dimension of polynomially covered loci

Dimension means the actual Krull dimension of the coordinate ring. The bounds
below use Noether normalization and finite polynomial-chart coverage.
-/

namespace MatchgateWidth

open MvPolynomial

noncomputable section

/-- The ideal of polynomials vanishing on a set of points. -/
def vanishingIdeal {K τ : Type*} [CommRing K] (S : Set (τ → K)) :
    Ideal (MvPolynomial τ K) :=
  ⨅ x : S, RingHom.ker (eval x.val)

@[simp] theorem mem_vanishingIdeal {K τ : Type*} [CommRing K]
    (S : Set (τ → K)) (p : MvPolynomial τ K) :
    p ∈ vanishingIdeal S ↔ ∀ x ∈ S, eval x p = 0 := by
  simp [vanishingIdeal]

/-- Vanishing ideals over fields are radical, as required for reduced affine varieties. -/
theorem vanishingIdeal_isRadical {K τ : Type*} [Field K] (S : Set (τ → K)) :
    (vanishingIdeal S).IsRadical := by
  intro p hp
  obtain ⟨n, hn⟩ := hp
  apply (mem_vanishingIdeal S p).mpr
  intro x hx
  have hv := (mem_vanishingIdeal S (p ^ n)).mp hn x hx
  rw [map_pow] at hv
  exact eq_zero_of_pow_eq_zero hv

/-- The reduced coordinate ring of the polynomial Zariski closure of a point set. -/
abbrev CoordinateRing {K τ : Type*} [CommRing K] (S : Set (τ → K)) :=
  MvPolynomial τ K ⧸ vanishingIdeal S

/-- Affine-algebraic dimension, measured by chains of prime ideals. -/
def affineDimension {K τ : Type*} [CommRing K] (S : Set (τ → K)) : WithBot ℕ∞ :=
  ringKrullDim (CoordinateRing S)

/-- Integral maps cannot increase the length of a chain of prime ideals,
by incomparability. No injectivity assumption is needed for this direction. -/
theorem ringKrullDim_le_of_integral {R A : Type*} [CommRing R] [CommRing A]
    (f : R →+* A) (hf : f.IsIntegral) : ringKrullDim A ≤ ringKrullDim R := by
  let := f.toAlgebra
  have : Algebra.IsIntegral R A := (algebraMap_isIntegral_iff).mp hf
  apply Order.krullDim_le_of_strictMono (PrimeSpectrum.comap f)
  intro I J hIJ
  exact Ideal.IsIntegral.under_lt_under hIJ

/-- An injective map from a domain into a finite product of rings has an
injective component. The product of one nonzero kernel element per component
would otherwise be a nonzero element in the joint kernel. -/
theorem exists_injective_component {K ι : Type*} [CommRing K] [IsDomain K]
    [Fintype ι] (B : ι → Type*) [∀ i, CommRing (B i)]
    (f : ∀ i, K →+* B i) (hinj : Function.Injective (fun x i => f i x)) :
    ∃ i, Function.Injective (f i) := by
  classical
  by_contra! hno
  have hk (i : ι) : ∃ x : K, x ≠ 0 ∧ f i x = 0 := by
    have hker : RingHom.ker (f i) ≠ ⊥ := by
      exact mt (RingHom.injective_iff_ker_eq_bot (f i)).mpr (hno i)
    obtain ⟨x, hx, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
    exact ⟨x, hne, hx⟩
  choose x hx hfx using hk
  have hprod : (∏ i, x i) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hx i)
  apply hprod
  apply hinj
  funext i
  change f i (∏ j, x j) = f i 0
  rw [map_zero, map_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (hfx i)

/-- A finitely generated algebra embedded in finitely many polynomial rings
has Krull dimension bounded by the largest parameter count. -/
theorem ringKrullDim_le_of_polynomial_embeddings
    {K A ι : Type} [Field K] [CommRing A] [Algebra K A]
    [Algebra.FiniteType K A] [Fintype ι]
    (σ : ι → Type) [∀ i, Fintype (σ i)] (d : ℕ)
    (hd : ∀ i, Fintype.card (σ i) ≤ d)
    (f : ∀ i, A →ₐ[K] MvPolynomial (σ i) K)
    (hinj : Function.Injective (fun a i => f i a)) :
    ringKrullDim A ≤ d := by
  nontriviality A
  obtain ⟨n, g, hginj, hgint⟩ := exists_integral_inj_algHom_of_fg K A
  have hjoint : Function.Injective (fun a i => (f i).comp g a) := by
    intro x y hxy
    apply hginj
    apply hinj
    exact hxy
  obtain ⟨i, hi⟩ := exists_injective_component
    (fun i => MvPolynomial (σ i) K) (fun i => ((f i).comp g).toRingHom) hjoint
  have hn : n ≤ Fintype.card (σ i) := by
    have ht := trdeg_le_of_injective ((f i).comp g) hi
    simpa only [MvPolynomial.trdeg_of_isDomain, Cardinal.mk_fintype,
      Fintype.card_fin, Cardinal.lift_natCast, Nat.cast_le] using ht
  calc
    ringKrullDim A ≤ ringKrullDim (MvPolynomial (Fin n) K) :=
      ringKrullDim_le_of_integral g.toRingHom hgint
    _ = n := by simp [ringKrullDim_eq_zero_of_field, Nat.card_eq_fintype_card]
    _ ≤ d := by exact_mod_cast hn.trans (hd i)

/-- Taking polynomial closure leaves the vanishing ideal unchanged. -/
theorem vanishingIdeal_polynomialZariskiClosure {K τ : Type*} [CommRing K]
    (S : Set (τ → K)) : vanishingIdeal (polynomialZariskiClosure S) = vanishingIdeal S := by
  ext p
  simp only [mem_vanishingIdeal]
  constructor
  · intro h x hx
    exact h x (fun q hq => hq x hx)
  · intro h x hx
    exact hx p h

/-- Taking polynomial closure leaves the coordinate-ring dimension unchanged. -/
@[simp] theorem affineDimension_polynomialZariskiClosure {K τ : Type*} [CommRing K]
    (S : Set (τ → K)) : affineDimension (polynomialZariskiClosure S) = affineDimension S := by
  unfold affineDimension CoordinateRing
  rw [vanishingIdeal_polynomialZariskiClosure]

/-- Inclusion of point sets induces a surjection of coordinate rings. -/
theorem affineDimension_mono {K τ : Type*} [CommRing K]
    {S T : Set (τ → K)} (hST : S ⊆ T) : affineDimension S ≤ affineDimension T := by
  have hI : vanishingIdeal T ≤ vanishingIdeal S := by
    intro p hp
    exact (mem_vanishingIdeal S p).mpr (fun x hx => (mem_vanishingIdeal T p).mp hp x (hST hx))
  exact ringKrullDim_le_of_surjective
    (Ideal.Quotient.factor hI) (Ideal.Quotient.factor_surjective hI)

/-- Union of polynomial parameter charts over the coefficient field. -/
def polynomialChartUnion {K τ ι : Type*} [CommRing K] {σ : ι → Type*}
    (p : ∀ i, τ → MvPolynomial (σ i) K) : Set (τ → K) :=
  {y | ∃ i x, polynomialMap (RingHom.id K) (p i) x = y}

/-- Vanishing on every point of an infinite-field polynomial chart is
equivalent to vanishing after symbolic substitution. -/
theorem mem_vanishingIdeal_polynomialChartUnion
    {K τ ι : Type*} [Field K] [Infinite K] {σ : ι → Type*}
    (p : ∀ i, τ → MvPolynomial (σ i) K) (q : MvPolynomial τ K) :
    q ∈ vanishingIdeal (polynomialChartUnion p) ↔ ∀ i, aeval (p i) q = 0 := by
  rw [mem_vanishingIdeal]
  constructor
  · intro h i
    apply MvPolynomial.funext
    intro x
    have hx := h (polynomialMap (RingHom.id K) (p i) x) ⟨i, x, rfl⟩
    change eval (fun j => eval x (p i j)) q = 0 at hx
    simpa only [aeval_eq_bind₁, ← aeval_eq_eval, aeval_bind₁, map_zero] using hx
  · intro h y hy
    obtain ⟨i, x, rfl⟩ := hy
    exact eval₂_polynomialMap_eq_zero_of_relation (RingHom.id K) (p i) q (h i) x

/-- The vanishing ideal of a chart union is its actual joint substitution kernel. -/
theorem vanishingIdeal_polynomialChartUnion_eq_iInf_ker
    {K τ ι : Type*} [Field K] [Infinite K] {σ : ι → Type*}
    (p : ∀ i, τ → MvPolynomial (σ i) K) :
    vanishingIdeal (polynomialChartUnion p) =
      ⨅ i, RingHom.ker (aeval (p i)).toRingHom := by
  ext q
  simp only [mem_vanishingIdeal_polynomialChartUnion, Ideal.mem_iInf, RingHom.mem_ker,
    AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]

/-- The actual coordinate ring of finitely many polynomial-chart images
has dimension at most their largest number of parameters. -/
theorem affineDimension_polynomialChartUnion_le
    {K τ ι : Type} [Field K] [Infinite K] [Finite τ] [Fintype ι]
    {σ : ι → Type} [∀ i, Fintype (σ i)]
    (p : ∀ i, τ → MvPolynomial (σ i) K) (d : ℕ)
    (hd : ∀ i, Fintype.card (σ i) ≤ d) :
    affineDimension (polynomialChartUnion p) ≤ d := by
  let I := vanishingIdeal (polynomialChartUnion p)
  have hker : ∀ i q, q ∈ I → aeval (p i) q = 0 := by
    intro i q hq
    exact (mem_vanishingIdeal_polynomialChartUnion p q).mp hq i
  let f : ∀ i, CoordinateRing (polynomialChartUnion p) →ₐ[K] MvPolynomial (σ i) K :=
    fun i => Ideal.Quotient.liftₐ I (aeval (p i)) (hker i)
  apply ringKrullDim_le_of_polynomial_embeddings σ d hd f
  intro a b hab
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
  apply Ideal.Quotient.eq.mpr
  apply (mem_vanishingIdeal_polynomialChartUnion p (a - b)).mpr
  intro i
  rw [map_sub, sub_eq_zero]
  exact congrFun hab i

/-- Finite polynomial coverage bounds the actual affine coordinate dimension. -/
theorem affineDimension_le_of_polynomial_cover
    {K τ ι : Type} [Field K] [Infinite K] [Finite τ] [Fintype ι]
    {σ : ι → Type} [∀ i, Fintype (σ i)]
    (S : Set (τ → K)) (p : ∀ i, τ → MvPolynomial (σ i) K) (d : ℕ)
    (hd : ∀ i, Fintype.card (σ i) ≤ d)
    (hcover : S ⊆ polynomialChartUnion p) : affineDimension S ≤ d :=
  (affineDimension_mono hcover).trans (affineDimension_polynomialChartUnion_le p d hd)

/-- The actual affine locus of arity-`s` matchgate identities. -/
def matchgateIdentityLocus (K : Type*) [CommRing K] (s : ℕ) : Set (BooleanTable s K) :=
  {f | BooleanMatchgateIdentities f}

/-- Lemma 5.3 at the level of the actual reduced coordinate ring, over any
infinite field. In particular it applies over both the rationals and complexes. -/
theorem matchgateIdentityLocus_affineDimension_le
    (K : Type) [Field K] [Infinite K] (s : ℕ) :
    affineDimension (matchgateIdentityLocus K s) ≤ delta s := by
  apply affineDimension_le_of_polynomial_cover
    (matchgateIdentityLocus K s)
    (fun pivot => pfaffianPivotChartPolynomial s K pivot (fun _ => 0))
    (delta s)
  · intro pivot
    simp [delta]
  · intro f hf
    obtain ⟨pivot, a, rfl⟩ := hf.exists_pfaffianPivotChart
    refine ⟨pivot, a, ?_⟩
    funext z
    exact eval₂_pfaffianPivotChartPolynomial (RingHom.id K) pivot (fun _ => 0) a z

/-- The actual sampled-star locus with one central matchgate and two shared samplers. -/
def starTableLocus (K : Type*) [CommRing K] (k r : ℕ) : Set (BooleanTable k K) :=
  {f | ∃ (Q : BooleanTable (k * r) K) (g : Fin 2 → BooleanTable r K),
    BooleanMatchgateIdentities Q ∧ (∀ l, BooleanMatchgateIdentities (g l)) ∧
      sampledAlphabetStar Q g = f}

/-- Proposition 5.4's dimension inequality for the actual star-table locus,
including its polynomial Zariski closure. -/
theorem starTableLocus_affineDimension_le
    (K : Type) [Field K] [Infinite K] (k r : ℕ) :
    affineDimension (starTableLocus K k r) ≤ D k r := by
  let p : AlphabetStarChartChoice (Fin 2) k r → BooleanInput k →
      MvPolynomial (AlphabetStarChartParameter (Fin 2) k r) K :=
    fun c z => sampledAlphabetChartStar c MvPolynomial.X z
  apply affineDimension_le_of_polynomial_cover (starTableLocus K k r) p (D k r)
  · intro c
    simp [D, delta, Nat.add_comm]
  · rintro f ⟨Q, g, hQ, hg, rfl⟩
    obtain ⟨c, a, ha⟩ := exists_sampledAlphabetChartStar_of_mgi hQ hg
    refine ⟨c, a, ?_⟩
    rw [ha]
    funext z
    change (eval₂Hom (RingHom.id K) a) (sampledAlphabetChartStar c X z) = _
    rw [sampledAlphabetChartStar_map]
    simp

/-- The closure in Proposition 5.4 has the same bounded coordinate-ring dimension. -/
theorem starTableLocus_closure_affineDimension_le
    (K : Type) [Field K] [Infinite K] (k r : ℕ) :
    affineDimension (polynomialZariskiClosure (starTableLocus K k r)) ≤ D k r := by
  rw [affineDimension_polynomialZariskiClosure]
  exact starTableLocus_affineDimension_le K k r

end
end MatchgateWidth
