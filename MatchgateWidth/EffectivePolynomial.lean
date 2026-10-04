import MatchgateWidth.AlgebraicObstruction
import Mathlib.Data.Finsupp.Encodable
import Mathlib.Data.Rat.Encodable
import Mathlib.Logic.Encodable.Pi

/-!
# Executable rational polynomial arithmetic

The library MvPolynomial ring uses noncomputable Finsupp arithmetic. This
newtype uses DFinsupp for executable addition and finite convolution, with
an injective interpretation proving agreement with the existing ring.
The interpretation homomorphisms are specifications only; none is used by
the executable search. No classical equality is used by runtime operations.
-/

namespace MatchgateWidth.Effective

/-- Executable exponent addition, with the ordinary finite-support meaning. -/
def addExponent {σ : Type} [DecidableEq σ] (a b : σ →₀ ℕ) : σ →₀ ℕ :=
  (a.toDFinsupp + b.toDFinsupp).toFinsupp

@[simp] theorem addExponent_eq {σ : Type} [DecidableEq σ] (a b : σ →₀ ℕ) :
    addExponent a b = a + b := by
  ext i
  simp [addExponent]

/-- Executable rational polynomials. DFinsupp has constructive additive operations. -/
def Polynomial (σ : Type) := Π₀ _ : σ →₀ ℕ, ℚ

namespace Polynomial
variable {σ : Type} [DecidableEq σ]

instance : CoeFun (Polynomial σ) (fun _ => (σ →₀ ℕ) → ℚ) := ⟨fun p => DFinsupp.toFun p⟩

instance : AddCommGroup (Polynomial σ) := inferInstanceAs (AddCommGroup (Π₀ _ : σ →₀ ℕ, ℚ))
instance : DecidableEq (Polynomial σ) := inferInstanceAs (DecidableEq (Π₀ _ : σ →₀ ℕ, ℚ))
instance [Encodable σ] : Encodable (Polynomial σ) := inferInstanceAs (Encodable (Π₀ _ : σ →₀ ℕ, ℚ))

def interpret (p : Polynomial σ) : MvPolynomial σ ℚ := AddMonoidAlgebra.ofCoeff (DFinsupp.toFinsupp p)

def monomial (e : σ →₀ ℕ) (a : ℚ) : Polynomial σ := DFinsupp.single e a

def mul (p q : Polynomial σ) : Polynomial σ :=
  ∑ m ∈ (p : Π₀ _ : σ →₀ ℕ, ℚ).support,
    ∑ n ∈ (q : Π₀ _ : σ →₀ ℕ, ℚ).support,
      monomial (addExponent m n) (p m * q n)

instance : Mul (Polynomial σ) := ⟨mul⟩
instance : One (Polynomial σ) := ⟨monomial 0 1⟩
instance : NatCast (Polynomial σ) := ⟨fun n => monomial 0 n⟩
instance : IntCast (Polynomial σ) := ⟨fun n => monomial 0 n⟩
instance : Pow (Polynomial σ) ℕ := ⟨fun p n => npowRec n p⟩

theorem interpret_injective : Function.Injective (interpret (σ := σ)) := by
  intro p q h
  exact DFinsupp.ext fun i => congrArg (fun t : MvPolynomial σ ℚ => t.coeff i) h

@[simp] theorem interpret_zero : interpret (0 : Polynomial σ) = 0 := by rfl
@[simp] theorem interpret_add (p q : Polynomial σ) :
    interpret (p + q) = interpret p + interpret q := by
  ext e
  rfl
@[simp] theorem interpret_neg (p : Polynomial σ) : interpret (-p) = -interpret p := by
  ext e
  rfl
@[simp] theorem interpret_sub (p q : Polynomial σ) :
    interpret (p - q) = interpret p - interpret q := by
  simp [sub_eq_add_neg]
@[simp] theorem interpret_monomial (e : σ →₀ ℕ) (a : ℚ) :
    interpret (monomial e a) = MvPolynomial.monomial e a := by
  exact congrArg AddMonoidAlgebra.ofCoeff (DFinsupp.toFinsupp_single e a)

noncomputable def interpretAddHom : Polynomial σ →+ MvPolynomial σ ℚ where
  toFun := interpret
  map_zero' := interpret_zero
  map_add' := interpret_add

@[simp] theorem interpret_sum {ι : Type} (s : Finset ι) (f : ι → Polynomial σ) :
    interpret (∑ i ∈ s, f i) = ∑ i ∈ s, interpret (f i) :=
  map_sum interpretAddHom f s

@[simp] theorem interpret_mul (p q : Polynomial σ) :
    interpret (p * q) = interpret p * interpret q := by
  change interpret (mul p q) = _
  simp only [mul, interpret_sum, interpret_monomial, addExponent_eq]
  rw [MvPolynomial.mul_def]
  rfl

@[simp] theorem interpret_one : interpret (1 : Polynomial σ) = 1 := by
  change interpret (monomial 0 1) = _
  rw [interpret_monomial]
  rfl

@[simp] theorem interpret_nsmul (n : ℕ) (p : Polynomial σ) :
    interpret (n • p) = n • interpret p := map_nsmul interpretAddHom n p
@[simp] theorem interpret_zsmul (n : ℤ) (p : Polynomial σ) :
    interpret (n • p) = n • interpret p := map_zsmul interpretAddHom n p

@[simp] theorem interpret_natCast (n : ℕ) : interpret (n : Polynomial σ) = n := by
  change interpret (monomial 0 n) = _
  simp
@[simp] theorem interpret_intCast (n : ℤ) : interpret (n : Polynomial σ) = n := by
  change interpret (monomial 0 n) = _
  simp

@[simp] theorem interpret_pow (p : Polynomial σ) (n : ℕ) :
    interpret (p ^ n) = interpret p ^ n := by
  induction n with
  | zero => exact interpret_one
  | succ n ih =>
      change interpret (p ^ n * p) = _
      rw [interpret_mul, ih, pow_succ]

instance : CommRing (Polynomial σ) :=
  fast_instance% Function.Injective.commRing interpret interpret_injective
    interpret_zero interpret_one interpret_add interpret_mul interpret_neg interpret_sub
    interpret_nsmul interpret_zsmul interpret_pow interpret_natCast interpret_intCast


/-- This homomorphism is only a specification; executable operations are above. -/
noncomputable def interpretHom : Polynomial σ →+* MvPolynomial σ ℚ where
  toFun := interpret
  map_zero' := interpret_zero
  map_one' := interpret_one
  map_add' := interpret_add
  map_mul' := interpret_mul

/-- Every ordinary polynomial has an executable finite-support representative. -/
def ofPolynomial (p : MvPolynomial σ ℚ) : Polynomial σ := p.coeff.toDFinsupp

@[simp] theorem interpret_ofPolynomial (p : MvPolynomial σ ℚ) :
    interpret (ofPolynomial p) = p := by
  ext e
  rfl

def C (a : ℚ) : Polynomial σ := monomial 0 a

@[simp] theorem interpret_C (a : ℚ) : interpret (C a : Polynomial σ) = MvPolynomial.C a := by
  exact interpret_monomial 0 a

def CHom : ℚ →+* Polynomial σ where
  toFun := C
  map_zero' := interpret_injective (by simp)
  map_one' := interpret_injective (by simp)
  map_add' a b := interpret_injective (by simp)
  map_mul' a b := interpret_injective (by simp)

def X (i : σ) : Polynomial σ :=
  monomial (DFinsupp.toFinsupp (DFinsupp.single i 1)) 1

@[simp] theorem interpret_X (i : σ) : interpret (X i) = MvPolynomial.X i := by
  simp only [X, interpret_monomial, DFinsupp.toFinsupp_single]
  rfl

/-- Evaluation is a finite sum of finite products, using decidable rational data. -/
def eval₂ {R : Type} [CommRing R] (f : ℚ →+* R) (a : σ → R) (p : Polynomial σ) : R :=
  ∑ m ∈ (p : Π₀ _ : σ →₀ ℕ, ℚ).support,
    f (p m) * ∏ i ∈ m.support, a i ^ m i

theorem eval₂_eq {R : Type} [CommRing R] (f : ℚ →+* R) (a : σ → R)
    (p : Polynomial σ) : eval₂ f a p = MvPolynomial.eval₂ f a (interpret p) := by
  rw [MvPolynomial.eval₂_eq]
  rfl

/-- Executable polynomial composition. -/
def compose {τ : Type} [DecidableEq τ] (p : Polynomial σ) (a : σ → Polynomial τ) :
    Polynomial τ := eval₂ CHom a p

theorem interpret_compose {τ : Type} [DecidableEq τ]
    (p : Polynomial σ) (a : σ → Polynomial τ) :
    interpret (compose p a) = MvPolynomial.aeval (fun i => interpret (a i)) (interpret p) := by
  rw [compose, eval₂_eq]
  change interpretHom (MvPolynomial.eval₂ CHom a (interpret p)) = _
  rw [MvPolynomial.eval₂_comp_left]
  have hc : (interpretHom (σ := τ)).comp CHom = algebraMap ℚ (MvPolynomial τ ℚ) := by
    apply RingHom.ext
    intro a
    exact interpret_C (σ := τ) a
  rw [hc]
  rfl


end Polynomial
end MatchgateWidth.Effective
