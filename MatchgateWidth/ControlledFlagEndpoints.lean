import MatchgateWidth.ExactFlagNormalForm
import MatchgateWidth.ControlledLabelledPresentation
import MatchgateWidth.ControlledFlagSupports

/-! # Literal parity endpoints of the controlled qutrit flag -/
namespace MatchgateWidth
noncomputable section
open scoped Classical

def controlledLabelledCode (k : ℕ) (d : Fin 3) : BooleanInput (2^k+3) :=
  (booleanWordEquiv (2^k+3)).symm (controlledCode k d)

theorem controlledLabelledCode_injective (k : ℕ) : Function.Injective (controlledLabelledCode k) :=
  (booleanWordEquiv _).symm.injective.comp (controlledCode_injective k)

theorem controlledLabelledCode_zero (k : ℕ) : controlledLabelledCode k 0 = fun _ => 0 := by
  funext i
  simp [controlledLabelledCode, booleanWordEquiv, controlledCode]

theorem controlledLabelledCode_one (k : ℕ) :
    controlledLabelledCode k 1 = fun i => if i = 0 then 1 else 0 := by
  funext i
  simp [controlledLabelledCode, booleanWordEquiv, controlledCode]

theorem controlledLabelledCode_zero_parity (k : ℕ) : booleanParity (controlledLabelledCode k 0)=0 := by
  rw [controlledLabelledCode_zero]
  simp [booleanParity, booleanSubsetEquiv]

theorem controlledLabelledCode_one_parity (k : ℕ) : booleanParity (controlledLabelledCode k 1)=1 := by
  rw [controlledLabelledCode_one]
  have h : booleanSubsetEquiv (2^k+3) (fun i => if i=0 then 1 else 0) = {0} := by
    ext i
    simp [booleanSubsetEquiv]
  simp only [booleanParity, h, Finset.card_singleton]

theorem controlledLabelledBase_rank (k : ℕ) : Matrix.rank (controlledLabelledBase k) = 3 :=
  coordinateBase_rank _ (controlledLabelledCode_injective k)

theorem controlledLabelledBase_code (k : ℕ) (u : Fin 3 → ℂ) (d : Fin 3) :
    (Matrix.transpose (controlledLabelledBase k)).mulVecLin u (controlledLabelledCode k d) = u d := by
  change ∑ i : Fin 3, controlledLabelledBase k i (controlledLabelledCode k d) * u i = u d
  simp [controlledLabelledBase, coordinateBase, controlledLabelledCode,
    (controlledCode_injective k).eq_iff]


/-- The two source parity endpoints are exactly the first two coordinate rays. -/
theorem controlled_flag_parity_endpoints (k : ℕ) :
    primitiveParityEndpoint (controlledLabelledBase k) (qutritCoordinatePlane 2) 0 =
      qutritCoordinateRay 0 ∧
    primitiveParityEndpoint (controlledLabelledBase k) (qutritCoordinatePlane 2) 1 =
      qutritCoordinateRay 1 := by
  have hc (r : Fin 3) : controlledLabelledBase k r =
      Pi.single (controlledLabelledCode k r) (1 : ℂ) := by
    funext y
    simp [controlledLabelledBase, coordinateBase, controlledLabelledCode, Pi.single_apply]
  have hgen (r : Fin 3) : (Matrix.transpose (controlledLabelledBase k)).mulVecLin (Pi.single r 1) =
      controlledLabelledBase k r := by
    ext y
    change (∑ x : Fin 3, controlledLabelledBase k x y * (Pi.single r (1 : ℂ) : Fin 3 → ℂ) x) = _
    simp [Pi.single_apply]
  have endpoint (b : ℕ) (d e : Fin 3) (hde : d ≠ e)
      (hd : d ≠ 2) (he : e ≠ 2) (hcover : ∀ i : Fin 3, i=d ∨ i=e ∨ i=2)
      (hpar : booleanParity (controlledLabelledCode k d)=b)
      (hother : booleanParity (controlledLabelledCode k e)≠b) :
      primitiveParityEndpoint (controlledLabelledBase k) (qutritCoordinatePlane 2) b =
        qutritCoordinateRay d := by
    apply le_antisymm
    · intro u hu
      have hu2 : u 2=0 := hu.1
      have hue : u e=0 := by
        have hx := hu.2 (controlledLabelledCode k e) hother
        exact (controlledLabelledBase_code k u e).symm.trans hx
      apply Submodule.mem_span_singleton.mpr
      refine ⟨u d, ?_⟩
      funext i
      rcases hcover i with rfl | rfl | rfl
      · simp
      · simp [hde, hue]
      · simp [hd, hu2]
    · apply Submodule.span_le.mpr
      intro u hu
      rcases Set.mem_singleton_iff.mp hu with rfl
      refine ⟨?_, ?_⟩
      · change (Pi.single d (1 : ℂ) : Fin 3 → ℂ) 2=0
        simp [Ne.symm hd]
      · change (Matrix.transpose (controlledLabelledBase k)).mulVecLin (Pi.single d 1) ∈ booleanParitySubspace _ b
        rw [hgen, hc]
        intro y hy
        have hne : y ≠ controlledLabelledCode k d := by intro h; subst y; exact hy hpar
        simp [ hne]
  exact ⟨endpoint 0 0 1 (by decide) (by decide) (by decide)
    (by intro i; fin_cases i <;> simp) (controlledLabelledCode_zero_parity k)
    (by rw [controlledLabelledCode_one_parity]; decide),
    endpoint 1 1 0 (by decide) (by decide) (by decide)
    (by intro i; fin_cases i <;> simp) (controlledLabelledCode_one_parity k)
    (by rw [controlledLabelledCode_zero_parity]; decide)⟩

end
end MatchgateWidth
