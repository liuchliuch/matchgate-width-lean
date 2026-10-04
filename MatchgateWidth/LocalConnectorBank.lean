import MatchgateWidth.TransversePortAngles
import MatchgateWidth.VariableAnnularRouting

/-! # Actual ordered local connector banks to transverse wire endpoints

One fixed local complex frame is retained, including its possibly nonunit
scale. Native matchgate ports are on an inner circle. Their actual perturbed
wire endpoints acquire explicit angles and radii; variable annular connectors
then give simple disjoint paths, bounded in the chosen local collar and outside
the inserted graph disk except at their own starts.
-/
namespace MatchgateWidth
noncomputable section
open Filter Topology

/-- The actual geometric local output of the annular connector construction. -/
structure LocalConnectorBank {N : ℕ} (c rot : ℂ) (R T : ℝ)
    (α : Fin N → ℝ) (endpoint : Fin N → ℂ) where
  path : ∀ q, Path (c + rot * ((R : ℂ)*boundaryPoint (α q))) (c + endpoint q)
  simple : ∀ q, Function.Injective (path q)
  disjoint : Pairwise (fun q s => Disjoint (Set.range (path q)) (Set.range (path s)))
  bound : ∀ q t, dist (path q t) c ≤ ‖rot‖*T
  inner_only_start : ∀ q t, dist (path q t) c ≤ ‖rot‖*R → t = 0

namespace LocalConnectorBank
variable {N : ℕ} {c rot : ℂ} {R T : ℝ} {α : Fin N → ℝ} {endpoint : Fin N → ℂ}

/-- Every local connector meets the inserted graph's closed carrier disk only
at its own exact source port. -/
theorem meets_inner (B : LocalConnectorBank c rot R T α endpoint) (q : Fin N) :
    Set.range (B.path q) ∩ Metric.closedBall c (‖rot‖*R) ⊆
      {c + rot*((R:ℂ)*boundaryPoint (α q))} := by
  intro z hz
  obtain ⟨t,rfl⟩ := hz.1
  have ht : t = 0 := B.inner_only_start q t hz.2
  change B.path q t = _
  rw [ht,Path.source]

theorem in_outer (B : LocalConnectorBank c rot R T α endpoint) (q : Fin N) :
    Set.range (B.path q) ⊆ Metric.closedBall c (‖rot‖*T) := by
  rintro z ⟨t,rfl⟩
  exact B.bound q t

end LocalConnectorBank

namespace OrderedRayAngles
variable {n r : ℕ} {p : Fin n → ℂ} (A : OrderedRayAngles p)

def blockRadius (w : Fin n → ℂ) (d : Fin n → Fin r → ℝ) (ε : ℝ)
    (q : Fin (n*r)) : ℝ :=
  let i := (finProdFinEquiv.symm q).1
  let k := (finProdFinEquiv.symm q).2
  A.radius i * transverseRadiusFactor (p i) (w i) (ε*d i k)

def flatBlockAngle (w : Fin n → ℂ) (d : Fin n → Fin r → ℝ) (ε : ℝ)
    (q : Fin (n*r)) : ℝ :=
  A.blockAngle w d ε (finProdFinEquiv.symm q).1 (finProdFinEquiv.symm q).2

@[simp] theorem blockRadius_zero (w : Fin n → ℂ) (d : Fin n → Fin r → ℝ)
    (q : Fin (n*r)) : A.blockRadius w d 0 q = A.radius (finProdFinEquiv.symm q).1 := by
  simp [blockRadius]

theorem blockRadius_continuousAt_zero (w : Fin n → ℂ) (d : Fin n → Fin r → ℝ)
    (q : Fin (n*r)) : ContinuousAt (fun ε => A.blockRadius w d ε q) 0 := by
  unfold blockRadius transverseRadiusFactor
  fun_prop (disch := simp)

/-- The explicit curve formula is defined even at zero width, where ports
inside one sector can coincide. Its positive-width instances are simple. -/
def localBlockConnector (c : ℂ) (w : Fin n → ℂ) (d : Fin n → Fin r → ℝ)
    (α : Fin (n*r) → ℝ) (R S ε : ℝ) (q : Fin (n*r)) (t : unitInterval) : ℂ :=
  c + A.rotation * (((affineBlend R (A.blockRadius w d ε q) t : ℝ) : ℂ) *
    boundaryPoint (affineBlend (α q) (A.flatBlockAngle w d ε q)
      (annularLevel R S (affineBlend R (A.blockRadius w d ε q) t))))

/-- Joint continuity along the compact zero-width reference trace, needed to
separate all nonincident stages by one uniform perturbation width. -/
theorem localBlockConnector_continuousAt_zero (c : ℂ) (w : Fin n → ℂ)
    (d : Fin n → Fin r → ℝ) (α : Fin (n*r) → ℝ) (R S : ℝ)
    (q : Fin (n*r)) (t : unitInterval) :
    ContinuousAt (fun z : ℝ × unitInterval => A.localBlockConnector c w d α R S z.1 q z.2) (0,t) := by
  have hρ : ContinuousAt (fun z : ℝ × unitInterval => A.blockRadius w d z.1 q) (0,t) :=
    (A.blockRadius_continuousAt_zero w d q).comp_of_eq continuousAt_fst rfl
  have hβ : ContinuousAt (fun z : ℝ × unitInterval => A.flatBlockAngle w d z.1 q) (0,t) :=
    (A.blockAngle_continuousAt_zero w d (finProdFinEquiv.symm q).1
      (finProdFinEquiv.symm q).2).comp_of_eq continuousAt_fst rfl
  have ht : ContinuousAt (fun z : ℝ × unitInterval => (z.2 : ℝ)) (0,t) :=
    continuous_subtype_val.continuousAt.comp continuousAt_snd
  have hlevel : Continuous (fun x : ℝ => (annularLevel R S x : ℝ)) := by
    unfold annularLevel
    exact continuous_subtype_val.comp (continuous_projIcc.comp (by fun_prop))
  have hcircle : Continuous boundaryPoint := by unfold boundaryPoint circleMap; fun_prop
  have hblend : ContinuousAt (fun z : ℝ × unitInterval => affineBlend R (A.blockRadius w d z.1 q) z.2) (0,t) :=
    ((continuousAt_const.sub ht).mul continuousAt_const).add (ht.mul hρ)
  have hℓ : ContinuousAt (fun z : ℝ × unitInterval =>
      (annularLevel R S (affineBlend R (A.blockRadius w d z.1 q) z.2) : ℝ)) (0,t) :=
    hlevel.continuousAt.comp hblend
  have hang : ContinuousAt (fun z : ℝ × unitInterval => affineBlend (α q)
      (A.flatBlockAngle w d z.1 q) (annularLevel R S (affineBlend R (A.blockRadius w d z.1 q) z.2))) (0,t) :=
    ((continuousAt_const.sub hℓ).mul continuousAt_const).add (hℓ.mul hβ)
  exact continuousAt_const.add (continuousAt_const.mul
    ((Complex.continuous_ofReal.continuousAt.comp hblend).mul
      (hcircle.continuousAt.comp hang)))

private theorem blockEndpoint_eq (w : Fin n → ℂ) (d : Fin n → Fin r → ℝ) (ε : ℝ)
    (hden : ∀ i k, 0 < 1+(ε*d i k)*(w i/p i).re) (q : Fin (n*r)) :
    A.blockEndpoint w d ε q = A.rotation *
      ((A.blockRadius w d ε q : ℝ) : ℂ) * boundaryPoint (A.flatBlockAngle w d ε q) := by
  exact A.perturbed_point_eq w (fun i => ε*d i (finProdFinEquiv.symm q).2)
    (fun i => hden i _) (finProdFinEquiv.symm q).1

/-- A bundled connector whose target is the literal transverse endpoint,
not a chosen point merely having the right order. -/
def localBlockConnectorPath (c : ℂ) (w : Fin n → ℂ) (d : Fin n → Fin r → ℝ)
    (α : Fin (n*r) → ℝ) (R S ε : ℝ) (hRS : R < S)
    (hρ : ∀ q, S ≤ A.blockRadius w d ε q)
    (hden : ∀ i k, 0 < 1+(ε*d i k)*(w i/p i).re) (q : Fin (n*r)) :
    Path (c + A.rotation * ((R : ℂ)*boundaryPoint (α q))) (c + A.blockEndpoint w d ε q) where
  toFun := A.localBlockConnector c w d α R S ε q
  continuous_toFun := by
    have hlevel : Continuous (annularLevel R S) := by
      unfold annularLevel
      exact continuous_projIcc.comp (by fun_prop)
    unfold localBlockConnector affineBlend boundaryPoint circleMap
    fun_prop
  source' := by simp [localBlockConnector,affineBlend,annularLevel_start]
  target' := by
    have hlevel := annularLevel_end hRS (hρ q)
    simp [localBlockConnector, affineBlend, hlevel, A.blockEndpoint_eq w d ε hden q, mul_assoc]

theorem localBlockConnector_norm (c : ℂ) (w : Fin n → ℂ)
    (d : Fin n → Fin r → ℝ) (α : Fin (n*r) → ℝ) (R S ε : ℝ)
    (hR : 0 < R) (hRS : R < S) (hρ : ∀ q, S ≤ A.blockRadius w d ε q)
    (q : Fin (n*r)) (t : unitInterval) :
    dist (A.localBlockConnector c w d α R S ε q t) c =
      ‖A.rotation‖ * affineBlend R (A.blockRadius w d ε q) t := by
  rw [dist_eq_norm]
  simp only [localBlockConnector,add_sub_cancel_left,norm_mul,norm_boundaryPoint,mul_one,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos
      (affineBlend_pos hR ((hR.trans hRS).trans_le (hρ q)) t)]

/-- Beyond the common inner interpolation circle, the bank follows the
literal ray through its exact transverse endpoint, even in a nonunit frame. -/
theorem localBlockConnector_radial_point (c : ℂ) (w : Fin n → ℂ)
    (d : Fin n → Fin r → ℝ) (α : Fin (n*r) → ℝ) (R S ε : ℝ)
    (hR : 0 < R) (hRS : R < S) (hρ : ∀ q, S ≤ A.blockRadius w d ε q)
    (hden : ∀ i k, 0 < 1+(ε*d i k)*(w i/p i).re)
    (q : Fin (n*r)) (t : unitInterval)
    (ht : S ≤ affineBlend R (A.blockRadius w d ε q) t) :
    A.localBlockConnector c w d α R S ε q t = c +
      (affineBlend R (A.blockRadius w d ε q) t / A.blockRadius w d ε q) •
        A.blockEndpoint w d ε q := by
  have hρ0 : A.blockRadius w d ε q ≠ 0 := ne_of_gt ((hR.trans hRS).trans_le (hρ q))
  unfold localBlockConnector
  rw [annularLevel_end hRS ht]
  simp only [affineBlend,Set.Icc.coe_one,sub_self,zero_mul,one_mul,zero_add]
  rw [A.blockEndpoint_eq w d ε hden q,Complex.real_smul,Complex.ofReal_div]
  have hc : (A.blockRadius w d ε q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hρ0
  field_simp

/-- The actual bank constructor once its explicitly computed endpoint angle
and radius inequalities are established. -/
def localConnectorBank (c : ℂ) (w : Fin n → ℂ) (d : Fin n → Fin r → ℝ)
    (α : Fin (n*r) → ℝ) (R S T ε : ℝ)
    (hR : 0 < R) (hRS : R < S)
    (hρ : ∀ q, S ≤ A.blockRadius w d ε q)
    (hT : ∀ q, A.blockRadius w d ε q ≤ T)
    (hden : ∀ i k, 0 < 1+(ε*d i k)*(w i/p i).re)
    (hα : StrictMono α) (hα0 : ∀ q, 0 < α q) (hα1 : ∀ q, α q < 1)
    (hβ : StrictMono (A.flatBlockAngle w d ε))
    (hβ0 : ∀ q, 0 < A.flatBlockAngle w d ε q)
    (hβ1 : ∀ q, A.flatBlockAngle w d ε q < 1) :
    LocalConnectorBank c A.rotation R T α (A.blockEndpoint w d ε) where
  path := A.localBlockConnectorPath c w d α R S ε hRS hρ hden
  simple := by
    intro q t u he
    have hr := congrArg (fun z => dist z c) he
    change dist (A.localBlockConnector c w d α R S ε q t) c =
      dist (A.localBlockConnector c w d α R S ε q u) c at hr
    rw [A.localBlockConnector_norm c w d α R S ε hR hRS hρ,
      A.localBlockConnector_norm c w d α R S ε hR hRS hρ] at hr
    have hn : ‖A.rotation‖ ≠ 0 := norm_ne_zero_iff.mpr A.rotation_ne_zero
    have hh := mul_left_cancel₀ hn hr
    have hρq : R < A.blockRadius w d ε q := hRS.trans_le (hρ q)
    apply Subtype.ext
    dsimp [affineBlend] at hh
    nlinarith
  disjoint := by
    intro i j hij
    have hh := variableAnnularConnectors_disjoint (n := n*r) 0 hR hRS
      (A.blockRadius w d ε) α (A.flatBlockAngle w d ε) hρ hα hβ hα0 hα1 hβ0 hβ1 hij
    apply Set.disjoint_left.mpr
    rintro z ⟨t,rfl⟩ ⟨u,hu⟩
    have he := mul_left_cancel₀ A.rotation_ne_zero (add_left_cancel hu)
    apply Set.disjoint_left.mp hh ⟨t,rfl⟩ ⟨u,?_⟩
    change (0 : ℂ) + (affineBlend R (A.blockRadius w d ε j) u : ℂ) *
        boundaryPoint (affineBlend (α j) (A.flatBlockAngle w d ε j)
          (annularLevel R S (affineBlend R (A.blockRadius w d ε j) u))) =
      0 + (affineBlend R (A.blockRadius w d ε i) t : ℂ) *
        boundaryPoint (affineBlend (α i) (A.flatBlockAngle w d ε i)
          (annularLevel R S (affineBlend R (A.blockRadius w d ε i) t)))
    simpa only [zero_add] using he
  bound := by
    intro q t
    change dist (A.localBlockConnector c w d α R S ε q t) c ≤ _
    rw [A.localBlockConnector_norm c w d α R S ε hR hRS hρ]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg A.rotation)
    have hb := (variableAnnularConnector_bounds 0 hR hRS (hρ q) (α q)
      (A.flatBlockAngle w d ε q) t).2
    rw [variableAnnularConnector_norm 0 hR] at hb
    exact hb.trans (hT q)
  inner_only_start := by
    intro q t ht
    change dist (A.localBlockConnector c w d α R S ε q t) c ≤ _ at ht
    rw [A.localBlockConnector_norm c w d α R S ε hR hRS hρ] at ht
    have hn : 0 < ‖A.rotation‖ := norm_pos_iff.mpr A.rotation_ne_zero
    have hh := (mul_le_mul_iff_right₀ hn).mp ht
    have hρq : R < A.blockRadius w d ε q := hRS.trans_le (hρ q)
    apply Subtype.ext
    change (t : ℝ) = 0
    dsimp [affineBlend] at hh
    nlinarith [t.property.1]

/-- One positive width bound constructs the complete bank for every smaller
positive width, preserving the native first port and physical within-block order. -/
theorem exists_localConnectorBank (c : ℂ) (w : Fin n → ℂ) (d : Fin n → Fin r → ℝ)
    (horder : ∀ i k l, k < l → 0 < (d i l-d i k)*orientedArea (p i) (w i))
    (α : Fin (n*r) → ℝ) (hα : StrictMono α)
    (hα0 : ∀ q, 0 < α q) (hα1 : ∀ q, α q < 1)
    (R S T : ℝ) (hR : 0 < R) (hRS : R < S)
    (hS : ∀ i, S < A.radius i) (hT : ∀ i, A.radius i < T) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε, 0 < ε → ε < ε₀ →
      ∃ B : LocalConnectorBank c A.rotation R T α (A.blockEndpoint w d ε),
        ∀ q t, B.path q t = A.localBlockConnector c w d α R S ε q t := by
  have hradius : ∀ᶠ ε in 𝓝 (0:ℝ), ∀ q, S < A.blockRadius w d ε q ∧ A.blockRadius w d ε q < T := by
    rw [Filter.eventually_all]
    intro q
    exact (continuousAt_const.eventually_lt (A.blockRadius_continuousAt_zero w d q)
      (by simpa using hS (finProdFinEquiv.symm q).1)).and
      ((A.blockRadius_continuousAt_zero w d q).eventually_lt continuousAt_const
        (by simpa using hT (finProdFinEquiv.symm q).1))
  obtain ⟨ε₀,hε₀,hball⟩ := Metric.mem_nhds_iff.mp ((A.eventually_blockAngle_order w d).and hradius)
  refine ⟨ε₀,hε₀,?_⟩
  intro ε hε hεlt
  have hmem : ε ∈ Metric.ball (0:ℝ) ε₀ := by simpa [Metric.mem_ball,Real.dist_eq,abs_of_pos hε] using hεlt
  obtain ⟨⟨hden,hrange,hbetween⟩,hρ⟩ := hball hmem
  have hβ : StrictMono (A.flatBlockAngle w d ε) := strictMono_flatten_blocks _
    (A.blockAngle_strictMono_of_signed_area w d horder hε hden) hbetween
  refine ⟨A.localConnectorBank c w d α R S T ε hR hRS
    (fun q => (hρ q).1.le) (fun q => (hρ q).2.le) hden hα hα0 hα1 hβ
    (fun q => (hrange _ _).1) (fun q => (hrange _ _).2), ?_⟩
  intro q t
  rfl

end OrderedRayAngles
end
end MatchgateWidth
