import torus.shared.ParameterRawJetLadderGaussian
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-! The genuine real-parameter oscillator commutator.  This is scalar calculus,
independent of the algebra used to construct its source.  In particular it does
not substitute commuting variables for exterior generators. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.ParameterLadderCommutator
open TorusLean.Shared.ParameterCellAdjoint TorusLean.Shared.ParameterRawJetLadder
open scoped ContDiff ComplexConjugate

private theorem directional_contDiff (f : ℂ → ℂ) (hf : ContDiff ℝ ∞ f) (v : ℂ) :
    ContDiff ℝ ∞ (fun z => fderiv ℝ f z v) :=
  (contDiff_infty_iff_fderiv.mp hf).2.clm_apply contDiff_const

private theorem directional_fderiv (f : ℂ → ℂ) (hf : ContDiff ℝ ∞ f)
    (z v w : ℂ) :
    fderiv ℝ (fun x => fderiv ℝ f x v) z w = fderiv ℝ (fderiv ℝ f) z w v := by
  have hd := (contDiff_infty_iff_fderiv.mp hf).2.differentiable (by simp)
  rw [fderiv_clm_apply (hd z) (differentiableAt_const v)]
  simp

theorem wirtinger_contDiff (f : ℂ → ℂ) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (parameterWirtinger f) ∧ ContDiff ℝ ∞ (parameterWirtingerBar f) := by
  constructor
  · exact ((directional_contDiff f hf 1).sub
      (contDiff_const.mul (directional_contDiff f hf Complex.I))).div_const 2
  · exact ((directional_contDiff f hf 1).add
      (contDiff_const.mul (directional_contDiff f hf Complex.I))).div_const 2

private theorem wirtinger_add (f g : ℂ → ℂ) (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) (z : ℂ) :
    parameterWirtinger (fun x => f x + g x) z = parameterWirtinger f z + parameterWirtinger g z ∧
    parameterWirtingerBar (fun x => f x + g x) z = parameterWirtingerBar f z + parameterWirtingerBar g z := by
  simp only [parameterWirtinger, parameterWirtingerBar, fderiv_fun_add (hf z) (hg z), add_apply]
  constructor <;> ring

private theorem wirtinger_sub (f g : ℂ → ℂ) (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) (z : ℂ) :
    parameterWirtinger (fun x => f x - g x) z = parameterWirtinger f z - parameterWirtinger g z ∧
    parameterWirtingerBar (fun x => f x - g x) z = parameterWirtingerBar f z - parameterWirtingerBar g z := by
  simp only [parameterWirtinger, parameterWirtingerBar, fderiv_fun_sub (hf z) (hg z), sub_apply]
  constructor <;> ring

private theorem wirtinger_directional (f : ℂ → ℂ) (hf : ContDiff ℝ ∞ f) (z v : ℂ) :
    parameterWirtinger (fun x => fderiv ℝ f x v) z =
      (fderiv ℝ (fderiv ℝ f) z 1 v - Complex.I * fderiv ℝ (fderiv ℝ f) z Complex.I v)/2 ∧
    parameterWirtingerBar (fun x => fderiv ℝ f x v) z =
      (fderiv ℝ (fderiv ℝ f) z 1 v + Complex.I * fderiv ℝ (fderiv ℝ f) z Complex.I v)/2 := by
  simp [parameterWirtinger, parameterWirtingerBar, directional_fderiv f hf]

/-- Schwarz symmetry is the only second-order input. -/
theorem wirtinger_commute (f : ℂ → ℂ) (hf : ContDiff ℝ ∞ f) (z : ℂ) :
    parameterWirtinger (parameterWirtingerBar f) z =
      parameterWirtingerBar (parameterWirtinger f) z := by
  let dx : ℂ → ℂ := fun x => fderiv ℝ f x 1
  let dy : ℂ → ℂ := fun x => fderiv ℝ f x Complex.I
  have hx : Differentiable ℝ dx := (directional_contDiff f hf 1).differentiable (by simp)
  have hy : Differentiable ℝ dy := (directional_contDiff f hf Complex.I).differentiable (by simp)
  have he : parameterWirtinger f = fun x => (1/2:ℂ) * (dx x - Complex.I*dy x) := by
    funext x; simp only [parameterWirtinger, dx, dy]; ring
  have hb : parameterWirtingerBar f = fun x => (1/2:ℂ) * (dx x + Complex.I*dy x) := by
    funext x; simp only [parameterWirtingerBar, dx, dy]; ring
  rw [hb, (wirtinger_const_mul (1/2:ℂ) (fun x => dx x + Complex.I*dy x)
      (hx.add (hy.const_mul Complex.I)) z).1,
    (wirtinger_add dx (fun x => Complex.I*dy x) hx (hy.const_mul Complex.I) z).1,
    (wirtinger_const_mul Complex.I dy hy z).1,
    he, (wirtinger_const_mul (1/2:ℂ) (fun x => dx x - Complex.I*dy x)
      (hx.sub (hy.const_mul Complex.I)) z).2,
    (wirtinger_sub dx (fun x => Complex.I*dy x) hx (hy.const_mul Complex.I) z).2,
    (wirtinger_const_mul Complex.I dy hy z).2]
  dsimp only [dx, dy]
  rw [(wirtinger_directional f hf z 1).1, (wirtinger_directional f hf z Complex.I).1,
    (wirtinger_directional f hf z 1).2, (wirtinger_directional f hf z Complex.I).2]
  have hs : IsSymmSndFDerivAt ℝ f z := hf.contDiffAt.isSymmSndFDerivAt (by simp)
  rw [hs (1 : ℂ) Complex.I]
  ring

def unscaledRaise (k : ℕ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  parameterWirtingerBar f z - ((k:ℂ)/2) * z * f z

def unscaledLower (k : ℕ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  -parameterWirtinger f z - ((k:ℂ)/2) * conj z * f z

theorem unscaled_contDiff (k : ℕ) (f : ℂ → ℂ) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (unscaledRaise k f) ∧ ContDiff ℝ ∞ (unscaledLower k f) := by
  have hw := wirtinger_contDiff f hf
  constructor
  · exact hw.2.sub ((contDiff_const.mul contDiff_id).mul hf)
  · exact hw.1.neg.sub ((contDiff_const.mul Complex.conjCLE.contDiff).mul hf)

/-- The unnormalized total parameter commutator is exactly the charge k. -/
theorem unscaled_commutator (k : ℕ) (f : ℂ → ℂ) (hf : ContDiff ℝ ∞ f) (z : ℂ) :
    unscaledLower k (unscaledRaise k f) z - unscaledRaise k (unscaledLower k f) z =
      (k:ℂ) * f z := by
  have hd := hf.differentiable (by simp)
  have hw := wirtinger_contDiff f hf
  have hwd := hw.1.differentiable (by simp)
  have hwbd := hw.2.differentiable (by simp)
  have hid : parameterWirtinger (fun x : ℂ => x) z = 1 := by
    simpa only [deriv_id''] using
      (wirtinger_holomorphic (fun x : ℂ => x) differentiable_id z).1
  have hc : parameterWirtingerBar (fun x : ℂ => conj x) z = 1 := by
    rw [(wirtinger_conj (fun x : ℂ => x) differentiable_id z).2, hid, map_one]
  have hL : unscaledLower k f = fun x => (-1:ℂ) * parameterWirtinger f x -
      ((k:ℂ)/2) * (conj x * f x) := by funext x; unfold unscaledLower; ring
  have hR : unscaledRaise k f = fun x => parameterWirtingerBar f x -
      ((k:ℂ)/2) * (x * f x) := by funext x; unfold unscaledRaise; ring
  have hr : parameterWirtinger (unscaledRaise k f) z =
      parameterWirtinger (parameterWirtingerBar f) z -
      ((k:ℂ)/2) * (f z + z*parameterWirtinger f z) := by
    rw [hR, (wirtinger_sub (parameterWirtingerBar f)
      (fun x => ((k:ℂ)/2)*(x*f x)) hwbd
      ((differentiable_id.mul hd).const_mul ((k:ℂ)/2)) z).1,
      (wirtinger_const_mul ((k:ℂ)/2) (fun x => x*f x)
        (differentiable_id.mul hd) z).1,
      wirtinger_mul (fun x : ℂ => x) f differentiable_id hd z,
      hid, one_mul]
  have hl : parameterWirtingerBar (unscaledLower k f) z =
      -parameterWirtingerBar (parameterWirtinger f) z -
      ((k:ℂ)/2) * (f z + conj z*parameterWirtingerBar f z) := by
    rw [hL, (wirtinger_sub (fun x => (-1:ℂ)*parameterWirtinger f x)
      (fun x => ((k:ℂ)/2)*(conj x*f x)) (hwd.const_mul (-1:ℂ))
      ((Complex.conjCLE.differentiable.mul hd).const_mul ((k:ℂ)/2)) z).2,
      (wirtinger_const_mul (-1:ℂ) (parameterWirtinger f) hwd z).2,
      (wirtinger_const_mul ((k:ℂ)/2) (fun x => conj x*f x)
        (Complex.conjCLE.differentiable.mul hd) z).2,
      wirtingerBar_mul (fun x : ℂ => conj x) f Complex.conjCLE.differentiable hd z,
      hc, one_mul]
    ring
  change -(parameterWirtinger (unscaledRaise k f) z) - ((k:ℂ)/2)*conj z*(unscaledRaise k f z) -
    (parameterWirtingerBar (unscaledLower k f) z - ((k:ℂ)/2)*z*(unscaledLower k f z)) = _
  rw [hr, hl, wirtinger_commute f hf z]
  simp only [unscaledRaise, unscaledLower]
  ring

theorem parameterRaise_eq_unscaled (k : ℕ) (f : ℂ → ℂ) :
    parameterRaise k f = fun z => (Real.sqrt (k:ℝ):ℂ)⁻¹ * unscaledRaise k f z := by
  funext z; unfold parameterRaise unscaledRaise; ring

theorem parameterLower_eq_unscaled (k : ℕ) (f : ℂ → ℂ) :
    parameterLower k f = fun z => (Real.sqrt (k:ℝ):ℂ)⁻¹ * unscaledLower k f z := by
  funext z; unfold parameterLower unscaledLower; ring

/-- The actual operators satisfy [lower,raise]=1 on their smooth domain. -/
theorem parameter_commutator (k : ℕ) [NeZero k] (f : ℂ → ℂ)
    (hf : ContDiff ℝ ∞ f) (z : ℂ) :
    parameterLower k (parameterRaise k f) z - parameterRaise k (parameterLower k f) z = f z := by
  have hk : (Real.sqrt (k:ℝ):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
    (ne_of_gt (Real.sqrt_pos.mpr (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne k)))))
  have hs : (Real.sqrt (k:ℝ):ℂ)^2 = (k:ℂ) := by
    exact_mod_cast Real.sq_sqrt (show (0:ℝ) ≤ k by positivity)
  have hu := unscaled_contDiff k f hf
  rw [parameterRaise_eq_unscaled k f, parameterLower_const_mul _ _ _ (hu.1.differentiable (by simp)),
    parameterLower_eq_unscaled k f, parameterRaise_const_mul _ _ _ (hu.2.differentiable (by simp)),
    parameterLower_eq_unscaled k (unscaledRaise k f),
    parameterRaise_eq_unscaled k (unscaledLower k f)]
  change (Real.sqrt (k:ℝ):ℂ)⁻¹ * ((Real.sqrt (k:ℝ):ℂ)⁻¹ * unscaledLower k (unscaledRaise k f) z) -
    (Real.sqrt (k:ℝ):ℂ)⁻¹ * ((Real.sqrt (k:ℝ):ℂ)⁻¹ * unscaledRaise k (unscaledLower k f) z) = f z
  calc
    _ = ((Real.sqrt (k:ℝ):ℂ)⁻¹)^2 *
        (unscaledLower k (unscaledRaise k f) z - unscaledRaise k (unscaledLower k f) z) := by ring
    _ = _ := by rw [unscaled_commutator k f hf z, ← hs]; field_simp [hk] <;> ring

#print axioms wirtinger_commute
#print axioms parameter_commutator
#print axioms wirtinger_contDiff
#print axioms unscaled_contDiff
#print axioms unscaled_commutator
#print axioms parameterRaise_eq_unscaled
#print axioms parameterLower_eq_unscaled

end TorusLean.Shared.ParameterLadderCommutator
