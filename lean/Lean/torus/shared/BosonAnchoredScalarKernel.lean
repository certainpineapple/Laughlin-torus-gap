import torus.shared.BosonAnchoredScalarExpansion
import torus.shared.ThermalCoherentAnchoredMoments
import torus.shared.PlaneJetGramBounds

set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.BosonAnchoredScalarKernel
open TorusLean.Geometry TorusLean.Shared.CoherentJetExpansion
open TorusLean.Shared.PlaneJetReproducing TorusLean.Shared.GroundJetReproducing
open TorusLean.Shared.BosonAnchoredScalarExpansion
open TorusLean.Shared.ThermalCoherentAnchoredMoments
open TorusLean.Shared.ThermalCoherentGaussian TorusLean.Shared.PlaneJetGramBounds
open scoped ComplexConjugate

private theorem gaussian_conj (z : ℂ) : conj (gaussianFactor 1 z)=gaussianFactor 1 z := by
  rw [gaussianFactor_eq_norm,←Complex.exp_conj,Complex.conj_ofReal]

private theorem gaussian_four (z : ℂ) : gaussianFactor 1 z ^ 4 = (thermalWeight 2 z : ℂ) := by
  rw [gaussianFactor_eq_norm]
  simp only [thermalWeight,Complex.ofReal_exp]
  rw [←Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem anchored_weight_factor (j l : ℕ) (z : ℂ) :
    gaussianFactor 1 z * conj (primalCoherentWeight z j) * pairCoherentWeight z l =
      anchoredPlaneCoefficient j l z := by
  simp only [primalCoherentWeight,pairCoherentWeight,map_div₀,map_mul,map_pow,
    gaussian_conj,Complex.conj_ofReal]
  calc
    _ = gaussianFactor 1 z ^ 4 * conj z^j * z^l * (Real.sqrt (2:ℝ):ℂ)^l /
      ((Real.sqrt (j.factorial:ℝ):ℂ)*(Real.sqrt (l.factorial:ℝ):ℂ)) := by
        simp only [div_eq_mul_inv,mul_inv_rev]
        ring
    _ = _ := by rw [gaussian_four]; rfl

/-- The three original torus orbitals retain their magnetic phases. Only
the single internal planar coherent edge has been unfolded. -/
theorem anchored_plane_phase (R z : ℂ) (f g h : ℂ → ℂ) :
    gaussianFactor 1 z *
      (conj (magneticTranslate 1 (-R) h z) *
        (magneticTranslate 1 (-R) f z * magneticTranslate 1 (-R) g z)) =
      conj (translatedPlaneJet 0 R (R+z)) * f (R+z) * g (R+z) * conj (h (R+z)) := by
  have hc : conj (magneticCocycle 1 R z) * magneticCocycle 1 R z = 1 := by
    rw [←Complex.normSq_eq_conj_mul_self,Complex.normSq_eq_norm_sq,magneticCocycle_norm_one]
    norm_num
  have hb (v : ℂ → ℂ) : magneticTranslate 1 (-R) v z =
      conj (magneticCocycle 1 R z) * v (R+z) := by
    have hv := congrArg (starRingEnd ℂ) (conjugate_backTranslate R z v)
    simpa only [map_mul,Complex.conj_conj] using hv
  have ht : translatedPlaneJet 0 R (R+z) = magneticCocycle 1 R z * gaussianFactor 1 z := by
    simp only [translatedPlaneJet,magneticTranslate,planeJet,add_sub_cancel_left,
      pow_zero,Nat.factorial_zero,Nat.cast_one,Real.sqrt_one,Complex.ofReal_one,div_one,mul_one]
    congr 1
    unfold magneticExponent magneticCocycle
    congr 1
    simp only [map_add,Complex.ofReal_one,one_mul]
    ring
  rw [conjugate_backTranslate,hb f,hb g,ht,map_mul,gaussian_conj]
  calc
    _ = (conj (magneticCocycle 1 R z) * magneticCocycle 1 R z) *
      (conj (magneticCocycle 1 R z) * gaussianFactor 1 z *
        f (R+z) * g (R+z) * conj (h (R+z))) := by ring
    _ = _ := by rw [hc,one_mul]

/-- Actual pointwise, absolutely convergent double expansion of the scalar
one-edge kernel. This statement does not interchange any integral. -/
theorem anchored_plane_kernel_hasSum (G : Geometry) (theta : Twist)
    (f g h : RawLLL G theta 1) (R z : ℂ) :
    HasSum (fun jl : ℕ × ℕ => anchoredPlaneCoefficient jl.1 jl.2 z *
      conj (rawJetCoefficient G theta h jl.1 R) * pairJetCoefficient G theta f g R jl.2)
      (conj (translatedPlaneJet 0 R (R+z)) * f.val (R+z) * g.val (R+z) * conj (h.val (R+z))) := by
  have ha := Complex.hasSum_conj'.mpr (primal_coherent_hasSum G theta h R z)
  have hb := pair_coherent_hasSum G theta f g R z
  have ht : Summable (fun jl : ℕ × ℕ =>
      conj (primalCoherentWeight z jl.1 * rawJetCoefficient G theta h jl.1 R) *
        (pairCoherentWeight z jl.2 * pairJetCoefficient G theta f g R jl.2)) :=
    summable_mul_of_summable_norm
      (f := fun j => conj (primalCoherentWeight z j * rawJetCoefficient G theta h j R))
      (g := fun l => pairCoherentWeight z l * pairJetCoefficient G theta f g R l)
      ha.summable.norm hb.summable.norm
  have hs := (ha.mul hb ht).mul_left (gaussianFactor 1 z)
  rw [anchored_plane_phase] at hs
  apply hs.congr_fun
  intro jl
  symm
  rw [map_mul]
  calc
    _ = (gaussianFactor 1 z * conj (primalCoherentWeight z jl.1) * pairCoherentWeight z jl.2) *
      conj (rawJetCoefficient G theta h jl.1 R) * pairJetCoefficient G theta f g R jl.2 := by ring
    _ = _ := by rw [anchored_weight_factor]

end TorusLean.Shared.BosonAnchoredScalarKernel
