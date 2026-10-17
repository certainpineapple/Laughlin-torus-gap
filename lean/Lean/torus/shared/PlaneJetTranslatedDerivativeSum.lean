import torus.shared.PlaneJetDerivativeSum
import torus.shared.PlaneJetReproducing
import Mathlib.Topology.MetricSpace.Algebra

set_option autoImplicit false
noncomputable section

namespace TorusLean.Shared.PlaneJetTranslatedDerivativeSum

open Filter TorusLean.Geometry TorusLean.Shared.PlaneJetMembership
open TorusLean.Shared.GroundJetReproducing TorusLean.Shared.PlaneJetReproducing
open TorusLean.Shared.PlaneJetDerivativeSum
open TorusLean.Fermion.CanonicalPlaneJets
open scoped ComplexConjugate

theorem locallyUniform_translatedStrippedFactor {ι : Type*} {l : Filter ι}
    {F : ι → ℂ → ℂ} {f : ℂ → ℂ} (hf : Continuous f)
    (hlim : TendstoLocallyUniformlyOn F f l Set.univ) (x : ℂ) :
    TendstoLocallyUniformlyOn (fun i => translatedStrippedFactor x (F i))
      (translatedStrippedFactor x f) l Set.univ := by
  let a : ℂ → ℂ := fun z => Complex.exp (z * conj x - (x * conj x) / 2)
  have ha : Continuous a := by dsimp [a]; fun_prop
  have hconst : TendstoLocallyUniformlyOn (fun _ : ι => a) a l Set.univ := by
    intro u hu z _
    exact ⟨Set.univ, Filter.univ_mem,
      Eventually.of_forall fun _ y _ => refl_mem_uniformity hu⟩
  have hc := hlim.comp (t := Set.univ) (fun z : ℂ => z - x) (Set.mapsTo_univ _ _) 
    (continuous_id.sub continuous_const).continuousOn
  exact hconst.mul₀ hc ha.continuousOn (hf.comp (continuous_id.sub continuous_const)).continuousOn

/-- Differentiation through the actual image series after an arbitrary
physical magnetic translation of the stripped factor. -/
theorem translatedPlaneJetStrippedImages_hasSum_iteratedDeriv
    (G : Geometry) (theta : Twist) (j n : ℕ) (R x z : ℂ) :
    HasSum (fun p : ℤ × ℤ =>
      iteratedDeriv n (translatedStrippedFactor x (planeJetStrippedImage G theta j R p)) z)
      (iteratedDeriv n (translatedStrippedFactor x
        (fun w => ∑' p : ℤ × ℤ, planeJetStrippedImage G theta j R p w)) z) := by
  apply hasSum_iteratedDeriv_of_locallyUniform
  · intro p
    exact translatedStrippedFactor_differentiable x _
      (planeJetStrippedImage_differentiable G theta j R p)
  · have ht := locallyUniform_translatedStrippedFactor
      (planeJetStrippedSum_differentiable G theta j R).continuous
      (planeJetStrippedImages_tendstoLocallyUniformlyOn G theta j R) x
    convert ht using 1
    ext s w
    simp [translatedStrippedFactor, Finset.mul_sum]

/-- The actual raw jet has exactly the original image-sum stripped factor. -/
theorem canonicalRawStripped_rawPlaneJet (G : Geometry) (theta : Twist)
    (j : ℕ) (R : ℂ) :
    canonicalRawStripped G theta (rawPlaneJet G theta j R) =
      fun z => ∑' p : ℤ × ℤ, planeJetStrippedImage G theta j R p z := by
  apply canonicalRawStripped_eq_factor
  intro z
  change (∑' p : ℤ × ℤ, magneticImage G.M 1 G.omega1 G.omega2
    theta.theta1 theta.theta2 (translatedPlaneJet j R) p z) = _
  simp_rw [planeJet_magneticImage_factor]
  exact tsum_mul_left

/-- The actual all-j/m Gram coefficient is a convergent single image sum
of exact translated derivatives, retaining the original sqrt(j!) denominator. -/
theorem rawJetCoefficient_rawPlaneJet_hasSum
    (G : Geometry) (theta : Twist) (j m : ℕ) (R S : ℂ) :
    HasSum (fun p : ℤ × ℤ =>
      iteratedDeriv j (translatedStrippedFactor (-R)
        (planeJetStrippedImage G theta m S p)) 0 / (Real.sqrt (j.factorial : ℝ) : ℂ))
      (rawJetCoefficient G theta (rawPlaneJet G theta m S) j R) := by
  unfold rawJetCoefficient
  rw [canonicalRawStripped_rawPlaneJet]
  exact (translatedPlaneJetStrippedImages_hasSum_iteratedDeriv G theta m j S (-R) 0).div_const _

/-- Exact physical cell Gram as a convergent single image derivative sum. -/
theorem rawPlaneJet_cell_gram_hasSum
    (G : Geometry) (theta : Twist) (j m : ℕ) (R S : ℂ) :
    HasSum (fun p : ℤ × ℤ =>
      iteratedDeriv j (translatedStrippedFactor (-R)
        (planeJetStrippedImage G theta m S p)) 0 / (Real.sqrt (j.factorial : ℝ) : ℂ))
      (cellInner G 1
        (rawJetFunction G.M G.omega1 G.omega2 theta.theta1 theta.theta2 j R)
        (rawJetFunction G.M G.omega1 G.omega2 theta.theta1 theta.theta2 m S)) := by
  rw [rawPlaneJet_cell_gram]
  exact rawJetCoefficient_rawPlaneJet_hasSum G theta j m R S

#print axioms rawPlaneJet_cell_gram_hasSum
#print axioms canonicalRawStripped_rawPlaneJet
#print axioms rawJetCoefficient_rawPlaneJet_hasSum
#print axioms locallyUniform_translatedStrippedFactor
#print axioms translatedPlaneJetStrippedImages_hasSum_iteratedDeriv

end TorusLean.Shared.PlaneJetTranslatedDerivativeSum
