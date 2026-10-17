import torus.shared.MagneticBoundaryUnfolding
import torus.shared.PlaneJetReproducing

/-! The actual exterior three-orbital coefficient has charge one, even
though it is not generally an analytic LLL section. This is the domain
needed to unfold one internal edge without changing the exterior orbitals. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.Shared.PhysicalBosonOneEdgeBoundary
open TorusLean.Geometry TorusLean.Shared.MagneticBoundaryUnfolding
open scoped ComplexConjugate

def exteriorTriple (G : Geometry) (theta : Twist)
    (f g h : RawLLL G theta 1) (S : ℂ) : ℂ := f.val S * g.val S * conj (h.val S)

theorem exteriorTriple_continuous (G : Geometry) (theta : Twist)
    (f g h : RawLLL G theta 1) : Continuous (exteriorTriple G theta f g h) :=
  ((rawLLL_continuous G theta 1 f).mul (rawLLL_continuous G theta 1 g)).mul
    (Complex.continuous_conj.comp (rawLLL_continuous G theta 1 h))

theorem exteriorTriple_boundary (G : Geometry) (theta : Twist)
    (f g h : RawLLL G theta 1) :
    HasLatticeBoundary G.M 1 G.omega1 G.omega2 theta.theta1 theta.theta2
      (exteriorTriple G theta f g h) := by
  apply (latticeBoundary_iff_forward _ _ _ _ _ _ _).mpr
  intro p S
  have hf := (latticeBoundary_iff_forward _ _ _ _ _ _ _).mp f.property.2 p S
  have hg := (latticeBoundary_iff_forward _ _ _ _ _ _ _).mp g.property.2 p S
  have hh := (latticeBoundary_iff_forward _ _ _ _ _ _ _).mp h.property.2 p S
  let b : ℂ := (latticeChi G.M theta.theta1 theta.theta2 p ^ 1)⁻¹ *
    Complex.exp (magneticExponent (1:ℝ) S (latticePeriod G.omega1 G.omega2 p))
  have hb : ‖b‖=1 := by
    simp only [b,norm_mul,norm_inv,norm_pow,latticeChi_norm,
      magneticMultiplier_norm,one_pow,inv_one,one_mul]
  have hc : conj b*b=1 := by
    rw [←Complex.normSq_eq_conj_mul_self,Complex.normSq_eq_norm_sq,hb]
    norm_num
  simp only [exteriorTriple, Nat.cast_one]
  rw [hf,hg,hh]
  simp only [Nat.cast_one]
  change (b*f.val S)*(b*g.val S)*conj (b*h.val S) = _
  calc
    _ = (conj b*b)*(b*(f.val S*g.val S*conj (h.val S))) := by
      rw [map_mul]
      ring
    _ = _ := by rw [hc,one_mul]


open MeasureTheory TorusLean.Fermion.CanonicalPlaneJets
open TorusLean.Fermion.PlaneMagneticUnitary

/-- True cell L1 for the exterior coefficient times one original internal
periodized edge. All three exterior orbitals remain periodized. -/
theorem exteriorTriple_jet_cross_integrable (G : Geometry) (theta : Twist)
    (f g h : RawLLL G theta 1) (j : ℕ) (R : ℂ) :
    Integrable (fun S => conj (rawJetFunction G.M G.omega1 G.omega2
      theta.theta1 theta.theta2 j R S) * exteriorTriple G theta f g h S)
      (cellMeasure G 1) := by
  have hi := magneticPeriodization_cross_integrable_cell G theta
    (exteriorTriple G theta f g h) (exteriorTriple_continuous G theta f g h)
    (exteriorTriple_boundary G theta f g h) (translatedPlaneJet j R)
    (TorusLean.Shared.MagneticCellUnfolding.translatedPlaneJet_integrable j R)
  have hic := Complex.conjCLE.toContinuousLinearMap.integrable_comp hi
  change Integrable (fun S => conj (conj (exteriorTriple G theta f g h S) * magneticPeriodization G.M 1 G.omega1 G.omega2 theta.theta1 theta.theta2 (translatedPlaneJet j R) S)) (cellMeasure G 1) at hic
  simpa only [Function.comp_apply, Complex.conjCLE_apply, rawJetFunction,
    map_mul,Complex.conj_conj,mul_comm] using hic

/-- The one-edge unfolding is an actual absolutely integrable plane integral,
with the exterior triple unchanged. This is not a planar replacement of the
three-body interaction or of the exterior magnetic sections. -/
theorem exteriorTriple_jet_unfold (G : Geometry) (theta : Twist)
    (f g h : RawLLL G theta 1) (j : ℕ) (R : ℂ) :
    (∫ S, conj (rawJetFunction G.M G.omega1 G.omega2 theta.theta1 theta.theta2 j R S) *
      exteriorTriple G theta f g h S ∂cellMeasure G 1) =
    ∫ S, conj (translatedPlaneJet j R S) * exteriorTriple G theta f g h S ∂planeMeasure := by
  have he := cellInner_magneticPeriodization_eq_planeInner G theta
    (exteriorTriple G theta f g h) (exteriorTriple_continuous G theta f g h)
    (exteriorTriple_boundary G theta f g h) (translatedPlaneJet j R)
    (TorusLean.Shared.MagneticCellUnfolding.translatedPlaneJet_integrable j R)
  have hc := congrArg (starRingEnd ℂ) he
  simp only [cellInner,planeInner,←integral_conj,map_mul,Complex.conj_conj] at hc
  simpa only [rawJetFunction,mul_comm] using hc

open TorusLean.Shared.PlaneJetMembership TorusLean.Shared.PlaneJetReproducing

/-- The actual full-cell raw ground-jet Gram is the conjugated kernel edge,
with its original magnetic phase, rather than only its absolute value. -/
theorem groundJetGram_eq_conj_kernel (G : Geometry) (theta : Twist) (R S : ℂ) :
    inner ℂ (rawPlaneJet G theta 0 R) (rawPlaneJet G theta 0 S) =
      conj (rawJetFunction G.M G.omega1 G.omega2 theta.theta1 theta.theta2 0 R S) := by
  rw [←inner_conj_symm,rawPlaneJet_inner_reproduces,rawJetCoefficient_zero]
  rfl

theorem groundJetGram_exterior_unfold (G : Geometry) (theta : Twist)
    (f g h : RawLLL G theta 1) (R : ℂ) :
    (∫ S, inner ℂ (rawPlaneJet G theta 0 R) (rawPlaneJet G theta 0 S) *
      exteriorTriple G theta f g h S ∂cellMeasure G 1) =
      ∫ S, conj (translatedPlaneJet 0 R S) * exteriorTriple G theta f g h S ∂planeMeasure := by
  simp_rw [groundJetGram_eq_conj_kernel]
  exact exteriorTriple_jet_unfold G theta f g h 0 R

end TorusLean.Shared.PhysicalBosonOneEdgeBoundary
