import torus.shared.ThermalCoherentAllCorePayments
import torus.shared.PhysicalBosonSingleAnchoredAllN
import torus.shared.BosonNatThreeSourceEnergyPayment

/-! The original three-body source payment on every particle-homogeneous
finite core. M=3 uses the genuine nonzero S3 theorem; only M<3 uses true
triple annihilator vanishing. The completed physical carrier is obtained by
its existing full-sector equivalence, with no new carrier or norm payment. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.ThermalCoherentAllCoreM3Payment
open MeasureTheory TorusLean.Boson TorusLean.Boson.SpectatorControl
open TorusLean.Boson.PhysicalContactLiftCandidate (contactCoreHamiltonian)
open TorusLean.Shared.PhysicalBosonSector TorusLean.Shared.PhysicalBosonS4Coefficients
open TorusLean.Shared.ThermalCoherentAllCorePayments
open TorusLean.Shared.PhysicalBosonSingleAnchoredAllN
open TorusLean.Shared.PhysicalBosonSingleTailPayment TorusLean.Shared.BosonThermalJacobiTail
open TorusLean.Shared.BosonThermalJacobiRows TorusLean.Shared.ThermalCoherentJacobiInsertion
open TorusLean.Shared.BosonNatThreeSourceEnergyComparison
open TorusLean.Shared.BosonSystole20Scalar TorusLean.Fermion.LatticePacking
open scoped BigOperators
local instance allM3Payment_nonempty (G : Geometry) (theta : Twist) :
    Nonempty (OrbitalIndex G theta) := ⟨⟨0,lll_finrank_pos G theta 1⟩⟩

private theorem relative_form_low (G : Geometry) (theta : Twist) (M : ℕ) (hM : M<3)
    (p : Core (OrbitalIndex G theta) ℂ) (hp : p.IsHomogeneous M) (d : ℕ) :
    w3RelativeForm G theta d p=0 := by
  unfold w3RelativeForm
  simp only [natThreeRemoval_low_sector G theta _ _ _ _ M hM p hp]
  simp [q,occupationMetricNormSq]

private theorem original_low_minus_tail_allM (G : Geometry) (theta : Twist)
    (hG : 20≤systole G) (M : ℕ) (p : Core (OrbitalIndex G theta) ℂ)
    (hp : p.IsHomogeneous M) :
    (∑ d ∈ Finset.range 9, 2*(-1/2:ℝ)^d*w3RelativeForm G theta d p) -
      (∑' d, oddRelativeTailTerm G theta p d) ≤ originalSingleForm G theta p := by
  by_cases hM : M<3
  · have hq := relative_form_low G theta M hM p hp
    have ht (d : ℕ) : oddRelativeTailTerm G theta p d=0 := by
      simp [oddRelativeTailTerm,hq]
    have hz := original_singleContraction_low_sector G theta M hM p hp
    simp only [hq,mul_zero,Finset.sum_const_zero,ht,tsum_zero,sub_zero,
      originalSingleForm,hz,ip,occupationInner_zero_right,Complex.zero_re,le_refl]
  · have he : (M-3)+3=M := Nat.sub_add_cancel (by omega)
    exact originalSingleForm_low_minus_tail G theta hG (M-3) p (by simpa only [he] using hp)

/-- Unchanged low relative energy paid by the true original S3 and the same
normalS4/coreH on all homogeneous particle sectors, including M=3. -/
theorem lowRelativeEnergyForm_allM_bound (G : Geometry) (theta : Twist) (M : ℕ)
    (p : Core (OrbitalIndex G theta) ℂ) (hp : p.IsHomogeneous M) (hG : 20≤systole G) :
    lowRelativeEnergyForm G theta p ≤ originalSingleForm G theta p +
      sAllowance*(c9+TorusLean.Shared.BosonSystole20Scalar.delta*c3)*
        (cAllowance*(normalOrderedFourBodyForm G theta p).re+
          (ip p (contactCoreHamiltonian G theta p)).re) := by
  let B : ℝ := cAllowance*(normalOrderedFourBodyForm G theta p).re+
    (ip p (contactCoreHamiltonian G theta p)).re
  let L : ℝ := ∑ d ∈ Finset.range 9, 2*(-1/2:ℝ)^d*w3RelativeForm G theta d p
  let Q : ℝ := ∑ d ∈ Finset.range 9, w3RelativeForm G theta d p
  change lowRelativeEnergyForm G theta p ≤ originalSingleForm G theta p +
    sAllowance*(c9+TorusLean.Shared.BosonSystole20Scalar.delta*c3)*B
  have hcut : Q≤c3*sAllowance*B := relative_cutoff_eight_allCore G theta p hG
  have hdelta : 0≤(TorusLean.BosonFiniteCertificate.delta:ℝ) := by
    norm_num [TorusLean.BosonFiniteCertificate.delta]
  have hpaid := mul_le_mul_of_nonneg_left hcut hdelta
  have htail := original_low_minus_tail_allM G theta hG M p hp
  have htail_bound := oddRelativeTail_allCore G theta p hG
  have hlow : L≤originalSingleForm G theta p+c9*sAllowance*B := by
    dsimp [L,B]
    linarith only [htail,htail_bound]
  have he : lowRelativeEnergyForm G theta p =
      L+(TorusLean.BosonFiniteCertificate.delta:ℝ)*Q := by
    simp only [lowRelativeEnergyForm,L,Q,add_mul,Finset.sum_add_distrib,Finset.mul_sum]
  rw [he]
  calc
    _ ≤ L+(TorusLean.BosonFiniteCertificate.delta:ℝ)*(c3*sAllowance*B) :=
      by linarith only [hpaid]
    _ ≤ (originalSingleForm G theta p+c9*sAllowance*B)+
        (TorusLean.BosonFiniteCertificate.delta:ℝ)*(c3*sAllowance*B) :=
      by linarith only [hlow]
    _ = _ := by
      have hd : (TorusLean.BosonFiniteCertificate.delta:ℝ)=
          TorusLean.Shared.BosonSystole20Scalar.delta := by
        norm_num [TorusLean.BosonFiniteCertificate.delta,TorusLean.Shared.BosonSystole20Scalar.delta]
      rw [hd]
      ring

/-- The actual original nine-block source form uses the same all-M payment;
its full-L3/source identities and positive certificate remain unchanged. -/
theorem originalM3SourceCellForm_allM_bound (G : Geometry) (theta : Twist) (M : ℕ)
    (p : Core (OrbitalIndex G theta) ℂ) (hp : p.IsHomogeneous M) (hG : 20≤systole G) :
    originalM3SourceCellForm G theta p ≤ originalSingleForm G theta p +
      sAllowance*(c9+TorusLean.Shared.BosonSystole20Scalar.delta*c3)*
        (cAllowance*(normalOrderedFourBodyForm G theta p).re+
          (ip p (contactCoreHamiltonian G theta p)).re) :=
  (originalM3SourceCellForm_le_low_energy G theta p).trans
    (lowRelativeEnergyForm_allM_bound G theta M p hp hG)

end TorusLean.Shared.ThermalCoherentAllCoreM3Payment
