import torus.shared.BosonThermalJacobiFourTransfer

/-! The complete triangular relative-source cutoff is controlled by the
original two-spectator heat form. The sharper minimum heat weight retains
r1 once and r2^(D+1); at D=16, a=1/16 this gives the paper's exact 272*(9/8)^17.
Identification of this source-rank cutoff with the actual planar H4 cutoff
remains a separate operator identity. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.ThermalCoherentJacobiFourCutoff
open TorusLean.Boson
open TorusLean.Fermion.PlaneMagneticUnitary TorusLean.Fermion.LatticePacking
open TorusLean.Shared.PhysicalBosonMembership TorusLean.Shared.PhysicalNBodyCarrier
open TorusLean.Shared.PhysicalBosonSector TorusLean.Shared.PhysicalBosonS4
open TorusLean.Shared.PhysicalBosonContactForm TorusLean.Shared.PhysicalBosonLinearEquiv
open TorusLean.Shared.BosonThermalJacobiFourRows
open TorusLean.Shared.BosonThermalJacobiFourTransfer
open TorusLean.Shared.ThermalCoherentDoubleIntegral TorusLean.Shared.BosonSystole20Scalar
open scoped BigOperators

/-- All ordered relative indices of total degree at most D. Odd first indices
are retained; their images vanish by a separate proved symmetry theorem. -/
def fourRelativeTriangle (D : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range (D+1)).product (Finset.range (D+1))).filter (fun de => de.1+de.2≤D)

def fourRelativeCutoffForm (G : Geometry) (theta : Twist) (D : ℕ)
    (p : Core (OrbitalIndex G theta) ℂ) : ℝ :=
  ∑ de ∈ fourRelativeTriangle D, w4RelativeForm G theta de.1 de.2 p

theorem four_relative_heat_weight_lower (a : ℝ) (ha : 0<a) (D d e : ℕ)
    (hde : d+e≤D) :
    (1/(1+a))*(1/(1+2*a))^(D+1) ≤ (1/(1+a))^(d+1)*(1/(1+2*a))^(e+1) := by
  have h10 : (0:ℝ)≤1/(1+a) := by positivity
  have h20 : (0:ℝ)≤1/(1+2*a) := by positivity
  have h21 : (1:ℝ)/(1+2*a)≤1 := (div_le_one (by positivity)).2 (by linarith)
  have hcompare : (1:ℝ)/(1+2*a)≤1/(1+a) :=
    (div_le_div_iff₀ (by positivity) (by positivity)).2 (by nlinarith)
  calc
    _ ≤ (1/(1+a))*(1/(1+2*a))^(d+e+1) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one h20 h21 (by omega)) h10
    _ = (1/(1+a))*((1/(1+2*a))^d*(1/(1+2*a))^(e+1)) := by
      rw [←pow_add,Nat.add_assoc]
    _ ≤ (1/(1+a))*((1/(1+a))^d*(1/(1+2*a))^(e+1)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ h20 hcompare d) (pow_nonneg h20 _)) h10
    _ = _ := by rw [pow_succ]; ring

/-- True complete triangular cutoff, controlled by the independently defined
full heat integral via its already proved positive HasSum. -/
theorem four_relative_cutoff_weighted_bound (G : Geometry) (theta : Twist) (a : ℝ)
    (ha : 0<a) (D : ℕ) (p : Core (OrbitalIndex G theta) ℂ) (hL : 20≤systole G) :
    (1/(1+a))*(1/(1+2*a))^(D+1) * fourRelativeCutoffForm G theta D p ≤
      twoSpectatorForm G theta a p := by
  calc
    _ ≤ ∑ de ∈ fourRelativeTriangle D,
        (1/(1+a))^(de.1+1)*(1/(1+2*a))^(de.2+1)*w4RelativeForm G theta de.1 de.2 p := by
      rw [fourRelativeCutoffForm,Finset.mul_sum]
      apply Finset.sum_le_sum
      intro de hde
      exact mul_le_mul_of_nonneg_right
        (four_relative_heat_weight_lower a ha D de.1 de.2 (Finset.mem_filter.mp hde).2)
        (w4RelativeForm_nonneg G theta de.1 de.2 p)
    _ ≤ _ := sum_le_hasSum (fourRelativeTriangle D)
      (fun de _ => by
        have hq := w4RelativeForm_nonneg G theta de.1 de.2 p
        positivity)
      (twoSpectatorForm_relative_hasSum G theta a ha p hL)

theorem actual_four_relative_cutoff_weighted_bound (G : Geometry) (theta : Twist) (a : ℝ)
    (ha : 0<a) (D N : ℕ) (f : PhysicalBosonCarrier G theta ((N+2)+2))
    (hL : 20≤systole G) :
    (1/(1+a))*(1/(1+2*a))^(D+1) * fourRelativeCutoffForm G theta D
      ((physicalSectorEquiv G theta ((N+2)+2)).symm f).val ≤
      (sAllowance^2/a^2) * (2*cAllowance*actualPositiveFourBodyForm G theta N f +
        actualParticleContactEnergy G ((N+2)+2) f.val) :=
  (four_relative_cutoff_weighted_bound G theta a ha D _ hL).trans
    (actualTwoSpectatorForm_bound G theta a ha N f hL)

/-- Exact paper coefficient on the complete degree-16 triangular relative
source cutoff. It pays against the same actual H and S4 with no N factor. -/
theorem actual_four_relative_cutoff_sixteen_bound (G : Geometry) (theta : Twist)
    (N : ℕ) (f : PhysicalBosonCarrier G theta ((N+2)+2)) (hL : 20≤systole G) :
    fourRelativeCutoffForm G theta 16 ((physicalSectorEquiv G theta ((N+2)+2)).symm f).val ≤
      (272*(9/8:ℝ)^17)*sAllowance^2 *
        (2*cAllowance*actualPositiveFourBodyForm G theta N f +
          actualParticleContactEnergy G ((N+2)+2) f.val) := by
  have h := actual_four_relative_cutoff_weighted_bound G theta (1/16) (by norm_num) 16 N f hL
  apply (mul_le_mul_iff_right₀ (by norm_num : (0:ℝ)<(1/(1+1/16))*(1/(1+2*(1/16)))^(16+1))).mp
  calc
    _ ≤ _ := h
    _ = _ := by norm_num <;> ring

end TorusLean.Shared.ThermalCoherentJacobiFourCutoff
