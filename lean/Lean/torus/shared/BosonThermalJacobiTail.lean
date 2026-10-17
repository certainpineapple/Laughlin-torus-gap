import torus.shared.BosonThermalJacobiTransfer

set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.BosonThermalJacobiTail
open TorusLean.Boson
open TorusLean.Fermion.PlaneMagneticUnitary TorusLean.Fermion.LatticePacking
open TorusLean.Shared.PhysicalBosonMembership TorusLean.Shared.PhysicalNBodyCarrier
open TorusLean.Shared.PhysicalBosonSector TorusLean.Shared.PhysicalBosonS4
open TorusLean.Shared.PhysicalBosonContactForm TorusLean.Shared.PhysicalBosonLinearEquiv
open TorusLean.Shared.BosonThermalJacobiRows TorusLean.Shared.BosonThermalJacobiTransfer
open TorusLean.Shared.ThermalCoherentIntegral TorusLean.Shared.BosonSystole20Scalar

/-- The independently specified odd high-degree relative rank-form tail.
Identification with a Hamiltonian negative part is a separate obligation. -/
def oddRelativeTailTerm (G : Geometry) (theta : Twist)
    (p : Core (OrbitalIndex G theta) ℂ) (d : ℕ) : ℝ :=
  if Odd d ∧ 9≤d then 2*(1/2:ℝ)^d*w3RelativeForm G theta d p else 0

theorem oddRelativeTailTerm_le (G : Geometry) (theta : Twist)
    (p : Core (OrbitalIndex G theta) ℂ) (d : ℕ) :
    oddRelativeTailTerm G theta p d ≤
      ((20/9:ℝ)*(5/9:ℝ)^9) * ((9/10:ℝ)^(d+1)*w3RelativeForm G theta d p) := by
  have hQ := w3RelativeForm_nonneg G theta d p
  by_cases h : Odd d ∧ 9≤d
  · rw [oddRelativeTailTerm,ite_eq_left h]
    have he : (2:ℝ)*(1/2:ℝ)^d = (20/9:ℝ)*(5/9:ℝ)^d*(9/10:ℝ)^(d+1) := by
      rw [pow_succ]
      calc
        _ = 2*((5/9:ℝ)*(9/10:ℝ))^d := by norm_num
        _ = _ := by rw [mul_pow]; ring
    rw [he]
    have hp := pow_le_pow_of_le_one (by norm_num : (0:ℝ)≤5/9)
      (by norm_num : (5/9:ℝ)≤1) h.2
    have hh := mul_le_mul_of_nonneg_right hp
      (show 0≤(20/9:ℝ)*(9/10:ℝ)^(d+1)*w3RelativeForm G theta d p from
        mul_nonneg (by positivity) hQ)
    nlinarith
  · rw [oddRelativeTailTerm,ite_eq_right h]
    exact mul_nonneg (by positivity) (mul_nonneg (by positivity) hQ)

theorem oddRelativeTail_bound (G : Geometry) (theta : Twist)
    (p : Core (OrbitalIndex G theta) ℂ) (hL : 20≤systole G) :
    Summable (oddRelativeTailTerm G theta p) ∧
      (∑' d, oddRelativeTailTerm G theta p d) ≤
        ((20/9:ℝ)*(5/9:ℝ)^9) * oneSpectatorForm G theta (2/27) p := by
  have hs := oneSpectatorForm_relative_hasSum G theta (2/27) (by norm_num) p hL
  have hr : (2:ℝ)/(2+3*(2/27:ℝ))=9/10 := by norm_num
  rw [hr] at hs
  have hk := hs.mul_left ((20/9:ℝ)*(5/9:ℝ)^9)
  have ht0 (d : ℕ) : 0≤oddRelativeTailTerm G theta p d := by
    unfold oddRelativeTailTerm
    split_ifs
    · exact mul_nonneg (by positivity) (w3RelativeForm_nonneg G theta d p)
    · exact le_rfl
  have ht : Summable (oddRelativeTailTerm G theta p) :=
    Summable.of_nonneg_of_le ht0 (oddRelativeTailTerm_le G theta p) hk.summable
  exact ⟨ht, hasSum_le (oddRelativeTailTerm_le G theta p) ht.hasSum hk⟩

theorem actual_oddRelativeTail_bound (G : Geometry) (theta : Twist) (N : ℕ)
    (f : PhysicalBosonCarrier G theta ((N+2)+2)) (hL : 20≤systole G) :
    (∑' d, oddRelativeTailTerm G theta
      ((physicalSectorEquiv G theta ((N+2)+2)).symm f).val d) ≤
      (30*(5/9:ℝ)^9)*sAllowance *
        (cAllowance * actualPositiveFourBodyForm G theta N f +
          actualParticleContactEnergy G ((N+2)+2) f.val) := by
  have h := (oddRelativeTail_bound G theta ((physicalSectorEquiv G theta ((N+2)+2)).symm f).val hL).2
  have he := actualOneSpectatorForm_bound G theta (2/27) (by norm_num) N f hL
  have hh := mul_le_mul_of_nonneg_left he (show 0≤(20/9:ℝ)*(5/9:ℝ)^9 by positivity)
  refine h.trans (hh.trans_eq ?_)
  ring

end TorusLean.Shared.BosonThermalJacobiTail
