import torus.shared.ThermalCoherentBosonRowEnvelope
import torus.shared.BosonThermalJacobiCutoff

/-! The complete auxiliary triangular trace. All pair/spectator states are
counted once; COM integration yields their actual degree multiplicities.
The systole-twenty payment uses the already proved positive thermal form. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.ThermalCoherentBosonRowEnvelope
open MeasureTheory TorusLean.Boson TorusLean.Boson.SpectatorControl
open TorusLean.Shared.PhysicalBosonSector TorusLean.Shared.BosonRelativeFrame
open TorusLean.Shared.BosonThermalJacobiRows TorusLean.Shared.BosonThermalJacobiCutoff
open TorusLean.Shared.PhysicalBosonMembership TorusLean.Shared.PhysicalNBodyCarrier
open TorusLean.Shared.PhysicalBosonLinearEquiv TorusLean.Shared.PhysicalBosonS4
open TorusLean.Shared.PhysicalBosonContactForm TorusLean.Shared.BosonSystole20Scalar
open TorusLean.Fermion.LatticePacking
open scoped BigOperators

/-- Genuine positive envelope for every p+j≤D, in complete total-degree order. -/
def auxiliaryEnvelope (G : Geometry) (theta : Twist) (D : ℕ)
    (f : Core (OrbitalIndex G theta) ℂ) (R : ℂ) : ℝ :=
  ∑ t ∈ Finset.range (D+1), ∑ p : Fin (t+1),
    q (singleJetAnnihilator G theta (t-p.val) R (pairDescendant G theta p.val R f))

private theorem triangle_count (D : ℕ) (F : ℕ → ℝ) :
    (∑ t ∈ Finset.range (D+1), ∑ d ∈ Finset.range (t+1), F d) =
    ∑ d ∈ Finset.range (D+1), ((D+1-d:ℕ):ℝ)*F d := by
  induction D with
  | zero => simp
  | succ D ih =>
    rw [Finset.sum_range_succ,ih]
    rw [Finset.sum_range_succ (f := fun d => ((D+1+1-d:ℕ):ℝ)*F d)]
    rw [Finset.sum_range_succ (f := F)]
    simp only [Nat.add_sub_cancel_left,Nat.cast_one,one_mul]
    rw [←add_assoc,←Finset.sum_add_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro d hd
    have hd' := Finset.mem_range.mp hd
    rw [show D+1+1-d=(D+1-d)+1 by omega,Nat.cast_add,Nat.cast_one]
    ring

/-- Actual L1 of the full auxiliary envelope before its cell integral. -/
theorem auxiliaryEnvelope_integrable (G : Geometry) (theta : Twist) (D : ℕ)
    (f : Core (OrbitalIndex G theta) ℂ) :
    Integrable (auxiliaryEnvelope G theta D f) (cellMeasure G 2) :=
  integrable_finsetSum _ (fun t _ => auxiliary_degree_integrable G theta t f)

/-- Exact multiplicity (D+1-d), with the original COM factor 2/3. -/
theorem auxiliaryEnvelope_integral (G : Geometry) (theta : Twist) (D : ℕ)
    (f : Core (OrbitalIndex G theta) ℂ) :
    (∫ R, auxiliaryEnvelope G theta D f R ∂cellMeasure G 2) =
      (2/3:ℝ)*∑ d ∈ Finset.range (D+1), ((D+1-d:ℕ):ℝ)*w3RelativeForm G theta d f := by
  unfold auxiliaryEnvelope
  rw [integral_finsetSum _ (fun t _ => auxiliary_degree_integrable G theta t f)]
  simp only [auxiliary_degree_integral]
  have hreflect (t : ℕ) :
      (∑ n : Fin (t+1), w3RelativeForm G theta (t-n.val) f) =
      ∑ d ∈ Finset.range (t+1), w3RelativeForm G theta d f := by
    rw [Fin.sum_univ_eq_sum_range (fun n => w3RelativeForm G theta (t-n) f) (t+1)]
    simpa only [Nat.add_sub_cancel] using
      Finset.sum_range_reflect (fun d => w3RelativeForm G theta d f) (t+1)
  simp_rw [hreflect]
  rw [←Finset.mul_sum,triangle_count]

/-- All 45 columns are paid with six times the degree-eight relative cutoff. -/
theorem auxiliaryEnvelope_eight_bound (G : Geometry) (theta : Twist)
    (f : Core (OrbitalIndex G theta) ℂ) :
    (∫ R, auxiliaryEnvelope G theta 8 f R ∂cellMeasure G 2) ≤
      6*∑ d ∈ Finset.range 9, w3RelativeForm G theta d f := by
  rw [auxiliaryEnvelope_integral]
  norm_num only
  calc
    _ ≤ (2/3:ℝ)*∑ d ∈ Finset.range 9, 9*w3RelativeForm G theta d f := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Finset.sum_le_sum
      intro d hd
      apply mul_le_mul_of_nonneg_right _ (w3RelativeForm_nonneg G theta d f)
      exact_mod_cast Nat.sub_le 9 d
    _ = _ := by rw [←Finset.mul_sum]; ring

/-- The original physical carrier pays the complete 45-column envelope. -/
theorem actual_auxiliaryEnvelope_bound (G : Geometry) (theta : Twist) (N : ℕ)
    (f : PhysicalBosonCarrier G theta ((N+2)+2)) (hG : 20≤systole G) :
    (∫ R, auxiliaryEnvelope G theta 8
      ((physicalSectorEquiv G theta ((N+2)+2)).symm f).val R ∂cellMeasure G 2) ≤
      (72*(9/8:ℝ)^9*sAllowance) *
        (cAllowance*actualPositiveFourBodyForm G theta N f+
          actualParticleContactEnergy G ((N+2)+2) f.val) := by
  have h := actual_relative_cutoff_bound G theta (1/12) (by norm_num) 8 N f hG
  norm_num only at h
  have hp : (0:ℝ)<(8/9)^9 := by positivity
  have hb := auxiliaryEnvelope_eight_bound G theta
    ((physicalSectorEquiv G theta ((N+2)+2)).symm f).val
  apply hb.trans
  have he := mul_le_mul_of_nonneg_left h (by positivity : (0:ℝ)≤6*(9/8)^9)
  norm_num at he ⊢
  nlinarith [he]

end TorusLean.Shared.ThermalCoherentBosonRowEnvelope
