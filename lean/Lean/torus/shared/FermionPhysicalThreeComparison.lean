import torus.shared.FermionCertificateThreeIntegral
import torus.shared.FermionCertificateThreeCertificate
import torus.shared.ThermalCoherentFermionAnchoredJacobiSpectrum
import torus.shared.ThermalCoherentFermionAnchoredJacobiPauli
import torus.shared.PhysicalFermionHighTailLimit

/-! Actual original K3/S3 comparison. The finite thirteen exact comparisons
consume the full seven-row physical identity; genuine exterior Pauli zeros
handle degrees 0,1,3. All remaining negative odd degrees use the actual same-H
tail. No target payment, source identity, or particle-dependent bound is a premise. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.FermionLocalJet.ThreeCoupling
open MeasureTheory TorusLean.Geometry TorusLean.Fermion OAI.Laughlin.Fock
open TorusLean.Shared.PhysicalFermionCAR TorusLean.Shared.PhysicalFermionNormalSquare
open TorusLean.Shared.PhysicalFermionHighTail
open TorusLean.Shared.ThermalCoherentFermionAnchored
open TorusLean.Shared.ThermalCoherentFermionAnchoredJacobiRemoval
open TorusLean.Shared.ThermalCoherentFermionAnchoredJacobiFiniteCell
open TorusLean.Shared.ThermalCoherentFermionAnchoredJacobiAbsolute
open TorusLean.Shared.ThermalCoherentFermionAnchoredJacobiSpectrum
open TorusLean.Fermion.LatticePacking TorusLean.Fermion.UniformTail
open scoped BigOperators ComplexConjugate

/-- Integrated actual relative matrix diagonal, including its signed q_z. -/
def weightedRelativeIntegral (G : Geometry) (theta : Twist)
    (x : Space (physicalQ G theta)) (z : ℕ) : ℝ :=
  q z*(∫ R, relativeEnergy G theta x z R ∂cellMeasure G 3)

theorem relativeEnergy_pauli_zero (G : Geometry) (theta : Twist)
    (x : Space (physicalQ G theta)) (z : ℕ) (hz : z=0 ∨ z=1 ∨ z=3) (R : ℂ) :
    relativeEnergy G theta x z R=0 := by
  have hf : formalRelativeSeed z=0 := by
    rcases hz with rfl|rfl|rfl
    · exact formalRelativeSeed_zero
    · exact formalRelativeSeed_one
    · exact formalRelativeSeed_three
  unfold relativeEnergy
  rw [← formalRemoval_relative_eq_paper,hf,formalRemoval_zero]
  simp only [occupationNormSq,map_zero,Finsupp.zero_apply,norm_zero,zero_pow (by decide : 2≠0),
    Finset.sum_const_zero]

/-- The 13 exact inequalities apply to genuine nonzero-degree sources;
vanishing degrees use their exterior zero theorem, not a scalar surrogate. -/
theorem finite_three_comparison (G : Geometry) (theta : Twist)
    (x : Space (physicalQ G theta)) :
    certificateThreeZeroEnergy G theta x≤
      ∑ z ∈ Finset.range 16, weightedRelativeIntegral G theta x z := by
  rw [certificateThreeZeroEnergy_mu3_sum,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro z hz
  have hI : 0≤∫ R, relativeEnergy G theta x z R ∂cellMeasure G 3 :=
    integral_nonneg (relativeEnergy_nonneg G theta x z)
  by_cases hp : z=0 ∨ z=1 ∨ z=3
  · simp only [relativeEnergy_pauli_zero G theta x z hp,integral_zero,
      weightedRelativeIntegral,mul_zero,le_refl]
  · have hc : z∈comparisonDegrees := by
      have hz' := Finset.mem_range.mp hz
      simp only [comparisonDegrees,Finset.mem_insert,Finset.mem_singleton]
      omega
    have he := threeEigenvalue_strict z hc
    have hq : (2/3:ℝ)*threeEigenvalue z≤q z := by
      unfold q
      nlinarith
    exact (by simpa only [weightedRelativeIntegral,mul_assoc] using
      mul_le_mul_of_nonneg_right hq hI)

/-- Actual S3 HasSum, with physical integrated energies. -/
theorem physical_three_relative_hasSum (G : Geometry) (theta : Twist)
    (hG : 1≤systole G) (x : Space (physicalQ G theta)) :
    HasSum (weightedRelativeIntegral G theta x)
      (occupationInner (physicalQ G theta) x
        (matrixSingleContraction (physicalQ G theta) (contactMatrix G theta) x)).re := by
  have hs := (physicalCOM_relative_hasSum G theta hG x x).summable
  have hh : HasSum (fun d => (q d:ℂ)*relativeCrossIntegral G theta x x d)
      (occupationInner (physicalQ G theta) x
        (matrixSingleContraction (physicalQ G theta) (contactMatrix G theta) x)) := by
    rw [matrixSingleContraction_relative_tsum G theta hG x x]
    exact hs.hasSum
  unfold weightedRelativeIntegral
  simpa only [relativeCrossIntegral_self,integral_complex_ofReal,← Complex.ofReal_mul,
    Complex.ofReal_re] using Complex.hasSum_re hh

/-- The absolute physical L1 series is retained for literal odd-tail exchange. -/
theorem relativeEnergy_weighted_absolute (G : Geometry) (theta : Twist)
    (hG : 1≤systole G) (x : Space (physicalQ G theta)) :
    Summable (fun d => ∫ R, ‖q d*relativeEnergy G theta x d R‖ ∂cellMeasure G 3) := by
  have hs := original_relative_series_summable_integral_norm G theta hG x x
  simpa only [relativeRemovalCross,formalRemoval_relative_eq_paper,occupationInner_self,
    ← Complex.ofReal_mul,Complex.norm_real,relativeEnergy] using hs

/-- The infinite original negative odd tail equals its integrated source series. -/
theorem negative_tail_eq_integrated_series (G : Geometry) (theta : Twist)
    (hG : 1≤systole G) (x : Space (physicalQ G theta)) :
    negativeRelativeTailEnergy G theta x=
      ∑' m, weightedRelativeIntegral G theta x (degree m) := by
  have hs := (relativeEnergy_weighted_absolute G theta hG x).comp_injective degree_injective
  have hi (m : ℕ) : Integrable (fun R => q (degree m)*relativeEnergy G theta x (degree m) R)
      (cellMeasure G 3) := (relativeEnergy_integrable G theta x (degree m) 3).const_mul _
  have hh := hasSum_integral_of_summable_integral_norm hi hs
  simp only [integral_const_mul] at hh
  rw [negativeRelativeTailEnergy_original_mu3]
  exact hh.tsum_eq.symm

private theorem weighted_even_tail_nonneg (G : Geometry) (theta : Twist)
    (x : Space (physicalQ G theta)) (m : ℕ) :
    0≤weightedRelativeIntegral G theta x (2*m+16) := by
  have hI : 0≤∫ R, relativeEnergy G theta x (2*m+16) R ∂cellMeasure G 3 :=
    integral_nonneg (relativeEnergy_nonneg G theta x (2*m+16))
  unfold weightedRelativeIntegral q
  apply mul_nonneg _ hI
  apply mul_nonneg
  · push_cast
    nlinarith only [Nat.cast_nonneg (α := ℝ) m]
  · rw [show 2*m+16=2*(m+8) by omega,pow_mul]
    positivity

/-- Finite prefix plus the full negative odd tail is below the original S3.
The even tail is nonnegative only after using the actual physical norm square. -/
theorem physical_three_prefix_tail_lower (G : Geometry) (theta : Twist)
    (hG : 1≤systole G) (x : Space (physicalQ G theta)) :
    (∑ z ∈ Finset.range 16, weightedRelativeIntegral G theta x z)+
        negativeRelativeTailEnergy G theta x≤
      (occupationInner (physicalQ G theta) x
        (matrixSingleContraction (physicalQ G theta) (contactMatrix G theta) x)).re := by
  let F : ℕ → ℝ := weightedRelativeIntegral G theta x
  have hs : HasSum F (occupationInner (physicalQ G theta) x
      (matrixSingleContraction (physicalQ G theta) (contactMatrix G theta) x)).re :=
    physical_three_relative_hasSum G theta hG x
  have ht : Summable (fun n : ℕ => F (n+16)) :=
    (summable_nat_add_iff (f := F) 16).mpr hs.summable
  have he : Summable (fun m : ℕ => F (2*m+16)) := ht.comp_injective (by
    intro a b h
    change 2*a=2*b at h
    omega)
  have ho : Summable (fun m : ℕ => F (2*m+1+16)) := ht.comp_injective (by
    intro a b h
    change 2*a+1=2*b+1 at h
    omega)
  have hsplit : (∑' m : ℕ, F (2*m+16))+(∑' m : ℕ, F (2*m+1+16))=
      ∑' n : ℕ, F (n+16) := tsum_even_add_odd (f := fun n : ℕ => F (n+16)) he ho
  have hfull : (∑ z ∈ Finset.range 16,F z)+(∑' n : ℕ,F (n+16))=∑' z,F z :=
    hs.summable.sum_add_tsum_nat_add 16
  have hdegree : (fun m : ℕ => F (2*m+1+16))=(fun m : ℕ => F (degree m)) := by
    funext m
    exact congrArg F (by unfold degree; omega)
  rw [hdegree] at hsplit
  have hp : 0≤∑' m : ℕ, F (2*m+16) := tsum_nonneg (weighted_even_tail_nonneg G theta x)
  have htail : (∑' m : ℕ,F (degree m))≤∑' n : ℕ,F (n+16) := by
    rw [← hsplit]
    exact le_add_of_nonneg_left hp
  rw [negative_tail_eq_integrated_series G theta hG x,← hs.tsum_eq]
  change (∑ z ∈ Finset.range 16,F z)+(∑' m,F (degree m))≤∑' z,F z
  exact (add_le_add (le_refl (∑ z ∈ Finset.range 16,F z)) htail).trans_eq hfull

/-- Uniform true whole-Fock comparison, with the same actual H and no N loss.
L is chosen before geometry, twist and the input vector. -/
theorem physical_three_comparison_uniform (eps : ℝ) (heps : 0<eps) :
    ∃ L : ℝ, 1≤L ∧ ∀ (G : Geometry) (theta : Twist), L≤systole G →
      ∀ x : Space (physicalQ G theta),
        certificateThreeZeroEnergy G theta x-
          (occupationInner (physicalQ G theta) x
            (matrixSingleContraction (physicalQ G theta) (contactMatrix G theta) x)).re-
          (61/4096:ℝ)*(occupationInner (physicalQ G theta) x (physicalHamiltonian G theta x)).re≤
            eps*(occupationInner (physicalQ G theta) x (physicalHamiltonian G theta x)).re := by
  obtain ⟨L,hL1,hL⟩ := physical_negative_tail_uniform eps heps
  refine ⟨L,hL1,?_⟩
  intro G theta hG x
  have hs := physical_three_prefix_tail_lower G theta (hL1.trans hG) x
  have hf := finite_three_comparison G theta x
  have ht := (hL G theta hG x).2
  nlinarith

end TorusLean.Shared.FermionLocalJet.ThreeCoupling
