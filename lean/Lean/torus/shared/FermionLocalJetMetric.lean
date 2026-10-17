import torus.shared.FermionLocalJetRows
import torus.shared.FermionLocalJetDescendantEnergy

/-! The seven actual certificate rows applied to original CAR pair descendants.
The grouped metric remainder is paid pointwise by original pair occupations;
the exact descendant-energy theorem supplies its same-H integral payment. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.Shared.FermionLocalJet
open MeasureTheory TorusLean.Geometry TorusLean.Fermion OAI.Laughlin.Fock
open TorusLean.Shared.PlaneJetMembership TorusLean.Shared.FermionRelativeFrame
open TorusLean.Shared.PhysicalFermionCAR TorusLean.Shared.PhysicalFermionNormalSquare
open TorusLean.Fermion.LatticePacking
open scoped BigOperators ComplexConjugate

/-- Finite weighted Cauchy--Schwarz in the actual occupation metric. -/
theorem occupation_sum_cauchy {I : Type*} (Q : ℕ) (s : Finset I)
    (c : I → ℝ) (v : I → Space Q) :
    occupationNormSq Q (∑ a ∈ s, (c a : ℂ) • v a) ≤
      (∑ a ∈ s, (c a)^2) * ∑ a ∈ s, occupationNormSq Q (v a) := by
  unfold occupationNormSq
  simp only [map_sum,Finsupp.finsetSum_apply,map_smul,Finsupp.smul_apply,smul_eq_mul]
  rw [Finset.sum_comm (f := fun a A => ‖(occupationBasis Q).repr (v a) A‖^2),Finset.mul_sum]
  apply Finset.sum_le_sum
  intro A hA
  have ht : ‖∑ a ∈ s, (c a : ℂ) * (occupationBasis Q).repr (v a) A‖ ≤
      ∑ a ∈ s, |c a| * ‖(occupationBasis Q).repr (v a) A‖ := by
    simpa only [norm_mul,Complex.norm_real,Real.norm_eq_abs] using
      norm_sum_le s (fun a => (c a : ℂ) * (occupationBasis Q).repr (v a) A)
  have hs := Finset.sum_mul_sq_le_sq_mul_sq s (fun a => |c a|)
    (fun a => ‖(occupationBasis Q).repr (v a) A‖)
  simp only [sq_abs] at hs
  exact (pow_le_pow_left₀ (norm_nonneg _) ht 2).trans hs

def certificateEntryJet (r : CertificateRow) (a : CertificateEntry r) : Fin 9 :=
  ⟨certificateJetIndex r a,by have := (certificate_row_support r a).2.2.2; omega⟩

/-- Original c_j(R) B_p(R), with p,j taken from the literal row entry. -/
def certificateAmplitude (G : Geometry) (theta : Twist) (r : CertificateRow)
    (a : CertificateEntry r) (R : ℂ) (x : Space (physicalQ G theta)) : Space (physicalQ G theta) :=
  localJetAnnihilate G theta (certificateEntryData r a).2.1 R
    (pairDescendant G theta (certificateEntryData r a).1 R x)

/-- The paper's X_i, retaining the actual coefficient, raw jets and pair order. -/
def certificateRowOutput (G : Geometry) (theta : Twist) (r : CertificateRow)
    (R : ℂ) (x : Space (physicalQ G theta)) (i : Fin 9) : Space (physicalQ G theta) :=
  ∑ a ∈ Finset.univ.filter (fun a : CertificateEntry r => certificateEntryJet r a = i),
    (certificateAlpha r a : ℂ) • certificateAmplitude G theta r a R x

/-- Each support entry belongs to one actual auxiliary jet index, without factor 9. -/
theorem certificate_group_sum {V : Type*} [AddCommMonoid V]
    (r : CertificateRow) (v : CertificateEntry r → V) :
    (∑ i : Fin 9, ∑ a ∈ Finset.univ.filter (fun a : CertificateEntry r =>
      certificateEntryJet r a = i), v a) = ∑ a, v a := by
  classical
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  simp

theorem certificateRowOutput_norm_bound (G : Geometry) (theta : Twist)
    (r : CertificateRow) (R : ℂ) (x : Space (physicalQ G theta)) :
    (∑ i : Fin 9, occupationNormSq (physicalQ G theta) (certificateRowOutput G theta r R x i)) ≤
      (certificateRowBudget r : ℝ) * ∑ a : CertificateEntry r,
        occupationNormSq (physicalQ G theta) (certificateAmplitude G theta r a R x) := by
  classical
  calc
    _ ≤ ∑ i : Fin 9, (certificateRowBudget r : ℝ) *
      ∑ a ∈ Finset.univ.filter (fun a : CertificateEntry r => certificateEntryJet r a = i),
        occupationNormSq (physicalQ G theta) (certificateAmplitude G theta r a R x) := by
      apply Finset.sum_le_sum
      intro i hi
      apply (occupation_sum_cauchy (physicalQ G theta) _ (certificateAlpha r)
        (fun a => certificateAmplitude G theta r a R x)).trans
      apply mul_le_mul_of_nonneg_right ?_ (Finset.sum_nonneg fun _ _ => occupationNormSq_nonneg _ _)
      simpa only [Finset.sum_filter,certificateEntryJet,Fin.ext_iff] using
        certificate_alpha_group_bound r i
    _ = _ := by rw [← Finset.mul_sum,certificate_group_sum]

/-- This is the literal grouped single-contraction Gram remainder of the seven rows. -/
def certificateMetricAt (G : Geometry) (theta : Twist) (R : ℂ)
    (x : Space (physicalQ G theta)) : ℝ :=
  ∑ r : CertificateRow, (∑ i : Fin 9, ∑ k : Fin 9,
    (inner ℂ (rawPlaneJet G theta i R) (rawPlaneJet G theta k R) - if i=k then 1 else 0) *
      occupationInner (physicalQ G theta) (certificateRowOutput G theta r R x i)
        (certificateRowOutput G theta r R x k)).re

/-- Every bounded left c_j is paid with its unchanged right pair amplitude. -/
theorem certificateAmplitude_norm_bound (G : Geometry) (theta : Twist)
    (hG : 1 ≤ systole G) (r : CertificateRow) (a : CertificateEntry r) (R : ℂ)
    (x : Space (physicalQ G theta)) :
    occupationNormSq (physicalQ G theta) (certificateAmplitude G theta r a R x) ≤
      (1+e8 G theta) * occupationNormSq (physicalQ G theta)
        (pairDescendant G theta (certificateEntryData r a).1 R x) :=
  localJetAnnihilate_finite_bound G theta 8 hG R (certificateEntryData r a).2.1
    (certificate_row_support r a).2.1 _

/-- Concrete seven-row metric budget, with no abstract Gram or pair-energy premise. -/
theorem certificateMetricAt_bound (G : Geometry) (theta : Twist)
    (hG : 1 ≤ systole G) (R : ℂ) (x : Space (physicalQ G theta)) :
    |certificateMetricAt G theta R x| ≤
      e8 G theta * (1+e8 G theta) * ∑ r : CertificateRow,
        (certificateRowBudget r : ℝ) * ∑ a : CertificateEntry r,
          occupationNormSq (physicalQ G theta)
            (pairDescendant G theta (certificateEntryData r a).1 R x) := by
  have he : 0 ≤ e8 G theta := localJetError_nonneg G theta 8 hG
  unfold certificateMetricAt
  calc
    _ ≤ ∑ r : CertificateRow, |(∑ i : Fin 9, ∑ k : Fin 9,
      (inner ℂ (rawPlaneJet G theta i R) (rawPlaneJet G theta k R) - if i=k then 1 else 0) *
        occupationInner (physicalQ G theta) (certificateRowOutput G theta r R x i)
          (certificateRowOutput G theta r R x k)).re| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ r : CertificateRow, e8 G theta *
      ((certificateRowBudget r : ℝ) * ((1+e8 G theta) * ∑ a : CertificateEntry r,
        occupationNormSq (physicalQ G theta)
          (pairDescendant G theta (certificateEntryData r a).1 R x))) := by
      apply Finset.sum_le_sum
      intro r hr
      apply (e8_occupation_metric_bound G theta hG R (certificateRowOutput G theta r R x)).trans
      apply mul_le_mul_of_nonneg_left _ he
      apply (certificateRowOutput_norm_bound G theta r R x).trans
      apply mul_le_mul_of_nonneg_left _ (by exact_mod_cast certificateRowBudget_nonneg r)
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum (fun a ha => certificateAmplitude_norm_bound G theta hG r a R x)
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      ring

#print axioms occupation_sum_cauchy
#print axioms certificate_group_sum
#print axioms certificateRowOutput_norm_bound
#print axioms certificateAmplitude_norm_bound
#print axioms certificateMetricAt_bound
end TorusLean.Shared.FermionLocalJet
