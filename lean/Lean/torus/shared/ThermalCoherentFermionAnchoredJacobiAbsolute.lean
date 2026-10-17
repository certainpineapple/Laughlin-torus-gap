import torus.shared.ThermalCoherentFermionAnchoredJacobiFiniteCell
import torus.shared.PhysicalFermionRelativeEnergy

/-! Absolute all-degree physical relative series. Its majorant comes from
true CAR and the exact same-H pair frame. The constant is used for convergence,
not as a loss in the gap budget. It has no particle-number multiplier. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.ThermalCoherentFermionAnchoredJacobiAbsolute
open MeasureTheory TorusLean.Geometry TorusLean.Fermion OAI.Laughlin.Fock
open TorusLean.Shared.PhysicalFermionCAR TorusLean.Shared.PhysicalFermionNormalSquare
open TorusLean.Shared.PhysicalFermionHighTail TorusLean.Shared.PlaneJetTailBudget
open TorusLean.Shared.ThermalCoherentFermionAnchored
open TorusLean.Shared.ThermalCoherentFermionAnchoredJacobiRemoval
open TorusLean.Shared.ThermalCoherentFermionAnchoredJacobiFiniteCell
open TorusLean.Fermion.LatticePacking TorusLean.Fermion.UniformTail
open scoped BigOperators ComplexConjugate

/-- The generic occupation adjoint is exactly the paper's literal D_d. -/
theorem formalRemoval_relative_eq_paper (G : Geometry) (theta : Twist)
    (d : ℕ) (R : ℂ) (x : Space (physicalQ G theta)) :
    formalRemoval G theta R (formalRelativeSeed d) x=paperRelativeRemoval G theta d R x := by
  apply sourceRemoval_eq_of_adjoint
  intro y
  exact paperRelativeRemoval_adjoint G theta d R y x

private theorem occupation_cross_norm_le (Q : ℕ) (x y : Space Q) :
    ‖occupationInner Q x y‖≤occupationNormSq Q x+occupationNormSq Q y := by
  classical
  unfold occupationInner occupationNormSq
  calc
    _ ≤ ∑ A, ‖star ((occupationBasis Q).repr x A)*((occupationBasis Q).repr y A)‖ :=
      norm_sum_le _ _
    _ = ∑ A, ‖(occupationBasis Q).repr x A‖*‖(occupationBasis Q).repr y A‖ := by
      simp only [norm_mul,norm_star]
    _ ≤ ∑ A, (‖(occupationBasis Q).repr x A‖^2+‖(occupationBasis Q).repr y A‖^2) := by
      apply Finset.sum_le_sum
      intro A hA
      nlinarith [sq_nonneg (‖(occupationBasis Q).repr x A‖-‖(occupationBasis Q).repr y A‖),
        mul_nonneg (norm_nonneg ((occupationBasis Q).repr x A))
          (norm_nonneg ((occupationBasis Q).repr y A))]
    _ = _ := Finset.sum_add_distrib

def relativeAbsoluteIntegral (G : Geometry) (theta : Twist)
    (x y : Space (physicalQ G theta)) (d : ℕ) : ℝ :=
  ∫ R, ‖relativeRemovalCross G theta x y d d R‖ ∂cellMeasure G 3

def relativeCrossIntegral (G : Geometry) (theta : Twist)
    (x y : Space (physicalQ G theta)) (d : ℕ) : ℂ :=
  ∫ R, relativeRemovalCross G theta x y d d R ∂cellMeasure G 3

def convergenceConstant (G : Geometry) (theta : Twist)
    (x y : Space (physicalQ G theta)) : ℝ :=
  (3/2:ℝ)*(4096+gaussianConstant)*
    ((occupationInner (physicalQ G theta) x (physicalHamiltonian G theta x)).re+
      (occupationInner (physicalQ G theta) y (physicalHamiltonian G theta y)).re)

theorem convergenceConstant_nonneg (G : Geometry) (theta : Twist)
    (x y : Space (physicalQ G theta)) : 0≤convergenceConstant G theta x y := by
  unfold convergenceConstant
  have hx := physicalHamiltonian_nonneg G theta x
  have hy := physicalHamiltonian_nonneg G theta y
  have hC : 0≤4096+gaussianConstant := by linarith [gaussianConstant_nonneg]
  positivity

/-- Uniform polynomial absolute-integral bound from the real relative source. -/
theorem relativeAbsoluteIntegral_bound (G : Geometry) (theta : Twist)
    (hG : 1≤systole G) (x y : Space (physicalQ G theta)) (d : ℕ) :
    relativeAbsoluteIntegral G theta x y d ≤ convergenceConstant G theta x y*((d:ℝ)+1)^2 := by
  obtain ⟨hix,hbx⟩ := paperRelativeRemoval_integrated_bound_mu3 G theta hG d x
  obtain ⟨hiy,hby⟩ := paperRelativeRemoval_integrated_bound_mu3 G theta hG d y
  have hp (R : ℂ) : ‖relativeRemovalCross G theta x y d d R‖≤
      occupationNormSq (physicalQ G theta) (paperRelativeRemoval G theta d R x)+
        occupationNormSq (physicalQ G theta) (paperRelativeRemoval G theta d R y) := by
    simpa only [relativeRemovalCross,formalRemoval_relative_eq_paper] using
      occupation_cross_norm_le (physicalQ G theta)
        (paperRelativeRemoval G theta d R x) (paperRelativeRemoval G theta d R y)
  have hi := integral_mono (relativeRemovalCross_integrable G theta x y d d 3).norm
    (hix.add hiy) hp
  simp only [Pi.add_apply] at hi
  rw [integral_add hix hiy] at hi
  have hb : relativeAbsoluteIntegral G theta x y d ≤
      (3/2:ℝ)*jetNormBudget G theta d*((d:ℝ)+1)*
        ((occupationInner (physicalQ G theta) x (physicalHamiltonian G theta x)).re+
          (occupationInner (physicalQ G theta) y (physicalHamiltonian G theta y)).re) := by
    dsimp only [relativeAbsoluteIntegral]
    nlinarith
  apply hb.trans
  have hx := physicalHamiltonian_nonneg G theta x
  have hy := physicalHamiltonian_nonneg G theta y
  have hM := jetNormBudget_le G theta hG d
  have hm := mul_le_mul_of_nonneg_right hM
    (show 0≤(3/2:ℝ)*((d:ℝ)+1)*
      ((occupationInner (physicalQ G theta) x (physicalHamiltonian G theta x)).re+
        (occupationInner (physicalQ G theta) y (physicalHamiltonian G theta y)).re) by positivity)
  convert hm using 1 <;> (try dsimp only [convergenceConstant]) <;> ring

private theorem shifted_cubic_half_summable :
    Summable (fun d : ℕ => ((d:ℝ)+1)^3*(1/2:ℝ)^d) := by
  have hs := summable_pow_mul_geometric_of_norm_lt_one 3
    (by norm_num : ‖(1/2:ℝ)‖<1)
  have ht := ((summable_nat_add_iff 1).mpr hs).mul_left 2
  convert ht using 1
  funext d
  simp only [Nat.cast_add,Nat.cast_one,pow_succ]
  ring

theorem all_relative_absolute_weight_summable (G : Geometry) (theta : Twist)
    (hG : 1≤systole G) (x y : Space (physicalQ G theta)) :
    Summable (fun d : ℕ => |3*(d:ℝ)-1| *(1/2:ℝ)^d*relativeAbsoluteIntegral G theta x y d) := by
  have hC := convergenceConstant_nonneg G theta x y
  apply Summable.of_nonneg_of_le (fun d => mul_nonneg (by positivity)
    (integral_nonneg (fun R => norm_nonneg _))) _
    (shifted_cubic_half_summable.mul_left (3*convergenceConstant G theta x y))
  intro d
  have hd : 0≤(d:ℝ) := Nat.cast_nonneg d
  have ha : |3*(d:ℝ)-1|≤3*((d:ℝ)+1) := abs_le.mpr ⟨by linarith,by linarith⟩
  calc
    _ ≤ |3*(d:ℝ)-1| *(1/2:ℝ)^d*
        (convergenceConstant G theta x y*((d:ℝ)+1)^2) :=
      mul_le_mul_of_nonneg_left (relativeAbsoluteIntegral_bound G theta hG x y d)
        (by positivity)
    _ ≤ (3*((d:ℝ)+1))*(1/2:ℝ)^d*
        (convergenceConstant G theta x y*((d:ℝ)+1)^2) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ha (by positivity))
        (by positivity)
    _ = _ := by ring

theorem original_relative_series_summable_integral_norm (G : Geometry) (theta : Twist)
    (hG : 1≤systole G) (x y : Space (physicalQ G theta)) :
    Summable (fun d => ∫ R, ‖(q d:ℂ)*relativeRemovalCross G theta x y d d R‖
      ∂cellMeasure G 3) := by
  have he (d : ℕ) : (∫ R, ‖(q d:ℂ)*relativeRemovalCross G theta x y d d R‖
      ∂cellMeasure G 3)=|3*(d:ℝ)-1| *(1/2:ℝ)^d*relativeAbsoluteIntegral G theta x y d := by
    simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,q,abs_mul,abs_pow,
      show |(-1/2:ℝ)|=1/2 by norm_num]
    rw [integral_const_mul]
    rfl
  simp_rw [he]
  exact all_relative_absolute_weight_summable G theta hG x y

/-- Literal two-index COM series, retaining original actual relative matrix elements. -/
def physicalCOMTerm (G : Geometry) (theta : Twist)
    (x y : Space (physicalQ G theta)) (dn : ℕ×ℕ) : ℂ :=
  (fermionAnchoredJacobiCrossWeight dn.1 dn.2:ℂ)*relativeCrossIntegral G theta x y dn.1

theorem physicalCOM_summable_norm (G : Geometry) (theta : Twist)
    (hG : 1≤systole G) (x y : Space (physicalQ G theta)) :
    Summable (fun dn : ℕ×ℕ => ‖physicalCOMTerm G theta x y dn‖) := by
  have hn (d n : ℕ) : ‖physicalCOMTerm G theta x y (d,n)‖=
      ‖fermionAnchoredJacobiCrossWeight d n‖*‖relativeCrossIntegral G theta x y d‖ := by
    simp only [physicalCOMTerm,norm_mul,Complex.norm_real]
  apply (summable_prod_of_nonneg (fun dn => norm_nonneg _)).mpr
  constructor
  · intro d
    simpa only [hn] using ((hasSum_norm_fermionAnchoredJacobiCrossWeight d).mul_right
      ‖relativeCrossIntegral G theta x y d‖).summable
  · have he (d : ℕ) : (∑' n, ‖physicalCOMTerm G theta x y (d,n)‖)=
        |3*(d:ℝ)-1| *(1/2:ℝ)^d*‖relativeCrossIntegral G theta x y d‖ := by
      simpa only [hn] using ((hasSum_norm_fermionAnchoredJacobiCrossWeight d).mul_right
        ‖relativeCrossIntegral G theta x y d‖).tsum_eq
    simp_rw [he]
    apply Summable.of_nonneg_of_le (fun d => by positivity) _
      (all_relative_absolute_weight_summable G theta hG x y)
    intro d
    exact mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _)
      (by positivity)

end TorusLean.Shared.ThermalCoherentFermionAnchoredJacobiAbsolute
