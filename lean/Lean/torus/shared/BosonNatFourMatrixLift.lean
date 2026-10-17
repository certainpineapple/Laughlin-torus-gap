import torus.shared.BosonNatFourLiftForm
import torus.shared.BosonNatFourAnnihilator
import torus.shared.BosonNatThreeMatrixLift

/-! Finite rank coefficient matrices inserted into the original full-core L4.
The source family need not be orthonormal. Positivity uses its actual finite
factorial output metric and does not assume an isometric periodization. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.BosonNatFourMatrixLift
open TorusLean.Boson TorusLean.Boson.SpectatorControl TorusLean.Boson.TwoBodyLift
open TorusLean.Shared.PhysicalBosonSector
open TorusLean.Shared.ThermalCoherentFourBodyLift
open TorusLean.Shared.ThermalCoherentFourBodyFrame
open TorusLean.Shared.BosonNatFourRemovalTrace
open TorusLean.Shared.BosonNatFourAnnihilator
open MeasureTheory Matrix
open scoped BigOperators ComplexConjugate ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- Scalar PSD acts on arbitrary actual polynomial outputs, with no dimension
or particle-number multiplier. -/
theorem occupation_matrix_nonneg {r : ℕ} (C : Matrix (Fin r) (Fin r) ℂ)
    (hC : C.PosSemidef) (Y : Fin r → Core ι ℂ) :
    0 ≤ (∑ i, ∑ j, C i j * ip (Y i) (Y j)).re := by
  classical
  let S := Finset.univ.biUnion (fun i => (Y i).support)
  have hY (i : Fin r) : (Y i).support ⊆ S := by
    intro n hn
    exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ i,hn⟩
  have he : (∑ i, ∑ j, C i j * ip (Y i) (Y j)) =
      ∑ n ∈ S, (occupationMetricWeight (fun _ : ι => 1) n : ℂ) *
        (star (fun i => (Y i).coeff n) ⬝ᵥ (C *ᵥ (fun i => (Y i).coeff n))) := by
    simp_rw [inner_supported S _ _ (hY _),Finset.mul_sum]
    conv_lhs =>
      arg 2
      ext i
      rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro n hn
    simp only [dotProduct,Matrix.mulVec,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    simp only [Pi.star_apply]
    ring
  rw [he]
  simp only [Complex.re_sum,Complex.mul_re,Complex.natCast_re,
    Complex.natCast_im,zero_mul,sub_zero]
  apply Finset.sum_nonneg
  intro n hn
  exact mul_nonneg (Nat.cast_nonneg _)
    (Complex.nonneg_iff.mp (hC.dotProduct_mulVec_nonneg (fun i => (Y i).coeff n))).1

theorem fourBodyLift_rank_inner (s t : FourSector ι) (f g : Core ι ℂ) :
    ip f (fourBodyLift (fourSeedRankOne s t) g) =
      ip (fourSeedRemoval s f) (fourSeedRemoval t g) := by
  rw [fourBodyLift_fourSeedRankOne_apply]
  calc
    _ = star (ip (s.val * fourSeedRemoval t g) f) :=
      (occupationInner_conj_symm (fun _ => 1) _ _).symm
    _ = star (ip (fourSeedRemoval t g) (fourSeedRemoval s f)) := by
      rw [fourSeedRemoval_adjoint]
    _ = _ := occupationInner_conj_symm (fun _ => 1) _ _

def fourRankRealization {r : ℕ} (w : Fin r → FourSector ι)
    (C : Matrix (Fin r) (Fin r) ℂ) : FourSector ι →ₗ[ℂ] FourSector ι :=
  ∑ i, ∑ j, C i j • fourSeedRankOne (w i) (w j)

theorem fourRankRealization_lift_inner {r : ℕ} (w : Fin r → FourSector ι)
    (C : Matrix (Fin r) (Fin r) ℂ) (f g : Core ι ℂ) :
    ip f (fourBodyLift (fourRankRealization w C) g) =
      ∑ i, ∑ j, C i j * ip (fourSeedRemoval (w i) f) (fourSeedRemoval (w j) g) := by
  change ip f (fourBodyLiftLinear (∑ i, ∑ j, C i j • fourSeedRankOne (w i) (w j)) g) = _
  simp only [map_sum,map_smul,LinearMap.sum_apply,LinearMap.smul_apply,
    inner_sum_right,TwoBodyLift.inner_smul_right]
  simp only [fourBodyLiftLinear,LinearMap.coe_mk,AddHom.coe_mk,fourBodyLift_rank_inner]

local instance natFourMatrix_nonempty (G : Geometry) (theta : Twist) :
    Nonempty (OrbitalIndex G theta) := ⟨⟨0,lll_finrank_pos G theta 1⟩⟩

def natFourMatrixCellLiftForm (G : Geometry) (theta : Twist) (charge : ℕ) {r : ℕ}
    (w : Fin r → Core ℕ ℂ) (hw : ∀ i, (w i).IsHomogeneous 4)
    (C : Matrix (Fin r) (Fin r) ℂ) (f : Core (OrbitalIndex G theta) ℂ) : ℝ :=
  ∫ R, (ip f (fourBodyLift (fourRankRealization
    (fun i => natFourSeed G theta (w i) (hw i) 0 R) C) f)).re ∂cellMeasure G charge

theorem natFourMatrixCellLiftForm_eq_rows (G : Geometry) (theta : Twist) (charge : ℕ) {r : ℕ}
    (w : Fin r → Core ℕ ℂ) (hw : ∀ i, (w i).IsHomogeneous 4)
    (C : Matrix (Fin r) (Fin r) ℂ) (f : Core (OrbitalIndex G theta) ℂ) :
    natFourMatrixCellLiftForm G theta charge w hw C f =
      ∫ R, (∑ i, ∑ j, C i j * ip (natFourRemoval G theta (w i) (hw i) 0 R f)
        (natFourRemoval G theta (w j) (hw j) 0 R f)).re ∂cellMeasure G charge := by
  simp only [natFourMatrixCellLiftForm,fourRankRealization_lift_inner,natFourRemoval]

theorem natFourMatrixCellLiftForm_eq_annihilator (G : Geometry) (theta : Twist) (charge : ℕ) {r : ℕ}
    (w : Fin r → Core ℕ ℂ) (hw : ∀ i, (w i).IsHomogeneous 4)
    (C : Matrix (Fin r) (Fin r) ℂ) (f : Core (OrbitalIndex G theta) ℂ) :
    natFourMatrixCellLiftForm G theta charge w hw C f =
      ∫ R, (∑ i, ∑ j, C i j * ip (natFourAnnihilator G theta R (w i) f)
        (natFourAnnihilator G theta R (w j) f)).re ∂cellMeasure G charge := by
  rw [natFourMatrixCellLiftForm_eq_rows]
  simp_rw [natFourAnnihilator_ground G theta _ (hw _)]

theorem natFourMatrixCellLiftForm_integrable (G : Geometry) (theta : Twist) (charge : ℕ) {r : ℕ}
    (w : Fin r → Core ℕ ℂ) (hw : ∀ i, (w i).IsHomogeneous 4)
    (C : Matrix (Fin r) (Fin r) ℂ) (f : Core (OrbitalIndex G theta) ℂ) :
    Integrable (fun R => (ip f (fourBodyLift (fourRankRealization
      (fun i => natFourSeed G theta (w i) (hw i) 0 R) C) f)).re) (cellMeasure G charge) := by
  simp_rw [fourRankRealization_lift_inner]
  have h : Integrable (fun R => ∑ i, ∑ j, C i j * ip
      (natFourRemoval G theta (w i) (hw i) 0 R f)
      (natFourRemoval G theta (w j) (hw j) 0 R f)) (cellMeasure G charge) := by
    apply integrable_finsetSum
    intro i hi
    apply integrable_finsetSum
    intro j hj
    exact (natFourRemoval_cross_integrable G theta charge (w i) (w j)
      (hw i) (hw j) 0 0 f f).const_mul (C i j)
  apply h.re.congr
  filter_upwards [] with R
  rfl

theorem natFourMatrixCellLiftForm_nonneg (G : Geometry) (theta : Twist) (charge : ℕ) {r : ℕ}
    (w : Fin r → Core ℕ ℂ) (hw : ∀ i, (w i).IsHomogeneous 4)
    (C : Matrix (Fin r) (Fin r) ℂ) (hC : C.PosSemidef)
    (f : Core (OrbitalIndex G theta) ℂ) :
    0 ≤ natFourMatrixCellLiftForm G theta charge w hw C f := by
  rw [natFourMatrixCellLiftForm_eq_rows]
  apply integral_nonneg
  intro R
  exact occupation_matrix_nonneg C hC _

theorem natFourMatrixCellLiftForm_sub (G : Geometry) (theta : Twist) (charge : ℕ) {r : ℕ}
    (w : Fin r → Core ℕ ℂ) (hw : ∀ i, (w i).IsHomogeneous 4)
    (C D : Matrix (Fin r) (Fin r) ℂ) (f : Core (OrbitalIndex G theta) ℂ) :
    natFourMatrixCellLiftForm G theta charge w hw (C-D) f =
      natFourMatrixCellLiftForm G theta charge w hw C f - natFourMatrixCellLiftForm G theta charge w hw D f := by
  have hC := natFourMatrixCellLiftForm_integrable G theta charge w hw C f
  have hD := natFourMatrixCellLiftForm_integrable G theta charge w hw D f
  simp_rw [fourRankRealization_lift_inner] at hC hD
  simp only [natFourMatrixCellLiftForm,fourRankRealization_lift_inner,
    Matrix.sub_apply,sub_mul,Finset.sum_sub_distrib,Complex.sub_re]
  exact integral_sub hC hD


#print axioms occupation_matrix_nonneg
#print axioms fourBodyLift_rank_inner
#print axioms fourRankRealization_lift_inner
#print axioms natFourMatrixCellLiftForm_eq_rows
#print axioms natFourMatrixCellLiftForm_eq_annihilator
#print axioms natFourMatrixCellLiftForm_integrable
#print axioms natFourMatrixCellLiftForm_nonneg
#print axioms natFourMatrixCellLiftForm_sub

end TorusLean.Shared.BosonNatFourMatrixLift
