import torus.shared.BosonNatThreeMatrixTrace
import torus.shared.BosonFiniteCertificateRealization

/-! Actual finite rank matrices after the original Nat seed periodization.
The matrix here is a rank coefficient, not a nonorthogonal-family form matrix.
No identification with a torus single-contraction Hamiltonian is asserted. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace TorusLean.Shared.BosonNatThreeMatrixLift
open TorusLean.Boson TorusLean.Boson.SpectatorControl TorusLean.Boson.TwoBodyLift
open TorusLean.Shared.PhysicalBosonSector TorusLean.Shared.BosonThreeBodyLift
open TorusLean.Shared.BosonFiniteCertificateRealization
open TorusLean.Shared.ThermalCoherentInsertionThreeLift
open TorusLean.Shared.BosonNatThreeRemovalTrace
open MeasureTheory Matrix
open scoped BigOperators ComplexConjugate ComplexOrder

local instance matrixLift_nonempty (G : Geometry) (theta : Twist) :
    Nonempty (OrbitalIndex G theta) := ⟨⟨0,lll_finrank_pos G theta 1⟩⟩

theorem threeBodyLift_familyRank_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] {r : ℕ} (w : Fin r → ThreeSector ι) (i j : Fin r) (p : Core ι ℂ) :
    threeBodyLift (familyRank w i j) p = (w i).val * threeSeedRemoval (w j) p := by
  have hrow (x : TripleIndex ι) :
      (∑ y, (ip (w j).val (tripleVacuum y).val * ip (tripleVacuum x).val (w i).val) •
        tripleCreate x (tripleRemove y p)) =
      ip (tripleVacuum x).val (w i).val • tripleCreate x (threeSeedRemoval (w j) p) := by
    simp only [threeSeedRemoval, LinearMap.sum_apply, LinearMap.smul_apply,
      map_sum, map_smul, Finset.smul_sum, smul_smul, mul_comm]
  simp only [threeBodyLift, tripleCoefficientLift, threeSectorKernel,
    familyRank, LinearMap.coe_mk, AddHom.coe_mk, Submodule.coe_smul,
    TwoBodyLift.inner_smul_right, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.comp_apply, hrow]
  exact threeSeed_creation_resolution (w i) _

theorem threeBodyLift_familyRank_inner {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] {r : ℕ} (w : Fin r → ThreeSector ι) (i j : Fin r) (f g : Core ι ℂ) :
    ip f (threeBodyLift (familyRank w i j) g) =
      ip (threeSeedRemoval (w i) f) (threeSeedRemoval (w j) g) := by
  rw [threeBodyLift_familyRank_apply]
  calc
    _ = star (ip ((w i).val * threeSeedRemoval (w j) g) f) :=
      (occupationInner_conj_symm (fun _ => 1) _ _).symm
    _ = star (ip (threeSeedRemoval (w j) g) (threeSeedRemoval (w i) f)) := by
      rw [threeSeedRemoval_adjoint]
    _ = _ := occupationInner_conj_symm (fun _ => 1) _ _

theorem rankOneRealization_lift_inner {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] {r : ℕ} (w : Fin r → ThreeSector ι) (C : Matrix (Fin r) (Fin r) ℂ)
    (f g : Core ι ℂ) :
    ip f (threeBodyLift (rankOneRealization w C) g) =
      ∑ i, ∑ j, C i j * ip (threeSeedRemoval (w i) f) (threeSeedRemoval (w j) g) := by
  change ip f (threeBodyLiftLinear (∑ i, ∑ j, C i j • familyRank w i j) g) = _
  simp only [map_sum,map_smul,LinearMap.sum_apply,LinearMap.smul_apply,
    inner_sum_right,TwoBodyLift.inner_smul_right]
  simp only [threeBodyLiftLinear,LinearMap.coe_mk,AddHom.coe_mk,
    threeBodyLift_familyRank_inner]

def natMatrixLiftForm (G : Geometry) (theta : Twist) {r : ℕ}
    (p : Fin r → Core ℕ ℂ) (hp : ∀ i, (p i).IsHomogeneous 3)
    (C : Matrix (Fin r) (Fin r) ℂ) (f : Core (OrbitalIndex G theta) ℂ) : ℝ :=
  ∫ R, (ip f (threeBodyLift
    (rankOneRealization (fun i => natThreeSeed G theta (p i) (hp i) 0 R) C) f)).re
      ∂cellMeasure G 3


theorem natMatrixLiftForm_eq_rows (G : Geometry) (theta : Twist) {r : ℕ}
    (p : Fin r → Core ℕ ℂ) (hp : ∀ i, (p i).IsHomogeneous 3)
    (C : Matrix (Fin r) (Fin r) ℂ) (f : Core (OrbitalIndex G theta) ℂ) :
    natMatrixLiftForm G theta p hp C f =
      ∫ R, (∑ i, ∑ j, C i j * ip
        (natThreeRemoval G theta (p i) (hp i) 0 R f)
        (natThreeRemoval G theta (p j) (hp j) 0 R f)).re ∂cellMeasure G 3 := by
  simp only [natMatrixLiftForm,rankOneRealization_lift_inner,natThreeRemoval]

theorem natMatrixLiftForm_nonneg (G : Geometry) (theta : Twist) {r : ℕ}
    (p : Fin r → Core ℕ ℂ) (hp : ∀ i, (p i).IsHomogeneous 3)
    (C : Matrix (Fin r) (Fin r) ℂ) (hC : C.PosSemidef)
    (f : Core (OrbitalIndex G theta) ℂ) : 0 ≤ natMatrixLiftForm G theta p hp C f := by
  apply integral_nonneg
  intro R
  exact rankOneRealization_lift_nonneg _ C hC f

theorem natMatrixLiftForm_integrable (G : Geometry) (theta : Twist) {r : ℕ}
    (p : Fin r → Core ℕ ℂ) (hp : ∀ i, (p i).IsHomogeneous 3)
    (C : Matrix (Fin r) (Fin r) ℂ) (f : Core (OrbitalIndex G theta) ℂ) :
    Integrable (fun R => (ip f (threeBodyLift
      (rankOneRealization (fun i => natThreeSeed G theta (p i) (hp i) 0 R) C) f)).re)
        (cellMeasure G 3) := by
  simp_rw [rankOneRealization_lift_inner]
  have h : Integrable (fun R => ∑ i, ∑ j, C i j * ip
      (natThreeRemoval G theta (p i) (hp i) 0 R f)
      (natThreeRemoval G theta (p j) (hp j) 0 R f)) (cellMeasure G 3) := by
    apply integrable_finsetSum
    intro i hi
    apply integrable_finsetSum
    intro j hj
    exact (natThreeRemoval_cross_integrable G theta 3 (p i) (p j)
      (hp i) (hp j) 0 0 f f).const_mul (C i j)
  apply h.re.congr
  filter_upwards [] with R
  rfl

end TorusLean.Shared.BosonNatThreeMatrixLift
