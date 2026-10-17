import torus.shared.BosonNatFourOriginalCOMTransfer
import torus.shared.BosonNatFourOriginalRelativeTrace
import torus.shared.BosonFiniteCertificateNatFourCOMTraceAverage

/-! Reassemble the original complete COM trace as its original finite relative
matrix average. The source-cell form, its full matrices, and all relative
multiplicities are unchanged. This file consumes the actual COM source and
coefficient identities, rather than assuming a relative-only source form. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.BosonNatFourOriginalRelativeAverage
open TorusLean.Boson TorusLean.Boson.SpectatorControl TorusLean.BosonFiniteCertificate
open TorusLean.Shared.PhysicalBosonSector TorusLean.Shared.BosonNatFourMatrixLift
open TorusLean.Shared.BosonNatFourRemovalTrace TorusLean.Shared.BosonNatFourMatrixCOMTrace
open TorusLean.Shared.BosonNatFourCOMReindex
open TorusLean.Shared.BosonNatFourOriginalCOMTransfer
open TorusLean.Shared.BosonNatFourOriginalRelativeTrace
open TorusLean.Shared.ThermalCoherentBosonRowOriginalFourLift
open MeasureTheory
open scoped BigOperators

private def relativeCross (G : Geometry) (theta : Twist)
    (f : Core (OrbitalIndex G theta) ℂ) (d : Fin 17)
    (a b : Fin (natFourRelativeDimension d)) : ℂ :=
  ∫ R, ip
    (natFourRemoval G theta (natFourRelativeColumn d a)
      (natFourRelativeColumn_bihomogeneous d a).1 0 R f)
    (natFourRemoval G theta (natFourRelativeColumn d b)
      (natFourRelativeColumn_bihomogeneous d b).1 0 R f)
    ∂cellMeasure G 4

private theorem fixed_degree (G : Geometry) (theta : Twist)
    (f : Core (OrbitalIndex G theta) ℂ) (D : Fin 17) :
    natFourMatrixCellLiftForm G theta 2 (natFourCompleteCOMFamily D)
      (fun i => (natFourCompleteCOMFamily_bihomogeneous D i).1)
      (natFourOriginalCOMRankCoefficient D) f =
    (∑ d : Fin (D.val+1), ∑ a, ∑ b,
      ((natFourCOMWeight (D.val-d.val)/2) *
        natFourOriginalCOMCoefficientFiber D d a b) *
        relativeCross G theta f (natFourRelativeDegreeAt D d) a b).re := by
  rw [originalCOMMatrixCell_eq_relative_fibers]
  congr 1
  simp only [Finset.mul_sum,relativeCross]
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  ring

private theorem averaged_cross (G : Geometry) (theta : Twist)
    (f : Core (OrbitalIndex G theta) ℂ) (d : Fin 17) :
    (∑ n : Fin (17-d.val), ∑ a, ∑ b,
      ((natFourCOMWeight n.val/2) * natFourOriginalDescendantCoefficient d n a b) *
        relativeCross G theta f d a b) =
    ∑ a, ∑ b, natFourRelativeM4RankCoefficient d a b * relativeCross G theta f d a b := by
  rw [←natFourOriginalCOM_trace_rank_coefficient d]
  simp only [Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,Finset.sum_mul]
  calc
    _ = ∑ a, ∑ n : Fin (17-d.val), ∑ b,
        ((natFourCOMWeight n.val/2)*natFourOriginalDescendantCoefficient d n a b)*
          relativeCross G theta f d a b := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a ha
      exact Finset.sum_comm

/-- The unchanged literal original M4 source-cell form is the sum of its
true relative JEJ matrix forms after the complete finite COM trace. -/
theorem originalM4SourceCellForm_eq_relative_matrices (G : Geometry) (theta : Twist)
    (f : Core (OrbitalIndex G theta) ℂ) :
    originalM4SourceCellForm G theta f =
      ∑ d : Fin 17, natFourMatrixCellLiftForm G theta 4 (natFourRelativeColumn d)
        (fun a => (natFourRelativeColumn_bihomogeneous d a).1)
        (natFourRelativeM4RankCoefficient d) f := by
  rw [originalM4SourceCellForm_eq_complete_COM]
  simp_rw [fixed_degree]
  rw [←Complex.re_sum]
  have htri := Fintype.sum_equiv (degreeCOMEquiv 16)
    (fun x => ∑ a, ∑ b,
      ((natFourCOMWeight (x.1.val-x.2.val)/2) *
        natFourOriginalCOMCoefficientFiber x.1 x.2 a b) *
        relativeCross G theta f (natFourRelativeDegreeAt x.1 x.2) a b)
    (fun x => ∑ a, ∑ b,
      ((natFourCOMWeight x.2.val/2) * natFourOriginalDescendantCoefficient x.1 x.2 a b) *
        relativeCross G theta f x.1 a b) ?_
  · simp only [Fintype.sum_sigma] at htri
    rw [htri]
    calc
      _ = (∑ d : Fin 17, ∑ a, ∑ b,
          natFourRelativeM4RankCoefficient d a b * relativeCross G theta f d a b).re := by
        exact congrArg Complex.re
          (Finset.sum_congr rfl (fun d _ => averaged_cross G theta f d))
      _ = _ := by
        rw [Complex.re_sum]
        apply Finset.sum_congr rfl
        intro d hd
        exact (natFourMatrixCellLiftForm_integrated_cross G theta 4
          (natFourRelativeColumn d) (fun a => (natFourRelativeColumn_bihomogeneous d a).1)
          (natFourRelativeM4RankCoefficient d) f).symm
  · rintro ⟨D,d⟩
    fin_cases D <;> fin_cases d
    all_goals rfl

#print axioms originalM4SourceCellForm_eq_relative_matrices
end TorusLean.Shared.BosonNatFourOriginalRelativeAverage
