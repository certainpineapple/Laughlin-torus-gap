import torus.shared.BosonFiniteCertificateNatFourCOMSourceFiber
import torus.shared.BosonNatFourMatrixCOMTrace
import torus.shared.BosonNatFourCOMReindex

/-! Fixed-degree physical COM trace with the original complete-family
coefficient. All relative multiplicities remain in the same fiber. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.BosonNatFourOriginalRelativeTrace
open TorusLean.Boson TorusLean.Boson.SpectatorControl TorusLean.BosonFiniteCertificate
open TorusLean.Shared.PhysicalBosonSector TorusLean.Shared.BosonNatFourMatrixLift
open TorusLean.Shared.BosonNatFourRemovalTrace TorusLean.Shared.BosonNatFourMatrixCOMTrace
open TorusLean.Shared.BosonNatFourCOMReindex
open MeasureTheory
open scoped BigOperators

private theorem sum_reindex_two {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (F : ι → ι → ℂ) :
    (∑ i, ∑ j, F i j) = ∑ a, ∑ b, F (e.symm a) (e.symm b) := by
  apply Fintype.sum_equiv e
  intro i
  apply Fintype.sum_equiv e
  intro j
  simp only [Equiv.symm_apply_apply]

private theorem sum_COM_fibers {N : ℕ} (D : ℕ) (r : Fin (D+1) → ℕ)
    (e : Fin N ≃ Σ d : Fin (D+1), Fin (r d))
    (C : Matrix (Fin N) (Fin N) ℂ)
    (K : (Σ d : Fin (D+1), Fin (r d)) →
      (Σ d : Fin (D+1), Fin (r d)) → ℂ) :
    (∑ i, ∑ j, if D-(e i).1.val=D-(e j).1.val then
      natFourCOMWeight (D-(e i).1.val) * C i j * K (e i) (e j) else 0) =
      ∑ d, ∑ a : Fin (r d), ∑ b : Fin (r d),
        natFourCOMWeight (D-d.val) * C (e.symm ⟨d,a⟩) (e.symm ⟨d,b⟩) *
          K ⟨d,a⟩ ⟨d,b⟩ := by
  rw [sum_reindex_two e]
  simp only [Equiv.apply_symm_apply]
  exact sum_equal_COM_level D r (fun i j =>
    natFourCOMWeight (D-i.1.val) * C (e.symm i) (e.symm j) * K i j)

private theorem matrix_COM_fibers (G : Geometry) (theta : Twist)
    {N : ℕ} (D : ℕ) (r : Fin (D+1) → ℕ)
    (e : Fin N ≃ Σ d : Fin (D+1), Fin (r d))
    (q : ∀ d : Fin (D+1), Fin (r d) → Core ℕ ℂ)
    (hq : ∀ d a, (q d a).IsHomogeneous 4)
    (hL : ∀ d a, canonicalCOMLowerNat (q d a)=0)
    (v : Fin N → Core ℕ ℂ) (hv : ∀ i, (v i).IsHomogeneous 4)
    (he : ∀ i, v i=(canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[D-(e i).1.val]
      (q (e i).1 (e i).2))
    (C : Matrix (Fin N) (Fin N) ℂ) (f : Core (OrbitalIndex G theta) ℂ) :
    natFourMatrixCellLiftForm G theta 2 v hv C f =
      ((2/4 : ℂ) * ∑ d : Fin (D+1), ∑ a : Fin (r d), ∑ b : Fin (r d),
        natFourCOMWeight (D-d.val) * C (e.symm ⟨d,a⟩) (e.symm ⟨d,b⟩) *
          (∫ R, ip (natFourRemoval G theta (q d a) (hq d a) 0 R f)
            (natFourRemoval G theta (q d b) (hq d b) 0 R f)
            ∂cellMeasure G 4)).re := by
  have ht := natFourMatrixCellLiftForm_COM_trace G theta (r := N)
    (fun i => q (e i).1 (e i).2) v (fun i => hq (e i).1 (e i).2) hv
    (fun i => hL (e i).1 (e i).2) (fun i => D-(e i).1.val) he C f
  exact ht.trans (congrArg (fun z : ℂ => ((2/4 : ℂ)*z).re)
    (sum_COM_fibers D r e C (fun i j =>
      ∫ R, ip (natFourRemoval G theta (q i.1 i.2) (hq i.1 i.2) 0 R f)
        (natFourRemoval G theta (q j.1 j.2) (hq j.1 j.2) 0 R f)
        ∂cellMeasure G 4)))

/-- The original degree-D matrix contributes precisely its equal-level
relative fibers after actual charge-two to charge-four cell integration. -/
theorem originalCOMMatrixCell_eq_relative_fibers (G : Geometry) (theta : Twist)
    (D : Fin 17) (f : Core (OrbitalIndex G theta) ℂ) :
    natFourMatrixCellLiftForm G theta 2 (natFourCompleteCOMFamily D)
      (fun i => (natFourCompleteCOMFamily_bihomogeneous D i).1)
      (natFourOriginalCOMRankCoefficient D) f =
      ((2/4 : ℂ) * ∑ d : Fin (D.val+1), ∑ a, ∑ b,
        natFourCOMWeight (D.val-d.val) * natFourOriginalCOMCoefficientFiber D d a b *
          (∫ R, ip
            (natFourRemoval G theta (natFourRelativeColumn (natFourRelativeDegreeAt D d) a)
              (natFourRelativeColumn_bihomogeneous (natFourRelativeDegreeAt D d) a).1 0 R f)
            (natFourRemoval G theta (natFourRelativeColumn (natFourRelativeDegreeAt D d) b)
              (natFourRelativeColumn_bihomogeneous (natFourRelativeDegreeAt D d) b).1 0 R f)
            ∂cellMeasure G 4)).re := by
  simpa only [natFourOriginalCOMCoefficientFiber, Matrix.submatrix_apply,
    natFourCOMFiberIndex] using
    (matrix_COM_fibers G theta (N := natFourOccupationDimension D)
    D.val (natFourRelativeDimensionAt D) (natFourCOMIndexEquiv D)
    (fun d => natFourRelativeColumn (natFourRelativeDegreeAt D d))
    (fun d a => (natFourRelativeColumn_bihomogeneous (natFourRelativeDegreeAt D d) a).1)
    (fun d a => natFourRelativeColumn_lower (natFourRelativeDegreeAt D d) a)
    (natFourCompleteCOMFamily D) (fun i => (natFourCompleteCOMFamily_bihomogeneous D i).1)
    (natFourCompleteCOMFamily_labelled D) (natFourOriginalCOMRankCoefficient D) f)

#print axioms originalCOMMatrixCell_eq_relative_fibers
end TorusLean.Shared.BosonNatFourOriginalRelativeTrace
