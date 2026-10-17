import torus.shared.BosonFiniteCertificateNatFourCOMOriginalCoefficient
import torus.shared.BosonFiniteCertificateNatFourCOMTraceCoefficientCore

/-! Restrict the genuine complete COM coefficient to one original relative
fiber. These are exact rectangular matrix operations on the original columns;
no new full-size inverse or orthogonal-basis hypothesis is used. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2
open TorusLean.Shared.BosonFiniteCertificateRealization
open Matrix
open scoped BigOperators

def natFourCOMFiberIndex (D : Fin 17) (d : Fin (D.val+1))
    (a : Fin (natFourRelativeDimensionAt D d)) : Fin (natFourOccupationDimension D) :=
  (natFourCOMIndexEquiv D).symm ⟨d,a⟩

def natFourOriginalCOMFiberForm (D : Fin 17) (d : Fin (D.val+1)) :
    Matrix (Fin (natFourRelativeDimensionAt D d)) (Fin (natFourRelativeDimensionAt D d)) ℚ :=
  (natFourCOMFiberCoordinates D d)ᵀ*natFourOriginalRawFormMatrix D*natFourCOMFiberCoordinates D d

def natFourOriginalCOMCoefficientFiber (D : Fin 17) (d : Fin (D.val+1)) :
    Matrix (Fin (natFourRelativeDimensionAt D d)) (Fin (natFourRelativeDimensionAt D d)) ℂ :=
  (natFourOriginalCOMRankCoefficient D).submatrix
    (natFourCOMFiberIndex D d) (natFourCOMFiberIndex D d)

theorem natFour_matrix_compression_submatrix {n m r : ℕ}
    (S : Matrix (Fin n) (Fin m) ℚ) (M : Matrix (Fin n) (Fin n) ℚ) (e : Fin r → Fin m) :
    (Sᵀ*M*S).submatrix e e=(S.submatrix id e)ᵀ*M*(S.submatrix id e) := by
  rw [Matrix.submatrix_mul (Sᵀ*M) S e id e Function.bijective_id,
    Matrix.submatrix_mul Sᵀ M e id id Function.bijective_id]
  rfl

theorem natFourCompleteCOMCoordinates_fiber (D : Fin 17) (d : Fin (D.val+1)) :
    (natFourCompleteCOMCoordinates D).submatrix id (natFourCOMFiberIndex D d)=
      natFourCOMFiberCoordinates D d := by
  ext i a
  exact congrArg (fun z : Σ d : Fin (D.val+1), Fin (natFourRelativeDimensionAt D d) =>
    natFourCOMFiberCoordinates D z.1 i z.2)
    ((natFourCOMIndexEquiv D).apply_symm_apply ⟨d,a⟩)

theorem natFourCOMSourceFormMatrix_fiber (D : Fin 17) (d : Fin (D.val+1)) :
    (natFourCOMSourceFormMatrix D (natFourOriginalRawFormMatrix D)).submatrix
      (natFourCOMFiberIndex D d) (natFourCOMFiberIndex D d)=natFourOriginalCOMFiberForm D d := by
  rw [natFourCOMSourceFormMatrix,natFour_matrix_compression_submatrix,
    natFourCompleteCOMCoordinates_fiber]
  rfl

/-- Exact diagonal fiber consumed by the physical unnormalized COM trace.
Its w^-2 is independent of the trace's w/2 factor. -/
theorem natFourOriginalCOMCoefficientFiber_eq (D : Fin 17) (d : Fin (D.val+1)) :
    natFourOriginalCOMCoefficientFiber D d =
      ((natFourCOMWeight (D.val-d.val))⁻¹*(natFourCOMWeight (D.val-d.val))⁻¹) •
        inverseGramCoefficient
          (complexify (natFourRelativeGramInverse (natFourRelativeDegreeAt D d)))
          (complexify (natFourOriginalCOMFiberForm D d)) := by
  have hE : (complexify (natFourCOMSourceFormMatrix D (natFourOriginalRawFormMatrix D))).submatrix
      (natFourCOMFiberIndex D d) (natFourCOMFiberIndex D d)=
        complexify (natFourOriginalCOMFiberForm D d) := by
    change complexify ((natFourCOMSourceFormMatrix D (natFourOriginalRawFormMatrix D)).submatrix
      (natFourCOMFiberIndex D d) (natFourCOMFiberIndex D d))= _
    rw [natFourCOMSourceFormMatrix_fiber]
  let J : ∀ e : Fin (D.val+1),
      Matrix (Fin (natFourRelativeDimensionAt D e))
        (Fin (natFourRelativeDimensionAt D e)) ℂ :=
    fun e => (natFourCOMWeight (D.val-e.val))⁻¹ •
      complexify (natFourRelativeGramInverse (natFourRelativeDegreeAt D e))
  let E := complexify (natFourCOMSourceFormMatrix D (natFourOriginalRawFormMatrix D))
  have hf := natFour_block_inverse_coefficient_reindexed_fiber
    (natFourRelativeDimensionAt D) J E (natFourCOMIndexEquiv D) d
  calc
    natFourOriginalCOMCoefficientFiber D d =
        inverseGramCoefficient (J d)
          (E.submatrix (natFourCOMFiberIndex D d) (natFourCOMFiberIndex D d)) := hf
    _ = inverseGramCoefficient (J d) (complexify (natFourOriginalCOMFiberForm D d)) :=
      congrArg (inverseGramCoefficient (J d)) hE
    _ = _ := by
      have hs (r : ℕ) (c : ℂ) (A B : Matrix (Fin r) (Fin r) ℂ) :
          inverseGramCoefficient (c • A) B = (c*c) • inverseGramCoefficient A B := by
        simp only [inverseGramCoefficient, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
      exact hs (natFourRelativeDimensionAt D d) (natFourCOMWeight (D.val-d.val))⁻¹
        (complexify (natFourRelativeGramInverse (natFourRelativeDegreeAt D d)))
        (complexify (natFourOriginalCOMFiberForm D d))

#print axioms natFour_matrix_compression_submatrix
#print axioms natFourCompleteCOMCoordinates_fiber
#print axioms natFourCOMSourceFormMatrix_fiber
#print axioms natFourOriginalCOMCoefficientFiber_eq
end TorusLean.BosonFiniteCertificate
