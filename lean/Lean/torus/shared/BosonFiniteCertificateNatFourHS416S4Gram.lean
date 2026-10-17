import torus.shared.BosonFiniteCertificateNatFourHS416S4GramARows0
import torus.shared.BosonFiniteCertificateNatFourHS416S4GramWRows0
import torus.shared.BosonFiniteCertificateNatFourHS416S4GramVRows0
import torus.shared.BosonFiniteCertificateNatFourHS416S4GramYRows0
import torus.shared.BosonFiniteCertificateNatFourHS416S4GramYRows1
import torus.shared.BosonFiniteCertificateNatFourHS416S4GramYRows2
import torus.shared.BosonFiniteCertificateNatFourHS416S4GramYRows3
import torus.shared.BosonFiniteCertificateNatFourHS416S4GramFRows0

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

private theorem f416hs_shape (a : Fin 64) :
    (f416basis a).length=4 ∧ (f416basis a).sum=16 := by
  apply natFourBasis_shape 16
  rw [← f416_basis_enumeration]
  exact List.mem_ofFn.mpr ⟨a,rfl⟩

theorem f416_S4_amplitude_gram_check :
    natFourS4AmplitudeGram 16 f416S4Amplitudes=f416rawS4Form := by
  have hA : natFourIntegerMatrix 1 f416S4GramAInt = f416S4Amplitudes := by
    ext a b
    have ha := a.isLt
    exact f416_S4Gram_hA_rows_0 a (by omega) (by omega) b
  have hW : natFourIntegerMatrix (2^18) f416S4GramWInt = (Matrix.diagonal (fun p : Fin 17 => natFourPairWeight p.val (16-p.val))) := by
    ext a b
    have ha := a.isLt
    exact f416_S4Gram_hW_rows_0 a (by omega) (by omega) b
  have hV : f416S4GramWInt*f416S4GramAInt = f416S4GramVInt := by
    ext a b
    have ha := a.isLt
    exact f416_S4Gram_hV_rows_0 a (by omega) (by omega) b
  have hY : f416S4GramAIntᵀ*f416S4GramVInt = f416S4GramYInt := by
    ext a b
    have ha := a.isLt
    by_cases h0 : a.val < 16
    · exact f416_S4Gram_hY_rows_0 a (by omega) h0 b
    by_cases h1 : a.val < 32
    · exact f416_S4Gram_hY_rows_1 a (by omega) h1 b
    by_cases h2 : a.val < 48
    · exact f416_S4Gram_hY_rows_2 a (by omega) h2 b
    exact f416_S4Gram_hY_rows_3 a (by omega) (by omega) b
  have hF : natFourIntegerMatrix (1*((2^18)*1)) f416S4GramYInt = f416rawS4Form := by
    ext a b
    have ha := a.isLt
    exact f416_S4Gram_hF_rows_0 a (by omega) (by omega) b
  unfold natFourS4AmplitudeGram
  rw [← hA, ← hW, ← natFourIntegerMatrix_transpose,
    natFourIntegerMatrix_mul, natFourIntegerMatrix_mul, hV, hY]
  exact hF

theorem f416_actual_raw_S4_matrix (x y : Fin 64 → ℂ) :
    natOccupationInner (natFourWordBlock f416basis x)
      (canonicalNatFourS4 (natFourWordBlock f416basis y))=
      star x ⬝ᵥ (complexify f416rawS4Form *ᵥ y) :=
  canonicalNatFourS4_amplitude_matrix_form 16 f416basis
    (fun a => (f416hs_shape a).1) (fun a => (f416hs_shape a).2)
    f416S4Amplitudes f416_S4_amplitudes_check f416rawS4Form f416_S4_amplitude_gram_check x y

#print axioms f416_S4_amplitude_gram_check
#print axioms f416_actual_raw_S4_matrix
end TorusLean.BosonFiniteCertificate
