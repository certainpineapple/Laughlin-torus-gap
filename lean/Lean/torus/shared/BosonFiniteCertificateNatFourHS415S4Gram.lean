import torus.shared.BosonFiniteCertificateNatFourHS415S4GramARows0
import torus.shared.BosonFiniteCertificateNatFourHS415S4GramWRows0
import torus.shared.BosonFiniteCertificateNatFourHS415S4GramVRows0
import torus.shared.BosonFiniteCertificateNatFourHS415S4GramYRows0
import torus.shared.BosonFiniteCertificateNatFourHS415S4GramYRows1
import torus.shared.BosonFiniteCertificateNatFourHS415S4GramYRows2
import torus.shared.BosonFiniteCertificateNatFourHS415S4GramYRows3
import torus.shared.BosonFiniteCertificateNatFourHS415S4GramFRows0

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

private theorem f415hs_shape (a : Fin 54) :
    (f415basis a).length=4 ∧ (f415basis a).sum=15 := by
  apply natFourBasis_shape 15
  rw [← f415_basis_enumeration]
  exact List.mem_ofFn.mpr ⟨a,rfl⟩

theorem f415_S4_amplitude_gram_check :
    natFourS4AmplitudeGram 15 f415S4Amplitudes=f415rawS4Form := by
  have hA : natFourIntegerMatrix 1 f415S4GramAInt = f415S4Amplitudes := by
    ext a b
    have ha := a.isLt
    exact f415_S4Gram_hA_rows_0 a (by omega) (by omega) b
  have hW : natFourIntegerMatrix (2^17) f415S4GramWInt = (Matrix.diagonal (fun p : Fin 16 => natFourPairWeight p.val (15-p.val))) := by
    ext a b
    have ha := a.isLt
    exact f415_S4Gram_hW_rows_0 a (by omega) (by omega) b
  have hV : f415S4GramWInt*f415S4GramAInt = f415S4GramVInt := by
    ext a b
    have ha := a.isLt
    exact f415_S4Gram_hV_rows_0 a (by omega) (by omega) b
  have hY : f415S4GramAIntᵀ*f415S4GramVInt = f415S4GramYInt := by
    ext a b
    have ha := a.isLt
    by_cases h0 : a.val < 16
    · exact f415_S4Gram_hY_rows_0 a (by omega) h0 b
    by_cases h1 : a.val < 32
    · exact f415_S4Gram_hY_rows_1 a (by omega) h1 b
    by_cases h2 : a.val < 48
    · exact f415_S4Gram_hY_rows_2 a (by omega) h2 b
    exact f415_S4Gram_hY_rows_3 a (by omega) (by omega) b
  have hF : natFourIntegerMatrix (1*((2^17)*1)) f415S4GramYInt = f415rawS4Form := by
    ext a b
    have ha := a.isLt
    exact f415_S4Gram_hF_rows_0 a (by omega) (by omega) b
  unfold natFourS4AmplitudeGram
  rw [← hA, ← hW, ← natFourIntegerMatrix_transpose,
    natFourIntegerMatrix_mul, natFourIntegerMatrix_mul, hV, hY]
  exact hF

theorem f415_actual_raw_S4_matrix (x y : Fin 54 → ℂ) :
    natOccupationInner (natFourWordBlock f415basis x)
      (canonicalNatFourS4 (natFourWordBlock f415basis y))=
      star x ⬝ᵥ (complexify f415rawS4Form *ᵥ y) :=
  canonicalNatFourS4_amplitude_matrix_form 15 f415basis
    (fun a => (f415hs_shape a).1) (fun a => (f415hs_shape a).2)
    f415S4Amplitudes f415_S4_amplitudes_check f415rawS4Form f415_S4_amplitude_gram_check x y

#print axioms f415_S4_amplitude_gram_check
#print axioms f415_actual_raw_S4_matrix
end TorusLean.BosonFiniteCertificate
