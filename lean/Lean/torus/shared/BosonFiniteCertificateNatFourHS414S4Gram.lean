import torus.shared.BosonFiniteCertificateNatFourHS414S4GramARows0
import torus.shared.BosonFiniteCertificateNatFourHS414S4GramWRows0
import torus.shared.BosonFiniteCertificateNatFourHS414S4GramVRows0
import torus.shared.BosonFiniteCertificateNatFourHS414S4GramYRows0
import torus.shared.BosonFiniteCertificateNatFourHS414S4GramYRows1
import torus.shared.BosonFiniteCertificateNatFourHS414S4GramYRows2
import torus.shared.BosonFiniteCertificateNatFourHS414S4GramFRows0

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

private theorem f414hs_shape (a : Fin 47) :
    (f414basis a).length=4 ∧ (f414basis a).sum=14 := by
  apply natFourBasis_shape 14
  rw [← f414_basis_enumeration]
  exact List.mem_ofFn.mpr ⟨a,rfl⟩

theorem f414_S4_amplitude_gram_check :
    natFourS4AmplitudeGram 14 f414S4Amplitudes=f414rawS4Form := by
  have hA : natFourIntegerMatrix 1 f414S4GramAInt = f414S4Amplitudes := by
    ext a b
    have ha := a.isLt
    exact f414_S4Gram_hA_rows_0 a (by omega) (by omega) b
  have hW : natFourIntegerMatrix (2^16) f414S4GramWInt = (Matrix.diagonal (fun p : Fin 15 => natFourPairWeight p.val (14-p.val))) := by
    ext a b
    have ha := a.isLt
    exact f414_S4Gram_hW_rows_0 a (by omega) (by omega) b
  have hV : f414S4GramWInt*f414S4GramAInt = f414S4GramVInt := by
    ext a b
    have ha := a.isLt
    exact f414_S4Gram_hV_rows_0 a (by omega) (by omega) b
  have hY : f414S4GramAIntᵀ*f414S4GramVInt = f414S4GramYInt := by
    ext a b
    have ha := a.isLt
    by_cases h0 : a.val < 16
    · exact f414_S4Gram_hY_rows_0 a (by omega) h0 b
    by_cases h1 : a.val < 32
    · exact f414_S4Gram_hY_rows_1 a (by omega) h1 b
    exact f414_S4Gram_hY_rows_2 a (by omega) (by omega) b
  have hF : natFourIntegerMatrix (1*((2^16)*1)) f414S4GramYInt = f414rawS4Form := by
    ext a b
    have ha := a.isLt
    exact f414_S4Gram_hF_rows_0 a (by omega) (by omega) b
  unfold natFourS4AmplitudeGram
  rw [← hA, ← hW, ← natFourIntegerMatrix_transpose,
    natFourIntegerMatrix_mul, natFourIntegerMatrix_mul, hV, hY]
  exact hF

theorem f414_actual_raw_S4_matrix (x y : Fin 47 → ℂ) :
    natOccupationInner (natFourWordBlock f414basis x)
      (canonicalNatFourS4 (natFourWordBlock f414basis y))=
      star x ⬝ᵥ (complexify f414rawS4Form *ᵥ y) :=
  canonicalNatFourS4_amplitude_matrix_form 14 f414basis
    (fun a => (f414hs_shape a).1) (fun a => (f414hs_shape a).2)
    f414S4Amplitudes f414_S4_amplitudes_check f414rawS4Form f414_S4_amplitude_gram_check x y

#print axioms f414_S4_amplitude_gram_check
#print axioms f414_actual_raw_S4_matrix
end TorusLean.BosonFiniteCertificate
