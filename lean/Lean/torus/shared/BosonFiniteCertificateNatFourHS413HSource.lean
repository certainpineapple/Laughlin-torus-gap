import torus.shared.BosonFiniteCertificateNatFourHS413Data
import torus.shared.BosonFiniteCertificateNatFourHS413HRows0
import torus.shared.BosonFiniteCertificateNatFourHS413HRows1
import torus.shared.BosonFiniteCertificateNatFourHS413HRows2
import torus.shared.BosonFiniteCertificateNatFourHS413HRows3
import torus.shared.BosonFiniteCertificateNatFourHS413HRows4
import torus.shared.BosonFiniteCertificateNatFourHS413HRows5
import torus.shared.BosonFiniteCertificateNatFourHS413HRows6

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2
open Matrix
open scoped BigOperators

private theorem f413hs_shape (a : Fin 39) :
    (f413basis a).length=4 ∧ (f413basis a).sum=13 := by
  apply natFourBasis_shape 13
  rw [← f413_basis_enumeration]
  exact List.mem_ofFn.mpr ⟨a,rfl⟩

theorem f413_raw_H_matrix_check : ∀ a b : Fin 39,
    natFourHWordForm 13 (f413basis a) (f413basis b)=f413rawHForm a b := by
  intro a b
  rw [← natFourHWordFormSparse_eq]
  fin_cases a
  · exact f413_H_rows_0 0 b (by decide) (by decide)
  · exact f413_H_rows_0 1 b (by decide) (by decide)
  · exact f413_H_rows_0 2 b (by decide) (by decide)
  · exact f413_H_rows_0 3 b (by decide) (by decide)
  · exact f413_H_rows_0 4 b (by decide) (by decide)
  · exact f413_H_rows_0 5 b (by decide) (by decide)
  · exact f413_H_rows_1 6 b (by decide) (by decide)
  · exact f413_H_rows_1 7 b (by decide) (by decide)
  · exact f413_H_rows_1 8 b (by decide) (by decide)
  · exact f413_H_rows_1 9 b (by decide) (by decide)
  · exact f413_H_rows_1 10 b (by decide) (by decide)
  · exact f413_H_rows_1 11 b (by decide) (by decide)
  · exact f413_H_rows_2 12 b (by decide) (by decide)
  · exact f413_H_rows_2 13 b (by decide) (by decide)
  · exact f413_H_rows_2 14 b (by decide) (by decide)
  · exact f413_H_rows_2 15 b (by decide) (by decide)
  · exact f413_H_rows_2 16 b (by decide) (by decide)
  · exact f413_H_rows_2 17 b (by decide) (by decide)
  · exact f413_H_rows_3 18 b (by decide) (by decide)
  · exact f413_H_rows_3 19 b (by decide) (by decide)
  · exact f413_H_rows_3 20 b (by decide) (by decide)
  · exact f413_H_rows_3 21 b (by decide) (by decide)
  · exact f413_H_rows_3 22 b (by decide) (by decide)
  · exact f413_H_rows_3 23 b (by decide) (by decide)
  · exact f413_H_rows_4 24 b (by decide) (by decide)
  · exact f413_H_rows_4 25 b (by decide) (by decide)
  · exact f413_H_rows_4 26 b (by decide) (by decide)
  · exact f413_H_rows_4 27 b (by decide) (by decide)
  · exact f413_H_rows_4 28 b (by decide) (by decide)
  · exact f413_H_rows_4 29 b (by decide) (by decide)
  · exact f413_H_rows_5 30 b (by decide) (by decide)
  · exact f413_H_rows_5 31 b (by decide) (by decide)
  · exact f413_H_rows_5 32 b (by decide) (by decide)
  · exact f413_H_rows_5 33 b (by decide) (by decide)
  · exact f413_H_rows_5 34 b (by decide) (by decide)
  · exact f413_H_rows_5 35 b (by decide) (by decide)
  · exact f413_H_rows_6 36 b (by decide) (by decide)
  · exact f413_H_rows_6 37 b (by decide) (by decide)
  · exact f413_H_rows_6 38 b (by decide) (by decide)


theorem f413_actual_raw_H_matrix (x y : Fin 39 → ℂ) :
    natOccupationInner (natFourWordBlock f413basis x)
      (canonicalPairHamiltonianNat (natFourWordBlock f413basis y))=
      star x ⬝ᵥ (complexify f413rawHForm *ᵥ y) :=
  canonicalNatFourH_matrix_form 13 f413basis (fun a => (f413hs_shape a).2)
    f413rawHForm f413_raw_H_matrix_check x y

#print axioms f413_raw_H_matrix_check
#print axioms f413_actual_raw_H_matrix
end TorusLean.BosonFiniteCertificate
