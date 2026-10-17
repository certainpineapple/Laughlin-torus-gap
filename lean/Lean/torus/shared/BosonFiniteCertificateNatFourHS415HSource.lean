import torus.shared.BosonFiniteCertificateNatFourHS415Data
import torus.shared.BosonFiniteCertificateNatFourHS415HRows0
import torus.shared.BosonFiniteCertificateNatFourHS415HRows1
import torus.shared.BosonFiniteCertificateNatFourHS415HRows2
import torus.shared.BosonFiniteCertificateNatFourHS415HRows3
import torus.shared.BosonFiniteCertificateNatFourHS415HRows4
import torus.shared.BosonFiniteCertificateNatFourHS415HRows5
import torus.shared.BosonFiniteCertificateNatFourHS415HRows6
import torus.shared.BosonFiniteCertificateNatFourHS415HRows7
import torus.shared.BosonFiniteCertificateNatFourHS415HRows8
import torus.shared.BosonFiniteCertificateNatFourHS415HRows9
import torus.shared.BosonFiniteCertificateNatFourHS415HRows10
import torus.shared.BosonFiniteCertificateNatFourHS415HRows11
import torus.shared.BosonFiniteCertificateNatFourHS415HRows12
import torus.shared.BosonFiniteCertificateNatFourHS415HRows13

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2
open Matrix
open scoped BigOperators

private theorem f415hs_shape (a : Fin 54) :
    (f415basis a).length=4 ∧ (f415basis a).sum=15 := by
  apply natFourBasis_shape 15
  rw [← f415_basis_enumeration]
  exact List.mem_ofFn.mpr ⟨a,rfl⟩

theorem f415_raw_H_matrix_check : ∀ a b : Fin 54,
    natFourHWordForm 15 (f415basis a) (f415basis b)=f415rawHForm a b := by
  intro a b
  rw [← natFourHWordFormSparse_eq]
  fin_cases a
  · exact f415_H_rows_0 0 b (by decide) (by decide)
  · exact f415_H_rows_0 1 b (by decide) (by decide)
  · exact f415_H_rows_0 2 b (by decide) (by decide)
  · exact f415_H_rows_0 3 b (by decide) (by decide)
  · exact f415_H_rows_1 4 b (by decide) (by decide)
  · exact f415_H_rows_1 5 b (by decide) (by decide)
  · exact f415_H_rows_1 6 b (by decide) (by decide)
  · exact f415_H_rows_1 7 b (by decide) (by decide)
  · exact f415_H_rows_2 8 b (by decide) (by decide)
  · exact f415_H_rows_2 9 b (by decide) (by decide)
  · exact f415_H_rows_2 10 b (by decide) (by decide)
  · exact f415_H_rows_2 11 b (by decide) (by decide)
  · exact f415_H_rows_3 12 b (by decide) (by decide)
  · exact f415_H_rows_3 13 b (by decide) (by decide)
  · exact f415_H_rows_3 14 b (by decide) (by decide)
  · exact f415_H_rows_3 15 b (by decide) (by decide)
  · exact f415_H_rows_4 16 b (by decide) (by decide)
  · exact f415_H_rows_4 17 b (by decide) (by decide)
  · exact f415_H_rows_4 18 b (by decide) (by decide)
  · exact f415_H_rows_4 19 b (by decide) (by decide)
  · exact f415_H_rows_5 20 b (by decide) (by decide)
  · exact f415_H_rows_5 21 b (by decide) (by decide)
  · exact f415_H_rows_5 22 b (by decide) (by decide)
  · exact f415_H_rows_5 23 b (by decide) (by decide)
  · exact f415_H_rows_6 24 b (by decide) (by decide)
  · exact f415_H_rows_6 25 b (by decide) (by decide)
  · exact f415_H_rows_6 26 b (by decide) (by decide)
  · exact f415_H_rows_6 27 b (by decide) (by decide)
  · exact f415_H_rows_7 28 b (by decide) (by decide)
  · exact f415_H_rows_7 29 b (by decide) (by decide)
  · exact f415_H_rows_7 30 b (by decide) (by decide)
  · exact f415_H_rows_7 31 b (by decide) (by decide)
  · exact f415_H_rows_8 32 b (by decide) (by decide)
  · exact f415_H_rows_8 33 b (by decide) (by decide)
  · exact f415_H_rows_8 34 b (by decide) (by decide)
  · exact f415_H_rows_8 35 b (by decide) (by decide)
  · exact f415_H_rows_9 36 b (by decide) (by decide)
  · exact f415_H_rows_9 37 b (by decide) (by decide)
  · exact f415_H_rows_9 38 b (by decide) (by decide)
  · exact f415_H_rows_9 39 b (by decide) (by decide)
  · exact f415_H_rows_10 40 b (by decide) (by decide)
  · exact f415_H_rows_10 41 b (by decide) (by decide)
  · exact f415_H_rows_10 42 b (by decide) (by decide)
  · exact f415_H_rows_10 43 b (by decide) (by decide)
  · exact f415_H_rows_11 44 b (by decide) (by decide)
  · exact f415_H_rows_11 45 b (by decide) (by decide)
  · exact f415_H_rows_11 46 b (by decide) (by decide)
  · exact f415_H_rows_11 47 b (by decide) (by decide)
  · exact f415_H_rows_12 48 b (by decide) (by decide)
  · exact f415_H_rows_12 49 b (by decide) (by decide)
  · exact f415_H_rows_12 50 b (by decide) (by decide)
  · exact f415_H_rows_12 51 b (by decide) (by decide)
  · exact f415_H_rows_13 52 b (by decide) (by decide)
  · exact f415_H_rows_13 53 b (by decide) (by decide)


theorem f415_actual_raw_H_matrix (x y : Fin 54 → ℂ) :
    natOccupationInner (natFourWordBlock f415basis x)
      (canonicalPairHamiltonianNat (natFourWordBlock f415basis y))=
      star x ⬝ᵥ (complexify f415rawHForm *ᵥ y) :=
  canonicalNatFourH_matrix_form 15 f415basis (fun a => (f415hs_shape a).2)
    f415rawHForm f415_raw_H_matrix_check x y

#print axioms f415_raw_H_matrix_check
#print axioms f415_actual_raw_H_matrix
end TorusLean.BosonFiniteCertificate
