import torus.shared.BosonFiniteCertificateNatFourHS414Data
import torus.shared.BosonFiniteCertificateNatFourHS414HRows0
import torus.shared.BosonFiniteCertificateNatFourHS414HRows1
import torus.shared.BosonFiniteCertificateNatFourHS414HRows2
import torus.shared.BosonFiniteCertificateNatFourHS414HRows3
import torus.shared.BosonFiniteCertificateNatFourHS414HRows4
import torus.shared.BosonFiniteCertificateNatFourHS414HRows5
import torus.shared.BosonFiniteCertificateNatFourHS414HRows6
import torus.shared.BosonFiniteCertificateNatFourHS414HRows7

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2
open Matrix
open scoped BigOperators

private theorem f414hs_shape (a : Fin 47) :
    (f414basis a).length=4 ∧ (f414basis a).sum=14 := by
  apply natFourBasis_shape 14
  rw [← f414_basis_enumeration]
  exact List.mem_ofFn.mpr ⟨a,rfl⟩

theorem f414_raw_H_matrix_check : ∀ a b : Fin 47,
    natFourHWordForm 14 (f414basis a) (f414basis b)=f414rawHForm a b := by
  intro a b
  rw [← natFourHWordFormSparse_eq]
  fin_cases a
  · exact f414_H_rows_0 0 b (by decide) (by decide)
  · exact f414_H_rows_0 1 b (by decide) (by decide)
  · exact f414_H_rows_0 2 b (by decide) (by decide)
  · exact f414_H_rows_0 3 b (by decide) (by decide)
  · exact f414_H_rows_0 4 b (by decide) (by decide)
  · exact f414_H_rows_0 5 b (by decide) (by decide)
  · exact f414_H_rows_1 6 b (by decide) (by decide)
  · exact f414_H_rows_1 7 b (by decide) (by decide)
  · exact f414_H_rows_1 8 b (by decide) (by decide)
  · exact f414_H_rows_1 9 b (by decide) (by decide)
  · exact f414_H_rows_1 10 b (by decide) (by decide)
  · exact f414_H_rows_1 11 b (by decide) (by decide)
  · exact f414_H_rows_2 12 b (by decide) (by decide)
  · exact f414_H_rows_2 13 b (by decide) (by decide)
  · exact f414_H_rows_2 14 b (by decide) (by decide)
  · exact f414_H_rows_2 15 b (by decide) (by decide)
  · exact f414_H_rows_2 16 b (by decide) (by decide)
  · exact f414_H_rows_2 17 b (by decide) (by decide)
  · exact f414_H_rows_3 18 b (by decide) (by decide)
  · exact f414_H_rows_3 19 b (by decide) (by decide)
  · exact f414_H_rows_3 20 b (by decide) (by decide)
  · exact f414_H_rows_3 21 b (by decide) (by decide)
  · exact f414_H_rows_3 22 b (by decide) (by decide)
  · exact f414_H_rows_3 23 b (by decide) (by decide)
  · exact f414_H_rows_4 24 b (by decide) (by decide)
  · exact f414_H_rows_4 25 b (by decide) (by decide)
  · exact f414_H_rows_4 26 b (by decide) (by decide)
  · exact f414_H_rows_4 27 b (by decide) (by decide)
  · exact f414_H_rows_4 28 b (by decide) (by decide)
  · exact f414_H_rows_4 29 b (by decide) (by decide)
  · exact f414_H_rows_5 30 b (by decide) (by decide)
  · exact f414_H_rows_5 31 b (by decide) (by decide)
  · exact f414_H_rows_5 32 b (by decide) (by decide)
  · exact f414_H_rows_5 33 b (by decide) (by decide)
  · exact f414_H_rows_5 34 b (by decide) (by decide)
  · exact f414_H_rows_5 35 b (by decide) (by decide)
  · exact f414_H_rows_6 36 b (by decide) (by decide)
  · exact f414_H_rows_6 37 b (by decide) (by decide)
  · exact f414_H_rows_6 38 b (by decide) (by decide)
  · exact f414_H_rows_6 39 b (by decide) (by decide)
  · exact f414_H_rows_6 40 b (by decide) (by decide)
  · exact f414_H_rows_6 41 b (by decide) (by decide)
  · exact f414_H_rows_7 42 b (by decide) (by decide)
  · exact f414_H_rows_7 43 b (by decide) (by decide)
  · exact f414_H_rows_7 44 b (by decide) (by decide)
  · exact f414_H_rows_7 45 b (by decide) (by decide)
  · exact f414_H_rows_7 46 b (by decide) (by decide)


theorem f414_actual_raw_H_matrix (x y : Fin 47 → ℂ) :
    natOccupationInner (natFourWordBlock f414basis x)
      (canonicalPairHamiltonianNat (natFourWordBlock f414basis y))=
      star x ⬝ᵥ (complexify f414rawHForm *ᵥ y) :=
  canonicalNatFourH_matrix_form 14 f414basis (fun a => (f414hs_shape a).2)
    f414rawHForm f414_raw_H_matrix_check x y

#print axioms f414_raw_H_matrix_check
#print axioms f414_actual_raw_H_matrix
end TorusLean.BosonFiniteCertificate
