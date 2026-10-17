import torus.shared.BosonFiniteCertificateNatFourHS412Data
import torus.shared.BosonFiniteCertificateNatFourHS412HRows0
import torus.shared.BosonFiniteCertificateNatFourHS412HRows1
import torus.shared.BosonFiniteCertificateNatFourHS412HRows2
import torus.shared.BosonFiniteCertificateNatFourHS412HRows3
import torus.shared.BosonFiniteCertificateNatFourHS412HRows4
import torus.shared.BosonFiniteCertificateNatFourHS412HRows5

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2
open Matrix
open scoped BigOperators

private theorem f412hs_shape (a : Fin 34) :
    (f412basis a).length=4 ∧ (f412basis a).sum=12 := by
  apply natFourBasis_shape 12
  rw [← f412_basis_enumeration]
  exact List.mem_ofFn.mpr ⟨a,rfl⟩

theorem f412_raw_H_matrix_check : ∀ a b : Fin 34,
    natFourHWordForm 12 (f412basis a) (f412basis b)=f412rawHForm a b := by
  intro a b
  rw [← natFourHWordFormSparse_eq]
  fin_cases a
  · exact f412_H_rows_0 0 b (by decide) (by decide)
  · exact f412_H_rows_0 1 b (by decide) (by decide)
  · exact f412_H_rows_0 2 b (by decide) (by decide)
  · exact f412_H_rows_0 3 b (by decide) (by decide)
  · exact f412_H_rows_0 4 b (by decide) (by decide)
  · exact f412_H_rows_0 5 b (by decide) (by decide)
  · exact f412_H_rows_1 6 b (by decide) (by decide)
  · exact f412_H_rows_1 7 b (by decide) (by decide)
  · exact f412_H_rows_1 8 b (by decide) (by decide)
  · exact f412_H_rows_1 9 b (by decide) (by decide)
  · exact f412_H_rows_1 10 b (by decide) (by decide)
  · exact f412_H_rows_1 11 b (by decide) (by decide)
  · exact f412_H_rows_2 12 b (by decide) (by decide)
  · exact f412_H_rows_2 13 b (by decide) (by decide)
  · exact f412_H_rows_2 14 b (by decide) (by decide)
  · exact f412_H_rows_2 15 b (by decide) (by decide)
  · exact f412_H_rows_2 16 b (by decide) (by decide)
  · exact f412_H_rows_2 17 b (by decide) (by decide)
  · exact f412_H_rows_3 18 b (by decide) (by decide)
  · exact f412_H_rows_3 19 b (by decide) (by decide)
  · exact f412_H_rows_3 20 b (by decide) (by decide)
  · exact f412_H_rows_3 21 b (by decide) (by decide)
  · exact f412_H_rows_3 22 b (by decide) (by decide)
  · exact f412_H_rows_3 23 b (by decide) (by decide)
  · exact f412_H_rows_4 24 b (by decide) (by decide)
  · exact f412_H_rows_4 25 b (by decide) (by decide)
  · exact f412_H_rows_4 26 b (by decide) (by decide)
  · exact f412_H_rows_4 27 b (by decide) (by decide)
  · exact f412_H_rows_4 28 b (by decide) (by decide)
  · exact f412_H_rows_4 29 b (by decide) (by decide)
  · exact f412_H_rows_5 30 b (by decide) (by decide)
  · exact f412_H_rows_5 31 b (by decide) (by decide)
  · exact f412_H_rows_5 32 b (by decide) (by decide)
  · exact f412_H_rows_5 33 b (by decide) (by decide)


theorem f412_actual_raw_H_matrix (x y : Fin 34 → ℂ) :
    natOccupationInner (natFourWordBlock f412basis x)
      (canonicalPairHamiltonianNat (natFourWordBlock f412basis y))=
      star x ⬝ᵥ (complexify f412rawHForm *ᵥ y) :=
  canonicalNatFourH_matrix_form 12 f412basis (fun a => (f412hs_shape a).2)
    f412rawHForm f412_raw_H_matrix_check x y

#print axioms f412_raw_H_matrix_check
#print axioms f412_actual_raw_H_matrix
end TorusLean.BosonFiniteCertificate
