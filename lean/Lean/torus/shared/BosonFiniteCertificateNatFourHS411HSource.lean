import torus.shared.BosonFiniteCertificateNatFourHS411Data
import torus.shared.BosonFiniteCertificateNatFourHS411HRows0
import torus.shared.BosonFiniteCertificateNatFourHS411HRows1
import torus.shared.BosonFiniteCertificateNatFourHS411HRows2
import torus.shared.BosonFiniteCertificateNatFourHS411HRows3
import torus.shared.BosonFiniteCertificateNatFourHS411HRows4

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2
open Matrix
open scoped BigOperators

private theorem f411hs_shape (a : Fin 27) :
    (f411basis a).length=4 ∧ (f411basis a).sum=11 := by
  apply natFourBasis_shape 11
  rw [← f411_basis_enumeration]
  exact List.mem_ofFn.mpr ⟨a,rfl⟩

theorem f411_raw_H_matrix_check : ∀ a b : Fin 27,
    natFourHWordForm 11 (f411basis a) (f411basis b)=f411rawHForm a b := by
  intro a b
  rw [← natFourHWordFormSparse_eq]
  fin_cases a
  · exact f411_H_rows_0 0 b (by decide) (by decide)
  · exact f411_H_rows_0 1 b (by decide) (by decide)
  · exact f411_H_rows_0 2 b (by decide) (by decide)
  · exact f411_H_rows_0 3 b (by decide) (by decide)
  · exact f411_H_rows_0 4 b (by decide) (by decide)
  · exact f411_H_rows_0 5 b (by decide) (by decide)
  · exact f411_H_rows_1 6 b (by decide) (by decide)
  · exact f411_H_rows_1 7 b (by decide) (by decide)
  · exact f411_H_rows_1 8 b (by decide) (by decide)
  · exact f411_H_rows_1 9 b (by decide) (by decide)
  · exact f411_H_rows_1 10 b (by decide) (by decide)
  · exact f411_H_rows_1 11 b (by decide) (by decide)
  · exact f411_H_rows_2 12 b (by decide) (by decide)
  · exact f411_H_rows_2 13 b (by decide) (by decide)
  · exact f411_H_rows_2 14 b (by decide) (by decide)
  · exact f411_H_rows_2 15 b (by decide) (by decide)
  · exact f411_H_rows_2 16 b (by decide) (by decide)
  · exact f411_H_rows_2 17 b (by decide) (by decide)
  · exact f411_H_rows_3 18 b (by decide) (by decide)
  · exact f411_H_rows_3 19 b (by decide) (by decide)
  · exact f411_H_rows_3 20 b (by decide) (by decide)
  · exact f411_H_rows_3 21 b (by decide) (by decide)
  · exact f411_H_rows_3 22 b (by decide) (by decide)
  · exact f411_H_rows_3 23 b (by decide) (by decide)
  · exact f411_H_rows_4 24 b (by decide) (by decide)
  · exact f411_H_rows_4 25 b (by decide) (by decide)
  · exact f411_H_rows_4 26 b (by decide) (by decide)


theorem f411_actual_raw_H_matrix (x y : Fin 27 → ℂ) :
    natOccupationInner (natFourWordBlock f411basis x)
      (canonicalPairHamiltonianNat (natFourWordBlock f411basis y))=
      star x ⬝ᵥ (complexify f411rawHForm *ᵥ y) :=
  canonicalNatFourH_matrix_form 11 f411basis (fun a => (f411hs_shape a).2)
    f411rawHForm f411_raw_H_matrix_check x y

#print axioms f411_raw_H_matrix_check
#print axioms f411_actual_raw_H_matrix
end TorusLean.BosonFiniteCertificate
