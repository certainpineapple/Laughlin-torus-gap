import torus.shared.BosonFiniteCertificateNatFourCOMOriginalIndexTransport

/-! All seventeen separately checked original M4 form matrices enter the
whole-N4, all-COM-level rank expansion. This is an identity of the original
normal-ordered source, not a definition of a candidate matrix operator. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2
open Matrix
open scoped BigOperators

theorem canonicalNatFourOriginalOperator_raw_matrix_form_D11
    (x y : Fin (natFourOccupationDimension (11 : Fin 17)) → ℂ) :
    natOccupationInner (natFourWordBlock (natFourOccupationBasis (11 : Fin 17)) x)
      (canonicalNatFourOriginalOperator (natFourWordBlock (natFourOccupationBasis (11 : Fin 17)) y))=
        star x ⬝ᵥ (complexify (natFourOriginalRawFormMatrix (11 : Fin 17)) *ᵥ y) := by
  have e : natFourOccupationDimension (11 : Fin 17)=27 := rfl
  have hb : natFourOccupationBasis (11 : Fin 17)=
      (fun i => f411basis (Fin.cast e i)) := rfl
  have hm : natFourOriginalRawFormMatrix (11 : Fin 17)=
      (fun i j => f411rawM4Form (Fin.cast e i) (Fin.cast e j)) := rfl
  exact natFourRawMatrixForm_transportIndex
    (n := natFourOccupationDimension (11 : Fin 17)) (m := 27) e
    (natFourOccupationBasis (11 : Fin 17)) f411basis
    (natFourOriginalRawFormMatrix (11 : Fin 17)) f411rawM4Form
    hb hm f411_actual_raw_M4_matrix x y

#print axioms canonicalNatFourOriginalOperator_raw_matrix_form_D11
end TorusLean.BosonFiniteCertificate
