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

theorem canonicalNatFourOriginalOperator_raw_matrix_form_D02
    (x y : Fin (natFourOccupationDimension (2 : Fin 17)) → ℂ) :
    natOccupationInner (natFourWordBlock (natFourOccupationBasis (2 : Fin 17)) x)
      (canonicalNatFourOriginalOperator (natFourWordBlock (natFourOccupationBasis (2 : Fin 17)) y))=
        star x ⬝ᵥ (complexify (natFourOriginalRawFormMatrix (2 : Fin 17)) *ᵥ y) := by
  have e : natFourOccupationDimension (2 : Fin 17)=2 := rfl
  have hb : natFourOccupationBasis (2 : Fin 17)=
      (fun i => f402basis (Fin.cast e i)) := rfl
  have hm : natFourOriginalRawFormMatrix (2 : Fin 17)=
      (fun i j => f402rawM4Form (Fin.cast e i) (Fin.cast e j)) := rfl
  exact natFourRawMatrixForm_transportIndex
    (n := natFourOccupationDimension (2 : Fin 17)) (m := 2) e
    (natFourOccupationBasis (2 : Fin 17)) f402basis
    (natFourOriginalRawFormMatrix (2 : Fin 17)) f402rawM4Form
    hb hm f402_actual_raw_M4_matrix x y

#print axioms canonicalNatFourOriginalOperator_raw_matrix_form_D02
end TorusLean.BosonFiniteCertificate
