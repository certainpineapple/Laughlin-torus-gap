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

theorem canonicalNatFourOriginalOperator_raw_matrix_form_D14
    (x y : Fin (natFourOccupationDimension (14 : Fin 17)) → ℂ) :
    natOccupationInner (natFourWordBlock (natFourOccupationBasis (14 : Fin 17)) x)
      (canonicalNatFourOriginalOperator (natFourWordBlock (natFourOccupationBasis (14 : Fin 17)) y))=
        star x ⬝ᵥ (complexify (natFourOriginalRawFormMatrix (14 : Fin 17)) *ᵥ y) := by
  have e : natFourOccupationDimension (14 : Fin 17)=47 := rfl
  have hb : natFourOccupationBasis (14 : Fin 17)=
      (fun i => f414basis (Fin.cast e i)) := rfl
  have hm : natFourOriginalRawFormMatrix (14 : Fin 17)=
      (fun i j => f414rawM4Form (Fin.cast e i) (Fin.cast e j)) := rfl
  exact natFourRawMatrixForm_transportIndex
    (n := natFourOccupationDimension (14 : Fin 17)) (m := 47) e
    (natFourOccupationBasis (14 : Fin 17)) f414basis
    (natFourOriginalRawFormMatrix (14 : Fin 17)) f414rawM4Form
    hb hm f414_actual_raw_M4_matrix x y

#print axioms canonicalNatFourOriginalOperator_raw_matrix_form_D14
end TorusLean.BosonFiniteCertificate
