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

theorem canonicalNatFourOriginalOperator_raw_matrix_form_D05
    (x y : Fin (natFourOccupationDimension (5 : Fin 17)) → ℂ) :
    natOccupationInner (natFourWordBlock (natFourOccupationBasis (5 : Fin 17)) x)
      (canonicalNatFourOriginalOperator (natFourWordBlock (natFourOccupationBasis (5 : Fin 17)) y))=
        star x ⬝ᵥ (complexify (natFourOriginalRawFormMatrix (5 : Fin 17)) *ᵥ y) := by
  have e : natFourOccupationDimension (5 : Fin 17)=6 := rfl
  have hb : natFourOccupationBasis (5 : Fin 17)=
      (fun i => f405basis (Fin.cast e i)) := rfl
  have hm : natFourOriginalRawFormMatrix (5 : Fin 17)=
      (fun i j => f405rawM4Form (Fin.cast e i) (Fin.cast e j)) := rfl
  exact natFourRawMatrixForm_transportIndex
    (n := natFourOccupationDimension (5 : Fin 17)) (m := 6) e
    (natFourOccupationBasis (5 : Fin 17)) f405basis
    (natFourOriginalRawFormMatrix (5 : Fin 17)) f405rawM4Form
    hb hm f405_actual_raw_M4_matrix x y

#print axioms canonicalNatFourOriginalOperator_raw_matrix_form_D05
end TorusLean.BosonFiniteCertificate
