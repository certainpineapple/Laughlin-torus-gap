import torus.shared.BosonFiniteCertificateNatFourDescendants413P0Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

theorem f413desc0_bounded_form_decode (a : Fin 5) (b : Fin 5) :
    (natFourIntegerMatrix (27720*1000000000000000000000000*27720) f413desc0IntegerFormShared) a b=(f413desc0Form) a b := by
  fin_cases a
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix (27720*1000000000000000000000000*27720) f413desc0IntegerFormShared) 0 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc0Form) 0 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix (27720*1000000000000000000000000*27720) f413desc0IntegerFormShared) 1 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc0Form) 1 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix (27720*1000000000000000000000000*27720) f413desc0IntegerFormShared) 2 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc0Form) 2 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix (27720*1000000000000000000000000*27720) f413desc0IntegerFormShared) 3 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc0Form) 3 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix (27720*1000000000000000000000000*27720) f413desc0IntegerFormShared) 4 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc0Form) 4 j) (by decide +kernel)
    exact h 0 b

#print axioms f413desc0_bounded_form_decode

end TorusLean.BosonFiniteCertificate
