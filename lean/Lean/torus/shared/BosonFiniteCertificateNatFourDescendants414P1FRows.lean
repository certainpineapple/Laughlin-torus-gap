import torus.shared.BosonFiniteCertificateNatFourDescendants414P1Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

theorem f414desc1_bounded_form_decode (a : Fin 8) (b : Fin 8) :
    (natFourIntegerMatrix (180180*1000000000000000000000000*180180) f414desc1IntegerFormShared) a b=(f414desc1Form) a b := by
  fin_cases a
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 8) => (natFourIntegerMatrix (180180*1000000000000000000000000*180180) f414desc1IntegerFormShared) 0 j)
      (fun (_ : Fin 1) (j : Fin 8) => (f414desc1Form) 0 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 8) => (natFourIntegerMatrix (180180*1000000000000000000000000*180180) f414desc1IntegerFormShared) 1 j)
      (fun (_ : Fin 1) (j : Fin 8) => (f414desc1Form) 1 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 8) => (natFourIntegerMatrix (180180*1000000000000000000000000*180180) f414desc1IntegerFormShared) 2 j)
      (fun (_ : Fin 1) (j : Fin 8) => (f414desc1Form) 2 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 8) => (natFourIntegerMatrix (180180*1000000000000000000000000*180180) f414desc1IntegerFormShared) 3 j)
      (fun (_ : Fin 1) (j : Fin 8) => (f414desc1Form) 3 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 8) => (natFourIntegerMatrix (180180*1000000000000000000000000*180180) f414desc1IntegerFormShared) 4 j)
      (fun (_ : Fin 1) (j : Fin 8) => (f414desc1Form) 4 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 8) => (natFourIntegerMatrix (180180*1000000000000000000000000*180180) f414desc1IntegerFormShared) 5 j)
      (fun (_ : Fin 1) (j : Fin 8) => (f414desc1Form) 5 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 8) => (natFourIntegerMatrix (180180*1000000000000000000000000*180180) f414desc1IntegerFormShared) 6 j)
      (fun (_ : Fin 1) (j : Fin 8) => (f414desc1Form) 6 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 8) => (natFourIntegerMatrix (180180*1000000000000000000000000*180180) f414desc1IntegerFormShared) 7 j)
      (fun (_ : Fin 1) (j : Fin 8) => (f414desc1Form) 7 j) (by decide +kernel)
    exact h 0 b

#print axioms f414desc1_bounded_form_decode

end TorusLean.BosonFiniteCertificate
