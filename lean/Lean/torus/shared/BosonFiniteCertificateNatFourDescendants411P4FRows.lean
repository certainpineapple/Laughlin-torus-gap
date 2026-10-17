import torus.shared.BosonFiniteCertificateNatFourDescendants411P4Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

theorem f411desc4_bounded_form_decode (a : Fin 4) (b : Fin 4) :
    (natFourIntegerMatrix (2520*1000000000000000000000000*2520) f411desc4IntegerFormShared) a b=(f411desc4Form) a b := by
  fin_cases a
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix (2520*1000000000000000000000000*2520) f411desc4IntegerFormShared) 0 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc4Form) 0 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix (2520*1000000000000000000000000*2520) f411desc4IntegerFormShared) 1 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc4Form) 1 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix (2520*1000000000000000000000000*2520) f411desc4IntegerFormShared) 2 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc4Form) 2 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix (2520*1000000000000000000000000*2520) f411desc4IntegerFormShared) 3 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc4Form) 3 j) (by decide +kernel)
    exact h 0 b

#print axioms f411desc4_bounded_form_decode

end TorusLean.BosonFiniteCertificate
