import torus.shared.BosonFiniteCertificateNatFourHS415HCompressionData

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

theorem f415_HCompression_hF_rows_0 (a : Fin 7) (hlo : 0 ≤ a.val) (hhi : a.val < 7) (b : Fin 7) :
    (natFourIntegerMatrix (360360*4*360360) f415HCompressionResult) a b=(b415h) a b := by
  fin_cases a
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix (360360*4*360360) f415HCompressionResult) 0 j)
      (fun (_ : Fin 1) (j : Fin 7) => (b415h) 0 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix (360360*4*360360) f415HCompressionResult) 1 j)
      (fun (_ : Fin 1) (j : Fin 7) => (b415h) 1 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix (360360*4*360360) f415HCompressionResult) 2 j)
      (fun (_ : Fin 1) (j : Fin 7) => (b415h) 2 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix (360360*4*360360) f415HCompressionResult) 3 j)
      (fun (_ : Fin 1) (j : Fin 7) => (b415h) 3 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix (360360*4*360360) f415HCompressionResult) 4 j)
      (fun (_ : Fin 1) (j : Fin 7) => (b415h) 4 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix (360360*4*360360) f415HCompressionResult) 5 j)
      (fun (_ : Fin 1) (j : Fin 7) => (b415h) 5 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix (360360*4*360360) f415HCompressionResult) 6 j)
      (fun (_ : Fin 1) (j : Fin 7) => (b415h) 6 j) (by decide +kernel)
    exact h 0 b

#print axioms f415_HCompression_hF_rows_0
end TorusLean.BosonFiniteCertificate
