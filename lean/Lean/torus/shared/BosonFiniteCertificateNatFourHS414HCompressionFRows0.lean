import torus.shared.BosonFiniteCertificateNatFourHS414HCompressionData

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

theorem f414_HCompression_hF_rows_0 (a : Fin 8) (hlo : 0 ≤ a.val) (hhi : a.val < 8) (b : Fin 8) :
    (natFourIntegerMatrix (180180*4*180180) f414HCompressionResult) a b=(b414h) a b := by
  fin_cases a
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 8) => (natFourIntegerMatrix (180180*4*180180) f414HCompressionResult) 0 j)
      (fun (_ : Fin 1) (j : Fin 8) => (b414h) 0 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 8) => (natFourIntegerMatrix (180180*4*180180) f414HCompressionResult) 1 j)
      (fun (_ : Fin 1) (j : Fin 8) => (b414h) 1 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 8) => (natFourIntegerMatrix (180180*4*180180) f414HCompressionResult) 2 j)
      (fun (_ : Fin 1) (j : Fin 8) => (b414h) 2 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 8) => (natFourIntegerMatrix (180180*4*180180) f414HCompressionResult) 3 j)
      (fun (_ : Fin 1) (j : Fin 8) => (b414h) 3 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 8) => (natFourIntegerMatrix (180180*4*180180) f414HCompressionResult) 4 j)
      (fun (_ : Fin 1) (j : Fin 8) => (b414h) 4 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 8) => (natFourIntegerMatrix (180180*4*180180) f414HCompressionResult) 5 j)
      (fun (_ : Fin 1) (j : Fin 8) => (b414h) 5 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 8) => (natFourIntegerMatrix (180180*4*180180) f414HCompressionResult) 6 j)
      (fun (_ : Fin 1) (j : Fin 8) => (b414h) 6 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 8) => (natFourIntegerMatrix (180180*4*180180) f414HCompressionResult) 7 j)
      (fun (_ : Fin 1) (j : Fin 8) => (b414h) 7 j) (by decide +kernel)
    exact h 0 b

#print axioms f414_HCompression_hF_rows_0
end TorusLean.BosonFiniteCertificate
