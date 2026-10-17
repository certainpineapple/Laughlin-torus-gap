import torus.shared.BosonFiniteCertificateNatFourHS413HCompressionData

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

theorem f413_HCompression_hF_rows_0 (a : Fin 5) (hlo : 0 ≤ a.val) (hhi : a.val < 5) (b : Fin 5) :
    (natFourIntegerMatrix (27720*2*27720) f413HCompressionResult) a b=(b413h) a b := by
  fin_cases a
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix (27720*2*27720) f413HCompressionResult) 0 j)
      (fun (_ : Fin 1) (j : Fin 5) => (b413h) 0 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix (27720*2*27720) f413HCompressionResult) 1 j)
      (fun (_ : Fin 1) (j : Fin 5) => (b413h) 1 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix (27720*2*27720) f413HCompressionResult) 2 j)
      (fun (_ : Fin 1) (j : Fin 5) => (b413h) 2 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix (27720*2*27720) f413HCompressionResult) 3 j)
      (fun (_ : Fin 1) (j : Fin 5) => (b413h) 3 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix (27720*2*27720) f413HCompressionResult) 4 j)
      (fun (_ : Fin 1) (j : Fin 5) => (b413h) 4 j) (by decide +kernel)
    exact h 0 b

#print axioms f413_HCompression_hF_rows_0
end TorusLean.BosonFiniteCertificate
