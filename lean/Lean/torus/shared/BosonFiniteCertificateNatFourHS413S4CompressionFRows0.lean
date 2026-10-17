import torus.shared.BosonFiniteCertificateNatFourHS413S4CompressionData

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

theorem f413_S4Compression_hF_rows_0 (a : Fin 5) (hlo : 0 ≤ a.val) (hhi : a.val < 5) (b : Fin 5) :
    (natFourIntegerMatrix (27720*4*27720) f413S4CompressionResult) a b=(b413s) a b := by
  fin_cases a
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix (27720*4*27720) f413S4CompressionResult) 0 j)
      (fun (_ : Fin 1) (j : Fin 5) => (b413s) 0 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix (27720*4*27720) f413S4CompressionResult) 1 j)
      (fun (_ : Fin 1) (j : Fin 5) => (b413s) 1 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix (27720*4*27720) f413S4CompressionResult) 2 j)
      (fun (_ : Fin 1) (j : Fin 5) => (b413s) 2 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix (27720*4*27720) f413S4CompressionResult) 3 j)
      (fun (_ : Fin 1) (j : Fin 5) => (b413s) 3 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix (27720*4*27720) f413S4CompressionResult) 4 j)
      (fun (_ : Fin 1) (j : Fin 5) => (b413s) 4 j) (by decide +kernel)
    exact h 0 b

#print axioms f413_S4Compression_hF_rows_0
end TorusLean.BosonFiniteCertificate
