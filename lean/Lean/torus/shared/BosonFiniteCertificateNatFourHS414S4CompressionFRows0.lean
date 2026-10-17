import torus.shared.BosonFiniteCertificateNatFourHS414S4CompressionData

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

theorem f414_S4Compression_hF_rows_0 (a : Fin 8) (hlo : 0 ≤ a.val) (hhi : a.val < 8) (b : Fin 8) :
    (natFourIntegerMatrix (180180*4*180180) f414S4CompressionResult) a b=(b414s) a b := by
  fin_cases a
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 8) => (natFourIntegerMatrix (180180*4*180180) f414S4CompressionResult) 0 j)
      (fun (_ : Fin 1) (j : Fin 8) => (b414s) 0 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 8) => (natFourIntegerMatrix (180180*4*180180) f414S4CompressionResult) 1 j)
      (fun (_ : Fin 1) (j : Fin 8) => (b414s) 1 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 8) => (natFourIntegerMatrix (180180*4*180180) f414S4CompressionResult) 2 j)
      (fun (_ : Fin 1) (j : Fin 8) => (b414s) 2 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 8) => (natFourIntegerMatrix (180180*4*180180) f414S4CompressionResult) 3 j)
      (fun (_ : Fin 1) (j : Fin 8) => (b414s) 3 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 8) => (natFourIntegerMatrix (180180*4*180180) f414S4CompressionResult) 4 j)
      (fun (_ : Fin 1) (j : Fin 8) => (b414s) 4 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 8) => (natFourIntegerMatrix (180180*4*180180) f414S4CompressionResult) 5 j)
      (fun (_ : Fin 1) (j : Fin 8) => (b414s) 5 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 8) => (natFourIntegerMatrix (180180*4*180180) f414S4CompressionResult) 6 j)
      (fun (_ : Fin 1) (j : Fin 8) => (b414s) 6 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 8) => (natFourIntegerMatrix (180180*4*180180) f414S4CompressionResult) 7 j)
      (fun (_ : Fin 1) (j : Fin 8) => (b414s) 7 j) (by decide +kernel)
    exact h 0 b

#print axioms f414_S4Compression_hF_rows_0
end TorusLean.BosonFiniteCertificate
