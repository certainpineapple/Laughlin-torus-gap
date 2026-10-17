import torus.shared.BosonFiniteCertificateNatFourHS416S4CompressionData

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

theorem f416_S4Compression_hF_rows_0 (a : Fin 10) (hlo : 0 ≤ a.val) (hhi : a.val < 10) (b : Fin 10) :
    (natFourIntegerMatrix (180180*4*180180) f416S4CompressionResult) a b=(b416s) a b := by
  fin_cases a
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix (180180*4*180180) f416S4CompressionResult) 0 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416s) 0 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix (180180*4*180180) f416S4CompressionResult) 1 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416s) 1 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix (180180*4*180180) f416S4CompressionResult) 2 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416s) 2 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix (180180*4*180180) f416S4CompressionResult) 3 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416s) 3 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix (180180*4*180180) f416S4CompressionResult) 4 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416s) 4 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix (180180*4*180180) f416S4CompressionResult) 5 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416s) 5 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix (180180*4*180180) f416S4CompressionResult) 6 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416s) 6 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix (180180*4*180180) f416S4CompressionResult) 7 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416s) 7 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix (180180*4*180180) f416S4CompressionResult) 8 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416s) 8 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix (180180*4*180180) f416S4CompressionResult) 9 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416s) 9 j) (by decide +kernel)
    exact h 0 b

#print axioms f416_S4Compression_hF_rows_0
end TorusLean.BosonFiniteCertificate
