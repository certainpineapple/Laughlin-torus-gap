import torus.shared.BosonFiniteCertificateNatFourHS415S4CompressionData

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

theorem f415_S4Compression_hF_rows_0 (a : Fin 7) (hlo : 0 ≤ a.val) (hhi : a.val < 7) (b : Fin 7) :
    (natFourIntegerMatrix (360360*2*360360) f415S4CompressionResult) a b=(b415s) a b := by
  fin_cases a
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix (360360*2*360360) f415S4CompressionResult) 0 j)
      (fun (_ : Fin 1) (j : Fin 7) => (b415s) 0 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix (360360*2*360360) f415S4CompressionResult) 1 j)
      (fun (_ : Fin 1) (j : Fin 7) => (b415s) 1 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix (360360*2*360360) f415S4CompressionResult) 2 j)
      (fun (_ : Fin 1) (j : Fin 7) => (b415s) 2 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix (360360*2*360360) f415S4CompressionResult) 3 j)
      (fun (_ : Fin 1) (j : Fin 7) => (b415s) 3 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix (360360*2*360360) f415S4CompressionResult) 4 j)
      (fun (_ : Fin 1) (j : Fin 7) => (b415s) 4 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix (360360*2*360360) f415S4CompressionResult) 5 j)
      (fun (_ : Fin 1) (j : Fin 7) => (b415s) 5 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix (360360*2*360360) f415S4CompressionResult) 6 j)
      (fun (_ : Fin 1) (j : Fin 7) => (b415s) 6 j) (by decide +kernel)
    exact h 0 b

#print axioms f415_S4Compression_hF_rows_0
end TorusLean.BosonFiniteCertificate
