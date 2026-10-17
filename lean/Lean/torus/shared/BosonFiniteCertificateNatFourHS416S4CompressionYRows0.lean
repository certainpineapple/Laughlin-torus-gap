import torus.shared.BosonFiniteCertificateNatFourHS416S4CompressionData

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

theorem f416_S4Compression_hY_rows_0 (a : Fin 10) (hlo : 0 ≤ a.val) (hhi : a.val < 5) (b : Fin 10) :
    (f416S4CompressionLeftProduct*f416S4CompressionCoordinates) a b=(f416S4CompressionResult) a b := by
  fin_cases a
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (f416S4CompressionLeftProduct*f416S4CompressionCoordinates) 0 j)
      (fun (_ : Fin 1) (j : Fin 10) => (f416S4CompressionResult) 0 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (f416S4CompressionLeftProduct*f416S4CompressionCoordinates) 1 j)
      (fun (_ : Fin 1) (j : Fin 10) => (f416S4CompressionResult) 1 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (f416S4CompressionLeftProduct*f416S4CompressionCoordinates) 2 j)
      (fun (_ : Fin 1) (j : Fin 10) => (f416S4CompressionResult) 2 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (f416S4CompressionLeftProduct*f416S4CompressionCoordinates) 3 j)
      (fun (_ : Fin 1) (j : Fin 10) => (f416S4CompressionResult) 3 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (f416S4CompressionLeftProduct*f416S4CompressionCoordinates) 4 j)
      (fun (_ : Fin 1) (j : Fin 10) => (f416S4CompressionResult) 4 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · change (5 : ℕ) < 5 at hhi
    omega
  · change (6 : ℕ) < 5 at hhi
    omega
  · change (7 : ℕ) < 5 at hhi
    omega
  · change (8 : ℕ) < 5 at hhi
    omega
  · change (9 : ℕ) < 5 at hhi
    omega

#print axioms f416_S4Compression_hY_rows_0
end TorusLean.BosonFiniteCertificate
