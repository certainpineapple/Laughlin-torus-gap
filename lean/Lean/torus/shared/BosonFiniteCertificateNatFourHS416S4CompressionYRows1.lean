import torus.shared.BosonFiniteCertificateNatFourHS416S4CompressionData

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

theorem f416_S4Compression_hY_rows_1 (a : Fin 10) (hlo : 5 ≤ a.val) (hhi : a.val < 10) (b : Fin 10) :
    (f416S4CompressionLeftProduct*f416S4CompressionCoordinates) a b=(f416S4CompressionResult) a b := by
  fin_cases a
  · change 5 ≤ (0 : ℕ) at hlo
    omega
  · change 5 ≤ (1 : ℕ) at hlo
    omega
  · change 5 ≤ (2 : ℕ) at hlo
    omega
  · change 5 ≤ (3 : ℕ) at hlo
    omega
  · change 5 ≤ (4 : ℕ) at hlo
    omega
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (f416S4CompressionLeftProduct*f416S4CompressionCoordinates) 5 j)
      (fun (_ : Fin 1) (j : Fin 10) => (f416S4CompressionResult) 5 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (f416S4CompressionLeftProduct*f416S4CompressionCoordinates) 6 j)
      (fun (_ : Fin 1) (j : Fin 10) => (f416S4CompressionResult) 6 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (f416S4CompressionLeftProduct*f416S4CompressionCoordinates) 7 j)
      (fun (_ : Fin 1) (j : Fin 10) => (f416S4CompressionResult) 7 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (f416S4CompressionLeftProduct*f416S4CompressionCoordinates) 8 j)
      (fun (_ : Fin 1) (j : Fin 10) => (f416S4CompressionResult) 8 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (f416S4CompressionLeftProduct*f416S4CompressionCoordinates) 9 j)
      (fun (_ : Fin 1) (j : Fin 10) => (f416S4CompressionResult) 9 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b

#print axioms f416_S4Compression_hY_rows_1
end TorusLean.BosonFiniteCertificate
