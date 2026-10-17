import torus.shared.BosonFiniteCertificateNatFourHS413S4CompressionData

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

theorem f413_S4Compression_hY_rows_0 (a : Fin 5) (hlo : 0 ≤ a.val) (hhi : a.val < 5) (b : Fin 5) :
    (f413S4CompressionLeftProduct*f413S4CompressionCoordinates) a b=(f413S4CompressionResult) a b := by
  fin_cases a
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (f413S4CompressionLeftProduct*f413S4CompressionCoordinates) 0 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413S4CompressionResult) 0 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (f413S4CompressionLeftProduct*f413S4CompressionCoordinates) 1 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413S4CompressionResult) 1 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (f413S4CompressionLeftProduct*f413S4CompressionCoordinates) 2 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413S4CompressionResult) 2 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (f413S4CompressionLeftProduct*f413S4CompressionCoordinates) 3 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413S4CompressionResult) 3 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (f413S4CompressionLeftProduct*f413S4CompressionCoordinates) 4 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413S4CompressionResult) 4 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b

#print axioms f413_S4Compression_hY_rows_0
end TorusLean.BosonFiniteCertificate
