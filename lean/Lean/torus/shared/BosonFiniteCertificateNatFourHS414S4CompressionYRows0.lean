import torus.shared.BosonFiniteCertificateNatFourHS414S4CompressionData

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

theorem f414_S4Compression_hY_rows_0 (a : Fin 8) (hlo : 0 ≤ a.val) (hhi : a.val < 8) (b : Fin 8) :
    (f414S4CompressionLeftProduct*f414S4CompressionCoordinates) a b=(f414S4CompressionResult) a b := by
  fin_cases a
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 8) => (f414S4CompressionLeftProduct*f414S4CompressionCoordinates) 0 j)
      (fun (_ : Fin 1) (j : Fin 8) => (f414S4CompressionResult) 0 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 8) => (f414S4CompressionLeftProduct*f414S4CompressionCoordinates) 1 j)
      (fun (_ : Fin 1) (j : Fin 8) => (f414S4CompressionResult) 1 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 8) => (f414S4CompressionLeftProduct*f414S4CompressionCoordinates) 2 j)
      (fun (_ : Fin 1) (j : Fin 8) => (f414S4CompressionResult) 2 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 8) => (f414S4CompressionLeftProduct*f414S4CompressionCoordinates) 3 j)
      (fun (_ : Fin 1) (j : Fin 8) => (f414S4CompressionResult) 3 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 8) => (f414S4CompressionLeftProduct*f414S4CompressionCoordinates) 4 j)
      (fun (_ : Fin 1) (j : Fin 8) => (f414S4CompressionResult) 4 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 8) => (f414S4CompressionLeftProduct*f414S4CompressionCoordinates) 5 j)
      (fun (_ : Fin 1) (j : Fin 8) => (f414S4CompressionResult) 5 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 8) => (f414S4CompressionLeftProduct*f414S4CompressionCoordinates) 6 j)
      (fun (_ : Fin 1) (j : Fin 8) => (f414S4CompressionResult) 6 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 8) => (f414S4CompressionLeftProduct*f414S4CompressionCoordinates) 7 j)
      (fun (_ : Fin 1) (j : Fin 8) => (f414S4CompressionResult) 7 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b

#print axioms f414_S4Compression_hY_rows_0
end TorusLean.BosonFiniteCertificate
