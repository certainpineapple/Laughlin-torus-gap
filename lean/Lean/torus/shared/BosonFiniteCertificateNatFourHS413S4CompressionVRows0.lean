import torus.shared.BosonFiniteCertificateNatFourHS413S4CompressionData

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

theorem f413_S4Compression_hV_rows_0 (a : Fin 5) (hlo : 0 ≤ a.val) (hhi : a.val < 2) (b : Fin 39) :
    (f413S4CompressionCoordinatesᵀ*f413S4CompressionInteger) a b=(f413S4CompressionLeftProduct) a b := by
  fin_cases a
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 39) => (f413S4CompressionCoordinatesᵀ*f413S4CompressionInteger) 0 j)
      (fun (_ : Fin 1) (j : Fin 39) => (f413S4CompressionLeftProduct) 0 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 39) => (f413S4CompressionCoordinatesᵀ*f413S4CompressionInteger) 1 j)
      (fun (_ : Fin 1) (j : Fin 39) => (f413S4CompressionLeftProduct) 1 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · change (2 : ℕ) < 2 at hhi
    omega
  · change (3 : ℕ) < 2 at hhi
    omega
  · change (4 : ℕ) < 2 at hhi
    omega

#print axioms f413_S4Compression_hV_rows_0
end TorusLean.BosonFiniteCertificate
