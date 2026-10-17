import torus.shared.BosonFiniteCertificateNatFourHS413S4CompressionData

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

theorem f413_S4Compression_hV_rows_1 (a : Fin 5) (hlo : 2 ≤ a.val) (hhi : a.val < 4) (b : Fin 39) :
    (f413S4CompressionCoordinatesᵀ*f413S4CompressionInteger) a b=(f413S4CompressionLeftProduct) a b := by
  fin_cases a
  · change 2 ≤ (0 : ℕ) at hlo
    omega
  · change 2 ≤ (1 : ℕ) at hlo
    omega
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 39) => (f413S4CompressionCoordinatesᵀ*f413S4CompressionInteger) 2 j)
      (fun (_ : Fin 1) (j : Fin 39) => (f413S4CompressionLeftProduct) 2 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · have h := natFourIntegerEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 39) => (f413S4CompressionCoordinatesᵀ*f413S4CompressionInteger) 3 j)
      (fun (_ : Fin 1) (j : Fin 39) => (f413S4CompressionLeftProduct) 3 j) (by decide +kernel)
    exact congrFun (congrFun h 0) b
  · change (4 : ℕ) < 4 at hhi
    omega

#print axioms f413_S4Compression_hV_rows_1
end TorusLean.BosonFiniteCertificate
