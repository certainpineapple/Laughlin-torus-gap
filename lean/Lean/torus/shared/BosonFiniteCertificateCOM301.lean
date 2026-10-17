import torus.shared.BosonFiniteCertificateReconstruct301
import torus.shared.BosonFiniteCertificateReconstruct302
import torus.shared.BosonFiniteCertificateReconstruct303
import torus.shared.BosonFiniteCertificateReconstruct304
import torus.shared.BosonFiniteCertificateReconstruct305
import torus.shared.BosonFiniteCertificateReconstruct306
import torus.shared.BosonFiniteCertificateReconstruct307
import torus.shared.BosonFiniteCertificateReconstruct308
import torus.shared.BosonFiniteCertificate301
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
open Matrix
open scoped ComplexOrder
namespace TorusLean.BosonFiniteCertificate

def c301lowerRaw : Matrix (Fin 1) (Fin 1) ℚ :=
  fun i j => (loweringEntry ((threeBasis 0)[i.val]?.getD []) (p301basis j) : ℤ)

theorem c301_lowering_reconstructed : c301lowerRaw = b301lower := by decide +kernel

theorem c301_relative_complete (v : Fin 1 → ℚ) :
    c301lowerRaw *ᵥ v = 0 ↔ ∃ x : Fin 0 → ℚ, b301relative *ᵥ x = v := by
  rw [c301_lowering_reconstructed]
  exact b301_relative_exact v

def c301desc1 : Matrix (Fin 1) (Fin 0) ℚ :=
  fun _ _ => 0

theorem c301desc1_normalization :
    c301desc1ᵀ * (Matrix.diagonal ![2] : Matrix (Fin 1) (Fin 1) ℚ) * c301desc1 =
      (1 : ℚ) • (b301relativeᵀ * (Matrix.diagonal ![2] : Matrix (Fin 1) (Fin 1) ℚ) * b301relative) := by decide +kernel

#print axioms c301desc1_normalization

theorem c301desc1_root : c301desc1 = b301relative := by decide +kernel

def c301raise1 : Matrix (Fin 2) (Fin 1) ℚ :=
  fun i j => (raisingEntry (p302basis i) (p301basis j) : ℤ)

def c301desc2 : Matrix (Fin 2) (Fin 0) ℚ :=
  fun _ _ => 0

theorem c301desc2_normalization :
    c301desc2ᵀ * (Matrix.diagonal ![4, 2] : Matrix (Fin 2) (Fin 2) ℚ) * c301desc2 =
      (3 : ℚ) • (b301relativeᵀ * (Matrix.diagonal ![2] : Matrix (Fin 1) (Fin 1) ℚ) * b301relative) := by decide +kernel

#print axioms c301desc2_normalization

def c301raise2 : Matrix (Fin 3) (Fin 2) ℚ :=
  fun i j => (raisingEntry (p303basis i) (p302basis j) : ℤ)

theorem c301desc2_step : c301raise1 * c301desc1 = c301desc2 := by decide +kernel

def c301desc3 : Matrix (Fin 3) (Fin 0) ℚ :=
  fun _ _ => 0

theorem c301desc3_normalization :
    c301desc3ᵀ * (Matrix.diagonal ![12, 2, 6] : Matrix (Fin 3) (Fin 3) ℚ) * c301desc3 =
      (18 : ℚ) • (b301relativeᵀ * (Matrix.diagonal ![2] : Matrix (Fin 1) (Fin 1) ℚ) * b301relative) := by decide +kernel

#print axioms c301desc3_normalization

def c301raise3 : Matrix (Fin 4) (Fin 3) ℚ :=
  fun i j => (raisingEntry (p304basis i) (p303basis j) : ℤ)

theorem c301desc3_step : c301raise2 * c301desc2 = c301desc3 := by decide +kernel

def c301desc4 : Matrix (Fin 4) (Fin 0) ℚ :=
  fun _ _ => 0

theorem c301desc4_normalization :
    c301desc4ᵀ * (Matrix.diagonal ![48, 6, 8, 4] : Matrix (Fin 4) (Fin 4) ℚ) * c301desc4 =
      (162 : ℚ) • (b301relativeᵀ * (Matrix.diagonal ![2] : Matrix (Fin 1) (Fin 1) ℚ) * b301relative) := by decide +kernel

#print axioms c301desc4_normalization

def c301raise4 : Matrix (Fin 5) (Fin 4) ℚ :=
  fun i j => (raisingEntry (p305basis i) (p304basis j) : ℤ)

theorem c301desc4_step : c301raise3 * c301desc3 = c301desc4 := by decide +kernel

def c301desc5 : Matrix (Fin 5) (Fin 0) ℚ :=
  fun _ _ => 0

theorem c301desc5_normalization :
    c301desc5ᵀ * (Matrix.diagonal ![240, 24, 12, 12, 8] : Matrix (Fin 5) (Fin 5) ℚ) * c301desc5 =
      (1944 : ℚ) • (b301relativeᵀ * (Matrix.diagonal ![2] : Matrix (Fin 1) (Fin 1) ℚ) * b301relative) := by decide +kernel

#print axioms c301desc5_normalization

def c301raise5 : Matrix (Fin 7) (Fin 5) ℚ :=
  fun i j => (raisingEntry (p306basis i) (p305basis j) : ℤ)

theorem c301desc5_step : c301raise4 * c301desc4 = c301desc5 := by decide +kernel

def c301desc6 : Matrix (Fin 7) (Fin 0) ℚ :=
  fun _ _ => 0

theorem c301desc6_normalization :
    c301desc6ᵀ * (Matrix.diagonal ![1440, 120, 48, 72, 48, 12, 48] : Matrix (Fin 7) (Fin 7) ℚ) * c301desc6 =
      (29160 : ℚ) • (b301relativeᵀ * (Matrix.diagonal ![2] : Matrix (Fin 1) (Fin 1) ℚ) * b301relative) := by decide +kernel

#print axioms c301desc6_normalization

def c301raise6 : Matrix (Fin 8) (Fin 7) ℚ :=
  fun i j => (raisingEntry (p307basis i) (p306basis j) : ℤ)

theorem c301desc6_step : c301raise5 * c301desc5 = c301desc6 := by decide +kernel

def c301desc7 : Matrix (Fin 8) (Fin 0) ℚ :=
  fun _ _ => 0

theorem c301desc7_normalization :
    c301desc7ᵀ * (Matrix.diagonal ![10080, 720, 240, 144, 240, 48, 72, 48] : Matrix (Fin 8) (Fin 8) ℚ) * c301desc7 =
      (524880 : ℚ) • (b301relativeᵀ * (Matrix.diagonal ![2] : Matrix (Fin 1) (Fin 1) ℚ) * b301relative) := by decide +kernel

#print axioms c301desc7_normalization

def c301raise7 : Matrix (Fin 10) (Fin 8) ℚ :=
  fun i j => (raisingEntry (p308basis i) (p307basis j) : ℤ)

theorem c301desc7_step : c301raise6 * c301desc6 = c301desc7 := by decide +kernel

def c301desc8 : Matrix (Fin 10) (Fin 0) ℚ :=
  fun _ _ => 0

theorem c301desc8_normalization :
    c301desc8ᵀ * (Matrix.diagonal ![80640, 5040, 1440, 720, 1152, 1440, 240, 144, 192, 144] : Matrix (Fin 10) (Fin 10) ℚ) * c301desc8 =
      (11022480 : ℚ) • (b301relativeᵀ * (Matrix.diagonal ![2] : Matrix (Fin 1) (Fin 1) ℚ) * b301relative) := by decide +kernel

#print axioms c301desc8_normalization

theorem c301desc8_step : c301raise7 * c301desc7 = c301desc8 := by decide +kernel

def c301averageRaw : Matrix (Fin 0) (Fin 0) ℚ :=
  ((2/3) : ℚ) • (c301desc1ᵀ * p301rawMform * c301desc1) +
    ((2/9) : ℚ) • (c301desc2ᵀ * p302rawMform * c301desc2) +
    ((1/27) : ℚ) • (c301desc3ᵀ * p303rawMform * c301desc3) +
    ((1/243) : ℚ) • (c301desc4ᵀ * p304rawMform * c301desc4) +
    ((1/2916) : ℚ) • (c301desc5ᵀ * p305rawMform * c301desc5) +
    ((1/43740) : ℚ) • (c301desc6ᵀ * p306rawMform * c301desc6) +
    ((1/787320) : ℚ) • (c301desc7ᵀ * p307rawMform * c301desc7) +
    ((1/16533720) : ℚ) • (c301desc8ᵀ * p308rawMform * c301desc8)

theorem c301_COM_reconstructed : c301averageRaw = b301average := by
  unfold c301averageRaw
  rw [p301_Mform_reconstructed, p302_Mform_reconstructed, p303_Mform_reconstructed, p304_Mform_reconstructed, p305_Mform_reconstructed, p306_Mform_reconstructed, p307_Mform_reconstructed, p308_Mform_reconstructed]
  decide +kernel

def c301hRaw : Matrix (Fin 0) (Fin 0) ℚ := b301relativeᵀ * p301rawHform * b301relative

def c301sRaw : Matrix (Fin 0) (Fin 0) ℚ :=
  b301relativeᵀ * planarSingleForm p301Ginv p301rawHform * b301relative

theorem c301_h_reconstructed : c301hRaw = b301h := by
  unfold c301hRaw
  rw [p301_Hform_reconstructed]
  decide +kernel

theorem c301_s_reconstructed : c301sRaw = b301s := by
  unfold c301sRaw
  rw [p301_Hform_reconstructed, p301_Sform_reconstructed]
  decide +kernel

def c301comparisonRaw : Matrix (Fin 0) (Fin 0) ℚ :=
  c301sRaw - c301averageRaw + delta • c301hRaw

theorem c301_comparison_reconstructed : c301comparisonRaw = b301comparison := by
  simp only [c301comparisonRaw, c301_s_reconstructed, c301_COM_reconstructed, c301_h_reconstructed, b301comparison, one_smul]

theorem c301_source_comparison_positive :
    (TorusLean.M2.complexify c301comparisonRaw).PosSemidef := by
  rw [c301_comparison_reconstructed]
  exact b301_comparison_positive

#print axioms c301_lowering_reconstructed
#print axioms c301_relative_complete
#print axioms c301_COM_reconstructed
#print axioms c301_h_reconstructed
#print axioms c301_s_reconstructed
#print axioms c301_comparison_reconstructed
#print axioms c301_source_comparison_positive
end TorusLean.BosonFiniteCertificate
