import torus.shared.BosonFiniteCertificateReconstruct304
import torus.shared.BosonFiniteCertificateReconstruct305
import torus.shared.BosonFiniteCertificateReconstruct306
import torus.shared.BosonFiniteCertificateReconstruct307
import torus.shared.BosonFiniteCertificateReconstruct308
import torus.shared.BosonFiniteCertificate304
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
open Matrix
open scoped ComplexOrder
namespace TorusLean.BosonFiniteCertificate

def c304lowerRaw : Matrix (Fin 3) (Fin 4) ℚ :=
  fun i j => (loweringEntry ((threeBasis 3)[i.val]?.getD []) (p304basis j) : ℤ)

theorem c304_lowering_reconstructed : c304lowerRaw = b304lower := by decide +kernel

theorem c304_relative_complete (v : Fin 4 → ℚ) :
    c304lowerRaw *ᵥ v = 0 ↔ ∃ x : Fin 1 → ℚ, b304relative *ᵥ x = v := by
  rw [c304_lowering_reconstructed]
  exact b304_relative_exact v

def c304desc4 : Matrix (Fin 4) (Fin 1) ℚ :=
  !![(1/3);
    (-4/3);
    1;
    0]

theorem c304desc4_normalization :
    c304desc4ᵀ * (Matrix.diagonal ![48, 6, 8, 4] : Matrix (Fin 4) (Fin 4) ℚ) * c304desc4 =
      (1 : ℚ) • (b304relativeᵀ * (Matrix.diagonal ![48, 6, 8, 4] : Matrix (Fin 4) (Fin 4) ℚ) * b304relative) := by decide +kernel

#print axioms c304desc4_normalization

theorem c304desc4_root : c304desc4 = b304relative := by decide +kernel

def c304raise4 : Matrix (Fin 5) (Fin 4) ℚ :=
  fun i j => (raisingEntry (p305basis i) (p304basis j) : ℤ)

def c304desc5 : Matrix (Fin 5) (Fin 1) ℚ :=
  !![(1/3);
    (-2/3);
    (2/3);
    (-4/3);
    1]

theorem c304desc5_normalization :
    c304desc5ᵀ * (Matrix.diagonal ![240, 24, 12, 12, 8] : Matrix (Fin 5) (Fin 5) ℚ) * c304desc5 =
      (3 : ℚ) • (b304relativeᵀ * (Matrix.diagonal ![48, 6, 8, 4] : Matrix (Fin 4) (Fin 4) ℚ) * b304relative) := by decide +kernel

#print axioms c304desc5_normalization

def c304raise5 : Matrix (Fin 7) (Fin 5) ℚ :=
  fun i j => (raisingEntry (p306basis i) (p305basis j) : ℤ)

theorem c304desc5_step : c304raise4 * c304desc4 = c304desc5 := by decide +kernel

def c304desc6 : Matrix (Fin 7) (Fin 1) ℚ :=
  !![(1/3);
    0;
    0;
    (2/3);
    -2;
    0;
    1]

theorem c304desc6_normalization :
    c304desc6ᵀ * (Matrix.diagonal ![1440, 120, 48, 72, 48, 12, 48] : Matrix (Fin 7) (Fin 7) ℚ) * c304desc6 =
      (18 : ℚ) • (b304relativeᵀ * (Matrix.diagonal ![48, 6, 8, 4] : Matrix (Fin 4) (Fin 4) ℚ) * b304relative) := by decide +kernel

#print axioms c304desc6_normalization

def c304raise6 : Matrix (Fin 8) (Fin 7) ℚ :=
  fun i j => (raisingEntry (p307basis i) (p306basis j) : ℤ)

theorem c304desc6_step : c304raise5 * c304desc5 = c304desc6 := by decide +kernel

def c304desc7 : Matrix (Fin 8) (Fin 1) ℚ :=
  !![(1/3);
    (2/3);
    0;
    (4/3);
    -2;
    -4;
    (2/3);
    3]

theorem c304desc7_normalization :
    c304desc7ᵀ * (Matrix.diagonal ![10080, 720, 240, 144, 240, 48, 72, 48] : Matrix (Fin 8) (Fin 8) ℚ) * c304desc7 =
      (162 : ℚ) • (b304relativeᵀ * (Matrix.diagonal ![48, 6, 8, 4] : Matrix (Fin 4) (Fin 4) ℚ) * b304relative) := by decide +kernel

#print axioms c304desc7_normalization

def c304raise7 : Matrix (Fin 10) (Fin 8) ℚ :=
  fun i j => (raisingEntry (p308basis i) (p307basis j) : ℤ)

theorem c304desc7_step : c304raise6 * c304desc6 = c304desc7 := by decide +kernel

def c304desc8 : Matrix (Fin 10) (Fin 1) ℚ :=
  !![(1/3);
    (4/3);
    (2/3);
    (4/3);
    (4/3);
    (-4/3);
    -8;
    (-4/3);
    -1;
    (20/3)]

theorem c304desc8_normalization :
    c304desc8ᵀ * (Matrix.diagonal ![80640, 5040, 1440, 720, 1152, 1440, 240, 144, 192, 144] : Matrix (Fin 10) (Fin 10) ℚ) * c304desc8 =
      (1944 : ℚ) • (b304relativeᵀ * (Matrix.diagonal ![48, 6, 8, 4] : Matrix (Fin 4) (Fin 4) ℚ) * b304relative) := by decide +kernel

#print axioms c304desc8_normalization

theorem c304desc8_step : c304raise7 * c304desc7 = c304desc8 := by decide +kernel

def c304averageRaw : Matrix (Fin 1) (Fin 1) ℚ :=
  ((2/3) : ℚ) • (c304desc4ᵀ * p304rawMform * c304desc4) +
    ((2/9) : ℚ) • (c304desc5ᵀ * p305rawMform * c304desc5) +
    ((1/27) : ℚ) • (c304desc6ᵀ * p306rawMform * c304desc6) +
    ((1/243) : ℚ) • (c304desc7ᵀ * p307rawMform * c304desc7) +
    ((1/2916) : ℚ) • (c304desc8ᵀ * p308rawMform * c304desc8)

theorem c304_COM_reconstructed : c304averageRaw = b304average := by
  unfold c304averageRaw
  rw [p304_Mform_reconstructed, p305_Mform_reconstructed, p306_Mform_reconstructed, p307_Mform_reconstructed, p308_Mform_reconstructed]
  decide +kernel

def c304hRaw : Matrix (Fin 1) (Fin 1) ℚ := b304relativeᵀ * p304rawHform * b304relative

def c304sRaw : Matrix (Fin 1) (Fin 1) ℚ :=
  b304relativeᵀ * planarSingleForm p304Ginv p304rawHform * b304relative

theorem c304_h_reconstructed : c304hRaw = b304h := by
  unfold c304hRaw
  rw [p304_Hform_reconstructed]
  decide +kernel

theorem c304_s_reconstructed : c304sRaw = b304s := by
  unfold c304sRaw
  rw [p304_Hform_reconstructed, p304_Sform_reconstructed]
  decide +kernel

def c304comparisonRaw : Matrix (Fin 1) (Fin 1) ℚ :=
  c304sRaw - c304averageRaw + delta • c304hRaw

theorem c304_comparison_reconstructed : c304comparisonRaw = b304comparison := by
  simp only [c304comparisonRaw, c304_s_reconstructed, c304_COM_reconstructed, c304_h_reconstructed, b304comparison, one_smul]

theorem c304_source_comparison_positive :
    (TorusLean.M2.complexify c304comparisonRaw).PosSemidef := by
  rw [c304_comparison_reconstructed]
  exact b304_comparison_positive

#print axioms c304_lowering_reconstructed
#print axioms c304_relative_complete
#print axioms c304_COM_reconstructed
#print axioms c304_h_reconstructed
#print axioms c304_s_reconstructed
#print axioms c304_comparison_reconstructed
#print axioms c304_source_comparison_positive
end TorusLean.BosonFiniteCertificate
