import torus.shared.BosonFiniteCertificateReconstruct302
import torus.shared.BosonFiniteCertificateReconstruct303
import torus.shared.BosonFiniteCertificateReconstruct304
import torus.shared.BosonFiniteCertificateReconstruct305
import torus.shared.BosonFiniteCertificateReconstruct306
import torus.shared.BosonFiniteCertificateReconstruct307
import torus.shared.BosonFiniteCertificateReconstruct308
import torus.shared.BosonFiniteCertificate302
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
open Matrix
open scoped ComplexOrder
namespace TorusLean.BosonFiniteCertificate

def c302lowerRaw : Matrix (Fin 1) (Fin 2) ℚ :=
  fun i j => (loweringEntry ((threeBasis 1)[i.val]?.getD []) (p302basis j) : ℤ)

theorem c302_lowering_reconstructed : c302lowerRaw = b302lower := by decide +kernel

theorem c302_relative_complete (v : Fin 2 → ℚ) :
    c302lowerRaw *ᵥ v = 0 ↔ ∃ x : Fin 1 → ℚ, b302relative *ᵥ x = v := by
  rw [c302_lowering_reconstructed]
  exact b302_relative_exact v

def c302desc2 : Matrix (Fin 2) (Fin 1) ℚ :=
  !![-1;
    1]

theorem c302desc2_normalization :
    c302desc2ᵀ * (Matrix.diagonal ![4, 2] : Matrix (Fin 2) (Fin 2) ℚ) * c302desc2 =
      (1 : ℚ) • (b302relativeᵀ * (Matrix.diagonal ![4, 2] : Matrix (Fin 2) (Fin 2) ℚ) * b302relative) := by decide +kernel

#print axioms c302desc2_normalization

theorem c302desc2_root : c302desc2 = b302relative := by decide +kernel

def c302raise2 : Matrix (Fin 3) (Fin 2) ℚ :=
  fun i j => (raisingEntry (p303basis i) (p302basis j) : ℤ)

def c302desc3 : Matrix (Fin 3) (Fin 1) ℚ :=
  !![-1;
    0;
    1]

theorem c302desc3_normalization :
    c302desc3ᵀ * (Matrix.diagonal ![12, 2, 6] : Matrix (Fin 3) (Fin 3) ℚ) * c302desc3 =
      (3 : ℚ) • (b302relativeᵀ * (Matrix.diagonal ![4, 2] : Matrix (Fin 2) (Fin 2) ℚ) * b302relative) := by decide +kernel

#print axioms c302desc3_normalization

def c302raise3 : Matrix (Fin 4) (Fin 3) ℚ :=
  fun i j => (raisingEntry (p304basis i) (p303basis j) : ℤ)

theorem c302desc3_step : c302raise2 * c302desc2 = c302desc3 := by decide +kernel

def c302desc4 : Matrix (Fin 4) (Fin 1) ℚ :=
  !![-1;
    -2;
    0;
    3]

theorem c302desc4_normalization :
    c302desc4ᵀ * (Matrix.diagonal ![48, 6, 8, 4] : Matrix (Fin 4) (Fin 4) ℚ) * c302desc4 =
      (18 : ℚ) • (b302relativeᵀ * (Matrix.diagonal ![4, 2] : Matrix (Fin 2) (Fin 2) ℚ) * b302relative) := by decide +kernel

#print axioms c302desc4_normalization

def c302raise4 : Matrix (Fin 5) (Fin 4) ℚ :=
  fun i j => (raisingEntry (p305basis i) (p304basis j) : ℤ)

theorem c302desc4_step : c302raise3 * c302desc3 = c302desc4 := by decide +kernel

def c302desc5 : Matrix (Fin 5) (Fin 1) ℚ :=
  !![-1;
    -4;
    -2;
    1;
    6]

theorem c302desc5_normalization :
    c302desc5ᵀ * (Matrix.diagonal ![240, 24, 12, 12, 8] : Matrix (Fin 5) (Fin 5) ℚ) * c302desc5 =
      (162 : ℚ) • (b302relativeᵀ * (Matrix.diagonal ![4, 2] : Matrix (Fin 2) (Fin 2) ℚ) * b302relative) := by decide +kernel

#print axioms c302desc5_normalization

def c302raise5 : Matrix (Fin 7) (Fin 5) ℚ :=
  fun i j => (raisingEntry (p306basis i) (p305basis j) : ℤ)

theorem c302desc5_step : c302raise4 * c302desc4 = c302desc5 := by decide +kernel

def c302desc6 : Matrix (Fin 7) (Fin 1) ℚ :=
  !![-1;
    -6;
    -6;
    -2;
    -3;
    12;
    6]

theorem c302desc6_normalization :
    c302desc6ᵀ * (Matrix.diagonal ![1440, 120, 48, 72, 48, 12, 48] : Matrix (Fin 7) (Fin 7) ℚ) * c302desc6 =
      (1944 : ℚ) • (b302relativeᵀ * (Matrix.diagonal ![4, 2] : Matrix (Fin 2) (Fin 2) ℚ) * b302relative) := by decide +kernel

#print axioms c302desc6_normalization

def c302raise6 : Matrix (Fin 8) (Fin 7) ℚ :=
  fun i j => (raisingEntry (p307basis i) (p306basis j) : ℤ)

theorem c302desc6_step : c302raise5 * c302desc5 = c302desc6 := by decide +kernel

def c302desc7 : Matrix (Fin 8) (Fin 1) ℚ :=
  !![-1;
    -8;
    -12;
    -10;
    -9;
    0;
    10;
    30]

theorem c302desc7_normalization :
    c302desc7ᵀ * (Matrix.diagonal ![10080, 720, 240, 144, 240, 48, 72, 48] : Matrix (Fin 8) (Fin 8) ℚ) * c302desc7 =
      (29160 : ℚ) • (b302relativeᵀ * (Matrix.diagonal ![4, 2] : Matrix (Fin 2) (Fin 2) ℚ) * b302relative) := by decide +kernel

#print axioms c302desc7_normalization

def c302raise7 : Matrix (Fin 10) (Fin 8) ℚ :=
  fun i j => (raisingEntry (p308basis i) (p307basis j) : ℤ)

theorem c302desc7_step : c302raise6 * c302desc6 = c302desc7 := by decide +kernel

def c302desc8 : Matrix (Fin 10) (Fin 1) ℚ :=
  !![-1;
    -10;
    -20;
    -22;
    -10;
    -17;
    -30;
    10;
    30;
    70]

theorem c302desc8_normalization :
    c302desc8ᵀ * (Matrix.diagonal ![80640, 5040, 1440, 720, 1152, 1440, 240, 144, 192, 144] : Matrix (Fin 10) (Fin 10) ℚ) * c302desc8 =
      (524880 : ℚ) • (b302relativeᵀ * (Matrix.diagonal ![4, 2] : Matrix (Fin 2) (Fin 2) ℚ) * b302relative) := by decide +kernel

#print axioms c302desc8_normalization

theorem c302desc8_step : c302raise7 * c302desc7 = c302desc8 := by decide +kernel

def c302averageRaw : Matrix (Fin 1) (Fin 1) ℚ :=
  ((2/3) : ℚ) • (c302desc2ᵀ * p302rawMform * c302desc2) +
    ((2/9) : ℚ) • (c302desc3ᵀ * p303rawMform * c302desc3) +
    ((1/27) : ℚ) • (c302desc4ᵀ * p304rawMform * c302desc4) +
    ((1/243) : ℚ) • (c302desc5ᵀ * p305rawMform * c302desc5) +
    ((1/2916) : ℚ) • (c302desc6ᵀ * p306rawMform * c302desc6) +
    ((1/43740) : ℚ) • (c302desc7ᵀ * p307rawMform * c302desc7) +
    ((1/787320) : ℚ) • (c302desc8ᵀ * p308rawMform * c302desc8)

theorem c302_COM_reconstructed : c302averageRaw = b302average := by
  unfold c302averageRaw
  rw [p302_Mform_reconstructed, p303_Mform_reconstructed, p304_Mform_reconstructed, p305_Mform_reconstructed, p306_Mform_reconstructed, p307_Mform_reconstructed, p308_Mform_reconstructed]
  decide +kernel

def c302hRaw : Matrix (Fin 1) (Fin 1) ℚ := b302relativeᵀ * p302rawHform * b302relative

def c302sRaw : Matrix (Fin 1) (Fin 1) ℚ :=
  b302relativeᵀ * planarSingleForm p302Ginv p302rawHform * b302relative

theorem c302_h_reconstructed : c302hRaw = b302h := by
  unfold c302hRaw
  rw [p302_Hform_reconstructed]
  decide +kernel

theorem c302_s_reconstructed : c302sRaw = b302s := by
  unfold c302sRaw
  rw [p302_Hform_reconstructed, p302_Sform_reconstructed]
  decide +kernel

def c302comparisonRaw : Matrix (Fin 1) (Fin 1) ℚ :=
  c302sRaw - c302averageRaw + delta • c302hRaw

theorem c302_comparison_reconstructed : c302comparisonRaw = b302comparison := by
  simp only [c302comparisonRaw, c302_s_reconstructed, c302_COM_reconstructed, c302_h_reconstructed, b302comparison, one_smul]

theorem c302_source_comparison_positive :
    (TorusLean.M2.complexify c302comparisonRaw).PosSemidef := by
  rw [c302_comparison_reconstructed]
  exact b302_comparison_positive

#print axioms c302_lowering_reconstructed
#print axioms c302_relative_complete
#print axioms c302_COM_reconstructed
#print axioms c302_h_reconstructed
#print axioms c302_s_reconstructed
#print axioms c302_comparison_reconstructed
#print axioms c302_source_comparison_positive
end TorusLean.BosonFiniteCertificate
