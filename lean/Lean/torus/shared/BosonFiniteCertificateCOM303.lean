import torus.shared.BosonFiniteCertificateReconstruct303
import torus.shared.BosonFiniteCertificateReconstruct304
import torus.shared.BosonFiniteCertificateReconstruct305
import torus.shared.BosonFiniteCertificateReconstruct306
import torus.shared.BosonFiniteCertificateReconstruct307
import torus.shared.BosonFiniteCertificateReconstruct308
import torus.shared.BosonFiniteCertificate303
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
open Matrix
open scoped ComplexOrder
namespace TorusLean.BosonFiniteCertificate

def c303lowerRaw : Matrix (Fin 2) (Fin 3) ℚ :=
  fun i j => (loweringEntry ((threeBasis 2)[i.val]?.getD []) (p303basis j) : ℤ)

theorem c303_lowering_reconstructed : c303lowerRaw = b303lower := by decide +kernel

theorem c303_relative_complete (v : Fin 3 → ℚ) :
    c303lowerRaw *ᵥ v = 0 ↔ ∃ x : Fin 1 → ℚ, b303relative *ᵥ x = v := by
  rw [c303_lowering_reconstructed]
  exact b303_relative_exact v

def c303desc3 : Matrix (Fin 3) (Fin 1) ℚ :=
  !![(1/2);
    (-3/2);
    1]

theorem c303desc3_normalization :
    c303desc3ᵀ * (Matrix.diagonal ![12, 2, 6] : Matrix (Fin 3) (Fin 3) ℚ) * c303desc3 =
      (1 : ℚ) • (b303relativeᵀ * (Matrix.diagonal ![12, 2, 6] : Matrix (Fin 3) (Fin 3) ℚ) * b303relative) := by decide +kernel

#print axioms c303desc3_normalization

theorem c303desc3_root : c303desc3 = b303relative := by decide +kernel

def c303raise3 : Matrix (Fin 4) (Fin 3) ℚ :=
  fun i j => (raisingEntry (p304basis i) (p303basis j) : ℤ)

def c303desc4 : Matrix (Fin 4) (Fin 1) ℚ :=
  !![(1/2);
    (-1/2);
    (-3/2);
    (3/2)]

theorem c303desc4_normalization :
    c303desc4ᵀ * (Matrix.diagonal ![48, 6, 8, 4] : Matrix (Fin 4) (Fin 4) ℚ) * c303desc4 =
      (3 : ℚ) • (b303relativeᵀ * (Matrix.diagonal ![12, 2, 6] : Matrix (Fin 3) (Fin 3) ℚ) * b303relative) := by decide +kernel

#print axioms c303desc4_normalization

def c303raise4 : Matrix (Fin 5) (Fin 4) ℚ :=
  fun i j => (raisingEntry (p305basis i) (p304basis j) : ℤ)

theorem c303desc4_step : c303raise3 * c303desc3 = c303desc4 := by decide +kernel

def c303desc5 : Matrix (Fin 5) (Fin 1) ℚ :=
  !![(1/2);
    (1/2);
    (-7/2);
    1;
    (3/2)]

theorem c303desc5_normalization :
    c303desc5ᵀ * (Matrix.diagonal ![240, 24, 12, 12, 8] : Matrix (Fin 5) (Fin 5) ℚ) * c303desc5 =
      (18 : ℚ) • (b303relativeᵀ * (Matrix.diagonal ![12, 2, 6] : Matrix (Fin 3) (Fin 3) ℚ) * b303relative) := by decide +kernel

#print axioms c303desc5_normalization

def c303raise5 : Matrix (Fin 7) (Fin 5) ℚ :=
  fun i j => (raisingEntry (p306basis i) (p305basis j) : ℤ)

theorem c303desc5_step : c303raise4 * c303desc4 = c303desc5 := by decide +kernel

def c303desc6 : Matrix (Fin 7) (Fin 1) ℚ :=
  !![(1/2);
    (3/2);
    -3;
    (-7/2);
    (3/2);
    (3/2);
    (3/2)]

theorem c303desc6_normalization :
    c303desc6ᵀ * (Matrix.diagonal ![1440, 120, 48, 72, 48, 12, 48] : Matrix (Fin 7) (Fin 7) ℚ) * c303desc6 =
      (162 : ℚ) • (b303relativeᵀ * (Matrix.diagonal ![12, 2, 6] : Matrix (Fin 3) (Fin 3) ℚ) * b303relative) := by decide +kernel

#print axioms c303desc6_normalization

def c303raise6 : Matrix (Fin 8) (Fin 7) ℚ :=
  fun i j => (raisingEntry (p307basis i) (p306basis j) : ℤ)

theorem c303desc6_step : c303raise5 * c303desc5 = c303desc6 := by decide +kernel

def c303desc7 : Matrix (Fin 8) (Fin 1) ℚ :=
  !![(1/2);
    (5/2);
    (-3/2);
    -10;
    3;
    (3/2);
    -2;
    6]

theorem c303desc7_normalization :
    c303desc7ᵀ * (Matrix.diagonal ![10080, 720, 240, 144, 240, 48, 72, 48] : Matrix (Fin 8) (Fin 8) ℚ) * c303desc7 =
      (1944 : ℚ) • (b303relativeᵀ * (Matrix.diagonal ![12, 2, 6] : Matrix (Fin 3) (Fin 3) ℚ) * b303relative) := by decide +kernel

#print axioms c303desc7_normalization

def c303raise7 : Matrix (Fin 10) (Fin 8) ℚ :=
  fun i j => (raisingEntry (p308basis i) (p307basis j) : ℤ)

theorem c303desc7_step : c303raise6 * c303desc6 = c303desc7 := by decide +kernel

def c303desc8 : Matrix (Fin 10) (Fin 1) ℚ :=
  !![(1/2);
    (7/2);
    1;
    (-23/2);
    -10;
    (11/2);
    6;
    (-25/2);
    (15/2);
    10]

theorem c303desc8_normalization :
    c303desc8ᵀ * (Matrix.diagonal ![80640, 5040, 1440, 720, 1152, 1440, 240, 144, 192, 144] : Matrix (Fin 10) (Fin 10) ℚ) * c303desc8 =
      (29160 : ℚ) • (b303relativeᵀ * (Matrix.diagonal ![12, 2, 6] : Matrix (Fin 3) (Fin 3) ℚ) * b303relative) := by decide +kernel

#print axioms c303desc8_normalization

theorem c303desc8_step : c303raise7 * c303desc7 = c303desc8 := by decide +kernel

def c303averageRaw : Matrix (Fin 1) (Fin 1) ℚ :=
  ((2/3) : ℚ) • (c303desc3ᵀ * p303rawMform * c303desc3) +
    ((2/9) : ℚ) • (c303desc4ᵀ * p304rawMform * c303desc4) +
    ((1/27) : ℚ) • (c303desc5ᵀ * p305rawMform * c303desc5) +
    ((1/243) : ℚ) • (c303desc6ᵀ * p306rawMform * c303desc6) +
    ((1/2916) : ℚ) • (c303desc7ᵀ * p307rawMform * c303desc7) +
    ((1/43740) : ℚ) • (c303desc8ᵀ * p308rawMform * c303desc8)

theorem c303_COM_reconstructed : c303averageRaw = b303average := by
  unfold c303averageRaw
  rw [p303_Mform_reconstructed, p304_Mform_reconstructed, p305_Mform_reconstructed, p306_Mform_reconstructed, p307_Mform_reconstructed, p308_Mform_reconstructed]
  decide +kernel

def c303hRaw : Matrix (Fin 1) (Fin 1) ℚ := b303relativeᵀ * p303rawHform * b303relative

def c303sRaw : Matrix (Fin 1) (Fin 1) ℚ :=
  b303relativeᵀ * planarSingleForm p303Ginv p303rawHform * b303relative

theorem c303_h_reconstructed : c303hRaw = b303h := by
  unfold c303hRaw
  rw [p303_Hform_reconstructed]
  decide +kernel

theorem c303_s_reconstructed : c303sRaw = b303s := by
  unfold c303sRaw
  rw [p303_Hform_reconstructed, p303_Sform_reconstructed]
  decide +kernel

def c303comparisonRaw : Matrix (Fin 1) (Fin 1) ℚ :=
  c303sRaw - c303averageRaw + delta • c303hRaw

theorem c303_comparison_reconstructed : c303comparisonRaw = b303comparison := by
  simp only [c303comparisonRaw, c303_s_reconstructed, c303_COM_reconstructed, c303_h_reconstructed, b303comparison, one_smul]

theorem c303_source_comparison_positive :
    (TorusLean.M2.complexify c303comparisonRaw).PosSemidef := by
  rw [c303_comparison_reconstructed]
  exact b303_comparison_positive

#print axioms c303_lowering_reconstructed
#print axioms c303_relative_complete
#print axioms c303_COM_reconstructed
#print axioms c303_h_reconstructed
#print axioms c303_s_reconstructed
#print axioms c303_comparison_reconstructed
#print axioms c303_source_comparison_positive
end TorusLean.BosonFiniteCertificate
