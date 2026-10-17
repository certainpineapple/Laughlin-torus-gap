import torus.shared.BosonFiniteCertificateReconstruct305
import torus.shared.BosonFiniteCertificateReconstruct306
import torus.shared.BosonFiniteCertificateReconstruct307
import torus.shared.BosonFiniteCertificateReconstruct308
import torus.shared.BosonFiniteCertificate305
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
open Matrix
open scoped ComplexOrder
namespace TorusLean.BosonFiniteCertificate

def c305lowerRaw : Matrix (Fin 4) (Fin 5) ℚ :=
  fun i j => (loweringEntry ((threeBasis 4)[i.val]?.getD []) (p305basis j) : ℤ)

theorem c305_lowering_reconstructed : c305lowerRaw = b305lower := by decide +kernel

theorem c305_relative_complete (v : Fin 5 → ℚ) :
    c305lowerRaw *ᵥ v = 0 ↔ ∃ x : Fin 1 → ℚ, b305relative *ᵥ x = v := by
  rw [c305_lowering_reconstructed]
  exact b305_relative_exact v

def c305desc5 : Matrix (Fin 5) (Fin 1) ℚ :=
  !![(-1/6);
    (5/6);
    (-1/3);
    (-4/3);
    1]

theorem c305desc5_normalization :
    c305desc5ᵀ * (Matrix.diagonal ![240, 24, 12, 12, 8] : Matrix (Fin 5) (Fin 5) ℚ) * c305desc5 =
      (1 : ℚ) • (b305relativeᵀ * (Matrix.diagonal ![240, 24, 12, 12, 8] : Matrix (Fin 5) (Fin 5) ℚ) * b305relative) := by decide +kernel

#print axioms c305desc5_normalization

theorem c305desc5_root : c305desc5 = b305relative := by decide +kernel

def c305raise5 : Matrix (Fin 7) (Fin 5) ℚ :=
  fun i j => (raisingEntry (p306basis i) (p305basis j) : ℤ)

def c305desc6 : Matrix (Fin 7) (Fin 1) ℚ :=
  !![(-1/6);
    (1/2);
    (1/2);
    (-1/3);
    (-1/2);
    -1;
    1]

theorem c305desc6_normalization :
    c305desc6ᵀ * (Matrix.diagonal ![1440, 120, 48, 72, 48, 12, 48] : Matrix (Fin 7) (Fin 7) ℚ) * c305desc6 =
      (3 : ℚ) • (b305relativeᵀ * (Matrix.diagonal ![240, 24, 12, 12, 8] : Matrix (Fin 5) (Fin 5) ℚ) * b305relative) := by decide +kernel

#print axioms c305desc6_normalization

def c305raise6 : Matrix (Fin 8) (Fin 7) ℚ :=
  fun i j => (raisingEntry (p307basis i) (p306basis j) : ℤ)

theorem c305desc6_step : c305raise5 * c305desc5 = c305desc6 := by decide +kernel

def c305desc7 : Matrix (Fin 8) (Fin 1) ℚ :=
  !![(-1/6);
    (1/6);
    1;
    (-1/6);
    0;
    (-3/2);
    (-4/3);
    2]

theorem c305desc7_normalization :
    c305desc7ᵀ * (Matrix.diagonal ![10080, 720, 240, 144, 240, 48, 72, 48] : Matrix (Fin 8) (Fin 8) ℚ) * c305desc7 =
      (18 : ℚ) • (b305relativeᵀ * (Matrix.diagonal ![240, 24, 12, 12, 8] : Matrix (Fin 5) (Fin 5) ℚ) * b305relative) := by decide +kernel

#print axioms c305desc7_normalization

def c305raise7 : Matrix (Fin 10) (Fin 8) ℚ :=
  fun i j => (raisingEntry (p308basis i) (p307basis j) : ℤ)

theorem c305desc7_step : c305raise6 * c305desc6 = c305desc7 := by decide +kernel

def c305desc8 : Matrix (Fin 10) (Fin 1) ℚ :=
  !![(-1/6);
    (-1/6);
    (7/6);
    (5/6);
    (-1/6);
    (1/6);
    (-1/2);
    (-13/3);
    (1/2);
    (8/3)]

theorem c305desc8_normalization :
    c305desc8ᵀ * (Matrix.diagonal ![80640, 5040, 1440, 720, 1152, 1440, 240, 144, 192, 144] : Matrix (Fin 10) (Fin 10) ℚ) * c305desc8 =
      (162 : ℚ) • (b305relativeᵀ * (Matrix.diagonal ![240, 24, 12, 12, 8] : Matrix (Fin 5) (Fin 5) ℚ) * b305relative) := by decide +kernel

#print axioms c305desc8_normalization

theorem c305desc8_step : c305raise7 * c305desc7 = c305desc8 := by decide +kernel

def c305averageRaw : Matrix (Fin 1) (Fin 1) ℚ :=
  ((2/3) : ℚ) • (c305desc5ᵀ * p305rawMform * c305desc5) +
    ((2/9) : ℚ) • (c305desc6ᵀ * p306rawMform * c305desc6) +
    ((1/27) : ℚ) • (c305desc7ᵀ * p307rawMform * c305desc7) +
    ((1/243) : ℚ) • (c305desc8ᵀ * p308rawMform * c305desc8)

theorem c305_COM_reconstructed : c305averageRaw = b305average := by
  unfold c305averageRaw
  rw [p305_Mform_reconstructed, p306_Mform_reconstructed, p307_Mform_reconstructed, p308_Mform_reconstructed]
  decide +kernel

def c305hRaw : Matrix (Fin 1) (Fin 1) ℚ := b305relativeᵀ * p305rawHform * b305relative

def c305sRaw : Matrix (Fin 1) (Fin 1) ℚ :=
  b305relativeᵀ * planarSingleForm p305Ginv p305rawHform * b305relative

theorem c305_h_reconstructed : c305hRaw = b305h := by
  unfold c305hRaw
  rw [p305_Hform_reconstructed]
  decide +kernel

theorem c305_s_reconstructed : c305sRaw = b305s := by
  unfold c305sRaw
  rw [p305_Hform_reconstructed, p305_Sform_reconstructed]
  decide +kernel

def c305comparisonRaw : Matrix (Fin 1) (Fin 1) ℚ :=
  c305sRaw - c305averageRaw + delta • c305hRaw

theorem c305_comparison_reconstructed : c305comparisonRaw = b305comparison := by
  simp only [c305comparisonRaw, c305_s_reconstructed, c305_COM_reconstructed, c305_h_reconstructed, b305comparison, one_smul]

theorem c305_source_comparison_positive :
    (TorusLean.M2.complexify c305comparisonRaw).PosSemidef := by
  rw [c305_comparison_reconstructed]
  exact b305_comparison_positive

#print axioms c305_lowering_reconstructed
#print axioms c305_relative_complete
#print axioms c305_COM_reconstructed
#print axioms c305_h_reconstructed
#print axioms c305_s_reconstructed
#print axioms c305_comparison_reconstructed
#print axioms c305_source_comparison_positive
end TorusLean.BosonFiniteCertificate
