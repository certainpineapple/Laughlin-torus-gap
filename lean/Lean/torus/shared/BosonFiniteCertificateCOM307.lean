import torus.shared.BosonFiniteCertificateReconstruct307
import torus.shared.BosonFiniteCertificateReconstruct308
import torus.shared.BosonFiniteCertificate307
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
open Matrix
open scoped ComplexOrder
namespace TorusLean.BosonFiniteCertificate

def c307lowerRaw : Matrix (Fin 7) (Fin 8) ℚ :=
  fun i j => (loweringEntry ((threeBasis 6)[i.val]?.getD []) (p307basis j) : ℤ)

theorem c307_lowering_reconstructed : c307lowerRaw = b307lower := by decide +kernel

theorem c307_relative_complete (v : Fin 8 → ℚ) :
    c307lowerRaw *ᵥ v = 0 ↔ ∃ x : Fin 1 → ℚ, b307relative *ᵥ x = v := by
  rw [c307_lowering_reconstructed]
  exact b307_relative_exact v

def c307desc7 : Matrix (Fin 8) (Fin 1) ℚ :=
  !![(1/20);
    (-7/20);
    (9/20);
    (-1/4);
    (3/5);
    (-3/2);
    1;
    0]

theorem c307desc7_normalization :
    c307desc7ᵀ * (Matrix.diagonal ![10080, 720, 240, 144, 240, 48, 72, 48] : Matrix (Fin 8) (Fin 8) ℚ) * c307desc7 =
      (1 : ℚ) • (b307relativeᵀ * (Matrix.diagonal ![10080, 720, 240, 144, 240, 48, 72, 48] : Matrix (Fin 8) (Fin 8) ℚ) * b307relative) := by decide +kernel

#print axioms c307desc7_normalization

theorem c307desc7_root : c307desc7 = b307relative := by decide +kernel

def c307raise7 : Matrix (Fin 10) (Fin 8) ℚ :=
  fun i j => (raisingEntry (p308basis i) (p307basis j) : ℤ)

def c307desc8 : Matrix (Fin 10) (Fin 1) ℚ :=
  !![(1/20);
    (-1/4);
    (1/10);
    (1/5);
    (-1/4);
    (1/4);
    (3/20);
    (1/4);
    (-3/2);
    1]

theorem c307desc8_normalization :
    c307desc8ᵀ * (Matrix.diagonal ![80640, 5040, 1440, 720, 1152, 1440, 240, 144, 192, 144] : Matrix (Fin 10) (Fin 10) ℚ) * c307desc8 =
      (3 : ℚ) • (b307relativeᵀ * (Matrix.diagonal ![10080, 720, 240, 144, 240, 48, 72, 48] : Matrix (Fin 8) (Fin 8) ℚ) * b307relative) := by decide +kernel

#print axioms c307desc8_normalization

theorem c307desc8_step : c307raise7 * c307desc7 = c307desc8 := by decide +kernel

def c307averageRaw : Matrix (Fin 1) (Fin 1) ℚ :=
  ((2/3) : ℚ) • (c307desc7ᵀ * p307rawMform * c307desc7) +
    ((2/9) : ℚ) • (c307desc8ᵀ * p308rawMform * c307desc8)

theorem c307_COM_reconstructed : c307averageRaw = b307average := by
  unfold c307averageRaw
  rw [p307_Mform_reconstructed, p308_Mform_reconstructed]
  decide +kernel

def c307hRaw : Matrix (Fin 1) (Fin 1) ℚ := b307relativeᵀ * p307rawHform * b307relative

def c307sRaw : Matrix (Fin 1) (Fin 1) ℚ :=
  b307relativeᵀ * planarSingleForm p307Ginv p307rawHform * b307relative

theorem c307_h_reconstructed : c307hRaw = b307h := by
  unfold c307hRaw
  rw [p307_Hform_reconstructed]
  decide +kernel

theorem c307_s_reconstructed : c307sRaw = b307s := by
  unfold c307sRaw
  rw [p307_Hform_reconstructed, p307_Sform_reconstructed]
  decide +kernel

def c307comparisonRaw : Matrix (Fin 1) (Fin 1) ℚ :=
  c307sRaw - c307averageRaw + delta • c307hRaw

theorem c307_comparison_reconstructed : c307comparisonRaw = b307comparison := by
  simp only [c307comparisonRaw, c307_s_reconstructed, c307_COM_reconstructed, c307_h_reconstructed, b307comparison, one_smul]

theorem c307_source_comparison_positive :
    (TorusLean.M2.complexify c307comparisonRaw).PosSemidef := by
  rw [c307_comparison_reconstructed]
  exact b307_comparison_positive

#print axioms c307_lowering_reconstructed
#print axioms c307_relative_complete
#print axioms c307_COM_reconstructed
#print axioms c307_h_reconstructed
#print axioms c307_s_reconstructed
#print axioms c307_comparison_reconstructed
#print axioms c307_source_comparison_positive
end TorusLean.BosonFiniteCertificate
