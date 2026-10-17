import torus.shared.BosonFiniteCertificateReconstruct306
import torus.shared.BosonFiniteCertificateReconstruct307
import torus.shared.BosonFiniteCertificateReconstruct308
import torus.shared.BosonFiniteCertificate306
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
open Matrix
open scoped ComplexOrder
namespace TorusLean.BosonFiniteCertificate

def c306lowerRaw : Matrix (Fin 5) (Fin 7) ℚ :=
  fun i j => (loweringEntry ((threeBasis 5)[i.val]?.getD []) (p306basis j) : ℤ)

theorem c306_lowering_reconstructed : c306lowerRaw = b306lower := by decide +kernel

theorem c306_relative_complete (v : Fin 7 → ℚ) :
    c306lowerRaw *ᵥ v = 0 ↔ ∃ x : Fin 2 → ℚ, b306relative *ᵥ x = v := by
  rw [c306_lowering_reconstructed]
  exact b306_relative_exact v

def c306desc6 : Matrix (Fin 7) (Fin 2) ℚ :=
  !![(-1/10), (1/10);
    (3/5), (-3/5);
    (-3/2), (1/2);
    1, 0;
    0, 1;
    0, -2;
    0, 1]

theorem c306desc6_normalization :
    c306desc6ᵀ * (Matrix.diagonal ![1440, 120, 48, 72, 48, 12, 48] : Matrix (Fin 7) (Fin 7) ℚ) * c306desc6 =
      (1 : ℚ) • (b306relativeᵀ * (Matrix.diagonal ![1440, 120, 48, 72, 48, 12, 48] : Matrix (Fin 7) (Fin 7) ℚ) * b306relative) := by decide +kernel

#print axioms c306desc6_normalization

theorem c306desc6_root : c306desc6 = b306relative := by decide +kernel

def c306raise6 : Matrix (Fin 8) (Fin 7) ℚ :=
  fun i j => (raisingEntry (p307basis i) (p306basis j) : ℤ)

def c306desc7 : Matrix (Fin 8) (Fin 2) ℚ :=
  !![(-1/10), (1/10);
    (2/5), (-2/5);
    (-9/10), (-1/10);
    (1/2), (1/2);
    (3/5), (2/5);
    (-3/2), (1/2);
    1, -2;
    0, 1]

theorem c306desc7_normalization :
    c306desc7ᵀ * (Matrix.diagonal ![10080, 720, 240, 144, 240, 48, 72, 48] : Matrix (Fin 8) (Fin 8) ℚ) * c306desc7 =
      (3 : ℚ) • (b306relativeᵀ * (Matrix.diagonal ![1440, 120, 48, 72, 48, 12, 48] : Matrix (Fin 7) (Fin 7) ℚ) * b306relative) := by decide +kernel

#print axioms c306desc7_normalization

def c306raise7 : Matrix (Fin 10) (Fin 8) ℚ :=
  fun i j => (raisingEntry (p308basis i) (p307basis j) : ℤ)

theorem c306desc7_step : c306raise6 * c306desc6 = c306desc7 := by decide +kernel

def c306desc8 : Matrix (Fin 10) (Fin 2) ℚ :=
  !![(-1/10), (1/10);
    (1/5), (-1/5);
    (-1/2), (-1/2);
    (-2/5), (2/5);
    (1/2), (1/2);
    1, 0;
    (-6/5), (6/5);
    1, -3;
    (-3/2), (3/2);
    1, 0]

theorem c306desc8_normalization :
    c306desc8ᵀ * (Matrix.diagonal ![80640, 5040, 1440, 720, 1152, 1440, 240, 144, 192, 144] : Matrix (Fin 10) (Fin 10) ℚ) * c306desc8 =
      (18 : ℚ) • (b306relativeᵀ * (Matrix.diagonal ![1440, 120, 48, 72, 48, 12, 48] : Matrix (Fin 7) (Fin 7) ℚ) * b306relative) := by decide +kernel

#print axioms c306desc8_normalization

theorem c306desc8_step : c306raise7 * c306desc7 = c306desc8 := by decide +kernel

def c306averageRaw : Matrix (Fin 2) (Fin 2) ℚ :=
  ((2/3) : ℚ) • (c306desc6ᵀ * p306rawMform * c306desc6) +
    ((2/9) : ℚ) • (c306desc7ᵀ * p307rawMform * c306desc7) +
    ((1/27) : ℚ) • (c306desc8ᵀ * p308rawMform * c306desc8)

theorem c306_COM_reconstructed : c306averageRaw = b306average := by
  unfold c306averageRaw
  rw [p306_Mform_reconstructed, p307_Mform_reconstructed, p308_Mform_reconstructed]
  decide +kernel

def c306hRaw : Matrix (Fin 2) (Fin 2) ℚ := b306relativeᵀ * p306rawHform * b306relative

def c306sRaw : Matrix (Fin 2) (Fin 2) ℚ :=
  b306relativeᵀ * planarSingleForm p306Ginv p306rawHform * b306relative

theorem c306_h_reconstructed : c306hRaw = b306h := by
  unfold c306hRaw
  rw [p306_Hform_reconstructed]
  decide +kernel

theorem c306_s_reconstructed : c306sRaw = b306s := by
  unfold c306sRaw
  rw [p306_Hform_reconstructed, p306_Sform_reconstructed]
  decide +kernel

def c306comparisonRaw : Matrix (Fin 2) (Fin 2) ℚ :=
  c306sRaw - c306averageRaw + delta • c306hRaw

theorem c306_comparison_reconstructed : c306comparisonRaw = b306comparison := by
  simp only [c306comparisonRaw, c306_s_reconstructed, c306_COM_reconstructed, c306_h_reconstructed, b306comparison, one_smul]

theorem c306_source_comparison_positive :
    (TorusLean.M2.complexify c306comparisonRaw).PosSemidef := by
  rw [c306_comparison_reconstructed]
  exact b306_comparison_positive

#print axioms c306_lowering_reconstructed
#print axioms c306_relative_complete
#print axioms c306_COM_reconstructed
#print axioms c306_h_reconstructed
#print axioms c306_s_reconstructed
#print axioms c306_comparison_reconstructed
#print axioms c306_source_comparison_positive
end TorusLean.BosonFiniteCertificate
