import torus.shared.BosonFiniteCertificateReconstruct308
import torus.shared.BosonFiniteCertificate308
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
open Matrix
open scoped ComplexOrder
namespace TorusLean.BosonFiniteCertificate

def c308lowerRaw : Matrix (Fin 8) (Fin 10) ℚ :=
  fun i j => (loweringEntry ((threeBasis 7)[i.val]?.getD []) (p308basis j) : ℤ)

theorem c308_lowering_reconstructed : c308lowerRaw = b308lower := by decide +kernel

theorem c308_relative_complete (v : Fin 10 → ℚ) :
    c308lowerRaw *ᵥ v = 0 ↔ ∃ x : Fin 2 → ℚ, b308relative *ᵥ x = v := by
  rw [c308_lowering_reconstructed]
  exact b308_relative_exact v

def c308desc8 : Matrix (Fin 10) (Fin 2) ℚ :=
  !![(1/35), (-1/35);
    (-8/35), (8/35);
    (4/5), (-3/10);
    (-8/5), (1/10);
    1, 0;
    0, (-1/2);
    0, (3/2);
    0, (-1/2);
    0, (-3/2);
    0, 1]

theorem c308desc8_normalization :
    c308desc8ᵀ * (Matrix.diagonal ![80640, 5040, 1440, 720, 1152, 1440, 240, 144, 192, 144] : Matrix (Fin 10) (Fin 10) ℚ) * c308desc8 =
      (1 : ℚ) • (b308relativeᵀ * (Matrix.diagonal ![80640, 5040, 1440, 720, 1152, 1440, 240, 144, 192, 144] : Matrix (Fin 10) (Fin 10) ℚ) * b308relative) := by decide +kernel

#print axioms c308desc8_normalization

theorem c308desc8_root : c308desc8 = b308relative := by decide +kernel

def c308averageRaw : Matrix (Fin 2) (Fin 2) ℚ :=
  ((2/3) : ℚ) • (c308desc8ᵀ * p308rawMform * c308desc8)

theorem c308_COM_reconstructed : c308averageRaw = b308average := by
  unfold c308averageRaw
  rw [p308_Mform_reconstructed]
  decide +kernel

def c308hRaw : Matrix (Fin 2) (Fin 2) ℚ := b308relativeᵀ * p308rawHform * b308relative

def c308sRaw : Matrix (Fin 2) (Fin 2) ℚ :=
  b308relativeᵀ * planarSingleForm p308Ginv p308rawHform * b308relative

theorem c308_h_reconstructed : c308hRaw = b308h := by
  unfold c308hRaw
  rw [p308_Hform_reconstructed]
  decide +kernel

theorem c308_s_reconstructed : c308sRaw = b308s := by
  unfold c308sRaw
  rw [p308_Hform_reconstructed, p308_Sform_reconstructed]
  decide +kernel

def c308comparisonRaw : Matrix (Fin 2) (Fin 2) ℚ :=
  c308sRaw - c308averageRaw + delta • c308hRaw

theorem c308_comparison_reconstructed : c308comparisonRaw = b308comparison := by
  simp only [c308comparisonRaw, c308_s_reconstructed, c308_COM_reconstructed, c308_h_reconstructed, b308comparison, one_smul]

theorem c308_source_comparison_positive :
    (TorusLean.M2.complexify c308comparisonRaw).PosSemidef := by
  rw [c308_comparison_reconstructed]
  exact b308_comparison_positive

#print axioms c308_lowering_reconstructed
#print axioms c308_relative_complete
#print axioms c308_COM_reconstructed
#print axioms c308_h_reconstructed
#print axioms c308_s_reconstructed
#print axioms c308_comparison_reconstructed
#print axioms c308_source_comparison_positive
end TorusLean.BosonFiniteCertificate
