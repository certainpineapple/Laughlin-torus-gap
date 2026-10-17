import torus.shared.BosonFiniteCertificateReconstruct300
import torus.shared.BosonFiniteCertificateReconstruct301
import torus.shared.BosonFiniteCertificateReconstruct302
import torus.shared.BosonFiniteCertificateReconstruct303
import torus.shared.BosonFiniteCertificateReconstruct304
import torus.shared.BosonFiniteCertificateReconstruct305
import torus.shared.BosonFiniteCertificateReconstruct306
import torus.shared.BosonFiniteCertificateReconstruct307
import torus.shared.BosonFiniteCertificateReconstruct308
import torus.shared.BosonFiniteCertificate300
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
open Matrix
open scoped ComplexOrder
namespace TorusLean.BosonFiniteCertificate

def c300lowerRaw : Matrix (Fin 0) (Fin 1) ℚ :=
  fun i j => (loweringEntry ((threeBasis 0)[i.val]?.getD []) (p300basis j) : ℤ)

theorem c300_lowering_reconstructed : c300lowerRaw = b300lower := by decide +kernel

theorem c300_relative_complete (v : Fin 1 → ℚ) :
    c300lowerRaw *ᵥ v = 0 ↔ ∃ x : Fin 1 → ℚ, b300relative *ᵥ x = v := by
  rw [c300_lowering_reconstructed]
  exact b300_relative_exact v

def c300desc0 : Matrix (Fin 1) (Fin 1) ℚ :=
  !![1]

theorem c300desc0_normalization :
    c300desc0ᵀ * (Matrix.diagonal ![6] : Matrix (Fin 1) (Fin 1) ℚ) * c300desc0 =
      (1 : ℚ) • (b300relativeᵀ * (Matrix.diagonal ![6] : Matrix (Fin 1) (Fin 1) ℚ) * b300relative) := by decide +kernel

#print axioms c300desc0_normalization

theorem c300desc0_root : c300desc0 = b300relative := by decide +kernel

def c300raise0 : Matrix (Fin 1) (Fin 1) ℚ :=
  fun i j => (raisingEntry (p301basis i) (p300basis j) : ℤ)

def c300desc1 : Matrix (Fin 1) (Fin 1) ℚ :=
  !![3]

theorem c300desc1_normalization :
    c300desc1ᵀ * (Matrix.diagonal ![2] : Matrix (Fin 1) (Fin 1) ℚ) * c300desc1 =
      (3 : ℚ) • (b300relativeᵀ * (Matrix.diagonal ![6] : Matrix (Fin 1) (Fin 1) ℚ) * b300relative) := by decide +kernel

#print axioms c300desc1_normalization

def c300raise1 : Matrix (Fin 2) (Fin 1) ℚ :=
  fun i j => (raisingEntry (p302basis i) (p301basis j) : ℤ)

theorem c300desc1_step : c300raise0 * c300desc0 = c300desc1 := by decide +kernel

def c300desc2 : Matrix (Fin 2) (Fin 1) ℚ :=
  !![3;
    6]

theorem c300desc2_normalization :
    c300desc2ᵀ * (Matrix.diagonal ![4, 2] : Matrix (Fin 2) (Fin 2) ℚ) * c300desc2 =
      (18 : ℚ) • (b300relativeᵀ * (Matrix.diagonal ![6] : Matrix (Fin 1) (Fin 1) ℚ) * b300relative) := by decide +kernel

#print axioms c300desc2_normalization

def c300raise2 : Matrix (Fin 3) (Fin 2) ℚ :=
  fun i j => (raisingEntry (p303basis i) (p302basis j) : ℤ)

theorem c300desc2_step : c300raise1 * c300desc1 = c300desc2 := by decide +kernel

def c300desc3 : Matrix (Fin 3) (Fin 1) ℚ :=
  !![3;
    18;
    6]

theorem c300desc3_normalization :
    c300desc3ᵀ * (Matrix.diagonal ![12, 2, 6] : Matrix (Fin 3) (Fin 3) ℚ) * c300desc3 =
      (162 : ℚ) • (b300relativeᵀ * (Matrix.diagonal ![6] : Matrix (Fin 1) (Fin 1) ℚ) * b300relative) := by decide +kernel

#print axioms c300desc3_normalization

def c300raise3 : Matrix (Fin 4) (Fin 3) ℚ :=
  fun i j => (raisingEntry (p304basis i) (p303basis j) : ℤ)

theorem c300desc3_step : c300raise2 * c300desc2 = c300desc3 := by decide +kernel

def c300desc4 : Matrix (Fin 4) (Fin 1) ℚ :=
  !![3;
    24;
    18;
    36]

theorem c300desc4_normalization :
    c300desc4ᵀ * (Matrix.diagonal ![48, 6, 8, 4] : Matrix (Fin 4) (Fin 4) ℚ) * c300desc4 =
      (1944 : ℚ) • (b300relativeᵀ * (Matrix.diagonal ![6] : Matrix (Fin 1) (Fin 1) ℚ) * b300relative) := by decide +kernel

#print axioms c300desc4_normalization

def c300raise4 : Matrix (Fin 5) (Fin 4) ℚ :=
  fun i j => (raisingEntry (p305basis i) (p304basis j) : ℤ)

theorem c300desc4_step : c300raise3 * c300desc3 = c300desc4 := by decide +kernel

def c300desc5 : Matrix (Fin 5) (Fin 1) ℚ :=
  !![3;
    30;
    60;
    60;
    90]

theorem c300desc5_normalization :
    c300desc5ᵀ * (Matrix.diagonal ![240, 24, 12, 12, 8] : Matrix (Fin 5) (Fin 5) ℚ) * c300desc5 =
      (29160 : ℚ) • (b300relativeᵀ * (Matrix.diagonal ![6] : Matrix (Fin 1) (Fin 1) ℚ) * b300relative) := by decide +kernel

#print axioms c300desc5_normalization

def c300raise5 : Matrix (Fin 7) (Fin 5) ℚ :=
  fun i j => (raisingEntry (p306basis i) (p305basis j) : ℤ)

theorem c300desc5_step : c300raise4 * c300desc4 = c300desc5 := by decide +kernel

def c300desc6 : Matrix (Fin 7) (Fin 1) ℚ :=
  !![3;
    36;
    90;
    60;
    90;
    360;
    90]

theorem c300desc6_normalization :
    c300desc6ᵀ * (Matrix.diagonal ![1440, 120, 48, 72, 48, 12, 48] : Matrix (Fin 7) (Fin 7) ℚ) * c300desc6 =
      (524880 : ℚ) • (b300relativeᵀ * (Matrix.diagonal ![6] : Matrix (Fin 1) (Fin 1) ℚ) * b300relative) := by decide +kernel

#print axioms c300desc6_normalization

def c300raise6 : Matrix (Fin 8) (Fin 7) ℚ :=
  fun i j => (raisingEntry (p307basis i) (p306basis j) : ℤ)

theorem c300desc6_step : c300raise5 * c300desc5 = c300desc6 := by decide +kernel

def c300desc7 : Matrix (Fin 8) (Fin 1) ℚ :=
  !![3;
    42;
    126;
    210;
    126;
    630;
    420;
    630]

theorem c300desc7_normalization :
    c300desc7ᵀ * (Matrix.diagonal ![10080, 720, 240, 144, 240, 48, 72, 48] : Matrix (Fin 8) (Fin 8) ℚ) * c300desc7 =
      (11022480 : ℚ) • (b300relativeᵀ * (Matrix.diagonal ![6] : Matrix (Fin 1) (Fin 1) ℚ) * b300relative) := by decide +kernel

#print axioms c300desc7_normalization

def c300raise7 : Matrix (Fin 10) (Fin 8) ℚ :=
  fun i j => (raisingEntry (p308basis i) (p307basis j) : ℤ)

theorem c300desc7_step : c300raise6 * c300desc6 = c300desc7 := by decide +kernel

def c300desc8 : Matrix (Fin 10) (Fin 1) ℚ :=
  !![3;
    48;
    168;
    336;
    210;
    168;
    1008;
    1680;
    1260;
    1680]

theorem c300desc8_normalization :
    c300desc8ᵀ * (Matrix.diagonal ![80640, 5040, 1440, 720, 1152, 1440, 240, 144, 192, 144] : Matrix (Fin 10) (Fin 10) ℚ) * c300desc8 =
      (264539520 : ℚ) • (b300relativeᵀ * (Matrix.diagonal ![6] : Matrix (Fin 1) (Fin 1) ℚ) * b300relative) := by decide +kernel

#print axioms c300desc8_normalization

theorem c300desc8_step : c300raise7 * c300desc7 = c300desc8 := by decide +kernel

def c300averageRaw : Matrix (Fin 1) (Fin 1) ℚ :=
  ((2/3) : ℚ) • (c300desc0ᵀ * p300rawMform * c300desc0) +
    ((2/9) : ℚ) • (c300desc1ᵀ * p301rawMform * c300desc1) +
    ((1/27) : ℚ) • (c300desc2ᵀ * p302rawMform * c300desc2) +
    ((1/243) : ℚ) • (c300desc3ᵀ * p303rawMform * c300desc3) +
    ((1/2916) : ℚ) • (c300desc4ᵀ * p304rawMform * c300desc4) +
    ((1/43740) : ℚ) • (c300desc5ᵀ * p305rawMform * c300desc5) +
    ((1/787320) : ℚ) • (c300desc6ᵀ * p306rawMform * c300desc6) +
    ((1/16533720) : ℚ) • (c300desc7ᵀ * p307rawMform * c300desc7) +
    ((1/396809280) : ℚ) • (c300desc8ᵀ * p308rawMform * c300desc8)

theorem c300_COM_reconstructed : c300averageRaw = b300average := by
  unfold c300averageRaw
  rw [p300_Mform_reconstructed, p301_Mform_reconstructed, p302_Mform_reconstructed, p303_Mform_reconstructed, p304_Mform_reconstructed, p305_Mform_reconstructed, p306_Mform_reconstructed, p307_Mform_reconstructed, p308_Mform_reconstructed]
  decide +kernel

def c300hRaw : Matrix (Fin 1) (Fin 1) ℚ := b300relativeᵀ * p300rawHform * b300relative

def c300sRaw : Matrix (Fin 1) (Fin 1) ℚ :=
  b300relativeᵀ * planarSingleForm p300Ginv p300rawHform * b300relative

theorem c300_h_reconstructed : c300hRaw = b300h := by
  unfold c300hRaw
  rw [p300_Hform_reconstructed]
  decide +kernel

theorem c300_s_reconstructed : c300sRaw = b300s := by
  unfold c300sRaw
  rw [p300_Hform_reconstructed, p300_Sform_reconstructed]
  decide +kernel

def c300comparisonRaw : Matrix (Fin 1) (Fin 1) ℚ :=
  c300sRaw - c300averageRaw + delta • c300hRaw

theorem c300_comparison_reconstructed : c300comparisonRaw = b300comparison := by
  simp only [c300comparisonRaw, c300_s_reconstructed, c300_COM_reconstructed, c300_h_reconstructed, b300comparison, one_smul]

theorem c300_source_comparison_positive :
    (TorusLean.M2.complexify c300comparisonRaw).PosSemidef := by
  rw [c300_comparison_reconstructed]
  exact b300_comparison_positive

#print axioms c300_lowering_reconstructed
#print axioms c300_relative_complete
#print axioms c300_COM_reconstructed
#print axioms c300_h_reconstructed
#print axioms c300_s_reconstructed
#print axioms c300_comparison_reconstructed
#print axioms c300_source_comparison_positive
end TorusLean.BosonFiniteCertificate
