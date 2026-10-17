import torus.shared.BosonFiniteCertificateNatCOMBasisGramBlocks300
import torus.shared.BosonFiniteCertificateNatCOMBasisGramBlocks301
import torus.shared.BosonFiniteCertificateNatCOMBasisGramBlocks302
import torus.shared.BosonFiniteCertificateNatCOMBasisGramBlocks303
import torus.shared.BosonFiniteCertificateNatCOMBasisGramBlocks304
import torus.shared.BosonFiniteCertificateNatCOMBasisGramBlocks305
import torus.shared.BosonFiniteCertificateNatCOMBasisGramBlocks306
import torus.shared.BosonFiniteCertificateNatCOMBasisGramBlocks307
import torus.shared.BosonFiniteCertificateNatCOMBasisGramBlocks308
import torus.shared.BosonFiniteCertificateCanonicalCompressionCore

/-! The finite same-relative-label weighted average of the genuine full
COM rank coefficient. The original full cross matrices remain untouched;
these are the blocks selected only after a separate physical cell trace. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open Matrix TorusLean.M2 TorusLean.Boson
open TorusLean.Shared.BosonFiniteCertificateCoordinate
open scoped BigOperators ComplexConjugate

private theorem natCOM_complexify_submatrix {m n r t : ℕ}
    (A : Matrix (Fin m) (Fin n) ℚ) (f : Fin r → Fin m) (g : Fin t → Fin n) :
    complexify (A.submatrix f g) = (complexify A).submatrix f g := rfl

def k300COMColumn0 (a : Fin 1) : Fin 1 := ⟨0+a.val,by omega⟩

private theorem k300COMColumn0_label (a : Fin 1) :
    k300COMLabel9 (k300COMColumn0 a) = ⟨(⟨0,by decide⟩ : Fin 9),
      ⟨a.val,by simpa [natCOMRelativeDimension] using a.isLt⟩⟩ := by
  fin_cases a <;> rfl

def k300COMColumn1 (a : Fin 1) : Fin 1 := ⟨0+a.val,by omega⟩

private theorem k300COMColumn1_label (a : Fin 1) :
    k301COMLabel9 (k300COMColumn1 a) = ⟨(⟨0,by decide⟩ : Fin 9),
      ⟨a.val,by simpa [natCOMRelativeDimension] using a.isLt⟩⟩ := by
  fin_cases a <;> rfl

def k300COMColumn2 (a : Fin 1) : Fin 2 := ⟨0+a.val,by omega⟩

private theorem k300COMColumn2_label (a : Fin 1) :
    k302COMLabel9 (k300COMColumn2 a) = ⟨(⟨0,by decide⟩ : Fin 9),
      ⟨a.val,by simpa [natCOMRelativeDimension] using a.isLt⟩⟩ := by
  fin_cases a <;> rfl

def k300COMColumn3 (a : Fin 1) : Fin 3 := ⟨0+a.val,by omega⟩

private theorem k300COMColumn3_label (a : Fin 1) :
    k303COMLabel9 (k300COMColumn3 a) = ⟨(⟨0,by decide⟩ : Fin 9),
      ⟨a.val,by simpa [natCOMRelativeDimension] using a.isLt⟩⟩ := by
  fin_cases a <;> rfl

def k300COMColumn4 (a : Fin 1) : Fin 4 := ⟨0+a.val,by omega⟩

private theorem k300COMColumn4_label (a : Fin 1) :
    k304COMLabel9 (k300COMColumn4 a) = ⟨(⟨0,by decide⟩ : Fin 9),
      ⟨a.val,by simpa [natCOMRelativeDimension] using a.isLt⟩⟩ := by
  fin_cases a <;> rfl

def k300COMColumn5 (a : Fin 1) : Fin 5 := ⟨0+a.val,by omega⟩

private theorem k300COMColumn5_label (a : Fin 1) :
    k305COMLabel9 (k300COMColumn5 a) = ⟨(⟨0,by decide⟩ : Fin 9),
      ⟨a.val,by simpa [natCOMRelativeDimension] using a.isLt⟩⟩ := by
  fin_cases a <;> rfl

def k300COMColumn6 (a : Fin 1) : Fin 7 := ⟨0+a.val,by omega⟩

private theorem k300COMColumn6_label (a : Fin 1) :
    k306COMLabel9 (k300COMColumn6 a) = ⟨(⟨0,by decide⟩ : Fin 9),
      ⟨a.val,by simpa [natCOMRelativeDimension] using a.isLt⟩⟩ := by
  fin_cases a <;> rfl

def k300COMColumn7 (a : Fin 1) : Fin 8 := ⟨0+a.val,by omega⟩

private theorem k300COMColumn7_label (a : Fin 1) :
    k307COMLabel9 (k300COMColumn7 a) = ⟨(⟨0,by decide⟩ : Fin 9),
      ⟨a.val,by simpa [natCOMRelativeDimension] using a.isLt⟩⟩ := by
  fin_cases a <;> rfl

def k300COMColumn8 (a : Fin 1) : Fin 10 := ⟨0+a.val,by omega⟩

private theorem k300COMColumn8_label (a : Fin 1) :
    k308COMLabel9 (k300COMColumn8 a) = ⟨(⟨0,by decide⟩ : Fin 9),
      ⟨a.val,by simpa [natCOMRelativeDimension] using a.isLt⟩⟩ := by
  fin_cases a <;> rfl

/-- Actual same-label C blocks with the original μ2 factor (2/3)·3^n n!. -/
def k300COMAveragedRankCoefficient : Matrix (Fin 1) (Fin 1) ℂ :=
  (((2/3 : ℚ) * (3 : ℚ)^0 * (Nat.factorial 0 : ℚ)) : ℂ) • (k300COMRankCoefficient.submatrix k300COMColumn0 k300COMColumn0) +
    (((2/3 : ℚ) * (3 : ℚ)^1 * (Nat.factorial 1 : ℚ)) : ℂ) • (k301COMRankCoefficient.submatrix k300COMColumn1 k300COMColumn1) +
    (((2/3 : ℚ) * (3 : ℚ)^2 * (Nat.factorial 2 : ℚ)) : ℂ) • (k302COMRankCoefficient.submatrix k300COMColumn2 k300COMColumn2) +
    (((2/3 : ℚ) * (3 : ℚ)^3 * (Nat.factorial 3 : ℚ)) : ℂ) • (k303COMRankCoefficient.submatrix k300COMColumn3 k300COMColumn3) +
    (((2/3 : ℚ) * (3 : ℚ)^4 * (Nat.factorial 4 : ℚ)) : ℂ) • (k304COMRankCoefficient.submatrix k300COMColumn4 k300COMColumn4) +
    (((2/3 : ℚ) * (3 : ℚ)^5 * (Nat.factorial 5 : ℚ)) : ℂ) • (k305COMRankCoefficient.submatrix k300COMColumn5 k300COMColumn5) +
    (((2/3 : ℚ) * (3 : ℚ)^6 * (Nat.factorial 6 : ℚ)) : ℂ) • (k306COMRankCoefficient.submatrix k300COMColumn6 k300COMColumn6) +
    (((2/3 : ℚ) * (3 : ℚ)^7 * (Nat.factorial 7 : ℚ)) : ℂ) • (k307COMRankCoefficient.submatrix k300COMColumn7 k300COMColumn7) +
    (((2/3 : ℚ) * (3 : ℚ)^8 * (Nat.factorial 8 : ℚ)) : ℂ) • (k308COMRankCoefficient.submatrix k300COMColumn8 k300COMColumn8)

private def k300COMAveragedRankRat : Matrix (Fin 1) (Fin 1) ℚ :=
  ((2/3 : ℚ) * (3 : ℚ)^0 * (Nat.factorial 0 : ℚ)) • (k300COMRankRatValue.submatrix k300COMColumn0 k300COMColumn0) +
    ((2/3 : ℚ) * (3 : ℚ)^1 * (Nat.factorial 1 : ℚ)) • (k301COMRankRatValue.submatrix k300COMColumn1 k300COMColumn1) +
    ((2/3 : ℚ) * (3 : ℚ)^2 * (Nat.factorial 2 : ℚ)) • (k302COMRankRatValue.submatrix k300COMColumn2 k300COMColumn2) +
    ((2/3 : ℚ) * (3 : ℚ)^3 * (Nat.factorial 3 : ℚ)) • (k303COMRankRatValue.submatrix k300COMColumn3 k300COMColumn3) +
    ((2/3 : ℚ) * (3 : ℚ)^4 * (Nat.factorial 4 : ℚ)) • (k304COMRankRatValue.submatrix k300COMColumn4 k300COMColumn4) +
    ((2/3 : ℚ) * (3 : ℚ)^5 * (Nat.factorial 5 : ℚ)) • (k305COMRankRatValue.submatrix k300COMColumn5 k300COMColumn5) +
    ((2/3 : ℚ) * (3 : ℚ)^6 * (Nat.factorial 6 : ℚ)) • (k306COMRankRatValue.submatrix k300COMColumn6 k300COMColumn6) +
    ((2/3 : ℚ) * (3 : ℚ)^7 * (Nat.factorial 7 : ℚ)) • (k307COMRankRatValue.submatrix k300COMColumn7 k300COMColumn7) +
    ((2/3 : ℚ) * (3 : ℚ)^8 * (Nat.factorial 8 : ℚ)) • (k308COMRankRatValue.submatrix k300COMColumn8 k300COMColumn8)

private theorem k300_COM_average_rank_rat :
    k300COMAveragedRankRat = k300J * b300average * k300J := by
  decide +kernel

/-- The genuine finite weighted rank average is J·averageRaw·J, with both Gram inverses. -/
theorem k300_COM_averaged_rank_coefficient :
    k300COMAveragedRankCoefficient = complexify (k300J * c300averageRaw * k300J) := by
  have h : k300COMAveragedRankCoefficient = complexify k300COMAveragedRankRat := by
    simp only [k300COMAveragedRankCoefficient,k300COMAveragedRankRat,
      k300_COM_rank_coefficient_value,
      k301_COM_rank_coefficient_value,
      k302_COM_rank_coefficient_value,
      k303_COM_rank_coefficient_value,
      k304_COM_rank_coefficient_value,
      k305_COM_rank_coefficient_value,
      k306_COM_rank_coefficient_value,
      k307_COM_rank_coefficient_value,
      k308_COM_rank_coefficient_value,
      complexify_add_rect,complexify_smul_rat,natCOM_complexify_submatrix,
      Rat.cast_mul,Rat.cast_pow,Rat.cast_natCast,Rat.cast_div,Rat.cast_ofNat]
  rw [h,k300_COM_average_rank_rat,c300_COM_reconstructed]

#print axioms k300_COM_averaged_rank_coefficient

/-- Exact entrywise endpoint for finite physical reindexing, with both relative duals. -/
theorem k300_COM_averaged_rank_entry (a b : Fin 1) :
    ((2/3 : ℂ) * (3 : ℂ)^0 * (Nat.factorial 0 : ℂ)) *
      k300COMRankCoefficient (k300COMColumn0 a) (k300COMColumn0 b) +
    ((2/3 : ℂ) * (3 : ℂ)^1 * (Nat.factorial 1 : ℂ)) *
      k301COMRankCoefficient (k300COMColumn1 a) (k300COMColumn1 b) +
    ((2/3 : ℂ) * (3 : ℂ)^2 * (Nat.factorial 2 : ℂ)) *
      k302COMRankCoefficient (k300COMColumn2 a) (k300COMColumn2 b) +
    ((2/3 : ℂ) * (3 : ℂ)^3 * (Nat.factorial 3 : ℂ)) *
      k303COMRankCoefficient (k300COMColumn3 a) (k300COMColumn3 b) +
    ((2/3 : ℂ) * (3 : ℂ)^4 * (Nat.factorial 4 : ℂ)) *
      k304COMRankCoefficient (k300COMColumn4 a) (k300COMColumn4 b) +
    ((2/3 : ℂ) * (3 : ℂ)^5 * (Nat.factorial 5 : ℂ)) *
      k305COMRankCoefficient (k300COMColumn5 a) (k300COMColumn5 b) +
    ((2/3 : ℂ) * (3 : ℂ)^6 * (Nat.factorial 6 : ℂ)) *
      k306COMRankCoefficient (k300COMColumn6 a) (k300COMColumn6 b) +
    ((2/3 : ℂ) * (3 : ℂ)^7 * (Nat.factorial 7 : ℂ)) *
      k307COMRankCoefficient (k300COMColumn7 a) (k300COMColumn7 b) +
    ((2/3 : ℂ) * (3 : ℂ)^8 * (Nat.factorial 8 : ℂ)) *
      k308COMRankCoefficient (k300COMColumn8 a) (k300COMColumn8 b) =
      (complexify k300J * complexify b300average * complexify k300J) a b := by
  have h := congrFun (congrFun k300_COM_averaged_rank_coefficient a) b
  rw [c300_COM_reconstructed] at h
  simpa only [k300COMAveragedRankCoefficient,complexify_mul_rect,
    Matrix.add_apply,Matrix.smul_apply,Matrix.submatrix_apply,smul_eq_mul,
    Rat.cast_mul,Rat.cast_div,Rat.cast_pow,Rat.cast_natCast,Rat.cast_ofNat] using h

#print axioms k300_COM_averaged_rank_entry

def k301COMColumn1 (a : Fin 0) : Fin 1 := ⟨1+a.val,by omega⟩

private theorem k301COMColumn1_label (a : Fin 0) :
    k301COMLabel9 (k301COMColumn1 a) = ⟨(⟨1,by decide⟩ : Fin 9),
      ⟨a.val,by simpa [natCOMRelativeDimension] using a.isLt⟩⟩ := by
  fin_cases a <;> rfl

def k301COMColumn2 (a : Fin 0) : Fin 2 := ⟨1+a.val,by omega⟩

private theorem k301COMColumn2_label (a : Fin 0) :
    k302COMLabel9 (k301COMColumn2 a) = ⟨(⟨1,by decide⟩ : Fin 9),
      ⟨a.val,by simpa [natCOMRelativeDimension] using a.isLt⟩⟩ := by
  fin_cases a <;> rfl

def k301COMColumn3 (a : Fin 0) : Fin 3 := ⟨1+a.val,by omega⟩

private theorem k301COMColumn3_label (a : Fin 0) :
    k303COMLabel9 (k301COMColumn3 a) = ⟨(⟨1,by decide⟩ : Fin 9),
      ⟨a.val,by simpa [natCOMRelativeDimension] using a.isLt⟩⟩ := by
  fin_cases a <;> rfl

def k301COMColumn4 (a : Fin 0) : Fin 4 := ⟨1+a.val,by omega⟩

private theorem k301COMColumn4_label (a : Fin 0) :
    k304COMLabel9 (k301COMColumn4 a) = ⟨(⟨1,by decide⟩ : Fin 9),
      ⟨a.val,by simpa [natCOMRelativeDimension] using a.isLt⟩⟩ := by
  fin_cases a <;> rfl

def k301COMColumn5 (a : Fin 0) : Fin 5 := ⟨1+a.val,by omega⟩

private theorem k301COMColumn5_label (a : Fin 0) :
    k305COMLabel9 (k301COMColumn5 a) = ⟨(⟨1,by decide⟩ : Fin 9),
      ⟨a.val,by simpa [natCOMRelativeDimension] using a.isLt⟩⟩ := by
  fin_cases a <;> rfl

def k301COMColumn6 (a : Fin 0) : Fin 7 := ⟨1+a.val,by omega⟩

private theorem k301COMColumn6_label (a : Fin 0) :
    k306COMLabel9 (k301COMColumn6 a) = ⟨(⟨1,by decide⟩ : Fin 9),
      ⟨a.val,by simpa [natCOMRelativeDimension] using a.isLt⟩⟩ := by
  fin_cases a <;> rfl

def k301COMColumn7 (a : Fin 0) : Fin 8 := ⟨1+a.val,by omega⟩

private theorem k301COMColumn7_label (a : Fin 0) :
    k307COMLabel9 (k301COMColumn7 a) = ⟨(⟨1,by decide⟩ : Fin 9),
      ⟨a.val,by simpa [natCOMRelativeDimension] using a.isLt⟩⟩ := by
  fin_cases a <;> rfl

def k301COMColumn8 (a : Fin 0) : Fin 10 := ⟨1+a.val,by omega⟩

private theorem k301COMColumn8_label (a : Fin 0) :
    k308COMLabel9 (k301COMColumn8 a) = ⟨(⟨1,by decide⟩ : Fin 9),
      ⟨a.val,by simpa [natCOMRelativeDimension] using a.isLt⟩⟩ := by
  fin_cases a <;> rfl

/-- Actual same-label C blocks with the original μ2 factor (2/3)·3^n n!. -/
def k301COMAveragedRankCoefficient : Matrix (Fin 0) (Fin 0) ℂ :=
  (((2/3 : ℚ) * (3 : ℚ)^0 * (Nat.factorial 0 : ℚ)) : ℂ) • (k301COMRankCoefficient.submatrix k301COMColumn1 k301COMColumn1) +
    (((2/3 : ℚ) * (3 : ℚ)^1 * (Nat.factorial 1 : ℚ)) : ℂ) • (k302COMRankCoefficient.submatrix k301COMColumn2 k301COMColumn2) +
    (((2/3 : ℚ) * (3 : ℚ)^2 * (Nat.factorial 2 : ℚ)) : ℂ) • (k303COMRankCoefficient.submatrix k301COMColumn3 k301COMColumn3) +
    (((2/3 : ℚ) * (3 : ℚ)^3 * (Nat.factorial 3 : ℚ)) : ℂ) • (k304COMRankCoefficient.submatrix k301COMColumn4 k301COMColumn4) +
    (((2/3 : ℚ) * (3 : ℚ)^4 * (Nat.factorial 4 : ℚ)) : ℂ) • (k305COMRankCoefficient.submatrix k301COMColumn5 k301COMColumn5) +
    (((2/3 : ℚ) * (3 : ℚ)^5 * (Nat.factorial 5 : ℚ)) : ℂ) • (k306COMRankCoefficient.submatrix k301COMColumn6 k301COMColumn6) +
    (((2/3 : ℚ) * (3 : ℚ)^6 * (Nat.factorial 6 : ℚ)) : ℂ) • (k307COMRankCoefficient.submatrix k301COMColumn7 k301COMColumn7) +
    (((2/3 : ℚ) * (3 : ℚ)^7 * (Nat.factorial 7 : ℚ)) : ℂ) • (k308COMRankCoefficient.submatrix k301COMColumn8 k301COMColumn8)

private def k301COMAveragedRankRat : Matrix (Fin 0) (Fin 0) ℚ :=
  ((2/3 : ℚ) * (3 : ℚ)^0 * (Nat.factorial 0 : ℚ)) • (k301COMRankRatValue.submatrix k301COMColumn1 k301COMColumn1) +
    ((2/3 : ℚ) * (3 : ℚ)^1 * (Nat.factorial 1 : ℚ)) • (k302COMRankRatValue.submatrix k301COMColumn2 k301COMColumn2) +
    ((2/3 : ℚ) * (3 : ℚ)^2 * (Nat.factorial 2 : ℚ)) • (k303COMRankRatValue.submatrix k301COMColumn3 k301COMColumn3) +
    ((2/3 : ℚ) * (3 : ℚ)^3 * (Nat.factorial 3 : ℚ)) • (k304COMRankRatValue.submatrix k301COMColumn4 k301COMColumn4) +
    ((2/3 : ℚ) * (3 : ℚ)^4 * (Nat.factorial 4 : ℚ)) • (k305COMRankRatValue.submatrix k301COMColumn5 k301COMColumn5) +
    ((2/3 : ℚ) * (3 : ℚ)^5 * (Nat.factorial 5 : ℚ)) • (k306COMRankRatValue.submatrix k301COMColumn6 k301COMColumn6) +
    ((2/3 : ℚ) * (3 : ℚ)^6 * (Nat.factorial 6 : ℚ)) • (k307COMRankRatValue.submatrix k301COMColumn7 k301COMColumn7) +
    ((2/3 : ℚ) * (3 : ℚ)^7 * (Nat.factorial 7 : ℚ)) • (k308COMRankRatValue.submatrix k301COMColumn8 k301COMColumn8)

private theorem k301_COM_average_rank_rat :
    k301COMAveragedRankRat = k301J * b301average * k301J := by
  decide +kernel

/-- The genuine finite weighted rank average is J·averageRaw·J, with both Gram inverses. -/
theorem k301_COM_averaged_rank_coefficient :
    k301COMAveragedRankCoefficient = complexify (k301J * c301averageRaw * k301J) := by
  have h : k301COMAveragedRankCoefficient = complexify k301COMAveragedRankRat := by
    simp only [k301COMAveragedRankCoefficient,k301COMAveragedRankRat,
      k301_COM_rank_coefficient_value,
      k302_COM_rank_coefficient_value,
      k303_COM_rank_coefficient_value,
      k304_COM_rank_coefficient_value,
      k305_COM_rank_coefficient_value,
      k306_COM_rank_coefficient_value,
      k307_COM_rank_coefficient_value,
      k308_COM_rank_coefficient_value,
      complexify_add_rect,complexify_smul_rat,natCOM_complexify_submatrix,
      Rat.cast_mul,Rat.cast_pow,Rat.cast_natCast,Rat.cast_div,Rat.cast_ofNat]
  rw [h,k301_COM_average_rank_rat,c301_COM_reconstructed]

#print axioms k301_COM_averaged_rank_coefficient

/-- Exact entrywise endpoint for finite physical reindexing, with both relative duals. -/
theorem k301_COM_averaged_rank_entry (a b : Fin 0) :
    ((2/3 : ℂ) * (3 : ℂ)^0 * (Nat.factorial 0 : ℂ)) *
      k301COMRankCoefficient (k301COMColumn1 a) (k301COMColumn1 b) +
    ((2/3 : ℂ) * (3 : ℂ)^1 * (Nat.factorial 1 : ℂ)) *
      k302COMRankCoefficient (k301COMColumn2 a) (k301COMColumn2 b) +
    ((2/3 : ℂ) * (3 : ℂ)^2 * (Nat.factorial 2 : ℂ)) *
      k303COMRankCoefficient (k301COMColumn3 a) (k301COMColumn3 b) +
    ((2/3 : ℂ) * (3 : ℂ)^3 * (Nat.factorial 3 : ℂ)) *
      k304COMRankCoefficient (k301COMColumn4 a) (k301COMColumn4 b) +
    ((2/3 : ℂ) * (3 : ℂ)^4 * (Nat.factorial 4 : ℂ)) *
      k305COMRankCoefficient (k301COMColumn5 a) (k301COMColumn5 b) +
    ((2/3 : ℂ) * (3 : ℂ)^5 * (Nat.factorial 5 : ℂ)) *
      k306COMRankCoefficient (k301COMColumn6 a) (k301COMColumn6 b) +
    ((2/3 : ℂ) * (3 : ℂ)^6 * (Nat.factorial 6 : ℂ)) *
      k307COMRankCoefficient (k301COMColumn7 a) (k301COMColumn7 b) +
    ((2/3 : ℂ) * (3 : ℂ)^7 * (Nat.factorial 7 : ℂ)) *
      k308COMRankCoefficient (k301COMColumn8 a) (k301COMColumn8 b) =
      (complexify k301J * complexify b301average * complexify k301J) a b := by
  have h := congrFun (congrFun k301_COM_averaged_rank_coefficient a) b
  rw [c301_COM_reconstructed] at h
  simpa only [k301COMAveragedRankCoefficient,complexify_mul_rect,
    Matrix.add_apply,Matrix.smul_apply,Matrix.submatrix_apply,smul_eq_mul,
    Rat.cast_mul,Rat.cast_div,Rat.cast_pow,Rat.cast_natCast,Rat.cast_ofNat] using h

#print axioms k301_COM_averaged_rank_entry

def k302COMColumn2 (a : Fin 1) : Fin 2 := ⟨1+a.val,by omega⟩

private theorem k302COMColumn2_label (a : Fin 1) :
    k302COMLabel9 (k302COMColumn2 a) = ⟨(⟨2,by decide⟩ : Fin 9),
      ⟨a.val,by simpa [natCOMRelativeDimension] using a.isLt⟩⟩ := by
  fin_cases a <;> rfl

def k302COMColumn3 (a : Fin 1) : Fin 3 := ⟨1+a.val,by omega⟩

private theorem k302COMColumn3_label (a : Fin 1) :
    k303COMLabel9 (k302COMColumn3 a) = ⟨(⟨2,by decide⟩ : Fin 9),
      ⟨a.val,by simpa [natCOMRelativeDimension] using a.isLt⟩⟩ := by
  fin_cases a <;> rfl

def k302COMColumn4 (a : Fin 1) : Fin 4 := ⟨1+a.val,by omega⟩

private theorem k302COMColumn4_label (a : Fin 1) :
    k304COMLabel9 (k302COMColumn4 a) = ⟨(⟨2,by decide⟩ : Fin 9),
      ⟨a.val,by simpa [natCOMRelativeDimension] using a.isLt⟩⟩ := by
  fin_cases a <;> rfl

def k302COMColumn5 (a : Fin 1) : Fin 5 := ⟨1+a.val,by omega⟩

private theorem k302COMColumn5_label (a : Fin 1) :
    k305COMLabel9 (k302COMColumn5 a) = ⟨(⟨2,by decide⟩ : Fin 9),
      ⟨a.val,by simpa [natCOMRelativeDimension] using a.isLt⟩⟩ := by
  fin_cases a <;> rfl

def k302COMColumn6 (a : Fin 1) : Fin 7 := ⟨1+a.val,by omega⟩

private theorem k302COMColumn6_label (a : Fin 1) :
    k306COMLabel9 (k302COMColumn6 a) = ⟨(⟨2,by decide⟩ : Fin 9),
      ⟨a.val,by simpa [natCOMRelativeDimension] using a.isLt⟩⟩ := by
  fin_cases a <;> rfl

def k302COMColumn7 (a : Fin 1) : Fin 8 := ⟨1+a.val,by omega⟩

private theorem k302COMColumn7_label (a : Fin 1) :
    k307COMLabel9 (k302COMColumn7 a) = ⟨(⟨2,by decide⟩ : Fin 9),
      ⟨a.val,by simpa [natCOMRelativeDimension] using a.isLt⟩⟩ := by
  fin_cases a <;> rfl

def k302COMColumn8 (a : Fin 1) : Fin 10 := ⟨1+a.val,by omega⟩

private theorem k302COMColumn8_label (a : Fin 1) :
    k308COMLabel9 (k302COMColumn8 a) = ⟨(⟨2,by decide⟩ : Fin 9),
      ⟨a.val,by simpa [natCOMRelativeDimension] using a.isLt⟩⟩ := by
  fin_cases a <;> rfl

/-- Actual same-label C blocks with the original μ2 factor (2/3)·3^n n!. -/
def k302COMAveragedRankCoefficient : Matrix (Fin 1) (Fin 1) ℂ :=
  (((2/3 : ℚ) * (3 : ℚ)^0 * (Nat.factorial 0 : ℚ)) : ℂ) • (k302COMRankCoefficient.submatrix k302COMColumn2 k302COMColumn2) +
    (((2/3 : ℚ) * (3 : ℚ)^1 * (Nat.factorial 1 : ℚ)) : ℂ) • (k303COMRankCoefficient.submatrix k302COMColumn3 k302COMColumn3) +
    (((2/3 : ℚ) * (3 : ℚ)^2 * (Nat.factorial 2 : ℚ)) : ℂ) • (k304COMRankCoefficient.submatrix k302COMColumn4 k302COMColumn4) +
    (((2/3 : ℚ) * (3 : ℚ)^3 * (Nat.factorial 3 : ℚ)) : ℂ) • (k305COMRankCoefficient.submatrix k302COMColumn5 k302COMColumn5) +
    (((2/3 : ℚ) * (3 : ℚ)^4 * (Nat.factorial 4 : ℚ)) : ℂ) • (k306COMRankCoefficient.submatrix k302COMColumn6 k302COMColumn6) +
    (((2/3 : ℚ) * (3 : ℚ)^5 * (Nat.factorial 5 : ℚ)) : ℂ) • (k307COMRankCoefficient.submatrix k302COMColumn7 k302COMColumn7) +
    (((2/3 : ℚ) * (3 : ℚ)^6 * (Nat.factorial 6 : ℚ)) : ℂ) • (k308COMRankCoefficient.submatrix k302COMColumn8 k302COMColumn8)

private def k302COMAveragedRankRat : Matrix (Fin 1) (Fin 1) ℚ :=
  ((2/3 : ℚ) * (3 : ℚ)^0 * (Nat.factorial 0 : ℚ)) • (k302COMRankRatValue.submatrix k302COMColumn2 k302COMColumn2) +
    ((2/3 : ℚ) * (3 : ℚ)^1 * (Nat.factorial 1 : ℚ)) • (k303COMRankRatValue.submatrix k302COMColumn3 k302COMColumn3) +
    ((2/3 : ℚ) * (3 : ℚ)^2 * (Nat.factorial 2 : ℚ)) • (k304COMRankRatValue.submatrix k302COMColumn4 k302COMColumn4) +
    ((2/3 : ℚ) * (3 : ℚ)^3 * (Nat.factorial 3 : ℚ)) • (k305COMRankRatValue.submatrix k302COMColumn5 k302COMColumn5) +
    ((2/3 : ℚ) * (3 : ℚ)^4 * (Nat.factorial 4 : ℚ)) • (k306COMRankRatValue.submatrix k302COMColumn6 k302COMColumn6) +
    ((2/3 : ℚ) * (3 : ℚ)^5 * (Nat.factorial 5 : ℚ)) • (k307COMRankRatValue.submatrix k302COMColumn7 k302COMColumn7) +
    ((2/3 : ℚ) * (3 : ℚ)^6 * (Nat.factorial 6 : ℚ)) • (k308COMRankRatValue.submatrix k302COMColumn8 k302COMColumn8)

private theorem k302_COM_average_rank_rat :
    k302COMAveragedRankRat = k302J * b302average * k302J := by
  decide +kernel

/-- The genuine finite weighted rank average is J·averageRaw·J, with both Gram inverses. -/
theorem k302_COM_averaged_rank_coefficient :
    k302COMAveragedRankCoefficient = complexify (k302J * c302averageRaw * k302J) := by
  have h : k302COMAveragedRankCoefficient = complexify k302COMAveragedRankRat := by
    simp only [k302COMAveragedRankCoefficient,k302COMAveragedRankRat,
      k302_COM_rank_coefficient_value,
      k303_COM_rank_coefficient_value,
      k304_COM_rank_coefficient_value,
      k305_COM_rank_coefficient_value,
      k306_COM_rank_coefficient_value,
      k307_COM_rank_coefficient_value,
      k308_COM_rank_coefficient_value,
      complexify_add_rect,complexify_smul_rat,natCOM_complexify_submatrix,
      Rat.cast_mul,Rat.cast_pow,Rat.cast_natCast,Rat.cast_div,Rat.cast_ofNat]
  rw [h,k302_COM_average_rank_rat,c302_COM_reconstructed]

#print axioms k302_COM_averaged_rank_coefficient

/-- Exact entrywise endpoint for finite physical reindexing, with both relative duals. -/
theorem k302_COM_averaged_rank_entry (a b : Fin 1) :
    ((2/3 : ℂ) * (3 : ℂ)^0 * (Nat.factorial 0 : ℂ)) *
      k302COMRankCoefficient (k302COMColumn2 a) (k302COMColumn2 b) +
    ((2/3 : ℂ) * (3 : ℂ)^1 * (Nat.factorial 1 : ℂ)) *
      k303COMRankCoefficient (k302COMColumn3 a) (k302COMColumn3 b) +
    ((2/3 : ℂ) * (3 : ℂ)^2 * (Nat.factorial 2 : ℂ)) *
      k304COMRankCoefficient (k302COMColumn4 a) (k302COMColumn4 b) +
    ((2/3 : ℂ) * (3 : ℂ)^3 * (Nat.factorial 3 : ℂ)) *
      k305COMRankCoefficient (k302COMColumn5 a) (k302COMColumn5 b) +
    ((2/3 : ℂ) * (3 : ℂ)^4 * (Nat.factorial 4 : ℂ)) *
      k306COMRankCoefficient (k302COMColumn6 a) (k302COMColumn6 b) +
    ((2/3 : ℂ) * (3 : ℂ)^5 * (Nat.factorial 5 : ℂ)) *
      k307COMRankCoefficient (k302COMColumn7 a) (k302COMColumn7 b) +
    ((2/3 : ℂ) * (3 : ℂ)^6 * (Nat.factorial 6 : ℂ)) *
      k308COMRankCoefficient (k302COMColumn8 a) (k302COMColumn8 b) =
      (complexify k302J * complexify b302average * complexify k302J) a b := by
  have h := congrFun (congrFun k302_COM_averaged_rank_coefficient a) b
  rw [c302_COM_reconstructed] at h
  simpa only [k302COMAveragedRankCoefficient,complexify_mul_rect,
    Matrix.add_apply,Matrix.smul_apply,Matrix.submatrix_apply,smul_eq_mul,
    Rat.cast_mul,Rat.cast_div,Rat.cast_pow,Rat.cast_natCast,Rat.cast_ofNat] using h

#print axioms k302_COM_averaged_rank_entry

def k303COMColumn3 (a : Fin 1) : Fin 3 := ⟨2+a.val,by omega⟩

private theorem k303COMColumn3_label (a : Fin 1) :
    k303COMLabel9 (k303COMColumn3 a) = ⟨(⟨3,by decide⟩ : Fin 9),
      ⟨a.val,by simpa [natCOMRelativeDimension] using a.isLt⟩⟩ := by
  fin_cases a <;> rfl

def k303COMColumn4 (a : Fin 1) : Fin 4 := ⟨2+a.val,by omega⟩

private theorem k303COMColumn4_label (a : Fin 1) :
    k304COMLabel9 (k303COMColumn4 a) = ⟨(⟨3,by decide⟩ : Fin 9),
      ⟨a.val,by simpa [natCOMRelativeDimension] using a.isLt⟩⟩ := by
  fin_cases a <;> rfl

def k303COMColumn5 (a : Fin 1) : Fin 5 := ⟨2+a.val,by omega⟩

private theorem k303COMColumn5_label (a : Fin 1) :
    k305COMLabel9 (k303COMColumn5 a) = ⟨(⟨3,by decide⟩ : Fin 9),
      ⟨a.val,by simpa [natCOMRelativeDimension] using a.isLt⟩⟩ := by
  fin_cases a <;> rfl

def k303COMColumn6 (a : Fin 1) : Fin 7 := ⟨2+a.val,by omega⟩

private theorem k303COMColumn6_label (a : Fin 1) :
    k306COMLabel9 (k303COMColumn6 a) = ⟨(⟨3,by decide⟩ : Fin 9),
      ⟨a.val,by simpa [natCOMRelativeDimension] using a.isLt⟩⟩ := by
  fin_cases a <;> rfl

def k303COMColumn7 (a : Fin 1) : Fin 8 := ⟨2+a.val,by omega⟩

private theorem k303COMColumn7_label (a : Fin 1) :
    k307COMLabel9 (k303COMColumn7 a) = ⟨(⟨3,by decide⟩ : Fin 9),
      ⟨a.val,by simpa [natCOMRelativeDimension] using a.isLt⟩⟩ := by
  fin_cases a <;> rfl

def k303COMColumn8 (a : Fin 1) : Fin 10 := ⟨2+a.val,by omega⟩

private theorem k303COMColumn8_label (a : Fin 1) :
    k308COMLabel9 (k303COMColumn8 a) = ⟨(⟨3,by decide⟩ : Fin 9),
      ⟨a.val,by simpa [natCOMRelativeDimension] using a.isLt⟩⟩ := by
  fin_cases a <;> rfl

/-- Actual same-label C blocks with the original μ2 factor (2/3)·3^n n!. -/
def k303COMAveragedRankCoefficient : Matrix (Fin 1) (Fin 1) ℂ :=
  (((2/3 : ℚ) * (3 : ℚ)^0 * (Nat.factorial 0 : ℚ)) : ℂ) • (k303COMRankCoefficient.submatrix k303COMColumn3 k303COMColumn3) +
    (((2/3 : ℚ) * (3 : ℚ)^1 * (Nat.factorial 1 : ℚ)) : ℂ) • (k304COMRankCoefficient.submatrix k303COMColumn4 k303COMColumn4) +
    (((2/3 : ℚ) * (3 : ℚ)^2 * (Nat.factorial 2 : ℚ)) : ℂ) • (k305COMRankCoefficient.submatrix k303COMColumn5 k303COMColumn5) +
    (((2/3 : ℚ) * (3 : ℚ)^3 * (Nat.factorial 3 : ℚ)) : ℂ) • (k306COMRankCoefficient.submatrix k303COMColumn6 k303COMColumn6) +
    (((2/3 : ℚ) * (3 : ℚ)^4 * (Nat.factorial 4 : ℚ)) : ℂ) • (k307COMRankCoefficient.submatrix k303COMColumn7 k303COMColumn7) +
    (((2/3 : ℚ) * (3 : ℚ)^5 * (Nat.factorial 5 : ℚ)) : ℂ) • (k308COMRankCoefficient.submatrix k303COMColumn8 k303COMColumn8)

private def k303COMAveragedRankRat : Matrix (Fin 1) (Fin 1) ℚ :=
  ((2/3 : ℚ) * (3 : ℚ)^0 * (Nat.factorial 0 : ℚ)) • (k303COMRankRatValue.submatrix k303COMColumn3 k303COMColumn3) +
    ((2/3 : ℚ) * (3 : ℚ)^1 * (Nat.factorial 1 : ℚ)) • (k304COMRankRatValue.submatrix k303COMColumn4 k303COMColumn4) +
    ((2/3 : ℚ) * (3 : ℚ)^2 * (Nat.factorial 2 : ℚ)) • (k305COMRankRatValue.submatrix k303COMColumn5 k303COMColumn5) +
    ((2/3 : ℚ) * (3 : ℚ)^3 * (Nat.factorial 3 : ℚ)) • (k306COMRankRatValue.submatrix k303COMColumn6 k303COMColumn6) +
    ((2/3 : ℚ) * (3 : ℚ)^4 * (Nat.factorial 4 : ℚ)) • (k307COMRankRatValue.submatrix k303COMColumn7 k303COMColumn7) +
    ((2/3 : ℚ) * (3 : ℚ)^5 * (Nat.factorial 5 : ℚ)) • (k308COMRankRatValue.submatrix k303COMColumn8 k303COMColumn8)

private theorem k303_COM_average_rank_rat :
    k303COMAveragedRankRat = k303J * b303average * k303J := by
  decide +kernel

/-- The genuine finite weighted rank average is J·averageRaw·J, with both Gram inverses. -/
theorem k303_COM_averaged_rank_coefficient :
    k303COMAveragedRankCoefficient = complexify (k303J * c303averageRaw * k303J) := by
  have h : k303COMAveragedRankCoefficient = complexify k303COMAveragedRankRat := by
    simp only [k303COMAveragedRankCoefficient,k303COMAveragedRankRat,
      k303_COM_rank_coefficient_value,
      k304_COM_rank_coefficient_value,
      k305_COM_rank_coefficient_value,
      k306_COM_rank_coefficient_value,
      k307_COM_rank_coefficient_value,
      k308_COM_rank_coefficient_value,
      complexify_add_rect,complexify_smul_rat,natCOM_complexify_submatrix,
      Rat.cast_mul,Rat.cast_pow,Rat.cast_natCast,Rat.cast_div,Rat.cast_ofNat]
  rw [h,k303_COM_average_rank_rat,c303_COM_reconstructed]

#print axioms k303_COM_averaged_rank_coefficient

/-- Exact entrywise endpoint for finite physical reindexing, with both relative duals. -/
theorem k303_COM_averaged_rank_entry (a b : Fin 1) :
    ((2/3 : ℂ) * (3 : ℂ)^0 * (Nat.factorial 0 : ℂ)) *
      k303COMRankCoefficient (k303COMColumn3 a) (k303COMColumn3 b) +
    ((2/3 : ℂ) * (3 : ℂ)^1 * (Nat.factorial 1 : ℂ)) *
      k304COMRankCoefficient (k303COMColumn4 a) (k303COMColumn4 b) +
    ((2/3 : ℂ) * (3 : ℂ)^2 * (Nat.factorial 2 : ℂ)) *
      k305COMRankCoefficient (k303COMColumn5 a) (k303COMColumn5 b) +
    ((2/3 : ℂ) * (3 : ℂ)^3 * (Nat.factorial 3 : ℂ)) *
      k306COMRankCoefficient (k303COMColumn6 a) (k303COMColumn6 b) +
    ((2/3 : ℂ) * (3 : ℂ)^4 * (Nat.factorial 4 : ℂ)) *
      k307COMRankCoefficient (k303COMColumn7 a) (k303COMColumn7 b) +
    ((2/3 : ℂ) * (3 : ℂ)^5 * (Nat.factorial 5 : ℂ)) *
      k308COMRankCoefficient (k303COMColumn8 a) (k303COMColumn8 b) =
      (complexify k303J * complexify b303average * complexify k303J) a b := by
  have h := congrFun (congrFun k303_COM_averaged_rank_coefficient a) b
  rw [c303_COM_reconstructed] at h
  simpa only [k303COMAveragedRankCoefficient,complexify_mul_rect,
    Matrix.add_apply,Matrix.smul_apply,Matrix.submatrix_apply,smul_eq_mul,
    Rat.cast_mul,Rat.cast_div,Rat.cast_pow,Rat.cast_natCast,Rat.cast_ofNat] using h

#print axioms k303_COM_averaged_rank_entry

def k304COMColumn4 (a : Fin 1) : Fin 4 := ⟨3+a.val,by omega⟩

private theorem k304COMColumn4_label (a : Fin 1) :
    k304COMLabel9 (k304COMColumn4 a) = ⟨(⟨4,by decide⟩ : Fin 9),
      ⟨a.val,by simpa [natCOMRelativeDimension] using a.isLt⟩⟩ := by
  fin_cases a <;> rfl

def k304COMColumn5 (a : Fin 1) : Fin 5 := ⟨3+a.val,by omega⟩

private theorem k304COMColumn5_label (a : Fin 1) :
    k305COMLabel9 (k304COMColumn5 a) = ⟨(⟨4,by decide⟩ : Fin 9),
      ⟨a.val,by simpa [natCOMRelativeDimension] using a.isLt⟩⟩ := by
  fin_cases a <;> rfl

def k304COMColumn6 (a : Fin 1) : Fin 7 := ⟨3+a.val,by omega⟩

private theorem k304COMColumn6_label (a : Fin 1) :
    k306COMLabel9 (k304COMColumn6 a) = ⟨(⟨4,by decide⟩ : Fin 9),
      ⟨a.val,by simpa [natCOMRelativeDimension] using a.isLt⟩⟩ := by
  fin_cases a <;> rfl

def k304COMColumn7 (a : Fin 1) : Fin 8 := ⟨3+a.val,by omega⟩

private theorem k304COMColumn7_label (a : Fin 1) :
    k307COMLabel9 (k304COMColumn7 a) = ⟨(⟨4,by decide⟩ : Fin 9),
      ⟨a.val,by simpa [natCOMRelativeDimension] using a.isLt⟩⟩ := by
  fin_cases a <;> rfl

def k304COMColumn8 (a : Fin 1) : Fin 10 := ⟨3+a.val,by omega⟩

private theorem k304COMColumn8_label (a : Fin 1) :
    k308COMLabel9 (k304COMColumn8 a) = ⟨(⟨4,by decide⟩ : Fin 9),
      ⟨a.val,by simpa [natCOMRelativeDimension] using a.isLt⟩⟩ := by
  fin_cases a <;> rfl

/-- Actual same-label C blocks with the original μ2 factor (2/3)·3^n n!. -/
def k304COMAveragedRankCoefficient : Matrix (Fin 1) (Fin 1) ℂ :=
  (((2/3 : ℚ) * (3 : ℚ)^0 * (Nat.factorial 0 : ℚ)) : ℂ) • (k304COMRankCoefficient.submatrix k304COMColumn4 k304COMColumn4) +
    (((2/3 : ℚ) * (3 : ℚ)^1 * (Nat.factorial 1 : ℚ)) : ℂ) • (k305COMRankCoefficient.submatrix k304COMColumn5 k304COMColumn5) +
    (((2/3 : ℚ) * (3 : ℚ)^2 * (Nat.factorial 2 : ℚ)) : ℂ) • (k306COMRankCoefficient.submatrix k304COMColumn6 k304COMColumn6) +
    (((2/3 : ℚ) * (3 : ℚ)^3 * (Nat.factorial 3 : ℚ)) : ℂ) • (k307COMRankCoefficient.submatrix k304COMColumn7 k304COMColumn7) +
    (((2/3 : ℚ) * (3 : ℚ)^4 * (Nat.factorial 4 : ℚ)) : ℂ) • (k308COMRankCoefficient.submatrix k304COMColumn8 k304COMColumn8)

private def k304COMAveragedRankRat : Matrix (Fin 1) (Fin 1) ℚ :=
  ((2/3 : ℚ) * (3 : ℚ)^0 * (Nat.factorial 0 : ℚ)) • (k304COMRankRatValue.submatrix k304COMColumn4 k304COMColumn4) +
    ((2/3 : ℚ) * (3 : ℚ)^1 * (Nat.factorial 1 : ℚ)) • (k305COMRankRatValue.submatrix k304COMColumn5 k304COMColumn5) +
    ((2/3 : ℚ) * (3 : ℚ)^2 * (Nat.factorial 2 : ℚ)) • (k306COMRankRatValue.submatrix k304COMColumn6 k304COMColumn6) +
    ((2/3 : ℚ) * (3 : ℚ)^3 * (Nat.factorial 3 : ℚ)) • (k307COMRankRatValue.submatrix k304COMColumn7 k304COMColumn7) +
    ((2/3 : ℚ) * (3 : ℚ)^4 * (Nat.factorial 4 : ℚ)) • (k308COMRankRatValue.submatrix k304COMColumn8 k304COMColumn8)

private theorem k304_COM_average_rank_rat :
    k304COMAveragedRankRat = k304J * b304average * k304J := by
  decide +kernel

/-- The genuine finite weighted rank average is J·averageRaw·J, with both Gram inverses. -/
theorem k304_COM_averaged_rank_coefficient :
    k304COMAveragedRankCoefficient = complexify (k304J * c304averageRaw * k304J) := by
  have h : k304COMAveragedRankCoefficient = complexify k304COMAveragedRankRat := by
    simp only [k304COMAveragedRankCoefficient,k304COMAveragedRankRat,
      k304_COM_rank_coefficient_value,
      k305_COM_rank_coefficient_value,
      k306_COM_rank_coefficient_value,
      k307_COM_rank_coefficient_value,
      k308_COM_rank_coefficient_value,
      complexify_add_rect,complexify_smul_rat,natCOM_complexify_submatrix,
      Rat.cast_mul,Rat.cast_pow,Rat.cast_natCast,Rat.cast_div,Rat.cast_ofNat]
  rw [h,k304_COM_average_rank_rat,c304_COM_reconstructed]

#print axioms k304_COM_averaged_rank_coefficient

/-- Exact entrywise endpoint for finite physical reindexing, with both relative duals. -/
theorem k304_COM_averaged_rank_entry (a b : Fin 1) :
    ((2/3 : ℂ) * (3 : ℂ)^0 * (Nat.factorial 0 : ℂ)) *
      k304COMRankCoefficient (k304COMColumn4 a) (k304COMColumn4 b) +
    ((2/3 : ℂ) * (3 : ℂ)^1 * (Nat.factorial 1 : ℂ)) *
      k305COMRankCoefficient (k304COMColumn5 a) (k304COMColumn5 b) +
    ((2/3 : ℂ) * (3 : ℂ)^2 * (Nat.factorial 2 : ℂ)) *
      k306COMRankCoefficient (k304COMColumn6 a) (k304COMColumn6 b) +
    ((2/3 : ℂ) * (3 : ℂ)^3 * (Nat.factorial 3 : ℂ)) *
      k307COMRankCoefficient (k304COMColumn7 a) (k304COMColumn7 b) +
    ((2/3 : ℂ) * (3 : ℂ)^4 * (Nat.factorial 4 : ℂ)) *
      k308COMRankCoefficient (k304COMColumn8 a) (k304COMColumn8 b) =
      (complexify k304J * complexify b304average * complexify k304J) a b := by
  have h := congrFun (congrFun k304_COM_averaged_rank_coefficient a) b
  rw [c304_COM_reconstructed] at h
  simpa only [k304COMAveragedRankCoefficient,complexify_mul_rect,
    Matrix.add_apply,Matrix.smul_apply,Matrix.submatrix_apply,smul_eq_mul,
    Rat.cast_mul,Rat.cast_div,Rat.cast_pow,Rat.cast_natCast,Rat.cast_ofNat] using h

#print axioms k304_COM_averaged_rank_entry

def k305COMColumn5 (a : Fin 1) : Fin 5 := ⟨4+a.val,by omega⟩

private theorem k305COMColumn5_label (a : Fin 1) :
    k305COMLabel9 (k305COMColumn5 a) = ⟨(⟨5,by decide⟩ : Fin 9),
      ⟨a.val,by simpa [natCOMRelativeDimension] using a.isLt⟩⟩ := by
  fin_cases a <;> rfl

def k305COMColumn6 (a : Fin 1) : Fin 7 := ⟨4+a.val,by omega⟩

private theorem k305COMColumn6_label (a : Fin 1) :
    k306COMLabel9 (k305COMColumn6 a) = ⟨(⟨5,by decide⟩ : Fin 9),
      ⟨a.val,by simpa [natCOMRelativeDimension] using a.isLt⟩⟩ := by
  fin_cases a <;> rfl

def k305COMColumn7 (a : Fin 1) : Fin 8 := ⟨4+a.val,by omega⟩

private theorem k305COMColumn7_label (a : Fin 1) :
    k307COMLabel9 (k305COMColumn7 a) = ⟨(⟨5,by decide⟩ : Fin 9),
      ⟨a.val,by simpa [natCOMRelativeDimension] using a.isLt⟩⟩ := by
  fin_cases a <;> rfl

def k305COMColumn8 (a : Fin 1) : Fin 10 := ⟨4+a.val,by omega⟩

private theorem k305COMColumn8_label (a : Fin 1) :
    k308COMLabel9 (k305COMColumn8 a) = ⟨(⟨5,by decide⟩ : Fin 9),
      ⟨a.val,by simpa [natCOMRelativeDimension] using a.isLt⟩⟩ := by
  fin_cases a <;> rfl

/-- Actual same-label C blocks with the original μ2 factor (2/3)·3^n n!. -/
def k305COMAveragedRankCoefficient : Matrix (Fin 1) (Fin 1) ℂ :=
  (((2/3 : ℚ) * (3 : ℚ)^0 * (Nat.factorial 0 : ℚ)) : ℂ) • (k305COMRankCoefficient.submatrix k305COMColumn5 k305COMColumn5) +
    (((2/3 : ℚ) * (3 : ℚ)^1 * (Nat.factorial 1 : ℚ)) : ℂ) • (k306COMRankCoefficient.submatrix k305COMColumn6 k305COMColumn6) +
    (((2/3 : ℚ) * (3 : ℚ)^2 * (Nat.factorial 2 : ℚ)) : ℂ) • (k307COMRankCoefficient.submatrix k305COMColumn7 k305COMColumn7) +
    (((2/3 : ℚ) * (3 : ℚ)^3 * (Nat.factorial 3 : ℚ)) : ℂ) • (k308COMRankCoefficient.submatrix k305COMColumn8 k305COMColumn8)

private def k305COMAveragedRankRat : Matrix (Fin 1) (Fin 1) ℚ :=
  ((2/3 : ℚ) * (3 : ℚ)^0 * (Nat.factorial 0 : ℚ)) • (k305COMRankRatValue.submatrix k305COMColumn5 k305COMColumn5) +
    ((2/3 : ℚ) * (3 : ℚ)^1 * (Nat.factorial 1 : ℚ)) • (k306COMRankRatValue.submatrix k305COMColumn6 k305COMColumn6) +
    ((2/3 : ℚ) * (3 : ℚ)^2 * (Nat.factorial 2 : ℚ)) • (k307COMRankRatValue.submatrix k305COMColumn7 k305COMColumn7) +
    ((2/3 : ℚ) * (3 : ℚ)^3 * (Nat.factorial 3 : ℚ)) • (k308COMRankRatValue.submatrix k305COMColumn8 k305COMColumn8)

private theorem k305_COM_average_rank_rat :
    k305COMAveragedRankRat = k305J * b305average * k305J := by
  decide +kernel

/-- The genuine finite weighted rank average is J·averageRaw·J, with both Gram inverses. -/
theorem k305_COM_averaged_rank_coefficient :
    k305COMAveragedRankCoefficient = complexify (k305J * c305averageRaw * k305J) := by
  have h : k305COMAveragedRankCoefficient = complexify k305COMAveragedRankRat := by
    simp only [k305COMAveragedRankCoefficient,k305COMAveragedRankRat,
      k305_COM_rank_coefficient_value,
      k306_COM_rank_coefficient_value,
      k307_COM_rank_coefficient_value,
      k308_COM_rank_coefficient_value,
      complexify_add_rect,complexify_smul_rat,natCOM_complexify_submatrix,
      Rat.cast_mul,Rat.cast_pow,Rat.cast_natCast,Rat.cast_div,Rat.cast_ofNat]
  rw [h,k305_COM_average_rank_rat,c305_COM_reconstructed]

#print axioms k305_COM_averaged_rank_coefficient

/-- Exact entrywise endpoint for finite physical reindexing, with both relative duals. -/
theorem k305_COM_averaged_rank_entry (a b : Fin 1) :
    ((2/3 : ℂ) * (3 : ℂ)^0 * (Nat.factorial 0 : ℂ)) *
      k305COMRankCoefficient (k305COMColumn5 a) (k305COMColumn5 b) +
    ((2/3 : ℂ) * (3 : ℂ)^1 * (Nat.factorial 1 : ℂ)) *
      k306COMRankCoefficient (k305COMColumn6 a) (k305COMColumn6 b) +
    ((2/3 : ℂ) * (3 : ℂ)^2 * (Nat.factorial 2 : ℂ)) *
      k307COMRankCoefficient (k305COMColumn7 a) (k305COMColumn7 b) +
    ((2/3 : ℂ) * (3 : ℂ)^3 * (Nat.factorial 3 : ℂ)) *
      k308COMRankCoefficient (k305COMColumn8 a) (k305COMColumn8 b) =
      (complexify k305J * complexify b305average * complexify k305J) a b := by
  have h := congrFun (congrFun k305_COM_averaged_rank_coefficient a) b
  rw [c305_COM_reconstructed] at h
  simpa only [k305COMAveragedRankCoefficient,complexify_mul_rect,
    Matrix.add_apply,Matrix.smul_apply,Matrix.submatrix_apply,smul_eq_mul,
    Rat.cast_mul,Rat.cast_div,Rat.cast_pow,Rat.cast_natCast,Rat.cast_ofNat] using h

#print axioms k305_COM_averaged_rank_entry

def k306COMColumn6 (a : Fin 2) : Fin 7 := ⟨5+a.val,by omega⟩

private theorem k306COMColumn6_label (a : Fin 2) :
    k306COMLabel9 (k306COMColumn6 a) = ⟨(⟨6,by decide⟩ : Fin 9),
      ⟨a.val,by simpa [natCOMRelativeDimension] using a.isLt⟩⟩ := by
  fin_cases a <;> rfl

def k306COMColumn7 (a : Fin 2) : Fin 8 := ⟨5+a.val,by omega⟩

private theorem k306COMColumn7_label (a : Fin 2) :
    k307COMLabel9 (k306COMColumn7 a) = ⟨(⟨6,by decide⟩ : Fin 9),
      ⟨a.val,by simpa [natCOMRelativeDimension] using a.isLt⟩⟩ := by
  fin_cases a <;> rfl

def k306COMColumn8 (a : Fin 2) : Fin 10 := ⟨5+a.val,by omega⟩

private theorem k306COMColumn8_label (a : Fin 2) :
    k308COMLabel9 (k306COMColumn8 a) = ⟨(⟨6,by decide⟩ : Fin 9),
      ⟨a.val,by simpa [natCOMRelativeDimension] using a.isLt⟩⟩ := by
  fin_cases a <;> rfl

/-- Actual same-label C blocks with the original μ2 factor (2/3)·3^n n!. -/
def k306COMAveragedRankCoefficient : Matrix (Fin 2) (Fin 2) ℂ :=
  (((2/3 : ℚ) * (3 : ℚ)^0 * (Nat.factorial 0 : ℚ)) : ℂ) • (k306COMRankCoefficient.submatrix k306COMColumn6 k306COMColumn6) +
    (((2/3 : ℚ) * (3 : ℚ)^1 * (Nat.factorial 1 : ℚ)) : ℂ) • (k307COMRankCoefficient.submatrix k306COMColumn7 k306COMColumn7) +
    (((2/3 : ℚ) * (3 : ℚ)^2 * (Nat.factorial 2 : ℚ)) : ℂ) • (k308COMRankCoefficient.submatrix k306COMColumn8 k306COMColumn8)

private def k306COMAveragedRankRat : Matrix (Fin 2) (Fin 2) ℚ :=
  ((2/3 : ℚ) * (3 : ℚ)^0 * (Nat.factorial 0 : ℚ)) • (k306COMRankRatValue.submatrix k306COMColumn6 k306COMColumn6) +
    ((2/3 : ℚ) * (3 : ℚ)^1 * (Nat.factorial 1 : ℚ)) • (k307COMRankRatValue.submatrix k306COMColumn7 k306COMColumn7) +
    ((2/3 : ℚ) * (3 : ℚ)^2 * (Nat.factorial 2 : ℚ)) • (k308COMRankRatValue.submatrix k306COMColumn8 k306COMColumn8)

private theorem k306_COM_average_rank_rat :
    k306COMAveragedRankRat = k306J * b306average * k306J := by
  decide +kernel

/-- The genuine finite weighted rank average is J·averageRaw·J, with both Gram inverses. -/
theorem k306_COM_averaged_rank_coefficient :
    k306COMAveragedRankCoefficient = complexify (k306J * c306averageRaw * k306J) := by
  have h : k306COMAveragedRankCoefficient = complexify k306COMAveragedRankRat := by
    simp only [k306COMAveragedRankCoefficient,k306COMAveragedRankRat,
      k306_COM_rank_coefficient_value,
      k307_COM_rank_coefficient_value,
      k308_COM_rank_coefficient_value,
      complexify_add_rect,complexify_smul_rat,natCOM_complexify_submatrix,
      Rat.cast_mul,Rat.cast_pow,Rat.cast_natCast,Rat.cast_div,Rat.cast_ofNat]
  rw [h,k306_COM_average_rank_rat,c306_COM_reconstructed]

#print axioms k306_COM_averaged_rank_coefficient

/-- Exact entrywise endpoint for finite physical reindexing, with both relative duals. -/
theorem k306_COM_averaged_rank_entry (a b : Fin 2) :
    ((2/3 : ℂ) * (3 : ℂ)^0 * (Nat.factorial 0 : ℂ)) *
      k306COMRankCoefficient (k306COMColumn6 a) (k306COMColumn6 b) +
    ((2/3 : ℂ) * (3 : ℂ)^1 * (Nat.factorial 1 : ℂ)) *
      k307COMRankCoefficient (k306COMColumn7 a) (k306COMColumn7 b) +
    ((2/3 : ℂ) * (3 : ℂ)^2 * (Nat.factorial 2 : ℂ)) *
      k308COMRankCoefficient (k306COMColumn8 a) (k306COMColumn8 b) =
      (complexify k306J * complexify b306average * complexify k306J) a b := by
  have h := congrFun (congrFun k306_COM_averaged_rank_coefficient a) b
  rw [c306_COM_reconstructed] at h
  simpa only [k306COMAveragedRankCoefficient,complexify_mul_rect,
    Matrix.add_apply,Matrix.smul_apply,Matrix.submatrix_apply,smul_eq_mul,
    Rat.cast_mul,Rat.cast_div,Rat.cast_pow,Rat.cast_natCast,Rat.cast_ofNat] using h

#print axioms k306_COM_averaged_rank_entry

def k307COMColumn7 (a : Fin 1) : Fin 8 := ⟨7+a.val,by omega⟩

private theorem k307COMColumn7_label (a : Fin 1) :
    k307COMLabel9 (k307COMColumn7 a) = ⟨(⟨7,by decide⟩ : Fin 9),
      ⟨a.val,by simpa [natCOMRelativeDimension] using a.isLt⟩⟩ := by
  fin_cases a <;> rfl

def k307COMColumn8 (a : Fin 1) : Fin 10 := ⟨7+a.val,by omega⟩

private theorem k307COMColumn8_label (a : Fin 1) :
    k308COMLabel9 (k307COMColumn8 a) = ⟨(⟨7,by decide⟩ : Fin 9),
      ⟨a.val,by simpa [natCOMRelativeDimension] using a.isLt⟩⟩ := by
  fin_cases a <;> rfl

/-- Actual same-label C blocks with the original μ2 factor (2/3)·3^n n!. -/
def k307COMAveragedRankCoefficient : Matrix (Fin 1) (Fin 1) ℂ :=
  (((2/3 : ℚ) * (3 : ℚ)^0 * (Nat.factorial 0 : ℚ)) : ℂ) • (k307COMRankCoefficient.submatrix k307COMColumn7 k307COMColumn7) +
    (((2/3 : ℚ) * (3 : ℚ)^1 * (Nat.factorial 1 : ℚ)) : ℂ) • (k308COMRankCoefficient.submatrix k307COMColumn8 k307COMColumn8)

private def k307COMAveragedRankRat : Matrix (Fin 1) (Fin 1) ℚ :=
  ((2/3 : ℚ) * (3 : ℚ)^0 * (Nat.factorial 0 : ℚ)) • (k307COMRankRatValue.submatrix k307COMColumn7 k307COMColumn7) +
    ((2/3 : ℚ) * (3 : ℚ)^1 * (Nat.factorial 1 : ℚ)) • (k308COMRankRatValue.submatrix k307COMColumn8 k307COMColumn8)

private theorem k307_COM_average_rank_rat :
    k307COMAveragedRankRat = k307J * b307average * k307J := by
  decide +kernel

/-- The genuine finite weighted rank average is J·averageRaw·J, with both Gram inverses. -/
theorem k307_COM_averaged_rank_coefficient :
    k307COMAveragedRankCoefficient = complexify (k307J * c307averageRaw * k307J) := by
  have h : k307COMAveragedRankCoefficient = complexify k307COMAveragedRankRat := by
    simp only [k307COMAveragedRankCoefficient,k307COMAveragedRankRat,
      k307_COM_rank_coefficient_value,
      k308_COM_rank_coefficient_value,
      complexify_add_rect,complexify_smul_rat,natCOM_complexify_submatrix,
      Rat.cast_mul,Rat.cast_pow,Rat.cast_natCast,Rat.cast_div,Rat.cast_ofNat]
  rw [h,k307_COM_average_rank_rat,c307_COM_reconstructed]

#print axioms k307_COM_averaged_rank_coefficient

/-- Exact entrywise endpoint for finite physical reindexing, with both relative duals. -/
theorem k307_COM_averaged_rank_entry (a b : Fin 1) :
    ((2/3 : ℂ) * (3 : ℂ)^0 * (Nat.factorial 0 : ℂ)) *
      k307COMRankCoefficient (k307COMColumn7 a) (k307COMColumn7 b) +
    ((2/3 : ℂ) * (3 : ℂ)^1 * (Nat.factorial 1 : ℂ)) *
      k308COMRankCoefficient (k307COMColumn8 a) (k307COMColumn8 b) =
      (complexify k307J * complexify b307average * complexify k307J) a b := by
  have h := congrFun (congrFun k307_COM_averaged_rank_coefficient a) b
  rw [c307_COM_reconstructed] at h
  simpa only [k307COMAveragedRankCoefficient,complexify_mul_rect,
    Matrix.add_apply,Matrix.smul_apply,Matrix.submatrix_apply,smul_eq_mul,
    Rat.cast_mul,Rat.cast_div,Rat.cast_pow,Rat.cast_natCast,Rat.cast_ofNat] using h

#print axioms k307_COM_averaged_rank_entry

def k308COMColumn8 (a : Fin 2) : Fin 10 := ⟨8+a.val,by omega⟩

private theorem k308COMColumn8_label (a : Fin 2) :
    k308COMLabel9 (k308COMColumn8 a) = ⟨(⟨8,by decide⟩ : Fin 9),
      ⟨a.val,by simpa [natCOMRelativeDimension] using a.isLt⟩⟩ := by
  fin_cases a <;> rfl

/-- Actual same-label C blocks with the original μ2 factor (2/3)·3^n n!. -/
def k308COMAveragedRankCoefficient : Matrix (Fin 2) (Fin 2) ℂ :=
  (((2/3 : ℚ) * (3 : ℚ)^0 * (Nat.factorial 0 : ℚ)) : ℂ) • (k308COMRankCoefficient.submatrix k308COMColumn8 k308COMColumn8)

private def k308COMAveragedRankRat : Matrix (Fin 2) (Fin 2) ℚ :=
  ((2/3 : ℚ) * (3 : ℚ)^0 * (Nat.factorial 0 : ℚ)) • (k308COMRankRatValue.submatrix k308COMColumn8 k308COMColumn8)

private theorem k308_COM_average_rank_rat :
    k308COMAveragedRankRat = k308J * b308average * k308J := by
  decide +kernel

/-- The genuine finite weighted rank average is J·averageRaw·J, with both Gram inverses. -/
theorem k308_COM_averaged_rank_coefficient :
    k308COMAveragedRankCoefficient = complexify (k308J * c308averageRaw * k308J) := by
  have h : k308COMAveragedRankCoefficient = complexify k308COMAveragedRankRat := by
    simp only [k308COMAveragedRankCoefficient,k308COMAveragedRankRat,
      k308_COM_rank_coefficient_value,
      complexify_add_rect,complexify_smul_rat,natCOM_complexify_submatrix,
      Rat.cast_mul,Rat.cast_pow,Rat.cast_natCast,Rat.cast_div,Rat.cast_ofNat]
  rw [h,k308_COM_average_rank_rat,c308_COM_reconstructed]

#print axioms k308_COM_averaged_rank_coefficient

/-- Exact entrywise endpoint for finite physical reindexing, with both relative duals. -/
theorem k308_COM_averaged_rank_entry (a b : Fin 2) :
    ((2/3 : ℂ) * (3 : ℂ)^0 * (Nat.factorial 0 : ℂ)) *
      k308COMRankCoefficient (k308COMColumn8 a) (k308COMColumn8 b) =
      (complexify k308J * complexify b308average * complexify k308J) a b := by
  have h := congrFun (congrFun k308_COM_averaged_rank_coefficient a) b
  rw [c308_COM_reconstructed] at h
  simpa only [k308COMAveragedRankCoefficient,complexify_mul_rect,
    Matrix.add_apply,Matrix.smul_apply,Matrix.submatrix_apply,smul_eq_mul,
    Rat.cast_mul,Rat.cast_div,Rat.cast_pow,Rat.cast_natCast,Rat.cast_ofNat] using h

#print axioms k308_COM_averaged_rank_entry

end TorusLean.BosonFiniteCertificate
