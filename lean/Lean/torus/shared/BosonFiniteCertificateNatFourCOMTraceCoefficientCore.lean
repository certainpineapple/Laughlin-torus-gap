import torus.shared.BosonFiniteCertificateNatFourCOMBlockGram
import torus.shared.BosonFiniteCertificateNatFourCOMForm

/-! Exact finite coefficient algebra behind the genuine COM trace. The
unnormalized trace contributes w/2; the complete-family inverse Gram supplies
1/w on each side. Their product is exactly the original 2/(4^(n+1)n!). -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2
open TorusLean.Shared.BosonFiniteCertificateRealization
open Matrix
open scoped BigOperators

private theorem blockDiagonal_mul_row {k : ℕ} (dim : Fin k → ℕ)
    (J : ∀ d, Matrix (Fin (dim d)) (Fin (dim d)) ℂ)
    (E : Matrix (Σ d, Fin (dim d)) (Σ d, Fin (dim d)) ℂ)
    (d : Fin k) (a : Fin (dim d)) (b : Σ d, Fin (dim d)) :
    (Matrix.blockDiagonal' J*E) ⟨d,a⟩ b =
      ∑ c, J d a c*E ⟨d,c⟩ b := by
  simp only [Matrix.mul_apply,←Finset.univ_sigma_univ,Finset.sum_sigma]
  rw [Fintype.sum_eq_single d]
  · simp only [Matrix.blockDiagonal'_apply_eq]
  · intro e he
    apply Finset.sum_eq_zero
    intro c hc
    rw [Matrix.blockDiagonal'_apply_ne J a c he.symm,zero_mul]

private theorem mul_blockDiagonal_col {k : ℕ} (dim : Fin k → ℕ)
    (J : ∀ d, Matrix (Fin (dim d)) (Fin (dim d)) ℂ)
    (E : Matrix (Σ d, Fin (dim d)) (Σ d, Fin (dim d)) ℂ)
    (a : Σ d, Fin (dim d)) (d : Fin k) (b : Fin (dim d)) :
    (E*Matrix.blockDiagonal' J) a ⟨d,b⟩ =
      ∑ c, E a ⟨d,c⟩*J d c b := by
  simp only [Matrix.mul_apply,←Finset.univ_sigma_univ,Finset.sum_sigma]
  rw [Fintype.sum_eq_single d]
  · simp only [Matrix.blockDiagonal'_apply_eq]
  · intro e he
    apply Finset.sum_eq_zero
    intro c hc
    rw [Matrix.blockDiagonal'_apply_ne J c b he,mul_zero]

theorem natFour_block_inverse_coefficient_fiber {k : ℕ} (dim : Fin k → ℕ)
    (J : ∀ d, Matrix (Fin (dim d)) (Fin (dim d)) ℂ)
    (E : Matrix (Σ d, Fin (dim d)) (Σ d, Fin (dim d)) ℂ) (d : Fin k) :
    (Matrix.blockDiagonal' J*E*Matrix.blockDiagonal' J).submatrix
      (fun a => (⟨d,a⟩ : Σ z, Fin (dim z))) (fun a => (⟨d,a⟩ : Σ z, Fin (dim z))) =
        inverseGramCoefficient (J d) (E.submatrix (fun a => (⟨d,a⟩ : Σ z, Fin (dim z))) (fun a => (⟨d,a⟩ : Σ z, Fin (dim z)))) := by
  ext a b
  change ((Matrix.blockDiagonal' J*E)*Matrix.blockDiagonal' J) ⟨d,a⟩ ⟨d,b⟩ = _
  rw [mul_blockDiagonal_col]
  simp_rw [blockDiagonal_mul_row]
  simp only [inverseGramCoefficient,Matrix.mul_apply,Matrix.submatrix_apply]

/-- Reindexing the complete family does not change the extracted fiber.
The equivalence is used on both matrix indices and is never a numerical basis
replacement. -/
theorem natFour_block_inverse_coefficient_reindexed_fiber {k N : ℕ}
    (dim : Fin k → ℕ) (J : ∀ d, Matrix (Fin (dim d)) (Fin (dim d)) ℂ)
    (E : Matrix (Fin N) (Fin N) ℂ) (e : Fin N ≃ Σ d, Fin (dim d)) (d : Fin k) :
    (inverseGramCoefficient ((Matrix.blockDiagonal' J).submatrix e e) E).submatrix
      (fun a => e.symm ⟨d,a⟩) (fun a => e.symm ⟨d,a⟩) =
        inverseGramCoefficient (J d)
          (E.submatrix (fun a => e.symm ⟨d,a⟩) (fun a => e.symm ⟨d,a⟩)) := by
  let E' := E.submatrix e.symm e.symm
  have he : E'.submatrix e e=E := by
    ext a b
    simp only [E',Matrix.submatrix_apply,Equiv.symm_apply_apply]
  have hh : inverseGramCoefficient ((Matrix.blockDiagonal' J).submatrix e e) E=
      (Matrix.blockDiagonal' J*E'*Matrix.blockDiagonal' J).submatrix e e := by
    calc
      _ = inverseGramCoefficient ((Matrix.blockDiagonal' J).submatrix e e)
          (E'.submatrix e e) := by rw [he]
      _ = _ := by simp only [inverseGramCoefficient,Matrix.submatrix_mul_equiv]
  rw [hh]
  simpa only [E',Matrix.submatrix_submatrix,Function.comp_def,Equiv.apply_symm_apply]
    using natFour_block_inverse_coefficient_fiber dim J E' d

/-- Each diagonal COM fiber has the inverse weight on both sides. -/
theorem natFour_COM_inverse_coefficient_fiber (D : ℕ) (dim : Fin (D+1) → ℕ)
    (J : ∀ d, Matrix (Fin (dim d)) (Fin (dim d)) ℂ)
    (E : Matrix (Σ d, Fin (dim d)) (Σ d, Fin (dim d)) ℂ) (d : Fin (D+1)) :
    (natFourCOMBlockInverse D dim J*E*natFourCOMBlockInverse D dim J).submatrix
      (fun a => (⟨d,a⟩ : Σ z, Fin (dim z))) (fun a => (⟨d,a⟩ : Σ z, Fin (dim z))) =
        ((natFourCOMWeight (D-d.val))⁻¹*(natFourCOMWeight (D-d.val))⁻¹) •
          inverseGramCoefficient (J d) (E.submatrix (fun a => (⟨d,a⟩ : Σ z, Fin (dim z))) (fun a => (⟨d,a⟩ : Σ z, Fin (dim z)))) := by
  rw [natFourCOMBlockInverse,natFour_block_inverse_coefficient_fiber]
  simp only [inverseGramCoefficient,Matrix.smul_mul,Matrix.mul_smul,smul_smul]

theorem natFour_COM_trace_inverse_weight (n : ℕ) :
    (natFourCOMWeight n/2)*((natFourCOMWeight n)⁻¹*(natFourCOMWeight n)⁻¹)=
      (natFourOriginalCOMWeight n : ℂ) := by
  have hw := natFourCOMWeight_ne_zero n
  have hn : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  unfold natFourCOMWeight natFourOriginalCOMWeight at *
  push_cast
  rw [pow_succ]
  field_simp
  <;> ring

/-- Pure finite matrix identity; source compression identities remain explicit
inputs. It does not assert any physical integral or source replacement. -/
theorem natFour_COM_trace_coefficient_sum {r N : ℕ}
    (J : Matrix (Fin r) (Fin r) ℂ)
    (E C : Fin N → Matrix (Fin r) (Fin r) ℂ)
    (A : Matrix (Fin r) (Fin r) ℂ)
    (hC : ∀ n, C n=((natFourCOMWeight n.val)⁻¹*(natFourCOMWeight n.val)⁻¹) •
      inverseGramCoefficient J (E n))
    (hA : ∑ n, (natFourOriginalCOMWeight n.val : ℂ) • E n=A) :
    (∑ n, (natFourCOMWeight n.val/2) • C n)=inverseGramCoefficient J A := by
  simp_rw [hC,smul_smul,natFour_COM_trace_inverse_weight]
  rw [←hA]
  simp only [inverseGramCoefficient,Matrix.mul_sum,Matrix.sum_mul,
    Matrix.mul_smul,Matrix.smul_mul]

#print axioms natFour_block_inverse_coefficient_fiber
#print axioms natFour_block_inverse_coefficient_reindexed_fiber
#print axioms natFour_COM_inverse_coefficient_fiber
#print axioms natFour_COM_trace_inverse_weight
#print axioms natFour_COM_trace_coefficient_sum
end TorusLean.BosonFiniteCertificate
