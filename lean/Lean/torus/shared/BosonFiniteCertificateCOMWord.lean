import torus.shared.BosonFiniteCertificateCanonicalCOMLower
import torus.shared.BosonFiniteCertificateRescaleCCR
import torus.shared.BosonAnchoredSeedActions

/-! Actual factorial-conjugated COM generators on arbitrary ordered canonical
words. The raise identity has the explicit no-top-orbital guard. The lower
identity includes orbital zero with its vanishing square-root coefficient. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open scoped BigOperators
open TorusLean.Boson
open TorusLean.Shared.BosonFiniteCertificateWords
open TorusLean.Shared.BosonFiniteCertificateConjugation
open TorusLean.Shared.BosonFiniteCertificateRescaleCCR
open TorusLean.Shared.ThermalCoherentSeedWord
open TorusLean.Shared.BosonAnchoredSeedActions

private theorem com_conjugate_sum {I : Type*} [Fintype I]
    (A : I → Core (Fin 9) ℂ →ₗ[ℂ] Core (Fin 9) ℂ) :
    conjugateOperator factorialRoot9 factorialRoot9_ne_zero (∑ a, A a) =
      ∑ a, conjugateOperator factorialRoot9 factorialRoot9_ne_zero (A a) := by
  apply LinearMap.ext
  intro p
  simp [conjugateOperator, LinearMap.sum_apply, map_sum]

private theorem com_conjugate_smul (c : ℂ)
    (A : Core (Fin 9) ℂ →ₗ[ℂ] Core (Fin 9) ℂ) :
    conjugateOperator factorialRoot9 factorialRoot9_ne_zero (c • A) =
      c • conjugateOperator factorialRoot9 factorialRoot9_ne_zero A := by
  apply LinearMap.ext
  intro p
  simp [conjugateOperator]

private theorem com_root_succ (j : Fin 8) :
    factorialRoot9 (raiseTarget9 j) =
      (Real.sqrt (j.val+1 : ℝ) : ℂ) * factorialRoot9 (raiseSource9 j) := by
  unfold factorialRoot9 raiseTarget9 raiseSource9
  rw [Nat.factorial_succ, Nat.cast_mul, Real.sqrt_mul (by positivity), Complex.ofReal_mul]
  norm_cast

private theorem com_root_raise_ratio (j : Fin 8) :
    factorialRoot9 (raiseTarget9 j) / factorialRoot9 (raiseSource9 j) =
      (Real.sqrt (j.val+1 : ℝ) : ℂ) := by
  rw [com_root_succ, mul_div_cancel_right₀ _ (factorialRoot9_ne_zero _)]

private theorem com_root_lower_ratio (j : Fin 8) :
    (j.val+1 : ℂ) * (factorialRoot9 (raiseSource9 j) / factorialRoot9 (raiseTarget9 j)) =
      (Real.sqrt (j.val+1 : ℝ) : ℂ) := by
  rw [com_root_succ]
  have ha : (Real.sqrt (j.val+1 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by positivity)
  have hb := factorialRoot9_ne_zero (raiseSource9 j)
  have hs : (Real.sqrt (j.val+1 : ℝ) : ℂ)^2 = (j.val+1 : ℂ) := by
    exact_mod_cast Real.sq_sqrt (show (0:ℝ) ≤ j.val+1 by positivity)
  rw [← hs]
  field_simp

theorem canonicalCOMRaise9_differential :
    canonicalCOMRaise9 = ∑ j : Fin 8,
      (Real.sqrt (j.val+1 : ℝ) : ℂ) • normalWord [raiseTarget9 j] [raiseSource9 j] := by
  rw [canonicalCOMRaise9, finitePaperRaise9, com_conjugate_sum]
  simp_rw [conjugateOperator_one_body, com_root_raise_ratio]

theorem canonicalCOMLower9_differential :
    canonicalCOMLower9 = ∑ j : Fin 8,
      (Real.sqrt (j.val+1 : ℝ) : ℂ) • normalWord [raiseSource9 j] [raiseTarget9 j] := by
  rw [canonicalCOMLower9, finitePaperLower9, com_conjugate_sum]
  simp_rw [com_conjugate_smul, conjugateOperator_one_body, smul_smul,
    com_root_lower_ratio]

private theorem com_onebody_apply (a b : Fin 9) (p : Core (Fin 9) ℂ) :
    normalWord [b] [a] p = MvPolynomial.X b * MvPolynomial.pderiv a p := by
  change (MvPolynomial.X b * 1) * MvPolynomial.pderiv a p = _
  rw [mul_one]

private theorem com_onebody_mul (a b : Fin 9) (p q : Core (Fin 9) ℂ) :
    normalWord [b] [a] (p*q) =
      normalWord [b] [a] p * q + p * normalWord [b] [a] q := by
  simp only [com_onebody_apply, MvPolynomial.pderiv_mul]
  ring

theorem canonicalCOMRaise9_mul (p q : Core (Fin 9) ℂ) :
    canonicalCOMRaise9 (p*q) = canonicalCOMRaise9 p * q + p * canonicalCOMRaise9 q := by
  simp [canonicalCOMRaise9_differential, LinearMap.sum_apply, com_onebody_mul,
    Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum,
    smul_add, smul_mul_assoc, mul_smul_comm]

theorem canonicalCOMLower9_mul (p q : Core (Fin 9) ℂ) :
    canonicalCOMLower9 (p*q) = canonicalCOMLower9 p * q + p * canonicalCOMLower9 q := by
  simp [canonicalCOMLower9_differential, LinearMap.sum_apply, com_onebody_mul,
    Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum,
    smul_add, smul_mul_assoc, mul_smul_comm]

private theorem com_onebody_X (a b c : Fin 9) :
    normalWord [b] [a] (MvPolynomial.X c : Core (Fin 9) ℂ) =
      if c=a then MvPolynomial.X b else 0 := by
  rw [com_onebody_apply]
  by_cases h : c=a <;> simp [h, MvPolynomial.pderiv_X]

private theorem com_source_injective : Function.Injective raiseSource9 := by
  intro a b h
  exact Fin.ext (congrArg (fun q : Fin 9 => q.val) h)

private theorem com_target_injective : Function.Injective raiseTarget9 := by
  intro a b h
  apply Fin.ext
  have he := congrArg Fin.val h
  change a.val+1=b.val+1 at he
  omega

theorem canonicalCOMRaise9_X_source (j : Fin 8) :
    canonicalCOMRaise9 (MvPolynomial.X (raiseSource9 j)) =
      (Real.sqrt (j.val+1 : ℝ) : ℂ) • MvPolynomial.X (raiseTarget9 j) := by
  simp [canonicalCOMRaise9_differential, LinearMap.sum_apply, com_onebody_X,
    com_source_injective.eq_iff]

theorem canonicalCOMLower9_X_target (j : Fin 8) :
    canonicalCOMLower9 (MvPolynomial.X (raiseTarget9 j)) =
      (Real.sqrt (j.val+1 : ℝ) : ℂ) • MvPolynomial.X (raiseSource9 j) := by
  simp [canonicalCOMLower9_differential, LinearMap.sum_apply, com_onebody_X,
    com_target_injective.eq_iff]

theorem canonicalCOMLower9_X_zero :
    canonicalCOMLower9 (MvPolynomial.X (0 : Fin 9)) = 0 := by
  have h (j : Fin 8) : (0 : Fin 9) ≠ raiseTarget9 j := by
    intro he
    have he' := congrArg Fin.val he
    change 0=j.val+1 at he'
    omega
  simp [canonicalCOMLower9_differential, LinearMap.sum_apply, com_onebody_X, h]

/-- Finite product rule derived only from the actual linear map and Leibniz. -/
theorem com_linear_product_rule {I : Type*} [DecidableEq I]
    (A : Core (Fin 9) ℂ →ₗ[ℂ] Core (Fin 9) ℂ)
    (hmul : ∀ p q, A (p*q) = A p*q+p*A q)
    (s : Finset I) (f : I → Core (Fin 9) ℂ) :
    A (∏ i ∈ s, f i) = ∑ i ∈ s, A (f i) * ∏ l ∈ s.erase i, f l := by
  have hOne : A 1 = 0 := by
    simpa only [mul_one, one_mul, add_eq_left] using (hmul 1 1).symm
  induction s using Finset.induction_on with
  | empty => simp [hOne]
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, hmul, ih, Finset.sum_insert ha]
    simp only [Finset.erase_insert ha]
    rw [Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro b hb
    have hba : b ≠ a := by intro h; subst b; exact ha hb
    rw [Finset.erase_insert_of_ne (Ne.symm hba), Finset.prod_insert (by simp [ha])]
    ring

private theorem com_word_update (k : ℕ) (j : Fin k → Fin 9) (i : Fin k) (n : Fin 9) :
    canonicalWord k (Function.update j i n) =
      MvPolynomial.X n * ∏ l ∈ Finset.univ.erase i, MvPolynomial.X (j l) := by
  unfold canonicalWord
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  simp only [Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro l hl
  rw [Function.update_of_ne (Finset.mem_erase.mp hl).1]

theorem canonicalCOMRaise9_word (k : ℕ) (j : Fin k → Fin 9)
    (htop : ∀ i, (j i).val+1<9) :
    canonicalCOMRaise9 (canonicalWord k j) =
      ∑ i, (Real.sqrt ((j i).val+1 : ℝ) : ℂ) •
        canonicalWord k (raiseWord 9 k j i (htop i)) := by
  rw [canonicalWord, com_linear_product_rule _ canonicalCOMRaise9_mul]
  apply Finset.sum_congr rfl
  intro i hi
  let a : Fin 8 := ⟨(j i).val, by have := htop i; omega⟩
  have ha : raiseSource9 a = j i := Fin.ext rfl
  rw [← ha, canonicalCOMRaise9_X_source]
  change _ = (Real.sqrt ((j i).val+1 : ℝ) : ℂ) •
    canonicalWord k (Function.update j i ⟨(j i).val+1, htop i⟩)
  rw [com_word_update]
  exact smul_mul_assoc _ _ _

theorem canonicalCOMLower9_word (k : ℕ) (j : Fin k → Fin 9) :
    canonicalCOMLower9 (canonicalWord k j) =
      ∑ i, (Real.sqrt ((j i).val : ℝ) : ℂ) •
        canonicalWord k (lowerWord 9 k j i) := by
  rw [canonicalWord, com_linear_product_rule _ canonicalCOMLower9_mul]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases h0 : (j i).val=0
  · have hj : j i = 0 := Fin.ext h0
    simp [hj, canonicalCOMLower9_X_zero]
  · let a : Fin 8 := ⟨(j i).val-1, by have := (j i).isLt; omega⟩
    have ha : raiseTarget9 a = j i := by apply Fin.ext; dsimp [raiseTarget9, a]; omega
    have hv : a.val+1=(j i).val := by dsimp [a]; omega
    have hX := canonicalCOMLower9_X_target a
    rw [ha] at hX
    rw [hX]
    change _ = (Real.sqrt ((j i).val : ℝ) : ℂ) •
      canonicalWord k (Function.update j i ⟨(j i).val-1, by have := (j i).isLt; omega⟩)
    rw [com_word_update]
    have hcast : (a.val : ℝ)+1 = ((j i).val : ℝ) := by exact_mod_cast hv
    rw [hcast]
    exact smul_mul_assoc _ _ _

#print axioms canonicalCOMRaise9_differential
#print axioms canonicalCOMLower9_differential
#print axioms canonicalCOMRaise9_mul
#print axioms canonicalCOMLower9_mul
#print axioms canonicalCOMRaise9_X_source
#print axioms canonicalCOMLower9_X_target
#print axioms canonicalCOMLower9_X_zero
#print axioms com_linear_product_rule
#print axioms canonicalCOMRaise9_word
#print axioms canonicalCOMLower9_word
end TorusLean.BosonFiniteCertificate
