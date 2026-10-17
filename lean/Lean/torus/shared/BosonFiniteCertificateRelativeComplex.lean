import torus.shared.BosonFiniteCertificateCanonicalCOMLower

/-! The stored relative basis is the full complex kernel of actual COM lowering
inside each stated canonical block span at degrees 0,...,8. No positivity,
energy or desired-kernel hypothesis is used: the finite identity decomposition
is an already checked rational witness, then transported to complex coordinates. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open Matrix
open TorusLean.M2 TorusLean.Boson
open TorusLean.Shared.BosonFiniteCertificateCoordinate

theorem kernel_from_split_complex {m n r : ℕ}
    (A : Matrix (Fin m) (Fin n) ℂ) (U : Matrix (Fin n) (Fin r) ℂ)
    (P : Matrix (Fin r) (Fin n) ℂ) (C : Matrix (Fin n) (Fin m) ℂ)
    (hAU : A * U = 0) (hsplit : U * P + C * A = 1) (v : Fin n → ℂ) :
    A *ᵥ v = 0 ↔ ∃ x : Fin r → ℂ, U *ᵥ x = v := by
  constructor
  · intro hv
    refine ⟨P *ᵥ v, ?_⟩
    have he := congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => M *ᵥ v) hsplit
    simpa only [add_mulVec, ← mulVec_mulVec, hv, mulVec_zero, add_zero, one_mulVec] using he
  · rintro ⟨x, rfl⟩
    rw [mulVec_mulVec, hAU, zero_mulVec]

theorem canonicalBlock_eq_zero_iff9 {n : ℕ} (occ : Fin n → (Fin 9 →₀ ℕ))
    (hocc : Function.Injective occ) (v : Fin n → ℂ) :
    canonicalBlock (factorialScale 8) occ v = 0 ↔ v = 0 := by
  constructor
  · intro h
    apply canonicalBlock_injective (factorialScale 8) (factorialScale_pos 8) occ hocc
    exact h.trans (canonicalBlock_zero9 occ).symm
  · rintro rfl
    exact canonicalBlock_zero9 occ

theorem b300_relative_exact_complex (v : Fin 1 → ℂ) :
    complexify b300lower *ᵥ v = 0 ↔
      ∃ x : Fin 1 → ℂ, complexify b300relative *ᵥ x = v := by
  apply kernel_from_split_complex (complexify b300lower) (complexify b300relative)
    (complexify b300free) (complexify b300split)
  · have h := congrArg (fun M : Matrix (Fin 0) (Fin 1) ℚ => complexify M)
      b300_relative_annihilated
    simpa only [complexify_mul_rect, complexify_zero_rect] using h
  · have h := congrArg (fun M : Matrix (Fin 1) (Fin 1) ℚ => complexify M)
      b300_relative_complete
    simpa only [lower_complexify_add_rect, complexify_mul_rect, complexify_one_rat] using h

/-- Full kernel equality in the actual polynomial block, over complex scalars. -/
theorem k300_actual_relative_kernel (v : Fin 1 → ℂ) :
    canonicalCOMLower9 (canonicalBlock (factorialScale 8) k300occ v) = 0 ↔
      ∃ x : Fin 1 → ℂ,
        canonicalBlock (factorialScale 8) k300occ (complexify b300relative *ᵥ x) =
          canonicalBlock (factorialScale 8) k300occ v := by
  constructor
  · intro _
    refine ⟨v, ?_⟩
    have h : complexify b300relative = (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
      ext i j; fin_cases i; fin_cases j; norm_num [complexify, b300relative]
    rw [h, Matrix.one_mulVec]
  · intro _
    exact k300_actual_lower_block v

theorem b301_relative_exact_complex (v : Fin 1 → ℂ) :
    complexify b301lower *ᵥ v = 0 ↔
      ∃ x : Fin 0 → ℂ, complexify b301relative *ᵥ x = v := by
  apply kernel_from_split_complex (complexify b301lower) (complexify b301relative)
    (complexify b301free) (complexify b301split)
  · have h := congrArg (fun M : Matrix (Fin 1) (Fin 0) ℚ => complexify M)
      b301_relative_annihilated
    simpa only [complexify_mul_rect, complexify_zero_rect] using h
  · have h := congrArg (fun M : Matrix (Fin 1) (Fin 1) ℚ => complexify M)
      b301_relative_complete
    simpa only [lower_complexify_add_rect, complexify_mul_rect, complexify_one_rat] using h

/-- Full kernel equality in the actual polynomial block, over complex scalars. -/
theorem k301_actual_relative_kernel (v : Fin 1 → ℂ) :
    canonicalCOMLower9 (canonicalBlock (factorialScale 8) k301occ v) = 0 ↔
      ∃ x : Fin 0 → ℂ,
        canonicalBlock (factorialScale 8) k301occ (complexify b301relative *ᵥ x) =
          canonicalBlock (factorialScale 8) k301occ v := by
  rw [k301_actual_lower_block,
    canonicalBlock_eq_zero_iff9 k300occ k300_occupation_injective,
    b301_relative_exact_complex]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, congrArg (canonicalBlock (factorialScale 8) k301occ) hx⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, canonicalBlock_injective (factorialScale 8) (factorialScale_pos 8)
      k301occ k301_occupation_injective hx⟩

theorem b302_relative_exact_complex (v : Fin 2 → ℂ) :
    complexify b302lower *ᵥ v = 0 ↔
      ∃ x : Fin 1 → ℂ, complexify b302relative *ᵥ x = v := by
  apply kernel_from_split_complex (complexify b302lower) (complexify b302relative)
    (complexify b302free) (complexify b302split)
  · have h := congrArg (fun M : Matrix (Fin 1) (Fin 1) ℚ => complexify M)
      b302_relative_annihilated
    simpa only [complexify_mul_rect, complexify_zero_rect] using h
  · have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℚ => complexify M)
      b302_relative_complete
    simpa only [lower_complexify_add_rect, complexify_mul_rect, complexify_one_rat] using h

/-- Full kernel equality in the actual polynomial block, over complex scalars. -/
theorem k302_actual_relative_kernel (v : Fin 2 → ℂ) :
    canonicalCOMLower9 (canonicalBlock (factorialScale 8) k302occ v) = 0 ↔
      ∃ x : Fin 1 → ℂ,
        canonicalBlock (factorialScale 8) k302occ (complexify b302relative *ᵥ x) =
          canonicalBlock (factorialScale 8) k302occ v := by
  rw [k302_actual_lower_block,
    canonicalBlock_eq_zero_iff9 k301occ k301_occupation_injective,
    b302_relative_exact_complex]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, congrArg (canonicalBlock (factorialScale 8) k302occ) hx⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, canonicalBlock_injective (factorialScale 8) (factorialScale_pos 8)
      k302occ k302_occupation_injective hx⟩

theorem b303_relative_exact_complex (v : Fin 3 → ℂ) :
    complexify b303lower *ᵥ v = 0 ↔
      ∃ x : Fin 1 → ℂ, complexify b303relative *ᵥ x = v := by
  apply kernel_from_split_complex (complexify b303lower) (complexify b303relative)
    (complexify b303free) (complexify b303split)
  · have h := congrArg (fun M : Matrix (Fin 2) (Fin 1) ℚ => complexify M)
      b303_relative_annihilated
    simpa only [complexify_mul_rect, complexify_zero_rect] using h
  · have h := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℚ => complexify M)
      b303_relative_complete
    simpa only [lower_complexify_add_rect, complexify_mul_rect, complexify_one_rat] using h

/-- Full kernel equality in the actual polynomial block, over complex scalars. -/
theorem k303_actual_relative_kernel (v : Fin 3 → ℂ) :
    canonicalCOMLower9 (canonicalBlock (factorialScale 8) k303occ v) = 0 ↔
      ∃ x : Fin 1 → ℂ,
        canonicalBlock (factorialScale 8) k303occ (complexify b303relative *ᵥ x) =
          canonicalBlock (factorialScale 8) k303occ v := by
  rw [k303_actual_lower_block,
    canonicalBlock_eq_zero_iff9 k302occ k302_occupation_injective,
    b303_relative_exact_complex]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, congrArg (canonicalBlock (factorialScale 8) k303occ) hx⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, canonicalBlock_injective (factorialScale 8) (factorialScale_pos 8)
      k303occ k303_occupation_injective hx⟩

theorem b304_relative_exact_complex (v : Fin 4 → ℂ) :
    complexify b304lower *ᵥ v = 0 ↔
      ∃ x : Fin 1 → ℂ, complexify b304relative *ᵥ x = v := by
  apply kernel_from_split_complex (complexify b304lower) (complexify b304relative)
    (complexify b304free) (complexify b304split)
  · have h := congrArg (fun M : Matrix (Fin 3) (Fin 1) ℚ => complexify M)
      b304_relative_annihilated
    simpa only [complexify_mul_rect, complexify_zero_rect] using h
  · have h := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℚ => complexify M)
      b304_relative_complete
    simpa only [lower_complexify_add_rect, complexify_mul_rect, complexify_one_rat] using h

/-- Full kernel equality in the actual polynomial block, over complex scalars. -/
theorem k304_actual_relative_kernel (v : Fin 4 → ℂ) :
    canonicalCOMLower9 (canonicalBlock (factorialScale 8) k304occ v) = 0 ↔
      ∃ x : Fin 1 → ℂ,
        canonicalBlock (factorialScale 8) k304occ (complexify b304relative *ᵥ x) =
          canonicalBlock (factorialScale 8) k304occ v := by
  rw [k304_actual_lower_block,
    canonicalBlock_eq_zero_iff9 k303occ k303_occupation_injective,
    b304_relative_exact_complex]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, congrArg (canonicalBlock (factorialScale 8) k304occ) hx⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, canonicalBlock_injective (factorialScale 8) (factorialScale_pos 8)
      k304occ k304_occupation_injective hx⟩

theorem b305_relative_exact_complex (v : Fin 5 → ℂ) :
    complexify b305lower *ᵥ v = 0 ↔
      ∃ x : Fin 1 → ℂ, complexify b305relative *ᵥ x = v := by
  apply kernel_from_split_complex (complexify b305lower) (complexify b305relative)
    (complexify b305free) (complexify b305split)
  · have h := congrArg (fun M : Matrix (Fin 4) (Fin 1) ℚ => complexify M)
      b305_relative_annihilated
    simpa only [complexify_mul_rect, complexify_zero_rect] using h
  · have h := congrArg (fun M : Matrix (Fin 5) (Fin 5) ℚ => complexify M)
      b305_relative_complete
    simpa only [lower_complexify_add_rect, complexify_mul_rect, complexify_one_rat] using h

/-- Full kernel equality in the actual polynomial block, over complex scalars. -/
theorem k305_actual_relative_kernel (v : Fin 5 → ℂ) :
    canonicalCOMLower9 (canonicalBlock (factorialScale 8) k305occ v) = 0 ↔
      ∃ x : Fin 1 → ℂ,
        canonicalBlock (factorialScale 8) k305occ (complexify b305relative *ᵥ x) =
          canonicalBlock (factorialScale 8) k305occ v := by
  rw [k305_actual_lower_block,
    canonicalBlock_eq_zero_iff9 k304occ k304_occupation_injective,
    b305_relative_exact_complex]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, congrArg (canonicalBlock (factorialScale 8) k305occ) hx⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, canonicalBlock_injective (factorialScale 8) (factorialScale_pos 8)
      k305occ k305_occupation_injective hx⟩

theorem b306_relative_exact_complex (v : Fin 7 → ℂ) :
    complexify b306lower *ᵥ v = 0 ↔
      ∃ x : Fin 2 → ℂ, complexify b306relative *ᵥ x = v := by
  apply kernel_from_split_complex (complexify b306lower) (complexify b306relative)
    (complexify b306free) (complexify b306split)
  · have h := congrArg (fun M : Matrix (Fin 5) (Fin 2) ℚ => complexify M)
      b306_relative_annihilated
    simpa only [complexify_mul_rect, complexify_zero_rect] using h
  · have h := congrArg (fun M : Matrix (Fin 7) (Fin 7) ℚ => complexify M)
      b306_relative_complete
    simpa only [lower_complexify_add_rect, complexify_mul_rect, complexify_one_rat] using h

/-- Full kernel equality in the actual polynomial block, over complex scalars. -/
theorem k306_actual_relative_kernel (v : Fin 7 → ℂ) :
    canonicalCOMLower9 (canonicalBlock (factorialScale 8) k306occ v) = 0 ↔
      ∃ x : Fin 2 → ℂ,
        canonicalBlock (factorialScale 8) k306occ (complexify b306relative *ᵥ x) =
          canonicalBlock (factorialScale 8) k306occ v := by
  rw [k306_actual_lower_block,
    canonicalBlock_eq_zero_iff9 k305occ k305_occupation_injective,
    b306_relative_exact_complex]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, congrArg (canonicalBlock (factorialScale 8) k306occ) hx⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, canonicalBlock_injective (factorialScale 8) (factorialScale_pos 8)
      k306occ k306_occupation_injective hx⟩

theorem b307_relative_exact_complex (v : Fin 8 → ℂ) :
    complexify b307lower *ᵥ v = 0 ↔
      ∃ x : Fin 1 → ℂ, complexify b307relative *ᵥ x = v := by
  apply kernel_from_split_complex (complexify b307lower) (complexify b307relative)
    (complexify b307free) (complexify b307split)
  · have h := congrArg (fun M : Matrix (Fin 7) (Fin 1) ℚ => complexify M)
      b307_relative_annihilated
    simpa only [complexify_mul_rect, complexify_zero_rect] using h
  · have h := congrArg (fun M : Matrix (Fin 8) (Fin 8) ℚ => complexify M)
      b307_relative_complete
    simpa only [lower_complexify_add_rect, complexify_mul_rect, complexify_one_rat] using h

/-- Full kernel equality in the actual polynomial block, over complex scalars. -/
theorem k307_actual_relative_kernel (v : Fin 8 → ℂ) :
    canonicalCOMLower9 (canonicalBlock (factorialScale 8) k307occ v) = 0 ↔
      ∃ x : Fin 1 → ℂ,
        canonicalBlock (factorialScale 8) k307occ (complexify b307relative *ᵥ x) =
          canonicalBlock (factorialScale 8) k307occ v := by
  rw [k307_actual_lower_block,
    canonicalBlock_eq_zero_iff9 k306occ k306_occupation_injective,
    b307_relative_exact_complex]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, congrArg (canonicalBlock (factorialScale 8) k307occ) hx⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, canonicalBlock_injective (factorialScale 8) (factorialScale_pos 8)
      k307occ k307_occupation_injective hx⟩

theorem b308_relative_exact_complex (v : Fin 10 → ℂ) :
    complexify b308lower *ᵥ v = 0 ↔
      ∃ x : Fin 2 → ℂ, complexify b308relative *ᵥ x = v := by
  apply kernel_from_split_complex (complexify b308lower) (complexify b308relative)
    (complexify b308free) (complexify b308split)
  · have h := congrArg (fun M : Matrix (Fin 8) (Fin 2) ℚ => complexify M)
      b308_relative_annihilated
    simpa only [complexify_mul_rect, complexify_zero_rect] using h
  · have h := congrArg (fun M : Matrix (Fin 10) (Fin 10) ℚ => complexify M)
      b308_relative_complete
    simpa only [lower_complexify_add_rect, complexify_mul_rect, complexify_one_rat] using h

/-- Full kernel equality in the actual polynomial block, over complex scalars. -/
theorem k308_actual_relative_kernel (v : Fin 10 → ℂ) :
    canonicalCOMLower9 (canonicalBlock (factorialScale 8) k308occ v) = 0 ↔
      ∃ x : Fin 2 → ℂ,
        canonicalBlock (factorialScale 8) k308occ (complexify b308relative *ᵥ x) =
          canonicalBlock (factorialScale 8) k308occ v := by
  rw [k308_actual_lower_block,
    canonicalBlock_eq_zero_iff9 k307occ k307_occupation_injective,
    b308_relative_exact_complex]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, congrArg (canonicalBlock (factorialScale 8) k308occ) hx⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, canonicalBlock_injective (factorialScale 8) (factorialScale_pos 8)
      k308occ k308_occupation_injective hx⟩

#print axioms kernel_from_split_complex
#print axioms canonicalBlock_eq_zero_iff9
#print axioms b300_relative_exact_complex
#print axioms k300_actual_relative_kernel
#print axioms b301_relative_exact_complex
#print axioms k301_actual_relative_kernel
#print axioms b302_relative_exact_complex
#print axioms k302_actual_relative_kernel
#print axioms b303_relative_exact_complex
#print axioms k303_actual_relative_kernel
#print axioms b304_relative_exact_complex
#print axioms k304_actual_relative_kernel
#print axioms b305_relative_exact_complex
#print axioms k305_actual_relative_kernel
#print axioms b306_relative_exact_complex
#print axioms k306_actual_relative_kernel
#print axioms b307_relative_exact_complex
#print axioms k307_actual_relative_kernel
#print axioms b308_relative_exact_complex
#print axioms k308_actual_relative_kernel
end TorusLean.BosonFiniteCertificate
